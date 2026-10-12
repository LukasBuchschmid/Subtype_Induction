import Lean
import Std.Data.HashMap
import SubtypeInduction.ViewExtension

open Lean Elab Command Meta Term

syntax (name := whatAViewCmd)
  "#What_A_View " term (" with " ident*)? (" plus " ident*)? (" cases " ident)? (" through " term)? : command

/-- Checks if a constructor argument is of the recursive target type. -/
def extractTargetTerm? (arg : Expr) (argType : Expr) (targetType : Expr) : MetaM (Option Expr) := do
  let argType ← instantiateMVars argType
  let targetType ← instantiateMVars targetType

  -- extract the head constant names of both types to check for a match
  let some targetFn := targetType.getAppFn.constName? | return none
  let some argFn := argType.getAppFn.constName? | return none

  -- if head constants match, ensure full type unification succeeds (e.g. for type parameters)
  if argFn == targetFn then
    _ ← isDefEq argType targetType
    return some arg
  else
    return none

/-- Recursively decomposes a nested `PSum` tree into flat branches. -/
partial def unrollCasesTree (goal : MVarId) (targetFVar : FVarId) : MetaM (Array CasesSubgoal) := do
  goal.withContext do
    let casesType ← inferType (mkFVar targetFVar)
    -- check if this branch is a sum of more cases (PSum A B)
    if casesType.isAppOf ``PSum then
      let subgoals ← goal.cases targetFVar
      match subgoals with
      | #[inlBranch, inrBranch] =>
        -- extract payload of the right branch and recursively unroll the rest of the cases tree
        match inrBranch.fields[0]? with
        | some inrPayloadExpr =>
          let inrPayloadFVar := inrPayloadExpr.fvarId!
          let restOfBranches ← unrollCasesTree inrBranch.mvarId inrPayloadFVar
          return #[inlBranch] ++ restOfBranches
        | none =>
          return subgoals
      | _ =>
        return subgoals
    else
      -- base case: we reached a leaf branch (the last case)
      return #[{
        mvarId   := goal,
        fields   := #[mkFVar targetFVar],
        subst    := {},
        ctorName := default
      }]

/-- Recursively unpacks nested `PSigma` types until reaching the leaf equality. -/
partial def unpackSigma (goal : MVarId) (payload : FVarId) : MetaM (MVarId × FVarId) := do
  goal.withContext do
    let payloadType ← inferType (mkFVar payload)
    -- if we hit the equality x = ctor args, we reached the bottom
    if payloadType.isEq then
      return (goal, payload)
    else
      -- otherwise it is a PSigma existential: split it to extract the witness and remaining payload
      let subgoals ← goal.cases payload
      match subgoals with
      | #[newBranch] =>
        match newBranch.fields[1]? with
        | some nextPayloadExpr =>
          let nextPayloadFVar := nextPayloadExpr.fvarId!
          -- recurse down the next layer of the PSigma chain
          unpackSigma newBranch.mvarId nextPayloadFVar
        | none =>
          throwError "PSigma branch did not have a second field!"
      | _ =>
        throwError "Expected exactly one subgoal from PSigma, got {subgoals.size}"

/-- Builds a single case branch: `Σ' (args...), x = ctor args...`. -/
def buildCasesBranch (x : Expr) (ctorName : Name) : MetaM Expr := do
  let ctorExpr ← mkConstWithFreshMVarLevels ctorName
  -- spawn metavariables for constructor arguments and unify return type with x
  let (mvars, bInfos, ctorRes) ← forallMetaTelescope (← inferType ctorExpr)
  _ ← isDefEq ctorRes (← inferType x)

  -- keep only explicit arguments (.default) so we don't bind inferred type parameters
  let mut explicitMvars := #[]
  for i in [:mvars.size] do
    if bInfos[i]! == .default then
      explicitMvars := explicitMvars.push mvars[i]!

  -- build the base equation x = ctor args
  let mut branch ← mkEq x (mkAppN ctorExpr mvars)
  branch ← instantiateMVars branch

  -- wrap arguments in reverse order from the inside out using PSigma (Σ')
  for mvar in explicitMvars.reverse do
    let mvarId := mvar.mvarId!
    let userName := (← mvarId.getDecl).userName
    let mvarType ← instantiateMVars (← inferType mvar)

    -- introduce local variable v with the parameter's userName and swap mvar for v
    branch ← withLocalDeclD userName mvarType fun v => do
      let branchBody := branch.replace fun e => if e == mvar then some v else none
      let lam ← mkLambdaFVars #[v] branchBody
      mkAppM ``PSigma #[lam]

  return branch

-- ============================================================================
-- Phase 1: Input Elaboration
-- ============================================================================

/-- Introduces local declarations for any unassigned type parameter metavariables in `rawTypeExpr`,
    executing `k` in the extended local context with the parameter free variables and the specialized `typeExpr`. -/
def withTypeParams (rawTypeExpr : Expr) (k : Array Expr → Expr → TermElabM Unit) : TermElabM Unit := do
  let typeMvars ← getMVars rawTypeExpr
  let rec loop (mvars : List MVarId) (fvars : Array Expr) : TermElabM Unit := do
    match mvars with
    | [] =>
      let typeExpr ← instantiateMVars rawTypeExpr
      k fvars typeExpr
    | m :: ms =>
      let mType ← instantiateMVars (← m.getType)
      let mDecl ← m.getDecl
      let mName := mDecl.userName
      let name := if mName.isAnonymous then (if fvars.isEmpty then `α else Lean.Name.mkSimple s!"α_{fvars.size}") else mName
      withLocalDeclD name mType fun fvar => do
        m.assign fvar
        loop ms (fvars.push fvar)
  loop typeMvars.toList #[]

/-- Instantiates a declared relation or measure function for `typeExpr`. -/
def mkRelFromDecl (typeExpr : Expr) (declName : Name) : MetaM (Option Expr) := do
  let expectedRelType ← mkAppM ``WellFoundedRelation #[typeExpr]

  -- 1. Try treating declName as WellFoundedRelation
  try
    let ctorExpr ← mkConstWithFreshMVarLevels declName
    let (mvars, _, _) ← forallMetaTelescope (← inferType ctorExpr)
    let app := mkAppN ctorExpr mvars
    if ← isDefEq (← inferType app) expectedRelType then
      let res ← instantiateMVars app
      return some res
  catch _ => pure ()

  -- 2. Try treating declName as a measure function: target → Nat
  -- We instantiate only the leading implicit/type parameters, leaving the target argument unapplied
  try
    let ctorExpr ← mkConstWithFreshMVarLevels declName
    let (mvars, _, resType) ← forallMetaTelescope (← inferType ctorExpr)
    if resType.isConstOf ``Nat && mvars.size > 0 then
      let fnMvars := mvars.pop
      let targetMVar := mvars.back!
      if ← isDefEq (← inferType targetMVar) typeExpr then
        let fnApp := mkAppN ctorExpr fnMvars
        let fnApp ← instantiateMVars fnApp
        let relExpr ← mkAppM ``measure #[fnApp]
        return some relExpr
  catch _ => pure ()

  return none

/-- Elaborates an explicit relation or measure term passed via `through <rel>`. -/
def elabExplicitRelation (typeExpr : Expr) (rel : Term) : TermElabM Expr := do
  let expectedRelType ← mkAppM ``WellFoundedRelation #[typeExpr]
  -- Try 1: WellFoundedRelation typeExpr
  try
    let relExpr ← withOptions (fun o => o.setBool `linter.unusedVariables false) do
      Term.elabTerm rel expectedRelType
    Term.synthesizeSyntheticMVarsNoPostponing
    let relExpr ← instantiateMVars relExpr
    if ← isDefEq (← inferType relExpr) expectedRelType then
      return relExpr
  catch _ => pure ()

  -- Try 2: measure function typeExpr → Nat
  try
    let natType := Lean.mkConst ``Nat
    let measureType ← mkArrow typeExpr natType
    let fnExpr ← withOptions (fun o => o.setBool `linter.unusedVariables false) do
      Term.elabTerm rel measureType
    Term.synthesizeSyntheticMVarsNoPostponing
    let fnExpr ← instantiateMVars fnExpr
    let relExpr ← mkAppM ``measure #[fnExpr]
    return relExpr
  catch _ => pure ()

  -- Fallback to standard elaboration with expected type to produce accurate error message
  let relExpr ← Term.elabTerm rel expectedRelType
  Term.synthesizeSyntheticMVarsNoPostponing
  let relExpr ← instantiateMVars relExpr
  unless ← isDefEq (← inferType relExpr) expectedRelType do
    throwErrorAt rel m!"Relation must have type '{expectedRelType}', but got '{← inferType relExpr}'"
  return relExpr

/-- Resolves the well-founded relation for the target type using a 3-tier fallback:
    0. Explicit `through <rel>` term if provided.
    1. Persistent environment extension `getViewRel? env targetName` (tagged via `@[view_rel]`).
    2. Default `.size` convention (`<targetName>.size`) or `SizeOf` instance (`sizeOfWFRel`).
    3. If all fail, throw an error requiring an explicit relation via `through <rel>`. -/
def resolveRelation (typeExpr : Expr) (targetName : Name) (optRel : Option Term) : TermElabM Expr := do
  -- Tier 0: Explicitly handed relation
  if let some rel := optRel then
    return ← elabExplicitRelation typeExpr rel

  let env ← getEnv

  -- Tier 1: Look for tagged relation in the persistent environment extension
  if let some relName := getViewRel? env targetName then
    if let some relExpr ← mkRelFromDecl typeExpr relName then
      return relExpr
    else
      throwError m!"Tagged relation '{relName}' for '{targetName}' could not be instantiated for '{typeExpr}'"

  -- Tier 2: Try .size naming convention (<targetName>.size)
  let sizeName := targetName ++ `size
  if env.contains sizeName then
    if let some relExpr ← mkRelFromDecl typeExpr sizeName then
      return relExpr

  -- Tier 2 (cont.): Try Lean's WellFoundedRelation / SizeOf instance synthesis
  let expectedRelType ← mkAppM ``WellFoundedRelation #[typeExpr]
  if let some inst ← synthInstance? expectedRelType then
    return inst

  -- Tier 3: All fallbacks failed -> require explicit relation
  throwError m!"No well-founded relation found for '{targetName}'. Please either:\n" ++
    m!"  1. Tag a relation/measure with @[view_rel]\n" ++
    m!"  2. Define a '{targetName}.size' measure\n" ++
    m!"  3. Provide one explicitly using 'through <rel>'"

/-- Backward-compatible helper for elaborating a target and explicit relation. -/
def elabRelation (typeExpr : Expr) (rel : Term) : TermElabM Expr :=
  elabExplicitRelation typeExpr rel

-- ============================================================================
-- Phase 2: Constructor Categorization
-- ============================================================================

/-- Partitions constructors into base constructors and recursive constructors. -/
def categorizeConstructors (typeExpr : Expr) (ctors : Array Ident) : MetaM (Array Name × Array Name) := do
  let mut localBase := #[]
  let mut localRec := #[]

  for ctor in ctors do
    -- verify constructor identifier exists in the environment
    let ctorName ← try
      realizeGlobalConstNoOverload ctor
    catch _ =>
      throwErrorAt ctor m!"'{ctor.getId}' is not a valid existing name in the environment!"

    let ctorExpr ← mkConstWithFreshMVarLevels ctorName
    -- peel constructor parameters to obtain its return type
    let (mvars, _, resultType) ← forallMetaTelescope (← inferType ctorExpr)

    let targetName := typeExpr.getAppFn.constName?
    let resultName := resultType.getAppFn.constName?

    -- verify the constructor actually returns the target type family
    if resultName.isNone || resultName != targetName then
      throwErrorAt ctor m!"Invalid domain: '{ctorName}' returns '{resultType}', expected family '{targetName.getD `unknown}'"

    -- if the target type is parameterized (e.g. Palindrome α), check exact match
    if typeExpr.isApp then
      unless ← isDefEq resultType typeExpr do
        throwErrorAt ctor m!"Invalid domain: '{ctorName}' returns '{resultType}', expected exact match '{typeExpr}'"

    -- inspect arguments: if any argument has the target type, it is recursive
    let mut isBaseCtor := true
    for mvar in mvars do
      let argType ← inferType mvar
      if (← extractTargetTerm? mvar argType typeExpr).isSome then
        isBaseCtor := false
        break

    if isBaseCtor then
      localBase := localBase.push ctorName
    else
      localRec := localRec.push ctorName

  return (localBase, localRec)

-- ============================================================================
-- Phase 3: Positiveness Verification
-- ============================================================================

/-- Verifies that each recursive argument decreases according to the relation via provided theorems. -/
def verifyPositiveness (typeExpr : Expr) (relExpr : Expr) (localRec : Array Name) (thms : Array Ident) : TermElabM Unit := do
  for ctorName in localRec do
    let ctorExpr ← mkConstWithFreshMVarLevels ctorName
    let (ctorArgs, _, _) ← forallMetaTelescope (← inferType ctorExpr)

    -- iterate through all arguments of the recursive constructor
    for i in [:ctorArgs.size] do
      let arg := ctorArgs[i]!
      let argType ← inferType arg
      match (← extractTargetTerm? arg argType typeExpr) with
      -- non-recursive argument (e.g. variable name), nothing to prove
      | none => pure ()
      | some targetTerm =>
        let mut targetProven := false
        -- try each positiveness theorem in thms to prove targetTerm < ctorApp
        for thm in thms do
          let matchSuccess ← try
            let thmName ← realizeGlobalConstNoOverload thm
            let ctorApp := mkAppN ctorExpr ctorArgs

            -- extract the binary relation function (.rel) from the WellFoundedRelation structure
            let relFunc ← mkAppOptM ``WellFoundedRelation.rel #[none, some relExpr]
            let rawProp := mkAppN relFunc #[targetTerm, ctorApp]
            let expectedProp ← instantiateMVars rawProp.headBeta

            -- peel theorem quantifiers and check if its conclusion matches the expected inequality
            let thmExpr ← mkConstWithFreshMVarLevels thmName
            let (_, _, thmRes) ← forallMetaTelescope (← inferType thmExpr)
            let thmResInst ← instantiateMVars thmRes

            Term.synthesizeSyntheticMVarsNoPostponing
            isDefEq thmResInst expectedProp
          catch _ =>
            pure false

          if matchSuccess then
            targetProven := true
            break

        unless targetProven do
          throwError m!"No positiveness theorem found for recursive term '{targetTerm}' in constructor '{ctorName}'"

-- ============================================================================
-- Phase 4: Cases Theorem Verification
-- ============================================================================

-- this currently enforces the cases theorem to have the same constructor order as the user hands them it
-- but that requirement is unecessary
/-- Verifies that the cases theorem exhaustively covers all constructors as expected. -/
def verifyCasesTheorem (typeExpr : Expr) (casesId : Ident) (ctors : Array Ident) : MetaM Name := do
  let casesName ← try
    realizeGlobalConstNoOverload casesId
  catch _ =>
    throwErrorAt casesId m!"'{casesId.getId}' is not a valid existing name in the environment!"

  let casesExpr ← mkConstWithFreshMVarLevels casesName
  let (casesArgs, _, casesRes) ← forallMetaTelescope (← inferType casesExpr)

  -- find the argument representing the target variable x to case-split on
  let mut xVarOpt := none
  for arg in casesArgs do
    if ← isDefEq (← inferType arg) typeExpr then
      xVarOpt := some arg
      break

  let some xVar := xVarOpt | throwErrorAt casesId m!"Cases theorem '{casesId.getId}' must take an argument of type '{typeExpr}'"

  -- fold the expected right-associative PSum tree: Branch_1 ⊕ (Branch_2 ⊕ ... ⊕ Branch_n)
  -- we start by building cases
  let mut expectedCasesRes ← buildCasesBranch xVar (← realizeGlobalConstNoOverload ctors.back!)
  for i in [1 : ctors.size] do
    let ctorId := ctors[ctors.size - 1 - i]!
    let ctorName ← realizeGlobalConstNoOverload ctorId
    let branch ← buildCasesBranch xVar ctorName
    expectedCasesRes ← mkAppM ``PSum #[branch, expectedCasesRes]

  let expectedCasesResInst ← instantiateMVars expectedCasesRes
  let casesResInst ← instantiateMVars casesRes

  -- verify that the user's cases theorem return type matches our synthesized tree definitionally
  unless ← isDefEq casesResInst expectedCasesResInst do
    throwErrorAt casesId m!"Cases theorem return type mismatch.\n\nExpected:\n{expectedCasesResInst}\n\nGot:\n{casesResInst}"

  return casesName

-- ============================================================================
-- Phase 5: Recursor Type Construction
-- ============================================================================

/-- Replaces unassigned metavariables with freshly bound local variables. -/
def mkAssumptionType (mvars : Array Expr) (bodyGen : Array Expr → MetaM Expr) : MetaM Expr := do
  -- filter out metavariables that were already solved (e.g. type parameters inferred by isDefEq)
  let unassigned ← mvars.filterM (fun m => not <$> m.mvarId!.isAssigned)

  -- recursively open nested local scopes for each unassigned argument to support dependent types
  let rec loop (i : Nat) (fvars : Array Expr) : MetaM Expr := do
    if h : i < unassigned.size then
      let mvar := unassigned[i]
      let decl ← mvar.mvarId!.getDecl
      let type ← instantiateMVars decl.type
      -- introduce local variable for argument and assign it to the metavariable placeholder
      withLocalDeclD decl.userName type fun fvar => do
        mvar.mvarId!.assign fvar
        loop (i + 1) (fvars.push fvar)
    else
      -- all arguments are now in context: call bodyGen to construct the assumption type
      bodyGen fvars
  loop 0 #[]

/-- Constructs the full recursor type: `∀ (motive) (case_1) ... (case_n) (x), motive x`. -/
def buildRecursorType (typeExpr : Expr) (localBase : Array Name) (localRec : Array Name) : MetaM Expr := do
  let u ← mkFreshLevelMVar
  let propExpr := mkSort u
  let predType ← mkArrow typeExpr propExpr
  let varName := Name.mkSimple "motive"

  -- introduce the motive predicate: (motive : typeExpr → Prop)
  withLocalDeclD varName predType fun motiveVar => do
    let mut arguments := #[]

    -- build assumption types for base constructors: ∀ args, motive (ctor args)
    for ctorName in localBase do
      let ctorExpr ← mkConstWithFreshMVarLevels ctorName
      let (mvars, _, resultType) ← forallMetaTelescope (← inferType ctorExpr)
      -- unify resultType with typeExpr to solve type parameter metavariables
      _ ← isDefEq resultType typeExpr
      let assumptionType ← mkAssumptionType mvars fun fvars => do
        let fullyAppliedCtor ← instantiateMVars (mkAppN ctorExpr mvars)
        let motiveApp := mkApp motiveVar fullyAppliedCtor
        mkForallFVars fvars motiveApp
      arguments := arguments.push assumptionType

    -- build assumption types for recursive constructors: ∀ args (ihs), motive (ctor args)
    for ctorName in localRec do
      let ctorExpr ← mkConstWithFreshMVarLevels ctorName
      let (mvars, _, resultType) ← forallMetaTelescope (← inferType ctorExpr)
      _ ← isDefEq resultType typeExpr
      let recAssumptionType ← mkAssumptionType mvars fun fvars => do
        -- collect all recursive arguments
        let mut allTargetTerms := #[]
        for fvar in fvars do
          let argType ← inferType fvar
          allTargetTerms := match (← extractTargetTerm? fvar argType typeExpr) with
            | some t => allTargetTerms.push t
            | none   => allTargetTerms

        -- recursively add induction hypotheses (h : motive t) for each recursive subterm t
        let rec buildAssumptions (terms : List Expr) (accAssumptions : Array Expr) : MetaM Expr := do
          match terms with
          | [] =>
              let fullyAppliedCtor ← instantiateMVars (mkAppN ctorExpr mvars)
              let motiveApp := mkApp motiveVar fullyAppliedCtor
              -- bind both constructor arguments and inductive hypotheses
              mkForallFVars (fvars ++ accAssumptions) motiveApp
          | targetTerm :: rest =>
              -- build the assumption (h : motive t)
              let hypType := mkApp motiveVar targetTerm
              withLocalDeclD `h hypType fun hyp => do
                buildAssumptions rest (accAssumptions.push hyp)
        buildAssumptions allTargetTerms.toList #[]

      arguments := arguments.push recAssumptionType

    -- fold all case assumptions into the final recursor type: ∀ motive case_1 ... case_n x, motive x
    let rec buildRecType (types : List Expr) (caseFvars : Array Expr) : MetaM Expr := do
      match types with
      | [] =>
          withLocalDeclD `x typeExpr fun xVar => do
            let body := mkApp motiveVar xVar
            let allFvars := #[motiveVar] ++ caseFvars ++ #[xVar]
            mkForallFVars allFvars body
      | t :: ts =>
          let caseName := Name.mkSimple s!"case_{caseFvars.size + 1}"
          withLocalDeclD caseName t fun fvar => do
            buildRecType ts (caseFvars.push fvar)

    buildRecType arguments.toList #[]

-- ============================================================================
-- Phase 6: Recursor Proof Generation
-- ============================================================================

/-- Synthesizes the recursor proof term using WellFounded.fix and cases decomposition. -/
def proveRecursor (_typeExpr : Expr) (relExpr : Expr) (casesName : Name)
    (localBase : Array Name) (localRec : Array Name) (thms : Array Ident)
    (finalRecursorType : Expr) : TermElabM Expr := do
  let mvar ← mkFreshExprMVar finalRecursorType
  let mut goal : MVarId := mvar.mvarId!

  -- intro all the assumptions of the recursor: motive + base rules + recursive rules + target x
  let numArgs := 1 + localBase.size + localRec.size + 1
  let (recursorFvars, nextGoal) ← goal.introN numArgs
  goal := nextGoal

  -- mapping constructor names to their corresponding motive assumption in fvars
  let mut caseMap : Lean.NameMap FVarId := {}
  for i in [:localBase.size] do
    caseMap := caseMap.insert localBase[i]! recursorFvars[1 + i]!
  for i in [:localRec.size] do
    caseMap := caseMap.insert localRec[i]! recursorFvars[1 + localBase.size + i]!

  -- apply WellFounded.fix to transform the goal into the induction step of strong induction
  goal ← goal.withContext do
    let motiveFVar := mkFVar recursorFvars[0]!
    let wfProof ← mkAppOptM ``WellFoundedRelation.wf #[none, some relExpr]
    let fixExpr ← mkAppOptM ``WellFounded.fix #[none, some motiveFVar, none, some wfProof]
    let subgoals ← goal.apply fixExpr
    pure subgoals[0]!

  -- intro the x on which we will do cases and prove positiveness together with the induction hypothesis
  let (indFVars, nextGoal) ← goal.introN 2 [`x_val, `ih_hyp]
  let xFVar  := indFVars[0]!
  goal := nextGoal

  -- apply the cases lemma to x, assert it and move it into the context
  let (_casesGoal2, casesSubgoals) ← goal.withContext do
    let casesVar := mkFVar xFVar
    let casesApp ← mkAppM casesName #[casesVar]
    let casesGoal ← goal.assert `casesVal (← inferType casesApp) casesApp
    let (casesFVarId, casesGoal2) ← casesGoal.intro1P
    let allFlatSubgoals ← unrollCasesTree casesGoal2 casesFVarId
    pure (casesGoal2, allFlatSubgoals)

  for branch in casesSubgoals do
    let initialGoal := branch.mvarId
    match branch.fields[0]? with
    | none => pure ()
    | some initialPayloadExpr =>
      let initialPayload := initialPayloadExpr.fvarId!
      -- unpack the Sigma term to obtain the equality x = ctor [args]
      let (unpackedGoal, eqFVar) ← unpackSigma initialGoal initialPayload
      unpackedGoal.withContext do
        let eqType ← inferType (mkFVar eqFVar)
        match eqType.eq? with
        | none =>
          throwError m!"Expected equality type, got '{eqType}'"
        | some (_type, _lhs, rhs) =>
          -- match on the constructor name which was applied
          match rhs.getAppFn.constName? with
          | none =>
            throwError m!"Could not extract constant name from RHS: '{rhs}'"
          | some funName =>
            match caseMap.find? funName with
            | none =>
              throwError m!"Could not find case rule for constructor '{funName}'"
            | some ruleFVar =>
              -- substitute along the equality in the cases lemma rewriting x => ctor [args]
              let substGoal ← Lean.Meta.subst unpackedGoal eqFVar
              -- apply the recursor case rule corresponding to this constructor
              let remainingGoals ← substGoal.apply (mkFVar ruleFVar)

              -- iterate through the remaining Assumptions and apply ih so ∀y, y < x : motive(y)
              for g in remainingGoals do
                let ihVar ← g.withContext do
                  let ihDecl ← getLocalDeclFromUserName `ih_hyp
                  pure (mkFVar ihDecl.fvarId)
                let newGoals ← g.apply ihVar

                -- now prove that y < x
                for mg in newGoals do
                  let mut solved := false
                  for thm in thms do
                    let thmName ← realizeGlobalConstNoOverload thm
                    let thmExpr ← mkConstWithFreshMVarLevels thmName
                    -- try applying the relevant theorem by iterating through all of them
                    try
                      let tempGoals ← mg.apply thmExpr
                      let mut allClosed := true
                      -- for any remaining goals, for example missing subtype proofs since positiveness operates on .val
                      -- try assumption tactic to infer the subtype proofs from the ambient context
                      for tempGoal in tempGoals do
                        try
                          tempGoal.assumption
                        catch _ =>
                          allClosed := false
                          break

                      if allClosed then
                        solved := true
                        break
                      else
                        continue
                    catch _ =>
                      continue

                  unless solved do
                    throwError m!"Could not prove positiveness for recursive subgoal in '{funName}'"

  instantiateMVars mvar

-- ============================================================================
-- Phase 7: Registration in the Environment
-- ============================================================================

/-- Abstracts universe levels and implicit type parameters, registering `<Target>.recView`. -/
def registerRecursor (typeExpr : Expr) (finalRecursorType : Expr) (proofVal : Expr) : MetaM Name := do
  let proofVal ← instantiateMVars proofVal
  let finalRecursorType ← instantiateMVars finalRecursorType

  let typeOfType ← inferType finalRecursorType
  let typeOfType ← instantiateMVars typeOfType
  let sortLevel ← getLevel typeOfType


  -- buidling an Id function to get the metavariables of the type and the proof to agree
  let idApp := mkApp2 (mkConst ``Id [sortLevel]) finalRecursorType proofVal
  let res ← abstractMVars idApp

  -- rename internal universe level names (_abstMVar.0) to u
  let newParamNames := if res.paramNames.size == 1 then
    res.paramNames.map fun n => if n.toString.startsWith "_abstMVar" then `u else n
  else
    res.paramNames.mapIdx fun idx n =>
      if n.toString.startsWith "_abstMVar" then
        if idx == 0 then `u else Lean.Name.mkSimple s!"u_{idx+1}"
      else n
  let finalExpr := res.expr.instantiateLevelParams res.paramNames.toList (newParamNames.toList.map Level.param)

  -- peeling away the Id function and the possible implicit parameters by quantifying over them
  let rec rebuild (e : Expr) : Expr × Expr :=
    match e with
    | .lam n t b bi =>
       let (typeBody, valBody) := rebuild b
       (.forallE n t typeBody bi, .lam n t valBody bi)
    | _ =>
       (e.appFn!.appArg!, e.appArg!)

  -- extract the final type and proof, and determine the declaration name
  let (finalType, finalProof) := rebuild finalExpr
  let recName := (typeExpr.getAppFn.constName?.getD `Target) ++ `recView

  -- register the Name in the environment
  Lean.addDecl <| Declaration.defnDecl {
    name := recName
    levelParams := newParamNames.toList
    type := finalType
    value := finalProof
    safety := .safe
    hints := .regular 0
  }
  return recName

-- ============================================================================
-- Main Command Elaborator
-- ============================================================================

elab_rules : command
  | `(#What_A_View $targetType $[with $[$userCtors]*]? $[plus $[$userThms]*]? $[cases $userCases:ident]? $[through $optRel]?) => do
    runTermElabM fun sectionVars => do
      let e ← Term.elabType targetType
      Term.synthesizeSyntheticMVarsNoPostponing
      let rawTypeExpr ← instantiateMVars e

      let some targetName := rawTypeExpr.getAppFn.constName?
        | throwError "Target type must be a constant name"

      let env ← getEnv

      -- 1. Resolve constructors from command arguments or from viewCtorExtension
      let ctors ← match userCtors with
        | some cs =>
          if cs.isEmpty then
            throwError "No constructors provided in the 'with' clause."
          pure cs
        | none =>
          let storedCtors := getViewCtors env targetName
          if storedCtors.isEmpty then
            throwError m!"No constructors found for '{targetName}'. Either provide 'with <ctors>*' or tag them with @[view_ctor]."
          pure (storedCtors.map mkIdent)

      -- 2. Resolve cases lemma from command argument, viewCasesExtension, or naming convention
      let casesId ← match userCases with
        | some cid => pure cid
        | none =>
          match getViewCases? env targetName with
          | some cid => pure (mkIdent cid)
          | none =>
            let defaultName := Lean.Name.mkSimple (targetName.toString.decapitalize ++ "_cases")
            if env.contains defaultName then
              pure (mkIdent defaultName)
            else if env.contains (targetName ++ `cases) then
              pure (mkIdent (targetName ++ `cases))
            else
              throwError m!"No cases theorem found for '{targetName}'. Either provide 'cases <lemma>' or tag it with @[view_cases]."

      -- 3. Resolve positiveness lemmas from command argument or viewPosExtension
      let thms ← match userThms with
        | some ts => pure ts
        | none =>
          pure (getViewPos env targetName |>.map mkIdent)

      withTypeParams rawTypeExpr fun typeFVars typeExpr => do
        -- 1. Resolve domain and well-founded relation (through / @[view_rel] / .size / SizeOf)
        let relExpr ← resolveRelation typeExpr targetName optRel

        -- 2. Categorize constructors into base and recursive
        let (localBase, localRec) ← categorizeConstructors typeExpr ctors

        -- 3. Verify positiveness of recursive arguments
        verifyPositiveness typeExpr relExpr localRec thms

        -- 4. Verify cases theorem coverage
        let casesName ← verifyCasesTheorem typeExpr casesId ctors

        -- 5. Construct the recursor type specification
        let finalRecursorType ← buildRecursorType typeExpr localBase localRec

        -- 6. Synthesize the recursor proof via tactics
        let proofVal ← proveRecursor typeExpr relExpr casesName localBase localRec thms finalRecursorType

        -- 7. Abstract universe levels / type params and register the definition
        let finalRecTypeWithParams ← mkForallFVars (sectionVars ++ typeFVars) finalRecursorType
        let proofValWithParams ← mkLambdaFVars (sectionVars ++ typeFVars) proofVal

        let recName ← registerRecursor typeExpr finalRecTypeWithParams proofValWithParams

        -- 8. Persistent Environment Extension Registration
        let allCtorNames ← ctors.mapM (fun id => realizeGlobalConstNoOverload id)
        let thmNames ← thms.mapM (fun id => realizeGlobalConstNoOverload id)

        let viewInfo : ViewInfo := {
          typeName := targetName
          allCtors := allCtorNames
          baseCtors := localBase
          recCtors := localRec
          positivenessLemmas := thmNames
          casesLemma := casesName
          recViewName := recName
        }

        modifyEnv fun env => addViewInfo env viewInfo
        logInfo m!"[What_A_View] Registered view metadata for '{targetName}' with recursor '{recName}'"
