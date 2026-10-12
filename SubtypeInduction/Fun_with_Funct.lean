import Lean
import Std.Data.HashMap
import SubtypeInduction.ViewExtension
import SubtypeInduction.What_A_View

open Lean Elab Command Meta Term

/--
Syntax specification for `def_view`:
```lean
def_view dropStep {α : Type} (p : Palindrome (α := α)) : Palindrome (α := α) :=
  | .nil => .nil
  | .singleton a => .nil
  | .step a (.step b p) => p
  | .step a p => .nil
```
Optionally, the user may still specify explicit `with <ctors>*` and `cases <casesId>`.
If omitted, `def_view` automatically resolves them from the `viewExtension` environment extension.
-/
syntax (name := defView)
  "def_view " ident optDeclSig (" with " ident*)? (" cases " ident)? (" := ")? (ppLine "| " term " => " term)* : command

-- ============================================================================
-- Section 1: Identifier & Syntax Parsing Utilities
-- ============================================================================

/--
Extracts the unqualified, short name of a constructor from a hierarchical `Name`.
For example:
- `Palindrome.step`  -> `"step"`
- `step`             -> `"step"`
- `.step`            -> `"step"`
-/
def getShortName (n : Name) : String :=
  match n with
  | .str _ s => s
  | _ => n.toString

/--
Recursively unwraps parenthesized syntax nodes `(...)`.
In Lean 4, nested patterns such as `(.step b p)` are wrapped in a `Term.paren` syntax node.
Peeling these parentheses allows us to inspect the inner application.
-/
partial def unwrapParens (stx : Syntax) : Syntax :=
  if stx.isOfKind ``Lean.Parser.Term.paren && stx.getNumArgs >= 2 then
    unwrapParens stx[1]
  else
    stx

/--
Extracts the constructor name from an identifier or a leading-dot identifier:
- Regular identifier: `step` -> `"step"`
- Leading-dot identifier (`Term.dotIdent`): `.step` -> `"step"`
  (where `stx[0]` is `"."` and `stx[1]` is the identifier node `step`)
-/
def extractCtorName? (stx : Syntax) : Option String :=
  let stx := unwrapParens stx
  if stx.isIdent then
    some (getShortName stx.getId)
  else if stx.isOfKind ``Lean.Parser.Term.dotIdent then
    let idNode := stx[1]
    some (getShortName idNode.getId)
  else
    none

/--
Structured representation of a parsed pattern:
- `ctorShortName`: The name of the constructor (e.g. `"step"`, `"nil"`).
- `args`: Array of argument syntax nodes (e.g. `#[a, (.step b p)]`).
-/
structure ParsedPat where
  ctorShortName : String
  args : Array Syntax
  deriving Inhabited

/--
Parses a user pattern syntax node into a `ParsedPat`:
1. Standalone constructor (0 arguments): e.g. `.nil` or `nil` -> `args = #[]`.
2. Constructor application: e.g. `.singleton a` or `.step a p`.
   In Lean 4, `Term.app` holds the head function/constructor in child `stx[0]`,
   and arguments in child `stx[1]` (typically packaged inside a `null` container node).
-/
def parsePattern (stx : Syntax) : Option ParsedPat := do
  let stx := unwrapParens stx
  if let some name := extractCtorName? stx then
    return { ctorShortName := name, args := #[] }
  else if stx.isOfKind ``Lean.Parser.Term.app then
    let fn := stx[0]
    let name ← extractCtorName? fn
    -- Extract the argument array from the null node or syntax children
    let args :=
      if stx.getNumArgs > 1 then
        if stx[1].getKind == `null then stx[1].getArgs
        else stx.getArgs.extract 1 stx.getNumArgs
      else
        #[]
    return { ctorShortName := name, args := args }
  else
    none

-- ============================================================================
-- Section 2: PSum & PSigma Pattern Construction
-- ============================================================================

/--
Constructs a chain of `n` nested `PSum.inr` calls:
- `0, term`     => `term`
- `1, term`     => `PSum.inr term`
- `2, term`     => `PSum.inr (PSum.inr term)`
-/
def mkInrChain : Nat → Term → MacroM Term
  | 0, term => pure term
  | n + 1, term => do
    let inner ← mkInrChain n term
    `(PSum.inr $inner)

/--
Embeds a constructor's payload pattern at its correct position in the `PSum` tree.

The cases theorem (`casesId`) emits a right-associative binary sum tree:
`Branch₀ ⊕ (Branch₁ ⊕ (Branch₂ ⊕ ... ⊕ Branch_{N-1}))`

For total `N` constructors:
- Branch `i < N - 1` : wrapped in `i` `PSum.inr`s, followed by `PSum.inl`:
  `PSum.inr^i (PSum.inl payload)`
- Branch `N - 1` (last): wrapped in `N - 1` `PSum.inr`s (without `PSum.inl`):
  `PSum.inr^{N-1} payload`

Example for N = 3 (nil, singleton, step):
- `idx = 0` (nil)       => `PSum.inl payload`
- `idx = 1` (singleton) => `PSum.inr (PSum.inl payload)`
- `idx = 2` (step)      => `PSum.inr (PSum.inr payload)`
-/
def wrapPSumPattern (idx : Nat) (total : Nat) (payload : Term) : MacroM Term := do
  if idx + 1 < total then
    mkInrChain idx (← `(PSum.inl $payload))
  else
    mkInrChain idx payload

/--
Builds a nested `PSigma` (`Σ'`) payload pattern for constructor arguments.
Each branch in the cases theorem is structured as:
`Σ' arg₁, Σ' arg₂, ... x = ctor arg₁ arg₂ ...`

In Lean pattern matching, `PSigma` unpacks with anonymous constructor notation `⟨arg, rest⟩`.
The equality at the end is matched with a wildcard hole `_`:
- `[]`        => `_`
- `[a]`       => `⟨a, _⟩`
- `[a, b]`    => `⟨a, ⟨b, _⟩⟩`
- `[a, b, c]` => `⟨a, ⟨b, ⟨c, _⟩⟩⟩`
-/
def mkPayloadPattern (args : Array Term) : MacroM Term := do
  let mut res : Term ← `(_)
  for arg in args.reverse do
    res ← `(⟨$arg, $res⟩)
  return res

-- ============================================================================
-- Section 3: Nesting Detection & Branch Compilation
-- ============================================================================

/--
Inspects a pattern argument to determine if it is a nested constructor application
belonging to the known view constructors `ctors` (e.g. the second argument in `.step a (.step b p)`).
-/
def getNestedCtor? (arg : Syntax) (ctors : Array Ident) : Option ParsedPat := do
  let innerParsed ← parsePattern (unwrapParens arg)
  if ctors.any (fun c => getShortName c.getId == innerParsed.ctorShortName) then
    some innerParsed
  else
    none

/--
Checks whether any branch in `matchingBranches` contains a nested constructor pattern.
If true, this constructor requires generating a 2-level decision tree (inner `match`).
-/
def hasNestedPattern (matchingBranches : Array (ParsedPat × Term)) (ctors : Array Ident) : Bool :=
  matchingBranches.any fun (parsed, _) =>
    parsed.args.any fun arg => (getNestedCtor? arg ctors).isSome

/--
Compiles a simple 1-level constructor branch into a `(pattern, rhs)` pair:
- Binds all arguments directly in the `PSigma` payload: `⟨arg₁, ⟨arg₂, _⟩⟩`
- Wraps into the appropriate `PSum` branch position.
- Emits the user's right-hand-side verbatim.
-/
def compileSimpleBranch (ctorIdx : Nat) (totalCtors : Nat) (parsed : ParsedPat) (rhs : Term) :
    MacroM (Term × Term) := do
  let termArgs : Array Term := parsed.args.map fun a => ⟨a⟩
  let payload ← mkPayloadPattern termArgs
  let psumPat ← wrapPSumPattern ctorIdx totalCtors payload
  return (psumPat, rhs)

/--
Compiles a constructor that has nested sub-patterns (e.g. `.step a (.step b p) => p`
and fallback `.step a p => .nil`) into an outer pattern and an inner `match` expression.

Compilation Steps:
1. Partition branches into the nested branch and the fallback (catch-all) branch.
2. Find which argument position is nested (e.g. index 1 for `step`).
3. In the outer `PSum` pattern, substitute the nested argument with a fresh variable `_inner_p`.
4. In the branch body, synthesize an inner `match casesId _inner_p with`:
   - Arm 1: matches the nested constructor and binds its inner variables, returning `nestedRhs`.
   - Arm 2 (wildcard `_`): binds the user's fallback variable (e.g. `let p := _inner_p`) and returns `fallbackRhs`.
-/
def compileNestedBranch (ctorIdx : Nat) (totalCtors : Nat) (ctors : Array Ident) (casesId : Ident)
    (ctorShortName : String) (matchingBranches : Array (ParsedPat × Term)) : MacroM (Term × Term) := do
  -- 1. Partition into nested branch and fallback branch
  let mut nestedBranchOpt := none
  let mut fallbackBranchOpt := none

  for (parsed, rhs) in matchingBranches do
    if parsed.args.any fun arg => (getNestedCtor? arg ctors).isSome then
      nestedBranchOpt := some (parsed, rhs)
    else
      fallbackBranchOpt := some (parsed, rhs)

  let some (nestedParsed, nestedRhs) := nestedBranchOpt
    | Macro.throwError s!"Expected a nested pattern branch for '{ctorShortName}'"
  let some (fallbackParsed, fallbackRhs) := fallbackBranchOpt
    | Macro.throwError s!"Expected a fallback branch for '{ctorShortName}'"

  -- 2. Locate the argument index holding the nested pattern
  let mut nestedArgIdx := 0
  for k in [:nestedParsed.args.size] do
    if (getNestedCtor? nestedParsed.args[k]! ctors).isSome then
      nestedArgIdx := k
      break

  let innerParsed := (getNestedCtor? nestedParsed.args[nestedArgIdx]! ctors).get!
  let innerCtorIdx := ctors.findIdx? (fun c => getShortName c.getId == innerParsed.ctorShortName) |>.getD 0

  -- 3. Outer pattern: replaces the nested argument with a fresh variable `_inner_p`
  let innerPVar := mkIdent `_inner_p
  let mut outerArgs : Array Term := #[]
  for k in [:nestedParsed.args.size] do
    if k == nestedArgIdx then
      outerArgs := outerArgs.push innerPVar
    else
      outerArgs := outerArgs.push ⟨nestedParsed.args[k]!⟩

  let outerPayload ← mkPayloadPattern outerArgs
  let outerPsumPat ← wrapPSumPattern ctorIdx totalCtors outerPayload

  -- 4. Inner pattern: matches `casesId _inner_p` against the nested constructor
  let innerTermArgs : Array Term := innerParsed.args.map fun a => ⟨a⟩
  let innerPayload ← mkPayloadPattern innerTermArgs
  let innerPsumPat ← wrapPSumPattern innerCtorIdx totalCtors innerPayload

  -- 5. Fallback arm: binds fallback variable if specified, then executes fallback RHS
  let fallbackVar := fallbackParsed.args[nestedArgIdx]!
  let innerBody ← do
    if fallbackVar.isIdent && fallbackVar.getId == `_ then
      `(match ($casesId $innerPVar:term) with
        | $innerPsumPat => $nestedRhs
        | _ => $fallbackRhs)
    else
      let fbIdent : Ident := ⟨fallbackVar⟩
      `(match ($casesId $innerPVar:term) with
        | $innerPsumPat => $nestedRhs
        | _ =>
          let $fbIdent:ident := $innerPVar
          $fallbackRhs)

  return (outerPsumPat, innerBody)

/--
Iterates through all declared constructors in `ctors` and compiles each into an outer
`match` arm. Validates that every constructor has at least one branch covering it.
-/
def compileConstructorBranches (ctors : Array Ident) (casesId : Ident)
    (pats : Array Term) (rhss : Array Term) : CommandElabM (Array Term × Array Term) := do
  let totalCtors := ctors.size
  let mut outerPats : Array Term := #[]
  let mut outerRhss : Array Term := #[]

  for i in [:totalCtors] do
    let ctor := ctors[i]!
    let ctorShortName := getShortName ctor.getId

    -- Filter user branches matching this constructor
    let mut matchingBranches : Array (ParsedPat × Term) := #[]
    for j in [:pats.size] do
      if let some parsed := parsePattern pats[j]! then
        if parsed.ctorShortName == ctorShortName then
          matchingBranches := matchingBranches.push (parsed, rhss[j]!)

    if matchingBranches.isEmpty then
      throwError m!"Missing pattern branch for constructor '{ctor.getId}'"

    -- Dispatch to simple or nested compilation based on presence of nested sub-patterns
    let (pat, rhs) ← liftMacroM do
      if hasNestedPattern matchingBranches ctors then
        compileNestedBranch i totalCtors ctors casesId ctorShortName matchingBranches
      else
        let (parsed, rhs) := matchingBranches[0]!
        compileSimpleBranch i totalCtors parsed rhs

    outerPats := outerPats.push pat
    outerRhss := outerRhss.push rhs

  return (outerPats, outerRhss)

-- ============================================================================
-- Section 4: Target Parameter Extraction & Command Emission
-- ============================================================================

/--
Resolves the target subtype parameter, constructor identifiers, and cases lemma identifier.
Uses `viewExtension` to automatically fill in omitted constructors or cases lemmas.
-/
def resolveViewAndTarget (binders : Syntax) (optCtors : Option (Array Ident)) (optCasesId : Option Ident) :
    TermElabM (Ident × Array Ident × Ident) := do
  let env ← getEnv
  -- If constructors are provided, determine target type family from constructor return type
  let targetFamilyFromCtors? : Option Name ← do
    if let some ctors := optCtors then
      if h : 0 < ctors.size then
        let firstCtor := ctors[0]
        let firstCtorName ← realizeGlobalConstNoOverload firstCtor
        let firstCtorExpr ← mkConstWithFreshMVarLevels firstCtorName
        let (_, _, ctorRes) ← forallMetaTelescope (← inferType firstCtorExpr)
        pure ctorRes.getAppFn.constName?
      else
        pure none
    else
      pure none

  -- Elaborate binders into local context free variables and identify target parameter
  elabBinders binders.getArgs fun fvars => do
    let mut targetIdent? : Option Ident := none
    let mut resolvedInfo? : Option ViewInfo := none

    for fvar in fvars do
      let fvarType ← inferType fvar
      if let some typeName := fvarType.getAppFn.constName? then
        if let some targetFamily := targetFamilyFromCtors? then
          if typeName == targetFamily then
            targetIdent? := some (mkIdent (← fvar.fvarId!.getUserName))
            resolvedInfo? := findViewInfo? env typeName
            break
        else
          if let some info := findViewInfo? env typeName then
            targetIdent? := some (mkIdent (← fvar.fvarId!.getUserName))
            resolvedInfo? := some info
            break

    let some targetIdent := targetIdent?
      | throwError "Could not find a parameter with a registered view in the signature."

    let ctors ← match optCtors with
      | some cs => pure cs
      | none =>
        match resolvedInfo? with
        | some info => pure (info.allCtors.map mkIdent)
        | none => throwError "No view constructors provided and no registered view found."

    let casesId ← match optCasesId with
      | some cid => pure cid
      | none =>
        match resolvedInfo? with
        | some info => pure (mkIdent info.casesLemma)
        | none => throwError "No cases theorem provided and no registered view found."

    return (targetIdent, ctors, casesId)

/--
Assembles the complete `def` command syntax:
```lean
def <fn> <sig> :=
  match (<casesId> <target>) with
  | <pat₁> => <rhs₁>
  | <pat₂> => <rhs₂>
  ...
```
-/
def buildDefCommand (fn : Ident) (sig : TSyntax ``Lean.Parser.Command.optDeclSig) (casesId : Ident) (targetIdent : Ident)
    (outerPats : Array Term) (outerRhss : Array Term) : MacroM Command := do
  let matchExpr ← `(match ($casesId $targetIdent:term) with
    $[| $outerPats => $outerRhss]*)
  `(def $fn:ident $sig:optDeclSig := $matchExpr)

-- ============================================================================
-- Section 5: Main Command Elaborator
-- ============================================================================

/--
Main command elaborator for `def_view`.
Executes a 4-step pipeline:
1. Expands `optDeclSig` and resolves the target parameter, constructors, and cases lemma (via `viewExtension` if omitted).
2. Compiles user pattern branches into outer `PSum` match arms (with nested inner matches where needed).
3. Synthesizes and elaborates the final `def` command in the Lean environment.
4. Logs confirmation of successful function definition.
-/
elab_rules : command
  | `(def_view $fn:ident $sig:optDeclSig $[with $[$ctors]*]? $[cases $casesId:ident]? $[ := ]? $[ | $pats => $rhss ]*) => do
      -- 1. Extract binders from signature and resolve view metadata
      let (binders, _) := expandOptDeclSig sig
      let (targetIdent, resolvedCtors, resolvedCasesId) ← liftTermElabM <|
        resolveViewAndTarget binders ctors casesId

      -- 2. Compile user pattern branches into outer PSum match arms
      let (outerPats, outerRhss) ← compileConstructorBranches resolvedCtors resolvedCasesId pats rhss

      -- 3. Assemble and execute the definition command
      let defCmd ← liftMacroM <| buildDefCommand fn sig resolvedCasesId targetIdent outerPats outerRhss
      elabCommand defCmd

      -- 4. Report success
      logInfo m!"[def_view] Successfully defined function '{fn.getId}'"
