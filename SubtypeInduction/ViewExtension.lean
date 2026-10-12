import Lean

open Lean Elab Command Meta

/--
Complete metadata record for a view registered via `#What_A_View`.
Stored persistently in the Lean environment across module imports.
-/
structure ViewInfo where
  /-- The target type constant name (e.g. `Palindrome`, `FO`, `Nat`). -/
  typeName : Name
  /-- All constructors in the exact order declared by the user in the `with` clause. -/
  allCtors : Array Name
  /-- Base constructors (constructors without recursive target arguments). -/
  baseCtors : Array Name
  /-- Recursive constructors (constructors with one or more recursive target arguments). -/
  recCtors : Array Name
  /-- Positiveness lemmas verified to prove structural decrease in recursive steps. -/
  positivenessLemmas : Array Name
  /-- Exhaustive cases/elimination theorem name. -/
  casesLemma : Name
  /-- Name of the synthesized view recursor (e.g. `<typeName>.recView`). -/
  recViewName : Name
  deriving Inhabited, Repr

-- ============================================================================
-- Section 1: Persistent Environment Extensions for View Components
-- ============================================================================

/-- Extension storing synthesized ViewInfo keyed by target type. -/
initialize viewExtension : SimplePersistentEnvExtension ViewInfo (NameMap ViewInfo) ←
  registerSimplePersistentEnvExtension {
    name := `viewExtension
    addEntryFn := fun map info => map.insert info.typeName info
    addImportedFn := fun arrays =>
      arrays.foldl (fun map arr =>
        arr.foldl (fun m info => m.insert info.typeName info) map) {}
  }

/-- Extension storing registered view constructors per target type: (target, ctor) -> NameMap (Array Name). -/
initialize viewCtorExtension : SimplePersistentEnvExtension (Name × Name) (NameMap (Array Name)) ←
  registerSimplePersistentEnvExtension {
    name := `viewCtorExtension
    addEntryFn := fun map (target, ctor) =>
      let existing := map.find? target |>.getD #[]
      if existing.contains ctor then map else map.insert target (existing.push ctor)
    addImportedFn := fun arrays =>
      arrays.foldl (fun map arr =>
        arr.foldl (fun m (target, ctor) =>
          let existing := m.find? target |>.getD #[]
          if existing.contains ctor then m else m.insert target (existing.push ctor)) map) {}
  }

/-- Extension storing registered cases/elimination lemma: (target, casesLemma) -> NameMap Name. -/
initialize viewCasesExtension : SimplePersistentEnvExtension (Name × Name) (NameMap Name) ←
  registerSimplePersistentEnvExtension {
    name := `viewCasesExtension
    addEntryFn := fun map (target, casesLemma) => map.insert target casesLemma
    addImportedFn := fun arrays =>
      arrays.foldl (fun map arr =>
        arr.foldl (fun m (target, casesLemma) => m.insert target casesLemma) map) {}
  }

/-- Extension storing registered positiveness decrease lemmas: (target, posLemma) -> NameMap (Array Name). -/
initialize viewPosExtension : SimplePersistentEnvExtension (Name × Name) (NameMap (Array Name)) ←
  registerSimplePersistentEnvExtension {
    name := `viewPosExtension
    addEntryFn := fun map (target, posLemma) =>
      let existing := map.find? target |>.getD #[]
      if existing.contains posLemma then map else map.insert target (existing.push posLemma)
    addImportedFn := fun arrays =>
      arrays.foldl (fun map arr =>
        arr.foldl (fun m (target, posLemma) =>
          let existing := m.find? target |>.getD #[]
          if existing.contains posLemma then m else m.insert target (existing.push posLemma)) map) {}
  }

/-- Extension storing registered well-founded relation or measure: (target, relName) -> NameMap Name. -/
initialize viewRelExtension : SimplePersistentEnvExtension (Name × Name) (NameMap Name) ←
  registerSimplePersistentEnvExtension {
    name := `viewRelExtension
    addEntryFn := fun map (target, relName) => map.insert target relName
    addImportedFn := fun arrays =>
      arrays.foldl (fun map arr =>
        arr.foldl (fun m (target, relName) => m.insert target relName) map) {}
  }

-- ============================================================================
-- Section 2: Helper Functions for Extension Management
-- ============================================================================

/-- Inserts a `ViewInfo` record into the environment. -/
def addViewInfo (env : Environment) (info : ViewInfo) : Environment :=
  viewExtension.addEntry env info

/-- Looks up view metadata for a given target type name. -/
def findViewInfo? (env : Environment) (typeName : Name) : Option ViewInfo :=
  (viewExtension.getState env).find? typeName

/-- Retrieves view metadata or throws an error if no view is registered. -/
def getViewInfo (typeName : Name) : MetaM ViewInfo := do
  let env ← getEnv
  match findViewInfo? env typeName with
  | some info => return info
  | none => throwError "No view registered for type '{typeName}'"

/-- Reverse lookup: finds the view containing a given constructor name. -/
def findViewInfoByCtor? (env : Environment) (ctorName : Name) : Option ViewInfo :=
  (viewExtension.getState env).foldl (fun acc _ info =>
    if acc.isSome then acc
    else if info.allCtors.contains ctorName then some info
    else none) none

/-- Returns a list of all registered views in the environment. -/
def getAllViews (env : Environment) : List ViewInfo :=
  ((viewExtension.getState env).toList).map (·.2)

/-- Adds a view constructor to `viewCtorExtension`. -/
def addViewCtor (env : Environment) (target : Name) (ctor : Name) : Environment :=
  viewCtorExtension.addEntry env (target, ctor)

/-- Gets all registered view constructors for a target type. -/
def getViewCtors (env : Environment) (target : Name) : Array Name :=
  (viewCtorExtension.getState env).find? target |>.getD #[]

/-- Registers a cases lemma in `viewCasesExtension`. -/
def setViewCases (env : Environment) (target : Name) (casesLemma : Name) : Environment :=
  viewCasesExtension.addEntry env (target, casesLemma)

/-- Gets the registered cases lemma for a target type. -/
def getViewCases? (env : Environment) (target : Name) : Option Name :=
  (viewCasesExtension.getState env).find? target

/-- Adds a positiveness decrease lemma to `viewPosExtension`. -/
def addViewPos (env : Environment) (target : Name) (posLemma : Name) : Environment :=
  viewPosExtension.addEntry env (target, posLemma)

/-- Gets all registered positiveness lemmas for a target type. -/
def getViewPos (env : Environment) (target : Name) : Array Name :=
  (viewPosExtension.getState env).find? target |>.getD #[]

/-- Registers a well-founded relation or measure in `viewRelExtension`. -/
def setViewRel (env : Environment) (target : Name) (relName : Name) : Environment :=
  viewRelExtension.addEntry env (target, relName)

/-- Gets the registered relation or measure for a target type. -/
def getViewRel? (env : Environment) (target : Name) : Option Name :=
  (viewRelExtension.getState env).find? target

-- ============================================================================
-- Section 3: Target Type Inference & Attribute Registration
-- ============================================================================

/-- Infers target type family name from constructor return type. -/
def inferTargetFromCtor (ctorName : Name) : MetaM Name := do
  let decl ← getConstInfo ctorName
  let (_, _, res) ← forallMetaTelescope decl.type
  match res.getAppFn.constName? with
  | some target => return target
  | none => throwError "Cannot determine target type from constructor '{ctorName}'"

/-- Infers target type family name from cases theorem parameters. -/
def inferTargetFromCases (casesName : Name) : MetaM Name := do
  let decl ← getConstInfo casesName
  let (mvars, _, _) ← forallMetaTelescope decl.type
  for mvar in mvars do
    let mvarType ← inferType mvar
    if let some target := mvarType.getAppFn.constName? then
      if target != ``PSum && target != ``PSigma && target != ``Eq then
        return target
  throwError "Cannot determine target type from cases lemma '{casesName}'"

/-- Infers target type family from positiveness lemma parameters. -/
def inferTargetFromPos (lemmaName : Name) : MetaM Name := do
  let decl ← getConstInfo lemmaName
  let (mvars, _, _) ← forallMetaTelescope decl.type
  for mvar in mvars do
    let mvarType ← inferType mvar
    if let some target := mvarType.getAppFn.constName? then
      if target != ``Nat && target != ``Bool && target != ``Eq && target != ``LT.lt then
        return target
  throwError "Cannot determine target type from positiveness lemma '{lemmaName}'"

/-- Infers target type family name from a WellFoundedRelation or measure function declaration. -/
def inferTargetFromRel (relName : Name) : MetaM Name := do
  let decl ← getConstInfo relName
  let (_, _, res) ← forallMetaTelescope decl.type
  if res.isAppOf ``WellFoundedRelation then
    let target := res.appArg!
    if let some targetName := target.getAppFn.constName? then
      return targetName
  let (mvars, _, _) ← forallMetaTelescope decl.type
  for mvar in mvars do
    let mvarType ← inferType mvar
    if let some target := mvarType.getAppFn.constName? then
      if target != ``Nat && target != ``Bool && target != ``Eq && target != ``LT.lt then
        return target
  throwError "Cannot determine target type from relation declaration '{relName}'"

/-- Attribute `@[view_ctor]` registers a constructor for its return type. -/
initialize registerBuiltinAttribute {
  name := `view_ctor
  descr := "Registers a constructor for a view on its target return type"
  add := fun declName _ _ => do
    MetaM.run' do
      let target ← inferTargetFromCtor declName
      modifyEnv fun env => addViewCtor env target declName
}

/-- Attribute `@[view_cases]` registers an elimination/cases lemma for a view. -/
initialize registerBuiltinAttribute {
  name := `view_cases
  descr := "Registers an elimination/cases lemma for a view"
  add := fun declName _ _ => do
    MetaM.run' do
      let target ← inferTargetFromCases declName
      modifyEnv fun env => setViewCases env target declName
}

/-- Attribute `@[view_pos]` registers a positiveness decrease lemma for a view. -/
initialize registerBuiltinAttribute {
  name := `view_pos
  descr := "Registers a positiveness decrease lemma for a view"
  add := fun declName _ _ => do
    MetaM.run' do
      let target ← inferTargetFromPos declName
      modifyEnv fun env => addViewPos env target declName
}

/-- Attribute `@[view_rel]` registers a well-founded relation or measure function for a view. -/
initialize registerBuiltinAttribute {
  name := `view_rel
  descr := "Registers a WellFoundedRelation or measure function for a view"
  add := fun declName _ _ => do
    MetaM.run' do
      let target ← inferTargetFromRel declName
      modifyEnv fun env => setViewRel env target declName
}

-- ============================================================================
-- Section 4: Explicit Batch Registration Commands
-- ============================================================================

syntax (name := regViewCtorCmd) "register_view_ctor " ident (" with ")? ident* : command
elab_rules : command
  | `(register_view_ctor $targetId:ident $[with]? $[$ctors]*) => do
    let targetName ← resolveGlobalConstNoOverload targetId
    for ctor in ctors do
      let ctorName ← resolveGlobalConstNoOverload ctor
      modifyEnv fun env => addViewCtor env targetName ctorName
    logInfo m!"[ViewExtension] Registered constructors {ctors.map (·.getId)} for '{targetName}'"

syntax (name := regViewCasesCmd) "register_view_cases " ident ident : command
elab_rules : command
  | `(register_view_cases $targetId:ident $casesId:ident) => do
    let targetName ← resolveGlobalConstNoOverload targetId
    let casesName ← resolveGlobalConstNoOverload casesId
    modifyEnv fun env => setViewCases env targetName casesName
    logInfo m!"[ViewExtension] Registered cases lemma '{casesName}' for '{targetName}'"

syntax (name := regViewPosCmd) "register_view_pos " ident (" with ")? ident* : command
elab_rules : command
  | `(register_view_pos $targetId:ident $[with]? $[$lemmas]*) => do
    let targetName ← resolveGlobalConstNoOverload targetId
    for lem in lemmas do
      let lemName ← resolveGlobalConstNoOverload lem
      modifyEnv fun env => addViewPos env targetName lemName
    logInfo m!"[ViewExtension] Registered positiveness lemmas {lemmas.map (·.getId)} for '{targetName}'"

syntax (name := regViewRelCmd) "register_view_rel " ident ident : command
elab_rules : command
  | `(register_view_rel $targetId:ident $relId:ident) => do
    let targetName ← resolveGlobalConstNoOverload targetId
    let relName ← resolveGlobalConstNoOverload relId
    modifyEnv fun env => setViewRel env targetName relName
    logInfo m!"[ViewExtension] Registered well-founded relation '{relName}' for '{targetName}'"

-- ============================================================================
-- Section 5: Inspection Command
-- ============================================================================

/-- Command to inspect registered view metadata in the environment. -/
syntax (name := viewInfoCmd) "#view_info " ident : command

elab_rules : command
  | `(#view_info $targetId:ident) => do
    let typeName ← resolveGlobalConstNoOverload targetId
    let env ← getEnv
    if let some info := findViewInfo? env typeName then
      let relMsg := match getViewRel? env typeName with
        | some r => s!"\n  • Tagged Relation: {r}"
        | none => ""
      logInfo m!"View Metadata for '{info.typeName}':\n  • Recursor: {info.recViewName}\n  • Cases Lemma: {info.casesLemma}\n  • Base Constructors: {info.baseCtors.toList}\n  • Recursive Constructors: {info.recCtors.toList}\n  • All Constructors: {info.allCtors.toList}\n  • Positiveness Lemmas: {info.positivenessLemmas.toList}{relMsg}"
    else
      let ctors := getViewCtors env typeName
      let casesLemma := getViewCases? env typeName
      let posLemmas := getViewPos env typeName
      let rel := getViewRel? env typeName
      if !ctors.isEmpty || casesLemma.isSome || !posLemmas.isEmpty || rel.isSome then
        logInfo m!"Registered View Components for '{typeName}' (prior to #What_A_View):\n  • Constructors: {ctors.toList}\n  • Cases Lemma: {casesLemma}\n  • Positiveness Lemmas: {posLemmas.toList}\n  • Relation: {rel}"
      else
        throwErrorAt targetId m!"No view metadata or registered components found for '{typeName}'"
