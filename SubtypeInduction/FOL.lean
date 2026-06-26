import Lean

open Lean (Name ToExpr)

inductive Rel
  | plain (name : Name)
  | trc (name : Name)
  deriving Repr, DecidableEq, Inhabited, ToExpr, Hashable

@[grind cases]
inductive Var
  | bound (deBruijnIdx : Nat)
  | free (name : Name)
  deriving Repr, DecidableEq, Inhabited, ToExpr


inductive FOF
  | pred (pred : Name) (var : Var)
  | rel (rel : Rel) (var₁ var₂ : Var)
  | top
  | not (φ : FOF)
  | and (φ₁ φ₂ : FOF)
  | or  (φ₁ φ₂ : FOF)
  | imp (φ₁ φ₂ : FOF)
  | exists (varName : Name) (φ : FOF)
  | forall (varName : Name) (φ : FOF)
  deriving Repr, DecidableEq, Inhabited, ToExpr

def FOF.size : FOF → Nat
  | pred _ _ => 1
  | rel _ _ _ => 1
  | top => 0
  | not φ => 1 + size φ
  | and φ₁ φ₂ => 1 + max (size φ₁) (size φ₂)
  | or φ₁ φ₂ => 1 + max (size φ₁) (size φ₂)
  | imp φ₁ φ₂ => 1 + max (size φ₁) (size φ₂)
  | «exists» _ φ => 1 + size φ
  | «forall» _ φ => 1 + size φ


/- Create the body with the bound variables, but not the quatifier -/
def FOF.mkBound_helper (nm : Lean.Name) (body : FOF) (depth : Nat) : FOF :=
  match body with
  | .pred p world =>
    let world' := match world with
      | .free nm' => if nm = nm' then .bound depth else world
      | _ => world
    .pred p world'
  | .rel r x y =>
    let x' := match x with
      | .free nm' => if nm = nm' then .bound depth else x
      | _ => x
    let y' := match y with
      | .free nm' => if nm = nm' then .bound depth else y
      | _ => y
    .rel r x' y'
  | .top => .top
  | .not body' => .not <| FOF.mkBound_helper nm body' depth
  | .and lhs rhs =>  .and (FOF.mkBound_helper nm lhs depth) (FOF.mkBound_helper nm rhs depth)
  | .or lhs rhs => .or (FOF.mkBound_helper nm lhs depth) (FOF.mkBound_helper nm rhs depth)
  | .imp lhs rhs =>  .imp (FOF.mkBound_helper nm lhs depth) (FOF.mkBound_helper nm rhs depth)
  | .exists var body' => .exists var <| FOF.mkBound_helper nm body' depth.succ
  | .forall var body' => .forall var  <| FOF.mkBound_helper nm body' depth.succ

/-- Given an expression `body : FOF`, build the existentially quantified version
  where the free variable `nm` is replaced in `body` with the right deBruijn index. -/
@[match_pattern]
def FOF.mkEx (nm : Lean.Name) (body : FOF) : FOF :=
  .exists nm <| FOF.mkBound_helper nm body 0

/-- Given an expression `body : FOF`, build the universially quantified version
  where the free variable `nm` is replaced in `body` with the right deBruijn index. -/
def FOF.mkForall (nm : Lean.Name) (body : FOF) : FOF :=
  .forall nm <| FOF.mkBound_helper nm body 0

/-- Replace `bound k` with `free x`. -/
def Var.rebind (x : Lean.Name) (k : Nat): Var → Var
  | bound n => if n = k then free x else bound n
  | free y => free y

/-- Apply `Var.rebind` throughout formula, replacing `bound k` with `free z`. -/
def FOF.rebind (z : Lean.Name) (k : Nat) : FOF → FOF
  | pred p world => pred p (world.rebind z k)
  | rel r x y => rel r (x.rebind z k) (y.rebind z k)
  | top => top
  | not φ => not (φ.rebind z k)
  | and φ₁ φ₂ => and (φ₁.rebind z k) (φ₂.rebind z k)
  | or φ₁ φ₂ => or (φ₁.rebind z k) (φ₂.rebind z k)
  | imp φ₁ φ₂ => imp (φ₁.rebind z k) (φ₂.rebind z k)
  | .exists varName φ =>
      if varName = z
      then .exists varName φ -- leave as it is
      else .exists varName (φ.rebind z (k+1))
  | .forall varName φ =>
      if varName = z
      then .forall varName φ -- leave as it is
      else .forall varName (φ.rebind z (k+1))

def intoQuantifier : FOF → Except String FOF
  | .forall nm body => .ok <| FOF.rebind nm 0 body
  | .exists nm body => .ok <| FOF.rebind nm 0 body
  | f => .error s!"{repr f} is not a quantifier"

def destructureQuantifier : FOF → Except String (Lean.Name × FOF)
  | .forall nm body => .ok (nm, body.rebind nm 0)
  | .exists nm body => .ok (nm, body.rebind nm 0)
  | f => .error s!"{repr f} is not a quantifier"

/-- Given a quantifier `(.forall nm body)` or `(.ex nm body)`, transformes
 the bound variable in body (`(.bound 0)`) to the free variable `(.free nm)`.

 Assumes the expression is a quantifier.  If the given `FOF` is not a quantifier,
it returns a garbage default expression.  -/
def destructureQuantifier' : FOF → (Lean.Name × FOF)
  | .forall nm body => (nm, body.rebind nm 0)
  | .exists nm body => (nm, body.rebind nm 0)
  | f => (`annonymous, f)

theorem destructureQuantifier_ok_eq_destructureQuantifier' (f : FOF) (body : FOF) (nm : Lean.Name) :
  destructureQuantifier f = (.ok (nm, body)) → destructureQuantifier' f = (nm, body) := by
  cases f <;> grind [destructureQuantifier, destructureQuantifier']


def Var.nameIn (v : Var) (nm : Lean.Name) : Prop :=
  match v with
    | .bound _ => False
    | .free nm' => nm = nm'

instance : Membership Lean.Name Var := ⟨Var.nameIn⟩

instance (v : Var) (nm : Lean.Name) : Decidable <| Var.nameIn v nm :=
  match v with
    | .bound _ => isFalse (fun a ↦ a)
    | .free nm' => if h : nm = nm' then isTrue h else isFalse h


namespace FOF

/--
Decides wether the free variable `nm` appears in the expression `f`.
Note that does not count bound variables in quantifiers.  -/
def nameIn (f : FOF) (nm : Lean.Name) : Prop :=
  match f with
    | .pred _ world => nm ∈ world
    | .rel _ x y => nm ∈ x ∨ nm ∈ y
    | .top => False
    | .not f' => FOF.nameIn f' nm
    | .and f₁ f₂ => FOF.nameIn f₁ nm ∨ FOF.nameIn f₂ nm
    | .or f₁ f₂ => FOF.nameIn f₁ nm ∨ FOF.nameIn f₂ nm
    | .imp f₁ f₂ => FOF.nameIn f₁ nm ∨ FOF.nameIn f₂ nm
    | .exists _ f' => FOF.nameIn f' nm
    | .forall _ f' => FOF.nameIn f' nm

def nameIn_decide (f : FOF) (nm : Lean.Name) : Decidable (FOF.nameIn f nm)  :=
  match f with
    | .pred _ world => if h : Var.nameIn world nm then isTrue h else isFalse h
    | .rel _ x y =>
      if hx : Var.nameIn x nm then isTrue (Or.inl hx)
      else
        if hy : Var.nameIn y nm then isTrue (Or.inr hy)
        else isFalse (by simp [nameIn]; exact ⟨hx, hy⟩)
    | .top => isFalse (by simp [FOF.nameIn])
    | .not f => match FOF.nameIn_decide f nm with
      | isTrue h => isTrue h
      | isFalse h => isFalse h
    | .and x y => match FOF.nameIn_decide x nm with
      | isTrue hx => isTrue <| Or.inl hx
      | isFalse hx => match FOF.nameIn_decide y nm with
        | isTrue hy => isTrue <| Or.inr hy
        | isFalse hy => isFalse (by simp [FOF.nameIn]; exact ⟨hx,hy⟩)
    | .or x y => match FOF.nameIn_decide x nm with
      | isTrue hx => isTrue <| Or.inl hx
      | isFalse hx => match FOF.nameIn_decide y nm with
        | isTrue hy => isTrue <| Or.inr hy
        | isFalse hy => isFalse (by simp [FOF.nameIn]; exact ⟨hx,hy⟩)
    | .imp x y => match FOF.nameIn_decide x nm with
      | isTrue hx => isTrue <| Or.inl hx
      | isFalse hx => match FOF.nameIn_decide y nm with
        | isTrue hy => isTrue <| Or.inr hy
        | isFalse hy => isFalse (by simp [FOF.nameIn]; exact ⟨hx,hy⟩)
    | .forall _ φ => match FOF.nameIn_decide φ nm with
      | isTrue h => isTrue h
      | isFalse h => isFalse h
    | .exists _ φ => match FOF.nameIn_decide φ nm with
      | isTrue h => isTrue h
      | isFalse h => isFalse h

instance : Membership Lean.Name FOF := ⟨FOF.nameIn⟩

instance (f : FOF) (nm : Lean.Name) : Decidable (FOF.nameIn f nm) := FOF.nameIn_decide f nm
instance (f : FOF) (nm : Lean.Name) : Decidable (nm ∈ f) := inferInstanceAs (Decidable (FOF.nameIn f nm))

theorem rebind_eq_size (nm : Lean.Name) (n : Nat) (φ : FOF) :
  size φ = size (φ.rebind nm n)  := by
  induction φ generalizing n
  any_goals simp [FOF.rebind, FOF.size]; try grind
  · case «exists» v φ ih =>
      by_cases v = nm
      case pos hv => simp [hv, size]
      case neg hnv =>
        simp [hnv, size]; rw [ih]
  · case «forall» v φ ih =>
      by_cases v = nm
      case pos hv => simp [hv, size]
      case neg hnv =>
        simp [hnv, size]; rw [ih]

theorem mkBound_helper_notin_eq {v : Lean.Name} {φ : FOF} (n : Nat) :
   v ∉ φ → FOF.mkBound_helper v φ n = φ := by
  intro hv
  induction φ generalizing n <;> simp_all [FOF.mkBound_helper, FOF.nameIn, Membership.mem]
  · case pred p w =>
    cases w <;> simp_all [Var.nameIn]
  · case rel _ x y => cases x <;> cases y <;> simp_all [Var.nameIn]

theorem mkBound_helper_rebind (v : Lean.Name) (φ : FOF) (n : Nat) :
  v ∉ φ → FOF.mkBound_helper v (FOF.rebind v n φ) n = φ := by
  intro hv
  induction φ generalizing n
  all_goals simp [FOF.mkBound_helper, FOF.rebind]; try grind
  · case pred p w =>
      cases w <;> simp [Var.rebind]
      · case bound idx => by_cases hidxn : idx = n <;> grind
      · case free nm'  => simp [Membership.mem, FOF.nameIn, Var.nameIn] at hv; assumption
  · case rel _ x y =>
      cases x <;> cases y <;> simp [Var.rebind]
      · case bound.bound idx₁ idx₂ => by_cases hidx₁ : idx₁ = n <;> grind
      · case bound.free idx nm' =>
          simp [Membership.mem, FOF.nameIn, Var.nameIn] at hv
          by_cases idx = n <;> grind
      · case free.bound nm' idx =>
          simp [Membership.mem, FOF.nameIn, Var.nameIn] at hv
          by_cases idx = n <;> grind
      · case free.free nm' nm''  => simp [Membership.mem, FOF.nameIn, Var.nameIn] at hv; assumption
  · case not a ih =>
      simp [Membership.mem, FOF.nameIn] at hv
      specialize ih n hv; assumption
  · case and x y ihx ihy =>
      simp [Membership.mem, FOF.nameIn] at hv
      specialize ihx n hv.1; specialize ihy n hv.2
      exact ⟨ihx,ihy⟩
  · case or x y ihx ihy =>
      simp [Membership.mem, FOF.nameIn] at hv
      specialize ihx n hv.1; specialize ihy n hv.2
      exact ⟨ihx,ihy⟩
  · case imp x y ihx ihy =>
      simp [Membership.mem, FOF.nameIn] at hv
      specialize ihx n hv.1; specialize ihy n hv.2
      exact ⟨ihx,ihy⟩
  · case «exists» v' φ ih =>
      by_cases hvv' : v' = v
      · case pos =>
          simp [hvv', FOF.mkBound_helper]
          simp [Membership.mem, FOF.nameIn] at hv
          apply mkBound_helper_notin_eq (n+1) hv
      · case neg =>
          simp [hvv', FOF.mkBound_helper]
          simp [Membership.mem, FOF.nameIn] at hv
          apply ih (n+1) hv
  · case «forall» v' φ ih =>
      by_cases hvv' : v' = v
      · case pos =>
          simp [hvv', FOF.mkBound_helper]
          simp [Membership.mem, FOF.nameIn] at hv
          specialize ih (n+1) hv
          apply mkBound_helper_notin_eq (n+1) hv
      · case neg =>
          simp [hvv', FOF.mkBound_helper]
          simp [Membership.mem, FOF.nameIn] at hv
          apply ih (n+1) hv


theorem mkEx_destructureQuantifier'_eq_exists (v : Lean.Name) (φ : FOF) :
   v ∉ φ → FOF.mkEx (destructureQuantifier' (FOF.exists v φ)).fst
   (destructureQuantifier' (FOF.exists v φ)).snd = FOF.exists v φ := by
   grind [destructureQuantifier', FOF.mkEx, mkBound_helper_rebind]

theorem mkForall_destructureQuantifier'_eq_forall (v : Lean.Name) (φ : FOF) :
   v ∉ φ → FOF.mkForall (destructureQuantifier' (FOF.forall v φ)).fst
   (destructureQuantifier' (FOF.forall v φ)).snd = FOF.forall v φ := by
   grind [destructureQuantifier', FOF.mkForall, mkBound_helper_rebind]

def wellFormedVar : FOF → Prop
  | .pred _ _ => True
  | .rel _ _ _ => True
  | .top => True
  | .not x => x.wellFormedVar
  | .and x y => x.wellFormedVar ∧ y.wellFormedVar
  | .or x y => x.wellFormedVar ∧ y.wellFormedVar
  | .imp x y => x.wellFormedVar ∧ y.wellFormedVar
  | .exists v φ => v ∉ φ ∧ φ.wellFormedVar
  | .forall v φ => v ∉ φ ∧ φ.wellFormedVar

def decide_wellFormedVar (φ : FOF) : Decidable φ.wellFormedVar := match φ with
  | .pred _ _ => isTrue (True.intro)
  | .rel _ _ _ => isTrue (True.intro)
  | .top => isTrue (True.intro)
  | .not φ => match φ.decide_wellFormedVar with
    | isTrue h => isTrue h
    | isFalse h => isFalse h
  | .and x y => match x.decide_wellFormedVar with
    | isFalse _ => isFalse (by intro ⟨hc₁, hc₂⟩; contradiction)
    | isTrue hx => match y.decide_wellFormedVar with
      | isFalse _ => isFalse (by intro ⟨hc₁, hc₂⟩; contradiction)
      | isTrue hy => isTrue ⟨hx,hy⟩
  | .or x y => match x.decide_wellFormedVar with
    | isFalse _ => isFalse (by intro ⟨hc₁, hc₂⟩; contradiction)
    | isTrue hx => match y.decide_wellFormedVar with
      | isFalse _ => isFalse (by intro ⟨hc₁, hc₂⟩; contradiction)
      | isTrue hy => isTrue ⟨hx,hy⟩
  | .imp x y => match x.decide_wellFormedVar with
    | isFalse _ => isFalse (by intro ⟨hc₁, hc₂⟩; contradiction)
    | isTrue hx => match y.decide_wellFormedVar with
      | isFalse _ => isFalse (by intro ⟨hc₁, hc₂⟩; contradiction)
      | isTrue hy => isTrue ⟨hx,hy⟩
  | .exists v φ => if h : v ∉ φ then
    match φ.decide_wellFormedVar with
      | isTrue hφ => isTrue ⟨h,hφ⟩
      | isFalse hφ => isFalse (by intro ⟨hc₁,hc₂⟩; contradiction)
      else isFalse (by intro ⟨hc₁,hc₂⟩; contradiction)
  | .forall v φ => if h : v ∉ φ then
    match φ.decide_wellFormedVar with
      | isTrue hφ => isTrue ⟨h,hφ⟩
      | isFalse hφ => isFalse (by intro ⟨hc₁,hc₂⟩; contradiction)
      else isFalse (by intro ⟨hc₁,hc₂⟩; contradiction)

instance (φ : FOF) : Decidable φ.wellFormedVar := φ.decide_wellFormedVar

theorem mkBound_helper_nm_notin_body (nm : Lean.Name) (depth : Nat) (body : FOF) :
   nm ∉ FOF.mkBound_helper nm body depth := by
     induction body generalizing depth <;>
     simp [FOF.mkBound_helper, Membership.mem, FOF.nameIn, Var.nameIn]
     · case pred pred world =>
        cases world
        · case bound deBruijnIdx =>  simp
        · case free nm' =>
           by_cases hnm : (nm = nm')
           all_goals simp [hnm]
     · case rel _ x y =>
        cases x <;> cases y
        · case bound.bound idx₁ idx₂ =>  simp
        · case bound.free idx₁ nm' =>
           by_cases hnm : (nm = nm')
           all_goals simp [hnm]
        · case free.bound nm' idx₂ =>
           by_cases hnm : (nm = nm')
           all_goals simp [hnm]
        · case free.free nm' nm'' =>
            by_cases hnm' : (nm' = nm) <;> by_cases hnm'' : (nm'' = nm)
            all_goals grind
     any_goals simp_all [Membership.mem]

theorem notin_rebind_notin {v v' : Lean.Name} {φ : FOF} {n : Nat}:
  v ≠ v' → v ∉ φ → v ∉ FOF.rebind v' n φ := by
    intro hv hnotin
    induction φ generalizing n
    · case pred _ w =>
        simp_all [Membership.mem, FOF.nameIn, FOF.rebind, Var.nameIn]
        cases w
        · case bound n' => simp_all [Var.rebind]; by_cases n' = n <;> grind
        · case free nm => simp_all [Var.rebind]
    · case rel _ x y =>
        simp_all [Membership.mem, FOF.nameIn, FOF.rebind, Var.nameIn]
        cases x <;> cases y
        · case bound.bound n' n'' =>
            by_cases (n' = n) <;> by_cases (n'' = n) <;> simp_all [Var.rebind]
        · case bound.free n' _ => by_cases (n' = n) <;> simp_all [Var.rebind]
        · case free.bound _ n' => by_cases (n' = n) <;> simp_all [Var.rebind]
        · case free.free => simp_all [Var.rebind]
    · case top => simp_all [Membership.mem, FOF.nameIn, FOF.rebind]
    · case not => simp_all [Membership.mem, FOF.nameIn, FOF.rebind]
    · case and => simp_all [Membership.mem, FOF.nameIn, FOF.rebind]
    · case or => simp_all [Membership.mem, FOF.nameIn, FOF.rebind]
    · case imp => simp_all [Membership.mem, FOF.nameIn, FOF.rebind]
    · case «exists» v'' φ' ih =>
        by_cases hv' : (v = v') <;> by_cases hv'' : (v'' = v) <;> try grind
        simp [Membership.mem, FOF.nameIn] at hnotin
        · case pos =>
            simp [hv'', FOF.rebind, hv', Membership.mem, FOF.nameIn]
            apply ih
            apply hnotin
        · case neg =>
            by_cases hv''' : (v' = v'') <;> simp [FOF.rebind, Membership.mem, *, FOF.nameIn]
            · case pos =>
               simp [Membership.mem, FOF.nameIn] at hnotin
               exact hnotin
            · case neg =>
               have hv'''' : v'' ≠ v' := by grind
               simp [hv'''']
               apply ih
               simp [Membership.mem, FOF.nameIn] at hnotin
               apply hnotin
    · case «forall» v'' φ' ih =>
        by_cases hv' : (v = v') <;> by_cases hv'' : (v'' = v) <;> try grind
        simp [Membership.mem, FOF.nameIn] at hnotin
        · case pos =>
            simp [hv'', FOF.rebind, hv', Membership.mem, FOF.nameIn]
            apply ih
            apply hnotin
        · case neg =>
            by_cases hv''' : (v' = v'') <;> simp [FOF.rebind, Membership.mem, *, FOF.nameIn]
            · case pos =>
               simp [Membership.mem, FOF.nameIn] at hnotin
               exact hnotin
            · case neg =>
               have hv'''' : v'' ≠ v' := by grind
               simp [hv'''']
               apply ih
               simp [Membership.mem, FOF.nameIn] at hnotin
               apply hnotin

theorem ex_var_notin_rebind {φ : FOF} (v : Lean.Name) (n : Nat) :
  φ.wellFormedVar → (FOF.rebind v n φ).wellFormedVar := by
  intro h
  induction φ generalizing n
  all_goals simp_all [FOF.wellFormedVar, FOF.rebind]
  · case «exists» v' φ' ih =>
      by_cases hvv' : v' = v
      · case pos => simp [hvv', FOF.wellFormedVar]; rw [← hvv']; assumption
      · case neg =>
          simp_all [FOF.wellFormedVar]
          apply notin_rebind_notin hvv' h.1
  · case «forall» v' φ' ih =>
      by_cases hvv' : v' = v
      · case pos => simp [hvv', FOF.wellFormedVar]; rw [← hvv']; assumption
      · case neg =>
          simp_all [FOF.wellFormedVar]
          apply notin_rebind_notin hvv' h.1

theorem ex_wfVar_destructureQuantifier' (v : Lean.Name) (φ : FOF) :
  φ.wellFormedVar → (destructureQuantifier' (.exists v φ)).2.wellFormedVar := by
  intro h
  simp [destructureQuantifier']
  induction φ
  any_goals grind [FOF.wellFormedVar, FOF.rebind]
  · case «exists» v' φ' ih =>
      simp [FOF.wellFormedVar] at h
      by_cases hvv' : v' = v
      · case pos => simp [FOF.rebind, hvv', FOF.wellFormedVar]; rw [← hvv']; assumption
      · case neg =>
        simp [FOF.rebind, hvv', FOF.wellFormedVar]
        constructor
        · case left => apply notin_rebind_notin hvv' h.1
        · case right =>
            apply ex_var_notin_rebind
            apply h.2
  · case «forall» v' φ' ih =>
      simp [FOF.wellFormedVar] at h
      by_cases hvv' : v' = v
      · case pos => simp [FOF.rebind, hvv', FOF.wellFormedVar]; rw [← hvv']; assumption
      · case neg =>
        simp [FOF.rebind, hvv', FOF.wellFormedVar]
        constructor
        · case left => apply notin_rebind_notin hvv' h.1
        · case right =>
            apply ex_var_notin_rebind
            apply h.2

theorem notin_body_notin_mkBound_helper {v nm : Lean.Name} {depth : Nat} {body : FOF} :
  v ∉ body → nm ≠ v → v ∉ FOF.mkBound_helper nm body depth := by
    intro hv hvnm
    induction body generalizing depth
    <;> simp_all [FOF.mkBound_helper, Membership.mem, FOF.nameIn, Var.nameIn]
    any_goals grind

theorem forall_wfVar_destructureQuantifier' (v : Lean.Name) (φ : FOF) :
  φ.wellFormedVar → (destructureQuantifier' (.forall v φ)).2.wellFormedVar := by
  intro h
  simp [destructureQuantifier']
  induction φ
  any_goals grind [FOF.wellFormedVar, FOF.rebind]
  · case «exists» v' φ' ih =>
      simp [FOF.wellFormedVar] at h
      by_cases hvv' : v' = v
      · case pos => simp [FOF.rebind, hvv', FOF.wellFormedVar]; rw [← hvv']; assumption
      · case neg =>
        simp [FOF.rebind, hvv', FOF.wellFormedVar]
        constructor
        · case left => apply notin_rebind_notin hvv' h.1
        · case right =>
            apply ex_var_notin_rebind
            apply h.2
  · case «forall» v' φ' ih =>
      simp [FOF.wellFormedVar] at h
      by_cases hvv' : v' = v
      · case pos => simp [FOF.rebind, hvv', FOF.wellFormedVar]; rw [← hvv']; assumption
      · case neg =>
        simp [FOF.rebind, hvv', FOF.wellFormedVar]
        constructor
        · case left => apply notin_rebind_notin hvv' h.1
        · case right =>
            apply ex_var_notin_rebind
            apply h.2

end FOF

abbrev FO := { φ : FOF // φ.wellFormedVar }

instance : Membership Lean.Name FO where
  mem f v := f.val.nameIn v

namespace FO

theorem mkBound_helper_wfVar {v : Lean.Name} {φ : FO} {n : Nat} :
  (FOF.mkBound_helper v φ.val n).wellFormedVar := by
  cases φ
  · case mk val property =>
    induction val generalizing n
    any_goals grind [FOF.wellFormedVar, FOF.mkBound_helper]
    · case «exists» v' φ ih =>
        simp [FOF.wellFormedVar, FOF.mkBound_helper]
        simp [FOF.wellFormedVar] at property
        by_cases hv : v = v'
        · case pos =>
            subst hv
            constructor
            exact FOF.mkBound_helper_nm_notin_body v (n + 1) φ
            apply ih property.2
        · case neg =>
            constructor
            apply FOF.notin_body_notin_mkBound_helper property.1 hv
            apply ih property.2
    · case «forall» v' φ ih =>
        simp [FOF.wellFormedVar, FOF.mkBound_helper]
        simp [FOF.wellFormedVar] at property
        by_cases hv : v = v'
        · case pos =>
            subst hv
            constructor
            exact FOF.mkBound_helper_nm_notin_body v (n + 1) φ
            apply ih property.2
        · case neg =>
            constructor
            apply FOF.notin_body_notin_mkBound_helper property.1 hv
            apply ih property.2

@[match_pattern]
def P : Lean.Name → Var → FO := fun p w => ⟨FOF.pred p w, True.intro⟩
@[match_pattern]
def R : Rel → Var → Var → FO := fun r x y => ⟨FOF.rel r x y, True.intro⟩
@[match_pattern]
def top : FO := ⟨FOF.top, True.intro⟩
@[match_pattern]
def not : FO → FO := fun ⟨φ, h⟩ => ⟨.not φ, h⟩
@[match_pattern]
def and : FO → FO → FO := fun ⟨x, hx⟩ ⟨y, hy⟩ => ⟨.and x y, ⟨hx, hy⟩⟩
@[match_pattern]
def or : FO → FO → FO := fun ⟨x, hx⟩ ⟨y, hy⟩ => ⟨.or x y, ⟨hx, hy⟩⟩
@[match_pattern]
def imp : FO → FO → FO := fun ⟨x, hx⟩ ⟨y, hy⟩ => ⟨.imp x y, ⟨hx, hy⟩⟩
@[match_pattern]
def mkEx (v : Lean.Name) (φ : FO) : FO :=
  ⟨FOF.mkEx v φ.val, by
    simp [FOF.wellFormedVar]
    constructor
    apply FOF.mkBound_helper_nm_notin_body v 0 φ.val
    apply mkBound_helper_wfVar⟩
@[match_pattern]
def mkForall (v : Lean.Name) (φ : FO) : FO :=
  ⟨FOF.mkForall v φ.val, by
    simp [FOF.mkForall, FOF.wellFormedVar]
    constructor
    apply FOF.mkBound_helper_nm_notin_body v 0 φ.val
    apply mkBound_helper_wfVar⟩

@[induction_eliminator]
def rec {motive : FO → Sort u}
  (P : (pred : Lean.Name) → (world : Var) → motive (FO.P pred world))
  (R : (r : Rel) → (x y : Var) → motive (FO.R r x y))
  (top :  motive FO.top)
  (not : (a : FO) → motive a → motive a.not)
  (and : (a b : FO) → motive a → motive b → motive (a.and b))
  (or : (a b : FO) → motive a → motive b → motive (a.or b))
  (imp : (a b : FO) → motive a → motive b → motive (a.imp b))
  (ex : (varName : Lean.Name) → (φ : FO) →  motive φ → motive (FO.mkEx varName φ))
  (fa : (varName : Lean.Name) → (φ : FO) →  motive φ → motive (FO.mkForall varName φ)) :
   (t : FO) → motive t
   | .P pred world => P pred world
   | .R r x y => R r x y
   | .top => top
   | .not ⟨a,h⟩ => not ⟨a,h⟩ («rec» P R top not and or imp ex fa ⟨a,h⟩)
   | ⟨.and x y, ⟨hx, hy⟩⟩ => and ⟨x,hx⟩ ⟨y,hy⟩ («rec» P R top not and or imp ex fa ⟨x,hx⟩) («rec» P R top not and or imp ex fa ⟨y,hy⟩)
   | ⟨.or x y, ⟨hx, hy⟩⟩ => or ⟨x,hx⟩ ⟨y,hy⟩ («rec» P R top not and or imp ex fa ⟨x,hx⟩) («rec» P R top not and or imp ex fa ⟨y,hy⟩)
   | ⟨.imp x y, ⟨hx, hy⟩⟩ => imp ⟨x,hx⟩ ⟨y,hy⟩ («rec» P R top not and or imp ex fa ⟨x,hx⟩) («rec» P R top not and or imp ex fa ⟨y,hy⟩)
   | (Subtype.mk (FOF.exists v φ) (And.intro hv hwf)) =>
      let free := destructureQuantifier' (FOF.exists v φ)
      let foo := FOF.ex_wfVar_destructureQuantifier' v φ hwf
      have hMkExWf : free.2.wellFormedVar := by
        simp [free]
        exact FOF.ex_wfVar_destructureQuantifier' v φ hwf
      let motiveMkEx := ex v ⟨free.2,_⟩ («rec» P R top not and or imp ex fa ⟨free.2,hMkExWf⟩)
      have heq : mkEx free.fst ⟨free.snd, _⟩ = ⟨FOF.exists v φ, _⟩ := by
        unfold mkEx
        simp [free]
        rw [FOF.mkEx_destructureQuantifier'_eq_exists v φ hv]
      heq ▸ motiveMkEx
   | (Subtype.mk (FOF.forall v φ) (And.intro hv hwf)) =>
      let free := destructureQuantifier' (FOF.forall v φ)
      let foo := FOF.forall_wfVar_destructureQuantifier' v φ hwf
      have hMkExWf : free.2.wellFormedVar := by
        simp [free]
        exact FOF.ex_wfVar_destructureQuantifier' v φ hwf
      let motiveMkEx := fa v ⟨free.2,_⟩ («rec» P R top not and or imp ex fa ⟨free.2,hMkExWf⟩)
      have heq : mkForall free.fst ⟨free.snd, _⟩ = ⟨FOF.forall v φ, _⟩ := by
        unfold mkForall
        simp [free]
        rw [FOF.mkForall_destructureQuantifier'_eq_forall v φ hv]
      heq ▸ motiveMkEx
  termination_by φ => φ.val.size
  decreasing_by
    all_goals (simp [FOF.size]; try omega)
    · unfold destructureQuantifier'; simp; rw [FOF.rebind_eq_size v 0 φ]; omega
    · unfold destructureQuantifier'; simp; rw [FOF.rebind_eq_size v 0 φ]; omega
