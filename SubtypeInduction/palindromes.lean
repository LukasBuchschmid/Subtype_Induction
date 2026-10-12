
import SubtypeInduction.What_A_View
import SubtypeInduction.dummy_command
import SubtypeInduction.Extra_Arguments_Exercise
import SubtypeInduction.Fun_with_Funct
import Mathlib.Logic.Equiv.Defs


def List.strongRec {α : Type} {motive : List α → Sort u}
  (l : List α)
  (step : (n : List α) → ((m : List α) → m.length < n.length → motive m) → motive n) :
  motive l :=
  step l (fun m _ => List.strongRec m step)
termination_by l.length

def List.snoc {α : Type} (a : α) (l : List α) : List α := l ++ [a]

theorem ListSnocLemma {α : Type} (a : α) (l : List α) : (a :: l).reverse = l.reverse ++ [a] := by
  simp

theorem ListSnocConsLemma {α : Type} (a : α) (l : List α) : l ++ [a] = (a :: l.reverse).reverse := by
  simp

def List.snocRec {α : Type} (motive : List α → Sort u) (nil : motive [])
  (snoc : (a : α) → (l : List α) → (motive l) → motive (List.snoc a l)) (t : List α)
  : motive t :=

      let MSmall : (n : List α) → ((m : List α) → m.length < n.length → motive m) → motive n :=
        fun n =>
        match n with
          | [] => fun pro => nil
          | e :: l => by
              intro ih
              let baseList := (List.tail (α := α) ((e :: l).reverse)).reverse
              let baseTerm := List.head (α := α) ((e :: l).reverse) (by simp)
              let smaller : baseList.length < (e :: l).length := by
                unfold baseList
                simp
              let BaseCase := ih baseList smaller
              let eq : (e :: l) = (List.snoc baseTerm baseList) := by
                unfold baseList baseTerm List.snoc
                simp
                rw [<- ListSnocLemma]
                simp
              exact eq.symm ▸ snoc baseTerm baseList BaseCase
    List.strongRec t MSmall


def List.snocRec2 {α : Type} (motive : List α → Sort u) (nil : motive [])
  (snoc : (a : α) → (l : List α) → (motive l) → motive (List.snoc a l)) (t : List α)
  : motive t :=
    match eq : t.reverse with
      | [] => by
            have t_eq : t = [] := by
              rw [← List.reverse_reverse t]
              rw [eq]
              rfl
            exact t_eq.symm ▸ nil
      | e :: l => by
            let prev := snocRec2 motive nil snoc l.reverse
            have t_eq : t = List.snoc e l.reverse := by
              have h1 : t = t.reverse.reverse := by simp
              rw [h1]
              rw[eq]
              rw [ListSnocLemma]
              rfl
            exact t_eq ▸ snoc e l.reverse prev
termination_by t.length
decreasing_by
  have h : t.reverse.length = (e :: l).length := by rw [eq]
  simp [List.length_reverse] at h ⊢
  omega



def IsPalindrome {α : Type} : List α → Prop :=
  fun l => l = l.reverse

def Palindrome {α : Type} := {l : List α // IsPalindrome l}



@[view_ctor]
def Palindrome.nil {α : Type} : Palindrome (α := α) := ⟨[], rfl⟩

@[view_ctor]
def Palindrome.singleton {α : Type} (a : α) : Palindrome (α := α) := ⟨[a], rfl⟩

def PalindromeStep {α : Type} (a : α) (l : List α) : List α :=
  a :: (a :: l).reverse



theorem StepIsPalindrome {α : Type} (a : α) (p : Palindrome (α := α)) : IsPalindrome (PalindromeStep a p.val) := by
  unfold PalindromeStep IsPalindrome
  simp
  exact (p.property).symm

theorem PrevPalindrome {α : Type} (a e : α) (l h : List α) (p1 : IsPalindrome (a :: l)) (eq1 : l.reverse = (e :: h)) : IsPalindrome h := by
  unfold IsPalindrome
  let eq2 : e = a := by
    unfold IsPalindrome at p1
    simp only [ListSnocLemma] at p1
    rw [eq1] at p1
    simp at p1
    exact (p1.1).symm
  let eq3 : l = h ++ [a] := by
    unfold IsPalindrome at p1
    simp only [ListSnocLemma] at p1
    rw [eq1] at p1
    simp at p1
    exact (p1.2)
  let eq4 : IsPalindrome (a :: (h ++ [a])) := by
    rw [<-eq3]
    exact p1
  rw [eq2] at eq1
  rw [eq3] at eq1
  simp at eq1
  exact eq1.symm







@[view_ctor]
def Palindrome.step {α : Type} (a : α) (p : Palindrome (α := α)) : Palindrome (α := α) :=
  ⟨PalindromeStep a p.val, (StepIsPalindrome a p)⟩

def dropStep2 {α : Type} (p : Palindrome (α := α)) : Palindrome (α := α) :=
 match p with
 | .nil => .nil
 | .singleton a => .step a .nil
 | _ => .nil

def Palindrome.rec {α : Type} (motive : Palindrome (α := α) → Sort u) (empty : motive Palindrome.nil) (single : (a : α) → motive (Palindrome.singleton a))
  (step : (a : α) → (p : Palindrome) → motive p → motive (Palindrome.step a p)) (t : Palindrome) : motive t :=
    match t with
      | ⟨pal, ppal⟩ =>
        -- let NewMotive (n : List α) (p3 : IsPalindrome n) : Sort u := motive ⟨n, p3⟩
        let SIM : (n : List α) → ((m : List α) → m.length < n.length → (p1 : IsPalindrome m) → motive ⟨m, p1⟩) → (p2 : IsPalindrome n) → motive ⟨n, p2⟩ := by
          intro n ih p2
          match n with
            | [] => exact empty
            | a :: l =>
              match l with
              | [] => exact single a
              | e :: k =>
                match eq1 : (e :: k).reverse with
                | [] => simp at eq1
                | e_rev :: h_rev =>
                  let new_p_p := PrevPalindrome a e_rev (e :: k) h_rev p2 eq1
                  have h_len : h_rev.length < (a :: e :: k).length := by
                    have h1 : (e :: k).reverse.length = (e_rev :: h_rev).length := by rw [eq1]
                    simp only [List.length_reverse, List.length_cons] at h1 ⊢
                    omega
                  let prev := ih h_rev h_len new_p_p
                  let test := step a ⟨h_rev, new_p_p⟩ prev
                  let eq2 : a :: (e :: k) = (Palindrome.step a ⟨h_rev, new_p_p⟩).val := by
                    unfold Palindrome.step
                    unfold PalindromeStep
                    simp
                    unfold IsPalindrome at p2
                    rw [ListSnocLemma] at p2
                    rw [eq1] at p2
                    rw [new_p_p] at p2
                    simp [List.cons_append] at p2
                    exact p2.2
                  let test2 := step a ⟨h_rev, new_p_p⟩ prev
                  have eq_sub : ⟨a :: e :: k, p2⟩ = Palindrome.step a ⟨h_rev, new_p_p⟩ :=
                    Subtype.ext eq2
                  exact eq_sub.symm ▸ test
        let NewMotive (x : List α) : Sort u := (p3 : IsPalindrome x) → motive ⟨x, p3⟩
        List.strongRec (motive := NewMotive) pal SIM ppal


@[view_pos]
theorem IsPositivePalindromeCons {α : Type} (a : α) (p : Palindrome (α := α)) :
    p.val.length < (Palindrome.step a p).val.length := by
  unfold Palindrome.step PalindromeStep
  simp
  omega

@[view_cases]
def palindrome_cases {α : Type} (x : Palindrome (α := α)) :
    PSum (x = Palindrome.nil)
         (PSum (Σ' a : α, x = Palindrome.singleton a)
               (Σ' a : α, Σ' p : Palindrome (α := α), x = Palindrome.step a p)) :=
  match x with
  | ⟨[], h⟩ => PSum.inl (Subtype.ext rfl)
  | ⟨a :: [], h⟩ => PSum.inr <| PSum.inl ⟨a, Subtype.ext rfl⟩
  | ⟨a :: e :: k, h⟩ =>
    match eq1 : (e :: k).reverse with
    | [] => by simp at eq1
    | e_rev :: h_rev =>
      let new_p_p := PrevPalindrome a e_rev (e :: k) h_rev h eq1
      let prev_pal : Palindrome (α := α) := ⟨h_rev, new_p_p⟩
      have eq2 : a :: (e :: k) = (Palindrome.step a prev_pal).val := by
        unfold Palindrome.step PalindromeStep
        simp
        unfold IsPalindrome at h
        rw [ListSnocLemma] at h
        rw [eq1] at h
        rw [new_p_p] at h
        simp [List.cons_append] at h
        exact h.2
      PSum.inr <| PSum.inr ⟨a, ⟨prev_pal, Subtype.ext eq2⟩⟩


@[instance_reducible, view_rel]
def Palindrome.wfRel {α : Type} : WellFoundedRelation (Palindrome (α := α)) :=
  measure (fun p => p.val.length)

#What_A_View Palindrome

#check Palindrome.recView

-- ============================================================================
-- Persistent Environment Extension: Inspection & Queries
-- ============================================================================

-- 1. Inspect registered view metadata using the new `#view_info` command:
#view_info Palindrome

#Build_Multi_Arg Nat, String, Bool

#Build_Dummy Palindrome

noncomputable def Palindrome.strongRecOn {α : Type} {motive : Palindrome (α := α) → Sort u}
  (t : Palindrome (α := α))
  (ind : (x : Palindrome (α := α)) → ((y : Palindrome (α := α)) → y.val.length < x.val.length → motive y) → motive x) : motive t :=
  WellFounded.fix (measure (fun x => x.val.length)).wf ind t

noncomputable def Palindrome.recNew {α : Type} {motive : Palindrome (α := α) → Sort u}
  (empty : motive Palindrome.nil)
  (single : (a : α) → motive (Palindrome.singleton a))
  (step : (a : α) → (p : Palindrome (α := α)) → motive p → motive (Palindrome.step a p))
  (t : Palindrome (α := α)) : motive t :=
    let ind : (x : Palindrome (α := α)) → ((y : Palindrome (α := α)) → y.val.length < x.val.length → motive y) → motive x := by
      intro x ih
      let prev := palindrome_cases x
      match prev with
      | PSum.inl h_eq =>
        exact h_eq ▸ empty
      | PSum.inr <| PSum.inl ⟨a, h_eq⟩ =>
        exact h_eq ▸ single a
      | PSum.inr <| PSum.inr ⟨a, ⟨p, h_eq⟩⟩ =>
        let pos_p : p.val.length < x.val.length := by
          rw [h_eq]
          exact IsPositivePalindromeCons a p
        exact h_eq ▸ step a p (ih p pos_p)

    Palindrome.strongRecOn t ind


-- ============================================================================
-- View-Based Function Definitions (`def_view`) Using Persistent Metadata
-- ============================================================================

-- Thanks to `viewExtension`, `def_view` automatically resolves `Palindrome.nil`,
-- `Palindrome.singleton`, `Palindrome.step`, and `palindrome_cases` from the environment.
-- Specifying `with ... cases ...` is now completely optional!

-- Example 1: Nested pattern match peeling outer layers:
def_view dropStep {α : Type} (p : Palindrome (α := α)) : Palindrome (α := α) :=
  | .nil => .nil
  | .singleton a => .nil
  | .step a (.step b p) => p
  | .step a p => .nil

-- Example 2: Extracting inner palindrome core:
def_view innerPal {α : Type} (p : Palindrome (α := α)) : Palindrome (α := α) :=
  | .nil => .nil
  | .singleton a => .nil
  | .step a p => p

-- Example 3: Extracting boundary characters of the palindrome:
def_view palEnds? {α : Type} (p : Palindrome (α := α)) : Option α :=
  | .nil => none
  | .singleton a => some a
  | .step a p => some a

-- Example 4: Testing depth >= 2 via view pattern matching:
def_view palDepthAtLeast2 {α : Type} (p : Palindrome (α := α)) : Bool :=
  | .nil => false
  | .singleton a => false
  | .step a (.step b p) => true
  | .step a p => false



-- ============================================================================
-- Inductive View of Palindromes & Type Equivalence
-- ============================================================================

/--
The inductive data type mirroring the view constructors for `Palindrome`:
- `nil` corresponds to `Palindrome.nil`
- `singleton a` corresponds to `Palindrome.singleton a`
- `step a v` corresponds to `Palindrome.step a p`
-/
inductive PalindromeView (α : Type) where
  | nil : PalindromeView α
  | singleton : α → PalindromeView α
  | step : α → PalindromeView α → PalindromeView α
deriving Repr, DecidableEq

/--
Canonical mapping from the subtype `Palindrome (α := α)` to the inductive view `PalindromeView α`.
Constructed using the subtype recursor `Palindrome.recView` built for the view.
-/
noncomputable def Palindrome.toView {α : Type} (p : Palindrome (α := α)) : PalindromeView α :=
  Palindrome.recView α
    (fun _ => PalindromeView α)
    PalindromeView.nil
    (fun a => PalindromeView.singleton a)
    (fun a _ ih => PalindromeView.step a ih)
    p

/-! ### Computation Lemmas for `toView` -/

theorem toView_nil {α : Type} : (Palindrome.nil (α := α)).toView = PalindromeView.nil := by
  unfold Palindrome.toView Palindrome.recView
  rw [WellFounded.fix_eq]
  dsimp [palindrome_cases, Palindrome.nil]

theorem toView_singleton {α : Type} (a : α) :
    (Palindrome.singleton a).toView = PalindromeView.singleton a := by
  unfold Palindrome.toView Palindrome.recView
  rw [WellFounded.fix_eq]
  dsimp [palindrome_cases, Palindrome.singleton]

theorem toView_step {α : Type} (a : α) (p : Palindrome (α := α)) :
    (Palindrome.step a p).toView = PalindromeView.step a p.toView := by
  sorry

/-! ### Inverse Direction 1: `toView ∘ toPalindrome = id` -/

def PalindromeView.toPalindrome {α : Type} : PalindromeView α → Palindrome (α := α)
  | .nil => Palindrome.nil
  | .singleton a => Palindrome.singleton a
  | .step a v => Palindrome.step a v.toPalindrome

theorem toView_toPalindrome {α : Type} (v : PalindromeView α) :
    v.toPalindrome.toView = v := by
  induction v with
  | nil =>
    exact toView_nil
  | singleton a =>
    exact toView_singleton a
  | step a v ih =>
    rw [PalindromeView.toPalindrome]
    rw [toView_step]
    rw [ih]

/-! ### Inverse Direction 2: `toPalindrome ∘ toView = id` -/

theorem toPalindrome_toView {α : Type} (p : Palindrome (α := α)) :
    p.toView.toPalindrome = p := by
  induction p using Palindrome.recView with
  | case_1 =>
    rw [toView_nil]
    rfl
  | case_2 a =>
    rw [toView_singleton]
    rfl
  | case_3 a p ih =>
    rw [toView_step]
    unfold PalindromeView.toPalindrome
    rw [ih]

/-! ### Two-way Equivalence: `Palindrome (α := α) ≃ PalindromeView α` -/

/--
Equivalence between the subtype `Palindrome (α := α)` and the inductive datatype `PalindromeView α`.
-/
noncomputable def Palindrome.equivView (α : Type) : Palindrome (α := α) ≃ PalindromeView α where
  toFun := Palindrome.toView
  invFun := PalindromeView.toPalindrome
  left_inv := toPalindrome_toView
  right_inv := toView_toPalindrome

/--
Equivalence in the other direction.
-/
noncomputable def PalindromeView.equivPalindrome (α : Type) : PalindromeView α ≃ Palindrome (α := α) :=
  (Palindrome.equivView α).symm


-- ============================================================================
-- Recursor View (`Palindrome.recView`) Proof Exercises
-- ============================================================================

/--
Unfolds `step` to reveal the symmetric sandwich structure `a :: (p.val ++ [a])`.
Proving this helper makes handling recursive step cases significantly easier.
-/
theorem Palindrome.step_val {α : Type} (a : α) (p : Palindrome (α := α)) :
    (Palindrome.step a p).val = a :: (p.val ++ [a]) := by
    induction p using (Palindrome.recView) with
    | case_1 =>
        dsimp [Palindrome.step, PalindromeStep]
        simp
        rfl
    | case_2 =>
        dsimp [Palindrome.step, PalindromeStep , Palindrome.singleton]
        simp
    | case_3 =>
        expose_names
        dsimp [Palindrome.step, PalindromeStep , Palindrome.singleton] at h ⊢
        simp at h ⊢
        exact h.symm



/-- Mapping any function `f` over a palindrome produces another palindrome. -/
theorem palindrome_map {α β : Type} (f : α → β) (p : Palindrome (α := α)) :
    IsPalindrome (p.val.map f) := by
    induction p using (Palindrome.recView) with
    | case_1 =>
      dsimp [IsPalindrome, Palindrome.nil]
      simp
    | case_2 =>
      dsimp [IsPalindrome, Palindrome.singleton]
      simp
    | case_3 =>
      expose_names
      dsimp [IsPalindrome, Palindrome.step, PalindromeStep] at h ⊢
      simp
      exact h.symm

/-- Structural reversal equality proved strictly via `recView`. -/
theorem palindrome_reverse_eq {α : Type} (p : Palindrome (α := α)) :
    p.val.reverse = p.val := by
    induction p using (Palindrome.recView) with
    | case_1 =>
      dsimp [Palindrome.nil]
    | case_2 =>
      dsimp [Palindrome.singleton]
      simp
    | case_3 =>
      expose_names
      dsimp [Palindrome.step, PalindromeStep]
      simp
      exact h.symm


/--
Round-trip theorem proved using `Palindrome.recView` instead of `Palindrome.rec`.
Connects `#What_A_View` to the `PalindromeView` equivalence above.
-/
theorem toPalindrome_toView_recView {α : Type} (p : Palindrome (α := α)) :
    p.toView.toPalindrome = p := by
    induction p using (Palindrome.recView) with
    | case_1 =>
      rw [toView_nil]
      rfl
    | case_2 a =>
      rw [toView_singleton]
      rfl
    | case_3 a p ih =>
      rw [toView_step]
      unfold PalindromeView.toPalindrome
      rw [ih]

/-- Filtering a palindrome by a predicate preserves palindromicity. -/
theorem palindrome_filter {α : Type} (P : α → Bool) (p : Palindrome (α := α)) :
    IsPalindrome (p.val.filter P) := by
  unfold IsPalindrome
  have h := p.property
  unfold IsPalindrome at h
  rw [← List.filter_reverse]
  rw [← h]

/-- The first and last elements of any palindrome coincide. -/
theorem palindrome_head?_eq_getLast? {α : Type} (p : Palindrome (α := α)) :
    p.val.head? = p.val.getLast? := by
    induction p using (Palindrome.recView) with
    | case_1 =>
      dsimp [Palindrome.nil]
    | case_2 =>
      dsimp [Palindrome.singleton]
    | case_3 =>
      rw [Palindrome.step_val]
      rw [← List.cons_append]
      rw [List.getLast?_concat]
      rfl


theorem palindrome_structure {α : Type} (p : Palindrome (α := α)) :
    (∃ w : List α, p.val = w ++ w.reverse) ∨
    (∃ w : List α, ∃ a : α, p.val = w ++ [a] ++ w.reverse) := by
  induction p using Palindrome.recView with
  | case_1 =>
    left
    use []
    rfl
  | case_2 a =>
    right
    use [], a
    rfl
  | case_3 a p ih =>
    rw [Palindrome.step_val]
    rcases ih with ⟨w, hw⟩ | ⟨w, b, hw⟩
    · left
      use a :: w
      simp [hw]
    · right
      use a :: w, b
      simp [hw]

theorem palindrome_structure_no_view {α : Type} (p : Palindrome (α := α)) :
    (∃ w : List α, p.val = w ++ w.reverse) ∨
    (∃ w : List α, ∃ a : α, p.val = w ++ [a] ++ w.reverse) := by
  exact palindrome_structure p
