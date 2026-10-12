import SubtypeInduction.What_A_View

def IsEvenLen (l : List Nat) : Prop := l.length % 2 = 0

def EvenList := { l : List Nat // IsEvenLen l }

def EvenList.nil : EvenList := ⟨[], by rfl⟩

def EvenList.cons2 (a b : Nat) (l : EvenList) : EvenList :=
  ⟨a :: b :: l.val, by
    have h := l.property
    dsimp [IsEvenLen] at h ⊢
    omega⟩

theorem even_cons2_smaller (a b : Nat) (l : EvenList) :
    l.val.length < (EvenList.cons2 a b l).val.length := by
  dsimp [EvenList.cons2]
  omega

def even_cases (x : EvenList) :
    PSum (x = EvenList.nil)
         (Σ' a : Nat, Σ' b : Nat, Σ' l : EvenList, x = EvenList.cons2 a b l) :=
  match eq : x.val with
  | [] => 
    have h : x = EvenList.nil := Subtype.ext eq
    PSum.inl h
  | [a] => by
    have h := x.property
    rw [eq] at h
    dsimp [IsEvenLen] at h
    contradiction
  | a :: b :: tail =>
    let inner : EvenList := ⟨tail, by
      have h := x.property
      rw [eq] at h
      dsimp [IsEvenLen] at h ⊢
      omega⟩
    have h_eq : x = EvenList.cons2 a b inner := Subtype.ext eq
    PSum.inr ⟨a, b, inner, h_eq⟩

#What_A_View EvenList with
  EvenList.nil EvenList.cons2
plus
  even_cons2_smaller
cases
  even_cases
through
  (measure (fun l => l.val.length))

-- ============================================================================
-- Why is this useful?
-- ============================================================================
--
-- Suppose you want to define a function that pairs up adjacent elements into tuples:
-- `[1, 2, 3, 4] -> [(1,2), (3,4)]`
--
-- If you do this on a normal `List`, the compiler will yell at you because what 
-- happens if the list has an odd number of elements? 
--
-- If you use `EvenList`, the view guarantees you ALWAYS have two elements to grab. 
-- You never have to write a panicking fallback case for a single leftover element!

noncomputable def EvenList.toPairs (l : EvenList) : List (Nat × Nat) := by
  induction l using EvenList.recView with
  | case_1 => exact []
  | case_2 a b _tail ih => exact (a, b) :: ih

theorem toPairs_nil : (EvenList.nil).toPairs = [] := by
  unfold EvenList.toPairs EvenList.recView
  rw [WellFounded.fix_eq]
  dsimp [even_cases, EvenList.nil]

theorem toPairs_cons2 (a b : Nat) (l : EvenList) :
    (EvenList.cons2 a b l).toPairs = (a, b) :: l.toPairs := by
  unfold EvenList.toPairs EvenList.recView
  rw [WellFounded.fix_eq]
  dsimp [even_cases, EvenList.cons2]
  have h_eq : (⟨l.val, by
    have h := l.property
    dsimp [IsEvenLen] at h ⊢
    omega⟩ : EvenList) = l := Subtype.ext rfl
  rw [h_eq]

/-- Exercise: Prove that `toPairs` produces a list exactly half the length of the original.
    (Hint: `induction l using EvenList.recView`) -/
theorem pairs_length_half (l : EvenList) :
    (l.toPairs).length * 2 = l.val.length := by
  induction l using EvenList.recView with
  | case_1 =>
    rw [toPairs_nil]
    rfl
  | case_2 a b tail ih =>
    rw [toPairs_cons2]
    dsimp [EvenList.cons2]
    omega
