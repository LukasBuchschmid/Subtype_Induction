import SubtypeInduction.What_A_View

def IsSorted : List Nat → Prop
  | [] => True
  | _ :: [] => True
  | a :: b :: l => a ≤ b ∧ IsSorted (b :: l)

def SortedList := { l : List Nat // IsSorted l }

def SortedList.nil : SortedList := ⟨[], trivial⟩

def SortedList.cons (a : Nat) (l : SortedList)
    (h : match l.val with | [] => True | b :: _ => a ≤ b) : SortedList :=
  ⟨a :: l.val, by
    rcases l with ⟨val, hval⟩
    match val with
    | [] => exact trivial
    | b :: tail =>
      dsimp [IsSorted]
      exact ⟨h, hval⟩⟩

theorem cons_smaller (a : Nat) (l : SortedList) (h : match l.val with | [] => True | b :: _ => a ≤ b) :
    l.val.length < (SortedList.cons a l h).val.length := by
  dsimp [SortedList.cons]
  omega

def sorted_cases (x : SortedList) :
    PSum (x = SortedList.nil)
         (Σ' a : Nat, Σ' l : SortedList, Σ' h : (match l.val with | [] => True | b :: _ => a ≤ b), x = SortedList.cons a l h) :=
  match x with
  | ⟨[], h⟩ => PSum.inl (Subtype.ext rfl)
  | ⟨a :: tail, h⟩ =>
    let l_val := tail
    have h_val : IsSorted l_val := by
      cases tail with
      | nil => exact trivial
      | cons b t =>
        dsimp [IsSorted] at h
        exact h.2
    let l : SortedList := ⟨l_val, h_val⟩
    have hb : match l.val with | [] => True | b :: _ => a ≤ b := by
      cases tail with
      | nil => exact trivial
      | cons b t =>
        dsimp [IsSorted] at h
        exact h.1
    PSum.inr ⟨a, l, hb, Subtype.ext rfl⟩

#What_A_View SortedList with
  SortedList.nil SortedList.cons
plus
  cons_smaller
cases
  sorted_cases
through
  (measure (fun l => l.val.length))

#check SortedList.recView



-- ============================================================================
-- Exercises
-- ============================================================================

/-- Idiomatic Lean: We assume the list is not empty, so we can use `head` and `getLast` directly. -/
theorem sorted_head_le_last (x : SortedList) (h : x.val ≠ []) :
    x.val.head h ≤ x.val.getLast h := by
  induction x using SortedList.recView with
  | case_1 =>
    contradiction
  | case_2 a l h_sorted ih =>
    cases h_eq : l.val with
    | nil =>
      dsimp [SortedList.cons]
      simp [h_eq]
    | cons b tail =>
      dsimp [SortedList.cons]
      simp [h_eq] at h_sorted
      have hl : l.val ≠ [] := by simp [h_eq]
      have h_ih := ih hl
      simp [h_eq] at h_ih ⊢
      omega
