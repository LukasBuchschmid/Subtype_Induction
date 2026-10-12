import SubtypeInduction.What_A_View

-- We represent '(' as `true` and ')' as `false`
-- We use a purely computational check for validity!
def isValidDyck : List Bool → Int → Prop
  | [], count => count = 0
  | true :: t, count => isValidDyck t (count + 1)
  | false :: t, count => count > 0 ∧ isValidDyck t (count - 1)

def dyckRun : List Bool → Int → Option Int
  | [], c => some c
  | true :: t, c => dyckRun t (c + 1)
  | false :: t, c => if c > 0 then dyckRun t (c - 1) else none

theorem isValidDyck_iff_dyckRun (l : List Bool) (c : Int) :
  isValidDyck l c ↔ dyckRun l c = some 0 := by
  induction l generalizing c with
  | nil =>
    unfold isValidDyck dyckRun
    simp
  | cons h t ih =>
    cases h
    · unfold isValidDyck dyckRun
      split
      · simp [*]
      · simp [*]
    · unfold isValidDyck dyckRun
      simp [*]

theorem dyckRun_append (A B : List Bool) (c : Int) :
  dyckRun (A ++ B) c = (dyckRun A c).bind (dyckRun B) := by
  induction A generalizing c with
  | nil => rfl
  | cons h t ih =>
    cases h <;> simp [dyckRun]
    · split <;> simp [ih]
    · simp [ih]

theorem dyckRun_add (l : List Bool) (c k : Int) (hk : k ≥ 0) :
  (∃ c', dyckRun l c = some c') → dyckRun l (c + k) = (dyckRun l c).map (fun x => x + k) := by
  intro h
  induction l generalizing c with
  | nil => rfl
  | cons hd tl ih =>
    cases hd
    · unfold dyckRun
      unfold dyckRun at h
      split at h
      · split
        · have h2 : c + k - 1 = c - 1 + k := by omega
          rw [h2]
          apply ih
          exact h
        · rename_i h1 h2
          have : c + k > 0 := by omega
          contradiction
      · rcases h with ⟨c', hc'⟩
        contradiction
    · unfold dyckRun
      unfold dyckRun at h
      have h2 : c + k + 1 = c + 1 + k := by omega
      rw [h2]
      apply ih
      exact h

def findZero : List Bool → Int → List Bool × List Bool
| [], _ => ([], [])
| true :: t, count => 
  let (A, B) := findZero t (count + 1)
  (true :: A, B)
| false :: t, count =>
  if count == 1 then
    ([], t)
  else
    let (A, B) := findZero t (count - 1)
    (false :: A, B)

theorem findZero_spec (l : List Bool) (c : Int) (hc : c > 0) (h : dyckRun l c = some 0) :
  let (A, B) := findZero l c
  l = A ++ [false] ++ B ∧ (∀ k ≥ c - 1, dyckRun A k = some (k - c + 1)) ∧ dyckRun B 0 = some 0 := by
  induction l generalizing c with
  | nil =>
    unfold dyckRun at h
    have : c = 0 := by injection h
    omega
  | cons hd tl ih =>
    match hd with
    | true =>
      unfold findZero
      have h_run : dyckRun (true :: tl) c = dyckRun tl (c + 1) := rfl
      rw [h_run] at h
      have hc1 : c + 1 > 0 := by omega
      have ih_res := ih (c + 1) hc1 h
      cases h_fz : findZero tl (c + 1) with
      | mk A B =>
        simp [h_fz] at ih_res
        rcases ih_res with ⟨h_eq, hA, hB⟩
        have h_eq2 : true :: tl = (true :: A) ++ [false] ++ B := by simp [h_eq]
        refine ⟨h_eq2, ?_, hB⟩
        intro k hk
        dsimp [dyckRun]
        have hk1 : c ≤ k + 1 := by omega
        have hA_res := hA (k + 1) hk1
        have h_math : k + 1 - (c + 1) + 1 = k - c + 1 := by omega
        rw [h_math] at hA_res
        exact hA_res
    | false =>
      unfold findZero
      dsimp
      split
      · rename_i hc1
        have hc_eq : c = 1 := by
          have h1 : (c == 1) = true := hc1
          exact eq_of_beq h1
        have h_run : dyckRun (false :: tl) c = dyckRun tl (c - 1) := by
          dsimp [dyckRun]
          simp [hc]
        rw [h_run] at h
        refine ⟨rfl, ?_, ?_⟩
        · intro k hk
          dsimp [dyckRun]
          apply congrArg
          omega
        · have hc_0 : c - 1 = 0 := by omega
          rw [hc_0] at h
          exact h
      · rename_i hc1
        have hc_neq : c ≠ 1 := by
          intro h_eq
          rw [h_eq] at hc1
          simp at hc1
        have hc_sub : c - 1 > 0 := by omega
        have h_run : dyckRun (false :: tl) c = dyckRun tl (c - 1) := by
          dsimp [dyckRun]
          simp [hc]
        rw [h_run] at h
        have ih_res := ih (c - 1) hc_sub h
        cases h_fz : findZero tl (c - 1) with
        | mk A B =>
          simp [h_fz] at ih_res
          rcases ih_res with ⟨h_eq, hA, hB⟩
          have h_eq2 : false :: tl = (false :: A) ++ [false] ++ B := by simp [h_eq]
          refine ⟨h_eq2, ?_, hB⟩
          intro k hk
          dsimp [dyckRun]
          have hk_pos : k > 0 := by omega
          simp [hk_pos]
          have hk_sub : c - 1 - 1 ≤ k - 1 := by omega
          have hA_res := hA (k - 1) hk_sub
          have h_math : k - 1 - (c - 1) + 1 = k - c + 1 := by omega
          rw [h_math] at hA_res
          exact hA_res

theorem dyck_cases_helper (tl : List Bool) (h : isValidDyck (true :: tl) 0) :
    ∃ A B : List Bool, isValidDyck A 0 ∧ isValidDyck B 0 ∧ (true :: tl) = ([true] ++ A ++ [false] ++ B) := by
  have h_run : dyckRun (true :: tl) 0 = some 0 := isValidDyck_iff_dyckRun _ _ |>.mp h
  have h_run_tl : dyckRun tl 1 = some 0 := h_run
  have h_spec := findZero_spec tl 1 (by omega) h_run_tl
  cases h_fz : findZero tl 1 with
  | mk A B =>
    simp [h_fz] at h_spec
    rcases h_spec with ⟨h_eq, hA, hB⟩
    have hA_valid : isValidDyck A 0 := by
      rw [isValidDyck_iff_dyckRun]
      exact hA 0 (by omega)
    have hB_valid : isValidDyck B 0 := isValidDyck_iff_dyckRun _ _ |>.mpr hB
    refine ⟨A, B, hA_valid, hB_valid, ?_⟩
    simp [h_eq]

def DyckWord := { l : List Bool // isValidDyck l 0 }

def DyckWord.nil : DyckWord := ⟨[], rfl⟩

theorem node_valid (A B : List Bool) (hA : isValidDyck A 0) (hB : isValidDyck B 0) :
  isValidDyck ([true] ++ A ++ [false] ++ B) 0 := by
  rw [isValidDyck_iff_dyckRun] at *
  have h_assoc1 : [true] ++ A ++ [false] ++ B = [true] ++ (A ++ [false] ++ B) := by simp
  rw [h_assoc1]
  have h_step : dyckRun ([true] ++ (A ++ [false] ++ B)) 0 = dyckRun (A ++ [false] ++ B) 1 := rfl
  rw [h_step]
  have h_assoc2 : A ++ [false] ++ B = A ++ ([false] ++ B) := by simp
  rw [h_assoc2, dyckRun_append]
  have hk : (1:Int) ≥ 0 := by omega
  have h_ex : ∃ c', dyckRun A 0 = some c' := ⟨0, hA⟩
  have h_add := dyckRun_add A 0 1 hk h_ex
  rw [hA] at h_add
  simp at h_add
  rw [h_add]
  have h_step2 : dyckRun ([false] ++ B) 1 = some 0 := by
    dsimp [dyckRun]
    exact hB
  exact h_step2

def DyckWord.node (A B : DyckWord) : DyckWord :=
  ⟨[true] ++ A.val ++ [false] ++ B.val, node_valid A.val B.val A.property B.property⟩

theorem node_smaller_A (A B : DyckWord) : A.val.length < (DyckWord.node A B).val.length := by
  dsimp [DyckWord.node]
  simp
  omega

theorem node_smaller_B (A B : DyckWord) : B.val.length < (DyckWord.node A B).val.length := by
  dsimp [DyckWord.node]
  simp
  omega

noncomputable def dyck_cases (x : DyckWord) :
    PSum (x = DyckWord.nil)
         (Σ' A : DyckWord, Σ' B : DyckWord, x = DyckWord.node A B) :=
  if h : x.val = [] then
    PSum.inl (Subtype.ext h)
  else
    match h_hd : x.val with
    | [] => by contradiction
    | true :: tl =>
      have h_prop : isValidDyck (true :: tl) 0 := by
        have prop := x.property
        rw [h_hd] at prop
        exact prop
      let h_ex := dyck_cases_helper tl h_prop
      let A := Classical.choose h_ex
      let h_ex2 := Classical.choose_spec h_ex
      let B := Classical.choose h_ex2
      let ⟨hA, hB, h_eq⟩ := Classical.choose_spec h_ex2
      PSum.inr ⟨⟨A, hA⟩, ⟨B, hB⟩, Subtype.ext (by rw [h_hd, h_eq]; rfl)⟩
    | false :: tl =>
      have h_prop : isValidDyck (false :: tl) 0 := by
        have prop := x.property
        rw [h_hd] at prop
        exact prop
      by
        unfold isValidDyck at h_prop
        simp at h_prop

#What_A_View DyckWord with
  DyckWord.nil DyckWord.node
plus
  node_smaller_A node_smaller_B
cases
  dyck_cases
through
  (measure (fun l => l.val.length))

-- ============================================================================
-- Why is this useful?
-- ============================================================================
--
-- A `List` is a flat, 1-dimensional structure. 
-- But a balanced bracket sequence has a hidden 2-dimensional Tree structure!
--
-- Our `DyckWord` type is defined by a purely computational check `isValidDyck`
-- and its underlying representation is just a flat `List Bool`.
-- If you just look at its definition, there is no tree in sight!
--
-- `DyckWord.recView` uses well-founded recursion over the list length to generate
-- a recursor that eliminates into `Type` / `Sort u`, allowing structural computation!
-- We synthesized a tree induction principle for a purely computational flat property!

/-- Counts the total number of characters in the word -/
def countChars (w : DyckWord) : Nat := w.val.length

/-- Counts the nesting depth (max open brackets) of the word -/
noncomputable def maxDepth (w : DyckWord) : Nat := by
  induction w using DyckWord.recView with
  | case_1 => exact 0
  | case_2 A B depthA depthB => exact max (depthA + 1) depthB
