import Mathlib.Data.List.Sort
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Finset.Basic

def MultisetAsSubtype (α : Type) [LinearOrder α] := { l : List α // List.Pairwise (· ≤ ·) l }

def MultisetAsSubtype.add {α : Type} [LinearOrder α] (a : α) (l : MultisetAsSubtype α) : MultisetAsSubtype α :=
  let newList := (a :: l.val).mergeSort (fun x y => decide (x ≤ y))
  have isSorted : newList.Pairwise (· ≤ ·) := List.pairwise_mergeSort' (· ≤ ·) (a :: l.val)
  ⟨newList, isSorted⟩

#check Multiset

#check Multiset.rec

#check Finset.rec

#check Finset.induction_on

lemma not_in_cons_of_neq {α} (a a' : α) (f : Finset α) (ha : a ∉ f) (ha' : a' ∉ f) (h_neq : a' ≠ a) :
  a' ∉ Finset.cons a f ha := by
    intro h_in
    rcases Multiset.mem_cons.mp h_in with h_eq | h_mem
    · exact h_neq h_eq
    · exact ha' h_mem



def Finset.rec2 {α : Type _} (motive : Finset α -> Sort u) (start : motive ∅)
  (step : (a : α) → (f : Finset α) -> (h : a ∉ f) -> motive f -> motive (Finset.cons a f h))
  (comm : ∀ (a a' : α) (f : Finset α) (ha : a ∉ f) (ha' : a' ∉ f) (h_neq : a ≠ a') (b : motive f),
    step a' (Finset.cons a f ha)
      (not_in_cons_of_neq a a' f ha ha' h_neq.symm)
      (step a f ha b)
    ≍
    step a (Finset.cons a' f ha')
      (not_in_cons_of_neq a' a f ha' ha h_neq)
      (step a' f ha' b)
  )
  (t : Finset α) : motive t :=
   match t with
    | ⟨s, nd⟩ =>
      let C : Multiset α → Sort u := fun m => (nd : m.Nodup) → motive ⟨m, nd⟩
      let C0 : C 0 := fun nd => start
      let C_cons : (a : α) → (m : Multiset α) → C m → C (a ::ₘ m) := by
        intro a m cm nd_cons
        have h_notin := (Multiset.nodup_cons.mp nd_cons).1
        have h_nodup := (Multiset.nodup_cons.mp nd_cons).2
        exact step a ⟨m, h_nodup⟩ h_notin (cm h_nodup)
      let C_cons_heq_body : ∀ (a a' : α) (m : Multiset α) (b : C m)
            (nd1 : (a ::ₘ a' ::ₘ m).Nodup)
            (nd2 : (a' ::ₘ a ::ₘ m).Nodup),
            C_cons a (a' ::ₘ m) (C_cons a' m b) nd1
            ≍
            C_cons a' (a ::ₘ m) (C_cons a m b) nd2 := by
              intro a a' m b nd1 nd2
              have ⟨h_notin_nd11, h_nodup_nd12⟩ := Multiset.nodup_cons.mp nd1
              have ⟨h_notin_nd21, h_nodup_nd22⟩ := Multiset.nodup_cons.mp nd2
              rw [Multiset.mem_cons] at h_notin_nd11
              push Not at h_notin_nd11
              rcases h_notin_nd11 with ⟨h_neq, h_notin_m_a⟩
              have ⟨h_notin_m_a', h_nodup_m⟩ := Multiset.nodup_cons.mp h_nodup_nd12
              dsimp [C_cons]
              exact (comm a a' ⟨m, h_nodup_m⟩ h_notin_m_a h_notin_m_a' h_neq (b h_nodup_m)).symm
      let C_cons_heq : ∀ (a a' : α) (m : Multiset α) (b : C m),
        C_cons a (a' ::ₘ m) (C_cons a' m b) ≍ C_cons a' (a ::ₘ m) (C_cons a m b) := by
          intro a a' m b
          have h_domain : (a ::ₘ a' ::ₘ m).Nodup = (a' ::ₘ a ::ₘ m).Nodup := by
            rw [Multiset.cons_swap a a' m]
          refine Function.hfunext h_domain ?_
          intro nd1 nd2 h_prop
          exact C_cons_heq_body a a' m b nd1 nd2
      Multiset.rec C0 C_cons C_cons_heq s nd
