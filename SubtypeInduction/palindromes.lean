-- List snoc rec

import SubtypeInduction.What_A_View


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




#check Nat.strongRecOn



def IsPalindrome {α : Type} : List α → Prop :=
  fun l => l = l.reverse

def Palindrome {α : Type} := {l : List α // IsPalindrome l}

def Palindrome.nil {α : Type} : Palindrome (α := α) := ⟨[], rfl⟩

def Palindrome.singleton {α : Type} (a : α) : Palindrome (α := α) := ⟨[a], rfl⟩

def PalindromeStep {α : Type} (a : α) (l : List α) : List α :=
  a :: (a :: l).reverse

theorem StepIsPalindrome {α : Type} (a : α) (p : Palindrome (α := α)) : IsPalindrome (PalindromeStep a p.val) := by
  unfold PalindromeStep IsPalindrome
  simp
  exact (p.property).symm

#What_A_View Palindrome

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







def Palindrome.step {α : Type} (a : α) (p : Palindrome (α := α)) : Palindrome (α := α) :=
  ⟨PalindromeStep a p.val, (StepIsPalindrome a p)⟩

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
