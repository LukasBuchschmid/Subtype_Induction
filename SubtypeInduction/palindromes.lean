-- List snoc rec

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
