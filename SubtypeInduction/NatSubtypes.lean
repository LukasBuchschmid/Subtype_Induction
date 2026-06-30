import SubtypeInduction.InductivePredicateTactic

inductive Even : Nat -> Prop where
  | zero : Even 0
  | plusTwo : Even n -> Even (n + 2)

inductive Odd : Nat -> Prop where
  | One : Odd 1
  | plusTwo : Odd n -> Odd (n + 2)

-- recursors for Odd and even

#check Nat.rec

#check Odd.rec

def EvenNumbers := {n : Nat // Even n}
def OddNumbers := {n : Nat // Odd n}

#check Subtype.rec

#Induct_Pred_Recursor EvenNumbers


def EvenRec
  {motive : EvenNumbers → Prop}
  (Zero : motive ⟨0, Even.zero⟩)
  (succ' : ∀ {n : Nat} (a : Even n), motive ⟨n, a⟩ → motive ⟨n + 2, Even.plusTwo a⟩)
  {k : Nat} (a : Even k) : motive ⟨k, a⟩ :=
    match k, a with
    | 0, Even.zero => Zero
    | _, Even.plusTwo l => succ' l (EvenRec Zero succ' l)

#print EvenRec

def OddRec
  {motive : OddNumbers -> Prop}
  (One : motive ⟨1, Odd.One⟩)
  (succ' : ∀ {n : Nat} (a : Odd n), motive ⟨n, a⟩ -> motive ⟨(n+2), Odd.plusTwo a⟩)
  {k : Nat} (h : Odd k) : motive ⟨k, h⟩ :=
    match k , h with
    | 1, Odd.One => One
    | m + 2 , Odd.plusTwo j => succ' j (OddRec One succ' j)



def Fin2 n := {i : Nat // i < n}
#check Fin2
#check Fin

#check Fin.rec
#check Fin.induction

inductive LEQ (n : Nat) : Nat -> Prop where
  | reflx : LEQ n n
  | step : LEQ n m -> LEQ n (m+1)

def AtLeast (n : Nat) := {k : Nat // LEQ n k}

#Induct_Pred_Recursor AtLeast

def AtLeastRec {n : Nat} {motive : (AtLeast n) -> Prop}
  (start : motive ⟨n, LEQ.reflx⟩)
  (step : ∀ (k : AtLeast n), motive k -> motive ⟨k.val + 1, LEQ.step k.property⟩)
  (l : AtLeast n) : motive l := by
  revert start step
  cases l with
  | mk val property =>
  induction property with
    | reflx =>
      intro start step
      exact start
    | step h ih =>
      intro start step
      apply step ⟨_, h⟩
      exact ih start step
