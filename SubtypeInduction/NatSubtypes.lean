import SubtypeInduction.InductivePredicateTactic

namespace Inductive

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

#Induct_Pred_Recursor Inductive.EvenNumbers

#check Nat.rec


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

#Induct_Pred_Recursor Inductive.AtLeast

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

end Inductive

#check Nat.succ

namespace Noninductive

def Even : Nat -> Prop :=
  fun n => n % 2 = 0

def Odd : Nat -> Prop :=
  fun n => n % 2 = 1

def EvenNumbers := {n : Nat // Even n}
def OddNumbers := {n : Nat // Odd n}

def EvenNumbers.zero : EvenNumbers := ⟨Nat.zero, rfl⟩
def EvenNumbers.succ (n : EvenNumbers ): EvenNumbers := ⟨n.val + 2, by grind [= Even]⟩

def EvenNumbers.rec.{u} {motive : EvenNumbers → Sort u} (zero : motive EvenNumbers.zero)
  (succ : (n : EvenNumbers) → motive n → motive n.succ) (t : EvenNumbers) :
  motive t := sorry

def OddNumbers.one : OddNumbers := ⟨Nat.zero.succ, rfl⟩
def OddNumbers.succ (n : OddNumbers) : OddNumbers := ⟨n.val +2, by grind [= Odd]⟩

inductive IsConstructed : OddNumbers -> Type where
  | base : IsConstructed OddNumbers.one
  | step (n : OddNumbers) : IsConstructed n -> IsConstructed (OddNumbers.succ n)

def EveryOddIsConstructed : Type := ∀ (n : OddNumbers), IsConstructed n

def ConsProofOdd : (n : OddNumbers) -> IsConstructed n
  | ⟨0, h⟩ => by contradiction
  | ⟨1, h⟩ => IsConstructed.base
  | ⟨k + 2, h⟩ =>
    have hk : Odd k := by
      dsimp [Odd] at h ⊢
      omega
    have ih : IsConstructed ⟨k, hk⟩ := ConsProofOdd ⟨k, hk ⟩
    IsConstructed.step ⟨k, hk⟩ ih
termination_by n => n.val

def AllConsProofOdd : EveryOddIsConstructed :=
  ConsProofOdd

def OddNumbers.rec.{u} {motive : OddNumbers → Sort u} (start : motive OddNumbers.one)
  (succ : (n : OddNumbers) → motive n → motive n.succ) (t : OddNumbers) :
  motive t :=
    let rec helper (k : Nat) (h : Odd k) : motive ⟨k, h⟩ :=
    match k, h with
      | 0, h0 => by
        dsimp [Odd] at h0
        omega
      | 1, _ => start
      | k' + 2, h2 => by
        have hk : Odd k' := by
          dsimp [Odd] at h2 ⊢
          omega
        exact succ ⟨k', hk⟩ (helper k' hk)
    match t with
      | ⟨k, h⟩ => helper k h


def OddNumbers.rec2.{u} {motive : OddNumbers → Sort u} (start : motive OddNumbers.one)
  (succ : (n : OddNumbers) → motive n → motive n.succ) (t : OddNumbers) :
  motive t :=
    let rec read_blueprint {n : OddNumbers} (blueprint : IsConstructed n) : motive n :=
    match blueprint with
    | IsConstructed.base => start
    | IsConstructed.step m bp => succ m (read_blueprint bp)
  read_blueprint (ConsProofOdd t)


theorem lemma2 {n : Nat} (h : Odd n) : n = 1 ∨ ∃ n', Odd n' ∧ n = n' + 2 :=
  match n with
  | 0 => by
    dsimp [Odd] at h
    omega
  | 1 => Or.inl rfl
  | n + 2 => by
    have hn : Odd n := by
      dsimp [Odd] at h ⊢
      omega
    exact Or.inr ⟨n, hn, rfl⟩

theorem odd_zero_impossible (h : Odd 0) : False := by
  have h_cases := lemma2 h
  match h_cases with
  | Or.inl h_zero_eq_one => contradiction
  | Or.inr ⟨n', hn', h_zero_eq_succ⟩ => contradiction

theorem odd_prev {n : Nat} (h : Odd (n + 2)) : Odd n := by
  dsimp [Odd] at h ⊢
  omega


def OddNumbers.rec3.{u} {motive : OddNumbers → Type u} (start : motive OddNumbers.one)
  (succ : (n : OddNumbers) → motive n → motive n.succ) (t : OddNumbers) : motive t :=

  let Motive' (k : Nat) : Type u :=
    ((h : Odd k) → motive ⟨k, h⟩) × ((h : Odd (k + 1)) → motive ⟨k + 1, h⟩)

  let rec helper (k : Nat) : Motive' k :=
    match k with
    | 0 =>
      ( fun h => False.elim (odd_zero_impossible h),
        fun _ => start )

    | n + 1 =>
      let prev := helper n
      ( prev.2,
        fun h_succ_succ => by
          have hn : Odd n := odd_prev h_succ_succ
          exact succ ⟨n, hn⟩ (prev.1 hn) )

  (helper t.val).1 t.property


inductive IndEven : Type where
  | zero' : IndEven
  | succ' : IndEven -> IndEven

def SubToInd (n : EvenNumbers) : IndEven :=
  match n with
  | ⟨0, h⟩ => IndEven.zero'
  | ⟨n + 2, h⟩ =>
      have hn : Even n := by
       dsimp [Even] at h ⊢
       omega
      IndEven.succ' (SubToInd ⟨n, hn⟩)
termination_by n.val

def IndToSub (n : IndEven) : EvenNumbers :=
  match n with
  | .zero' => ⟨0, rfl⟩
  | .succ' n' =>
      let ⟨n, hn⟩ := IndToSub n'
      have h : (Even (n + 2)) := by
        dsimp [Even] at hn ⊢
        omega
    ⟨n + 2, h⟩


theorem IndToSub_left_inv_SubToInd : Function.LeftInverse IndToSub SubToInd :=
  fun n =>
    match n with
      | ⟨0, h⟩ => by
        apply Subtype.ext
        simp [SubToInd, IndToSub]
      | ⟨k + 2, h⟩ => by
        have hk : Even k := by
          dsimp [Even] at h ⊢
          omega
        have ih := IndToSub_left_inv_SubToInd ⟨k, hk⟩
        apply Subtype.ext
        simp [SubToInd, IndToSub, ih]
termination_by n => n.val

theorem SubToInd_left_inv_IndToSub : Function.LeftInverse SubToInd IndToSub :=
  fun n =>
    match n with
      | .zero' => by
        unfold IndToSub
        ---unfold SubToInd    this should work, I don't know why it doesn't
        sorry


      | .succ' m => by
        have ih := SubToInd_left_inv_IndToSub m
        unfold IndToSub
        cases h : IndToSub m
        expose_names
        unfold SubToInd
        dsimp
        simp
        rw[h] at ih
        rw[ih]


def EvenNumbers.rec2.{u} {motive : EvenNumbers → Type u} (start : motive EvenNumbers.zero)
  (succ : (n : EvenNumbers) → motive n → motive n.succ) (t : EvenNumbers) : motive t :=
    let rec helper (m : IndEven) : motive (IndToSub m) :=
      match m with
        | .zero' => by
          unfold IndToSub
          apply start
        | .succ' m => by
          let ih := helper m
          unfold IndToSub
          cases h : IndToSub m
          dsimp
          rw [h] at ih
          expose_names
          exact succ ⟨val, property⟩ ih
    by
      have inv := IndToSub_left_inv_SubToInd t
      rw [← inv]
      apply helper (SubToInd t)


def mod4_1 : Nat -> Prop :=
  fun n => n%4 = 1

def mod4_1Number := {n : Nat // mod4_1 n}

def mod4_1Number.one : mod4_1Number := ⟨1, rfl⟩
def mod4_1Number.succ (n : mod4_1Number) : mod4_1Number := ⟨n.val + 4, by grind [mod4_1]⟩

def mod4_1Number.rec.{u} {motive : mod4_1Number → Type u} (one : motive mod4_1Number.one)
  (succ : (n : mod4_1Number) → motive n → motive n.succ) (t : mod4_1Number) : motive t :=
  let Motive' (k : Nat) : Type u :=
    ((h : mod4_1 k)       → motive ⟨k, h⟩) × ((h : mod4_1 (k + 1)) → motive ⟨k + 1, h⟩) ×
    ((h : mod4_1 (k + 2)) → motive ⟨k + 2, h⟩) × ((h : mod4_1 (k + 3)) → motive ⟨k + 3, h⟩)

  let rec helper (k : Nat) : Motive' k :=
    match k with
      | 0 =>
        ( fun h => by dsimp [mod4_1] at h; omega,
          fun _ => one,
          fun h => by dsimp [mod4_1] at h; omega,
          fun h => by dsimp [mod4_1] at h; omega )
      | n + 1 =>
        let prev := helper n
        ( prev.2.1,
          prev.2.2.1,
          prev.2.2.2,
          fun h_succ => by
            have hn : mod4_1 n := by
              dsimp [mod4_1] at h_succ ⊢
              omega
            exact succ ⟨n, hn⟩ (prev.1 hn)
              )

  (helper t.val).1 t.property


end Noninductive

#check Fin


#check Fin.rec

#check Fin.induction

def Fin.rec2.{u} {n : Nat} (h : n > 0)
  {motive : Fin n -> Sort u}
  (zero : motive ⟨0, h⟩)
  (succ : (m : Fin (n - 1)) ->
          motive (Fin.cast (Nat.sub_add_cancel h) m.castSucc) ->
          motive (Fin.cast (Nat.sub_add_cancel h) m.succ))
  (i : Fin n) : motive i :=
    let rec helper (k : Nat) (h : k < n) : motive ⟨k, h⟩ :=
      match k, h with
      |0, h => zero
      |n + 1 , h => by
        expose_names
        have hn : n < n_1 - 1 := by omega
        have h_eq_fin : Fin.cast (Nat.sub_add_cancel h_1) (Fin.succ ⟨n, hn⟩) = ⟨n + 1, h⟩ := by
          apply Fin.ext
          rfl
        have hn_cast : n < n_1 := by omega
        let rec_call := helper n hn_cast
        exact h_eq_fin ▸ succ ⟨n, hn⟩ rec_call
  match i with
    | ⟨k, h⟩ => helper k h


-- it kind of feels like what interesting here is the fact that we can propegate the predicate downwards along the structure of the natural numbers, which allows us
-- to recurse downwards and stay in the subtype (is that just a recursive predicate and therefore a case of the ornament stuff)
