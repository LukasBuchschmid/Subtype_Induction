import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Prime.Basic
import SubtypeInduction.What_A_View

/-- We view the natural numbers through their prime factorization. -/
abbrev NatFactorization := ℕ

def NatFactorization.base_zero : NatFactorization := 0
def NatFactorization.base_one : NatFactorization := 1

def NatFactorization.mul_minFac (p : ℕ) (m : NatFactorization) (_hp : p.Prime) (_hm : m ≠ 0) : NatFactorization := p * m

theorem mul_minFac_smaller (p : ℕ) (m : NatFactorization) (hp : p.Prime) (hm : m ≠ 0) :
  m < NatFactorization.mul_minFac p m hp hm := by
  dsimp [NatFactorization.mul_minFac]
  have hp_gt_one : p > 1 := hp.one_lt
  have hm_pos : 0 < m := Nat.pos_of_ne_zero hm
  calc m = 1 * m := (Nat.one_mul m).symm
       _ < p * m := Nat.mul_lt_mul_of_pos_right hp_gt_one hm_pos

def prime_factorization_cases (n : NatFactorization) :
  PSum (n = NatFactorization.base_zero)
    (PSum (n = NatFactorization.base_one)
      (Σ' (p : ℕ) (m : NatFactorization) (hp : p.Prime) (hm : m ≠ 0), n = NatFactorization.mul_minFac p m hp hm)) := by
  if h0 : n = 0 then
    exact PSum.inl h0
  else if h1 : n = 1 then
    exact PSum.inr (PSum.inl h1)
  else
    let p := n.minFac
    have hp : p.Prime := Nat.minFac_prime h1
    let m := n / p
    have hm : m ≠ 0 := by
      intro hm_eq
      have h_n_eq_0 : n = 0 := by
        calc n = p * (n / p) + n % p := (Nat.div_add_mod n p).symm
             _ = p * m + 0 := by rw [Nat.mod_eq_zero_of_dvd (Nat.minFac_dvd n)]
             _ = p * 0 + 0 := by rw [hm_eq]
             _ = 0 := by simp
      exact h0 h_n_eq_0
    have h_eq : n = NatFactorization.mul_minFac p m hp hm := by
      dsimp [NatFactorization.mul_minFac, p, m]
      exact (Nat.mul_div_cancel' (Nat.minFac_dvd n)).symm
    exact PSum.inr (PSum.inr ⟨p, m, hp, hm, h_eq⟩)

noncomputable section
#What_A_View NatFactorization with
  NatFactorization.base_zero NatFactorization.base_one NatFactorization.mul_minFac
plus
  mul_minFac_smaller
cases
  prime_factorization_cases
through
  (measure id)
end

/-- Extract the list of prime factors. -/
noncomputable def primeFactors (n : NatFactorization) : List ℕ := by
  induction n using NatFactorization.recView with
  | case_1 => exact []
  | case_2 => exact []
  | case_3 p _ _ _ ih => exact p :: ih

/-- Example Proof 1: Every natural number ≥ 2 has at least one prime divisor. -/
theorem exists_prime_factor (n : NatFactorization) (hn : 2 ≤ n) :
    ∃ p, p.Prime ∧ p ∣ n := by
  induction n using NatFactorization.recView with
  | case_1 =>
    change 2 ≤ 0 at hn
    contradiction
  | case_2 =>
    change 2 ≤ 1 at hn
    contradiction
  | case_3 p m hp _hm _ih =>
    use p, hp
    dsimp [NatFactorization.mul_minFac]
    exact dvd_mul_right p m

/-- Example Proof 2: Every natural number n ≥ 2 is either prime itself or composite (p * m with m ≥ 2). -/
theorem prime_or_composite (n : NatFactorization) (hn : 2 ≤ n) :
    n.Prime ∨ ∃ p m, p.Prime ∧ 2 ≤ m ∧ n = p * m := by
  induction n using NatFactorization.recView with
  | case_1 =>
    change 2 ≤ 0 at hn
    contradiction
  | case_2 =>
    change 2 ≤ 1 at hn
    contradiction
  | case_3 p m hp hm _ih =>
    dsimp [NatFactorization.mul_minFac]
    if hm1 : m = 1 then
      left
      subst hm1
      rw [mul_one]
      exact hp
    else
      right
      have hm_ge2 : 2 ≤ m := by
        cases m with
        | zero => contradiction
        | succ m' =>
          cases m' with
          | zero => contradiction
          | succ m'' => exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le m''))
      exact ⟨p, m, hp, hm_ge2, rfl⟩
