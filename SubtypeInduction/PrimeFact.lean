import SubtypeInduction.What_A_View
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factors

def PNat := { n : Nat // n > 0 }

def PNat.one : PNat := ⟨1, by decide⟩

def PNat.mulPrime (p : Nat) (hp : p.Prime) (n : PNat) : PNat :=
  ⟨p * n.val, by
    have h1 : p > 0 := Nat.Prime.pos hp
    have h2 : n.val > 0 := n.property
    exact Nat.mul_pos h1 h2⟩

theorem mulPrime_smaller (p : Nat) (hp : p.Prime) (n : PNat) :
  n.val < (PNat.mulPrime p hp n).val := by
  dsimp [PNat.mulPrime]
  have hp_ge_2 : p ≥ 2 := Nat.Prime.two_le hp
  have hn_pos : n.val > 0 := n.property
  exact calc n.val < n.val + n.val := by omega
    _ = 2 * n.val := by omega
    _ ≤ p * n.val := Nat.mul_le_mul_right n.val hp_ge_2

def pnat_cases (n : PNat) :
  PSum (n = PNat.one) (Σ' (p : Nat) (hp : p.Prime) (m : PNat), n = PNat.mulPrime p hp m) :=
  if h : n.val = 1 then
    PSum.inl (Subtype.ext h)
  else
    have h_gt_1 : n.val > 1 := by
      have hn_pos : n.val > 0 := n.property
      omega
    let p := Nat.minFac n.val
    have hp : p.Prime := Nat.minFac_prime (by omega)
    have hp_dvd : p ∣ n.val := Nat.minFac_dvd n.val
    let m_val := n.val / p
    have hm_pos : m_val > 0 := Nat.div_pos (Nat.minFac_le (by omega)) (Nat.Prime.pos hp)
    let m : PNat := ⟨m_val, hm_pos⟩
    PSum.inr ⟨p, hp, m, Subtype.ext (Nat.mul_div_cancel' hp_dvd).symm⟩

#What_A_View PNat with
  PNat.one PNat.mulPrime
plus
  mulPrime_smaller
cases
  pnat_cases
through
  (measure (fun n => n.val))

/-- Compute the number of prime factors -/
noncomputable def numFactors (n : PNat) : Nat := by
  induction n using PNat.recView with
  | case_1 => exact 0
  | case_2 p hp m ih => exact ih + 1
