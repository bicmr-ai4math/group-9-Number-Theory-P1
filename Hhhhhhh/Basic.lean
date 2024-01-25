import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime
import Mathlib.Algebra.BigOperators.Order
import MIL.Common
import Mathlib.Data.Nat.GCD.Basic


open BigOperators

namespace Homework

theorem pred_sub_pred_eq_sub {x y : ℕ} (yge : y ≥ 1) (ylex : y ≤ x) : (x - 1) - (y - 1) = x - y := by
  rw [← Nat.pred_eq_sub_one, ← Nat.pred_eq_sub_one]
  nth_rewrite 2 [← Nat.succ_pred (a := x), ← Nat.succ_pred (a := y)]
  rw [Nat.succ_sub_succ]
  linarith; linarith

theorem lemma_0 {m n s : ℕ} (mge : m ≠ 0) (nge : n ≠ 0) (h : m + n ≤ s): n < s := by
  have nge : n > 0 := by apply Nat.zero_lt_of_ne_zero nge
  have mge : m > 0 := by apply Nat.zero_lt_of_ne_zero mge
  have sge : s > 0 := by linarith
  rw [add_comm] at h
  calc
    n ≤ s - m := by apply Nat.le_sub_of_add_le (a := n) (b := m) (c := s) h
    _ < s := by
      apply Nat.sub_lt sge mge

theorem lemma_0' {m n s : ℕ} (mge : m ≠ 0) (nge : n ≠ 0) (h : m + n ≤ s): m < s := by
  rw [add_comm] at h
  intros
  apply lemma_0 (m := n) nge mge h

theorem  gcd_property' {x y z : ℕ} (h : Nat.gcd x y = 1) : Nat.gcd x (z * y) = Nat.gcd x z := by
  obtain pro1: Nat.gcd x z ∣  Nat.gcd x (z*y) := by
    apply Nat.gcd_dvd_gcd_mul_right_right
  obtain pro2:Nat.gcd x (z*y)∣  Nat.gcd x z :=by
    obtain h1: Nat.gcd x (z*y)∣(Nat.gcd x z * Nat.gcd x y) :=by apply Nat.gcd_mul_dvd_mul_gcd
    rw[h] at h1
    rw[Nat.mul_one] at h1
    apply h1
  apply dvd_antisymm pro2 pro1

-- 跟后面用的时候位置对不上，我就重新改了一下
theorem  gcd_property {x y z : ℕ} (h : Nat.gcd x y = 1) : Nat.gcd z x = Nat.gcd (z * y) x := by
  have : Nat.gcd z x = Nat.gcd x z := by apply gcd_comm
  rw [this]
  have : Nat.gcd (z * y) x = Nat.gcd x (z * y) := by apply gcd_comm
  rw [this, gcd_property']
  exact h

theorem final' {a spt : ℕ} (age: a ≥ 1) : ∀ s t : ℕ , s + t ≤ spt →  a ^ (Nat.gcd s t) - 1 = Nat.gcd (a ^ s - 1) (a ^ t - 1) := by
  have a0 : a > 0 := by linarith
  induction' spt using Nat.strong_induction_on with spt ih
  intro s t hst
  by_cases s0 : s = 0
  rw [s0]; simp
  push_neg at s0
  by_cases t0 : t = 0
  rw [t0]; simp
  push_neg at t0
  by_cases h: s ≤ t
  · have: t < spt := by apply lemma_0 s0 t0 hst
    specialize ih t this
    have: s + (t - s) ≤ t := calc
      s + (t - s) = t := by exact Nat.add_sub_of_le h
      _ ≤ t := by rfl
    specialize ih s (t -s) this -- 得到目标条件 ih

    have h₁ : Nat.gcd s (t - s) = Nat.gcd s t := by exact Nat.gcd_sub_self_right h
    have h₂ : Nat.gcd (a ^ s - 1) (a ^ (t - s) - 1) = Nat.gcd (a ^ s - 1) (a ^ t - 1) := calc
      Nat.gcd (a ^ s - 1) (a ^ (t - s) - 1) = Nat.gcd (a ^ s - 1) (a ^ t - a ^ s) := by
        rw [← gcd_property' (x := a ^ s - 1) (z := a ^ (t - s) - 1) (y := a ^ s)]
        rw [Nat.mul_sub_right_distrib (n := a ^ (t - s)) (m := 1) (k := a ^ s), Nat.one_mul, ← Nat.pow_add, Nat.sub_add_cancel (m := s) (n := t)]
        apply h
        rw [Nat.gcd_self_sub_left (m := 1) (n := a ^ s)]; simp
        apply Nat.one_le_pow; exact a0
      Nat.gcd (a ^ s - 1) (a ^ t - a ^ s) = Nat.gcd (a ^ s - 1) (a ^ t - 1) := by
        rw [← Nat.gcd_sub_self_right (m := a ^ s - 1) (n := a ^ t - 1)]
        rw [pred_sub_pred_eq_sub (x := a ^ t) (y := a ^ s)]
        apply Nat.one_le_pow; apply a0
        apply Nat.pow_le_pow_right; apply a0
        apply h
        simp; rw [add_comm, Nat.add_sub_of_le]; apply Nat.pow_le_pow_right a0 h; apply Nat.one_le_pow; exact a0
    rw [h₁, h₂] at ih; exact ih

  · push_neg at h
    have h': t ≤ s := by exact Nat.le_of_lt h
    have: s < spt := by apply lemma_0' s0 t0 hst
    specialize ih s this
    have: (s - t) + t ≤ s := by rw [add_comm, Nat.add_sub_of_le]; exact h'
    specialize ih (s-t) t this
    have as_ge_one : a ^ s ≥ 1 := by apply Nat.one_le_pow; exact a0
    have h₁ : Nat.gcd (s - t) t  = Nat.gcd s t := by exact Nat.gcd_sub_self_left h'
    --
    have h₂'' (tls : t ≤ s): a ^ s - a ^ t = (a ^ (s - t) - 1) * a ^ t := by
      rw [Nat.mul_sub_right_distrib (n := a ^ (s - t)) (m := 1) (k := a ^ t), Nat.one_mul]
      rw [← Nat.pow_add]; congr
      rw [Nat.sub_add_cancel (m := t) (n := s)]
      exact tls
    have hhh : a ^ s - a ^ t = (a ^ s - 1) - (a ^ t - 1) := by
      rw [pred_sub_pred_eq_sub (x := a ^ s) (y := a ^ t)]
      apply Nat.one_le_pow; exact a0; apply Nat.pow_le_pow_right a0 h'
    --
    have a_pow_coprime_a_pow_m1' : Nat.gcd (a ^ t - 1) (a ^ t) = Nat.gcd 1 (a ^ t) := by
      apply Nat.gcd_self_sub_left (m := 1) (n := a ^ t); apply Nat.one_le_pow; exact a0
    have a_pow_coprime_a_pow_m1 : Nat.gcd (a ^ t - 1) (a ^ t) = 1 := by rw [a_pow_coprime_a_pow_m1']; simp
    have h₂' : Nat.gcd (a ^ (s - t) - 1) (a ^ t - 1) = Nat.gcd (a ^ s - a ^ t) (a ^ t - 1) := by
      rw [h₂'' h']; apply gcd_property (x := a ^ t - 1) (y := a ^ t) (z := a ^ (s - t) - 1); exact a_pow_coprime_a_pow_m1
    have h₂ : Nat.gcd (a ^ (s - t) - 1) (a ^ t - 1) = Nat.gcd (a ^ s - 1) (a ^ t - 1) := by
      rw [h₂', hhh]
      apply Nat.gcd_sub_self_left (m := a ^ t - 1) (n := a ^ s - 1)
      simp; rw [add_comm, Nat.add_sub_of_le]; apply Nat.pow_le_pow_right a0 h'; exact as_ge_one
    rw [h₁, h₂] at ih; exact ih;

theorem final {a : ℕ} (age : a ≥ 1) : ∀ s t : ℕ, a ^ (Nat.gcd s t) - 1 = Nat.gcd (a ^ s - 1) (a ^ t - 1) := by
  intro s t
  apply final' (spt := s + t) age
  simp
