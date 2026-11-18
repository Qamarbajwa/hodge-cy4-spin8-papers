/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
import ShiodaFormalConjectures
import HodgeVerification

/-!
# Finite Cyclotomic Incidence Sieve and Residual Form Left Behind

This module formalizes the finite multi-block incidence sieve connecting
cyclotomic circle/plane covers to the surviving residual form left behind.
It proves universally quantified sieve conservation laws over arbitrary
multiplicity bucket lists and instantiates the three-level master certificate
for Band 1 matchings, 20 coordinate planes, and degree-2 Macaulay syzygies.
-/

/-- Total union size (active support) covered by a list of `(multiplicity, count)` buckets. -/
def activeSupport : List (Nat × Nat) → Nat
  | [] => 0
  | (_, n) :: rest => n + activeSupport rest

/-- Total incidence sum `∑ k * n_k` across all blocks in a bucket list. -/
def totalIncidences : List (Nat × Nat) → Nat
  | [] => 0
  | (k, n) :: rest => k * n + totalIncidences rest

/-- Multi-block collision excess measuring overlap beyond the active union. -/
def collisionExcess (buckets : List (Nat × Nat)) : Nat :=
  totalIncidences buckets - activeSupport buckets

/-- Dimension of the uncovered residual form left behind inside `ambientDim`. -/
def residualFormDim (ambientDim : Nat) (buckets : List (Nat × Nat)) : Nat :=
  ambientDim - activeSupport buckets

private theorem nat_mul_ge_self (k n : Nat) (hk : 1 ≤ k) : n ≤ k * n := by
  cases k with
  | zero => exact absurd hk (Nat.not_le_of_gt (Nat.zero_lt_one))
  | succ k' =>
    rw [Nat.succ_mul, Nat.add_comm]
    exact Nat.le_add_right n (k' * n)

private theorem blt_zero_to_one_le (k : Nat) (h : Nat.blt 0 k = true) : 1 ≤ k := by
  cases k with
  | zero => contradiction
  | succ k' => exact Nat.succ_le_succ (Nat.zero_le k')

private theorem bool_and_left {a b : Bool} (h : (a && b) = true) : a = true := by
  cases a <;> cases b <;> first | rfl | contradiction

private theorem bool_and_right {a b : Bool} (h : (a && b) = true) : b = true := by
  cases a <;> cases b <;> first | rfl | contradiction

/-- For any bucket list with every multiplicity `k >= 1`, `activeSupport <= totalIncidences`. -/
theorem activeSupport_le_totalIncidences (buckets : List (Nat × Nat))
    (h : buckets.all (fun p => Nat.blt 0 p.1) = true) :
    activeSupport buckets ≤ totalIncidences buckets := by
  induction buckets with
  | nil => exact Nat.le_refl 0
  | cons p rest ih =>
    cases p with
    | mk k n =>
      dsimp [List.all] at h
      have hk1 : 1 ≤ k := blt_zero_to_one_le k (bool_and_left h)
      have ih' : activeSupport rest ≤ totalIncidences rest := ih (bool_and_right h)
      exact Nat.add_le_add (nat_mul_ge_self k n hk1) ih'

private theorem nat_add_sub_of_le (a b : Nat) (h : a ≤ b) : a + (b - a) = b := by
  induction a generalizing b with
  | zero => exact Nat.zero_add b
  | succ a' ih =>
    cases b with
    | zero => exact absurd h (Nat.not_le_of_gt (Nat.zero_lt_succ a'))
    | succ b' =>
      rw [Nat.succ_add, Nat.succ_sub_succ]
      exact congrArg Nat.succ (ih b' (Nat.le_of_succ_le_succ h))

/-- Universal sieve identity: `activeSupport + collisionExcess = totalIncidences`. -/
theorem activeSupport_add_collisionExcess (buckets : List (Nat × Nat))
    (h : buckets.all (fun p => Nat.blt 0 p.1) = true) :
    activeSupport buckets + collisionExcess buckets = totalIncidences buckets :=
  nat_add_sub_of_le (activeSupport buckets) (totalIncidences buckets)
    (activeSupport_le_totalIncidences buckets h)

/-- Universal residual form identity: `activeSupport + residualFormDim = ambientDim`. -/
theorem activeSupport_add_residualFormDim (ambientDim : Nat) (buckets : List (Nat × Nat))
    (h : activeSupport buckets ≤ ambientDim) :
    activeSupport buckets + residualFormDim ambientDim buckets = ambientDim :=
  nat_add_sub_of_le (activeSupport buckets) ambientDim h

/-- Multiplicity buckets for the 20 coordinate 2-planes in `R^6(F_0)`. -/
def twentyPlaneBuckets : List (Nat × Nat) := [(1, 200), (4, 45)]

/-- Unified three-level cyclotomic incidence sieve and residual form master certificate. -/
theorem cyclotomic_incidence_residual_form_master_cert :
    (totalIncidences band1_multiplicity_pairs == 1875 &&
     activeSupport band1_multiplicity_pairs == 1001 &&
     collisionExcess band1_multiplicity_pairs == 874 &&
     residualFormDim h22_prim band1_multiplicity_pairs == 750 &&
     residualFormDim h22_prim band1_multiplicity_pairs ==
       fermat_band2_count 6 + fermat_band3_count 6) ∧
    (totalIncidences twentyPlaneBuckets == 380 &&
     activeSupport twentyPlaneBuckets == 245 &&
     collisionExcess twentyPlaneBuckets == 135 &&
     residualFormDim h31_prim twentyPlaneBuckets == 181 &&
     residualFormDim h31_prim twentyPlaneBuckets == high_support_moduli_dim) ∧
    ((monomials4 2).length - macaulayMatrixRank planeSoclePoly 2 == 4 &&
     (monomials4 2).length - macaulayMatrixRank quadricJetSoclePoly 2 == 1) :=
  ⟨rfl, rfl, rfl⟩

#print axioms activeSupport_le_totalIncidences
#print axioms activeSupport_add_collisionExcess
#print axioms activeSupport_add_residualFormDim
#print axioms cyclotomic_incidence_residual_form_master_cert
