/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
import ShiodaFormalConjectures
import HodgeVerification

/-!
# Shioda-Aoki Fermat Fourfold Character Cohomology

This module provides Mathlib-style universally quantified structural theorems
for the Shioda-Aoki cyclotomic character classification on Fermat fourfolds,
including fuel-bounded GCD termination properties, mutual exclusivity and
exhaustiveness of the four-band partition, coordinate-swap invariance, and
low-degree Band 4 vanishing certificates.
-/

/-- Fuel-bounded Euclidean reduction returns `a` whenever the second argument is zero. -/
theorem gcdFuel_zero_right (k a : Nat) : gcdFuel (k + 1) a 0 = a := by
  rfl

/-- Fuel-bounded GCD agrees with `Nat.gcd` for all `1 <= t < m <= 20`. -/
theorem gcdFuel_eq_nat_gcd_le_20 :
    (rangeList 1 20).all (fun m =>
      (rangeList 1 m).all (fun t => gcdFuel m t m == Nat.gcd t m)) = true := by
  rfl

/-- The four Shioda-Aoki geometric bands are pairwise mutually exclusive
for all degrees `m` and all character tuples `a`. -/
theorem band_partition_mutually_exclusive (m : Nat) (a : List Nat) :
    (isBand1CompletePairs m a && isBand2ThreePlusThree m a) = false ∧
    (isBand1CompletePairs m a && isBand3TwoPlusFour m a) = false ∧
    (isBand1CompletePairs m a && isBand4Residual m a) = false ∧
    (isBand2ThreePlusThree m a && isBand3TwoPlusFour m a) = false ∧
    (isBand2ThreePlusThree m a && isBand4Residual m a) = false ∧
    (isBand3TwoPlusFour m a && isBand4Residual m a) = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · cases h1 : isBand1CompletePairs m a with
    | false => rfl
    | true => dsimp [isBand2ThreePlusThree]; rw [h1]; rfl
  · cases h1 : isBand1CompletePairs m a with
    | false => rfl
    | true => dsimp [isBand3TwoPlusFour]; rw [h1]; rfl
  · cases h1 : isBand1CompletePairs m a with
    | false => rfl
    | true =>
      dsimp [isBand4Residual]
      rw [h1]
      cases isShiodaHodge22 m a <;> cases isBand2ThreePlusThree m a <;>
        cases isBand3TwoPlusFour m a <;> rfl
  · cases h2 : isBand2ThreePlusThree m a with
    | false => rfl
    | true =>
      dsimp [isBand3TwoPlusFour]
      rw [h2]
      cases isBand1CompletePairs m a <;> rfl
  · cases h2 : isBand2ThreePlusThree m a with
    | false => rfl
    | true =>
      dsimp [isBand4Residual]
      rw [h2]
      cases isShiodaHodge22 m a <;> cases isBand1CompletePairs m a <;>
        cases isBand3TwoPlusFour m a <;> rfl
  · cases h3 : isBand3TwoPlusFour m a with
    | false => rfl
    | true =>
      dsimp [isBand4Residual]
      rw [h3]
      cases (isShiodaHodge22 m a && !(isBand1CompletePairs m a) &&
        !(isBand2ThreePlusThree m a)) <;> rfl

/-- Every primitive `(2,2)`-Hodge character lies in at least one of the four bands. -/
theorem band_partition_exhaustive (m : Nat) (a : List Nat)
    (h : isShiodaHodge22 m a = true) :
    (isBand1CompletePairs m a || isBand2ThreePlusThree m a ||
     isBand3TwoPlusFour m a || isBand4Residual m a) = true := by
  cases h1 : isBand1CompletePairs m a with
  | true => rfl
  | false =>
    cases h2 : isBand2ThreePlusThree m a with
    | true => rfl
    | false =>
      cases h3 : isBand3TwoPlusFour m a with
      | true => rfl
      | false =>
        dsimp [isBand4Residual]
        rw [h, h1, h2, h3]
        rfl

private theorem bool_or_comm (x y : Bool) : (x || y) = (y || x) := by
  cases x <;> cases y <;> rfl

private theorem bool_or_assoc (x y z : Bool) : ((x || y) || z) = (x || (y || z)) := by
  cases x <;> cases y <;> cases z <;> rfl

private theorem bool_or_swap3 (x y z : Bool) : ((x || y) || z) = ((x || z) || y) := by
  cases x <;> cases y <;> cases z <;> rfl

private theorem bool_or_true (x : Bool) : (x || true) = true := by
  cases x <;> rfl

private theorem bool_true_or (x : Bool) : (true || x) = true := by
  cases x <;> rfl

private theorem bool_false_or (x : Bool) : (false || x) = x := by
  cases x <;> rfl

private theorem bool_or_13_group (p a1 a2 a3 b1 b2 b3 c1 c2 c3 d1 d2 d3 : Bool) :
    ((((((((((((p || a1) || a2) || a3) || b1) || b2) || b3) ||
      c1) || c2) || c3) || d1) || d2) || d3) =
    ((((((p || (a1 || b1)) || (a2 || c1)) || (a3 || d1)) ||
      (b2 || c2)) || (b3 || d2)) || (c3 || d3)) := by
  cases p
  case true => repeat (first | rw [bool_true_or] | rw [bool_or_true] | rw [bool_false_or])
  case false =>
  cases a1
  case true => repeat (first | rw [bool_true_or] | rw [bool_or_true] | rw [bool_false_or])
  case false =>
  cases a2
  case true => repeat (first | rw [bool_true_or] | rw [bool_or_true] | rw [bool_false_or])
  case false =>
  cases a3
  case true => repeat (first | rw [bool_true_or] | rw [bool_or_true] | rw [bool_false_or])
  case false =>
  cases b1
  case true => repeat (first | rw [bool_true_or] | rw [bool_or_true] | rw [bool_false_or])
  case false =>
  cases b2
  case true => repeat (first | rw [bool_true_or] | rw [bool_or_true] | rw [bool_false_or])
  case false =>
  cases b3
  case true => repeat (first | rw [bool_true_or] | rw [bool_or_true] | rw [bool_false_or])
  case false =>
  cases c1
  case true => repeat (first | rw [bool_true_or] | rw [bool_or_true] | rw [bool_false_or])
  case false =>
  cases c2
  case true => repeat (first | rw [bool_true_or] | rw [bool_or_true] | rw [bool_false_or])
  case false =>
  cases c3
  case true => repeat (first | rw [bool_true_or] | rw [bool_or_true] | rw [bool_false_or])
  case false =>
  cases d1
  case true => repeat (first | rw [bool_true_or] | rw [bool_or_true] | rw [bool_false_or])
  case false =>
  cases d2
  case true => repeat (first | rw [bool_true_or] | rw [bool_or_true] | rw [bool_false_or])
  case false =>
  cases d3 <;> rfl

/-- Swapping the first two coordinates preserves `isBand1CompletePairs`. -/
theorem isBand1CompletePairs_swap01 (m a0 a1 a2 a3 a4 a5 : Nat) :
    isBand1CompletePairs m [a0, a1, a2, a3, a4, a5] =
      isBand1CompletePairs m [a1, a0, a2, a3, a4, a5] := by
  dsimp [isBand1CompletePairs, with6Nat]
  rw [Nat.add_comm a0 a1]
  let p1 := (a1 + a0 == m && a2 + a3 == m && a4 + a5 == m) ||
            (a1 + a0 == m && a2 + a4 == m && a3 + a5 == m) ||
            (a1 + a0 == m && a2 + a5 == m && a3 + a4 == m)
  let c02 := a0 + a2 == m && a1 + a3 == m && a4 + a5 == m
  let c02' := a1 + a2 == m && a0 + a3 == m && a4 + a5 == m
  let c03 := a0 + a3 == m && a1 + a2 == m && a4 + a5 == m
  let c03' := a1 + a3 == m && a0 + a2 == m && a4 + a5 == m
  let d02 := a0 + a2 == m && a1 + a4 == m && a3 + a5 == m
  let d02' := a1 + a2 == m && a0 + a4 == m && a3 + a5 == m
  let d04 := a0 + a4 == m && a1 + a2 == m && a3 + a5 == m
  let d04' := a1 + a4 == m && a0 + a2 == m && a3 + a5 == m
  let e02 := a0 + a2 == m && a1 + a5 == m && a3 + a4 == m
  let e02' := a1 + a2 == m && a0 + a5 == m && a3 + a4 == m
  let e05 := a0 + a5 == m && a1 + a2 == m && a3 + a4 == m
  let e05' := a1 + a5 == m && a0 + a2 == m && a3 + a4 == m
  let f03 := a0 + a3 == m && a1 + a4 == m && a2 + a5 == m
  let f03' := a1 + a3 == m && a0 + a4 == m && a2 + a5 == m
  let f04 := a0 + a4 == m && a1 + a3 == m && a2 + a5 == m
  let f04' := a1 + a4 == m && a0 + a3 == m && a2 + a5 == m
  let g03 := a0 + a3 == m && a1 + a5 == m && a2 + a4 == m
  let g03' := a1 + a3 == m && a0 + a5 == m && a2 + a4 == m
  let g05 := a0 + a5 == m && a1 + a3 == m && a2 + a4 == m
  let g05' := a1 + a5 == m && a0 + a3 == m && a2 + a4 == m
  let h04 := a0 + a4 == m && a1 + a5 == m && a2 + a3 == m
  let h04' := a1 + a4 == m && a0 + a5 == m && a2 + a3 == m
  let h05 := a0 + a5 == m && a1 + a4 == m && a2 + a3 == m
  let h05' := a1 + a5 == m && a0 + a4 == m && a2 + a3 == m
  have hc : (c02 || c03) = (c02' || c03') := by
    dsimp [c02, c03, c02', c03']
    cases (a0 + a2 == m) <;> cases (a1 + a3 == m) <;>
    cases (a0 + a3 == m) <;> cases (a1 + a2 == m) <;>
    cases (a4 + a5 == m) <;> rfl
  have hd : (d02 || d04) = (d02' || d04') := by
    dsimp [d02, d04, d02', d04']
    cases (a0 + a2 == m) <;> cases (a1 + a4 == m) <;>
    cases (a0 + a4 == m) <;> cases (a1 + a2 == m) <;>
    cases (a3 + a5 == m) <;> rfl
  have he : (e02 || e05) = (e02' || e05') := by
    dsimp [e02, e05, e02', e05']
    cases (a0 + a2 == m) <;> cases (a1 + a5 == m) <;>
    cases (a0 + a5 == m) <;> cases (a1 + a2 == m) <;>
    cases (a3 + a4 == m) <;> rfl
  have hf : (f03 || f04) = (f03' || f04') := by
    dsimp [f03, f04, f03', f04']
    cases (a0 + a3 == m) <;> cases (a1 + a4 == m) <;>
    cases (a0 + a4 == m) <;> cases (a1 + a3 == m) <;>
    cases (a2 + a5 == m) <;> rfl
  have hg : (g03 || g05) = (g03' || g05') := by
    dsimp [g03, g05, g03', g05']
    cases (a0 + a3 == m) <;> cases (a1 + a5 == m) <;>
    cases (a0 + a5 == m) <;> cases (a1 + a3 == m) <;>
    cases (a2 + a4 == m) <;> rfl
  have hh : (h04 || h05) = (h04' || h05') := by
    dsimp [h04, h05, h04', h05']
    cases (a0 + a4 == m) <;> cases (a1 + a5 == m) <;>
    cases (a0 + a5 == m) <;> cases (a1 + a4 == m) <;>
    cases (a2 + a3 == m) <;> rfl
  change ((((((((((((p1 || c02) || d02) || e02) || c03) || f03) || g03) ||
      d04) || f04) || h04) || e05) || g05) || h05) =
    ((((((((((((p1 || c02') || d02') || e02') || c03') || f03') || g03') ||
      d04') || f04') || h04') || e05') || g05') || h05')
  rw [bool_or_13_group p1 c02 d02 e02 c03 f03 g03 d04 f04 h04 e05 g05 h05,
    bool_or_13_group p1 c02' d02' e02' c03' f03' g03' d04' f04' h04' e05' g05' h05',
    hc, hd, he, hf, hg, hh]

/-- Residual Band 4 characters vanish identically for all degrees `3 <= m <= 10`. -/
theorem shioda_aoki_band4_empty_of_le_ten :
    [3, 4, 5, 6, 7, 8, 9, 10].map fermat_band4_count =
      [0, 0, 0, 0, 0, 0, 0, 0] :=
  shioda_aoki_fermat_fourfold_census_m3_to_m10_empty_band4

/-- Degree `m = 12` Fermat fourfold character census and single closed Band 4 Galois orbit. -/
theorem shioda_aoki_m12_band4_orbits :
    fermatCensusSummary 12 =
      (52991, 15101, 21690, 15840, 360,
        [[1, 1, 8, 8, 9, 9], [3, 3, 4, 4, 11, 11],
         [3, 3, 7, 7, 8, 8], [4, 4, 5, 5, 9, 9]]) :=
  shioda_aoki_fermat_m12_census_cert

#print axioms gcdFuel_zero_right
#print axioms gcdFuel_eq_nat_gcd_le_20
#print axioms band_partition_mutually_exclusive
#print axioms band_partition_exhaustive
#print axioms isBand1CompletePairs_swap01
#print axioms shioda_aoki_band4_empty_of_le_ten
#print axioms shioda_aoki_m12_band4_orbits
