/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
import ShiodaFormalConjectures

/-!
# Phase 5 (Wall 4): Complete-Intersection Cayley-Trick Jacobian Spectrum

Distinguishes two exact Artinian Gorenstein / Hodge spectra for smooth codimension-2 complete
intersection fourfolds `X_{d_1, d_2} = V(F_1, F_2) ⊂ P^6`:
1. The **7-variable auxiliary split Jacobian ring** `(1 + t + ... + t^{d_max - 2})^7`:
   - `d_max = 3` (`X_{3,3}` block): `(1 + t)^7 = [1, 7, 21, 35, 35, 21, 7, 1]` (sum `128`),
   - `d_max = 4` (`X_{3,4}`, `X_{4,4}` block): `(1 + t + t^2)^7` (length `15`, sum `2187`),
   - `d_max = 5` (`X_{2,5}` block): `(1 + t + t^2 + t^3)^7` (length `22`, sum `16384`),
   whereas the **full bigraded / weighted Cayley quotient** `R(y_1 F_1 + y_2 F_2)` on `P^6 × P^1`
   with `wt(z_i) = 1, wt(y_k) = d_max + 1 - d_k` is tracked in `counterexample_sieve.py`.
2. The exact palindromic primitive middle Hodge diamonds `[h^{4,0}_prim, ..., h^{0,4}_prim]`
   for `X_{3,3}`, `X_{3,4}`, and `X_{2,5}`.
-/

private def listGetNat (xs : List Nat) (i : Nat) : Nat :=
  match xs with
  | [] => 0
  | x :: rest => match i with | 0 => x | i' + 1 => listGetNat rest i'

private def polyConvNat (a b : List Nat) : List Nat :=
  let n := a.length + b.length - 1
  (rangeList 0 n).map (fun d =>
    (rangeList 0 (d + 1)).foldl (fun acc k =>
      acc + listGetNat a k * listGetNat b (d - k)) 0)

private def powConvNat (base : List Nat) : Nat → List Nat
  | 0 => [1]
  | k + 1 => polyConvNat base (powConvNat base k)

/-- 7-variable `(1 + t)^7` auxiliary Jacobian Hilbert series for `(3,3)` Fermat-type blocks. -/
def cayleyCI33AuxHilbertSeries : List Nat :=
  powConvNat [1, 1] 7

/-- 7-variable `(1 + t + t^2)^7` auxiliary Jacobian Hilbert series for `X_{3,4} ⊂ P^6`. -/
def cayleyCI34HilbertSeries : List Nat :=
  powConvNat [1, 1, 1] 7

/-- 7-variable `(1 + t + t^2 + t^3)^7` auxiliary Jacobian Hilbert series for `X_{2,5} ⊂ P^6`. -/
def cayleyCI25AuxHilbertSeries : List Nat :=
  powConvNat [1, 1, 1, 1] 7

/-- Primitive middle Hodge diamonds `[h^{4,0}, h^{3,1}, h^{2,2}, h^{1,3}, h^{0,4}]`
for smooth complete intersections `(3,3)`, `(3,4)`, and `(2,5)` in `P^6`. -/
def hodgePrimCI33 : List Nat := [0, 49, 266, 49, 0]
def hodgePrimCI34 : List Nat := [1, 237, 995, 237, 1]
def hodgePrimCI25 : List Nat := [1, 356, 1471, 356, 1]

/-- Exact Gorenstein palindromic symmetry of `cayleyCI34HilbertSeries` (socle degree `14`,
length `15`, peak `393`, total Milnor dimension `3^7 = 2187`). -/
theorem cayley_ci34_gorenstein_palindromic_cert :
    cayleyCI34HilbertSeries = [1, 7, 28, 77, 161, 266, 357, 393, 357, 266, 161, 77, 28, 7, 1] ∧
    cayleyCI34HilbertSeries.length = 15 ∧
    (cayleyCI34HilbertSeries == cayleyCI34HilbertSeries.reverse) = true ∧
    cayleyCI34HilbertSeries.foldl (· + ·) 0 = 2187 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Verified `(3,3)`, `(3,4)`, and `(2,5)` auxiliary Gorenstein and primitive Hodge symmetry:
1. `(3,3)` auxiliary `(1 + t)^7` is palindromic of length `8`, sum `128`, with primitive Hodge
   diamond `[0, 49, 266, 49, 0]` (palindromic, total `364`).
2. `(3,4)` Calabi-Yau primitive Hodge diamond `[1, 237, 995, 237, 1]` is palindromic (total `1471`).
3. `(2,5)` Calabi-Yau auxiliary `(1 + t + t^2 + t^3)^7` is palindromic of length `22`, sum `16384`,
   with primitive Hodge diamond `[1, 356, 1471, 356, 1]` (palindromic, total `2185`). -/
theorem cayley_ci33_and_ci34_gorenstein_symmetry_cert :
    cayleyCI33AuxHilbertSeries = [1, 7, 21, 35, 35, 21, 7, 1] ∧
    (cayleyCI33AuxHilbertSeries == cayleyCI33AuxHilbertSeries.reverse) = true ∧
    cayleyCI33AuxHilbertSeries.foldl (· + ·) 0 = 128 ∧
    (cayleyCI25AuxHilbertSeries.length = 22) ∧
    (cayleyCI25AuxHilbertSeries == cayleyCI25AuxHilbertSeries.reverse) = true ∧
    cayleyCI25AuxHilbertSeries.foldl (· + ·) 0 = 16384 ∧
    (hodgePrimCI33 == hodgePrimCI33.reverse) = true ∧
    hodgePrimCI33.foldl (· + ·) 0 = 364 ∧
    (hodgePrimCI34 == hodgePrimCI34.reverse) = true ∧
    hodgePrimCI34.foldl (· + ·) 0 = 1471 ∧
    (hodgePrimCI25 == hodgePrimCI25.reverse) = true ∧
    hodgePrimCI25.foldl (· + ·) 0 = 2185 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

#print axioms cayley_ci34_gorenstein_palindromic_cert
#print axioms cayley_ci33_and_ci34_gorenstein_symmetry_cert
