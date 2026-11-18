/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
import WiebeSchejaStorch

/-!
# Global 1751 x 426 -> 426 IVHS Obstruction Spectrum and Gorenstein Poincare Duality

This module formalizes the global Infinitesimal Variation of Hodge Structure (IVHS)
pairing `R^{12}(F_0) × R^6(F_0) -> R^{18}(F_0)` on the Fermat sextic Calabi-Yau fourfold `X_6^4`:
1. Direct 6-variable cohomology basis enumeration `[1, 426, 1751, 426, 1]` in degrees
   `[0, 6, 12, 18, 24]` and exact Gorenstein Poincare duality bijection `poincareDualMonom6`
   pairing `R^6 <-> R^{18}` and `R^{12} <-> R^{12}` into the unique socle `[4, 4, 4, 4, 4, 4]`.
2. Exact 6-variable IVHS obstruction rank evaluator `monomIVHSRank` and Noether-Lefschetz
   tangent dimension `monomNLTangentDim m := 426 - monomIVHSRank m` across all 1,751 modes
   of `monomials6 12`, verified against `colonCodim6 [(p, 1)] 6` on all 18 exponent partitions.
3. Extremal characterization of the 20 coordinate 2-planes (`rank = 19`, `dim T_NL = 407`)
   and unique central mode `[2, 2, 2, 2, 2, 2]` (`rank = 141`, `dim T_NL = 285`), together with
   the complete 17-rank / 18-partition decomposition summing to 1,751 and constructive
   surjectivity `R^{12}(F_0) ⊗ R^6(F_0) ↠ R^{18}(F_0)` across all 426 target monomials.

All theorems compile constructively with no placeholder proofs and no external dependencies.
-/

/-! ## Part 1: Gorenstein Poincare Duality Involution -/

/-- Poincare dual exponent vector `4 - e_i` in the Fermat sextic Jacobian ring `R(F_0)`. -/
def poincareDualMonom6 (m : Monom6) : Monom6 :=
  m.map (fun e => 4 - e)

/-- Unique degree-24 Gorenstein socle monomial `z_0^4 z_1^4 z_2^4 z_3^4 z_4^4 z_5^4`. -/
def socleMonom6 : Monom6 :=
  [4, 4, 4, 4, 4, 4]

private def strictLexLt6 (l1 l2 : Monom6) : Bool :=
  match l1 with
  | [] => false
  | x :: xs =>
    match l2 with
    | [] => false
    | y :: ys => if x == y then strictLexLt6 xs ys else Nat.blt x y

/-- Verifies a list of 6-variable monomials is strictly increasing (hence pairwise distinct). -/
def isStrictLexSorted6 : List Monom6 → Bool
  | [] => true
  | x :: xs =>
    match xs with
    | [] => true
    | y :: ys => strictLexLt6 x y && isStrictLexSorted6 (y :: ys)


/-! ## Part 2: Exhaustive IVHS Obstruction Rank & Exponent Partition Helpers -/

private def getNatAtZero (xs : List Nat) (idx : Nat) : Nat :=
  match xs with
  | [] => 0
  | x :: rest =>
    match idx with
    | 0 => x
    | idx' + 1 => getNatAtZero rest idx'

private def countBoundedSumAux (s : Nat) (dp : List Nat) (b : Nat) : List Nat :=
  (rangeList 0 (s + 1)).map (fun j =>
    (rangeList 0 (b + 1)).foldl (fun acc k =>
      if Nat.blt j k then acc
      else acc + getNatAtZero dp (j - k)) 0)

/-- Counts tuples `(k_0, ..., k_5)` with `0 <= k_i <= b_i` and `sum k_i = s` via exact DP. -/
def countBoundedSum (bounds : List Nat) (s : Nat) : Nat :=
  let init := 1 :: (rangeList 0 s).map (fun _ => 0)
  let finalDp := bounds.foldl (countBoundedSumAux s) init
  getNatAtZero finalDp s

/-- Exact IVHS obstruction rank `rk(z^m · - : R^6(F_0) -> R^{18}(F_0))` for `m ∈ R^{12}(F_0)`. -/
def monomIVHSRank (m : Monom6) : Nat :=
  countBoundedSum (poincareDualMonom6 m) 6

/-- Noether-Lefschetz tangent space dimension `426 - monomIVHSRank m` inside `R^6(F_0)`. -/
def monomNLTangentDim (m : Monom6) : Nat :=
  426 - monomIVHSRank m

private def insertNatDesc (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if Nat.ble y x then x :: y :: ys else y :: insertNatDesc x ys

/-- Sorts a monomial's exponent list in non-increasing order (`S_6` partition type). -/
def sortMonomDesc : List Nat → List Nat
  | [] => []
  | x :: xs => insertNatDesc x (sortMonomDesc xs)

/-- All 18 sorted partitions of `12` into `6` non-negative parts `<= 4`. -/
def all18Partitions12 : List Monom6 :=
  [[4, 4, 4, 0, 0, 0],
   [4, 4, 3, 1, 0, 0],
   [4, 4, 2, 2, 0, 0],
   [4, 4, 2, 1, 1, 0],
   [4, 4, 1, 1, 1, 1],
   [4, 3, 3, 2, 0, 0],
   [4, 3, 3, 1, 1, 0],
   [4, 3, 2, 2, 1, 0],
   [4, 3, 2, 1, 1, 1],
   [3, 3, 3, 3, 0, 0],
   [4, 2, 2, 2, 2, 0],
   [4, 2, 2, 2, 1, 1],
   [3, 3, 3, 2, 1, 0],
   [3, 3, 3, 1, 1, 1],
   [3, 3, 2, 2, 2, 0],
   [3, 3, 2, 2, 1, 1],
   [3, 2, 2, 2, 2, 1],
   [2, 2, 2, 2, 2, 2]]

/-- Expected `(rank, modeCount)` histogram across the 17 distinct IVHS ranks of `R^{12}(F_0)`. -/
def expectedIVHSRankCensus : List (Nat × Nat) :=
  [(19, 20), (32, 180), (37, 90), (40, 180), (44, 15),
   (50, 180), (54, 180), (62, 360), (68, 135), (71, 30),
   (78, 60), (84, 120), (92, 20), (96, 60), (106, 90),
   (122, 30), (141, 1)]

/-- Expected `(partition, rank, orbitCount)` census across all 18 exponent partitions of `R^{12}(F_0)`. -/
def expectedPartitionCensus : List (Monom6 × Nat × Nat) :=
  [([4, 4, 4, 0, 0, 0], 19, 20),
   ([4, 4, 3, 1, 0, 0], 32, 180),
   ([4, 4, 2, 2, 0, 0], 37, 90),
   ([4, 4, 2, 1, 1, 0], 40, 180),
   ([4, 4, 1, 1, 1, 1], 44, 15),
   ([4, 3, 3, 2, 0, 0], 50, 180),
   ([4, 3, 3, 1, 1, 0], 54, 180),
   ([4, 3, 2, 2, 1, 0], 62, 360),
   ([4, 3, 2, 1, 1, 1], 68, 120),
   ([3, 3, 3, 3, 0, 0], 68, 15),
   ([4, 2, 2, 2, 2, 0], 71, 30),
   ([4, 2, 2, 2, 1, 1], 78, 60),
   ([3, 3, 3, 2, 1, 0], 84, 120),
   ([3, 3, 3, 1, 1, 1], 92, 20),
   ([3, 3, 2, 2, 2, 0], 96, 60),
   ([3, 3, 2, 2, 1, 1], 106, 90),
   ([3, 2, 2, 2, 2, 1], 122, 30),
   ([2, 2, 2, 2, 2, 2], 141, 1)]

private def splitTakeUpTo (rem : Nat) : List Nat → Monom6 × Monom6
  | [] => ([], [])
  | c :: cs =>
    let b := if Nat.ble c rem then c else rem
    let (ms, bs) := splitTakeUpTo (rem - b) cs
    ((c - b) :: ms, b :: bs)

/-- Constructively decomposes any `c ∈ R^{18}(F_0)` into `m ∈ R^{12}(F_0)` and
`b ∈ R^6(F_0)` such that `z^m · z^b = z^c`. -/
def splitMonom18to12And6 (c : Monom6) : Monom6 × Monom6 :=
  splitTakeUpTo 6 c


/-! ## Part 3: Kernel-Certified Global IVHS & Poincare Duality Theorems -/

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
/-- Gorenstein Poincare Duality Bijection Certificate for `R(F_0)`:
1. Direct 6-variable basis counts in degrees `[0, 6, 12, 18, 24]` equal `[1, 426, 1751, 426, 1]`,
   and bases in degrees `6, 12, 18` are strictly lex-sorted (pairwise distinct).
2. `poincareDualMonom6` is an involution pairing every `m ∈ R^6 ∪ R^{12} ∪ R^{18}`
   into `socleMonom6 = [4, 4, 4, 4, 4, 4]`.
3. `poincareDualMonom6` maps `monomials6 6` bijectively to `(monomials6 18).reverse`,
   `monomials6 18` bijectively to `(monomials6 6).reverse`, and `monomials6 12`
   bijectively to `(monomials6 12).reverse`. -/
theorem gorenstein_poincare_duality_bijection_cert :
    let m6 := monomials6 6
    let m12 := monomials6 12
    let m18 := monomials6 18
    [0, 6, 12, 18, 24].map (fun d => (monomials6 d).length) = [1, 426, 1751, 426, 1] ∧
    (isStrictLexSorted6 m6 && isStrictLexSorted6 m12 && isStrictLexSorted6 m18) = true ∧
    (m6 ++ m12 ++ m18).all (fun m =>
      (poincareDualMonom6 (poincareDualMonom6 m) == m) &&
      (monomMul6 m (poincareDualMonom6 m) == socleMonom6)) = true ∧
    (m6.map poincareDualMonom6).length = 426 ∧
    m6.map poincareDualMonom6 = m18.reverse ∧
    m18.map poincareDualMonom6 = m6.reverse ∧
    m12.map poincareDualMonom6 = m12.reverse :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
/-- Global 1,751-Mode IVHS Obstruction Spectrum & Surjectivity Certificate:
1. Across all 18 exponent partitions `p ∈ all18Partitions12`, `monomIVHSRank p == colonCodim6 [(p, 1)] 6`.
2. Across all 1,751 monomials `m ∈ monomials6 12`, `19 <= monomIVHSRank m <= 141`
   (equivalently `285 <= monomNLTangentDim m <= 407`).
3. Minimum obstruction (`rank = 19`, `dim T_NL = 407`) is attained by exactly 20 modes,
   each having `S_6` exponent partition `[4, 4, 4, 0, 0, 0]` (the 20 coordinate 2-plane socles).
4. Maximum obstruction (`rank = 141`, `dim T_NL = 285`) is attained by the unique mode
   `[[2, 2, 2, 2, 2, 2]]`.
5. All 1,751 modes partition exactly into the 17 IVHS rank buckets and 18 `S_6` partition
   buckets with counts summing to `1751`.
6. Every target monomial `c ∈ monomials6 18` splits constructively as `m * b` with
   `m ∈ R^{12}(F_0)` and `b ∈ R^6(F_0)`, proving global surjectivity `R^{12} ⊗ R^6 ↠ R^{18}`. -/
theorem global_ivhs_1751_obstruction_spectrum_cert :
    let m12 := monomials6 12
    let m18 := monomials6 18
    let ranks12 := m12.map monomIVHSRank
    let parts12 := m12.map sortMonomDesc
    let minModes := m12.filter (fun m => monomIVHSRank m == 19)
    let maxModes := m12.filter (fun m => monomIVHSRank m == 141)
    let rankCensus := expectedIVHSRankCensus.map (fun (r, _) => (r, (ranks12.filter (· == r)).length))
    let partCensus := expectedPartitionCensus.map (fun (p, _, _) =>
      (p, monomIVHSRank p, (parts12.filter (· == p)).length))
    all18Partitions12.all (fun p => monomIVHSRank p == colonCodim6 [(p, 1)] 6) = true ∧
    ranks12.all (fun r => Nat.ble 19 r && Nat.ble r 141) = true ∧
    m12.all (fun m => Nat.ble 285 (monomNLTangentDim m) && Nat.ble (monomNLTangentDim m) 407) = true ∧
    minModes.length = 20 ∧
    minModes.all (fun m => sortMonomDesc m == [4, 4, 4, 0, 0, 0]) = true ∧
    maxModes = [[2, 2, 2, 2, 2, 2]] ∧
    rankCensus = expectedIVHSRankCensus ∧
    (rankCensus.foldl (fun acc (_, c) => acc + c) 0) = 1751 ∧
    partCensus = expectedPartitionCensus ∧
    (partCensus.foldl (fun acc (_, _, c) => acc + c) 0) = 1751 ∧
    m18.all (fun c =>
      let (m, b) := splitMonom18to12And6 c
      monomDeg6 m == 12 && !monomInJac6 m &&
      monomDeg6 b == 6 && !monomInJac6 b &&
      (monomMul6 m b == c)) = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

#print axioms gorenstein_poincare_duality_bijection_cert
#print axioms global_ivhs_1751_obstruction_spectrum_cert
