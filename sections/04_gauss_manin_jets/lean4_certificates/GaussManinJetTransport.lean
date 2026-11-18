/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
import WiebeSchejaStorch

/-!
# Three-Band Infinitesimal Gauss-Manin Jet Transport and Gotzmann Persistence

This module eliminates the Python-to-Lean verification gap for the blind 3-band
Gauss-Manin jet reconstruction engine (`blind_gauss_manin_jet_reconstructor.py`) in `R(F_0)`:
1. Infinitesimal Gauss-Manin Jacobian reduction step `gaussManinJetStep (wDir prevLam : Poly6)`
   implementing Griffiths-Dwork pole-order reduction on `wDir * prevLam` from degree 18 back to
   `R^{12}(F_0)` and multi-order jet Macaulay rank `jetMacaulayRank6 (jet : List Poly6) (d : Nat)`.
2. Explicit derivation of Band 1 (`Q_2 = V(z_2, z_4, z_0 z_1)`) directly from the static 2-plane
   socle `sigmaPlaneExpected = z_0^4 z_2^4 z_4^4` (`[1, 3, 6, 10, 15, 18, 19]`) via the
   smoothing deformation `wSmoothBand1 = z_0^2 z_1^4` to obtain `lam_1 = z_1^4 z_2^4 z_4^4` and
   prove the multi-component jet `[sigmaPlaneExpected, lam_1]` jumps to rank profile
   `[1, 4, 9, 16, 24, 30, 32]`, with joint degree-1 annihilator dimension `2` (`z_2, z_4`) and
   joint degree-2 annihilator dimension `12` (`1` on the 4-variable slice, `q_2 = z_0 z_1`).
3. Full 6-variable Macaulay rank profiles (`0 <= d <= 6`), annihilator kernels `dim ker M^(d)`,
   and Gotzmann persistence across Band 1 (`G = 2`), Band 2 (`3+3` curve join, `G = 3`),
   and Band 3 (`2+4` surface-curve join, `G = 3`).

All theorems compile constructively with no placeholder proofs and no external dependencies.
-/

/-! ## Part 1: Infinitesimal Gauss-Manin Jet Transport & Joint Jet Contraction in R(F_0) -/

private def gdReduceMonomAux (idx : Nat) (c : Int) (orig revPrefix : Monom6) : Poly6 :=
  match orig with
  | [] => []
  | a :: rest =>
    if Nat.ble 5 a then
      if a == 5 then []
      else
        let newExp := a - 6
        let factor := ((a - 5 : Nat) : Int)
        let newMonom := revPrefix.reverse ++ (newExp :: rest)
        [(newMonom, c * factor)]
    else
      gdReduceMonomAux (idx + 1) c rest (a :: revPrefix)

/-- Griffiths-Dwork Jacobian reduction of a single degree-18 term modulo `J(F_0)`:
writes `z^m = z_i^5 * Q_i` for the first Jacobian variable `a_i >= 5` and applies
pole-lowering differentiation `d/dz_i (Q_i)` to return a degree-12 term. -/
def gdReduceTerm18to12 (m : Monom6) (c : Int) : Poly6 :=
  gdReduceMonomAux 0 c m []

/-- Infinitesimal Gauss-Manin jet transport step `nabla_{d/dt} lam^(k) = M_W lam^(k-1)`:
multiplies the degree-12 dual functional `prevLam` by a degree-6 deformation `wDir`,
applies Griffiths-Dwork Jacobian reduction from degree 18 to degree 12, and reduces
the result in `R^{12}(F_0)`. -/
def gaussManinJetStep (wDir prevLam : Poly6) : Poly6 :=
  let prod18 := polyMul6 wDir prevLam
  let reduced := prod18.foldl (fun acc (m, c) => polyAdd6 acc (gdReduceTerm18to12 m c)) []
  polyModJac6 reduced

/-- Third-order Gauss-Manin jet tuple `[lam^(0), lam^(1), lam^(2), lam^(3)]`. -/
def buildGaussManinJet (wDir lam0 : Poly6) : List Poly6 :=
  let lam1 := gaussManinJetStep wDir lam0
  let lam2 := gaussManinJetStep wDir lam1
  let lam3 := gaussManinJetStep wDir lam2
  [lam0, lam1, lam2, lam3]

/-- Checks whether a polynomial `p` is non-empty and homogeneous of degree `12` in `R(F_0)`. -/
def isNonZeroDeg12 (p : Poly6) : Bool :=
  !p.isEmpty && p.all (fun (m, c) => intNe c 0 && monomDeg6 m == 12 && !monomInJac6 m)

private def tagCompsAux (k : Nat) : List Poly6 → Poly6
  | [] => []
  | p :: rest => p.map (fun (m, c) => (k :: m, c)) ++ tagCompsAux (k + 1) rest

/-- Multi-order joint Macaulay contraction rank `rk(M^(d)_jet : R^d(F_0) -> ⊕_k R^{12+d}(F_0))`:
maps each `m ∈ monomials6 d` to the concatenated reduced list
`jet.map (fun lam => polyModJac6 (polyMul6 [(m, 1)] lam))` and computes its exact linear rank. -/
def jetMacaulayRank6 (jet : List Poly6) (d : Nat) : Nat :=
  let imgs := (monomials6 d).map (fun m =>
    let comps := jet.map (fun lam => polyModJac6 (polyMul6 [(m, 1)] lam))
    tagCompsAux 0 comps)
  polyListRank6 imgs

/-- Joint annihilator kernel dimension `dim ker(M^(d)_jet)` in `R^d(F_0)`. -/
def jetAnnDim6 (jet : List Poly6) (d : Nat) : Nat :=
  (monomials6 d).length - jetMacaulayRank6 jet d

/-- Single-component 6-variable Macaulay contraction rank `rk(M^(d)_lam)`. -/
def macaulayRank6 (lam : Poly6) (d : Nat) : Nat :=
  colonCodim6 lam d

/-- Single-component annihilator kernel dimension `dim ker(M^(d)_lam)` in `R^d(F_0)`. -/
def macaulayAnnDim6 (lam : Poly6) (d : Nat) : Nat :=
  (monomials6 d).length - macaulayRank6 lam d

/-- Checks that every polynomial in `gens` annihilates `lam` in `R(F_0)`. -/
def allAnnihilate (gens : List Poly6) (lam : Poly6) : Bool :=
  gens.all (fun g => (polyModJac6 (polyMul6 g lam)).isEmpty)


/-! ## Part 2: Cyclotomic Band 1, Band 2, and Band 3 Functionals and Deformations -/

/-- Quadric smoothing deformation monomial `W_smooth = z_0^2 z_1^4`, sending
`sigmaPlaneExpected = z_0^4 z_2^4 z_4^4` under `gaussManinJetStep` to `z_1^4 z_2^4 z_4^4`. -/
def wSmoothBand1 : Poly6 :=
  [([2, 4, 0, 0, 0, 0], 1)]

/-- Band 1 dual functional `Lambda_Band1 = (z_0^4 + z_1^4) z_2^4 z_4^4` for `Q_2 = V(z_2, z_4, z_0 z_1)`. -/
def lamBand1 : Poly6 :=
  polyCanon6 [([4, 0, 4, 0, 4, 0], 1), ([0, 4, 4, 0, 4, 0], 1)]

def wDirBand1 : Poly6 :=
  polyCanon6 [([3, 3, 0, 0, 0, 0], 1), ([4, 2, 0, 0, 0, 0], 1), ([2, 4, 0, 0, 0, 0], 1)]

/-- Band 2 dual functional `Lambda_Band2 = z_0^2 z_1^2 z_2^2 z_3^2 z_4^2 z_5^2` (`3+3` curve join). -/
def lamBand2 : Poly6 :=
  [([2, 2, 2, 2, 2, 2], 1)]

def wDirBand2 : Poly6 :=
  polyCanon6 [([4, 1, 0, 1, 0, 0], 1), ([0, 0, 1, 4, 1, 0], 1), ([0, 1, 0, 0, 1, 4], 1)]

/-- Band 3 dual functional `Lambda_Band3 = z_0^4 z_1^2 z_2^2 z_3^2 z_4 z_5` (`2+4` surface-curve join). -/
def lamBand3 : Poly6 :=
  [([4, 2, 2, 2, 1, 1], 1)]

def wDirBand3 : Poly6 :=
  polyCanon6 [([0, 4, 0, 0, 1, 1], 1), ([0, 0, 4, 0, 1, 1], 1), ([0, 0, 0, 4, 1, 1], 1)]

/-- Safe list indexing defaulting to `0`. -/
def listGetZero (xs : List Nat) (i : Nat) : Nat :=
  match xs with
  | [] => 0
  | x :: rest =>
    match i with
    | 0 => x
    | i' + 1 => listGetZero rest i'

/-- Discrete Cauchy convolution of two truncated Hilbert vectors up to `maxDeg`. -/
def convHilbert (a b : List Nat) (maxDeg : Nat) : List Nat :=
  (rangeList 0 (maxDeg + 1)).map (fun d =>
    (rangeList 0 (d + 1)).foldl (fun acc k =>
      acc + listGetZero a k * listGetZero b (d - k)) 0)

/-- Truncated 3-variable cubic-bounded block Hilbert series `(1 + x + x^2)^3`. -/
def curveBlockTrunc3 : List Nat := [1, 3, 6, 7, 6, 3, 1]

/-- Full 3-variable Fermat curve Jacobian ring Hilbert series `(1 + x + x^2 + x^3 + x^4)^3`. -/
def fermatCurveRing3 : List Nat := [1, 3, 6, 10, 12, 12, 10]

/-- Truncated 2-variable quartic-bounded curve block `(1 + x + x^2 + x^3)^2`. -/
def curveBlockTrunc2 : List Nat := [1, 2, 3, 4, 3, 2, 1]


/-! ## Part 3: Macaulay Binomial Expansion & Gotzmann Persistence -/

private def findMacaulayK (rem deg k fuel : Nat) : Nat :=
  match fuel with
  | 0 => k
  | fuel' + 1 =>
    if Nat.ble (binomNat (k + 1) deg) rem then
      findMacaulayK rem deg (k + 1) fuel'
    else
      k

private def macaulayUpperAux (rem deg : Nat) : Nat :=
  match deg with
  | 0 => 0
  | deg' + 1 =>
    if rem == 0 then 0
    else if Nat.ble (binomNat (deg' + 1) (deg' + 1)) rem then
      let k := findMacaulayK rem (deg' + 1) (deg' + 1) (rem + deg' + 1)
      let term := binomNat k (deg' + 1)
      let upperTerm := binomNat (k + 1) (deg' + 2)
      upperTerm + macaulayUpperAux (rem - term) deg'
    else
      macaulayUpperAux rem deg'

/-- Evaluates Macaulay's `d`-binomial upper growth bound `h_d^{<d>}` for `h_d >= 0, d >= 1`. -/
def macaulayUpperBound (h_d d : Nat) : Nat :=
  if h_d == 0 || d == 0 then 0 else macaulayUpperAux h_d d

/-- Verifies Macaulay's growth inequality `h_{d+1} <= h_d^{<d>}` for all `1 <= d < hs.length - 1`. -/
def macaulayGrowthHolds (hs : List Nat) : Bool :=
  (rangeList 1 (hs.length - 2)).all (fun d =>
    Nat.ble (listGetZero hs (d + 1)) (macaulayUpperBound (listGetZero hs d) d))

/-- Evaluates Gotzmann's canonical Hilbert polynomial `sum_{i=1}^G C(t + a_i - i + 1, a_i)`
for a sorted descending exponent list `exps = [a_1, ..., a_G]` and non-negative degree `t`. -/
def gotzmannPoly (exps : List Nat) (t : Nat) : Nat :=
  (rangeList 0 exps.length).foldl (fun acc idx =>
    let ai := listGetZero exps idx
    if Nat.blt (t + ai) idx then acc
    else acc + binomNat (t + ai - idx) ai) 0


/-! ## Part 4: Kernel-Certified Theorems Across Bands 1, 2, and 3 -/

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
/-- Band 1 Gauss-Manin Jet Transport and Quadric Recovery Certificate:
1. Static single plane `sigmaPlaneExpected = z_0^4 z_2^4 z_4^4` has rank profile `[1, 3, 6, 10, 15, 18, 19]`.
2. Applying `gaussManinJetStep wSmoothBand1 sigmaPlaneExpected` produces `lam_1 = z_1^4 z_2^4 z_4^4`.
3. The deformed first-order jet sum `deformedBand1 = sigmaPlaneExpected + lam_1` equals `lamBand1`,
   whose rank jumps from `[1, 3, 6, 10, 15, 18, 19]` to `[1, 4, 9, 16, 24, 30, 32]`.
4. The multi-component 2-jet `jet2 := [sigmaPlaneExpected, lam_1]` has joint rank profile
   `[1, 4, 9, 16, 25, 32, 35]` (matching the unquotiented quadric surface `Q_2 = V(z_2, z_4, z_0 z_1)`
   through degree 4 before the Artinian Gorenstein socle relation `z_0^4 - z_1^4`), joint degree-1
   annihilator dimension `2` (`z_2, z_4`), and joint degree-2 annihilator dimension `12`
   (`10 - 9 = 1` on the 4-variable slice, spanned by `q_2 = z_0 z_1`).
5. Third-order jet `buildGaussManinJet wDirBand1 deformedBand1` produces 4 non-zero degree-12 classes
   retaining `[z_2, z_4]`, and Gotzmann persistence holds at `G = 2` (`macaulayUpperBound 9 2 = 16`). -/
theorem gauss_manin_band1_quadric_jet_cert :
    let lam1 := gaussManinJetStep wSmoothBand1 sigmaPlaneExpected
    let deformedBand1 := polyAdd6 sigmaPlaneExpected lam1
    let jet2 := [sigmaPlaneExpected, lam1]
    let jet3 := buildGaussManinJet wDirBand1 deformedBand1
    let staticRanks := [0, 1, 2, 3, 4, 5, 6].map (macaulayRank6 sigmaPlaneExpected)
    let deformedRanks := [0, 1, 2, 3, 4, 5, 6].map (macaulayRank6 deformedBand1)
    let jointRanks := [0, 1, 2, 3, 4, 5, 6].map (jetMacaulayRank6 jet2)
    staticRanks = [1, 3, 6, 10, 15, 18, 19] ∧
    polyEq6 lam1 [([0, 4, 4, 0, 4, 0], 1)] = true ∧
    polyEq6 deformedBand1 lamBand1 = true ∧
    deformedRanks = [1, 4, 9, 16, 24, 30, 32] ∧
    jointRanks = [1, 4, 9, 16, 25, 32, 35] ∧
    (jetAnnDim6 jet2 1, binomNat 5 2 - jetMacaulayRank6 jet2 2, jetAnnDim6 jet2 2) = (2, 1, 12) ∧
    jet2.all (allAnnihilate [varPow6 2 1, varPow6 4 1]) = true ∧
    jet2.all (allAnnihilate [polyMul6 (varPow6 0 1) (varPow6 1 1)]) = true ∧
    jet3.length = 4 ∧
    jet3.all isNonZeroDeg12 = true ∧
    jet3.all (allAnnihilate [varPow6 2 1, varPow6 4 1]) = true ∧
    macaulayGrowthHolds deformedRanks = true ∧
    macaulayGrowthHolds jointRanks = true ∧
    macaulayUpperBound 9 2 = 16 ∧
    [0, 1, 2, 3].map (gotzmannPoly [2, 2]) = [1, 4, 9, 16] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
/-- Band 2 Gauss-Manin Jet Transport and 3+3 Curve-Join Certificate:
1. Third-order jet `buildGaussManinJet wDirBand2 lamBand2` produces 4 non-zero degree-12 classes
   in `R^{12}(F_0)`.
2. Exact 6-variable Macaulay rank profile for `0 <= d <= 6` is `[1, 6, 21, 50, 90, 126, 141]`,
   matching both `jetMacaulayRank6 [lamBand2]` and the discrete convolution of the two 3-variable blocks.
3. Linear and quadric annihilators vanish (`dim ker M^(1) = 0`, `dim ker M^(2) = 0`), while
   cubic syzygies emerge at Gotzmann regularity `G = 3` with `dim ker M^(3) = 56 - 50 = 6`,
   spanned explicitly by `[z_0^3, z_1^3, z_2^3, z_3^3, z_4^3, z_5^3]`.
4. Macaulay growth holds across `d = 1..5`, with persistence at `d = 1 -> 2`
   (`macaulayUpperBound 6 1 = 21`) and first syzygy drop at `d = 3` (`50 < 56 = 21^{<2>}`). -/
theorem gauss_manin_band2_curve_join_jet_cert :
    let jet := buildGaussManinJet wDirBand2 lamBand2
    let ranks := [0, 1, 2, 3, 4, 5, 6].map (jetMacaulayRank6 [lamBand2])
    let cubics := [0, 1, 2, 3, 4, 5].map (fun i => varPow6 i 3)
    jet.length = 4 ∧
    jet.all isNonZeroDeg12 = true ∧
    ranks = [1, 6, 21, 50, 90, 126, 141] ∧
    convHilbert curveBlockTrunc3 curveBlockTrunc3 6 = ranks ∧
    (jetAnnDim6 [lamBand2] 1, jetAnnDim6 [lamBand2] 2,
      jetAnnDim6 [lamBand2] 3) = (0, 0, 6) ∧
    allAnnihilate cubics lamBand2 = true ∧
    macaulayGrowthHolds ranks = true ∧
    macaulayUpperBound 6 1 = 21 ∧
    macaulayUpperBound 21 2 = 56 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
/-- Band 3 Gauss-Manin Jet Transport and 2+4 Surface-Curve Join Certificate:
1. Third-order jet `buildGaussManinJet wDirBand3 lamBand3` produces 4 non-zero degree-12 classes
   in `R^{12}(F_0)`, every order retaining the linear hyperplane annihilator `z_0`.
2. Exact 6-variable Macaulay rank profile for `0 <= d <= 6` is `[1, 5, 15, 32, 53, 71, 78]`,
   matching both `jetMacaulayRank6 [lamBand3]` and the discrete convolution of the 3-variable and 2-variable blocks.
3. Linear annihilator dimension is `dim ker M^(1) = 6 - 5 = 1`, quadric syzygies on the active
   5-variable hyperplane slice vanish (`binomNat 6 2 - 15 = 0`), and cubic syzygies emerge at
   Gotzmann regularity `G = 3` (`binomNat 7 3 - 32 = 3`, spanned by `[z_1^3, z_2^3, z_3^3]`).
4. Macaulay growth holds across `d = 1..5`, with persistence at `d = 1 -> 2`
   (`macaulayUpperBound 5 1 = 15`) and first nonlinear drop at `d = 3` (`32 < 35 = 15^{<2>}`). -/
theorem gauss_manin_band3_surface_curve_jet_cert :
    let jet := buildGaussManinJet wDirBand3 lamBand3
    let ranks := [0, 1, 2, 3, 4, 5, 6].map (jetMacaulayRank6 [lamBand3])
    let sliceCubics := [varPow6 1 3, varPow6 2 3, varPow6 3 3]
    jet.length = 4 ∧
    jet.all isNonZeroDeg12 = true ∧
    jet.all (allAnnihilate [varPow6 0 1]) = true ∧
    ranks = [1, 5, 15, 32, 53, 71, 78] ∧
    convHilbert curveBlockTrunc3 curveBlockTrunc2 6 = ranks ∧
    (jetAnnDim6 [lamBand3] 1, binomNat 6 2 - jetMacaulayRank6 [lamBand3] 2,
      binomNat 7 3 - jetMacaulayRank6 [lamBand3] 3) = (1, 0, 3) ∧
    allAnnihilate sliceCubics lamBand3 = true ∧
    macaulayGrowthHolds ranks = true ∧
    macaulayUpperBound 5 1 = 15 ∧
    macaulayUpperBound 15 2 = 35 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

#print axioms gauss_manin_band1_quadric_jet_cert
#print axioms gauss_manin_band2_curve_join_jet_cert
#print axioms gauss_manin_band3_surface_curve_jet_cert
