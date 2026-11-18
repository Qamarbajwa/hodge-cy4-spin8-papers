/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
import HodgeVerification

/-!
# Full D_4 Root System, Order-3 Outer Triality Automorphism tau, and Subalgebra Kernels

This module formalizes the complete Lie algebra root geometry of `D_4 = so(8)` and its
order-3 outer triality automorphism `tau` in Lean 4:
1. Full 24-root system `Phi(D_4)` (`d4AllRoots`), 12 positive roots `Phi^+(D_4)` (`d4PositiveRoots`),
   Euclidean inner product `weightDot`, and Weyl reflections `weylReflect` across all 24 roots,
   proving involution, inner-product isometry, and bijective invariance on `d4AllRoots`, `S^+_8`,
   `S^-_8`, and `V_8`.
2. Order-3 outer triality automorphism `outerTrialityTau := hadamardTriality ∘ trialityReflect3`:
   - Cycles the three peripheral simple roots `alpha_1 -> alpha_4 -> alpha_3 -> alpha_1` while
     fixing the central node `alpha_2`.
   - Cycles the three 8-dimensional representations `V_8 -> S^+_8 -> S^-_8 -> V_8` bijectively
     with `tau^3 = id`.
   - Preserves `d4AllRoots`, `d4PositiveRoots`, and the inner product `weightDot`.
3. Root subsystem Casimir Gram matrices `rootSubsystemGram6` on the 6-dimensional Cartan
   zero-weight space `(⋀^4 S^+_8)_0`:
   - Full `Phi^+(D_4)` (12 roots) and `Phi(D_4)` (24 roots) both have rank `6` (zero `so(8)` singlets).
   - Peripheral `A_1 x A_1 x A_1` subsystem `[alpha_1, alpha_3, alpha_4]` has rank `4` (2-dim kernel).
   - Connected pairs `[alpha_1, alpha_2]`, `[alpha_2, alpha_3]`, `[alpha_2, alpha_4]` all have rank `4`,
     and the three triality-conjugate closed `A_3 = so(6)` root subsystems cycled by `tau`
     all have identical Gram rank `6`.

All theorems compile constructively with no placeholder proofs and no external dependencies.
-/

/-! ## Part 1: Full 24-Root System Phi(D_4) and Weyl Reflections -/

/-- The 12 positive roots `2 e_i ± 2 e_j` (`0 <= i < j <= 3`) of `D_4 = so(8)`. -/
def d4PositiveRoots : List Weight :=
  [0, 1, 2, 3].foldl (fun acc i =>
    [0, 1, 2, 3].foldl (fun acc2 j =>
      if Nat.blt i j then
        acc2 ++ [addW4 (basisVec4 i 2) (basisVec4 j (-2)),
                 addW4 (basisVec4 i 2) (basisVec4 j 2)]
      else acc2) acc) []

/-- Negation of a `Weight` vector. -/
def negWeight (w : Weight) : Weight :=
  (-w.1, -w.2.1, -w.2.2.1, -w.2.2.2)

/-- Full 24-root system `Phi(D_4) = Phi^+(D_4) ∪ (-Phi^+(D_4))`. -/
def d4AllRoots : List Weight :=
  d4PositiveRoots ++ d4PositiveRoots.map negWeight

/-- Euclidean Cartan/Killing inner product `<u, v>` on scaled `Weight` vectors. -/
def weightDot (u v : Weight) : Int :=
  u.1 * v.1 + u.2.1 * v.2.1 + u.2.2.1 * v.2.2.1 + u.2.2.2 * v.2.2.2

/-- Exact equality check on `Weight`. -/
def weightEq (u v : Weight) : Bool :=
  intEq u.1 v.1 && intEq u.2.1 v.2.1 && intEq u.2.2.1 v.2.2.1 && intEq u.2.2.2 v.2.2.2

/-- Exact Weyl reflection `s_alpha(w) = w - (2 <w, alpha> / <alpha, alpha>) * alpha`,
where every root `alpha ∈ Phi(D_4)` has `<alpha, alpha> = 8`. -/
def weylReflect (alpha w : Weight) : Weight :=
  let k := weightDot w alpha / 4
  (w.1 - k * alpha.1,
   w.2.1 - k * alpha.2.1,
   w.2.2.1 - k * alpha.2.2.1,
   w.2.2.2 - k * alpha.2.2.2)

/-- Checks whether `f` maps `src` bijectively onto `dst` as distinct sets of weights. -/
def isWeightBijection (f : Weight → Weight) (src dst : List Weight) : Bool :=
  src.length == dst.length &&
  src.all (fun w => dst.any (fun y => weightEq (f w) y)) &&
  dst.all (fun y => src.any (fun w => weightEq (f w) y))


/-! ## Part 2: Order-3 Outer Triality Automorphism tau of Spin(8) -/

/-- Sign-flip reflection on the 4th coordinate (`r_3`). -/
def trialityReflect3 (w : Weight) : Weight :=
  (w.1, w.2.1, w.2.2.1, -w.2.2.2)

/-- Integer Hadamard triality involution `H_tri` on doubled `Weight` coordinates. -/
def hadamardTriality (w : Weight) : Weight :=
  ((w.1 + w.2.1 + w.2.2.1 + w.2.2.2) / 2,
   (w.1 + w.2.1 - w.2.2.1 - w.2.2.2) / 2,
   (w.1 - w.2.1 + w.2.2.1 - w.2.2.2) / 2,
   (w.1 - w.2.1 - w.2.2.1 + w.2.2.2) / 2)

/-- Order-3 outer triality automorphism `tau = H_tri ∘ r_3` of `D_4 = so(8)`. -/
def outerTrialityTau (w : Weight) : Weight :=
  hadamardTriality (trialityReflect3 w)


/-! ## Part 3: Full Root Subsystem Casimir Gram Matrices on (⋀^4 S^+_8)_0 -/

/-- Constructs the 6x6 Gram matrix of an arbitrary root list `roots ⊆ Phi(D_4)`
acting on the 6-dimensional Cartan zero-weight space `zeroIndexTuples ⊂ ⋀^4 S^+_8`. -/
def rootSubsystemGram6 (roots : List Weight) : List (List Int) :=
  let imgs := roots.map (fun alpha => zeroIndexTuples.map (applyRootToTuple alpha))
  (rangeList 0 6).map (fun a =>
    (rangeList 0 6).map (fun b =>
      imgs.foldl (fun acc rootImgs =>
        let ta := match rootImgs.drop a with | x :: _ => x | [] => []
        let tb := match rootImgs.drop b with | x :: _ => x | [] => []
        acc + dotTupleTerms ta tb) 0))

/-- Exact rank of the 6x6 root subsystem Gram matrix on `(⋀^4 S^+_8)_0`. -/
def rootSubsystemRank6 (roots : List Weight) : Nat :=
  intMatRankAuxClean 6 (rootSubsystemGram6 roots)

private def simpleAlpha1 : Weight := addW4 (basisVec4 0 2) (basisVec4 1 (-2))
private def simpleAlpha2 : Weight := addW4 (basisVec4 1 2) (basisVec4 2 (-2))
private def simpleAlpha3 : Weight := addW4 (basisVec4 2 2) (basisVec4 3 (-2))
private def simpleAlpha4 : Weight := addW4 (basisVec4 2 2) (basisVec4 3 2)

/-- Three triality-conjugate closed `A_3 = so(6)` positive-root subsystems (6 roots each)
and full root subsystems (12 roots each), obtained by intersecting `Phi(D_4)` with the
hyperplanes orthogonal to `(2,0,0,0) ∈ V_8`, `(1,1,1,1) ∈ S^+_8`, and `(1,1,1,-1) ∈ S^-_8`. -/
def a3PosDropAlpha1 : List Weight := d4PositiveRoots.filter (fun r => intEq (weightDot r (2, 0, 0, 0)) 0)
def a3PosDropAlpha3 : List Weight := d4PositiveRoots.filter (fun r => intEq (weightDot r (1, 1, 1, 1)) 0)
def a3PosDropAlpha4 : List Weight := d4PositiveRoots.filter (fun r => intEq (weightDot r (1, 1, 1, -1)) 0)

def a3AllDropAlpha1 : List Weight := d4AllRoots.filter (fun r => intEq (weightDot r (2, 0, 0, 0)) 0)
def a3AllDropAlpha3 : List Weight := d4AllRoots.filter (fun r => intEq (weightDot r (1, 1, 1, 1)) 0)
def a3AllDropAlpha4 : List Weight := d4AllRoots.filter (fun r => intEq (weightDot r (1, 1, 1, -1)) 0)


/-! ## Part 4: Kernel-Certified Theorems for D_4 Roots, Triality tau, and Subalgebras -/

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
/-- Weyl Reflection Invariance Certificate across all 24 roots of `Phi(D_4)`:
1. `d4PositiveRoots.length = 12`, `d4AllRoots.length = 24`, and every root has squared norm `8`.
2. For all `alpha ∈ d4AllRoots`, `weylReflect alpha` is an involution on all weights in
   `d4AllRoots ∪ V_8 ∪ S^+_8 ∪ S^-_8`, preserves `weightDot`, and bijectively permutes
   `d4AllRoots`, `so8Weights` (`S^+_8`), `so8OddSpinorWeights` (`S^-_8`), and `so8VectorWeights` (`V_8`). -/
theorem d4_weyl_reflection_invariance_cert :
    let allRepWeights := d4AllRoots ++ so8VectorWeights ++ so8Weights ++ so8OddSpinorWeights
    d4PositiveRoots.length = 12 ∧
    d4AllRoots.length = 24 ∧
    d4AllRoots.all (fun r => intEq (weightDot r r) 8) = true ∧
    d4AllRoots.all (fun alpha =>
      allRepWeights.all (fun w => weightEq (weylReflect alpha (weylReflect alpha w)) w)) = true ∧
    d4AllRoots.all (fun alpha =>
      allRepWeights.all (fun u =>
        allRepWeights.all (fun v =>
          intEq (weightDot (weylReflect alpha u) (weylReflect alpha v)) (weightDot u v)))) = true ∧
    d4AllRoots.all (fun alpha =>
      isWeightBijection (weylReflect alpha) d4AllRoots d4AllRoots &&
      isWeightBijection (weylReflect alpha) so8Weights so8Weights &&
      isWeightBijection (weylReflect alpha) so8OddSpinorWeights so8OddSpinorWeights &&
      isWeightBijection (weylReflect alpha) so8VectorWeights so8VectorWeights) = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
/-- Order-3 Outer Triality Automorphism Certificate (`tau = H_tri ∘ r_3`):
1. Dynkin 3-cycle on `d4SimpleRoots = [alpha_1, alpha_2, alpha_3, alpha_4]`:
   `tau(alpha_1) = alpha_4`, `tau(alpha_4) = alpha_3`, `tau(alpha_3) = alpha_1`, `tau(alpha_2) = alpha_2`.
2. Representation 3-cycle `V_8 -> S^+_8 -> S^-_8 -> V_8` bijectively, with `tau^3 = id` across
   all 24 weights of `V_8 ∪ S^+_8 ∪ S^-_8` and all 24 roots of `d4AllRoots`.
3. Root system and Killing form invariance: `tau` maps `d4AllRoots` bijectively onto `d4AllRoots`,
   maps `d4PositiveRoots` bijectively onto `d4PositiveRoots`, and preserves `weightDot` identically
   for all pairs `(u, v) ∈ d4AllRoots × d4AllRoots`. -/
theorem spin8_outer_triality_order3_and_dynkin_cert :
    let rep24 := so8VectorWeights ++ so8Weights ++ so8OddSpinorWeights
    d4SimpleRoots.map outerTrialityTau = [simpleAlpha4, simpleAlpha2, simpleAlpha1, simpleAlpha3] ∧
    outerTrialityTau simpleAlpha1 = simpleAlpha4 ∧
    outerTrialityTau simpleAlpha4 = simpleAlpha3 ∧
    outerTrialityTau simpleAlpha3 = simpleAlpha1 ∧
    outerTrialityTau simpleAlpha2 = simpleAlpha2 ∧
    isWeightBijection outerTrialityTau so8VectorWeights so8Weights = true ∧
    isWeightBijection outerTrialityTau so8Weights so8OddSpinorWeights = true ∧
    isWeightBijection outerTrialityTau so8OddSpinorWeights so8VectorWeights = true ∧
    (rep24 ++ d4AllRoots).all (fun w =>
      weightEq (outerTrialityTau (outerTrialityTau (outerTrialityTau w))) w) = true ∧
    isWeightBijection outerTrialityTau d4AllRoots d4AllRoots = true ∧
    isWeightBijection outerTrialityTau d4PositiveRoots d4PositiveRoots = true ∧
    d4AllRoots.all (fun u =>
      d4AllRoots.all (fun v =>
        intEq (weightDot (outerTrialityTau u) (outerTrialityTau v)) (weightDot u v))) = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
/-- Full `D_4` Casimir Gram Matrix and Subalgebra Kernel Certificate on `(⋀^4 S^+_8)_0`:
1. Full 12-positive-root (`Phi^+(D_4)`) and full 24-root (`Phi(D_4)`) Casimir Gram matrices both
   have rank `6` (0-dimensional kernel, confirming zero `so(8)` singlets).
2. Under the peripheral `A_1 x A_1 x A_1` root subsystem `[alpha_1, alpha_3, alpha_4]` (dropping
   the central root `alpha_2`), the 6x6 Gram matrix has rank `4` (exact 2-dimensional invariant kernel).
3. Connected root pairs `[alpha_1, alpha_2]`, `[alpha_2, alpha_3]`, `[alpha_2, alpha_4]` have
   identical Gram ranks `(4, 4, 4)` (2-dimensional invariant kernels), while the three
   triality-conjugate closed `A_3 = so(6)` subalgebras (cycled by `outerTrialityTau`) have
   identical Gram ranks `(6, 6, 6)` both over `Phi^+(A_3)` and over `Phi(A_3)`. -/
theorem spin8_casimir_and_subalgebra_kernels_cert :
    rootSubsystemRank6 d4PositiveRoots = 6 ∧
    rootSubsystemRank6 d4AllRoots = 6 ∧
    rootSubsystemRank6 [simpleAlpha1, simpleAlpha3, simpleAlpha4] = 4 ∧
    (rootSubsystemRank6 [simpleAlpha1, simpleAlpha2],
     rootSubsystemRank6 [simpleAlpha2, simpleAlpha3],
     rootSubsystemRank6 [simpleAlpha2, simpleAlpha4]) = (4, 4, 4) ∧
    isWeightBijection outerTrialityTau a3AllDropAlpha1 a3AllDropAlpha3 = true ∧
    isWeightBijection outerTrialityTau a3AllDropAlpha3 a3AllDropAlpha4 = true ∧
    isWeightBijection outerTrialityTau a3AllDropAlpha4 a3AllDropAlpha1 = true ∧
    (rootSubsystemRank6 a3PosDropAlpha1,
     rootSubsystemRank6 a3PosDropAlpha3,
     rootSubsystemRank6 a3PosDropAlpha4) = (6, 6, 6) ∧
    (rootSubsystemRank6 a3AllDropAlpha1,
     rootSubsystemRank6 a3AllDropAlpha3,
     rootSubsystemRank6 a3AllDropAlpha4) = (6, 6, 6) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

#print axioms d4_weyl_reflection_invariance_cert
#print axioms spin8_outer_triality_order3_and_dynkin_cert
#print axioms spin8_casimir_and_subalgebra_kernels_cert
