/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
import Spin8LieAlgebraTriality

/-!
# Explicit 2-Dimensional Weil/Mumford Kernel Bases on (⋀^4 S^+_8)_0

Phase 3 (Wall 3) constructive kernel extension:
1. Exhibits explicit integer 6-vectors spanning the 2-dimensional nullspaces of the rank-4
   root-subsystem Gram matrices on `(⋀^4 S^+_8)_0`:
   - `A_1^3 = [alpha_1, alpha_3, alpha_4]`: spanned by `[1, 0, 0, 0, 0, 0]` and
     `[0, 0, 0, 0, 0, 1]`, containing `weil_w2 = [1, 0, 0, 0, 0, -1]` orthogonal to `theta2`.
   - `A_2` connected pairs `[alpha_1, alpha_2]`, `[alpha_2, alpha_3]`, and `[alpha_2, alpha_4]`.
2. Certifies linear independence (non-zero 2x2 Gram determinants), exact annihilation
   `G_sub * v = 0`, and non-vanishing under full `Phi(D_4)` with zero axioms.
-/

private def intVecDot (u v : List Int) : Int :=
  match u with
  | [] => 0
  | x :: xs =>
    match v with
    | [] => 0
    | y :: ys => x * y + intVecDot xs ys

private def intMatMulVec (m : List (List Int)) (v : List Int) : List Int :=
  m.map (fun row => intVecDot row v)

private def isZeroIntVec (v : List Int) : Bool :=
  v.all (fun x => intEq x 0)

private def gramDet2 (u v : List Int) : Int :=
  let uu := intVecDot u u
  let vv := intVecDot v v
  let uv := intVecDot u v
  uu * vv - uv * uv

private def sAlpha1 : Weight := addW4 (basisVec4 0 2) (basisVec4 1 (-2))
private def sAlpha2 : Weight := addW4 (basisVec4 1 2) (basisVec4 2 (-2))
private def sAlpha3 : Weight := addW4 (basisVec4 2 2) (basisVec4 3 (-2))
private def sAlpha4 : Weight := addW4 (basisVec4 2 2) (basisVec4 3 2)

/-- Nullspace basis of the peripheral `A_1^3` subsystem `[alpha_1, alpha_3, alpha_4]`. -/
def a1CubedKerV1 : List Int := [1, 0, 0, 0, 0, 0]
def a1CubedKerV2 : List Int := [0, 0, 0, 0, 0, 1]

/-- Connected `A_2` pair `[alpha_1, alpha_2]` kernel basis (and `theta2`-orthogonal combination). -/
def a2Pair12KerV1 : List Int := [1, -1, -1, 0, 0, 0]
def a2Pair12KerV2 : List Int := [0, 0, 0, 1, 1, -1]
def a2Pair12WeilOrth : List Int := [1, -1, -1, 1, 1, -1]

/-- Connected `A_2` pair `[alpha_2, alpha_3]` kernel basis. -/
def a2Pair23KerV1 : List Int := [1, -1, 1, 0, 0, 0]
def a2Pair23KerV2 : List Int := [0, 0, 0, 1, -1, 1]

/-- Connected `A_2` pair `[alpha_2, alpha_4]` kernel basis. -/
def a2Pair24KerV1 : List Int := [1, -1, 0, 1, 0, 0]
def a2Pair24KerV2 : List Int := [0, 0, 1, 0, -1, 1]

private def checkMumfordWeil2DKernelBases : Bool :=
  let gA13 := rootSubsystemGram6 [sAlpha1, sAlpha3, sAlpha4]
  let gA12 := rootSubsystemGram6 [sAlpha1, sAlpha2]
  let gA23 := rootSubsystemGram6 [sAlpha2, sAlpha3]
  let gA24 := rootSubsystemGram6 [sAlpha2, sAlpha4]
  let gD4 := rootSubsystemGram6 d4AllRoots
  isZeroIntVec (intMatMulVec gA13 a1CubedKerV1) &&
  isZeroIntVec (intMatMulVec gA13 a1CubedKerV2) &&
  isZeroIntVec (intMatMulVec gA13 weil_w2) &&
  intEq (intVecDot weil_w2 theta2) 0 &&
  intEq (gramDet2 a1CubedKerV1 a1CubedKerV2) 1 &&
  !(isZeroIntVec (intMatMulVec gD4 weil_w2)) &&
  isZeroIntVec (intMatMulVec gA12 a2Pair12KerV1) &&
  isZeroIntVec (intMatMulVec gA12 a2Pair12KerV2) &&
  isZeroIntVec (intMatMulVec gA12 a2Pair12WeilOrth) &&
  intEq (intVecDot a2Pair12WeilOrth theta2) 0 &&
  intEq (gramDet2 a2Pair12KerV1 a2Pair12KerV2) 9 &&
  isZeroIntVec (intMatMulVec gA23 a2Pair23KerV1) &&
  isZeroIntVec (intMatMulVec gA23 a2Pair23KerV2) &&
  intEq (gramDet2 a2Pair23KerV1 a2Pair23KerV2) 9 &&
  isZeroIntVec (intMatMulVec gA24 a2Pair24KerV1) &&
  isZeroIntVec (intMatMulVec gA24 a2Pair24KerV2) &&
  intEq (gramDet2 a2Pair24KerV1 a2Pair24KerV2) 9

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
/-- Constructive 2-Dimensional `A_1^3` and `A_2` Weil Kernel Certificate (zero axioms). -/
theorem mumford_weil_2d_kernel_bases_cert :
    checkMumfordWeil2DKernelBases = true :=
  rfl

private def intMatMul (a b : List (List Int)) : List (List Int) :=
  a.map (fun row =>
    (rangeList 0 6).map (fun j =>
      let col := b.map (fun r => r.drop j |>.headD 0)
      intVecDot row col))

private def intMatScale (k : Int) (m : List (List Int)) : List (List Int) :=
  m.map (fun row => row.map (fun x => k * x))

private def intMatAdd (a b : List (List Int)) : List (List Int) :=
  List.zipWith (fun r1 r2 => List.zipWith (· + ·) r1 r2) a b

private def intMatEq (a b : List (List Int)) : Bool :=
  (List.zipWith (fun r1 r2 =>
    List.zipWith intEq r1 r2 |>.all id) a b).all id

private def intMatZero (m : List (List Int)) : Bool :=
  m.all isZeroIntVec

private def outerProd6 (u : List Int) : List (List Int) :=
  u.map (fun a => u.map (fun b => a * b))

private def intMatTrace (m : List (List Int)) : Int :=
  (rangeList 0 m.length).foldl (fun acc i =>
    acc + ((m.drop i |>.headD []).drop i |>.headD 0)) 0

/-- Rank-2 integer orthogonal projector onto `ker(G_{A_2})` for `[alpha_1, alpha_2]`:
`P_{A_2} = 2 u_1 u_1^T + 2 u_2 u_2^T` (`P^2 = 6 P`, `G_{A_2} P = 0`, `trace = 12`).
Note `dim(ker G_{A_2} ∩ theta_2^⊥) = 1`, spanned by `w = u_1 + u_2 = [1,-1,-1,1,1,-1]`,
yielding the rank-1 primitive Weil projector `P_prim = w w^T` (`P_prim^2 = 6 P_prim`,
`G_{A_2} P_prim = 0`, `P_prim theta_2 = 0`, `trace = 6`). -/
def pWeilA2Rank2 : List (List Int) :=
  intMatAdd
    (intMatScale 2 (outerProd6 a2Pair12KerV1))
    (intMatScale 2 (outerProd6 a2Pair12KerV2))

def pWeilA2PrimRank1 : List (List Int) :=
  outerProd6 a2Pair12WeilOrth

/-- Rank-2 primitive `theta_2`-orthogonal projector on `[alpha_1, alpha_4]` (`dim = 2`):
`v_1 = [-1, 0, 0, 0, 0, 1]` (`||v_1||^2 = 2`), `v_2 = [0, -1, -1, 1, 1, 0]` (`||v_2||^2 = 4`),
`P_{14} = 2 v_1 v_1^T + v_2 v_2^T` (`P_{14}^2 = 4 P_{14}`, `G_{14} P_{14} = 0`,
`P_{14} theta_2 = 0`, `trace = 8`). -/
def a14OrthV1 : List Int := [-1, 0, 0, 0, 0, 1]
def a14OrthV2 : List Int := [0, -1, -1, 1, 1, 0]

def pWeilA14PrimRank2 : List (List Int) :=
  intMatAdd (intMatScale 2 (outerProd6 a14OrthV1)) (outerProd6 a14OrthV2)

private def checkProjectorCert : Bool :=
  let gA12 := rootSubsystemGram6 [sAlpha1, sAlpha2]
  let gA14 := rootSubsystemGram6 [sAlpha1, sAlpha4]
  let rk2Ok :=
    intMatEq (intMatMul pWeilA2Rank2 pWeilA2Rank2) (intMatScale 6 pWeilA2Rank2) &&
    intMatZero (intMatMul gA12 pWeilA2Rank2) &&
    intEq (intMatTrace pWeilA2Rank2) 12 &&
    intEq (intMatRankAuxClean 6 pWeilA2Rank2) 2
  let prim1Ok :=
    intMatEq (intMatMul pWeilA2PrimRank1 pWeilA2PrimRank1) (intMatScale 6 pWeilA2PrimRank1) &&
    intMatZero (intMatMul gA12 pWeilA2PrimRank1) &&
    isZeroIntVec (intMatMulVec pWeilA2PrimRank1 theta2) &&
    intEq (intMatTrace pWeilA2PrimRank1) 6 &&
    intEq (intMatRankAuxClean 6 pWeilA2PrimRank1) 1
  let a14Ok :=
    intMatEq (intMatMul pWeilA14PrimRank2 pWeilA14PrimRank2) (intMatScale 4 pWeilA14PrimRank2) &&
    intMatZero (intMatMul gA14 pWeilA14PrimRank2) &&
    isZeroIntVec (intMatMulVec pWeilA14PrimRank2 theta2) &&
    intEq (intMatTrace pWeilA14PrimRank2) 8 &&
    intEq (intMatRankAuxClean 6 pWeilA14PrimRank2) 2
  rk2Ok && prim1Ok && a14Ok

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
/-- Certified idempotent Weil correspondence projectors on `(⋀^4 S^+_8)_0` (`0` axioms):
1. Rank-2 `A_2` kernel projector `P_{A_2}^2 = 6 P_{A_2}`, `G_{A_2} P_{A_2} = 0`, `tr = 12`,
   `rank = 2`.
2. Rank-1 primitive `A_2` Weil projector `P_prim^2 = 6 P_prim`, `G_{A_2} P_prim = 0`,
   `P_prim theta_2 = 0`, `tr = 6`, `rank = 1`.
3. Rank-2 primitive `[alpha_1, alpha_4]` projector `P_{14}^2 = 4 P_{14}`, `G_{14} P_{14} = 0`,
   `P_{14} theta_2 = 0`, `tr = 8`, `rank = 2`. -/
theorem mumford_weil_idempotent_projector_and_cm_correspondence_cert :
    checkProjectorCert = true :=
  rfl

#print axioms mumford_weil_2d_kernel_bases_cert
#print axioms mumford_weil_idempotent_projector_and_cm_correspondence_cert
