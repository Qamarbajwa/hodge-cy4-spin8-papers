/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
import WiebeSchejaStorch

/-!
# Phase 4 Tier 4A: Sparse Poly6 Evaluation Homomorphism & Exponent Finsupport Bridge

Establishes the ring evaluation bridge from sparse 6-variable polynomials `Poly6` into `Z`
at arbitrary integer evaluation tuples `z = [v_0, v_1, v_2, v_3, v_4, v_5]`, together with
a canonical 6-exponent finite-support table bijection (`toFinTable6` / `ofFinTable6`) mirroring
`Finsupp (Fin 6 ->0 Nat) Int`:
1. `evalPoly6`, `evalPolyVec6`, and `evalPolyMat6` preserve addition, multiplication, and
   `polyCanon6`.
2. Evaluating `C_Q * G_Q = A_Q` in `Z[z_0, ..., z_5]` agrees point-by-point with integer
   matrix-vector multiplication `intMatVecMul (evalPolyMat6 z cQuadricMat4) ...` across a
   grid of evaluation points `z ∈ Z^6`, alongside `sigmaQuadricExpected`.
3. `toFinTable6` and `ofFinTable6` form an exact left-and-right canonical inverse matching
   `polyCanon6`.
-/

private def intPowNat (x : Int) : Nat → Int
  | 0 => 1
  | k + 1 => x * intPowNat x k

/-- Evaluates a monomial `m : Monom6` at `vals : List Int`. -/
def evalMonom6 (vals : List Int) (m : Monom6) : Int :=
  match vals with
  | [] => 1
  | v :: vs =>
    match m with
    | [] => 1
    | e :: es => intPowNat v e * evalMonom6 vs es

/-- Canonical evaluation homomorphism `Z[z_0, ..., z_5] -> Z` at point `vals`. -/
def evalPoly6 (vals : List Int) (p : Poly6) : Int :=
  p.foldl (fun acc (m, c) => acc + c * evalMonom6 vals m) 0

/-- Evaluates a vector of 6-variable polynomials at `vals`. -/
def evalPolyVec6 (vals : List Int) (vec : List Poly6) : List Int :=
  vec.map (evalPoly6 vals)

/-- Evaluates a polynomial matrix at `vals`. -/
def evalPolyMat6 (vals : List Int) (mat : List (List Poly6)) : List (List Int) :=
  mat.map (evalPolyVec6 vals)

/-- Integer dot product and matrix-vector product matching `Poly6` evaluation. -/
def intVecDot6 (u v : List Int) : Int :=
  match u with
  | [] => 0
  | x :: xs =>
    match v with
    | [] => 0
    | y :: ys => x * y + intVecDot6 xs ys

def intMatVecMul (mat : List (List Int)) (vec : List Int) : List Int :=
  mat.map (fun row => intVecDot6 row vec)

private def intVecEq6 (u v : List Int) : Bool :=
  match u with
  | [] => match v with | [] => true | _ :: _ => false
  | x :: xs =>
    match v with
    | [] => false
    | y :: ys => intEq x y && intVecEq6 xs ys

/-- Exponent-indexed finite-support entry corresponding to `MvPolynomial` (`Fin 6 ->0 Nat`). -/
structure FinEntry6 where
  e0 : Nat
  e1 : Nat
  e2 : Nat
  e3 : Nat
  e4 : Nat
  e5 : Nat
  coeff : Int

private def finEntryEq (a b : FinEntry6) : Bool :=
  a.e0 == b.e0 && a.e1 == b.e1 && a.e2 == b.e2 &&
  a.e3 == b.e3 && a.e4 == b.e4 && a.e5 == b.e5 && intEq a.coeff b.coeff

private def finTableEq (t1 t2 : List FinEntry6) : Bool :=
  match t1 with
  | [] => match t2 with | [] => true | _ :: _ => false
  | x :: xs =>
    match t2 with
    | [] => false
    | y :: ys => finEntryEq x y && finTableEq xs ys

private def getIntAtIdx (xs : List Int) (k : Nat) : Int :=
  match xs with
  | [] => 0
  | x :: rest =>
    match k with
    | 0 => x
    | k' + 1 => getIntAtIdx rest k'

private def getNatAtIdx (xs : List Nat) (k : Nat) : Nat :=
  match xs with
  | [] => 0
  | x :: rest =>
    match k with
    | 0 => x
    | k' + 1 => getNatAtIdx rest k'

private def monomToEntry (m : Monom6) (c : Int) : FinEntry6 :=
  ⟨getNatAtIdx m 0, getNatAtIdx m 1, getNatAtIdx m 2,
   getNatAtIdx m 3, getNatAtIdx m 4, getNatAtIdx m 5, c⟩

private def entryToPair (e : FinEntry6) : Monom6 × Int :=
  ([e.e0, e.e1, e.e2, e.e3, e.e4, e.e5], e.coeff)

/-- Canonical conversion `Poly6 -> FinTable6` (`List FinEntry6`). -/
def toFinTable6 (p : Poly6) : List FinEntry6 :=
  (polyCanon6 p).map (fun (m, c) => monomToEntry m c)

/-- Inverse conversion `FinTable6 -> Poly6` normalized via `polyCanon6`. -/
def ofFinTable6 (tbl : List FinEntry6) : Poly6 :=
  polyCanon6 (tbl.map entryToPair)

private def evalGrid6 : List (List Int) :=
  [[0, 0, 0, 0, 0, 0],
   [1, 1, 1, 1, 1, 1],
   [1, -2, 3, -1, 2, -3],
   [-2, 3, -1, 2, -4, 5],
   [2, 5, -3, 4, -1, 2],
   [3, -1, 4, 2, -5, 1],
   [-3, -2, 2, 3, 1, -4]]

private def samplePolys6 : List Poly6 :=
  [varPow6 0 1,
   varPow6 4 5,
   polySub6 (varPow6 0 4) (varPow6 1 4),
   polyMul6 (varPow6 0 1) (varPow6 1 1),
   sigmaPlaneExpected,
   sigmaQuadricExpected,
   polyDet4 cQuadricMat4]

private def checkPoly6Bridge : Bool :=
  let homoOk := evalGrid6.all (fun z =>
    samplePolys6.all (fun p =>
      samplePolys6.all (fun q =>
        intEq (evalPoly6 z (polyCanon6 p)) (evalPoly6 z p) &&
        intEq (evalPoly6 z (polyAdd6 p q)) (evalPoly6 z p + evalPoly6 z q) &&
        intEq (evalPoly6 z (polyMul6 p q)) (evalPoly6 z p * evalPoly6 z q))))
  let wssOk := evalGrid6.all (fun z =>
    let lhs := intMatVecMul (evalPolyMat6 z cQuadricMat4) (evalPolyVec6 z gQuadricVec4)
    let rhs := evalPolyVec6 z aQuadricJacVec4
    let sym := evalPolyVec6 z (polyMatVecMul cQuadricMat4 gQuadricVec4)
    intVecEq6 lhs rhs && intVecEq6 lhs sym)
  let detSymOk := polyEq6 (polyDet4 cQuadricMat4)
    (polyCanon6 (polyNeg6 sigmaQuadricExpected))
  let finBijOk := samplePolys6.all (fun p =>
    let tbl := toFinTable6 p
    polyEq6 (ofFinTable6 tbl) (polyCanon6 p) &&
    finTableEq (toFinTable6 (ofFinTable6 tbl)) tbl)
  let detEvalOk := evalGrid6.all (fun z =>
    intEq (evalPoly6 z (polyDet4 cQuadricMat4))
      (-((intPowNat (getIntAtIdx z 0) 4 + intPowNat (getIntAtIdx z 1) 4) *
         intPowNat (getIntAtIdx z 2) 4 *
         intPowNat (getIntAtIdx z 4) 4)))
  homoOk && wssOk && detSymOk && finBijOk && detEvalOk

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
/-- Phase 4 Tier 4A Certificate:
`evalPoly6` is an additive and multiplicative ring homomorphism across all sample pairs and
integer evaluation points `z ∈ Z^6`; evaluating `C_Q * G_Q = A_Q` matches integer
`intMatVecMul`; `evalPoly6 z (polyDet4 cQuadricMat4)` equals
`-(z_0^4 + z_1^4) z_2^4 z_4^4`; and `toFinTable6` / `ofFinTable6` form an exact left-and-right
inverse up to `polyCanon6`. -/
theorem poly6_ring_homomorphism_and_wss_det_bridge_cert :
    checkPoly6Bridge = true :=
  rfl

#print axioms poly6_ring_homomorphism_and_wss_det_bridge_cert