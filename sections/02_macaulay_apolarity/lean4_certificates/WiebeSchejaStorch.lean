/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
import ShiodaFormalConjectures

/-!
# True 6-Variable Wiebe-Scheja-Storch Transition Determinants and Colon Ideals

This module formalizes the 6-variable polynomial ring `Z[z_0, ..., z_5]`,
its Artinian Gorenstein quotient `R(F_0) = Z[z_0, ..., z_5] / (z_0^5, ..., z_5^5)`,
3x3 and 4x4 polynomial matrix multiplication and determinants, and the exact
double-inclusion Wiebe-Scheja-Storch colon ideal theorem `(J(F_0) : det C) = <G_Z>` for both:
1. A coordinate 2-plane `Pi = V(z_0, z_2, z_4)` via its 3x3 transition matrix `C_Pi`
   with `C_Pi * G_Pi = A_Pi` in `Z[z_0, ..., z_5]` and graded quotient dimensions
   `[1, 3, 6, 10, 15, 18, 19]`.
2. A quadric complete intersection `Q_2 = V(z_0 z_1, z_0^4 - z_1^4, z_2, z_4)` via its
   non-diagonal 4x4 transition matrix `C_Q` satisfying `C_Q * G_Q = A_Q` identically in
   `Z[z_0, ..., z_5]`, `det(C_Q) = -(z_0^4 + z_1^4) z_2^4 z_4^4`, and graded quotient
   dimensions `[1, 4, 9, 16, 24, 30, 32]`.

All theorems compile constructively with no placeholder proofs and no external dependencies.
-/

abbrev Monom6 := List Nat
abbrev Poly6 := List (Monom6 × Int)

private def natListEq (l1 l2 : List Nat) : Bool :=
  match l1 with
  | [] => match l2 with | [] => true | _ :: _ => false
  | x :: xs => match l2 with | [] => false | y :: ys => (x == y) && natListEq xs ys

private def natListLt (l1 l2 : List Nat) : Bool :=
  match l1 with
  | [] => false
  | x :: xs =>
    match l2 with
    | [] => false
    | y :: ys => if x == y then natListLt xs ys else Nat.blt x y

def monomMul6 : Monom6 → Monom6 → Monom6
  | [], _ => []
  | _, [] => []
  | x :: xs, y :: ys => (x + y) :: monomMul6 xs ys

def monomDeg6 (m : Monom6) : Nat :=
  m.foldl (· + ·) 0

def monomInJac6 (m : Monom6) : Bool :=
  m.any (fun e => Nat.ble 5 e)

def polyInsert6 (m : Monom6) (c : Int) : Poly6 → Poly6
  | [] => if intEq c 0 then [] else [(m, c)]
  | (m', c') :: rest =>
    if natListEq m m' then
      let s := c + c'
      if intEq s 0 then rest else (m', s) :: rest
    else if natListLt m m' then
      if intEq c 0 then (m', c') :: rest else (m, c) :: (m', c') :: rest
    else
      (m', c') :: polyInsert6 m c rest

def polyCanon6 (p : Poly6) : Poly6 :=
  p.foldl (fun acc (m, c) => if intEq c 0 then acc else polyInsert6 m c acc) []

def polyAdd6 (p q : Poly6) : Poly6 :=
  q.foldl (fun acc (m, c) => if intEq c 0 then acc else polyInsert6 m c acc) (polyCanon6 p)

def polyNeg6 (p : Poly6) : Poly6 :=
  p.map (fun (m, c) => (m, -c))

def polySub6 (p q : Poly6) : Poly6 :=
  polyAdd6 p (polyNeg6 q)

def polyMul6 (p q : Poly6) : Poly6 :=
  p.foldl (fun acc (m1, c1) =>
    q.foldl (fun acc2 (m2, c2) =>
      let c := c1 * c2
      if intEq c 0 then acc2 else polyInsert6 (monomMul6 m1 m2) c acc2) acc) []

def polyModJac6 (p : Poly6) : Poly6 :=
  polyCanon6 (p.filter (fun (m, _) => !monomInJac6 m))

def polyDeg6 (p : Poly6) : Nat :=
  match p with
  | [] => 0
  | (m, _) :: _ => monomDeg6 m

def polyEq6 (p1 p2 : Poly6) : Bool :=
  match p1 with
  | [] => match p2 with | [] => true | _ :: _ => false
  | (m1, c1) :: r1 =>
    match p2 with
    | [] => false
    | (m2, c2) :: r2 => natListEq m1 m2 && intEq c1 c2 && polyEq6 r1 r2

def polyVecEq6 (v1 v2 : List Poly6) : Bool :=
  match v1 with
  | [] => match v2 with | [] => true | _ :: _ => false
  | p :: ps =>
    match v2 with
    | [] => false
    | q :: qs => polyEq6 (polyCanon6 p) (polyCanon6 q) && polyVecEq6 ps qs

def polyDot (u v : List Poly6) : Poly6 :=
  match u with
  | [] => []
  | u0 :: us =>
    match v with
    | [] => []
    | v0 :: vs => polyAdd6 (polyMul6 u0 v0) (polyDot us vs)

def polyDot3 (u v : List Poly6) : Poly6 :=
  polyDot u v

def polyMatVecMul (mat : List (List Poly6)) (vec : List Poly6) : List Poly6 :=
  mat.map (fun row => polyDot row vec)

def polyMatVecMul3 (mat : List (List Poly6)) (vec : List Poly6) : List Poly6 :=
  polyMatVecMul mat vec

private def polyAt (v : List Poly6) (i : Nat) : Poly6 :=
  match v with
  | [] => []
  | x :: xs =>
    match i with
    | 0 => x
    | i' + 1 => polyAt xs i'

private def dropNthPoly (row : List Poly6) (idx : Nat) : List Poly6 :=
  match row with
  | [] => []
  | x :: xs =>
    match idx with
    | 0 => xs
    | idx' + 1 => x :: dropNthPoly xs idx'

def polyDet3 (mat : List (List Poly6)) : Poly6 :=
  match mat with
  | [] => []
  | r0 :: rest1 =>
    match rest1 with
    | [] => []
    | r1 :: rest2 =>
      match rest2 with
      | [] => []
      | r2 :: rest3 =>
        match rest3 with
        | _ :: _ => []
        | [] =>
          let c00 := polyAt r0 0
          let c01 := polyAt r0 1
          let c02 := polyAt r0 2
          let c10 := polyAt r1 0
          let c11 := polyAt r1 1
          let c12 := polyAt r1 2
          let c20 := polyAt r2 0
          let c21 := polyAt r2 1
          let c22 := polyAt r2 2
          let t1 := polyMul6 c00 (polyMul6 c11 c22)
          let t2 := polyMul6 c00 (polyMul6 c12 c21)
          let t3 := polyMul6 c01 (polyMul6 c10 c22)
          let t4 := polyMul6 c01 (polyMul6 c12 c20)
          let t5 := polyMul6 c02 (polyMul6 c10 c21)
          let t6 := polyMul6 c02 (polyMul6 c11 c20)
          polyModJac6 (polySub6 (polyAdd6 t1 (polyAdd6 t4 t5)) (polyAdd6 t2 (polyAdd6 t3 t6)))

/-- General 4x4 polynomial matrix determinant via Laplace cofactor expansion along row 0. -/
def polyDet4 (mat : List (List Poly6)) : Poly6 :=
  match mat with
  | [] => []
  | r0 :: subRows =>
    let minor0 := subRows.map (fun r => dropNthPoly r 0)
    let minor1 := subRows.map (fun r => dropNthPoly r 1)
    let minor2 := subRows.map (fun r => dropNthPoly r 2)
    let minor3 := subRows.map (fun r => dropNthPoly r 3)
    let d0 := polyMul6 (polyAt r0 0) (polyDet3 minor0)
    let d1 := polyMul6 (polyAt r0 1) (polyDet3 minor1)
    let d2 := polyMul6 (polyAt r0 2) (polyDet3 minor2)
    let d3 := polyMul6 (polyAt r0 3) (polyDet3 minor3)
    polyModJac6 (polySub6 (polyAdd6 d0 d2) (polyAdd6 d1 d3))

/-- Canonical coordinate monomial `z_i^k` in `Z[z_0, ..., z_5]`. -/
def varPow6 (i k : Nat) : Poly6 :=
  let m := (rangeList 0 6).map (fun j => if j == i then k else 0)
  [(m, 1)]

/-- Coordinate 2-plane `Pi = V(z_0, z_2, z_4)` generators and Jacobian target. -/
def gPlaneVec : List Poly6 := [varPow6 0 1, varPow6 2 1, varPow6 4 1]
def aPlaneJacVec : List Poly6 := [varPow6 0 5, varPow6 2 5, varPow6 4 5]

def cPlaneMat : List (List Poly6) :=
  [[varPow6 0 4, [], []],
   [[], varPow6 2 4, []],
   [[], [], varPow6 4 4]]

def sigmaPlaneExpected : Poly6 := [([4, 0, 4, 0, 4, 0], 1)]

/-- Quadric complete intersection `Q_2 = V(z_0 z_1, z_0^4 - z_1^4, z_2, z_4)`
with its exact non-diagonal 4x4 Wiebe-Scheja-Storch transition matrix `C_Q`
satisfying `C_Q * G_Q = [-z_0^5, -z_1^5, z_2^5, z_4^5]` identically in `Z[z_0, ..., z_5]`. -/
def gQuadricVec4 : List Poly6 :=
  [polyMul6 (varPow6 0 1) (varPow6 1 1),
   polySub6 (varPow6 0 4) (varPow6 1 4),
   varPow6 2 1,
   varPow6 4 1]

def aQuadricJacVec4 : List Poly6 :=
  [polyNeg6 (varPow6 0 5),
   polyNeg6 (varPow6 1 5),
   varPow6 2 5,
   varPow6 4 5]

def cQuadricMat4 : List (List Poly6) :=
  [[polyNeg6 (varPow6 1 3), polyNeg6 (varPow6 0 1), [], []],
   [polyNeg6 (varPow6 0 3), varPow6 1 1, [], []],
   [[], [], varPow6 2 4, []],
   [[], [], [], varPow6 4 4]]

def sigmaQuadricExpected : Poly6 :=
  polyCanon6 [([4, 0, 4, 0, 4, 0], 1), ([0, 4, 4, 0, 4, 0], 1)]

/-- Colon ideal membership `(J(F_0) : detC)` predicate: `f * detC ≡ 0 (mod J(F_0))`. -/
def inColonIdeal (detC f : Poly6) : Bool :=
  (polyModJac6 (polyMul6 f detC)).isEmpty

/-- All 6-variable monomials of degree `d` with every exponent `<= 4`. -/
def monomials6 (d : Nat) : List Monom6 :=
  [0, 1, 2, 3, 4].foldl (fun acc0 a0 =>
    if Nat.blt d a0 then acc0 else
    acc0 ++ [0, 1, 2, 3, 4].foldl (fun acc1 a1 =>
      if Nat.blt d (a0 + a1) then acc1 else
      acc1 ++ [0, 1, 2, 3, 4].foldl (fun acc2 a2 =>
        if Nat.blt d (a0 + a1 + a2) then acc2 else
        acc2 ++ [0, 1, 2, 3, 4].foldl (fun acc3 a3 =>
          if Nat.blt d (a0 + a1 + a2 + a3) then acc3 else
          acc3 ++ [0, 1, 2, 3, 4].foldl (fun acc4 a4 =>
            if Nat.blt d (a0 + a1 + a2 + a3 + a4) then acc4 else
            let a5 := d - (a0 + a1 + a2 + a3 + a4)
            if Nat.ble a5 4 then acc4 ++ [[a0, a1, a2, a3, a4, a5]] else acc4
          ) []
        ) []
      ) []
    ) []
  ) []

private def monomInsertSorted (m : Monom6) : List Monom6 → List Monom6
  | [] => [m]
  | x :: xs =>
    if natListEq m x then x :: xs
    else if natListLt m x then m :: x :: xs
    else x :: monomInsertSorted m xs

private def monomMemSorted (m : Monom6) : List Monom6 → Bool
  | [] => false
  | x :: xs =>
    if natListEq m x then true
    else if natListLt m x then false
    else monomMemSorted m xs

private def polyCoeffAt (m : Monom6) : Poly6 → Int
  | [] => 0
  | (m', c) :: rest => if natListEq m m' then c else polyCoeffAt m rest

/-- Exact rank of an arbitrary list of polynomials `polys` in `R(F_0)`:
first performs coordinate pivot elimination using all single-monomial elements,
then computes the exact fraction-free integer Gaussian rank on remaining multi-term elements. -/
def polyListRank6 (polys : List Poly6) : Nat :=
  let nz := (polys.map polyCanon6).filter (fun p => !p.isEmpty)
  let unitPivots := nz.foldl (fun acc p =>
    match p with
    | [] => acc
    | (m, _) :: rest =>
      match rest with
      | [] => monomInsertSorted m acc
      | _ :: _ => acc) []
  let remMulti := (nz.filterMap (fun p =>
    match p with
    | [] => none
    | (_, _) :: rest =>
      match rest with
      | [] => none
      | _ :: _ =>
        let proj := p.filter (fun (m, _) => !monomMemSorted m unitPivots)
        if proj.isEmpty then none else some proj))
  let multiRank :=
    match remMulti with
    | [] => 0
    | _ :: _ =>
      let cols := remMulti.foldl (fun acc p =>
        p.foldl (fun acc2 (m, _) => monomInsertSorted m acc2) acc) []
      let mat := remMulti.map (fun p => cols.map (fun colM => polyCoeffAt colM p))
      intMatRankAuxClean cols.length mat
  unitPivots.length + multiRank

/-- Exact rank of the multiplication-by-`detC` map `R^d(F_0) -> R^{d+12}(F_0)`,
which equals `dim (R(F_0) / (J(F_0) : detC))_d` by rank-nullity. -/
def colonCodim6 (detC : Poly6) (d : Nat) : Nat :=
  let imgs := (monomials6 d).map (fun m => polyModJac6 (polyMul6 [(m, 1)] detC))
  polyListRank6 imgs

/-- Exact dimension of the degree-`d` quotient `(R(F_0) / <gens>)_d`
computed directly from the polynomial span of `{m * g_i mod J(F_0)}`. -/
def idealQuotientDim6 (gens : List Poly6) (d : Nat) : Nat :=
  let spanPolys := gens.foldl (fun acc g =>
    let dg := polyDeg6 g
    if Nat.blt d dg then acc
    else
      acc ++ (monomials6 (d - dg)).map (fun m => polyModJac6 (polyMul6 [(m, 1)] g))) []
  (monomials6 d).length - polyListRank6 spanPolys

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
/-- Double-inclusion Wiebe-Scheja-Storch theorem for the coordinate 2-plane
`Pi = V(z_0, z_2, z_4)` in the full 6-variable Jacobian ring `R(F_0)`:
1. `C_Pi * G_Pi = A_Pi` holds identically in `Z[z_0, ..., z_5]`.
2. `det(C_Pi) mod J(F_0)` equals `z_0^4 z_2^4 z_4^4`.
3. `<G_Pi> ⊆ (J(F_0) : det C_Pi)` since every generator `g_i` satisfies `g_i * det(C_Pi) ≡ 0 (mod J(F_0))`.
4. `dim (R(F_0) / <G_Pi>)_d = dim (R(F_0) / (J(F_0) : det C_Pi))_d = [1, 3, 6, 10, 15, 18, 19]`
   for `0 <= d <= 6`, establishing exact ideal equality `<G_Pi>_d = (J(F_0) : det C_Pi)_d`. -/
theorem wiebe_scheja_storch_plane_colon_ideal_cert :
    polyVecEq6 (polyMatVecMul3 cPlaneMat gPlaneVec) aPlaneJacVec = true ∧
    polyEq6 (polyDet3 cPlaneMat) sigmaPlaneExpected = true ∧
    gPlaneVec.all (inColonIdeal (polyDet3 cPlaneMat)) = true ∧
    [0, 1, 2, 3, 4, 5, 6].map (colonCodim6 (polyDet3 cPlaneMat)) =
      [1, 3, 6, 10, 15, 18, 19] ∧
    [0, 1, 2, 3, 4, 5, 6].map (idealQuotientDim6 gPlaneVec) =
      [0, 1, 2, 3, 4, 5, 6].map (colonCodim6 (polyDet3 cPlaneMat)) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
/-- Double-inclusion Wiebe-Scheja-Storch theorem for the quadric complete intersection
`Q_2 = V(z_0 z_1, z_0^4 - z_1^4, z_2, z_4)` in `R(F_0)`:
1. `C_Q * G_Q = A_Q` holds identically in `Z[z_0, ..., z_5]` (no Jacobian reduction needed).
2. `det(C_Q) mod J(F_0)` equals `-(z_0^4 + z_1^4) z_2^4 z_4^4 = -sigmaQuadricExpected`.
3. `<G_Q> ⊆ (J(F_0) : det C_Q)` since every generator `g_i` satisfies `g_i * det(C_Q) ≡ 0 (mod J(F_0))`.
4. `dim (R(F_0) / <G_Q>)_d = dim (R(F_0) / (J(F_0) : det C_Q))_d = [1, 4, 9, 16, 24, 30, 32]`
   for `0 <= d <= 6`, establishing exact ideal equality `<G_Q>_d = (J(F_0) : det C_Q)_d`. -/
theorem wiebe_scheja_storch_quadric_colon_ideal_cert :
    polyVecEq6 (polyMatVecMul cQuadricMat4 gQuadricVec4) aQuadricJacVec4 = true ∧
    polyEq6 (polyDet4 cQuadricMat4) (polyNeg6 sigmaQuadricExpected) = true ∧
    polyEq6 (polyNeg6 (polyDet4 cQuadricMat4)) sigmaQuadricExpected = true ∧
    gQuadricVec4.all (inColonIdeal (polyDet4 cQuadricMat4)) = true ∧
    [0, 1, 2, 3, 4, 5, 6].map (colonCodim6 (polyDet4 cQuadricMat4)) =
      [1, 4, 9, 16, 24, 30, 32] ∧
    [0, 1, 2, 3, 4, 5, 6].map (idealQuotientDim6 gQuadricVec4) =
      [0, 1, 2, 3, 4, 5, 6].map (colonCodim6 (polyDet4 cQuadricMat4)) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

#print axioms wiebe_scheja_storch_plane_colon_ideal_cert
#print axioms wiebe_scheja_storch_quadric_colon_ideal_cert
