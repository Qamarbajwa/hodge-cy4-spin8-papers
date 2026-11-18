/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
import GaussManinJetTransport

/-!
# Phase 2 (Wall 1): Multi-Order Gauss-Manin Jets (mod t^8) & Unmixed CI Profiles

Extends `GaussManinJetTransport.lean` up to 7th-order jets (`mod t^8`) across Bands 1, 2, and 3
and certifies the graded quotient dimension profiles of unmixed codimension-3 projective
complete intersections in `R(F_0)` matching `multi_order_gd_crt.py` and `nl_moduli_walk.py`.
Combines:
1. Packed base-5 column keys and a bounded-depth binary radix `PivTrie` over `F_65521` and
   `F_65519` up to degree `6` (`sparseJetRankModP`, `sparseIdealQuotientDimModP`).
2. Exact fraction-free integer (`Z`) rank certification (`jetMacaulayRank6`) for `0 <= d <= 3`
   together with exact integral annihilator preservation (`allAnnihilate`).
-/

private abbrev PackedRowN := List (Nat × Nat)

private inductive PivTrie where
  | empty : PivTrie
  | val : PackedRowN → PivTrie
  | branch : PivTrie → PivTrie → PivTrie

private def pivTrieFind (depth : Nat) (col : Nat) : PivTrie → Option PackedRowN
  | .empty => none
  | .val r => some r
  | .branch z o =>
    match depth with
    | 0 => none
    | d' + 1 =>
      if col % 2 == 0 then pivTrieFind d' (col / 2) z
      else pivTrieFind d' (col / 2) o

private def pivTrieInsert (depth : Nat) (col : Nat) (row : PackedRowN) (t : PivTrie) :
    PivTrie :=
  match depth with
  | 0 => .val row
  | d' + 1 =>
    match t with
    | .empty =>
      if col % 2 == 0 then .branch (pivTrieInsert d' (col / 2) row .empty) .empty
      else .branch .empty (pivTrieInsert d' (col / 2) row .empty)
    | .val _ => .val row
    | .branch z o =>
      if col % 2 == 0 then .branch (pivTrieInsert d' (col / 2) row z) o
      else .branch z (pivTrieInsert d' (col / 2) row o)

private def pack6Aux (acc : Nat) : Monom6 → Nat
  | [] => acc
  | e :: rest => pack6Aux (acc * 5 + e) rest

private def pack6 (m : Monom6) : Nat :=
  pack6Aux 0 m

private def addModJac6 (m1 m2 : Monom6) : Option Monom6 :=
  match m1 with
  | [] => match m2 with | [] => some [] | _ :: _ => none
  | a :: as =>
    match m2 with
    | [] => none
    | b :: bs =>
      let s := a + b
      if Nat.ble 5 s then none
      else
        match addModJac6 as bs with
        | none => none
        | some rest => some (s :: rest)

private def intModP (p : Nat) (c : Int) : Nat :=
  let m := c.natAbs % p
  if m == 0 then 0 else if c < 0 then p - m else m

private def polyToModP (p : Nat) (lam : Poly6) : List (Monom6 × Nat) :=
  lam.filterMap (fun (m, c) =>
    let v := intModP p c
    if v == 0 then none else some (m, v))

private def mulMonomModP (offset : Nat) (m : Monom6) : List (Monom6 × Nat) → PackedRowN
  | [] => []
  | (a, c) :: rest =>
    match addModJac6 m a with
    | none => mulMonomModP offset m rest
    | some prod => (offset + pack6 prod, c) :: mulMonomModP offset m rest

private def linCombModP (p a : Nat) (r1 : PackedRowN) (b : Nat) (r2 : PackedRowN)
    (fuel : Nat) : PackedRowN :=
  match fuel with
  | 0 => []
  | fuel' + 1 =>
    match r1 with
    | [] =>
      r2.foldr (fun (col, c) acc =>
        let v := (b * (p - c)) % p
        if v == 0 then acc else (col, v) :: acc) []
    | (c1, v1) :: p' =>
      match r2 with
      | [] =>
        r1.foldr (fun (col, c) acc =>
          let v := (a * c) % p
          if v == 0 then acc else (col, v) :: acc) []
      | (c2, v2) :: q' =>
        if c1 == c2 then
          let t1 := (a * v1) % p
          let t2 := (b * v2) % p
          let v := if Nat.ble t2 t1 then t1 - t2 else t1 + p - t2
          let tail := linCombModP p a p' b q' fuel'
          if v == 0 then tail else (c1, v) :: tail
        else if Nat.blt c1 c2 then
          let v := (a * v1) % p
          let tail := linCombModP p a p' b r2 fuel'
          if v == 0 then tail else (c1, v) :: tail
        else
          let v := (b * (p - v2)) % p
          let tail := linCombModP p a r1 b q' fuel'
          if v == 0 then tail else (c2, v) :: tail

private def reduceRowModP (depth p : Nat) (row : PackedRowN) (pivs : PivTrie) (fuel : Nat) :
    Option (Nat × PackedRowN) :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
    match row with
    | [] => none
    | (col, rc) :: _ =>
      match pivTrieFind depth col pivs with
      | none => some (col, row)
      | some prow =>
        match prow with
        | [] => some (col, row)
        | (_, pc) :: _ =>
          let comb := linCombModP p pc row rc prow (row.length + prow.length + 1)
          reduceRowModP depth p comb pivs fuel'

private def rankModP (depth p : Nat) (rows : List PackedRowN) : Nat :=
  (rows.foldl (fun (st : PivTrie × Nat) row =>
    match row with
    | [] => st
    | _ :: _ =>
      match reduceRowModP depth p row st.1 (st.2 + 1) with
      | none => st
      | some (col, pivRow) => (pivTrieInsert depth col pivRow st.1, st.2 + 1)) (.empty, 0)).2

private def tagJetModP (k : Nat) (m : Monom6) : List (List (Monom6 × Nat)) → PackedRowN
  | [] => []
  | lam :: rest => mulMonomModP (k * 15625) m lam ++ tagJetModP (k + 1) m rest

/-- Sparse `F_p` Macaulay contraction rank across a multi-order jet tuple `jet` (depth 17 trie). -/
def sparseJetRankModP (p : Nat) (jet : List Poly6) (d : Nat) : Nat :=
  let nz := (jet.filter (fun q => !q.isEmpty)).map (polyToModP p)
  rankModP 17 p ((monomials6 d).map (fun m => tagJetModP 0 m nz))

/-- Sparse `F_p` degree-`d` quotient dimension `(R(F_0) / <gens>)_d` (depth 14 trie). -/
def sparseIdealQuotientDimModP (p : Nat) (gens : List Poly6) (d : Nat) : Nat :=
  let rows := gens.foldl (fun acc g =>
    let dg := polyDeg6 g
    if Nat.blt d dg then acc
    else
      let cg := polyToModP p (polyCanon6 g)
      acc ++ (monomials6 (d - dg)).map (fun m => mulMonomModP 0 m cg)) []
  (monomials6 d).length - rankModP 14 p rows

/-- Recursive arbitrary-order Gauss-Manin jet builder `[lam^(0), ..., lam^(steps)]`. -/
def buildGaussManinJetN (steps : Nat) (wDir lam0 : Poly6) : List Poly6 :=
  match steps with
  | 0 => [lam0]
  | k + 1 =>
    let tail := buildGaussManinJetN k wDir (gaussManinJetStep wDir lam0)
    lam0 :: tail

/-- Complete-intersection regular sequence `<z_0 z_1, z_2 z_3, z_4>` in `R(F_0)` (`G = 3`). -/
def band3TypeCIGens : List Poly6 :=
  [polyMul6 (varPow6 0 1) (varPow6 1 1),
   polyMul6 (varPow6 2 1) (varPow6 3 1),
   varPow6 4 1]

/-- Complete-intersection regular sequence `<z_0^2 - z_1^2, z_2^2 - z_3^2, z_4^2 - z_5^2>`
in `R(F_0)`. -/
def band2TypeQuadricCIGens : List Poly6 :=
  [polySub6 (varPow6 0 2) (varPow6 1 2),
   polySub6 (varPow6 2 2) (varPow6 3 2),
   polySub6 (varPow6 4 2) (varPow6 5 2)]

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
/-- Multi-order `mod t^8` Gauss-Manin jet transport certificate across Bands 1, 2, and 3:
1. Band 1 smoothing from `sigmaPlaneExpected` stabilizes at `[1, 3, 4, 5, 5, 5, 5, 5]` terms
   with joint `F_65521` rank `[1, 4, 10, 20, 35, 48, 57]` and `[z_2, z_4]` annihilation.
2. Band 2 under pole-lowering `gaussManinJetStep` nilpotently terminates at `t^4`
   (`[1, 3, 3, 1, 0, 0, 0, 0]`) with joint rank `[1, 6, 21, 53, 108, 181, 254]`.
3. Band 3 under pole-lowering `gaussManinJetStep` nilpotently terminates at `t^4`
   (`[1, 3, 3, 1, 0, 0, 0, 0]`) with joint rank `[1, 5, 15, 35, 68, 113, 153]`,
   preserving the linear hyperplane `z_0` (`allAnnihilate`). -/
theorem multi_order_t8_gauss_manin_jet_cert :
    (buildGaussManinJetN 7 wDirBand1 sigmaPlaneExpected).map List.length =
      [1, 3, 4, 5, 5, 5, 5, 5] ∧
    (buildGaussManinJetN 7 wDirBand2 lamBand2).map List.length =
      [1, 3, 3, 1, 0, 0, 0, 0] ∧
    (buildGaussManinJetN 7 wDirBand3 lamBand3).map List.length =
      [1, 3, 3, 1, 0, 0, 0, 0] ∧
    (buildGaussManinJetN 7 wDirBand1 sigmaPlaneExpected).all
        (allAnnihilate [varPow6 2 1, varPow6 4 1]) = true ∧
    (buildGaussManinJetN 7 wDirBand3 lamBand3).all
        (allAnnihilate [varPow6 0 1]) = true ∧
    [0, 1, 2, 3, 4, 5, 6].map
        (sparseJetRankModP 65521 (buildGaussManinJetN 7 wDirBand1 sigmaPlaneExpected)) =
      [1, 4, 10, 20, 35, 48, 57] ∧
    [0, 1, 2, 3, 4, 5, 6].map
        (sparseJetRankModP 65521 (buildGaussManinJetN 7 wDirBand2 lamBand2)) =
      [1, 6, 21, 53, 108, 181, 254] ∧
    [0, 1, 2, 3, 4, 5, 6].map
        (sparseJetRankModP 65521 (buildGaussManinJetN 7 wDirBand3 lamBand3)) =
      [1, 5, 15, 35, 68, 113, 153] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
/-- Exact fraction-free integer (`Z`) rank witness for `mod t^8` jets across `0 <= d <= 3`
(`jetMacaulayRank6`) paired with exact `Z`-quotient dimension checks for `gPlaneVec`,
`band3TypeCIGens`, and `band2TypeQuadricCIGens` on `0 <= d <= 3`. -/
theorem multi_order_t8_exact_z_rank_witness_cert :
    [0, 1, 2, 3].map
        (jetMacaulayRank6 (buildGaussManinJetN 7 wDirBand1 sigmaPlaneExpected)) =
      [1, 4, 10, 20] ∧
    [0, 1, 2, 3].map
        (jetMacaulayRank6 (buildGaussManinJetN 7 wDirBand2 lamBand2)) =
      [1, 6, 21, 53] ∧
    [0, 1, 2, 3].map
        (jetMacaulayRank6 (buildGaussManinJetN 7 wDirBand3 lamBand3)) =
      [1, 5, 15, 35] ∧
    [0, 1, 2, 3].map (idealQuotientDim6 band3TypeCIGens) = [1, 5, 13, 25] ∧
    [0, 1, 2, 3].map (idealQuotientDim6 band2TypeQuadricCIGens) = [1, 6, 18, 38] :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
/-- Unmixed codimension-3 complete-intersection graded quotient profiles in `R(F_0)`:
1. Plane `<z_0, z_2, z_4>`: `[1, 3, 6, 10, 15, 18, 19]`.
2. Band-3 type CI `<z_0 z_1, z_2 z_3, z_4>`: `[1, 5, 13, 25, 41, 56, 64]`.
3. Band-2 type quadric CI `<z_0^2 - z_1^2, z_2^2 - z_3^2, z_4^2 - z_5^2>`:
   `[1, 6, 18, 38, 66, 96, 116]`. -/
theorem codim3_unmixed_complete_intersection_profiles_cert :
    [0, 1, 2, 3, 4, 5, 6].map (sparseIdealQuotientDimModP 65521 gPlaneVec) =
      [1, 3, 6, 10, 15, 18, 19] ∧
    [0, 1, 2, 3, 4, 5, 6].map (sparseIdealQuotientDimModP 65521 band3TypeCIGens) =
      [1, 5, 13, 25, 41, 56, 64] ∧
    [0, 1, 2, 3, 4, 5, 6].map (sparseIdealQuotientDimModP 65521 band2TypeQuadricCIGens) =
      [1, 6, 18, 38, 66, 96, 116] :=
  ⟨rfl, rfl, rfl⟩

private def dropAtPoly (row : List Poly6) (idx : Nat) : List Poly6 :=
  match row with
  | [] => []
  | x :: xs =>
    match idx with
    | 0 => xs
    | k + 1 => x :: dropAtPoly xs k

private def polyDetAux (fuel : Nat) (mat : List (List Poly6)) : Poly6 :=
  match fuel with
  | 0 => [([0, 0, 0, 0, 0, 0], 1)]
  | fuel' + 1 =>
    match mat with
    | [] => [([0, 0, 0, 0, 0, 0], 1)]
    | r0 :: subRows =>
      match subRows with
      | [] => match r0 with | a :: _ => polyCanon6 a | [] => []
      | _ :: _ =>
        let res := r0.foldl (fun (st : Nat × Poly6) a =>
          let (col, acc) := st
          let ca := polyCanon6 a
          let nextAcc :=
            if ca.isEmpty then acc
            else
              let minor := subRows.map (fun r => dropAtPoly r col)
              let term := polyMul6 ca (polyDetAux fuel' minor)
              if col % 2 == 0 then polyAdd6 acc term else polySub6 acc term
          (col + 1, nextAcc)) (0, [])
        res.2

/-- Exact recursive Laplace determinant in `Z[z_0, ..., z_5]` (skipping zero minors). -/
def polyDetZ6 (mat : List (List Poly6)) : Poly6 :=
  polyDetAux mat.length mat

/-- G=3 complete intersection `Z_{2,2,1} = V(z_0 z_1, z_0^4 - z_1^4, z_2 z_3, z_2^4 - z_3^4, z_4)`
and its 5x5 Wiebe-Scheja-Storch matrix `C_{2,2,1}` in `Z[z_0, ..., z_5]`. -/
def gZ221Vec5 : List Poly6 :=
  [polyMul6 (varPow6 0 1) (varPow6 1 1),
   polySub6 (varPow6 0 4) (varPow6 1 4),
   polyMul6 (varPow6 2 1) (varPow6 3 1),
   polySub6 (varPow6 2 4) (varPow6 3 4),
   varPow6 4 1]

def aZ221JacVec5 : List Poly6 :=
  [polyNeg6 (varPow6 0 5), polyNeg6 (varPow6 1 5),
   polyNeg6 (varPow6 2 5), polyNeg6 (varPow6 3 5), varPow6 4 5]

def cZ221Mat5 : List (List Poly6) :=
  [[polyNeg6 (varPow6 1 3), polyNeg6 (varPow6 0 1), [], [], []],
   [polyNeg6 (varPow6 0 3), varPow6 1 1, [], [], []],
   [[], [], polyNeg6 (varPow6 3 3), polyNeg6 (varPow6 2 1), []],
   [[], [], polyNeg6 (varPow6 2 3), varPow6 3 1, []],
   [[], [], [], [], varPow6 4 4]]

def detZ221Expected : Poly6 :=
  polyMul6
    (polyMul6 (polyAdd6 (varPow6 0 4) (varPow6 1 4)) (polyAdd6 (varPow6 2 4) (varPow6 3 4)))
    (varPow6 4 4)

/-- G=3 complete intersection `Z_{2,2,2}` (`z_i z_j, z_i^4 - z_j^4` across 3 coordinate pairs)
and its 6x6 Wiebe-Scheja-Storch matrix `C_{2,2,2}` in `Z[z_0, ..., z_5]`. -/
def gZ222Vec6 : List Poly6 :=
  [polyMul6 (varPow6 0 1) (varPow6 1 1),
   polySub6 (varPow6 0 4) (varPow6 1 4),
   polyMul6 (varPow6 2 1) (varPow6 3 1),
   polySub6 (varPow6 2 4) (varPow6 3 4),
   polyMul6 (varPow6 4 1) (varPow6 5 1),
   polySub6 (varPow6 4 4) (varPow6 5 4)]

def aZ222JacVec6 : List Poly6 :=
  [polyNeg6 (varPow6 0 5), polyNeg6 (varPow6 1 5),
   polyNeg6 (varPow6 2 5), polyNeg6 (varPow6 3 5),
   polyNeg6 (varPow6 4 5), polyNeg6 (varPow6 5 5)]

def cZ222Mat6 : List (List Poly6) :=
  [[polyNeg6 (varPow6 1 3), polyNeg6 (varPow6 0 1), [], [], [], []],
   [polyNeg6 (varPow6 0 3), varPow6 1 1, [], [], [], []],
   [[], [], polyNeg6 (varPow6 3 3), polyNeg6 (varPow6 2 1), [], []],
   [[], [], polyNeg6 (varPow6 2 3), varPow6 3 1, [], []],
   [[], [], [], [], polyNeg6 (varPow6 5 3), polyNeg6 (varPow6 4 1)],
   [[], [], [], [], polyNeg6 (varPow6 4 3), varPow6 5 1]]

def detZ222Expected : Poly6 :=
  polyNeg6 (polyMul6
    (polyMul6 (polyAdd6 (varPow6 0 4) (varPow6 1 4)) (polyAdd6 (varPow6 2 4) (varPow6 3 4)))
    (polyAdd6 (varPow6 4 4) (varPow6 5 4)))

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
/-- Exact over-Z Wiebe-Scheja-Storch certificate for the `G = 3` complete intersections
`Z_{2,2,1}` and `Z_{2,2,2}`:
1. `C_{2,2,1} * G_{2,2,1} = A_{2,2,1}` holds identically in `Z[z_0, ..., z_5]`.
2. `det(C_{2,2,1}) = (z_0^4 + z_1^4)(z_2^4 + z_3^4) z_4^4` in `Z[z_0, ..., z_5]`, and
   every generator of `G_{2,2,1}` lies in `(J(F_0) : det(C_{2,2,1}))`.
3. `C_{2,2,2} * G_{2,2,2} = A_{2,2,2}` identically in `Z[z_0, ..., z_5]`,
   `det(C_{2,2,2}) = -(z_0^4 + z_1^4)(z_2^4 + z_3^4)(z_4^4 + z_5^4)`, and every generator
   of `G_{2,2,2}` lies in `(J(F_0) : det(C_{2,2,2}))`. -/
theorem g3_complete_intersection_wiebe_scheja_storch_z_cert :
    polyVecEq6 (polyMatVecMul cZ221Mat5 gZ221Vec5) aZ221JacVec5 = true ∧
    polyEq6 (polyDetZ6 cZ221Mat5) (polyCanon6 detZ221Expected) = true ∧
    gZ221Vec5.all (inColonIdeal detZ221Expected) = true ∧
    polyVecEq6 (polyMatVecMul cZ222Mat6 gZ222Vec6) aZ222JacVec6 = true ∧
    polyEq6 (polyDetZ6 cZ222Mat6) (polyCanon6 detZ222Expected) = true ∧
    gZ222Vec6.all (inColonIdeal detZ222Expected) = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

#print axioms multi_order_t8_gauss_manin_jet_cert
#print axioms multi_order_t8_exact_z_rank_witness_cert
#print axioms codim3_unmixed_complete_intersection_profiles_cert
#print axioms g3_complete_intersection_wiebe_scheja_storch_z_cert
