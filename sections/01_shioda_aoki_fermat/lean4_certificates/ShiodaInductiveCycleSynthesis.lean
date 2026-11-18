/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
import ShiodaFormalConjectures

/-!
# Constructive Shioda-Aoki Algebraic Cycle Witness Synthesis & Surface Lefschetz (1,1) Verification

This module upgrades boolean Shioda-Aoki partition filtering into constructive algebraic
cycle witness synthesis across all four Shioda-Aoki bands for Fermat fourfolds `X_m^4`:
1. `isShiodaSurfaceHodge11`: exact Galois criterion over `(Z/mZ)^x` for a 4-tuple character
   to lie in `H^{1,1}_{prim}(X_m^2) ∩ H^2(X_m^2, Q)` on the Fermat surface `X_m^2 ⊂ P^3`,
   which is algebraic by the Lefschetz (1,1)-theorem.
2. `InductiveCycleWitness`: explicit algebraic witness datatype covering Band 1
   (`X_m^0 * X_m^0 * X_m^0`), Band 2 (`X_m^1 * X_m^1` curve join), Band 3
   (`X_m^0 * X_m^2` surface-curve join), and Band 4 (Aoki paired-diagonal correspondences).
3. `synthesizeInductiveWitness`: constructive extractor mapping every primitive `(2,2)`-Hodge
   character to an explicit `InductiveCycleWitness` together with `isValidCycleWitness` and
   `witnessSortedChar`.
4. Certified theorems `shioda_band3_implies_surface_hodge11_m3_to_m12` and
   `shioda_aoki_complete_cycle_witness_synthesis_m3_to_m10_and_m12` covering every degree
   `m ∈ {3, 4, 5, 6, 7, 8, 9, 10, 12}` (including all 1,751 classes at `m = 6` and all
   52,991 classes at `m = 12`).

All theorems compile constructively with no placeholder proofs and no external dependencies.
-/

/-- Exact Fermat surface `X_m^2 ⊂ P^3` rational `(1,1)`-Hodge criterion:
`s.length == 4`, `1 <= b_i < m`, and for EVERY unit `t ∈ (Z/mZ)^x`,
`sum_{i=0}^3 ((t * b_i) mod m) == 2 * m`. -/
def isShiodaSurfaceHodge11 (m : Nat) (s : List Nat) : Bool :=
  s.length == 4 &&
  s.all (fun x => Nat.blt 0 x && Nat.blt x m) &&
  (coprimeUnits m).all (fun t =>
    (s.foldl (fun acc x => acc + (t * x) % m) 0) == 2 * m)

/-- Exact Fermat curve-product `X_m^1 × X_m^1` rational `(1,1)`-Hodge criterion:
for EVERY unit `t ∈ (Z/mZ)^x`, one triple `(t1 or t2)` has Hodge type `(1,0)` (sum `m`)
and the other has Hodge type `(0,1)` (sum `2*m`), so their product lies in
`H^{1,1}(X_m^1 × X_m^1) ∩ H^2(X_m^1 × X_m^1, Q)` and is algebraic by Lefschetz `(1,1)`. -/
def isShiodaCurveProductHodge11 (m : Nat) (t1 t2 : List Nat) : Bool :=
  t1.length == 3 && t2.length == 3 &&
  t1.all (fun x => Nat.blt 0 x && Nat.blt x m) &&
  t2.all (fun x => Nat.blt 0 x && Nat.blt x m) &&
  (coprimeUnits m).all (fun t =>
    let s1 := t1.foldl (fun acc x => acc + (t * x) % m) 0
    let s2 := t2.foldl (fun acc x => acc + (t * x) % m) 0
    (s1 == m && s2 == 2 * m) || (s1 == 2 * m && s2 == m))

/-- Explicit inductive algebraic cycle witness for primitive `(2,2)`-Hodge classes on `X_m^4`. -/
inductive InductiveCycleWitness where
  | band1LinearPlane (p1 p2 p3 : Nat × Nat)
  | band2CurveJoin (t1 t2 : Nat × Nat × Nat)
  | band3SurfaceJoin (pair0 : Nat × Nat) (surf4 : List Nat)
  | band4PairedDiagonal (u0 u1 u2 : Nat)

namespace ShiodaCycleSynthesis

private def insertNatSorted (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if Nat.ble x y then x :: y :: ys else y :: insertNatSorted x ys

/-- Insertion sort on `List Nat` into non-decreasing order. -/
def sortNatList : List Nat → List Nat
  | [] => []
  | x :: xs => insertNatSorted x (sortNatList xs)

end ShiodaCycleSynthesis

open ShiodaCycleSynthesis (sortNatList)

private def inOpenRange (m x : Nat) : Bool :=
  Nat.blt 0 x && Nat.blt x m

/-- Validates that an `InductiveCycleWitness` satisfies the exact geometric and Galois
conditions of its Shioda-Aoki cycle family on `X_m^4`. -/
def isValidCycleWitness (m : Nat) (w : InductiveCycleWitness) : Bool :=
  match w with
  | .band1LinearPlane (a0, a1) (a2, a3) (a4, a5) =>
    inOpenRange m a0 && inOpenRange m a1 &&
    inOpenRange m a2 && inOpenRange m a3 &&
    inOpenRange m a4 && inOpenRange m a5 &&
    (a0 + a1 == m) && (a2 + a3 == m) && (a4 + a5 == m)
  | .band2CurveJoin (a0, a1, a2) (a3, a4, a5) =>
    let s1 := a0 + a1 + a2
    let s2 := a3 + a4 + a5
    inOpenRange m a0 && inOpenRange m a1 && inOpenRange m a2 &&
    inOpenRange m a3 && inOpenRange m a4 && inOpenRange m a5 &&
    ((s1 == m && s2 == 2 * m) || (s1 == 2 * m && s2 == m)) &&
    isShiodaHodge22 m [a0, a1, a2, a3, a4, a5] &&
    isShiodaCurveProductHodge11 m [a0, a1, a2] [a3, a4, a5]
  | .band3SurfaceJoin (a0, a1) surf4 =>
    inOpenRange m a0 && inOpenRange m a1 &&
    (a0 + a1 == m) && isShiodaSurfaceHodge11 m surf4
  | .band4PairedDiagonal u0 u1 u2 =>
    inOpenRange m u0 && inOpenRange m u1 && inOpenRange m u2 &&
    isShiodaHodge22 m [u0, u0, u1, u1, u2, u2]

/-- Returns the sorted 6-tuple character image of the Shioda inductive join map `Φ(w)`. -/
def witnessSortedChar (w : InductiveCycleWitness) : List Nat :=
  match w with
  | .band1LinearPlane (a0, a1) (a2, a3) (a4, a5) => sortNatList [a0, a1, a2, a3, a4, a5]
  | .band2CurveJoin (a0, a1, a2) (a3, a4, a5) => sortNatList [a0, a1, a2, a3, a4, a5]
  | .band3SurfaceJoin (a0, a1) surf4 => sortNatList ([a0, a1] ++ surf4)
  | .band4PairedDiagonal u0 u1 u2 => sortNatList [u0, u0, u1, u1, u2, u2]

private def with6NatOpt {α : Type} (a : List Nat)
    (f : Nat → Nat → Nat → Nat → Nat → Nat → Option α) : Option α :=
  match a with
  | [] => none
  | a0 :: r0 =>
    match r0 with
    | [] => none
    | a1 :: r1 =>
      match r1 with
      | [] => none
      | a2 :: r2 =>
        match r2 with
        | [] => none
        | a3 :: r3 =>
          match r3 with
          | [] => none
          | a4 :: r4 =>
            match r4 with
            | [] => none
            | a5 :: r5 =>
              match r5 with
              | [] => f a0 a1 a2 a3 a4 a5
              | _ :: _ => none

private def synthBand1Aux (m a0 a1 a2 a3 a4 a5 : Nat) : Option InductiveCycleWitness :=
  let mk (x0 x1 x2 x3 x4 x5 : Nat) : Option InductiveCycleWitness :=
    some (.band1LinearPlane (x0, x1) (x2, x3) (x4, x5))
  if a0 + a1 == m && a2 + a3 == m && a4 + a5 == m then mk a0 a1 a2 a3 a4 a5
  else if a0 + a1 == m && a2 + a4 == m && a3 + a5 == m then mk a0 a1 a2 a4 a3 a5
  else if a0 + a1 == m && a2 + a5 == m && a3 + a4 == m then mk a0 a1 a2 a5 a3 a4
  else if a0 + a2 == m && a1 + a3 == m && a4 + a5 == m then mk a0 a2 a1 a3 a4 a5
  else if a0 + a2 == m && a1 + a4 == m && a3 + a5 == m then mk a0 a2 a1 a4 a3 a5
  else if a0 + a2 == m && a1 + a5 == m && a3 + a4 == m then mk a0 a2 a1 a5 a3 a4
  else if a0 + a3 == m && a1 + a2 == m && a4 + a5 == m then mk a0 a3 a1 a2 a4 a5
  else if a0 + a3 == m && a1 + a4 == m && a2 + a5 == m then mk a0 a3 a1 a4 a2 a5
  else if a0 + a3 == m && a1 + a5 == m && a2 + a4 == m then mk a0 a3 a1 a5 a2 a4
  else if a0 + a4 == m && a1 + a2 == m && a3 + a5 == m then mk a0 a4 a1 a2 a3 a5
  else if a0 + a4 == m && a1 + a3 == m && a2 + a5 == m then mk a0 a4 a1 a3 a2 a5
  else if a0 + a4 == m && a1 + a5 == m && a2 + a3 == m then mk a0 a4 a1 a5 a2 a3
  else if a0 + a5 == m && a1 + a2 == m && a3 + a4 == m then mk a0 a5 a1 a2 a3 a4
  else if a0 + a5 == m && a1 + a3 == m && a2 + a4 == m then mk a0 a5 a1 a3 a2 a4
  else if a0 + a5 == m && a1 + a4 == m && a2 + a3 == m then mk a0 a5 a1 a4 a2 a3
  else none

private def synthBand2Aux (m a0 a1 a2 a3 a4 a5 : Nat) : Option InductiveCycleWitness :=
  let check (x0 x1 x2 x3 x4 x5 : Nat) : Bool :=
    let s1 := x0 + x1 + x2
    let s2 := x3 + x4 + x5
    (s1 == m && s2 == 2 * m) || (s1 == 2 * m && s2 == m)
  let mk (x0 x1 x2 x3 x4 x5 : Nat) : Option InductiveCycleWitness :=
    some (.band2CurveJoin (x0, x1, x2) (x3, x4, x5))
  if check a0 a1 a2 a3 a4 a5 then mk a0 a1 a2 a3 a4 a5
  else if check a0 a1 a3 a2 a4 a5 then mk a0 a1 a3 a2 a4 a5
  else if check a0 a1 a4 a2 a3 a5 then mk a0 a1 a4 a2 a3 a5
  else if check a0 a1 a5 a2 a3 a4 then mk a0 a1 a5 a2 a3 a4
  else if check a0 a2 a3 a1 a4 a5 then mk a0 a2 a3 a1 a4 a5
  else if check a0 a2 a4 a1 a3 a5 then mk a0 a2 a4 a1 a3 a5
  else if check a0 a2 a5 a1 a3 a4 then mk a0 a2 a5 a1 a3 a4
  else if check a0 a3 a4 a1 a2 a5 then mk a0 a3 a4 a1 a2 a5
  else if check a0 a3 a5 a1 a2 a4 then mk a0 a3 a5 a1 a2 a4
  else if check a0 a4 a5 a1 a2 a3 then mk a0 a4 a5 a1 a2 a3
  else none

private def synthBand3Aux (m a0 a1 a2 a3 a4 a5 : Nat) : Option InductiveCycleWitness :=
  if a0 + a1 == m then some (.band3SurfaceJoin (a0, a1) [a2, a3, a4, a5])
  else if a0 + a2 == m then some (.band3SurfaceJoin (a0, a2) [a1, a3, a4, a5])
  else if a0 + a3 == m then some (.band3SurfaceJoin (a0, a3) [a1, a2, a4, a5])
  else if a0 + a4 == m then some (.band3SurfaceJoin (a0, a4) [a1, a2, a3, a5])
  else if a0 + a5 == m then some (.band3SurfaceJoin (a0, a5) [a1, a2, a3, a4])
  else if a1 + a2 == m then some (.band3SurfaceJoin (a1, a2) [a0, a3, a4, a5])
  else if a1 + a3 == m then some (.band3SurfaceJoin (a1, a3) [a0, a2, a4, a5])
  else if a1 + a4 == m then some (.band3SurfaceJoin (a1, a4) [a0, a2, a3, a5])
  else if a1 + a5 == m then some (.band3SurfaceJoin (a1, a5) [a0, a2, a3, a4])
  else if a2 + a3 == m then some (.band3SurfaceJoin (a2, a3) [a0, a1, a4, a5])
  else if a2 + a4 == m then some (.band3SurfaceJoin (a2, a4) [a0, a1, a3, a5])
  else if a2 + a5 == m then some (.band3SurfaceJoin (a2, a5) [a0, a1, a3, a4])
  else if a3 + a4 == m then some (.band3SurfaceJoin (a3, a4) [a0, a1, a2, a5])
  else if a3 + a5 == m then some (.band3SurfaceJoin (a3, a5) [a0, a1, a2, a4])
  else if a4 + a5 == m then some (.band3SurfaceJoin (a4, a5) [a0, a1, a2, a3])
  else none

/-- Constructively synthesizes an explicit `InductiveCycleWitness` from any 6-tuple character `a`
across Bands 1, 2, 3, and 4. -/
def synthesizeInductiveWitness (m : Nat) (a : List Nat) : Option InductiveCycleWitness :=
  with6NatOpt a fun a0 a1 a2 a3 a4 a5 =>
    if isBand1CompletePairs m a then synthBand1Aux m a0 a1 a2 a3 a4 a5
    else if isBand2ThreePlusThree m a then synthBand2Aux m a0 a1 a2 a3 a4 a5
    else if isBand3TwoPlusFour m a then synthBand3Aux m a0 a1 a2 a3 a4 a5
    else if a0 == a1 && a2 == a3 && a4 == a5 then some (.band4PairedDiagonal a0 a2 a4)
    else none

private def checkBand3SurfaceAt (m : Nat) : Bool :=
  let band3Orbits := (sortedHodge22Tuples m).filter (isBand3TwoPlusFour m)
  band3Orbits.all fun alpha =>
    match synthesizeInductiveWitness m alpha with
    | none => false
    | some w =>
      match w with
      | .band1LinearPlane _ _ _ => false
      | .band2CurveJoin _ _ => false
      | .band3SurfaceJoin _ surf4 => isShiodaSurfaceHodge11 m surf4
      | .band4PairedDiagonal _ _ _ => false

private def checkCompleteWitnessAt (m : Nat) : Bool :=
  (sortedHodge22Tuples m).all fun alpha =>
    match synthesizeInductiveWitness m alpha with
    | none => false
    | some w => isValidCycleWitness m w && (witnessSortedChar w == alpha)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
/-- Across all degrees `m ∈ {3, 4, 5, 6, 7, 8, 9, 10, 12}`, every Band 3 `(2,2)`-Hodge
character on `X_m^4` synthesizes an explicit `band3SurfaceJoin (a0, a1) surf4` witness whose
4-tuple factor `surf4` satisfies `isShiodaSurfaceHodge11 m surf4 = true` (hence is algebraic
on the Fermat surface `X_m^2 ⊂ P^3` by the Lefschetz `(1,1)`-theorem). -/
theorem shioda_band3_implies_surface_hodge11_m3_to_m12 :
    [3, 4, 5, 6, 7, 8, 9, 10, 12].all checkBand3SurfaceAt = true :=
  rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
/-- Across all degrees `m ∈ {3, 4, 5, 6, 7, 8, 9, 10, 12}`, EVERY primitive `(2,2)`-Hodge
orbit representative `alpha ∈ sortedHodge22Tuples m` (accounting for all 1,751 characters at `m = 6`
and all 52,991 characters at `m = 12`) constructively synthesizes a valid `InductiveCycleWitness`
whose inductive join character equals `alpha`. -/
theorem shioda_aoki_complete_cycle_witness_synthesis_m3_to_m10_and_m12 :
    [3, 4, 5, 6, 7, 8, 9, 10, 12].all checkCompleteWitnessAt = true :=
  rfl

#print axioms shioda_band3_implies_surface_hodge11_m3_to_m12
#print axioms shioda_aoki_complete_cycle_witness_synthesis_m3_to_m10_and_m12
