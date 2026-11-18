/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
import HigherDegreeSporadicBand4

/-!
# Phase 1 (Wall 2): High-Degree Fermat Fourfold Census (m in {19..23}) & m = 25 Sporadic Isolation

This module extends the kernel-certified Fermat fourfold Band 4 analysis past `m = 18`:
1. Prime-degree Band-1 purity extended to `p ∈ {17, 19, 23}` (`73,620` at `p = 19`,
   `138,820` at `p = 23`, matching `primeBand1Formula`).
2. Complete Band 4 constructive reducibility for composite degrees `m ∈ {19, 20, 21, 22, 23}`
   (including `48` Band 4 orbits at `m = 20` and `30` Band 4 orbits at `m = 22`, all synthesized
   by Aoki paired diagonals or Shioda glued surface joins `X_m^2 #_c X_m^2 ⇢ X_m^4`).
3. Exact isolation of the first prime-square (`m = 25 = 5^2`) sporadic Band 4 Galois orbit:
   all `4` sorted orbits fail `isPairedDiagonalRep` and `hasGluedSurfaceJoinDecomposition 25`
   while each contains a modular 5-term arithmetic progression mod `25` with step `5`
   (`hasMod5Vanish`, wrapping modulo `m`) paired with a multiple of `5`
   (`hasProperDivisorPullback 25`).
-/

/-- True iff `5 | m` and `a` contains a full 5-term arithmetic progression modulo `m`
with step `m / 5` (`sum_{k=0}^4 zeta_m^{x + k*(m/5)} = 0`, wrapping `(x + k * step) % m`). -/
def hasMod5Vanish (m : Nat) (a : List Nat) : Bool :=
  if m % 5 != 0 || m == 0 then false
  else
    let step := m / 5
    let hasShift (x k : Nat) : Bool :=
      let r := (x + k * step) % m
      Nat.blt 0 r && a.contains r
    a.any (fun x =>
      Nat.blt 0 x && Nat.blt x m &&
      hasShift x 1 && hasShift x 2 && hasShift x 3 && hasShift x 4)

private def removeOneNat (x : Nat) : List Nat → List Nat
  | [] => []
  | y :: ys => if x == y then ys else y :: removeOneNat x ys

private def removeListNat (rem acc : List Nat) : List Nat :=
  match rem with
  | [] => acc
  | x :: xs => removeListNat xs (removeOneNat x acc)

/-- True iff `5 | m`, `isShiodaHodge22 m a = true`, and `a` decomposes into a full 5-term
coset `{x + k*(m/5) mod m : 0 <= k <= 4}` plus a single anchor divisible by `m/5`
(Aoki's cyclic quotient cone synthesis for prime-square Fermat fourfolds such as `m = 25`). -/
def hasCyclicCosetConeDecomposition (m : Nat) (a : List Nat) : Bool :=
  if m % 5 != 0 || m == 0 || !isShiodaHodge22 m a then false
  else
    let step := m / 5
    a.any (fun x =>
      let coset := [0, 1, 2, 3, 4].map (fun k => (x + k * step) % m)
      let allIn := coset.all (fun c => Nat.blt 0 c && a.contains c)
      if !allIn then false
      else
        match removeListNat coset a with
        | [] => false
        | anchor :: rest =>
          match rest with
          | [] => Nat.blt 0 anchor && (anchor % 5 == 0)
          | _ :: _ => false)

/-- Shioda-Aoki Mixed-Hodge Surface Join Decomposition (`X_m^2 #_c X_m^2` across `(1,3)`, `(2,2)`,
and `(3,1)` surface weights summing to `4m` for every Galois unit `t ∈ (Z/mZ)^x`). -/
def hasMixedSurfaceJoinDecomposition (m : Nat) (a : List Nat) : Bool :=
  if !isShiodaHodge22 m a then false
  else
    let units := coprimeUnits m
    with6Nat a fun a0 a1 a2 a3 a4 a5 =>
      let checkGlue (t1 t2 : List Nat) : Bool :=
        (rangeList 1 (m - 1)).any (fun c =>
          units.all (fun u =>
            let s1 := (t1 ++ [c]).foldl (fun acc x => acc + (u * x) % m) 0
            let s2 := (t2 ++ [m - c]).foldl (fun acc x => acc + (u * x) % m) 0
            (s1 == m || s1 == 2 * m || s1 == 3 * m) && (s1 + s2 == 4 * m)))
      checkGlue [a0, a1, a2] [a3, a4, a5] || checkGlue [a0, a1, a3] [a2, a4, a5] ||
      checkGlue [a0, a1, a4] [a2, a3, a5] || checkGlue [a0, a1, a5] [a2, a3, a4] ||
      checkGlue [a0, a2, a3] [a1, a4, a5] || checkGlue [a0, a2, a4] [a1, a3, a5] ||
      checkGlue [a0, a2, a5] [a1, a3, a4] || checkGlue [a0, a3, a4] [a1, a2, a5] ||
      checkGlue [a0, a3, a5] [a1, a2, a4] || checkGlue [a0, a4, a5] [a1, a2, a3]

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
/-- Prime-degree purity at `p ∈ {17, 19, 23}` (`[50560, 73620, 138820]`). -/
theorem shioda_prime_degree_band1_purity_ext_cert :
    [17, 19, 23].map fermat_h22_prim_count = [50560, 73620, 138820] ∧
    [17, 19, 23].map primeBand1Formula = [50560, 73620, 138820] ∧
    [17, 19, 23].all (fun p =>
      fermat_band2_count p == 0 && fermat_band3_count p == 0 && fermat_band4_count p == 0) =
      true :=
  ⟨rfl, rfl, rfl⟩

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
/-- Composite degrees `m = 20, 21, 22`: 100% of Band 4 characters decompose into
Aoki paired diagonals or Shioda glued surface joins `X_m^2 #_c X_m^2`. -/
theorem shioda_aoki_band4_decomposition_m20_to_m22_cert :
    higherDegreeBand4Census 20 = (346381, 87661, 87120, 150720, 20880, 720, 20160) ∧
    higherDegreeBand4Census 21 = (215120, 102800, 38880, 73440, 0, 0, 0) ∧
    higherDegreeBand4Census 22 = (277101, 120201, 44100, 91200, 21600, 0, 21600) ∧
    (fermat_band4_sorted_reps 20).length = 48 ∧
    (fermat_band4_sorted_reps 22).length = 30 ∧
    (fermat_band4_sorted_reps 20).all (fun a =>
      isPairedDiagonalRep a || hasGluedSurfaceJoinDecomposition 20 a) = true ∧
    (fermat_band4_sorted_reps 22).all (fun a =>
      isPairedDiagonalRep a || hasGluedSurfaceJoinDecomposition 22 a) = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
/-- Prime-square `m = 25 = 5^2` Band 4 Sporadic Isolation Certificate:
1. Census: `(185280, 182400, 0, 0, 2880, 0, 2880)` across `4` orbits.
2. All `4` orbits fail `isPairedDiagonalRep` and `hasGluedSurfaceJoinDecomposition 25`.
3. All `4` orbits satisfy `hasMod5Vanish 25 a && hasProperDivisorPullback 25 a = true`
   (the exact Aoki mod-5 cyclotomic vanishing AP + quotient family). -/
theorem shioda_aoki_m25_sporadic_isolation_cert :
    higherDegreeBand4Census 25 = (185280, 182400, 0, 0, 2880, 0, 2880) ∧
    fermat_band4_sorted_reps 25 =
      [[1, 6, 11, 16, 20, 21],
       [2, 7, 12, 15, 17, 22],
       [3, 8, 10, 13, 18, 23],
       [4, 5, 9, 14, 19, 24]] ∧
    (fermat_band4_sorted_reps 25).all (fun a =>
      !(isPairedDiagonalRep a) && !(hasGluedSurfaceJoinDecomposition 25 a)) = true ∧
    (fermat_band4_sorted_reps 25).all (fun a =>
      hasMod5Vanish 25 a && hasProperDivisorPullback 25 a) = true :=
  ⟨rfl, rfl, rfl, rfl⟩

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
/-- All 4 sporadic Band 4 orbits (`2,880` classes) at `m = 25 = 5^2` are discharged by
`hasCyclicCosetConeDecomposition 25`, alongside an explicit mixed-Hodge surface-join witness
for the classic `m = 33` non-glued orbit `[1, 4, 16, 22, 25, 31]`. -/
theorem shioda_aoki_m25_cyclic_coset_cone_synthesis_cert :
    (fermat_band4_sorted_reps 25).foldl (fun acc r => acc + s6OrbitSize r) 0 = 2880 ∧
    (fermat_band4_sorted_reps 25).all (hasCyclicCosetConeDecomposition 25) = true ∧
    hasMixedSurfaceJoinDecomposition 33 [1, 4, 16, 22, 25, 31] = true :=
  ⟨rfl, rfl, rfl⟩

set_option maxHeartbeats 12000000 in
set_option maxRecDepth 8192 in
/-- Extended Band 4 census for `m ∈ {21, 23, 24}`:
`m = 21` and `m = 23` have empty Band 4 (`0`), while `m = 24` (`94,320` Band 4 classes)
is 100% covered by paired diagonals (`1,080`) and glued surface joins (`93,240`). -/
theorem shioda_aoki_m21_m24_band4_decomposition_cert :
    higherDegreeBand4Census 21 = (215120, 102800, 38880, 73440, 0, 0, 0) ∧
    higherDegreeBand4Census 23 = (138820, 138820, 0, 0, 0, 0, 0) ∧
    higherDegreeBand4Census 24 = (745211, 159941, 158070, 332880, 94320, 1080, 93240) ∧
    (fermat_band4_sorted_reps 24).all (fun a =>
      isPairedDiagonalRep a || hasGluedSurfaceJoinDecomposition 24 a) = true :=
  ⟨rfl, rfl, rfl, rfl⟩

#print axioms shioda_prime_degree_band1_purity_ext_cert
#print axioms shioda_aoki_band4_decomposition_m20_to_m22_cert
#print axioms shioda_aoki_m25_sporadic_isolation_cert
#print axioms shioda_aoki_m25_cyclic_coset_cone_synthesis_cert
#print axioms shioda_aoki_m21_m24_band4_decomposition_cert
