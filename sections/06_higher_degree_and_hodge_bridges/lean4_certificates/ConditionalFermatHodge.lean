/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
import HodgeBridgeInterfaces

/-!
# Phase 4: Conditional End-to-End Algebraicity Certificate for Fermat Fourfolds (m <= 22)

Connects the pure kernel certificates
(`shioda_aoki_complete_cycle_witness_synthesis_m3_to_m10_and_m12`,
`shioda_aoki_higher_degree_band4_decomposition_m11_to_m16_cert`,
`shioda_aoki_band4_decomposition_m18_cert`, `shioda_aoki_band4_decomposition_m20_to_m22_cert`)
to the audited `FermatFourfoldHodgeBridge` structure without adding hidden assumptions.
-/

private theorem bool_and_left {a b : Bool} (h : (a && b) = true) : a = true := by
  cases a with
  | false => cases h
  | true => rfl

private theorem bool_and_right {a b : Bool} (h : (a && b) = true) : b = true := by
  cases a with
  | false => cases h
  | true => exact h

private theorem nat_beq_eq (x : Nat) : ∀ (y : Nat), (x == y) = true → x = y := by
  induction x with
  | zero =>
    intro y h
    cases y with
    | zero => rfl
    | succ _ => cases h
  | succ x ih =>
    intro y h
    cases y with
    | zero => cases h
    | succ y =>
      have hsub : x = y := ih y h
      cases hsub
      rfl

private theorem natList_beq_eq (l1 : List Nat) :
    ∀ (l2 : List Nat), (l1 == l2) = true → l1 = l2 := by
  induction l1 with
  | nil =>
    intro l2 h
    cases l2 with
    | nil => rfl
    | cons _ _ => cases h
  | cons x xs ih =>
    intro l2 h
    cases l2 with
    | nil => cases h
    | cons y ys =>
      have hxy : (x == y) = true := bool_and_left h
      have hrest : (xs == ys) = true := bool_and_right h
      have hx : x = y := nat_beq_eq x y hxy
      have hxs : xs = ys := ih ys hrest
      cases hx
      cases hxs
      rfl

private theorem list_all_mem {α : Type} {p : α → Bool} (xs : List α) :
    xs.all p = true → ∀ x : α, x ∈ xs → p x = true := by
  induction xs with
  | nil =>
    intro _ x hx
    cases hx
  | cons y ys ih =>
    intro h x hx
    cases hx with
    | head => exact bool_and_left h
    | tail _ hmem => exact ih (bool_and_right h) x hmem

/-- Soundness of `isValidCycleWitness`: any validated `InductiveCycleWitness` lifts through
`FermatFourfoldHodgeBridge m` into `B.isAlgebraicCycleClass (witnessSortedChar w)`. -/
theorem valid_witness_implies_algebraic (m : Nat) (B : FermatFourfoldHodgeBridge m)
    (w : InductiveCycleWitness) (hw : isValidCycleWitness m w = true) :
    B.isAlgebraicCycleClass (witnessSortedChar w) := by
  cases w with
  | band1LinearPlane p1 p2 p3 =>
    cases p1 with | mk a0 a1 =>
    cases p2 with | mk a2 a3 =>
    cases p3 with | mk a4 a5 =>
    dsimp [isValidCycleWitness] at hw
    have h1 := bool_and_left hw
    have hEq3 := bool_and_right hw
    have h2 := bool_and_left h1
    have hEq2 := bool_and_right h1
    have h3 := bool_and_left h2
    have hEq1 := bool_and_right h2
    have h4 := bool_and_left h3
    have ha5r := bool_and_right h3
    have h5 := bool_and_left h4
    have ha4r := bool_and_right h4
    have h6 := bool_and_left h5
    have ha3r := bool_and_right h5
    have h7 := bool_and_left h6
    have ha2r := bool_and_right h6
    have ha0r := bool_and_left h7
    have ha1r := bool_and_right h7
    exact B.isAlgebraic_sort_closed [a0, a1, a2, a3, a4, a5] (B.shioda_band1_plane_algebraic
      a0 a1 a2 a3 a4 a5 ha0r ha1r ha2r ha3r ha4r ha5r hEq1 hEq2 hEq3)
  | band2CurveJoin t1 t2 =>
    cases t1 with | mk a0 r1 => cases r1 with | mk a1 a2 =>
    cases t2 with | mk a3 r2 => cases r2 with | mk a4 a5 =>
    dsimp [isValidCycleWitness] at hw
    have h1 := bool_and_left hw
    have hCurve := bool_and_right hw
    have hHodge := bool_and_right h1
    exact B.isAlgebraic_sort_closed [a0, a1, a2, a3, a4, a5]
      (B.shioda_band2_curve_join_algebraic a0 a1 a2 a3 a4 a5 hHodge hCurve)
  | band3SurfaceJoin p0 surf4 =>
    cases p0 with | mk a0 a1 =>
    dsimp [isValidCycleWitness] at hw
    have h1 := bool_and_left hw
    have hSurf := bool_and_right hw
    have h2 := bool_and_left h1
    have hEq := bool_and_right h1
    have ha0r := bool_and_left h2
    have ha1r := bool_and_right h2
    exact B.isAlgebraic_sort_closed ([a0, a1] ++ surf4)
      (B.shioda_band3_surface_join_algebraic a0 a1 surf4 ha0r ha1r hEq hSurf)
  | band4PairedDiagonal u0 u1 u2 =>
    dsimp [isValidCycleWitness] at hw
    have h1 := bool_and_left hw
    have hHodge := bool_and_right hw
    have h2 := bool_and_left h1
    have hu2r := bool_and_right h1
    have hu0r := bool_and_left h2
    have hu1r := bool_and_right h2
    exact B.isAlgebraic_sort_closed [u0, u0, u1, u1, u2, u2]
      (B.aoki_paired_diagonal_algebraic u0 u1 u2 hu0r hu1r hu2r hHodge)

/-- Conditional glued surface-join algebraicity theorem linking `hasGluedSurfaceJoinDecomposition`
witnesses `(t1, t2, c)` directly into `B.isAlgebraicCycleClass (t1 ++ t2)`. -/
theorem conditional_glued_surface_join_algebraic (m : Nat) (B : FermatFourfoldHodgeBridge m)
    (t1 t2 : List Nat) (c : Nat)
    (ht1 : t1.length = 3) (ht2 : t2.length = 3)
    (hc : (Nat.blt 0 c && Nat.blt c m) = true)
    (hs1 : isShiodaSurfaceHodge11 m (t1 ++ [c]) = true)
    (hs2 : isShiodaSurfaceHodge11 m (t2 ++ [m - c]) = true) :
    B.isAlgebraicCycleClass (t1 ++ t2) :=
  B.shioda_glued_surface_join_algebraic t1 t2 c ht1 ht2 hc hs1 hs2

/-- Searches the 10 triple bipartitions of a sorted 6-tuple `a` for an explicit Shioda
glued surface-join witness `(t1, t2, c)` whose sorted join image equals `a`. -/
def findGluedWitness (m : Nat) (a : List Nat) : Option (List Nat × List Nat × Nat) :=
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
              | _ :: _ => none
              | [] =>
                let splits : List (List Nat × List Nat) :=
                  [([a0, a1, a2], [a3, a4, a5]), ([a0, a1, a3], [a2, a4, a5]),
                   ([a0, a1, a4], [a2, a3, a5]), ([a0, a1, a5], [a2, a3, a4]),
                   ([a0, a2, a3], [a1, a4, a5]), ([a0, a2, a4], [a1, a3, a5]),
                   ([a0, a2, a5], [a1, a3, a4]), ([a0, a3, a4], [a1, a2, a5]),
                   ([a0, a3, a5], [a1, a2, a4]), ([a0, a4, a5], [a1, a2, a3])]
                splits.findSome? fun (t1, t2) =>
                  (rangeList 1 (m - 1)).findSome? fun c =>
                    if (t1.length == 3) && (t2.length == 3) &&
                       (Nat.blt 0 c && Nat.blt c m) &&
                       isShiodaSurfaceHodge11 m (t1 ++ [c]) &&
                       isShiodaSurfaceHodge11 m (t2 ++ [m - c]) &&
                       (ShiodaCycleSynthesis.sortNatList (t1 ++ t2) == a)
                    then some (t1, t2, c) else none

/-- Decidable check verifying that a glued witness `(t1, t2, c)` satisfies Shioda's
`X_m^2 #_c X_m^2` conditions and reconstructs `a` after coordinate sorting. -/
def isGluedWitnessValid (m : Nat) (a : List Nat) (gw : List Nat × List Nat × Nat) : Bool :=
  let (t1, t2, c) := gw
  (t1.length == 3) && (t2.length == 3) && (Nat.blt 0 c && Nat.blt c m) &&
  isShiodaSurfaceHodge11 m (t1 ++ [c]) &&
  isShiodaSurfaceHodge11 m (t2 ++ [m - c]) &&
  (ShiodaCycleSynthesis.sortNatList (t1 ++ t2) == a)

/-- Unified constructive synthesizability predicate covering both `synthesizeInductiveWitness`
(Bands 1-3 and Band-4 paired diagonals) and Shioda glued surface joins `findGluedWitness`. -/
def isHodge22Synthesizable (m : Nat) (a : List Nat) : Bool :=
  (match synthesizeInductiveWitness m a with
   | some w => isValidCycleWitness m w && (witnessSortedChar w == a)
   | none => false) ||
  (match findGluedWitness m a with
   | some gw => isGluedWitnessValid m a gw
   | none => false)

private theorem bool_or_cases {x y : Bool} (h : (x || y) = true) : x = true ∨ y = true := by
  cases x with
  | true => exact Or.inl rfl
  | false => exact Or.inr h

private theorem glued_valid_implies_algebraic (m : Nat) (B : FermatFourfoldHodgeBridge m)
    (a : List Nat) (gw : List Nat × List Nat × Nat)
    (hgw : isGluedWitnessValid m a gw = true) :
    B.isAlgebraicCycleClass a := by
  cases gw with
  | mk t1 rest =>
    cases rest with
    | mk t2 c =>
      dsimp [isGluedWitnessValid] at hgw
      have h1 := bool_and_left hgw
      have hSort := bool_and_right hgw
      have h2 := bool_and_left h1
      have hs2 := bool_and_right h1
      have h3 := bool_and_left h2
      have hs1 := bool_and_right h2
      have h4 := bool_and_left h3
      have hc := bool_and_right h3
      have ht1b := bool_and_left h4
      have ht2b := bool_and_right h4
      have ht1 : t1.length = 3 := nat_beq_eq t1.length 3 ht1b
      have ht2 : t2.length = 3 := nat_beq_eq t2.length 3 ht2b
      have hAlgJoin := B.shioda_glued_surface_join_algebraic t1 t2 c ht1 ht2 hc hs1 hs2
      have hAlgSorted := B.isAlgebraic_sort_closed (t1 ++ t2) hAlgJoin
      have hEq : ShiodaCycleSynthesis.sortNatList (t1 ++ t2) = a :=
        natList_beq_eq (ShiodaCycleSynthesis.sortNatList (t1 ++ t2)) a hSort
      rw [← hEq]
      exact hAlgSorted

/-- Any character passing `isHodge22Synthesizable m a = true` lifts through
`FermatFourfoldHodgeBridge m` into `B.isAlgebraicCycleClass a`. -/
theorem synthesizable_implies_algebraic (m : Nat) (B : FermatFourfoldHodgeBridge m)
    (a : List Nat) (hs : isHodge22Synthesizable m a = true) :
    B.isAlgebraicCycleClass a := by
  dsimp [isHodge22Synthesizable] at hs
  cases bool_or_cases hs with
  | inl hInd =>
    cases hwOpt : synthesizeInductiveWitness m a with
    | none =>
      rw [hwOpt] at hInd
      cases hInd
    | some w =>
      rw [hwOpt] at hInd
      dsimp at hInd
      have hw := bool_and_left hInd
      have heqB := bool_and_right hInd
      have hAlg := valid_witness_implies_algebraic m B w hw
      have hEq : witnessSortedChar w = a := natList_beq_eq (witnessSortedChar w) a heqB
      rw [← hEq]
      exact hAlg
  | inr hGlued =>
    cases hgwOpt : findGluedWitness m a with
    | none =>
      rw [hgwOpt] at hGlued
      cases hGlued
    | some gw =>
      rw [hgwOpt] at hGlued
      dsimp at hGlued
      exact glued_valid_implies_algebraic m B a gw hGlued

/-- End-to-end universal quantifier theorem: for any Fermat fourfold bridge `B` of degree `m`,
if every orbit representative in `sortedHodge22Tuples m` satisfies `isHodge22Synthesizable m`,
then every `α ∈ sortedHodge22Tuples m` is a genuine algebraic cycle class in `CH^2(X_m^4)_Q`. -/
theorem conditional_fermat_hodge22_all_synthesized_algebraic (m : Nat)
    (B : FermatFourfoldHodgeBridge m)
    (hall : (sortedHodge22Tuples m).all (isHodge22Synthesizable m) = true) :
    ∀ alpha, alpha ∈ sortedHodge22Tuples m → B.isAlgebraicCycleClass alpha := by
  intro alpha hmem
  have hSynth := list_all_mem (sortedHodge22Tuples m) hall alpha hmem
  exact synthesizable_implies_algebraic m B alpha hSynth

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
/-- Constructive kernel verification that every `(2,2)`-Hodge orbit representative in
`sortedHodge22Tuples m` across `m ∈ {3..16, 18, 20, 22}` satisfies `isHodge22Synthesizable m`,
unconditionally discharging the boolean hypothesis of
`conditional_fermat_hodge22_all_synthesized_algebraic` across all 17 degrees. -/
theorem conditional_fermat_hodge22_verified_m3_to_m22_cert :
    [3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 22].all
      (fun m => (sortedHodge22Tuples m).all (isHodge22Synthesizable m)) = true :=
  rfl

#print axioms valid_witness_implies_algebraic
#print axioms conditional_glued_surface_join_algebraic
#print axioms synthesizable_implies_algebraic
#print axioms conditional_fermat_hodge22_all_synthesized_algebraic
#print axioms conditional_fermat_hodge22_verified_m3_to_m22_cert
