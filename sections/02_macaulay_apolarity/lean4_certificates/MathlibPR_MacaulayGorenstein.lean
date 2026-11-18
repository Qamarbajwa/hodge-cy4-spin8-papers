/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
import ShiodaFormalConjectures

/-!
# Artinian Gorenstein Apolarity and Macaulay Contraction Ranks

This module provides Mathlib-style universally quantified theorems for
monomial divisibility, exponent-vector addition commutativity, and
Macaulay pairing matrix transpose duality across degrees `0 <= d <= 12`.
-/

private theorem nat_ble_refl (n : Nat) : Nat.ble n n = true := by
  induction n with
  | zero => rfl
  | succ _ ih => exact ih

private theorem nat_ble_trans (a b c : Nat)
    (hab : Nat.ble a b = true) (hbc : Nat.ble b c = true) :
    Nat.ble a c = true := by
  induction a generalizing b c with
  | zero => rfl
  | succ a' ih =>
    cases b with
    | zero => contradiction
    | succ b' =>
      cases c with
      | zero => contradiction
      | succ c' => exact ih b' c' hab hbc

private theorem bool_and_left {a b : Bool} (h : (a && b) = true) : a = true := by
  cases a <;> cases b <;> first | rfl | contradiction

private theorem bool_and_right {a b : Bool} (h : (a && b) = true) : b = true := by
  cases a <;> cases b <;> first | rfl | contradiction

private theorem bool_and_intro {a b : Bool} (ha : a = true) (hb : b = true) :
    (a && b) = true := by
  rw [ha, hb]; rfl

/-- Monomial divisibility is reflexive for all exponent lists `m`. -/
theorem monomialDivides_refl (m : List Nat) : monomialDivides m m = true := by
  induction m with
  | nil => rfl
  | cons x xs ih =>
    dsimp [monomialDivides]
    exact bool_and_intro (nat_ble_refl x) ih

/-- Monomial divisibility is transitive for all exponent lists `a`, `b`, `c`. -/
theorem monomialDivides_trans (a b c : List Nat)
    (hab : monomialDivides a b = true) (hbc : monomialDivides b c = true) :
    monomialDivides a c = true := by
  induction a generalizing b c with
  | nil => rfl
  | cons x xs ih =>
    cases b with
    | nil => contradiction
    | cons y ys =>
      cases c with
      | nil => contradiction
      | cons z zs =>
        dsimp [monomialDivides] at hab hbc ⊢
        exact bool_and_intro
          (nat_ble_trans x y z (bool_and_left hab) (bool_and_left hbc))
          (ih ys zs (bool_and_right hab) (bool_and_right hbc))

/-- Componentwise exponent addition is commutative for all lists `m1` and `m2`. -/
theorem addExp4_comm (m1 m2 : List Nat) : addExp4 m1 m2 = addExp4 m2 m1 := by
  induction m1 generalizing m2 with
  | nil =>
    cases m2 <;> rfl
  | cons x xs ih =>
    cases m2 with
    | nil => rfl
    | cons y ys =>
      dsimp [addExp4]
      rw [Nat.add_comm x y, ih ys]

/-- Contraction coefficient in any socle polynomial is symmetric in `m1` and `m2`. -/
theorem coeffInSocle_addExp4_comm (socle : List (List Nat × Int)) (m1 m2 : List Nat) :
    coeffInSocle (addExp4 m1 m2) socle = coeffInSocle (addExp4 m2 m1) socle := by
  rw [addExp4_comm]

private def intListEq (l1 l2 : List Int) : Bool :=
  match l1 with
  | [] => match l2 with | [] => true | _ :: _ => false
  | x :: xs => match l2 with | [] => false | y :: ys => intEq x y && intListEq xs ys

private def intMatEq (m1 m2 : List (List Int)) : Bool :=
  match m1 with
  | [] => match m2 with | [] => true | _ :: _ => false
  | r1 :: rs1 => match m2 with | [] => false | r2 :: rs2 => intListEq r1 r2 && intMatEq rs1 rs2

set_option maxHeartbeats 2000000 in
/-- Explicit Macaulay pairing matrices satisfy transpose duality across all `0 <= d <= 12`
for both `planeSoclePoly` and `quadricJetSoclePoly`. -/
theorem macaulayPairingMatrix_transpose_duality :
    (rangeList 0 13).all (fun d =>
      intMatEq (macaulayPairingMatrix planeSoclePoly d)
        (transposeMat (monomials4 d).length
          (macaulayPairingMatrix planeSoclePoly (12 - d))) &&
      intMatEq (macaulayPairingMatrix quadricJetSoclePoly d)
        (transposeMat (monomials4 d).length
          (macaulayPairingMatrix quadricJetSoclePoly (12 - d)))) = true := by
  rfl

#print axioms monomialDivides_refl
#print axioms monomialDivides_trans
#print axioms addExp4_comm
#print axioms coeffInSocle_addExp4_comm
#print axioms macaulayPairingMatrix_transpose_duality
