-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/AtText/ShortTailToy.lean: a small example that satisfies the algebraic part of the
non-degeneracy premise of the negative test short_tail_fails.
Terms: Johnson/LinkSim/Spec.lean; for the prover's algorithm, Johnson/LinkSim/AtText/Defs.lean.

What this file proves. short_tail_fails (Johnson/LinkSim/AtText/ShortTail.lean) asks that the last
entry of shPsi is not 0. shPsi is made in four steps. First, the claim's coefficient vector is read
off the verifier's state along the prover's algorithm. Second, the shift of the first fold's
coefficients is foldShift at that vector (Fold.lean). Third, that shift is packed into a row
(packedN, Johnson/Prover/Link/BodyPack.lean). Fourth, tailFor (Johnson/LinkSim/Tail.lean) gives the
compensating tail for that row at the points of the opened positions. This file takes the last three
steps alone. The vector v, the message's change dm and the set of points are values that are chosen,
not read off any run of the algorithm, and the points are not the points of positions.
  shortToy_member   in the small example below, there is one point, as many as the tail has
                    entries, and the tail's last entry is not 0.
  shortToy_exists   the same, stated as "there are a stage, v, dm, challenges and points".
So, at the example's sizes, foldShift, packedN and tailFor in turn do not always give 0 at the
last entry: no reason that lies in these three steps alone makes the premise fail there.
The small example: a stage with one row variable, one main row entry, a mask row of three
entries and a tail of one entry; the one point 1; every sampled element 1; v = 1 everywhere; dm
= 1 at the main row with the row variable 0, and 0 elsewhere. There the last and only entry of
the tail is not 0 (in the proof it comes out as 1).

How it fits. ShortTail.lean's head points here for the part of its premise that is checked.

Other names (namespace OnBytes.LinkSim.AtText).
  sToy, DToy, vToy, dmToy   the small example.
  tailFor_single   through one point, the interpolating polynomial is the constant.
  placeV_total     a vector that is placed into other coordinates keeps its sum.
  drawn_toy        every sampled element of DToy is 1.
  toy_row_sum      the packed row's three entries add up to the three coefficients' sum.
  sTr_head         a first round polynomial's coefficient 0 is the pairing of the two lower
                   halves.
  toy_pair         the first round's coefficient 0 in the example is 1.
  toy_shift_sum    the three coefficients of the shift in the example add up to -1.

Limits.
- It is no instance of short_tail_fails's own premise, which is stated along the prover's algorithm:
  short_tail_fails (Johnson/LinkSim/AtText/ShortTail.lean) stays conditional. It says nothing on
  whether the link's own algorithm ever meets the premise, and nothing at the library's full-size
  parameter set (dsFull).
- It is one small example: a tail of one entry and one point, where the full-size parameter set has
  97 of each at that tree.
- The example's stage is not checked against the public premises on sizes.
Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.AtText.ShortTail
import Johnson.Prover.Link.FoldRun

set_option autoImplicit false

noncomputable section

namespace OnBytes.LinkSim.AtText
open OnBytes OnBytes.Slice Cb
open Johnson.Prover.Link

/-- A stage with one row variable; main code (0, 1, 0); mask code (0, 3, 1). -/
abbrev sToy : Sg := ⟨⟨0, 1, 0⟩, ⟨0, 3, 1⟩, 0, 1, 0⟩

/-- Every round samples the element 1. -/
def DToy : ℕ → Fmt.Drawn := fun _ => ⟨[ofE 1], [], [], none⟩

def vToy : sToy.cIn.J → GE := fun _ => 1

/-- 1 at the main row with the row variable 0; 0 elsewhere. -/
def dmToy : sToy.cIn.J → GE := fun x =>
  match x with
  | .inl bc => if bc.1 (0 : Fin 1) then 0 else 1
  | .inr _ => 0

theorem tailFor_single {F : Type} [Field F] [DecidableEq F] (x : F) (v : F → F) :
    tailFor {x} v 0 = v x := by
  unfold tailFor
  rw [Lagrange.interpolate_singleton, Polynomial.coeff_C_zero]

theorem placeV_total {Cl J : Type} [Fintype Cl] [Fintype J] [DecidableEq J] (plc : Cl → J)
    (v : Cl → GE) : ∑ j, placeV plc v j = ∑ c, v c := by
  unfold placeV
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_ite_eq]
  exact if_pos (Finset.mem_univ _)

theorem drawn_toy (n : ℕ) : drawnE (DToy n) = 1 := by
  show readE (E.ofTriple (ofE 1)) = 1
  rw [readE_ofTriple, toE_ofE]

/-- The packed row's three entries add up to the three coefficients' sum. -/
theorem toy_row_sum (W : HIdx (sVars GE 2 (sToy.h + sToy.g)) → GE) :
    packedN sToy W 0 0 + packedN sToy W 0 1 + packedN sToy W 0 2 =
      W (Sum.inl (0 : Fin 2)) + W (Sum.inl (1 : Fin 2)) + W (Sum.inr ()) := by
  have hl : sToy.h + 2 * sToy.g + 1 ≤ sToy.Z.l := by decide
  have e : ∀ (j : ℕ) (hj : j < sToy.Z.l), packedN sToy W 0 j =
      packed sToy hl W (fun t => (0 : ℕ).testBit t.val, ⟨j, hj⟩) := fun j hj => dif_pos ⟨hl, hj⟩
  have e3 : packedN sToy W 0 0 + packedN sToy W 0 1 + packedN sToy W 0 2 =
      ∑ j : Fin 3, packed sToy hl W (fun t => (0 : ℕ).testBit t.val, j) := by
    rw [Fin.sum_univ_three, e 0 (by decide), e 1 (by decide), e 2 (by decide)]
    rfl
  rw [e3]
  have e4 : ∑ j : Fin 3, packed sToy hl W (fun t => (0 : ℕ).testBit t.val, j) =
      ∑ c : PCol 0 1 1, pkC 0 1 1 W (fun t => (0 : ℕ).testBit t.val, c) :=
    placeV_total (placeF sToy hl) _
  have pk : ∀ (u : (Fin 1 × Fin 2) ⊕ Unit) (w : GE),
      (match u with
        | .inl tp => W (hIx GE 2 (0 + 1) (Fin.natAdd 0 tp.1) tp.2)
        | .inr _ => W (hCst GE 2 (0 + 1))) = w →
      pkC 0 1 1 W (fun t => (0 : ℕ).testBit t.val, .inr u) = w := by
    intro u w hw
    cases u with
    | inl tp =>
      show W (hIx GE 2 (0 + 1) (Fin.natAdd 0 tp.1) tp.2) +
        (if pLead 1 1 (.inl tp) then ∑ i : Fin 0, _ else 0) = w
      rw [Fin.sum_univ_zero, ite_self, add_zero]
      exact hw
    | inr x =>
      show W (hCst GE 2 (0 + 1)) + (if pLead 1 1 (.inr x) then ∑ i : Fin 0, _ else 0) = w
      rw [Fin.sum_univ_zero, ite_self, add_zero]
      exact hw
  rw [e4, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_prod_type,
    Fin.sum_univ_zero, Fin.sum_univ_one, Fin.sum_univ_two, Fintype.sum_unique, zero_add,
    pk (.inl (0, 0)) (W (Sum.inl (0 : Fin 2))) rfl, pk (.inl (0, 1)) (W (Sum.inl (1 : Fin 2))) rfl,
    pk (.inr default) (W (Sum.inr ())) rfl]

theorem sTr_head {J : Type} [Fintype J] (n k : ℕ) (L m : (Fin (k + 1) → Bool) → J → GE)
    (γ : HPt (sVars GE n (k + 1))) :
    sTr n (k + 1) L m γ (Sum.inl (0 : Fin (n + 1))) = sBl (sHalf false L) (sHalf false m) :=
  if_pos rfl

/-- The first round's coefficient 0 in the example. -/
theorem toy_pair (γ : HPt (sVars GE 2 (sToy.h + sToy.g))) :
    foldQ sToy vToy dmToy 0 1 γ (Sum.inl (0 : Fin 3)) = 1 := by
  have h0 : hTr (sVars GE 2 (sToy.h + sToy.g)) (0 : GE) 0 γ (Sum.inl (0 : Fin 3)) = 0 :=
    (Prod.mk.inj (List.cons.inj (pairs_zero 1 γ)).1).1
  rw [foldQ_eq]
  unfold foldQc
  rw [h0, zero_add, one_mul]
  refine (sTr_head 2 0 _ _ γ).trans ?_
  unfold sBl sHalf
  rw [Fintype.sum_unique, Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three]
  show (1 : GE) * 1 + (_ * 0 + _ * 0 + _ * 0) = 1
  rw [mul_zero, mul_zero, mul_zero, add_zero, add_zero, add_zero, mul_one]

/-- The three coefficients of the shift in the example add up to -1. -/
theorem toy_shift_sum :
    foldShift sToy vToy dmToy DToy (Sum.inl (0 : Fin 2)) +
        foldShift sToy vToy dmToy DToy (Sum.inl (1 : Fin 2)) +
        foldShift sToy vToy dmToy DToy (Sum.inr ()) = -1 := by
  have hq : ∀ y1 y2 : GE,
      shiftH (E := GE) 1 0 [(y1, y2)] (Sum.inl (0 : Fin 2)) +
          shiftH (E := GE) 1 0 [(y1, y2)] (Sum.inl (1 : Fin 2)) +
          shiftH (E := GE) 1 0 [(y1, y2)] (Sum.inr ()) = -y1 := by
    intro y1 y2
    have w0 : shiftH (E := GE) 1 0 [(y1, y2)] (Sum.inl (0 : Fin 2)) = 0 - y2 - 2 * y1 := by
      show (if (0 : Fin 2) = (0 : Fin 2) then 0 - y2 - 2 * y1 else y2) = _
      exact if_pos rfl
    have w1 : shiftH (E := GE) 1 0 [(y1, y2)] (Sum.inl (1 : Fin 2)) = y2 := by
      show (if (1 : Fin 2) = (0 : Fin 2) then 0 - y2 - 2 * y1 else y2) = _
      exact if_neg (by decide)
    have w2 : shiftH (E := GE) 1 0 [(y1, y2)] (Sum.inr ()) = y1 := rfl
    rw [w0, w1, w2]
    ring
  have e := hq
    (foldQ sToy vToy dmToy 0 (drawnE (DToy 0))
      (ptK (sToy.h + sToy.g) fun n => drawnE (DToy (n + 1))) (Sum.inl (0 : Fin 3)))
    (foldQ sToy vToy dmToy 0 (drawnE (DToy 0))
      (ptK (sToy.h + sToy.g) fun n => drawnE (DToy (n + 1))) (Sum.inl (2 : Fin 3)))
  rw [drawn_toy 0, toy_pair] at e
  exact e

open Classical in
/-- In the small example the tail that tailFor builds from the packed foldShift has a last entry
that is not 0: the algebraic part of short_tail_fails's premise, not the premise of the prover's
algorithm. -/
theorem shortToy_member :
    ({1} : Finset GE).card = sToy.Z.r ∧
      tailFor {1} (fun p => msgPart sToy.Z.r sToy.Z.l p fun i =>
        -packedN sToy (foldShift sToy vToy dmToy DToy) 0 i) (sToy.Z.r - 1) ≠ 0 := by
  refine ⟨Finset.card_singleton 1, ?_⟩
  show tailFor {1} (fun p => msgPart 1 3 p fun i =>
    -packedN sToy (foldShift sToy vToy dmToy DToy) 0 i) 0 ≠ 0
  rw [tailFor_single]
  have e : msgPart 1 3 (1 : GE) (fun i => -packedN sToy (foldShift sToy vToy dmToy DToy) 0 i) =
      -(packedN sToy (foldShift sToy vToy dmToy DToy) 0 0 +
        packedN sToy (foldShift sToy vToy dmToy DToy) 0 1 +
        packedN sToy (foldShift sToy vToy dmToy DToy) 0 2) := by
    unfold msgPart
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    simp only [one_pow, one_mul]
    ring
  rw [e, toy_row_sum, toy_shift_sum, neg_neg]
  exact one_ne_zero

open Classical in
/-- The same, as "there are". -/
theorem shortToy_exists : ∃ (s : Sg) (v dm : s.cIn.J → GE) (D : ℕ → Fmt.Drawn) (pts : Finset GE),
    pts.card = s.Z.r ∧
      tailFor pts (fun p => msgPart s.Z.r s.Z.l p fun i => -packedN s (foldShift s v dm D) 0 i)
        (s.Z.r - 1) ≠ 0 :=
  ⟨sToy, vToy, dmToy, DToy, {1}, shortToy_member⟩

end OnBytes.LinkSim.AtText

#print axioms OnBytes.LinkSim.AtText.tailFor_single
#print axioms OnBytes.LinkSim.AtText.placeV_total
#print axioms OnBytes.LinkSim.AtText.drawn_toy
#print axioms OnBytes.LinkSim.AtText.toy_row_sum
#print axioms OnBytes.LinkSim.AtText.sTr_head
#print axioms OnBytes.LinkSim.AtText.toy_pair
#print axioms OnBytes.LinkSim.AtText.toy_shift_sum
#print axioms OnBytes.LinkSim.AtText.shortToy_member
#print axioms OnBytes.LinkSim.AtText.shortToy_exists
