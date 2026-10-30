-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/PadFreeByBlocks.lean: the public condition PadsFree
(Johnson/P5J/WordsAtQ.lean: "no place that a borrower's seats name for the borrowed matrix is a
pad's place of either copy")
FROM A CHEAP TEST, BY BLOCKS, at the seats that the plan's layout gives. Definitions with code and
theorems.

Why. That condition's plain test (Johnson/P5J/PadsFreeB.lean, not in this repository) asks every
row of symbols, every column and every member: too many steps at the full size. Here the members
are asked once a pair, and the array's blocks once a member.

What is said. seat := Meaning.seatBy (Meaning.fLay layout num) X s throughout.
  copiesMiss cs arr ms N k n A   every member of ms that sits in N.group k with the number n has a
      shape at which the array A misses the pad (Law/LaidOffPad.lean: missB).
  offPad_of_miss   then OffPad cs arr ms N k n r p wherever laidAt A i c = some (r, p).
  padFreeC ... k k' a   the array that the label of entry a of sub-proof k names is there, and
      copiesMiss holds of it at k and at k', at the number of its message.
  **padFree_of_C**   under Meaning.laidThere X s layout = true and k < 25: padFreeC = true gives
      PadFree.
  padsFreeC, **padsFree_of_C**   at the 24 pairs.

What it does not give. One way alone. laidThere is a premise (a cheap road to it:
Goal/Meaning/LaidCovered.lean). Nothing on the other public conditions of words_ownQ. The full size
alone (the 24 pairs are literals). Nothing on soundness.

-/
import Johnson.P5J.WordsAtQ
import Johnson.Goal.Meaning.HidSeatsOf
import Johnson.Desc.Kinds.Law.LaidOffPad

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law.OffPad

open _root_.Meaning (ownerK ownerA nameOf labAt laidThere seatBy fLay seat_of_laidThere)
open OnBytes OnBytes.Road
open OnBytes.Model.Layer (matIx)
open OnBytes.Params (ReqArray ReqLayout)
open Cb.Pv.Tail (Size)
open VerifiableInference.Desc (laidAt arrayOf)
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.Sound (Mem seatOf numOf OffPad)
open P5J (PadFree PadsFree)

variable (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ) (ms : List Mem) (N : Numbers)

/-- Every copy of the message number n in segment k's group has a shape at which A misses the pad.
-/
def copiesMiss (k n : ℕ) (A : ReqArray) : Bool :=
  ms.all fun y => !(decide (seatOf y ∈ N.group k) && decide (numOf arr y = n)) ||
    missB cs (y.1.l.get y.2).1 A

theorem offPad_of_miss {k n : ℕ} {A : ReqArray} (h : copiesMiss cs arr ms N k n A = true)
    {i c r p : ℕ} (hl : laidAt A i c = some (r, p)) : OffPad cs arr ms N k n r p := by
  intro y hy hg hn
  have h1 := List.all_eq_true.1 h y hy
  rw [decide_eq_true hg, decide_eq_true hn] at h1
  exact padB_off (by simpa using h1) hl

variable (X : Model.Verify.Public) (s : ℕ → Size) (layout : ReqLayout) (num : ℕ → ℕ → ℕ)

/-- The cheap test at one pair. -/
def padFreeC (k k' a : ℕ) : Bool :=
  match arrayOf layout (ownerK (labAt X k a)) (nameOf (ownerA (labAt X k a))) with
  | none => false
  | some A =>
    copiesMiss cs arr ms N k (num (ownerK (labAt X k a)) A.message) A &&
      copiesMiss cs arr ms N k' (num (ownerK (labAt X k a)) A.message) A

/-- **A yes of the cheap test gives the condition at the pair.** -/
theorem padFree_of_C (T : laidThere X s layout = true) {k k' a : ℕ} (hk : k < 25)
    (h : padFreeC cs arr ms N X layout num k k' a = true) :
    PadFree cs arr ms N s (seatBy (fLay layout num) X s) k k' a := by
  intro ha i hi c hc
  obtain ⟨A, x, hA, -, -, hl, hs⟩ := seat_of_laidThere T num hk ⟨a, ha⟩ hi hc
  unfold padFreeC at h
  rw [hA, Bool.and_eq_true] at h
  rw [hs]
  exact ⟨offPad_of_miss cs arr ms N h.1 hl, offPad_of_miss cs arr ms N h.2 hl⟩

/-- The cheap test at the 24 pairs. -/
def padsFreeC : Bool :=
  ((List.range 12).all fun g =>
      (g == 0 || padFreeC cs arr ms N X layout num (2 * g) (2 * (g - 1)) (matIx X.y).iXI) &&
      padFreeC cs arr ms N X layout num (2 * g + 1) (2 * g) ((Hd.shapeA X g).cf.NAs + 3)) &&
    padFreeC cs arr ms N X layout num 24 22 (X.hS.NHf + 3)

/-- **A yes of the cheap test gives PadsFree.** -/
theorem padsFree_of_C (T : laidThere X s layout = true)
    (h : padsFreeC cs arr ms N X layout num = true) :
    PadsFree cs arr ms N s (seatBy (fLay layout num) X s) X := by
  unfold padsFreeC at h
  rw [Bool.and_eq_true, List.all_eq_true] at h
  refine ⟨fun g h0 hg => ?_, fun g hg => ?_,
    padFree_of_C cs arr ms N X s layout num T (by norm_num) h.2⟩
  · have k := h.1 g (List.mem_range.2 hg)
    rw [Bool.and_eq_true, Bool.or_eq_true] at k
    rcases k.1 with e | e
    · exact absurd (eq_of_beq e) (Nat.pos_iff_ne_zero.1 h0)
    · exact padFree_of_C cs arr ms N X s layout num T (by omega) e
  · have k := h.1 g (List.mem_range.2 hg)
    rw [Bool.and_eq_true] at k
    exact padFree_of_C cs arr ms N X s layout num T (by omega) k.2

end VerifiableInference.Desc.Kinds.Head.Law.OffPad

#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.offPad_of_miss
#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.padFree_of_C
#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.padsFree_of_C
