-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/AtText/PadPlace.lean: where the link prover's algorithm puts the pad that the
link proof's own OOD sample at the front reads, with one negative test.
Terms: Johnson/LinkSim/Spec.lean; for the prover's algorithm, Johnson/LinkSim/AtText/Defs.lean.

What this file proves. A member's message (membMsg, Johnson/Prover/Link/FrontMsg.lean) holds the
fold's coefficients at their entries and the other values fr at every other entry. The pad's entry
is the last entry of the last row (Sz.padJ, OnBytes/Slice/LinkAt.lean). PadRoom S says that the
sizes S leave that entry free: the folded table row's message part and its tail part, as they are
placed in a member's rows, both end before the last entry.
  membMsg_pad    if PadRoom S, a member's message at the pad's entry is the value of fr there.
  lMem_split     if PadRoom S, the two members' messages of the prover's algorithm (lMem,
                 Johnson/Prover/Link/LinkAll.lean) are those with both pads 0, plus each pad's
                 value C.pad a at the pad's entry.
  lMem_zero      if PadRoom S, then at the data 0 (zeroIn X) the two members' messages are C.pad a
                 at the pad's entry and 0 everywhere else.
  pad_lost       a negative test. Suppose the tail ends exactly at the last entry
                 (t0 + T.r = R * C.l), with T.l ≤ t0 and 0 < T.r. Then a member's message at the
                 pad's entry does not depend on the other values fr. Since an entry of the
                 message reads fr at that same entry alone, the pad's coin then enters the
                 message nowhere (by inspection of membMsg and lMem, not proved). The library's
                 own bound on the sizes (Sz.fitT, OnBytes/Slice/LinkAt.lean) allows such sizes.

How it fits. FrontStep.lean and ShortTail.lean, in this folder, use lMem_split and lMem_zero;
MustFail.lean uses lMem_split. ShortTail.lean and LinkShift.lean obtain PadRoom from the public
premises on sizes (Sizes.pad, Johnson/LinkSim/AtText/SpecShift.lean) by padRoom_of.

Other names (namespace OnBytes.LinkSim.AtText).
  padRoom_of     PadRoom from the two bounds written as "at most R * C.l - 1", the form of
                 Sizes.pad.
  padJ_entry     the pad's entry is number R * C.l - 1 among a member's entries: the last.
  membMsg_single if PadRoom S, with fold coefficients 0 and x at the pad's entry alone, the
                 message is x at that entry and 0 elsewhere.

Limits.
- That the library's full-size parameter set (dsFull; its sizes: frS) meets PadRoom is not proved
  here.

Notes.
- At that parameter set the public premises on sizes, Sizes.pad among them, are proved elsewhere
  (fr_sizes, Johnson/LinkSim/AtText/SeamAtFull3.lean), and padRoom_of turns Sizes.pad into PadRoom.
Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.AtText.Front

set_option autoImplicit false

noncomputable section

namespace OnBytes.LinkSim.AtText
open OnBytes OnBytes.Slice Cb
open Johnson.Prover.Link
open _root_.Desc.K15 (P15)

/-- The sizes leave the pad's entry free: the folded row's message part and its tail part both end
before the last entry of a member's rows. -/
structure PadRoom (S : Sz) : Prop where
  msg : S.P.T.l < S.P.R * S.P.C.l
  tail : S.P.t0 + S.P.T.r < S.P.R * S.P.C.l

theorem padRoom_of (S : Sz)
    (h : S.P.T.l ≤ S.P.R * S.P.C.l - 1 ∧ S.P.t0 + S.P.T.r ≤ S.P.R * S.P.C.l - 1) : PadRoom S := by
  have hp : 0 < S.P.R * S.P.C.l := Nat.mul_pos S.hR S.hl
  exact ⟨by omega, by omega⟩

/-- The number of the pad's entry among a member's entries: the last. -/
theorem padJ_entry (S : Sz) :
    (S.P.R - 1) * S.P.C.l + (S.P.C.l - 1) = S.P.R * S.P.C.l - 1 := by
  have h1 := S.hR
  have h2 := S.hl
  obtain ⟨r, hr⟩ : ∃ r, S.P.R = r + 1 := ⟨S.P.R - 1, by omega⟩
  rw [hr, Nat.add_sub_cancel, Nat.succ_mul]
  omega

theorem membMsg_pad (S : Sz) (h : PadRoom S) (u : S.Co → GE) (fr : S.MJ → GE) :
    membMsg S u fr S.padJ = fr S.padJ := by
  have e := padJ_entry S
  have h1 := h.msg
  have h2 := h.tail
  show membMsg S u fr (.inl (⟨S.P.R - 1, _⟩, ⟨S.P.C.l - 1, _⟩)) = _
  simp only [membMsg]
  rw [dif_neg (by omega), dif_neg (by omega)]
  rfl

theorem membMsg_single (S : Sz) (h : PadRoom S) (x : GE) :
    membMsg S 0 (fun j => if j = S.padJ then x else 0) = Pi.single S.padJ x := by
  funext j
  rw [Pi.single_apply]
  by_cases hj : j = S.padJ
  · rw [hj, membMsg_pad S h, if_pos rfl]
  · rw [if_neg hj]
    rcases j with y | y
    · simp only [membMsg]
      split_ifs <;> rfl
    · exact y.1.elim

section Text
variable (S : Sz) (X : LIn S) (C : LCoins) (D : ℕ → Fmt.Drawn)

/-- If PadRoom S, the two members' messages are those with both pads 0, plus each pad's value at
the pad's entry. -/
theorem lMem_split (h : PadRoom S) :
    lMem S X C D = frontMem S (lGam S D) X.M₀ X.M₁ 0 + fun a => Pi.single S.padJ (C.pad a) := by
  have e := frontMem_add S (lGam S D) X.M₀ 0 X.M₁ 0 0 fun a j => if j = S.padJ then C.pad a else 0
  rw [add_zero, add_zero, zero_add] at e
  unfold lMem
  rw [e]
  congr 1
  funext a
  show membMsg S (foldAll (lGam S D) (if a then (0 : (Fin S.P.v → Bool) → S.Co → GE) else 0)) _ = _
  have z : foldAll (lGam S D) (if a then (0 : (Fin S.P.v → Bool) → S.Co → GE) else 0) = 0 := by
    rw [ite_self]
    exact foldAll_zero0 _
  rw [z]
  exact membMsg_single S h (C.pad a)

theorem lMem_zero (h : PadRoom S) :
    lMem S (zeroIn X) C D = fun a => Pi.single S.padJ (C.pad a) := by
  rw [lMem_split S (zeroIn X) C D h]
  have z : frontMem S (lGam S D) (zeroIn X).M₀ (zeroIn X).M₁ 0 = 0 := by
    have e := frontMem_add S (lGam S D) (0 : (Fin S.P.v → Bool) → S.Co → GE) 0 0 0 0 0
    rw [add_zero, add_zero] at e
    exact left_eq_add.mp e
  rw [z, zero_add]

end Text

/-- A negative test: if the tail ends exactly at the last entry, a member's message at the pad's
entry does not depend on the other values fr. -/
theorem pad_lost (S : Sz) (hM : S.P.T.l ≤ S.P.t0) (hr : 0 < S.P.T.r)
    (he : S.P.t0 + S.P.T.r = S.P.R * S.P.C.l) (u : S.Co → GE) (fr fr' : S.MJ → GE) :
    membMsg S u fr S.padJ = membMsg S u fr' S.padJ := by
  have e := padJ_entry S
  show membMsg S u fr (.inl (⟨S.P.R - 1, _⟩, ⟨S.P.C.l - 1, _⟩)) =
    membMsg S u fr' (.inl (⟨S.P.R - 1, _⟩, ⟨S.P.C.l - 1, _⟩))
  simp only [membMsg]
  rw [dif_neg (by omega), dif_pos (by omega), dif_neg (by omega), dif_pos (by omega)]

end OnBytes.LinkSim.AtText

#print axioms OnBytes.LinkSim.AtText.membMsg_pad
#print axioms OnBytes.LinkSim.AtText.lMem_split
#print axioms OnBytes.LinkSim.AtText.lMem_zero
#print axioms OnBytes.LinkSim.AtText.pad_lost
