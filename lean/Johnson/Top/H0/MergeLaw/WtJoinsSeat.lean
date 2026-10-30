-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/WtJoinsSeat.lean: the lemma that joins the two sentences for "weights" at
the output head's segment (`wtK6_of_wtP1`, Johnson/Desc/Kinds/Law/WtJointAt.lean), WITHOUT ITS
PREMISE hmaskOf: at a state that meets `WaK6` and holds the mask row's seat (`MaskSeatAt`,
Johnson/Desc/Kinds/Law/MaskRowsOne.lean). Two definitions, theorems with their proofs. ITS NAMES
STAND IN THE NAMESPACE OF THE FILES THAT IT CALLS (VerifiableInference.Desc.Kinds.Head.Law.AtTable),
not in that of its folder: so that the statement reads in `wtK6_of_wtP1`'s own words, with that
file's short names.

Why. `wtK6_of_wtP1` takes as a premise that the two readers of segment 24's mask row agree, below
the merge's number of slots, at EVERY state that meets `WaK6`. That is not shown, and we hold it
false: `WaK6` reads neither the frame, nor the book of trees, nor the messages' shapes, so the mask
row's seat is free under it; no counterexample is typed. What can be had is the equation at the one
state in hand, where that state holds the seat (`maskRows_one`); and `wtK6_of_wtP1`'s own proof
spends the premise at the state and the witness in hand alone.

How. `wtK6_of_wtP1` IS CALLED, not proved again. Its reader of the mask row, maskOf, is a parameter,
and the sentence `wtP1` reads it at the state and the witness in hand alone. So it is called at a
reader made for the purpose (`maskMix`): below the merge's number of slots the other side's reading,
which does not look at the state; from there on the merge's own reader. At that reader hmaskOf holds
at every state by definition; and at a state that holds the seat it is, as a function of the slot,
the merge's own reader (`maskMix_is`), so that the sentence in hand is the sentence at it
(`wtP1_same`).

Main names:
  `wtP1_same`: `wtP1` at two readers of the mask row that agree at the state and the witness in
    hand.
  `maskMix`, `maskMix_is`: the reader made for the purpose; at a state that holds the seat it is
    `Sound.maskRowAt`.
  `WaSeat`: the condition on the state with its eighth clause: `WaK6 W V' s ∧ MaskSeatAt arr N n rb
    s`.
  `wtK6_of_wtP1_seat`: THE JOINING LEMMA under `WaSeat`, at maskOf := `Sound.maskRowAt cs arr msR N
    24`. In hmaskOf's place: `namedOnce arr N 24 n = true` and Pm.nMsg ≤ W.H.ns, both closed. Every
    other premise is `wtK6_of_wtP1`'s own, in its own words.

Limits. `wtK6_of_wtP1`'s, but for hmaskOf. That `WaSeat` holds at any state is not shown here: its
first half is for the authors of `WaK6` to show at the reached states; its second half follows from
an accept of `maskAtB` (MaskJoinsNamed.lean). No example. The reference sizes alone. Nothing on
soundness.

-/
import Johnson.Desc.Kinds.Law.WtJointAt
import Johnson.Desc.Kinds.Law.MaskRowsOne

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable

open OnBytes.Params (ReqLayout)
open Inst.Model (ppref)
open Inst.Model.Layout (kRef)
open VerifiableInference.OnPublicFiles.Flat (GE)
open VerifiableInference.Desc.First (S Numbers)
open VerifiableInference.Desc.First.FillP1 (wtP1 wtAt)
open VerifiableInference.Desc.Sound (Mem MsgT namedOnce)
open Johnson.Desc.First.ForkMerge (HeadMergeP)

/-- The sentence for "weights" reads the mask row's reader at the state and the witness in hand
alone. -/
theorem wtP1_same {P W : Type} (Pm : HeadMergeP) (ni : ℕ) (cellOf : W → ℕ → ℕ → GE)
    (m m' : P × S → W → ℕ → GE) (a : P × S) (y : Strs) (w : W) (e : m a w = m' a w)
    (h : wtP1 Pm ni cellOf m a y w) : wtP1 Pm ni cellOf m' a y w := by
  obtain ⟨s₀, p3, lkW, hl, hn, ui, sv, hsv, c, hc, hr, hW⟩ := h
  exact ⟨s₀, p3, lkW, hl, hn, ui, sv, hsv, c, hc, hr, e ▸ hW⟩

section
variable {rows cols : ℕ} {P Tok : Type} (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ) (msR : List Mem)
  (N : Numbers) (W : OnBytes.Model.Verify.Public) (lay6 : ReqLayout) (num : ℕ → ℕ → ℕ) (n rb : ℕ)

/-- A reader of the mask row made for the call: below m the other side's reading, which does not
look at the state; from m on the merge's own reader. -/
def maskMix (m : ℕ) : P × S → Wit (Fin rows → Fin cols → GE) Tok MsgT → ℕ → K :=
  fun a w j =>
    if j < m then
      rd ((compCut cs arr msR N (Meaning.sizesOf W) (seatLay W lay6 num) W (plAt n rb) w).2 j)
    else Sound.maskRowAt cs arr msR N 24 a w j

/-- At a state that holds the mask row's seat it is the merge's own reader. -/
theorem maskMix_is (m : ℕ) (h1 : namedOnce arr N 24 n = true) (hns : m ≤ W.H.ns) (a : P × S)
    (w : Wit (Fin rows → Fin cols → GE) Tok MsgT) (hs : MaskSeatAt arr N n rb a.2) :
    Sound.maskRowAt cs arr msR N 24 a w = maskMix cs arr msR N W lay6 num n rb m a w := by
  funext j
  unfold maskMix
  by_cases hj : j < m
  · rw [if_pos hj]
    exact (maskRows_one cs arr msR N _ _ W n rb h1 a w hs j (Nat.lt_of_lt_of_le hj hns)).symm
  · rw [if_neg hj]

/-- **The condition on the state in front of the merge, with its eighth clause.** -/
def WaSeat (V' : ℕ) (s : S) : Prop := WaK6 W V' s ∧ MaskSeatAt arr N n rb s

/-- **THE JOINING LEMMA, WITHOUT hmaskOf.** -/
theorem wtK6_of_wtP1_seat (hplan : (parOf W.hS (workOf W)).ok = true) (hTT : W.T = W.hS.T)
    (V' : ℕ) (hr : rows ≤ Inst.Model.Layout.hRef) (hc : cols ≤ 2 ^ kRef) (Pm : HeadMergeP)
    (hlay : Pm.lay = W.layers.wsLay) (ni : ℕ)
    (cellOf : Wit (Fin rows → Fin cols → GE) Tok MsgT → ℕ → ℕ → K)
    (hcellOf : ∀ w r c, cellOf w r c =
      if h : r < rows ∧ c < cols then w.cells ⟨r, h.1⟩ ⟨c, h.2⟩ else 0)
    (h1 : namedOnce arr N 24 n = true) (hns : Pm.nMsg ≤ W.H.ns)
    {sh : OnBytes.Model.WsShape} (Z : OnBytes.Road.SizedW sh ppref)
    (hl : OnBytes.Model.wsLayOf sh true kRef = .ok W.layers.wsLay) (hlam : W.H.lamS = 13)
    (hV2 : W.hS.V = 202048) (hd5 : W.hS.d = 5120) (a : P × S) (y : Strs)
    (w : Wit (Fin rows → Fin cols → GE) Tok MsgT) (hWa : WaSeat arr N W n rb V' a.2)
    (hw : wtP1 Pm ni cellOf (Sound.maskRowAt cs arr msR N 24) a y w) :
    wtK6 cs arr msR N W lay6 num n rb 24 a y w :=
  wtK6_of_wtP1 cs arr msR N W lay6 num n rb hplan hTT V' hr hc Pm hlay ni cellOf
    (maskMix cs arr msR N W lay6 num n rb Pm.nMsg) hcellOf
    (fun _ _ _ j hj => by unfold maskMix; rw [if_pos hj]) Z hl hlam hV2 hd5 a y w hWa.1
    (wtP1_same Pm ni cellOf _ _ a y w
      (maskMix_is cs arr msR N W lay6 num n rb Pm.nMsg h1 hns a w hWa.2) hw)

end

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.wtP1_same
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.maskMix_is
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.wtK6_of_wtP1_seat
