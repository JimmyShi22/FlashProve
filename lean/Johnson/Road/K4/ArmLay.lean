-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/ArmLay.lean: K4's FILES' HALF OF THE EXCHANGE AT A LAYERS' SEGMENT's SECOND
SENDING, IN THE ONE FORM IN WHICH IT IS ASKED OF EVERY KIND AT THE TABLE OF JOINTS (ArmCell,
Johnson/Desc/Sound/StatedCell.lean), at K4's arm uLay tl M (Johnson/Road/K4/FillStated.lean) of the
one stated function uBySort (Johnson/Desc/Sound/StatedAll.lean); and K4's own sentence on the letter
St (StatedAt) out of the table of joints' (StatedIs).

  `statedAt_of_is`: StatedIs St (uLay tl M) s gives StatedAt St M s tl o c n D at the name c of the
    reads' array, at every n and D.
  `statedAt_bySort`: so at St := Stated.of (uBySort uL uA uH), where the layers' arm at the open
    link's number is uLay tl M.
  `armCell_lay`: ArmCell at u := uLay tl M: at each entry that a form of the run names, the
    committed cell, read behind the sending, is u at the verifier's state in front: out of the
    approximate range proof's tie (entryTrue_of_tie, Johnson/Road/K4/CellOfTie.lean).
No new argument.
Limits. PREMISES of armCell_lay, none paid here: the verifier's state stands in a layers' link and
holds what K4 has heard (hs, ho) · the part a has that link's context (hA) · hE: EACH ENTRY THAT A
FORM OF THE READER's ANSWER NAMES has the reads' number, row 0, a place below n and an owner among
o.funs (for K4's two runs: Johnson/Road/K4/Reads/RowZero.lean and Johnson/Road/K4/OwnedForms.lean,
under premises on what the lookup has heard, once the reader's answer is known to be the run's list)
· T: the tie at the closed structure tl' and the table of cells A · hfun, htab, hu3: what the step
that closes the list leaves (closing_turns, Johnson/Road/K4/ClosedTurns.lean, at tl := the place's
parameter) with "the public parameters' number of the reads is K4's" · hAc: below n, A's row 0 of
the reads is the data's cell behind the sending · hM: inside the ranges the matrices M are cellA at
A. Met through Lean at no member. K04_law, the law of K4's sub-protocol itself, IS NOT PROVED: K4's
row spends formsT; this serves the row of the second sending. Nothing on soundness.


-/
import Johnson.Road.K4.CellOfTie
import Johnson.Desc.Sound.StatedCell

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace OnBytes.Road.K4

open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Own)
open OnBytes.Tie.Pv.Tail.Port (u3Of)
open VerifiableInference.Desc.First (S LayOwn)
open VerifiableInference.Desc.First.K8 (TieOf)
open VerifiableInference.Desc.K9 (Readers)
open VerifiableInference.Desc.K9L (Bound)
open VerifiableInference.Desc.Sound (GQ MsgQ Stated second dataQ UFn StatedIs ArmCell uBySort linkNo
  stated_lay)
open Meaning.Reads (cellA)

/-- K4's sentence on St (StatedAt) out of the table of joints' (StatedIs), under hs ho hc h2. -/
theorem statedAt_of_is {St : Stated} {tl : HTailF2} {M : S → Bound GQ → Mats GQ} {s : S}
    {b : LayOwn} {o : Own} {c : ℕ × String} (I : StatedIs St (uLay tl M) s) (hs : s.here = .lay b)
    (ho : b.own = some o) (hc : b.L.arrayOf[o.v.iU3]? = some c) (h2 : second s c = true) (n : ℕ)
    (D : Bound GQ) : StatedAt St M s tl o c n D :=
  ⟨fun i _ => by rw [I.cell D c 0 i h2, uLay_cell tl M hs ho hc D 0 i], I.mask D⟩

/-- At the one stated function, where the layers' arm at the open link's number is uLay tl M. -/
theorem statedAt_bySort (uL uA uH : ℕ → UFn) {tl : HTailF2} {M : S → Bound GQ → Mats GQ} {s : S}
    {b : LayOwn} {o : Own} {c : ℕ × String} (hu : uL (linkNo s) = uLay tl M)
    (hs : s.here = .lay b) (ho : b.own = some o) (hc : b.L.arrayOf[o.v.iU3]? = some c)
    (h2 : second s c = true) (n : ℕ) (D : Bound GQ) :
    StatedAt (Stated.of (uBySort uL uA uH)) M s tl o c n D :=
  statedAt_of_is (hu ▸ stated_lay uL uA uH s b hs) hs ho hc h2 n D

/-- **K4's FILES' HALF OF THE EXCHANGE**, under hs ho hA hE T hfun htab hu3 hAc hM. -/
theorem armCell_lay (Rd : Readers) (own own' : List (ℕ × ℕ)) (piece : ℕ) (run : String) {s : S}
    (a b : VerifiableInference.Desc.K9.Part) (rd : ℕ × ℕ → MsgQ) {tl tl' : HTailF2}
    {M : S → Bound GQ → Mats GQ} {b₀ : LayOwn} {o : Own} {n : ℕ} {A : ℕ → ℕ → ℕ → Cb.Gl.E}
    (hs : s.here = .lay b₀) (ho : b₀.own = some o) (hA : a.L = b₀.L)
    (hE : ∀ R, Rd.forms piece run s = some R → ∀ f ∈ R.forms, ∀ x ∈ f.ents.toList,
      x.tree = o.v.iU3 ∧ x.row = 0 ∧ x.idx < n ∧
        ∃ y : HFun × ℕ × ℕ, y.1 ∈ o.funs ∧ tl.tabAt y.1 y.2.1 y.2.2 = some x.idx)
    (T : TieOf tl' A) (hfun : tl'.funs = o.funs)
    (htab : ∀ Fn c sg, tl.tabAt Fn c sg = tl'.tabAt Fn c sg) (hu3 : u3Of tl' = o.v.iU3)
    (hAc : ∀ c, b₀.L.arrayOf[o.v.iU3]? = some c → ∀ i, i < n →
      A o.v.iU3 0 i = (dataQ own' b rd).cell c.1 c.2 0 i)
    (hM : InRange tl' (M s (dataQ own a rd)) (cellA tl' A)) :
    ArmCell Rd own own' piece run s a b rd (uLay tl M) := by
  intro R hR f hf x hx c hc _
  obtain ⟨e1, e2, e3, hown⟩ := hE R hR f hf x hx
  rw [e1, hA] at hc
  rw [e2, uLay_cell tl M hs ho hc _ 0 x.idx, entryTrue_of_tie T hfun htab hM hown, hu3,
    hAc c hc x.idx e3]

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.statedAt_of_is
#print axioms OnBytes.Road.K4.statedAt_bySort
#print axioms OnBytes.Road.K4.armCell_lay
