-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Total/DigitsFormsNew.lean: the kind "lookup" (K3). Conditional,
under the library's hypothesis `P5J.AtMgA`: the one public test "formsIn" that is new behind the
lookup on the digits holds behind its acceptance: formsIn l (7 + the sort's shift) "objects": the
lookup's own runs at the digits' piece. At every sort of link. Said of two states of the verifier.
Theorems.

Terms. Honest/K3/GLOSSARY.md. In this file: a test "formsIn" is the Boolean test of a public item
`Pub.formsIn l pc nm` (Johnson/Desc/First/Borders.lean), for the run of claims named nm at piece pc
of link l; a kept test is one of `keptDigits`, the new one is `newDigits`
(Johnson/Desc/Sound/MgAt/K3DigitsSorted.lean). The stated sub-protocol at the digits' address is
`k3Const … l true` (Johnson/Desc/First/Look/K3Base.lean). The tests in front are the list
`frontDig mgMore l` (K3DigitsSorted.lean). The book-keeping's first test is `shapeAt`
(Borders.lean). The book-keeping's fourth test is `bookAt` (Borders.lean). In the statements two
local notations stand: PS for the places of all the first chain's sub-protocols, in the flat list's
order, at the full size's row of links (`flatPlacesOf linksFull true`,
Johnson/Desc/First/Driver/Chain.lean); 𝔐 for `AtMg.𝔇 (AtMgA.toAtMg h) (AtMgA.𝔇 h)`: through it the
hypothesis `h` enters them.

What is shown.
  `fits_dig_at`: in front of the digits the library's test `sFvFitsB`
    (Johnson/Desc/First/Look/MergeSlotFits.lean) accepts: the slot of the merge's end value lies
    below the ledger's next slot, or the merge has no slot.
  `mask_behind_dig`: behind the acceptance the mask row's message has a seat among the link's group.
  `objectsNew_dig_at`: the test: the library's `objIn_dig_fits`
    (Johnson/Desc/Sound/MgAt/K3DigitsObjInFits.lean), called.
The statements speak of no thread, piece, transcript or string. The file is the fellow of
Honest/K3/Law/Total/DigitsFormsFour.lean and Honest/K3/Law/Total/DigitsFormsOwn.lean.

Hypotheses that remain, in the last theorem.
  `h`: the library's hypothesis `P5J.AtMgA` (Johnson/P5J/MgAtAll.lean).
  `hb`, `hOk`, `hd`: b' is the stated sub-protocol at the digits' address; it passes its test on the
    plan; its decision accepts from s to s'.
  `hfront`: the public tests that are open or tied in front hold at s.
  `hl`, `hsub`: the link is below 25; its sort in the written full list.
  `hshape`, `hbook`: the book-keeping's first and fourth tests hold in front.
  `hr`, `hf`: s is reached by the wrapped sub-protocols' steps (`Reach`,
    Johnson/Top/H0/Walk/Reach.lean); it bears no mark (`s.failed = none`).
  `hlook`, `T`, `hF`: (in `mask_behind_dig`) x is the lookup's place; `SameBut s s'`
    (Johnson/Desc/First/Look/K3CallsTurns.lean); a ledger is open at s.

Follows. The proof of `mask_behind_dig` follows the library's `hmask_dig_lean`
(Johnson/Desc/Sound/MgAt/K3DigitsMaskLean.lean) line for line from the book's test on, over
`maskSeat_at_dig` (there; "on one state"), and `P5J.k03_frame` (Johnson/P5J/K03FoldAt.lean) for
three of its six facts.

How the proof goes. `fits_dig_at`: at a layers' link from "reached" (`mergeBelow_reach`,
Johnson/Road/K4/MergeBelowReached.lean; `sFvFits_of_below`, Johnson/P5J/K03MergeAt.lean: as the
library's own `k03_sFvFits_lay`, Johnson/P5J/K03DigPartsAt.lean); at an attention link by the text
of `mergeOf` (Johnson/Desc/First/Batch/AtS.lean) in that case; at the head's from "reached"
(`noMerge_345`, Johnson/K11R/NoMergeAt345.lean). `mask_behind_dig`: all six facts come of four
fields of the library's `FoldFacts` (Johnson/Desc/First/FoldFacts.lean): liveShape, liveGroups,
seatsCarried, and three clauses of frameIs; taken at "reached" itself (`atMgR_of_head`,
Johnson/P5J/StartAtHead.lean, which is general in that letter), not at the "reached" of `P5J.AtMgA`,
which asks more beside it. The closed test is `AtMg.hTests_digits`
(Johnson/P2LawR/MasksAtHead.lean). The terms of `objIn_dig_fits` are those that the library's
`P5J.k03_digForms` (Johnson/P5J/K03DigFormsAt.lean) uses.

Users. `forms_dig_at` (Honest/K3/Law/Total/MadeOwedDigits.lean) calls `objectsNew_dig_at`.

Options. `maxRecDepth` is raised to 100000 for the file; `maxHeartbeats` to 4000000 in front of two
theorems; `quotPrecheck` is off at one local notation. These raise limits on Lean's own work or
switch off a check on a notation's names: none loosens a check on a proof.

Limits. All statements are implications. No instance of these hypotheses is exhibited in this file.
At the full size alone.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Total.DigitsFormsFour
import Johnson.Desc.Sound.MgAt.K3DigitsObjInFits
import Johnson.Desc.Sound.MgAt.K3DigitsMaskLean
import Johnson.Desc.Sound.MgAt.K3DigitsOwed
import Johnson.Desc.First.Look.K3DigitsStep
import Johnson.P5J.K03DigFormsAt
import Johnson.P5J.StartAtHead
import Johnson.K11R.NoMergeAt345

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Law.Total
open OnBytes OnBytes.Model
open OnBytes.Maker (WholeD)
open VerifiableInference VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart shift standOf bookAt)
open VerifiableInference.Desc.K9 (segAt? maskSeat mergeOf)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)
open P5J

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)

local notation "PS" => Desc.First.flatPlacesOf linksFull true
set_option quotPrecheck false in
local notation "𝔐" => AtMg.𝔇 (AtMgA.toAtMg h) (AtMgA.𝔇 h)

include h in
/-- **In front of the digits the test on the merge's slot accepts.** Conditional on `P5J.AtMgA`, the
book-keeping's first Boolean test in front, and s being reached. No instance of these hypotheses is
exhibited in this file. -/
theorem fits_dig_at {l : ℕ} (hl : l < 25) {sub : ModelPart} (hsub : linksFull[l]? = some sub) {s : TS}
    (z : ProofFile.InstPub) (hshape : Desc.First.shapeAt linksFull PS[k3K l true]? s = true)
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) (k3K l true) (z, s)) :
    Desc.K3.sFvFitsB s = true := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hStand := dig_stand hl hsub hshape
  cases sub with
  | layers =>
    have he : l % 2 = 0 ∧ l < 24 := by
      rcases Nat.lt_or_ge l 24 with h24 | h24
      · rcases Nat.mod_two_eq_zero_or_one l with he | ho
        · exact ⟨he, h24⟩
        · exact absurd (hsub.symm.trans (links_att l h24 ho)) (by simp)
      · obtain rfl : l = 24 := by omega
        exact absurd hsub (by decide)
    obtain ⟨g, rfl⟩ : ∃ g, l = 2 * g := ⟨l / 2, by omega⟩
    have hg : g < 12 := by omega
    have hr' := reach_raw hr
    rw [digits_number g hg] at hr'
    exact sFvFits_of_below
      (OnBytes.Road.K4.mergeBelow_reach h.scope h.reads O h.laid.planOk hg (by omega : 3 < 4) hr')
  | attention =>
    obtain ⟨w, hatt⟩ := VerifiableInference.OnPublicFiles.here_att_of_stand hStand
    refine Desc.K3.sFvFits_none ?_
    unfold mergeOf
    rw [hatt]
  | head =>
    obtain rfl : l = 24 := (P5J.k03_sorts_full l hl).2 hsub
    exact Desc.K3.sFvFits_none
      (P1K11.noMerge_345 h.scope h.reads O h.laid.planOk (z := z) (s := s) hr)

set_option maxHeartbeats 4000000 in
/-- **Behind the acceptance the mask row's message has a seat among the link's group.** Conditional
on `P5J.AtMgA`; the place; `SameBut` between the two states; s being reached, without a mark, with
an open ledger; the book's test in front. No instance of these hypotheses is exhibited in this file.
-/
theorem mask_behind_dig {l : ℕ} (hl : l < 25) {x : Desc.First.Look.Place}
    (hlook : lookAt (At.X Zp) l true = some x) {s s' : TS} (T : SameBut s s') (z : ProofFile.InstPub)
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) (k3K l true) (z, s))
    (hf : s.failed = none) {F : Fork} (hF : s.fork? = some F)
    (hbook : bookAt (𝔐).N PS[k3K l true]? s = true) :
    ∀ c, segAt? s' = some c → (maskSeat ((𝔐).N.group l) c).isSome = true := by
  obtain ⟨L, R⟩ := atMgR_of_head h (Str := Unit)
    (fun k a => Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) k a.1) (fun _ _ ha => ha)
  have Fo := R.fold
  have elk : x.link = l := lookAt_link hlook
  have hTests := h.toAtMg.hTests_digits R.listed hl
  obtain ⟨L', hL⟩ := link_some_of_fork hF
  have Tf := Fo.frameIs (k3K l true) ((z, s), ()) (IM.k3Place l true) l L' hr hf
    (K3Lot.k03_at_full l hl true) rfl hL
  have e : s.live = L'.check := by
    unfold Desc.First.S.live
    rw [hL]
  obtain ⟨m3, hp⟩ := k3DigMoment_at hl
  obtain ⟨-, hown, -, hrest⟩ := Tf
  have hbook' : bookAt (𝔐).N PS[k3K l true + 1]? s' = true :=
    Desc.First.bookAt_step (𝔐).N PS (At.told cF) (k03_book_at Zp cF) (k3K l true)
      (List.getElem?_eq_some_iff.1 (K3Lot.k03_at_full l hl true)).1
      (k03_tells_at h.toAtMg l hl true) s s' T.book (by rw [T.st]) hbook
  have eLive : s'.live = s.live := by
    unfold Desc.First.S.live
    rw [T.link]
    cases s.link? with
    | none => exact T.check
    | some C => rfl
  refine maskSeat_at_dig x (D := (𝔐).sent) (nos := (At.foldD Zp cF L).ownAt l 3)
    ((𝔐).l3.seat x.link true) ?_ ?_ ?_ ?_ ?_ hbook' ?_ (by rw [elk]; exact hTests)
  · rw [eLive]
    exact Fo.liveShape (k3K l true) ((z, s), ()) hr hf
  · rw [eLive]
    exact Fo.liveGroups (k3K l true) ((z, s), ()) hr hf
  · rw [eLive, e, elk]
    exact (hrest hp).1
  · rw [eLive, e]
    exact (hrest hp).2
  · rw [eLive, e, hown]
    exact congrArg _ m3
  · have h0 := Fo.seatsCarried (k3K l true) ((z, s), ()) hr hf
    unfold Desc.K12.Door.atFirstSeats at h0 ⊢
    rw [T.book]
    exact h0

set_option maxHeartbeats 4000000 in
/-- **The new "objects" behind the acceptance.** Conditional on `P5J.AtMgA`; the acceptance of the
stated sub-protocol's decision; the public tests and the book-keeping's first and fourth Boolean
tests in front; s being reached and without a mark. No instance of these hypotheses is exhibited in
this file. -/
theorem objectsNew_dig_at {l : ℕ} (hl : l < 25) {sub : ModelPart} (hsub : linksFull[l]? = some sub)
    {b' : Block TS ProofFile.Cl}
    (hb : k3Const (At.X Zp) Zp.first.codes Zp.first.shape l true = some b')
    (hOk : b'.planOk = true) {s s' : TS} {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))}
    (hd : b'.decide s rs gs = .ok s') (z : ProofFile.InstPub)
    (hfront : ∀ p ∈ frontDig mgMore l, (mgAll (𝔐) mgBase).pub p (z, s) = true)
    (hshape : Desc.First.shapeAt linksFull PS[k3K l true]? s = true)
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) (k3K l true) (z, s))
    (hf : s.failed = none) (hbook : bookAt (𝔐).N PS[k3K l true]? s = true) :
    (mgAll (𝔐) mgBase).pub (.formsIn l (7 + shift sub) "objects") (z, s') = true := by
  obtain ⟨hpc, x, hlook, hIn, F, hF, hSz⟩ := dig_front h hl hsub hb z hfront
  obtain ⟨lk, hlk, -, -, hO6, hG6⟩ := P5J.k03_finds_dig h hl hsub
  obtain ⟨hs, hsh⟩ : ∃ hs,
      (Desc.First.Look.P.ofPlace (Params.settingOf (At.X Zp).P.frame) true x).shape = some hs := by
    cases e : (Desc.First.Look.P.ofPlace (Params.settingOf (At.X Zp).P.frame) true x).shape with
    | none =>
      unfold Desc.K3.k3OnIn at hIn
      rw [e] at hIn
      cases hIn
    | some hs => exact ⟨hs, rfl⟩
  have T := (k3_digits_step_turns K3Lot.ofForm (K3Lot.readersAt (At.X Zp)) (At.X Zp)
    Zp.first.codes Zp.first.shape (IM.k3Place l true) b' hb hOk l rfl hpc hlook hsh s s' rs gs
    hd).1
  exact objIn_dig_fits (𝔐) mgBase (Desc.K9.holesAt (At.X Zp) (headLink (At.X Zp)) l lk) lk
    (K3Lot.readersAt (At.X Zp)) Zp.first.codes Zp.first.shape (IM.k3Place l true) b' K3Lot.ofForm hb
    hOk rfl hpc rfl hsub (rd_holesAt (𝔐) hlk) atS2_ofForm z s s' rs gs hd hF hSz
    (k := 7 + shift sub) (B₀ := 6 + shift sub) (by cases sub <;> rfl) passR k03_hpass k03_hsame
    ⟨_, _, hO6, fun _ _ _ hr _ => hr⟩ ⟨_, _, hG6, fun _ _ _ hr _ => hr⟩
    (mask_behind_dig h hl hlook T z hr hf hF hbook) (fits_dig_at h hl hsub z hshape hr)

end ProofFile.Honest.K3.Law.Total

#print axioms ProofFile.Honest.K3.Law.Total.fits_dig_at
#print axioms ProofFile.Honest.K3.Law.Total.mask_behind_dig
#print axioms ProofFile.Honest.K3.Law.Total.objectsNew_dig_at
