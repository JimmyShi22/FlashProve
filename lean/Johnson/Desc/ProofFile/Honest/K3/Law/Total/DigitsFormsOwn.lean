-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Total/DigitsFormsOwn.lean: the kind "lookup" (K3). Conditional,
under the library's hypothesis `P5J.AtMgA`: three more of the live public tests "formsIn" hold
behind an acceptance of the lookup on the digits: the kept "own" (the calling kind's own runs) at an
attention link and at the head's, and the kept "join" at the head's. Said of two states of the
verifier. Theorems.

Terms. Honest/K3/GLOSSARY.md. In this file: a test "formsIn" is the Boolean test of a public item
`Pub.formsIn l pc nm` (Johnson/Desc/First/Borders.lean), for the run of claims named nm at piece pc
of link l; a kept test is one of `keptDigits`, the new one is `newDigits`
(Johnson/Desc/Sound/MgAt/K3DigitsSorted.lean). The stated sub-protocol at the digits' address is
`k3Const … l true` (Johnson/Desc/First/Look/K3Base.lean). The tests in front are the list
`frontDig mgMore l` (K3DigitsSorted.lean). The book-keeping's first test is `shapeAt`
(Borders.lean). In the statements two local notations stand: PS for the places of all the first
chain's sub-protocols, in the flat list's order, at the full size's row of links
(`flatPlacesOf linksFull true`, Johnson/Desc/First/Driver/Chain.lean); 𝔐 for
`AtMg.𝔇 (AtMgA.toAtMg h) (AtMgA.𝔇 h)`: through it the hypothesis `h` enters them.

What is shown.
  `own_dig_att`: the kept "own" at an attention link: the library's `own_kept_dig_att`
    (Johnson/Desc/Sound/MgAt/K3DigitsOwnAtt.lean), called.
  `ready_dig_head`: in front of the head's digits the output head's promise `K6Ready`
    (Johnson/Desc/Kinds/Law/RunsStill.lean) holds at whatever the state shows: from "reached".
  `own_dig_head`: the kept "own" at the head's link: `own_kept_dig_head`
    (Johnson/Desc/Sound/MgAt/K3DigitsHeadItems.lean), called.
  `join_dig_head`: the kept "join" at the head's link: `join_kept_dig_head`
    (K3DigitsHeadItems.lean), called.
The statements speak of no thread, piece, transcript or string. The file is the fellow of
Honest/K3/Law/Total/DigitsFormsFour.lean.

Hypotheses that remain.
  `h`: the library's hypothesis `P5J.AtMgA` (Johnson/P5J/MgAtAll.lean).
  `hb`, `hOk`, `hd`: b' is the stated sub-protocol at the digits' address; it passes its test on the
    plan; its decision accepts from s to s'.
  `hfront`: the public tests that are open or tied in front hold at s.
  `hl`, `hsub`: (at attention) the link is below 25; it is an attention link.
  `hshape`: the book-keeping's first test holds in front.
  `hr`: (at the head's link) s is reached by the wrapped sub-protocols' steps (`Reach`,
    Johnson/Top/H0/Walk/Reach.lean).
  `hF`: (in `ready_dig_head`) a ledger is open at s.

Imported. DigitsFormsFour.lean and files of the library. No module under Johnson/Goal/ is imported
directly. One name that is declared under that folder is written in a proof here:
`Meaning.scope_plans` (Johnson/Goal/Meaning/PlanShapes.lean), a lemma's call.

How the proof goes. Where the hypotheses of the library's three laws come from. At attention, two
terms: what the link's second sub-protocol states is the attention kind's four runs
(`K05_states_raw_of_open`, Johnson/H2K5R/StatesRawAtOpen.lean, at the plan that `IM.ground_tails`,
Johnson/IMR/K8Seat.lean, gives: as the library's own `P5J.k03_ownIt_att`,
Johnson/P5J/K03OwnItAttAt.lean, gets them); these runs but "join" return the state that they were
given (`runsN_keeps`, StatesRawAtOpen.lean). At the head, three terms: `P5J.k03_six_K`,
`k03_six_hBo`, `k03_six_hBj` (Johnson/P5J/K03HeadSixAt.lean); and one fact on the state in front,
`K6Ready`: by `heardAt_345` (Johnson/P5J/K03ReadyAt345.lean: on every state reached at number 345),
`k6Ready_at` (Johnson/Desc/Kinds/Law/K6Claims.lean) and `ready_of_seen`
(Johnson/Top/H/Keep/HeadOwnReady.lean). In which case of the state the chain stands: `dig_stand`
(DigitsFormsFour.lean).
Where the library itself calls these three laws: in their own two files alone, at letters, at a
piece's acceptance.
At its closed constant the library
goes another way.

Users. `forms_dig_at` (Honest/K3/Law/Total/MadeOwedDigits.lean) calls `own_dig_att`, `own_dig_head`
and `join_dig_head`.

Options. `maxRecDepth` is raised to 100000 for the file; `maxHeartbeats` to 4000000 in front of
three theorems; `quotPrecheck` is off at one local notation. These raise limits on Lean's own work
or switch off a check on a notation's names: none loosens a check on a proof.

Limits. All statements are implications. No instance of these hypotheses is exhibited in this file.
Nothing on "own" at a layers' link or on the new "objects". At the full size alone.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Total.DigitsFormsFour
import Johnson.Desc.Sound.MgAt.K3DigitsOwnAtt
import Johnson.Desc.Sound.MgAt.K3DigitsHeadItems
import Johnson.H2K5R.StatesRawAtOpen
import Johnson.P5J.K03HeadSixAt
import Johnson.P5J.K03ReadyAt345
import Johnson.Top.H.Keep.HeadOwnReady
import Johnson.IMR.K8Seat

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
open VerifiableInference.Desc.First (ModelPart shift standOf)
open VerifiableInference.Desc.First.Att.P (K05_states_raw_of_open runsN_keeps)
open VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Head.Law
open Johnson.Desc.First.Walk.Tied (Reach)
open P5J

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)

local notation "PS" => Desc.First.flatPlacesOf linksFull true
set_option quotPrecheck false in
local notation "𝔐" => AtMg.𝔇 (AtMgA.toAtMg h) (AtMgA.𝔇 h)

set_option maxHeartbeats 4000000 in
/-- **The kept "own" behind the acceptance, at an attention link.** Conditional on `P5J.AtMgA`, the
acceptance of the stated sub-protocol's decision, the public tests and the book-keeping's first
Boolean test in front. No instance of these hypotheses is exhibited in this file. -/
theorem own_dig_att {l : ℕ} (hl : l < 25) (hsub : linksFull[l]? = some ModelPart.attention)
    {b' : Block TS ProofFile.Cl}
    (hb : k3Const (At.X Zp) Zp.first.codes Zp.first.shape l true = some b')
    (hOk : b'.planOk = true) {s s' : TS} {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))}
    (hd : b'.decide s rs gs = .ok s') (z : ProofFile.InstPub)
    (hfront : ∀ p ∈ frontDig mgMore l, (mgAll (𝔐) mgBase).pub p (z, s) = true)
    (hshape : Desc.First.shapeAt linksFull PS[k3K l true]? s = true) :
    (mgAll (𝔐) mgBase).pub (.formsIn l 3 "own") (z, s') = true := by
  obtain ⟨hpc, -, -, -, F, hF, hSz⟩ := dig_front h hl hsub hb z hfront
  have ht := hfront _ ((digits_sorted hl hsub).2 (.formsIn l 3 "own") (by simp [keptDigits]))
  obtain ⟨w, hatt⟩ := VerifiableInference.OnPublicFiles.here_att_of_stand (dig_stand hl hsub hshape)
  obtain ⟨s2, hs2, -, a3⟩ := K3Lot.k03_sub_full l hl
  obtain rfl : s2 = .attention := Option.some.inj (hs2.symm.trans hsub)
  obtain ⟨ho, h24⟩ := (P5J.k03_sorts_full l hl).1 hs2
  obtain ⟨g, hg⟩ : ∃ g, l = 2 * g + 1 := ⟨l / 2, by omega⟩
  have hg12 : g < 12 := by omega
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hW : Bs.G₀.W = At.X Zp := O.W
  obtain ⟨hp4, hN, -, -⟩ := _root_.Meaning.scope_plans h.scope h.reads h.pubOne
  obtain ⟨hT, -⟩ := IM.ground_tails h.scope h.reads O.pub O.blank
  obtain ⟨-, A, -, -, -, hA, -⟩ := hT g hg12
  obtain ⟨Lk, hLk, hSt⟩ := K05_states_raw_of_open O (by rw [hW]; exact hp4)
    (by rw [hW]; exact hN ▸ hg12) hA
  rw [← hg] at hLk
  exact own_kept_dig_att (𝔐) mgBase Lk (K3Lot.readersAt (At.X Zp)) Zp.first.codes
    Zp.first.shape (IM.k3Place l true) b' K3Lot.ofForm hb hOk rfl hpc rfl hs2
    ((h.laid.linkAt l).trans hLk) z s s' rs gs hd hF hSz
    (notHead_of_piece (hpc.symm.trans a3)) A hatt hSt (runsN_keeps A) ht

include h in
/-- **In front of the head's digits `K6Ready` holds at whatever the state shows.** Conditional on
`P5J.AtMgA`, s being reached, and an open ledger. No instance of these hypotheses is exhibited in
this file. -/
theorem ready_dig_head {s : TS} (z : ProofFile.InstPub)
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) (k3K 24 true) (z, s)) {F : Fork}
    (hF : s.fork? = some F) :
    ∀ zz U, Sees s zz U → K6Ready (At.X Zp).hS (readsOf (At.X Zp))
      (parOf (At.X Zp).hS (workOf (At.X Zp))) zz U := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have k := heardAt_345 h.scope h.reads O h.laid.planOk (z := z) (s345 := s) hr
  rw [O.W] at k
  exact ready_of_seen _ _ _ hF fun zz U hz hU => k6Ready_at _ _ _ k hz hU

set_option maxHeartbeats 4000000 in
/-- **The kept "own" behind the acceptance, at the head's link.** Conditional on `P5J.AtMgA`, the
acceptance of the stated sub-protocol's decision, the public tests and the book-keeping's first
Boolean test in front, and s being reached. No instance of these hypotheses is exhibited in this
file. -/
theorem own_dig_head {b' : Block TS ProofFile.Cl}
    (hb : k3Const (At.X Zp) Zp.first.codes Zp.first.shape 24 true = some b')
    (hOk : b'.planOk = true) {s s' : TS} {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))}
    (hd : b'.decide s rs gs = .ok s') (z : ProofFile.InstPub)
    (hfront : ∀ p ∈ frontDig mgMore 24, (mgAll (𝔐) mgBase).pub p (z, s) = true)
    (hshape : Desc.First.shapeAt linksFull PS[k3K 24 true]? s = true)
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) (k3K 24 true) (z, s)) :
    (mgAll (𝔐) mgBase).pub (.formsIn 24 4 "own") (z, s') = true := by
  have hl : 24 < 25 := by omega
  have hsub : linksFull[24]? = some ModelPart.head := rfl
  obtain ⟨hpc, -, -, -, F, hF, hSz⟩ := dig_front h hl hsub hb z hfront
  have ht := hfront _ ((digits_sorted hl hsub).2 (.formsIn 24 4 "own") (by simp [keptDigits]))
  obtain ⟨o', hhead⟩ := VerifiableInference.OnPublicFiles.here_head_of_stand (dig_stand hl hsub hshape)
  obtain ⟨s2, hs2, -, a3⟩ := K3Lot.k03_sub_full 24 hl
  obtain rfl : s2 = .head := Option.some.inj (hs2.symm.trans hsub)
  obtain ⟨-, lk, -, hlk, -, -⟩ := P5J.k03_rawP_head h
  exact own_kept_dig_head (𝔐) mgBase lk (K3Lot.readersAt (At.X Zp)) Zp.first.codes
    Zp.first.shape (IM.k3Place 24 true) b' K3Lot.ofForm hb hOk rfl hpc rfl hs2 hlk z s s' rs gs hd
    hF hSz (isHead_of_piece (hpc.symm.trans a3)) hhead (At.X Zp).hS (readsOf (At.X Zp)) 24 4
    (parOf (At.X Zp).hS (workOf (At.X Zp))) (k03_six_K h hlk) (ready_dig_head h z hr hF)
    (k03_six_hBo h hlk) ht

set_option maxHeartbeats 4000000 in
/-- **The kept "join" behind the acceptance, at the head's link.** Conditional on the like.
No instance of these hypotheses is exhibited in this file. -/
theorem join_dig_head {b' : Block TS ProofFile.Cl}
    (hb : k3Const (At.X Zp) Zp.first.codes Zp.first.shape 24 true = some b')
    (hOk : b'.planOk = true) {s s' : TS} {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))}
    (hd : b'.decide s rs gs = .ok s') (z : ProofFile.InstPub)
    (hfront : ∀ p ∈ frontDig mgMore 24, (mgAll (𝔐) mgBase).pub p (z, s) = true)
    (hshape : Desc.First.shapeAt linksFull PS[k3K 24 true]? s = true)
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) (k3K 24 true) (z, s)) :
    (mgAll (𝔐) mgBase).pub (.formsIn 24 4 "join") (z, s') = true := by
  have hl : 24 < 25 := by omega
  have hsub : linksFull[24]? = some ModelPart.head := rfl
  obtain ⟨hpc, -, -, -, F, hF, hSz⟩ := dig_front h hl hsub hb z hfront
  have ht := hfront _ ((digits_sorted hl hsub).2 (.formsIn 24 4 "join") (by simp [keptDigits]))
  obtain ⟨o', hhead⟩ := VerifiableInference.OnPublicFiles.here_head_of_stand (dig_stand hl hsub hshape)
  obtain ⟨s2, hs2, -, a3⟩ := K3Lot.k03_sub_full 24 hl
  obtain rfl : s2 = .head := Option.some.inj (hs2.symm.trans hsub)
  obtain ⟨-, lk, -, hlk, -, -⟩ := P5J.k03_rawP_head h
  exact join_kept_dig_head (𝔐) mgBase lk (K3Lot.readersAt (At.X Zp)) Zp.first.codes
    Zp.first.shape (IM.k3Place 24 true) b' K3Lot.ofForm hb hOk rfl hpc rfl hs2 hlk z s s' rs gs hd
    hF hSz (isHead_of_piece (hpc.symm.trans a3)) hhead (At.X Zp).hS (readsOf (At.X Zp)) 24 4
    (parOf (At.X Zp).hS (workOf (At.X Zp))) (k03_six_K h hlk) (ready_dig_head h z hr hF)
    (k03_six_hBj h hlk) atS2_calls_ofForm ht

end ProofFile.Honest.K3.Law.Total

#print axioms ProofFile.Honest.K3.Law.Total.own_dig_att
#print axioms ProofFile.Honest.K3.Law.Total.ready_dig_head
#print axioms ProofFile.Honest.K3.Law.Total.own_dig_head
#print axioms ProofFile.Honest.K3.Law.Total.join_dig_head
