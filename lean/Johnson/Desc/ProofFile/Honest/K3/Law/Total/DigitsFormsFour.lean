-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Total/DigitsFormsFour.lean: the kind "lookup" (K3).
Conditional, under the library's hypothesis `P5J.AtMgA`: four of the live public tests "formsIn"
hold behind an acceptance of the lookup on the digits: the kept "objects" and "small" at every sort
of link; the kept "planes" at an attention link and at the head's; the kept "join" at an attention
link. Said of two states of the verifier, at the composed meaning's own data. Theorems.

Terms. Honest/K3/GLOSSARY.md. In this file: a test "formsIn" is the Boolean test of a public item
`Pub.formsIn l pc nm` (Johnson/Desc/First/Borders.lean), for the run of claims named nm at piece pc
of link l; a kept test is one of `keptDigits`, the new one is `newDigits`
(Johnson/Desc/Sound/MgAt/K3DigitsSorted.lean). The stated sub-protocol at the digits' address is
`k3Const … l true` (Johnson/Desc/First/Look/K3Base.lean). The tests in front are the list
`frontDig mgMore l` (K3DigitsSorted.lean). The book-keeping's first test is `shapeAt`
(Borders.lean). The sentence of the item leftOn l is the library's `k3LeftOnItemAt`
(Johnson/Desc/First/Look/K3LeftItem.lean).

What is shown.
  `dig_front`: out of the tests in front: the address's piece is the public structure's; the place;
    the lookup's promise in front (`k3OnIn`, Johnson/Desc/First/Look/K3Borders.lean); a ledger with
    its sizes.
  `dig_stand`: out of the book-keeping's first test in front: the state stands inside a link of the
    written sort.
  `objectsKept_dig_at`: the kept "objects": the library's `objects_kept_dig`
    (Johnson/Desc/Sound/MgAt/K3DigitsFormsKept.lean), called.
  `small_dig_at`: the kept "small": `small_pass_dig`
    (Johnson/Desc/Sound/MgAt/K3DigitsFormsSmall.lean).
  `planes_dig_at`: the kept "planes": `planes_kept_dig_att`
    (Johnson/Desc/Sound/MgAt/K3DigitsFormsPlanes.lean) and `planes_kept_dig_head_free`
    (Johnson/Desc/Sound/MgAt/K3DigitsPlanesHead.lean).
  `join_dig_att`: the kept "join": `join_kept_dig_att`
    (Johnson/Desc/Sound/MgAt/K3DigitsFormsJoinAtt.lean).
The statements speak of no thread, piece, transcript or string.

Hypotheses that remain.
  `h`: the library's hypothesis `P5J.AtMgA` (Johnson/P5J/MgAtAll.lean).
  `hl`, `hsub`: the link is below 25; its sort in the written full list.
  `hb`, `hOk`, `hd`: b' is the stated sub-protocol at the digits' address; it passes its test on the
    plan; its decision accepts from s to s'.
  `hfront`: the public tests that are open or tied in front hold at s.
  `hshape`: (for "planes" and "join", and in `dig_stand`) the book-keeping's first test holds in
    front.
  `hnl`, `hLeft`: (for "planes") the link is no layers' link; what the item leftOn l says of the
    state in front holds: a sentence, not a Boolean test.

Follows. The calls are those of three other files of the lookup's, on the honest thread, argument
for argument: Honest/K3/Law/Thread/FormRestAtHeadItems.lean [not in this library],
Honest/K3/Law/Thread/FormRestAtHeadPlanes.lean [not in this library] and
Honest/K3/Law/Thread/FormRestAtHeadJoin.lean [not in this library].
What these drew out of the thread's promise is a hypothesis here.

How the proof goes. The library's laws stand at the stated sub-protocol's own decision: they are
called. Their terms are shown from `P5J.AtMgA` alone in Johnson/P5J/K03DigPartsAt.lean,
Johnson/P5J/K03DigPlanesAt.lean and Johnson/P5J/K03JoinRawAt.lean.

Users. `forms_dig_at` (Honest/K3/Law/Total/MadeOwedDigits.lean) calls the last four; they show a
part of the hypothesis `hF` of Honest/K3/Law/Total/DigitsBehindState.lean.
Honest/K3/Law/Total/DigitsFormsOwn.lean, DigitsFormsNew.lean and DigitsFormsLay.lean in this
folder import this file.

Options. `maxRecDepth` is raised to 100000 for the file; `maxHeartbeats` to 4000000 in front of two
theorems; `quotPrecheck` is off at one local notation. These raise limits on Lean's own work or
switch off a check on a notation's names: none loosens a check on a proof.

Limits. All statements are implications. No instance of these hypotheses is exhibited in this file.
Nothing on "own", on "join" at the head's link, or on the new "objects". At the full size alone.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.Sound.MgAt.K3DigitsFormsKeptFound
import Johnson.Desc.Sound.MgAt.K3DigitsFormsLive
import Johnson.Desc.Sound.MgAt.K3DigitsFormsSmall
import Johnson.Desc.Sound.MgAt.K3DigitsOthers
import Johnson.P5J.K03DigPartsAt
import Johnson.P5J.K03DigPlanesAt
import Johnson.P5J.K03JoinRawAt

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
open VerifiableInference.Desc.First (ModelPart shift standOf pubSets)
open P5J

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)

local notation "PS" => Desc.First.flatPlacesOf linksFull true
set_option quotPrecheck false in
local notation "𝔐" => AtMg.𝔇 (AtMgA.toAtMg h) (AtMgA.𝔇 h)

/-- **Out of the tests in front of the digits.** Conditional on `P5J.AtMgA`, the stated sub-protocol
at the address, and the public tests in front. No instance of these hypotheses is exhibited in this
file. -/
theorem dig_front {l : ℕ} (hl : l < 25) {sub : ModelPart} (hsub : linksFull[l]? = some sub)
    {b' : Block TS ProofFile.Cl}
    (hb : k3Const (At.X Zp) Zp.first.codes Zp.first.shape l true = some b') {s : TS}
    (z : ProofFile.InstPub)
    (hfront : ∀ p ∈ frontDig mgMore l, (mgAll (𝔐) mgBase).pub p (z, s) = true) :
    (IM.k3Place l true).piece = Desc.K3.pieceAt (At.X Zp) l true ∧
      ∃ x, lookAt (At.X Zp) l true = some x ∧
        Desc.K3.k3OnIn (Desc.First.Look.P.ofPlace (Params.settingOf (At.X Zp).P.frame) true x) s =
          true ∧ ∃ F, s.fork? = some F ∧ OnBytes.PscRun.Sized F := by
  obtain ⟨hpc, p, hp, -⟩ := K3Lot.k03_place K3Lot.ofForm (K3Lot.readersAt (At.X Zp)) (At.X Zp)
    Zp.first.codes Zp.first.shape l true b' hb
  obtain ⟨x, hlook, -⟩ : ∃ x, lookAt (At.X Zp) l true = some x ∧
      Desc.First.Look.P.ofPlace (Params.settingOf (At.X Zp).P.frame) true x = p := by
    unfold placeAt at hp
    exact Option.map_eq_some_iff.1 hp
  obtain ⟨sub', hsub', -, hpcT⟩ := K3Lot.k03_sub_full l hl
  obtain rfl : sub' = sub := Option.some.inj (hsub'.symm.trans hsub)
  have eM : (mgAll (𝔐) mgBase).more = mgMore := mgAll_more_closed (𝔐) mgBase rfl
  have hIn : Desc.K3.k3OnIn
      (Desc.First.Look.P.ofPlace (Params.settingOf (At.X Zp).P.frame) true x) s = true := by
    have hOpen := digits_lookIn_open (mgAll (𝔐) mgBase).more linksFull PS (k3K l true)
      (IM.k3Place l true) l sub' (hfit_mgAll (𝔐) mgBase rfl) (K3Lot.k03_at_full l hl true) rfl hsub
      hpcT (.lookIn l (7 + shift sub')) (by simp)
    rw [eM] at hOpen
    have hp' := hfront _ (List.mem_append_left _ hOpen)
    rw [hpcT.symm.trans hpc] at hp'
    exact k3LookIn_onIn (fLook_at (k3At_mgAll (𝔐) mgBase) l true hlook z s hp')
  obtain ⟨F, hF, hSz, _⟩ := k3OnIn_ledger hIn
  exact ⟨hpc, x, hlook, hIn, F, hF, hSz⟩

/-- **In front of the digits the state stands inside a link of the written sort.** Conditional on
the book-keeping's first Boolean test there. No instance of these hypotheses is exhibited in this
file. `P5J.k03_stand_of_shape` (Johnson/P5J/K03ReadersHeadAtt.lean) has the same statement; neither
calls the other. -/
theorem dig_stand {l : ℕ} (hl : l < 25) {sub : ModelPart} (hsub : linksFull[l]? = some sub) {s : TS}
    (hshape : Desc.First.shapeAt linksFull PS[k3K l true]? s = true) : standOf s = .link sub := by
  have h0 := List.all_eq_true.1 digStandAt_full l (List.mem_range.2 hl)
  unfold digStandRowB at h0
  have h1 := of_decide_eq_true h0
  rw [hsub, Option.getD_some] at h1
  rw [K3Lot.k03_at_full l hl true] at hshape
  unfold Desc.First.shapeAt at hshape
  simp only [Bool.and_eq_true, beq_iff_eq] at hshape
  rw [hshape.1.1, h1]

/-- **The kept "objects" behind the acceptance.** Conditional on `P5J.AtMgA`, the acceptance of the
stated sub-protocol's decision and the public tests in front. No instance of these hypotheses is
exhibited in this file. -/
theorem objectsKept_dig_at {l : ℕ} (hl : l < 25) {sub : ModelPart} (hsub : linksFull[l]? = some sub)
    {b' : Block TS ProofFile.Cl}
    (hb : k3Const (At.X Zp) Zp.first.codes Zp.first.shape l true = some b')
    (hOk : b'.planOk = true) {s s' : TS} {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))}
    (hd : b'.decide s rs gs = .ok s') (z : ProofFile.InstPub)
    (hfront : ∀ p ∈ frontDig mgMore l, (mgAll (𝔐) mgBase).pub p (z, s) = true) :
    (mgAll (𝔐) mgBase).pub (.formsIn l (2 + shift sub) "objects") (z, s') = true := by
  obtain ⟨hpc, -, -, -, F, hF, hSz⟩ := dig_front h hl hsub hb z hfront
  obtain ⟨lk, hlk, hrawO, hrawG, _, _⟩ := P5J.k03_finds_dig h hl hsub
  have ht := hfront _ ((digits_sorted hl hsub).2 (.formsIn l (2 + shift sub) "objects") (by
    cases sub <;> simp [keptDigits, shift]))
  exact objects_kept_dig (𝔐) mgBase lk (K3Lot.readersAt (At.X Zp)) Zp.first.codes
    Zp.first.shape (IM.k3Place l true) b' K3Lot.ofForm hb hOk rfl hpc rfl hsub hlk
    atS2_calls_ofForm _ s s' rs gs hd hF hSz rfl hrawO hrawG ht

/-- **The kept "small" behind the acceptance.** Conditional on the like. No instance of these
hypotheses is exhibited in this file. -/
theorem small_dig_at {l : ℕ} (hl : l < 25) {sub : ModelPart} (hsub : linksFull[l]? = some sub)
    {b' : Block TS ProofFile.Cl}
    (hb : k3Const (At.X Zp) Zp.first.codes Zp.first.shape l true = some b')
    (hOk : b'.planOk = true) {s s' : TS} {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))}
    (hd : b'.decide s rs gs = .ok s') (z : ProofFile.InstPub)
    (hfront : ∀ p ∈ frontDig mgMore l, (mgAll (𝔐) mgBase).pub p (z, s) = true) :
    (mgAll (𝔐) mgBase).pub (.formsIn l (5 + shift sub) "small") (z, s') = true := by
  obtain ⟨hpc, -, -, -, F, hF, hSz⟩ := dig_front h hl hsub hb z hfront
  obtain ⟨lk, hlk, _⟩ := P5J.k03_finds_dig h hl hsub
  have ht := hfront _ ((digits_sorted hl hsub).2 (.formsIn l (5 + shift sub) "small") (by
    cases sub <;> simp [keptDigits, shift]))
  exact small_pass_dig (𝔐) mgBase
    (Desc.K9.holesAt (At.X Zp) (headLink (At.X Zp)) l lk) lk (K3Lot.readersAt (At.X Zp))
    Zp.first.codes Zp.first.shape (IM.k3Place l true) b' K3Lot.ofForm hb hOk rfl hpc rfl hsub
    (rd_holesAt (𝔐) hlk) rfl _ s s' rs gs hd hF hSz
    (B₀ := 4 + shift sub) (by cases sub <;> rfl) ht

set_option maxHeartbeats 4000000 in
/-- **The kept "planes" behind the acceptance, at an attention link and at the head's.** Conditional
on the like, the book-keeping's first Boolean test in front, and what the item leftOn l says of the
state in front. No instance of these hypotheses is exhibited in this file. -/
theorem planes_dig_at {l : ℕ} (hl : l < 25) {sub : ModelPart} (hsub : linksFull[l]? = some sub)
    {b' : Block TS ProofFile.Cl}
    (hb : k3Const (At.X Zp) Zp.first.codes Zp.first.shape l true = some b')
    (hOk : b'.planOk = true) {s s' : TS} {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))}
    (hd : b'.decide s rs gs = .ok s') (z : ProofFile.InstPub)
    (hfront : ∀ p ∈ frontDig mgMore l, (mgAll (𝔐) mgBase).pub p (z, s) = true)
    (hnl : sub ≠ .layers)
    (hshape : Desc.First.shapeAt linksFull PS[k3K l true]? s = true)
    (hLeft : k3LeftOnItemAt (At.X Zp) l s) :
    (mgAll (𝔐) mgBase).pub (.formsIn l (2 + shift sub) "planes") (z, s') = true := by
  obtain ⟨hpc, -, -, -, F, hF, hSz⟩ := dig_front h hl hsub hb z hfront
  have ht := hfront _ ((digits_sorted hl hsub).2 (.formsIn l (2 + shift sub) "planes") (by
    cases sub with
    | layers => exact absurd rfl hnl
    | attention => simp [keptDigits, shift]
    | head => simp [keptDigits, shift]))
  obtain ⟨s2, hs2, a2, a3⟩ := K3Lot.k03_sub_full l hl
  obtain rfl : s2 = sub := Option.some.inj (hs2.symm.trans hsub)
  have hStand := dig_stand hl hs2 hshape
  have hFr := List.all_eq_true.1 planesFront_mgMore l (List.mem_range.2 hl)
  unfold planesFrontRowB at hFr
  rw [Bool.and_eq_true] at hFr
  have m1 : Desc.First.Pub.lookOut l (IM.k3Place l false).piece ∈ frontDig mgMore l := by
    simpa using hFr.1
  have ePc : (IM.k3Place l false).piece = Desc.K3.pieceAt (At.X Zp) l false := by
    have a1 := pieceAt_calls (At.X Zp) l
    omega
  have K := k3At_mgAll (𝔐) mgBase
  obtain ⟨pc, hpcAt, hLf⟩ := hLeft
  have hO : Desc.K3.k3OnOut pc s = true := by
    have h0 := hfront _ m1
    rw [ePc] at h0
    have h1 := (K.lookOut l false _).symm.trans h0
    unfold k3OnOutAt at h1
    rw [hpcAt] at h1
    exact h1
  have hdc : pc.digits = false := by
    unfold placeAt at hpcAt
    obtain ⟨y', -, rfl⟩ := Option.map_eq_some_iff.1 hpcAt
    rfl
  cases s2 with
  | layers => exact absurd rfl hnl
  | attention =>
    obtain ⟨w, hatt⟩ := VerifiableInference.OnPublicFiles.here_att_of_stand hStand
    obtain ⟨ho, h24⟩ := (P5J.k03_sorts_full l hl).1 hs2
    obtain ⟨g, hg⟩ : ∃ g, l = 2 * g + 1 := ⟨l / 2, by omega⟩
    obtain ⟨lk, p, a, hlk, -, -, hraw⟩ := P5J.k03_rawP_att h (g := g) (by omega)
    rw [← hg] at hlk
    exact planes_kept_dig_att (𝔐) mgBase lk (K3Lot.readersAt (At.X Zp)) Zp.first.codes
      Zp.first.shape (IM.k3Place l true) b' K3Lot.ofForm hb hOk rfl hpc rfl hs2 hlk
      atS2_calls_ofForm _ s s' rs gs hd hF hSz rfl hnl
      (notHead_of_piece (hpc.symm.trans a3)) p.lm a hatt hdc hO hLf hraw ht
  | head =>
    obtain ⟨o', hhead⟩ := VerifiableInference.OnPublicFiles.here_head_of_stand hStand
    have e24 := (P5J.k03_sorts_full l hl).2 hs2
    obtain ⟨-, lk, p, hlk, -, hraw⟩ := P5J.k03_rawP_head h
    rw [← e24] at hlk
    exact planes_kept_dig_head_free (𝔐) mgBase lk (K3Lot.readersAt (At.X Zp))
      Zp.first.codes Zp.first.shape (IM.k3Place l true) b' K3Lot.ofForm hb hOk rfl hpc rfl
      hs2 hlk atS2_calls_ofForm _ s s' rs gs hd hF hSz rfl hnl
      (isHead_of_piece (hpc.symm.trans a3)) p.lm 0 hhead hdc hO hLf hraw ht

set_option maxHeartbeats 4000000 in
/-- **The kept "join" behind the acceptance, at an attention link.** Conditional on the like and the
book-keeping's first Boolean test in front. No instance of these hypotheses is exhibited in this
file. -/
theorem join_dig_att {l : ℕ} (hl : l < 25) (hsub : linksFull[l]? = some ModelPart.attention)
    {b' : Block TS ProofFile.Cl}
    (hb : k3Const (At.X Zp) Zp.first.codes Zp.first.shape l true = some b')
    (hOk : b'.planOk = true) {s s' : TS} {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))}
    (hd : b'.decide s rs gs = .ok s') (z : ProofFile.InstPub)
    (hfront : ∀ p ∈ frontDig mgMore l, (mgAll (𝔐) mgBase).pub p (z, s) = true)
    (hshape : Desc.First.shapeAt linksFull PS[k3K l true]? s = true) :
    (mgAll (𝔐) mgBase).pub (.formsIn l 2 "join") (z, s') = true := by
  obtain ⟨hpc, -, -, -, F, hF, hSz⟩ := dig_front h hl hsub hb z hfront
  have ht := hfront _ ((digits_sorted hl hsub).2 (.formsIn l 2 "join") (by
    simp [keptDigits]))
  obtain ⟨w, hatt⟩ := VerifiableInference.OnPublicFiles.here_att_of_stand (dig_stand hl hsub hshape)
  obtain ⟨s2, hs2, -, a3⟩ := K3Lot.k03_sub_full l hl
  obtain rfl : s2 = .attention := Option.some.inj (hs2.symm.trans hsub)
  obtain ⟨ho, h24⟩ := (P5J.k03_sorts_full l hl).1 hs2
  obtain ⟨g, hg⟩ : ∃ g, l = 2 * g + 1 := ⟨l / 2, by omega⟩
  obtain ⟨lk, -, a, hlk, ha, -, -⟩ := P5J.k03_rawP_att h (g := g) (by omega)
  have hraw := P5J.k03_joinRaw_att h g (by omega) a ha lk ((h.laid.linkAt _).symm.trans hlk)
  rw [← hg] at hlk
  exact join_kept_dig_att (𝔐) mgBase lk (K3Lot.readersAt (At.X Zp)) Zp.first.codes
    Zp.first.shape (IM.k3Place l true) b' K3Lot.ofForm hb hOk rfl hpc rfl hs2 hlk
    K3Lot.ofForm atS2_calls_ofForm _ s s' rs gs hd hF hSz
    (notHead_of_piece (hpc.symm.trans a3)) a hatt hraw ht

end ProofFile.Honest.K3.Law.Total

#print axioms ProofFile.Honest.K3.Law.Total.dig_front
#print axioms ProofFile.Honest.K3.Law.Total.dig_stand
#print axioms ProofFile.Honest.K3.Law.Total.objectsKept_dig_at
#print axioms ProofFile.Honest.K3.Law.Total.small_dig_at
#print axioms ProofFile.Honest.K3.Law.Total.planes_dig_at
#print axioms ProofFile.Honest.K3.Law.Total.join_dig_att
