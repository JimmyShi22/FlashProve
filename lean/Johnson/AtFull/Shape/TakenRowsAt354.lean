-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/TakenRowsAt354.lean: UNDER THE HEAD `P5J.AtMgA`: AT EVERY STATE THAT THE PROOF
FILE's OWN FIRST CHAIN REACHES IN FRONT OF ITS LAST PROXIMITY TEST (border 354), WHOEVER PLAYS,
EVERY ROW THAT A PROXIMITY TEST ON ANY GROUP OF THE STATEMENT WOULD TAKE IN IS IN ORDER (`OrderRow`,
OnBytes/Slice/BlkProxOrder.lean). It carries TakenRowsOrder.lean's top one member further: over the
last code switch. A joining of laws; nothing is evaluated.

Why one file more. The library has its invariant on the stored sample rows (`SampleGoodS`,
Johnson/Top/H0/K2Hands/SampleChainS.lean) at the reached states up to border 353
(`P1K2.both_at_open`, Johnson/P1K2R/FoldSide.lean), and, apart, that the code switch's own texts
keep it (`keepsS_k2`, SampleChainS.lean; `keepsInv_finishPlace`,
Johnson/Top/H0/K2Hands/SampleSeatK2.lean). Here the member number 353 is tied to that text at its
seat (`IM.k2_finish_of`, Johnson/IMR/K2Seat.lean; `IM.back_numbers`, Johnson/IMR/BackSeat.lean;
`IM.yes_alone`, Johnson/IMR/SeatForm.lean).

Main names.
* `finish_keeps_good`: the member number 353 keeps the invariant, on rounds whose drawn elements are
  in canonical form.
* `goodS_at_354`: so SampleGoodS holds at every state reached at border 354.
* `samplesPlain_at_354`: no stored sample row has a written-out factor there.
* `taken_order_at_354`: every row of runRows s.st G is in order there, at every group G of the
  statement: the open rows by OpenRowsOrder.lean, the stored sample rows by the line above.
* `taken_order_entered`: the proximity test works on a state of its own, which `enterFinish`
  (Johnson/Desc/K12/AtFinish.lean) makes of the chain's: it takes the statement over as it is
  (`Seat.enterFinish_ok`, Johnson/Desc/K12/SeatLaws.lean). So where enterFinish s = .ok t: every row
  of runRows t.st G is in order at the group G number t.g.

What it is for. A law by which the chain's last proximity test returns could ask "the rows taken in
are in order" of the state in front. At a reached state that is this file's top, in the letters of
the test's own state: `taken_order_entered`.

Limits. "REACHED" IS TAKEN WITH THE TEST ON THE WORDS IN FRONT OF EACH DECISION (`Reach 0
(cF.blocksInOrder.map below) …`). BORDER 354 ALONE, beside TakenRowsOrder.lean's borders up to 353: nothing
behind the proximity test. "In order" is less than "has no written-out factor", and less than
`Tensor.ok` for the stored sample rows. NO LAW ON THE PROXIMITY TEST IS CALLED OR SHOWN HERE: that
it returns at any state is not said. That the head has a member is shown in scope, where the reader
returns and `protocolDataWellFormed` accepts (`head_of_live`, Johnson/P5J/HeadOfLive.lean); that these three hold
together, at two named sets of public files, in a side library. At the format's second hash
function. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.TakenRowsOrder
import Johnson.IMR.K2Seat
import Johnson.IMR.BackSeat
import Johnson.Desc.K12.SeatLaws
import Johnson.Top.H0.K2Hands.SampleSeatK2
import Johnson.Top.H0.K2Hands.SampleReach

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model OnBytes.Slice
open OnBytes.Slice.ProxRun (OrderRow)
open VerifiableInference.Desc (Block Chain step_iff)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (SampleGoodS QGoodS KeepsInv keepsInv_finishPlace keepsS_k2
  keepsD_below)
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)
open OnBytes.Maker (WholeD)
open P5J (AtMgA)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The last code switch (member 353) keeps the library's invariant on the stored sample rows**,
on rounds whose drawn elements are in canonical form. -/
theorem finish_keeps_good (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {b : Block S ProofFile.Cl}
    (hb : cF.blocksInOrder[353]? = some b) : KeepsInv QGoodS b := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨b₀, y, e1, -, -, hla, harm⟩ := IM.k2_finish_of O
  have q := (IM.back_numbers h.scope h.reads O).1 0 b₀ e1
  obtain rfl : ({ b₀ with planOk := b₀.planOk && b₀.hasNoClaimsAndNothingAfter } : Block S ProofFile.Cl) = b :=
    Option.some.inj (q.symm.trans hb)
  intro s s' rs gs hr hd hs
  have hd' : b₀.decide s rs gs = .ok s' := hd
  have hy : y.decide s rs gs = .ok s' := ((IM.yes_alone hla (by simp) s s' rs gs).1 hd').1
  rcases harm with ⟨-, he⟩ | ⟨P, n, -, -, ex⟩
  · obtain ⟨e, he'⟩ := he s rs gs
    rw [he'] at hy
    cases hy
  · rw [ex] at hy
    exact keepsInv_finishPlace _ (keepsS_k2 _) s s' rs gs hr hy hs

/-- **So the invariant stands at every state that is reached behind it**, with the test on the words
in front of each decision. -/
theorem goodS_at_354 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {p : ProofFile.InstPub} {s : S}
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) 354 (p, s)) : SampleGoodS s.st := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  cases hr with
  | @succ k z s₀ s' b' hprev hb hy =>
    have g0 := (P1K2.both_at_open O h.laid.value h.laid.planOk
      (le_of_eq (Meaning.K2.front_len h.scope h.reads O).symm) hprev).1
    rw [List.getElem?_map] at hb
    obtain ⟨b, hb0, rfl⟩ := Option.map_eq_some_iff.1 hb
    obtain ⟨R, c, -, hs⟩ := hy
    obtain ⟨_, hd, _⟩ := (step_iff 0 (below b) s₀ s R c _).1 hs
    exact keepsD_below (finish_keeps_good h hb0) s₀ s _ _ (fun _ _ => trivial) hd g0

/-- No stored sample row has a written-out factor there. -/
theorem samplesPlain_at_354 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {p : ProofFile.InstPub} {s : S}
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) 354 (p, s)) : SamplesPlain s.st :=
  samplesPlain_of_good (goodS_at_354 h hr)

/-- **IN FRONT OF THE CHAIN's LAST PROXIMITY TEST: EVERY ROW THAT A PROXIMITY TEST ON ANY GROUP OF
THE STATEMENT WOULD TAKE IN IS IN ORDER.** -/
theorem taken_order_at_354 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {p : ProofFile.InstPub} {s : S}
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) 354 (p, s)) {g : Nat} {G : Group}
    (hG : s.st.groups[g]? = some G) : ∀ r ∈ (runRows s.st G).toList, OrderRow r :=
  runRows_order (openOrd_reach h (reach_raw hr)) (samplesPlain_at_354 h hr) hG

/-- **So of the state with which the proximity test goes in**: its statement is the chain's, and its
group is one of that statement's. -/
theorem taken_order_entered (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {p : ProofFile.InstPub} {s : S}
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) 354 (p, s))
    {t : VerifiableInference.Desc.K12.T12}
    (he : VerifiableInference.Desc.K12.enterFinish s = .ok t) :
    ∀ G, t.st.groups[t.g]? = some G → ∀ r ∈ (runRows t.st G).toList, OrderRow r := by
  obtain ⟨o, -, -, -, rfl⟩ := VerifiableInference.Desc.K12.Seat.enterFinish_ok s t he
  exact fun G hG => taken_order_at_354 h hr hG

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.finish_keeps_good
#print axioms Johnson.AtFull.Shape.goodS_at_354
#print axioms Johnson.AtFull.Shape.samplesPlain_at_354
#print axioms Johnson.AtFull.Shape.taken_order_at_354
#print axioms Johnson.AtFull.Shape.taken_order_entered
