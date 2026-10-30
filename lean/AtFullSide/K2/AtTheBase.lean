-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K2/AtTheBase.lean: the proofs of K2Plays and K2Accepted (AtTheBaseStatement.lean of this
folder): two of the five debts of the code switch at the base prover, at each of the kind's 25
members.

  prepW_some, numsW_some   by Lean's kernel: the plan's numbers are there at each written switch
  sortsW        by Lean's kernel: each written switch stands at one of three sorts of number and place
  nonZeroW      by Lean's kernel: one draw marked never 0 at each switch, as the entry's test asks
  half_base     the search at a switch's place finds the kind's side
  k2Plays, k2Accepted   the two debts

Limits. Those of the statement: nothing here says that the thread's sentence holds at any state.
-/
import AtFullSide.K2.AtTheBaseStatement
import AtFullSide.K2.FoundAtTheTerm
import AtFullSide.K2.PlaysAtJoin
import Johnson.Prover.Link.BasePart
import Johnson.HonestTrace.U3Fit.ReadsDebt3
import Johnson.Desc.ProofFile.Honest.K5.Law.AttValsAtHead
import Johnson.Desc.ProofFile.Honest.K2.Law.AcceptedAtHead
import Johnson.Desc.ProofFile.Honest.K2.Law.AcceptedAtArms
import Johnson.Desc.ProofFile.Honest.K2.Law.ExchangeByKind
import Johnson.Desc.ProofFile.Honest.Thread.SaidMono
import Johnson.Desc.ProofFile.Honest.K2.Law.PublicOkOfReads
import AtFullSide.K2.JoinFitFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K2.Base
open VerifiableInference.Desc (Chain Block Place KindName Strs fieldPrimeWord)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.K2.Honest (carryExact)
open VerifiableInference.Desc.K2.Honest.Returns (switchPlaceAt headPlaceAt)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open OnBytes.HonestTrace (Sz)
open OnBytes.SendSim.Seat (wJobs)
open P5J (AtMgA CellsM TS F0T)
open _root_.Desc.K14.Law (secondAt seatZ)
open IM (k2PlaceF)
open ProofFile.Honest
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K2
open ProofFile.Honest.K2.Law
open AtFullSide.K2.Term

set_option maxRecDepth 1000000 in
/-- By Lean's kernel: the plan is there. -/
theorem prepW_some : IM.prepW.isSome = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- By Lean's kernel: the plan's numbers are there at each written switch. -/
theorem numsW_some : (placesW.all fun p => (numsW p.place.link).isSome) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- By Lean's kernel: each written switch stands at a link's number, or at one of the two arms. -/
theorem sortsW : (placesW.all fun p =>
    (decide (1 ≤ p.link) && decide (p.link ≤ 23) && (switchNo p == 14 * p.link + 2) &&
      (p.place == switchPlaceAt p.link)) ||
    ((switchNo p == 339) && (p.place == headPlaceAt)) ||
    ((switchNo p == 353) && (p.place == k2PlaceF))) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- By Lean's kernel: at each written switch one draw is marked never 0, as many as the greatest
count of answers: the entry's test planOk1 asks that. -/
theorem nonZeroW : (placesW.all fun p => (numsW p.place.link).any fun n =>
    (n.nonZero == n.sent.foldl (fun a x => max a x.shape.answers) 0) && (n.nonZero == 1)) = true := by
  decide +kernel

variable {W₀ : Type} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)}

/-- The plan's numbers at a written switch, under the head and the opening. -/
theorem nums_of_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) {p : SwitchPlace} (hp : p ∈ placesW) :
    ∃ Pp n, P1K2.prepOf Zp Bs.G₀ = some Pp ∧ P1K2.numsAt Pp p.place.link = some n := by
  obtain ⟨Pp, hW⟩ := Option.isSome_iff_exists.1 prepW_some
  have hP : P1K2.prepOf Zp Bs.G₀ = some Pp := (prep_at_head h.toAtMg O).trans hW
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.1 (List.all_eq_true.1 numsW_some p hp)
  exact ⟨Pp, n, hP, (numsW_at_head h.toAtMg O hP p.place.link).symm.trans hn⟩

/-- **The accepting step at a written switch, at any fall.** hhalf: the side that stands at the place
has two rounds. -/
theorem accepted_at_switch (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) {Bk : ProverCoinCounts}
    {Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    {g : Placed (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X} {p : SwitchPlace}
    (hp : p ∈ placesW) (hhalf : (H.first.find? fun a => a.place == p.place) = some g)
    (hg : g.rounds = 2) (fall : Nat → TS → List Fmt.Drawn → Option String) :
    AcceptedS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk fall
      (switchNo p) := by
  have hs := List.all_eq_true.1 sortsW p hp
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hs
  rcases hs with (⟨⟨⟨h1, h2⟩, e⟩, ep⟩ | ⟨e, ep⟩) | ⟨e, ep⟩
  · obtain ⟨i, hi⟩ : ∃ i, p.link = i + 1 := ⟨p.link - 1, by omega⟩
    have h23 : i < 23 := by omega
    rw [ep, hi] at hhalf
    rw [e, hi]
    exact link_acceptedS_head h O h23 H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hhalf hg fall
  · rw [ep] at hhalf
    rw [e]
    exact head_acceptedS_head h O H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hhalf hg fall
  · rw [ep] at hhalf
    rw [e]
    exact fin_acceptedS_head h O H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hhalf hg fall

/-- Where the description's first test accepts an instance, the instance is light. -/
theorem light_of_start (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) {ξ : ProofFile.Inst}
    (hx : (F0T OnBytes.secondHashFunction Zp Np cF).okStart ξ = true) : ReadsLight Zp Bs.G₀ ξ :=
  OnBytes.HonestTrace.U3.Fit.readsLight_of_att h O hx (OnBytes.HonestTrace.U3.Att.att_returns_at_open h O)

/-- Every stored word of a prover lies below the prime. -/
theorem stored_below {Rc Xi Ky Tr X₀ X : Type} (H : Prover W₀ Rc Xi Ky Tr X₀ X) (w₀ : W₀) (rc : Rc)
    (i y : Nat) (u : List UInt64) (e : H.storedWords w₀ rc i y = some u) : ∀ a ∈ u, a < fieldPrimeWord := by
  unfold Prover.storedWords at e
  obtain ⟨l, -, rfl⟩ := Option.map_eq_some_iff.1 e
  intro a ha
  obtain ⟨f, -, rfl⟩ := List.mem_map.1 ha
  exact Johnson.Prover.Link.lt_ofF f

/-- The kind's side at a switch, with what the laws below read. -/
theorem half_base {I : WiderIn W₀} {Oh : OnlineProverArguments} {A : BaseReturn W₀} (hA : Returns I Oh Z A)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) {p : SwitchPlace} (hp : p ∈ switchPlaces Zp Bs.G₀) :
    (A.H.first.find? fun g => g.place == p.place) =
      some (switchHalf (coreSender freshTable) (rowsAt Zp Bs) (reader I Zp)
        (lotClosingAt Bs.G₀.first.layout (segmentsOf Zp Bs.G₀)) p) :=
  k2_found I OnBytes.secondHashFunction Sz.ref Oh O hA hp

/-- **The side plays.** -/
theorem k2Plays : K2Plays := by
  intro W₀ I Oh Z D r Zp Np cF x A Bs base hA h O Y X₂ S test item n₁ n₂ b₀ Vd Rd Kp w Said hst b q
    hb hq
  obtain ⟨p, hp, rfl⟩ := k2_place_at hb hq
  have hpS : p ∈ switchPlaces Zp Bs.G₀ := by
    rw [places_at_head h.toAtMg O]
    exact hp
  obtain ⟨Pp, n, hP, hn⟩ := nums_of_head h O hp
  have hin : ShareIn (switchShareAt A.B cF.blocksInOrder 0 Zp Bs.G₀ (rowsAt Zp Bs) (reader I Zp) S.rest)
      S.Oth := by
    rw [S.share]
    exact shareIn_add_left _ _
  have F := joinFit_full h O hA S.no (K1.lotData Sz.ref) S.Dd 0 (placeIn I Zp) S.own₀ (rowsAt Zp Bs)
    (reader I Zp) S.rest S.ch S.Jt S.stages S.own₂ S.n₀ S.ok S.codes S.sh S.sh₁ S.rest₂
  rw [← S.share] at F
  exact playsS_at_join h O hA hpS S.no (K1.lotData Sz.ref) S.Dd F hin S.cellsQ S.tokQ A.H test
    (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd Rd Kp w Said hP hn (half_base hA O hpS)
    (fun hV p' hp' => publicOk_of_reads h O (light_of_start h O (hst hV)) p' hp')

/-- **The member's step says yes.** -/
theorem k2Accepted : K2Accepted := by
  intro W₀ I Oh Z D r Zp Np cF x A Bs base hA h O Q test item n₁ n₂ b₀ Vd Rd Kp w Said hOk b q hb hq
    fall
  obtain ⟨p, hp, rfl⟩ := k2_place_at hb hq
  have hpS : p ∈ switchPlaces Zp Bs.G₀ := by
    rw [places_at_head h.toAtMg O]
    exact hp
  exact acceptedS_mono _ hOk
    (accepted_at_switch h O A.H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd Rd Kp w
      hp (half_base hA O hpS) rfl fall)

end AtFullSide.K2.Base

#print axioms AtFullSide.K2.Base.prepW_some
#print axioms AtFullSide.K2.Base.numsW_some
#print axioms AtFullSide.K2.Base.sortsW
#print axioms AtFullSide.K2.Base.nonZeroW
#print axioms AtFullSide.K2.Base.nums_of_head
#print axioms AtFullSide.K2.Base.accepted_at_switch
#print axioms AtFullSide.K2.Base.stored_below
#print axioms AtFullSide.K2.Base.k2Plays
#print axioms AtFullSide.K2.Base.k2Accepted
