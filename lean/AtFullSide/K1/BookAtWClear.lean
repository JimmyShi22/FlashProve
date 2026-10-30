-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/BookAtWClear.lean: the shared "sending" (the kind K1): THE BOOK's SIDE AT W's SENDER (the
owner ⟨⟨1, none, 4, .K1⟩, 0⟩), WHOLE, AND SO AT 51 OF THE 52 SENDERS: in scope, where the gate accepts,
at the book that the maker onlineProverFromPublicFiles returns, at any filling and every order of places, the premise on
the book of handIn_at_return (Johnson/Desc/ProofFile/Honest/K1/Sim/AtFill.lean) holds at W's sender;
with clear_at_later (AtFullSide/K1/BookAtIdle.lean): at every job of the 52 but the opening's. Public
data alone: entries, addresses, numbers. Four theorems; no definition.

  spent_w_only       at a book with the written entries nobody but ⟨⟨3, none, 2, .K12⟩, 0⟩ spends a
                     coin of W's sender
  clear_w_head       under the library's head: SpendersClearAny at W's job, at every such book: that
                     one address spends the 11 coefficients of the table that rides (FoldSpenderAny);
                     what is known there ends in front of them
  clear_at_w         the same at the maker's own book
  clear_but_opening  AT 51 OF THE 52 JOBS

By what. aheadW_four, book_at_w (AtFullSide/K1/BookAtW.lean); w_tail_from
(Honest/K1/Law/FreshAtPAtW.lean); parW_written, msg_w_head (Honest/K1/Law/FitsAtW.lean);
ahead_at_return, clear_at_later (BookAtIdle.lean).

Limits. THE OPENING's SENDER IS NOT HERE: it lends the most, and until the premise is paid there Good
is not had at its row. All limits of the files named. The full size alone; the format's second hash function
alone. In the side library, because it imports files of it. No property of the protocol is claimed.
-/
import AtFullSide.K1.BookAtW
import AtFullSide.K1.BookAtIdle
import Johnson.Desc.ProofFile.Honest.K1.Law.FreshAtPAtW

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K1
open OnBytes OnBytes.Slice OnBytes.Means VerifiableInference.Desc
open VerifiableInference.Desc (Chain Block)
open VerifiableInference.Desc.K13.Law (wMsgFull)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS F0T)
open ProofFile (Inst Pub Ground)
open ProofFile.Honest ProofFile.Honest.K1 ProofFile.Honest.K1.Sim ProofFile.Honest.K14
open AtFullSide.K14
open OnBytes.SendSim.At OnBytes.SendSim.Seat

/-- **Nobody but ⟨⟨3, none, 2, .K12⟩, 0⟩ spends a coin of W's sender.** -/
theorem spent_w_only {B : ProverCoinCounts} (hB : B.ahead = rawAheadW) {p : Addr}
    (hp : p ≠ ⟨⟨3, none, 2, .K12⟩, 0⟩) : B.spentBy ⟨⟨1, none, 4, .K1⟩, 0⟩ p = [] := by
  have h4 := aheadW_four
  rw [← hB] at h4
  unfold ProverCoinCounts.spentBy
  rw [List.filter_eq_nil_iff]
  intro e he hc
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨ho, hs⟩, h1⟩ := hc
  have hm : e ∈ B.ahead.filter (·.owner == (⟨⟨1, none, 4, .K1⟩, 0⟩ : Addr)) :=
    List.mem_filter.2 ⟨he, beq_iff_eq.2 ho⟩
  rw [h4] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact hp hs.symm
  · exact Bool.noConfusion h1
  · exact Bool.noConfusion h1
  · exact Bool.noConfusion h1

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
  {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)}
  (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
    (_root_.Desc.K14.Law.seatZ Zp Np) (_root_.Desc.K14.Law.secondAt Zp Np))
include h O

/-- **Under the head: the premise on the book at W's job**, at every book with the written entries,
at every order of places. -/
theorem clear_w_head {X Xi : Type} (no : Place → Nat) (Dd : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi)
    {J : SendJob (PlaceIn Xi) X} (hJ : J ∈ wJobs no Dd Zp Bs.G₀) {B : ProverCoinCounts}
    (hB : B.ahead = rawAheadW) (ord : List Place) :
    SpendersClearAny J.P J.ride B ord ⟨J.P.place, 0⟩ := by
  have hJe : J = wJobAt Zp.first (wGp Zp) 4 wMsgFull (no ⟨1, none, 4, .K1⟩) (Dd Zp Bs.G₀) := by
    have hJ' := hJ
    unfold wJobs at hJ'
    rw [msg_w_head h O] at hJ'
    simpa using hJ'
  subst hJe
  show SpendersClearAny (K1.parW Zp.first (wGp Zp) 4 wMsgFull) (rideOf (wFold Zp.first.lin)) B ord
    ⟨⟨1, none, 4, .K1⟩, 0⟩
  intro p hp
  by_cases hpp : p = ⟨⟨3, none, 2, .K12⟩, 0⟩
  swap
  · exact absurd (spent_w_only hB hpp) hp
  subst hpp
  obtain ⟨⟨e, hSp, hc, hs⟩, ⟨y, hKn, hys, hyc⟩⟩ := book_at_w hB ord
  have hdue : dueR (K1.parW Zp.first (wGp Zp) 4 wMsgFull) (rideOf (wFold Zp.first.lin)) =
      ⟨0, 4003⟩ := by
    rw [parW_written h O,
      (K13.Law.likeFull_in_scope h.scope h.laid.pub (K1.pin1_atAll h)).lin]
    decide +kernel
  have hst : maskStart (K1.parW Zp.first (wGp Zp) 4 wMsgFull)
      (rideOf (wFold Zp.first.lin)) 1 = 3882 := by
    rw [parW_written h O,
      (K13.Law.likeFull_in_scope h.scope h.laid.pub (K1.pin1_atAll h)).lin]
    decide +kernel
  have hrd : rideOf (wFold Zp.first.lin) 1 = some ⟨5, 1⟩ := by
    rw [(K13.Law.likeFull_in_scope h.scope h.laid.pub (K1.pin1_atAll h)).lin]
    decide +kernel
  have hs' : e.start.e = 3882 := by rw [hs]
  have hK : ∀ i ∈ eAll (B.knownBy ord ⟨⟨1, none, 4, .K1⟩, 0⟩ ⟨⟨3, none, 2, .K12⟩, 0⟩),
      i < 3882 := by
    intro i hi
    rw [hKn] at hi
    have h1 : i ∈ eOf y := by simpa [eAll] using hi
    have h2 := (Finset.mem_Ico.1 h1).2
    rw [hys, hyc] at h2
    omega
  refine ⟨?_, Or.inr (Or.inr ⟨⟨1, ⟨5, 1⟩, e, ?_, hrd, hSp, hc, hs'.trans hst.symm, ?_⟩, ?_⟩)⟩
  · intro a ha
    rw [hSp, hKn] at ha
    rw [hdue]
    rcases ha with ha | ha
    · rw [List.mem_singleton.1 ha, hs, hc]
      exact ⟨by decide, by decide⟩
    · rw [List.mem_singleton.1 ha, hys, hyc]
      exact ⟨by decide, by decide⟩
  · show 1 < (K1.parW Zp.first (wGp Zp) 4 wMsgFull).sent.size
    rw [parW_written h O]
    decide +kernel
  · intro ρ _ q _ hmem
    exact absurd (hK _ hmem) (Nat.not_lt.2 (w_tail_from h O ρ q))
  · refine Finset.disjoint_left.2 fun i hi hk => ?_
    rw [hSp] at hi
    have h1 : i ∈ eOf e := by simpa [eAll] using hi
    have h2 := (Finset.mem_Ico.1 h1).1
    have h3 := hK i hk
    omega

end

/-- **THE PREMISE ON THE BOOK AT W's SENDER, AT THE MAKER's OWN BOOK**, at every order of places. -/
theorem clear_at_w {W₀ Rc Tr X₀ X : Type} {Z : VerifierAndGoals.PublicFiles} (hS : VerifierAndGoals.InScope Z = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true) (Dd : Pub → Ground → RowDataOf Inst)
    {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) (ord : List Place) :
    ∀ J ∈ wJobs (X := Unit) (lotNo OnBytes.secondHashFunction A.Z) Dd A.Z A.G,
      SpendersClearAny J.P J.ride A.B ord ⟨J.P.place, 0⟩ := by
  obtain ⟨pp, hR⟩ := H2K.Sizes.inScope_readFiles hS
  obtain ⟨Zp, Np, cF, x, h⟩ := P5J.head_exists_at_name Z hS hR hL (P5J.owed_of_live hL)
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨m, -⟩ := K5.parts_of_atPure hA
  have eZ : A.Z = Zp := Except.ok.inj (m.pub.symm.trans O.pub)
  have eG : A.G = Bs.G₀ := by
    have g := m.ground
    rw [eZ] at g
    exact Option.some.inj (g.symm.trans O.blank)
  intro J hJ
  rw [eZ, eG] at hJ
  exact clear_w_head h O _ Dd hJ (ahead_at_return hS hL hA) ord

/-- **AT 51 OF THE 52 JOBS THE PREMISE ON THE BOOK HOLDS AT THE MAKER's OWN BOOK**: at every job but
the opening's. -/
theorem clear_but_opening {W₀ Rc Tr X₀ X : Type} {Z : VerifierAndGoals.PublicFiles} (hS : VerifierAndGoals.InScope Z = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) (ord : List Place) :
    ∀ J ∈ k1Jobs OnBytes.secondHashFunction S O A.Z A.G, J.P.place ≠ ⟨1, some 0, 1, .K1⟩ →
      SpendersClearAny J.P J.ride A.B ord ⟨J.P.place, 0⟩ := by
  intro J hJ hne
  rcases List.mem_append.1 hJ with hJ | hJ
  · have hc : J ∈ placeJob (X := Unit) (K1.firstPar A.G.first (K1.gpOf A.Z))
        (lotNo OnBytes.secondHashFunction A.Z ⟨1, some 0, 1, .K1⟩) (firstFold A.G.first) (lotData S A.Z A.G) ::
        (lotJobs (X := Unit) (lotNo OnBytes.secondHashFunction A.Z) (lotData S) A.Z A.G).tail := hJ
    rcases List.mem_cons.1 hc with rfl | ht
    · exact absurd rfl hne
    · exact clear_at_later hS hL S hA ord J ht
  · exact clear_at_w hS hL _ hA ord J hJ

end AtFullSide.K1

#print axioms AtFullSide.K1.spent_w_only
#print axioms AtFullSide.K1.clear_w_head
#print axioms AtFullSide.K1.clear_at_w
#print axioms AtFullSide.K1.clear_but_opening
