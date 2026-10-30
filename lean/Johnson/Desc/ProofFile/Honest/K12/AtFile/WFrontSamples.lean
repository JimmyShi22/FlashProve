-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/WFrontSamples.lean: under the head, at the border behind the
first chain's last member: every stored sample row is Send.form at some seeds (SampleGood), so none
has a written-out factor. It carries goodS_at_354 (Johnson/AtFull/Shape/TakenRowsAt354.lean) over the four
members behind it: the proximity test, K13's batching, W's sending with the own group, the seal.

  keepsGood_sendAtS    a sending keeps the invariant, with no word on the factors of its seeds
  good_next            the invariant goes one member further along Reach
  keeps_at_354 to keeps_at_357   the four members
  sampleGood_at_358, samplesPlain_at_358   the statements, at a state reached under the test on words
  sampleGood_of_fold   the statement along a bare fold, at rounds in canonical form: no word on the
                       columns
  samplesPlain_of_good   such rows have no written-out factor

Limits.
- The two statements at border 358 speak of a state reached with the test on the words in front of
  each decision, as at border 354.
- The weaker invariant SampleGood: the proximity test's law on rows (RowsAcross.lean) has no word on a
  seed's factor.
- Nothing on the shared chain. Nothing on completeness, soundness or what is hidden.
-/
import Johnson.AtFull.Shape.TakenRowsDense
import Johnson.Desc.K12.Law.RowsAcross
import Johnson.Desc.K13.Law.RowsKept
import Johnson.Desc.K1.Law.RowsKeptPlan
import Johnson.IMR.SealSeat
import Johnson.Goal.Numbers.LengthsOkWritten
import Johnson.AtFull.Shape.Numbers
import Johnson.Top.H0.K2Hands.BothFrontS
import Johnson.Top.H0.K2Hands.SamplePre
import Johnson.Desc.ProofFile.Honest.Thread.SaidOk
import Johnson.P1K2R.FoldSide

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtFile
open OnBytes OnBytes.Slice
open VerifiableInference.Desc (Block Chain step_iff foldBlocks)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (QGood QGoodS SampleGood KeepsInv OkDrawn keepsInv_of_old
  keepsD_below)
open Johnson.AtFull.Shape (goodS_at_354)
open VerifiableInference.Desc.K1 (sendAtS)
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach)
open OnBytes.Maker (WholeD)
open P5J (AtMgA)

/-- **A sending keeps the invariant**, where the block passes its test on the plan and every code's
message length is a power of two. -/
theorem keepsGood_sendAtS {Cl : Type} (P : VerifiableInference.Desc.K1.Par)
    (hp : (sendAtS P : Block S Cl).planOk = true) (hl : P.codes.lengthsOk = true) :
    KeepsInv QGood (sendAtS P : Block S Cl) :=
  keepsInv_of_old (VerifiableInference.Desc.K1.keepsOld_sendAtS P) fun s s' rs gs hr hy => by
    obtain ⟨ids, d', h1, e1, _⟩ := VerifiableInference.Desc.K1.sendAtS_ok P s s' _ gs hy
    rw [e1]
    intro o y ho hy' hs
    exact (VerifiableInference.Desc.K1.decideSend_newP P
      (VerifiableInference.Desc.K1.planOwn_sendAtS hp) hl _
      (VerifiableInference.Desc.K1.stateOf s (#[] : Array ℕ)) d' rs ids hr h1 o y ho hy' hs).imp
      fun _ q => q.1

/-- The invariant goes one member further. -/
theorem good_next {bs : List (Block S ProofFile.Cl)} {start : ProofFile.InstPub → S} {n : ℕ} {z : ProofFile.InstPub}
    {s : S} (hK : ∀ b, bs[n]? = some b → KeepsInv QGood b)
    (hp : ∀ s₀, Reach 0 (bs.map below) start n (z, s₀) → SampleGood s₀.st)
    (hr : Reach 0 (bs.map below) start (n + 1) (z, s)) : SampleGood s.st := by
  cases hr with
  | @succ k z' s₀ s' b' hprev hb hy =>
    rw [List.getElem?_map] at hb
    obtain ⟨b, hb0, rfl⟩ := Option.map_eq_some_iff.1 hb
    obtain ⟨R, c, -, hs⟩ := hy
    obtain ⟨_, hd, _⟩ := (step_iff 0 (below b) s₀ s R c _).1 hs
    exact keepsD_below (hK b hb0) s₀ s _ _ (fun _ _ => trivial) hd (hp _ hprev)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

theorem keeps_at_354 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (b : Block S ProofFile.Cl)
    (hb : cF.blocksInOrder[354]? = some b) : KeepsInv QGood b := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨-, ⟨b₀, b', e1, -, rfl, hla⟩, -, -⟩ := IM.back_of O
  have q := (IM.back_numbers h.scope h.reads O).1 1 b₀ e1
  obtain rfl : ({ b₀ with planOk := b₀.planOk && b₀.hasNoClaimsAndNothingAfter } : Block S ProofFile.Cl) = b :=
    Option.some.inj (q.symm.trans hb)
  intro s s' rs gs hr hd hs
  have hd' : b₀.decide s rs gs = .ok s' := hd
  have hy := ((IM.yes_alone hla (by simp) s s' rs gs).1 hd').1
  exact H2K.Out.atFinish_good _ s s' rs gs hr hy hs

theorem keeps_at_355 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (b : Block S ProofFile.Cl)
    (hb : cF.blocksInOrder[355]? = some b) : KeepsInv QGood b := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨-, -, ⟨b₀, b', e1, -, rfl, hla⟩, -⟩ := IM.back_of O
  have q := (IM.back_numbers h.scope h.reads O).1 2 b₀ e1
  obtain rfl : ({ b₀ with planOk := b₀.planOk && b₀.hasNoClaimsAndNothingAfter } : Block S ProofFile.Cl) = b :=
    Option.some.inj (q.symm.trans hb)
  intro s s' rs gs hr hd hs
  have hd' : b₀.decide s rs gs = .ok s' := hd
  have hy := ((IM.yes_alone hla (by simp) s s' rs gs).1 hd').1
  exact VerifiableInference.Desc.K13.Law.keepsInv_atM3 _ s s' rs gs hr hy hs

theorem keeps_at_356 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (b : Block S ProofFile.Cl)
    (hb : cF.blocksInOrder[356]? = some b) : KeepsInv QGood b := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨-, -, -, ⟨b₀, b', w, e1, -, hw, rfl, hla⟩⟩ := IM.back_of O
  have q := (IM.back_numbers h.scope h.reads O).1 3 b₀ e1
  obtain rfl : ({ b₀ with planOk := b₀.planOk && b₀.hasNoClaimsAndNothingAfter } : Block S ProofFile.Cl) = b :=
    Option.some.inj (q.symm.trans hb)
  have hpl := Johnson.AtFull.Shape.plans_at h _ (List.mem_of_getElem? hb)
  have hpl' : b₀.planOk = true := (Bool.and_eq_true _ _ ▸ hpl).1
  rw [IM.alone_planOk hla] at hpl'
  have hl : Zp.first.codes.lengthsOk = true :=
    VerifiableInference.Desc.K13.Law.lengthsOk_of_pub O.pub
  unfold VerifiableInference.Desc.K13.wBlock VerifiableInference.Desc.K1.wAt at hw
  obtain ⟨msg, -, rfl⟩ := Option.map_eq_some_iff.1 hw
  have hwp : (sendAtS (VerifiableInference.Desc.K1.parW Zp.first
      { samples := Zp.P.samples, firstTree := Zp.P.firstTree } 4 msg) : Block S Unit).planOk =
      true := by
    have e : _ := hpl'
    simp only [VerifiableInference.Desc.K13.atM4, Block.retype, Block.andThen, Bool.and_eq_true,
      List.isEmpty_iff, beq_iff_eq] at e
    simp at e
    exact e.1.1
  intro s s' rs gs hr hd hs
  have hd' : b₀.decide s rs gs = .ok s' := hd
  have hy := ((IM.yes_alone hla (by simp) s s' rs gs).1 hd').1
  exact VerifiableInference.Desc.K13.Law.keepsInv_atM4 _ _
    (keepsGood_sendAtS _ hwp hl) s s' rs gs hr hy hs

theorem keeps_at_357 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (b : Block S ProofFile.Cl)
    (hb : cF.blocksInOrder[357]? = some b) : KeepsInv QGood b := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨b', -, rfl, hla⟩ := IM.seal_seated O
  have q := (IM.back_numbers h.scope h.reads O).2
  obtain rfl : ({ cF.last with planOk := cF.last.planOk && cF.last.hasNoClaimsAndNothingAfter } : Block S ProofFile.Cl) = b :=
    Option.some.inj (q.symm.trans hb)
  intro s s' rs gs hr hd hs
  have hd' : cF.last.decide s rs gs = .ok s' := hd
  have hy := ((IM.yes_alone hla (by simp) s s' rs gs).1 hd').1
  exact (VerifiableInference.Desc.K13.Law.keepsInv_chainEnd (Cl := Unit) (Q := QGood) 1 5 true
    (VerifiableInference.Desc.K13.inFrontOf Zp) VerifiableInference.Desc.First.endAsks)
    s s' rs gs hr hy hs

/-- **Behind the first chain's last member every stored sample row is Send.form at some seeds.** -/
theorem sampleGood_at_358 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {p : ProofFile.InstPub} {s : S}
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) 358 (p, s)) : SampleGood s.st :=
  good_next (keeps_at_357 h) (fun _ h1 => good_next (keeps_at_356 h) (fun _ h2 =>
    good_next (keeps_at_355 h) (fun _ h3 => good_next (keeps_at_354 h) (fun _ h4 =>
      (goodS_at_354 h h4).good) h3) h2) h1) hr

/-- **The same along a bare fold over the whole list**, at rounds whose drawn elements are in canonical
form. -/
theorem sampleGood_of_fold (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {pI : ProofFile.InstPub} {e : S}
    {rs r₀ : List Fmt.RoundView} {cols c₀ : List VerifiableInference.Desc.OpenedColumn}
    (hv : ∀ y ∈ rs, OkDrawn y)
    (hf : foldBlocks 0 cF.blocksInOrder (ProofFile.startS Zp pI) rs cols = .ok (e, r₀, c₀)) : SampleGood e.st := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hlen : cF.blocksInOrder.length = 358 := Johnson.AtFull.Shape.flat_len h
  obtain ⟨Z', c', A', B', hZ, hE, -, hl, hall⟩ :=
    VerifiableInference.Desc.First.K2.keepsBoth_front h.laid.value h.laid.planOk
  obtain rfl : Zp = Z' := Except.ok.inj (O.pub.symm.trans hZ)
  obtain rfl : cF = c' := P1K2.chain_of_desc (O.desc.symm.trans hE)
  have hfront : ∀ b ∈ cF.blocksInOrder.take 353, KeepsInv QGoodS b :=
    (hall 353 (by rw [Meaning.K2.front_len h.scope h.reads O])).good
  have hpre : ∀ b ∈ cF.blocksInOrder.take 354, KeepsInv QGoodS b := by
    intro b hb
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hb
    rw [List.getElem?_take] at hi
    split at hi
    · rename_i hi'
      by_cases e353 : i = 353
      · subst e353
        exact Johnson.AtFull.Shape.finish_keeps_good h hi
      · refine hfront b (List.mem_iff_getElem?.2 ⟨i, ?_⟩)
        rw [List.getElem?_take, if_pos (by omega)]
        exact hi
    · cases hi
  have hpost : ∀ b ∈ cF.blocksInOrder.drop 354, KeepsInv QGood b := by
    intro b hb
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hb
    rw [List.getElem?_drop] at hi
    have hlt : 354 + i < 358 := by
      rw [← hlen]
      exact (List.getElem?_eq_some_iff.1 hi).1
    have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl
    · exact keeps_at_354 h b hi
    · exact keeps_at_355 h b hi
    · exact keeps_at_356 h b hi
    · exact keeps_at_357 h b hi
  rw [← List.take_append_drop 354 cF.blocksInOrder] at hf
  obtain ⟨t, r₁, c₁, f1, f2⟩ := Johnson.Desc.First.Walk.Tied.fold_split 0 _ _ _ _ _ _ hf
  have g0 : VerifiableInference.Desc.First.K2.RowsInv QGoodS (ProofFile.startS Zp pI).st :=
    LTPile.rowsInv_startS hZ _ pI
  have g1 := VerifiableInference.Desc.First.K2.inv_at_pre hpre hv f1 g0
  have g2 : VerifiableInference.Desc.First.K2.RowsInv QGood t.st :=
    VerifiableInference.Desc.First.K2.SampleGoodS.good g1
  exact VerifiableInference.Desc.First.K2.inv_at_pre hpost
    (fun y hy => hv y ((ProofFile.Honest.fold_left 0 _ _ _ _ _ _ _ f1).1 y hy)) f2 g2

/-- A statement whose sample rows are Send.form at some seeds has no written-out factor in them. -/
theorem samplesPlain_of_good {T : Statement} (h : SampleGood T) :
    Johnson.AtFull.Shape.SamplesPlain T := by
  intro o y hy row hrow
  have hs : y.sampleRows.size ≠ 0 := by
    intro e
    have : y.sampleRows.toList = [] := by
      rw [← List.length_eq_zero_iff]
      simpa using e
    rw [this] at hrow
    cases hrow
  obtain ⟨seeds, hA⟩ := h o y hy hs
  exact Johnson.AtFull.Shape.plain_of_rowsAre hA row hrow

/-- **So no stored sample row has a written-out factor there.** -/
theorem samplesPlain_at_358 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {p : ProofFile.InstPub} {s : S}
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) 358 (p, s)) :
    Johnson.AtFull.Shape.SamplesPlain s.st :=
  samplesPlain_of_good (sampleGood_at_358 h hr)

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.keepsGood_sendAtS
#print axioms ProofFile.Honest.K12.AtFile.sampleGood_at_358
#print axioms ProofFile.Honest.K12.AtFile.samplesPlain_at_358
#print axioms ProofFile.Honest.K12.AtFile.sampleGood_of_fold
#print axioms ProofFile.Honest.K12.AtFile.samplesPlain_of_good
