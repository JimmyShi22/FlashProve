-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K8/KeepsBehind.lean: the debt «behind» at the smallness test's draw (the kind K8, 25 places),
at the first chain's letters with the list csHead and the family fHeadJ.

  k8_number         a place of the kind stands at the draw's number of a segment
  k8_draws          at each segment's draw number stands a place of the kind
  k8_draw_yes       the member's step is the draw's decision, with no mark behind
  k8_riders_behind  the clauses of csHead that speak behind the draw: those that spoke in front, and
                    at number 343 the clause that the draw lays
  k8_behindS        BehindS: the form, the riders and the kind's clause of fHeadJ, at every Said

Limits. The library's head is a premise. Nothing here says that the member accepts.
-/
import Johnson.Desc.ProofFile.Honest.K8.Law.FormBehind
import Johnson.Desc.ProofFile.Honest.Thread.FHeadJ
import Johnson.Desc.ProofFile.Honest.Thread.CsHead
import Johnson.Desc.ProofFile.Honest.Thread.KeepsBy
import Johnson.Desc.K8.Honest.KeepsMark
import Johnson.Desc.K8.Honest.KeepsHead
import Johnson.Desc.K8.Honest.KeepsFold
import Johnson.Desc.First.K8.LawFunsStay
import Johnson.IMR.HandsReach

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K8.Term
open VerifiableInference.Desc (Block Chain KindName Place Strs)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K8 (drawAt approximateRangeProofDrawKind atS Seats Par putTl_own)
open VerifiableInference.Desc.First.K8.Honest (K8Keeps K8KeepsM keeps_of_decide keeps_lay keeps_att)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K8 (k8_sits_head k8_form_at)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

set_option maxRecDepth 1000000 in
/-- The written list has 358 places, and a place of the kind stands at a draw's number. -/
theorem k8_numbers : P5J.At.ps.length = 358 ∧ ((List.range 358).all fun b =>
    (P5J.At.ps[b]?).all fun p => p.kind != KindName.K8 ||
      (List.range 25).any fun l => b == drawAt l) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The converse: at each segment's draw number stands a place of the kind. So the kind's borders
are the 25 draws. -/
theorem k8_draws : ((List.range 25).all fun l =>
    (P5J.At.ps[drawAt l]?).map (·.kind) == some KindName.K8) = true := by
  decide +kernel

/-- **A place of the kind stands at the draw's number of a segment.** -/
theorem k8_number {b : Nat} {pl : Place} (ha : P5J.At.ps[b]? = some pl)
    (hk : pl.kind = KindName.K8) : ∃ l, l ≤ 24 ∧ b = drawAt l := by
  have hb : b < 358 := by
    have e := (List.getElem?_eq_some_iff.1 ha).1
    rw [k8_numbers.1] at e
    exact e
  have t := List.all_eq_true.1 k8_numbers.2 b (List.mem_range.2 hb)
  rw [ha] at t
  simp only [Option.all_some, hk, bne_self_eq_false, Bool.false_or, List.any_eq_true,
    List.mem_range, beq_iff_eq] at t
  obtain ⟨l, hl, e⟩ := t
  exact ⟨l, by omega, e⟩

/-- **The member's step is the draw's decision, with no mark behind.** -/
theorem k8_draw_yes (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : Nat} (hl : l ≤ 24)
    {blk : Block TS ProofFile.Cl} (hblk : cF.blocksInOrder[drawAt l]? = some blk) {s s' : TS}
    (hyes : IM.Yes 0 blk s s') :
    ∃ (p : Par) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))),
      (approximateRangeProofDrawKind (Cl := ProofFile.Cl) atS p).decide s rs gs = .ok s' ∧ s'.failed = none := by
  obtain ⟨Bs, base0, O⟩ := h.laid.opened
  obtain ⟨Lk, B, Xl, -, -, hB, e3, -, hSe, -, -⟩ := k8_sits_head h O hl
  have hB' : cF.blocksInOrder[drawAt l]? = some B := by
    rw [P1K8T.drawAt_place]
    exact hB
  obtain rfl : B = blk := Option.some.inj (hB'.symm.trans hblk)
  obtain ⟨rs, gs, hd⟩ := Johnson.Desc.First.Walk.Tied.stepYes_decide (IM.yes_stepYes hyes)
  obtain ⟨hdraw, h1⟩ := (hSe.2 s _ _ s').1 hd
  exact ⟨_, _, _, hdraw, h1⟩

/-- The draw's number, in two cases. -/
theorem drawAt_cases (l : Nat) : (l = 24 ∧ drawAt l = 343) ∨ (l ≠ 24 ∧ drawAt l = 14 * l + 6) := by
  unfold drawAt
  by_cases e : l = 24
  · exact Or.inl ⟨e, by rw [if_pos e]⟩
  · exact Or.inr ⟨e, by rw [if_neg e]⟩

/-- **The clauses of csHead behind the draw.** A clause that speaks at the border behind spoke at
the border in front, and the draw leaves what it says, but for the clause on the count of folds at
number 343, which the draw lays. -/
theorem k8_riders_behind {W : Type} (ν : Nat) (st : Nat → S → Prop)
    (R : Nat → Option OnBytes.Model.Forest.Heard → Prop) {l : Nat} (hl : l ≤ 24) (v : W)
    {s s' : S} (hK : K8Keeps s s') (hR : ridersOf (csHead ν st R) (drawAt l) v s) :
    ridersOf (csHead ν st R) (drawAt l + 1) v s' := by
  intro c hc hlo hhi
  have hfront := hR c hc
  rcases (csHead_mem ν st R c).1 hc with
    ((((rfl | rfl | rfl | rfl | rfl | rfl | rfl) | ⟨l', hl', rfl⟩) | ⟨g, hg, rfl⟩) | ⟨g, hg, rfl⟩)
  · -- the head's x
    have a1 : 342 ≤ drawAt l + 1 := hlo
    have a2 : drawAt l + 1 ≤ 347 := hhi
    have hf : 342 ≤ drawAt l ∧ drawAt l ≤ 347 := by
      rcases drawAt_cases l with ⟨-, e⟩ | ⟨h2, e⟩ <;> omega
    obtain ⟨a, ha, hp⟩ := hfront hf.1 hf.2
    obtain ⟨a', ha', e1, -, -⟩ := hK.head a ha
    exact ⟨a', ha', by show a'.x.isSome = true; rw [e1]; exact hp⟩
  · -- the head's t
    have a1 : 343 ≤ drawAt l + 1 := hlo
    have a2 : drawAt l + 1 ≤ 348 := hhi
    have hf : 343 ≤ drawAt l ∧ drawAt l ≤ 348 := by
      rcases drawAt_cases l with ⟨-, e⟩ | ⟨h2, e⟩ <;> omega
    obtain ⟨a, ha, hp⟩ := hfront hf.1 hf.2
    obtain ⟨a', ha', -, e2, -⟩ := hK.head a ha
    exact ⟨a', ha', by show a'.t.isSome = true; rw [e2]; exact hp⟩
  · -- the head's wo
    have a1 : 347 ≤ drawAt l + 1 := hlo
    exfalso
    rcases drawAt_cases l with ⟨-, e⟩ | ⟨h2, e⟩ <;> omega
  · -- the head's F.next
    have a1 : 346 ≤ drawAt l + 1 := hlo
    exfalso
    rcases drawAt_cases l with ⟨-, e⟩ | ⟨h2, e⟩ <;> omega
  · -- the count of folds, laid here: the head's x says that the chain stands in the head's link
    have a1 : 344 ≤ drawAt l + 1 := hlo
    have a2 : drawAt l + 1 ≤ 345 := hhi
    have e343 : drawAt l = 343 := by
      rcases drawAt_cases l with ⟨-, e⟩ | ⟨h2, e⟩ <;> omega
    have hx := hR (riderHead 342 347 (fun a => a.x.isSome = true))
      ((csHead_mem ν st R _).2 (Or.inl (Or.inl (Or.inl (Or.inl rfl)))))
      (by show 342 ≤ drawAt l; omega) (by show drawAt l ≤ 347; omega)
    obtain ⟨a, ha, -⟩ := hx
    exact hK.fold0_head a ha
  · have a1 : 346 ≤ drawAt l + 1 := hlo
    exfalso
    rcases drawAt_cases l with ⟨-, e⟩ | ⟨h2, e⟩ <;> omega
  · have a1 : 346 ≤ drawAt l + 1 := hlo
    exfalso
    rcases drawAt_cases l with ⟨-, e⟩ | ⟨h2, e⟩ <;> omega
  · -- after a segment's lookup on the digits
    have a1 : 14 * l' + 9 ≤ drawAt l + 1 := hlo
    have a2 : drawAt l + 1 ≤ 14 * l' + 9 := hhi
    exfalso
    rcases drawAt_cases l with ⟨-, e⟩ | ⟨h2, e⟩ <;> omega
  · -- an attention segment's fact
    have a1 : 14 * (2 * g + 1) + 4 ≤ drawAt l + 1 := hlo
    have a2 : drawAt l + 1 ≤ 14 * (2 * g + 1) + 9 := hhi
    have hf : 14 * (2 * g + 1) + 4 ≤ drawAt l ∧ drawAt l ≤ 14 * (2 * g + 1) + 9 := by
      rcases drawAt_cases l with ⟨-, e⟩ | ⟨h2, e⟩ <;> omega
    obtain ⟨a, ha, hp⟩ := hfront hf.1 hf.2
    obtain ⟨tl', e⟩ := keeps_att hK ha
    exact ⟨_, e, hp⟩
  · -- a layers' segment's fact
    have a1 : 28 * g + 5 ≤ drawAt l + 1 := hlo
    have a2 : drawAt l + 1 ≤ 28 * g + 10 := hhi
    have hf : 28 * g + 5 ≤ drawAt l ∧ drawAt l ≤ 28 * g + 10 := by
      rcases drawAt_cases l with ⟨-, e⟩ | ⟨h2, e⟩ <;> omega
    obtain ⟨o, ho⟩ := hfront hf.1 hf.2
    obtain ⟨tl, cf, first, -, -, -, -, -, rfl⟩ := hK
    exact ⟨o, (putTl_own s _).trans ho⟩

/-- **The debt «behind» at a member of the kind**, at every Said. -/
theorem k8_behindS (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (ν : Nat) (st : Nat → TS → Prop)
    (R : Nat → Option OnBytes.Model.Forest.Heard → Prop) (G : ProofFile.Ground) (take : Nat → Bool)
    (P11 : Johnson.Desc.First.ForkMerge.HeadMergeP) (p12 : VerifiableInference.Desc.K12.P12)
    (P13 : VerifiableInference.Desc.K13.Where) (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    {b : Nat} {pl : Place} (ha : P5J.At.ps[b]? = some pl) (hk : pl.kind = KindName.K8) :
    BehindS (lettersHead h H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R))
      (kpBy (fHeadJ Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread Said b := by
  intro blk hblk k s m E ds y cols s' hT _ hS
  obtain ⟨l, hl, rfl⟩ := k8_number ha hk
  have hblk' : cF.blocksInOrder[drawAt l]? = some blk := hblk
  have hForm := k8_form_at h H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R))
    (kpBy (fHeadJ Zp cF G take P11 p12 P13 h.𝔇.pubD)) w hl blk hblk' k s m E ds y cols s' hT.1 hS
  have hyes : IM.Yes 0 blk s s' := ⟨roundsOf y.1, cols, cols.length, hS.2⟩
  obtain ⟨p, rs, gs, hdraw, h1⟩ := k8_draw_yes h hl hblk' hyes
  have hKM : K8KeepsM s s' := ⟨keeps_of_decide p hdraw, h1⟩
  have hThr := hT.1
  unfold Thr at hThr
  obtain ⟨-, -, -, -, -, hR, -⟩ := hThr
  have hp := head_place h H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R))
    (kpBy (fHeadJ Zp cF G take P11 p12 P13 h.𝔇.pubD)) w hblk
  have epl : pl = blk.place := Option.some.inj (ha.symm.trans hp)
  have hkb : blk.place.kind = KindName.K8 := epl ▸ hk
  -- the input stays
  have hS' := hS
  unfold Thread.Stepped Thread.Moved at hS'
  obtain ⟨⟨⟨l', -, hy⟩, -⟩, -⟩ := hS'
  obtain ⟨ei, -, -⟩ := play_mid _ _ _ _ _ hy
  refine ⟨hForm, ⟨fun hb => ?_, ?_⟩, ?_⟩
  · have hb' : 339 ≤ drawAt l := by
      rcases drawAt_cases l with ⟨-, e⟩ | ⟨h2, e⟩ <;> omega
    have hR₁ := head_reply h H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R))
      (kpBy (fHeadJ Zp cF G take P11 p12 P13 h.𝔇.pubD)) w hb' hR
    rw [ei, hKM.rest.2]
    exact hR₁
  · rw [ei]
    exact k8_riders_behind ν st R hl _ hKM.1 hR.2
  · refine (head_keeps_kind h H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R))
      (fHeadJ Zp cF G take P11 p12 P13 h.𝔇.pubD) w hblk hkb s s').2 ?_
    exact ⟨⟨⟨⟨⟨hKM, formsBehind_of_form h H Q test carryX item n₁ n₂ 339 Vd
      (ridersOf (csHead ν st R)) (kpBy (fHeadJ Zp cF G take P11 p12 P13 h.𝔇.pubD)) w hp hForm⟩,
      trivial⟩, trivial⟩, trivial⟩, trivial⟩

end AtFullSide.K8.Term

#print axioms AtFullSide.K8.Term.k8_numbers
#print axioms AtFullSide.K8.Term.k8_draws
#print axioms AtFullSide.K8.Term.k8_number
#print axioms AtFullSide.K8.Term.k8_draw_yes
#print axioms AtFullSide.K8.Term.drawAt_cases
#print axioms AtFullSide.K8.Term.k8_riders_behind
#print axioms AtFullSide.K8.Term.k8_behindS
