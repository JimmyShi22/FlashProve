-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K8/TailAtSorts.lean: the named tests on values of the smallness test behind the batching,
at a segment of each of the three sorts, at every state that the wrapped blocks reach and at which
the kind's share of these tests is silent.

  layers_seat_k4, att_seat, head_seat   what the library holds on a segment's seat, gathered
  held_lay, held_att, held_head         what holds behind the batching block's yes (BehindHeld)
  ledger_behind                         the ledger behind a yes has the slots of the ledger in front
  k8_rest_behind                        every guard beside the share, behind the run "K8.lsTail"
  k8_valsS_behind                       **the named tests accept there**
  valsS_free, k8_valsS_free             and behind the layers' run "free-slot", which leaves them

Limits. The scope, the files read, the opening and the description's test on its plan are premises.
The share's silence is a premise: it hangs on the drawn element, so it is a fall's. The laws speak of
every state that accepting steps reach, honest or not: the five tests beside the share follow from
the batching's yes, and no honest value is spent. Nothing here says that a run comes to such a state.
-/
import AtFullSide.K8.TailValues
import Johnson.P1K8R.FallAtSeatAtt
import Johnson.P1K8R.FallAtSeatHead
import Johnson.Desc.First.Batch.Law.AddAgrees
import Johnson.Desc.First.Batch.Law.Ledger
import Johnson.Desc.First.TailClaims.K8SitsMeet
import Johnson.Desc.K8.Honest.EqFront
import Johnson.Desc.K8.Honest.FallDraw
import Johnson.Desc.K8.Honest.LengthsAtPlans
import Johnson.AtFull.Shape.SeatsNamed

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K8.Term
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law (blank partOf sits_lsTail blank_lsTail part_set)
open VerifiableInference.Desc.First.TailClaims.Law.Tests
open VerifiableInference.Desc.First.K8.Honest
open VerifiableInference.Desc.Kinds.Head (callerReaders planesAt)
open VerifiableInference.Desc.Kinds.Head.Law.InScope (head_24)
open VerifiableInference.Desc.K9L (addAll_sizes addList_older)
open ProofFile.Honest.K8
open ProofFile.Honest.K9 (SeatedFree BatBehind free_at_seat_all behind_of_step batch_join drawnOne
  gathered_split draw_facts draw_iff)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)
open _root_.P1K8

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **A feed-forward segment's seat.** -/
theorem layers_seat_k4 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12) :
    ∃ (Lk : Link S Claim) (p4 : OnBytes.Desc.First.K4.Par) (X : LinkH),
      c.links[2 * g]? = some Lk ∧ LPFK9.k4ParAt Z Bs.G₀ (2 * g) = some p4 ∧
      Bs.G₀.built[2 * g]? = some X ∧ LinkJoin.LayersTies Lk p4 (ProofFile.k8NU Bs.G₀ X) ∧
      (∀ run, LinkJoin.At Lk (1, "objects") run → LinkJoin.Under run Desc.K9.objectsCalls) ∧
      (∀ run, LinkJoin.At Lk (6, "objects") run → LinkJoin.Under run Desc.K9.objectsDigits) ∧
      Lk.order = First.orderOf .layers := by
  have hl : 2 * g < 25 := by omega
  have h24 : 2 * g ≠ 24 := by omega
  have hsub : IM.subAt (2 * g) = .layers := by
    unfold IM.subAt
    rw [if_neg h24, if_pos (by omega)]
  obtain ⟨Lk, p, w, T, e1, e2, -, -, -, -, hb, -, -, -, -, hord, hordA, -⟩ :=
    (IM.k9_of hS hR O).2 (2 * g) hl
  have hs25 := IM.subs_scope hS hR O (2 * g) hl
  rw [hsub] at hs25 hord
  obtain ⟨Lk', p4, X, e1', hp, hX, ties⟩ :=
    LPFK9.layers_ties_at O.made O.places O.chain (2 * g) hs25
  obtain rfl : Lk = Lk' := Option.some.inj (e1.symm.trans e1')
  rw [Array.getElem?_toList] at hX
  refine ⟨Lk, p4, X, e1, hp, hX, ties, ?_, ?_, hord⟩
  · intro run hrun
    have hrun' : LinkJoin.At Lk (IM.k3Ix (2 * g) false, "objects") run := by
      simpa [IM.k3Ix, h24] using hrun
    rw [OnPublicFiles.at_objects_is hS hR O hl false e1 hrun', objectsRun_at.1]
    exact LinkJoin.under_refl _
  · intro run hrun
    have hrun' : LinkJoin.At Lk (IM.k3Ix (2 * g) true, "objects") run := by
      simpa [IM.k3Ix, h24] using hrun
    rw [OnPublicFiles.at_objects_is hS hR O hl true e1 hrun', objectsRun_at.2]
    exact LinkJoin.under_refl _

/-- **An attention segment's seat.** -/
theorem att_seat (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12) :
    ∃ (Lk : Link S Claim) (Ap : Attention.Plan) (X : LinkH),
      c.links[2 * g + 1]? = some Lk ∧ Bs.G₀.W.A[g]? = some Ap ∧
      Bs.G₀.built[2 * g + 1]? = some X ∧
      LinkJoin.AttTies Lk (Att.P.parCOf Ap) (ProofFile.k8NU Bs.G₀ X) ∧
      (∀ run, LinkJoin.At Lk (1, "objects") run → LinkJoin.Under run Desc.K9.objectsCalls) ∧
      (∀ run, LinkJoin.At Lk (6, "objects") run → LinkJoin.Under run Desc.K9.objectsDigits) ∧
      (∀ run, LinkJoin.At Lk (2, "join") run → LinkJoin.Under run
        (Desc.K9.joinCalls (Att.P.keysOfK (Att.P.seatCO (Att.P.parCOf Ap)) (Att.P.parCOf Ap)))) ∧
      (∀ run, LinkJoin.At Lk (1, "planes") run → ∃ lm, LinkJoin.Under run
        (Desc.K9.planesCalls lm
          (Att.P.readersOfK (Att.P.seatCO (Att.P.parCOf Ap)) (Att.P.parCOf Ap)))) ∧
      Lk.order = First.orderOf .attention := by
  have hl : 2 * g + 1 < 25 := by omega
  have h24 : 2 * g + 1 ≠ 24 := by omega
  have hsub : IM.subAt (2 * g + 1) = .attention := by
    unfold IM.subAt
    rw [if_neg h24, if_neg (by omega)]
  obtain ⟨Lk, p, w, T, e1, e2, -, -, -, -, hb, -, -, -, -, hord, hordA, -⟩ :=
    (IM.k9_of hS hR O).2 (2 * g + 1) hl
  have hs25 := IM.subs_scope hS hR O (2 * g + 1) hl
  rw [hsub] at hs25 hord
  obtain ⟨Lk', Xl, Ap, X, e1', hXl, -, hA, hX, ties⟩ :=
    LPFK9.att_ties_at O.made O.places O.chain (2 * g + 1) hs25
  obtain rfl : Lk = Lk' := Option.some.inj (e1.symm.trans e1')
  obtain ⟨h4, g', hg', e⟩ := Att.P.att_only O.pub O.blank hs25
  obtain rfl : g = g' := by omega
  obtain ⟨Xl', hXl', -, hgX, -⟩ := Att.P.built_att O.pub O.blank h4 hg'
  obtain rfl : Xl' = Xl := Option.some.inj (hXl'.symm.trans hXl)
  rw [hgX] at hA
  rw [Array.getElem?_toList] at hX
  refine ⟨Lk, Ap, X, e1, hA, hX, ties, ?_, ?_, ?_, ?_, hord⟩
  · intro run hrun
    have hrun' : LinkJoin.At Lk (IM.k3Ix (2 * g + 1) false, "objects") run := by
      simpa [IM.k3Ix, h24] using hrun
    rw [OnPublicFiles.at_objects_is hS hR O hl false e1 hrun', objectsRun_at.1]
    exact LinkJoin.under_refl _
  · intro run hrun
    have hrun' : LinkJoin.At Lk (IM.k3Ix (2 * g + 1) true, "objects") run := by
      simpa [IM.k3Ix, h24] using hrun
    rw [OnPublicFiles.at_objects_is hS hR O hl true e1 hrun', objectsRun_at.2]
    exact LinkJoin.under_refl _
  · intro run hrun
    rw [LinkJoin.at_join_is O h4 hg' hA e1 hrun]
    exact LinkJoin.under_refl _
  · intro run hrun
    have hrun' : LinkJoin.At Lk (IM.k3Ix (2 * g + 1) false, "planes") run := by
      simpa [IM.k3Ix, h24] using hrun
    obtain ⟨q, -, rfl⟩ :=
      OnPublicFiles.at_planes_is hS hR O hl e1 (H2K5.Door.readersAt_att h4 hA) hrun'
    exact ⟨q.lm, LinkJoin.under_refl _⟩

/-- **The head's segment's seat.** -/
theorem head_seat (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∃ (Lk : Link S Claim) (X : LinkH), c.links[24]? = some Lk ∧ Bs.G₀.built[24]? = some X ∧
      LinkJoin.HeadTies Lk Bs.G₀.W.hS 0 (Bs.G₀.built.size - 1) 4
        (Kinds.Head.parOf Bs.G₀.W.hS (Kinds.Head.Law.workAtW Bs.G₀.W)) (ProofFile.k8NU Bs.G₀ X) ∧
      (∀ run, LinkJoin.At Lk (2, "objects") run → LinkJoin.Under run Desc.K9.objectsCalls) ∧
      (∀ run, LinkJoin.At Lk (7, "objects") run → LinkJoin.Under run Desc.K9.objectsDigits) ∧
      (∀ run, LinkJoin.At Lk (2, "planes") run →
        ∃ lm, LinkJoin.Under run (Desc.K9.planesCalls lm (callerReaders (planesAt 0)))) ∧
      Lk.order = First.orderOf .head := by
  have hl : 24 < 25 := by omega
  have hsub : IM.subAt 24 = .head := rfl
  obtain ⟨Lk, p, w, T, e1, e2, -, -, -, -, hb, -, -, -, -, hord, hordA, -⟩ :=
    (IM.k9_of hS hR O).2 24 hl
  have hs25 := IM.subs_scope hS hR O 24 hl
  rw [hsub] at hs25 hord
  have hU3 := head_u3 O.public
  obtain ⟨Lk', X, e1', hX, ties⟩ := LPFK9.head_ties_at O.made O.places O.chain 24 hs25 0 hU3
  obtain rfl : Lk = Lk' := Option.some.inj (e1.symm.trans e1')
  obtain ⟨h4, hN⟩ := head_24 hS O.public
  have hH : K3.isHead Bs.G₀.W 24 = true := by
    unfold K3.isHead
    rw [h4, hN]
    rfl
  rw [Array.getElem?_toList] at hX
  refine ⟨Lk, X, e1, hX, ties, ?_, ?_, ?_, hord⟩
  · intro run hrun
    have hrun' : LinkJoin.At Lk (IM.k3Ix 24 false, "objects") run := hrun
    rw [OnPublicFiles.at_objects_is hS hR O hl false e1 hrun', objectsRun_at.1]
    exact LinkJoin.under_refl _
  · intro run hrun
    have hrun' : LinkJoin.At Lk (IM.k3Ix 24 true, "objects") run := hrun
    rw [OnPublicFiles.at_objects_is hS hR O hl true e1 hrun', objectsRun_at.2]
    exact LinkJoin.under_refl _
  · intro run hrun
    have hrun' : LinkJoin.At Lk (IM.k3Ix 24 false, "planes") run := hrun
    obtain ⟨q, -, rfl⟩ := OnPublicFiles.at_planes_is hS hR O hl e1 (OnPublicFiles.readersAt_head hH hU3) hrun'
    exact ⟨q.lm, LinkJoin.under_refl _⟩


/-- **Behind the batching, at a feed-forward segment.** -/
theorem held_lay (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {g : ℕ} (hg : g < 12) {Lk : Link S Claim} (hLk : c.links[2 * g]? = some Lk) {Xl : LinkH}
    (e3 : Bs.G₀.built[2 * g]? = some Xl) (p : K9.Where) {z : ProofFile.InstPub} {s t' : S}
    (hw : Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z)
      (14 * (2 * g) + (if 2 * g = 24 then 11 else 9)) (z, s))
    {tl : HTailF2} (ht : s.tl? = some tl) (d : Fmt.Drawn)
    (hbt : (K9.batch K9.atS p (claimsInBy Lk.each Lk.hear Lk.order)).decide s [⟨[], d⟩] [] =
      .ok t') : BehindHeld tl t' := by
  obtain ⟨Lk', p4, X', e1, hp, hX, ties, tC, tD, hord⟩ := layers_seat_k4 hS hR O hg
  obtain rfl : Lk = Lk' := Option.some.inj (hLk.symm.trans e1)
  obtain rfl : Xl = X' := Option.some.inj (e3.symm.trans hX)
  obtain ⟨tl0, Fk, g0, nbW, Wn, ht0, hF, hg0, D⟩ := allFront_at_all hS hR O hOk (by omega) e3 hw
  obtain rfl : tl = tl0 := Option.some.inj (ht.symm.trans ht0)
  have r9 : Reach 0 c.blocksInOrder (ProofFile.startS Z) (28 * g + 9) (z, s) := by
    have r := reach_raw hw
    rw [if_neg (by omega), show 14 * (2 * g) + 9 = 28 * g + 9 by omega] at r
    exact r
  obtain ⟨funs, hf, -⟩ := LinkJoin.funsSkel_at_batch hS hR O hg r9
  have hT : ∀ a0, K9.atS.get? s = some a0 → a0.L.list.nt.size = Fk.trees.size :=
    fun a0 h0 => listSize_at_batch hS hR O (by omega) e3 (reach_raw hw) Fk a0 hF h0
  have asks := layAsks_at_wrap hS hR O hOk hg hp ⟨z, hw⟩ ht
  exact behindHeld_of (hord.trans lay_order) (lay_preOk Lk p4 _ ties tC tD)
    (lay_postOk Lk p4 _ ties) ties.tEq p s t' tl Fk funs ht hF hf d hbt
    (allHeld_at_layers Lk p4 _ ties tC tD hord p
      (fun u rs => (K9.batch K9.atS p (claimsInBy Lk.each Lk.hear Lk.order)).decide u rs [])
      s t' tl Fk funs (fun _ _ h => h) ht hF hf g0 hg0 nbW Wn D hT asks d hbt)

/-- **Behind the batching, at an attention segment.** -/
theorem held_att (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {g : ℕ} (hg : g < 12) {Lk : Link S Claim} (hLk : c.links[2 * g + 1]? = some Lk) {Xl : LinkH}
    (e3 : Bs.G₀.built[2 * g + 1]? = some Xl) (p : K9.Where) {z : ProofFile.InstPub} {s t' : S}
    (hw : Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z)
      (14 * (2 * g + 1) + (if 2 * g + 1 = 24 then 11 else 9)) (z, s))
    {tl : HTailF2} (ht : s.tl? = some tl) (d : Fmt.Drawn)
    (hbt : (K9.batch K9.atS p (claimsInBy Lk.each Lk.hear Lk.order)).decide s [⟨[], d⟩] [] =
      .ok t') : BehindHeld tl t' := by
  obtain ⟨Lk', Ap, X', e1, hA, hX, ties, tC, tD, tJ, tP, hord⟩ := att_seat hS hR O hg
  obtain rfl : Lk = Lk' := Option.some.inj (hLk.symm.trans e1)
  obtain rfl : Xl = X' := Option.some.inj (e3.symm.trans hX)
  obtain ⟨tl0, Fk, g0, nbW, Wn, ht0, hF, hg0, D⟩ := allFront_at_all hS hR O hOk (by omega) e3 hw
  obtain rfl : tl = tl0 := Option.some.inj (ht.symm.trans ht0)
  have r9 : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * (2 * g + 1) + 9) (z, s) := by
    have r := reach_raw hw
    rw [if_neg (by omega)] at r
    exact r
  obtain ⟨a', funs, -, hf, -⟩ := LinkJoin.attSkel_at_batch hS hR O hg r9
  have hT : ∀ a0, K9.atS.get? s = some a0 → a0.L.list.nt.size = Fk.trees.size :=
    fun a0 h0 => listSize_at_batch hS hR O (by omega) e3 (reach_raw hw) Fk a0 hF h0
  obtain ⟨asks, hU2, a, ha, hU⟩ := attAsks_at_wrap hS hR O hOk hg hA ⟨z, hw⟩ ht
  exact behindHeld_of (by rw [hord]; rfl) (att_pre Lk (Att.P.parCOf Ap) _ ties tC tD tJ tP)
    (post_nil Lk) ties.tEq p s t' tl Fk funs ht hF hf d hbt
    (allHeld_at_att Lk Ap _ ties tC tD tJ tP hord p
      (fun u rs => (K9.batch K9.atS p (claimsInBy Lk.each Lk.hear Lk.order)).decide u rs [])
      s t' tl Fk funs (fun _ _ h => h) ht hF hf g0 hg0 nbW Wn D hT asks a ha hU hU2 d hbt)

/-- **Behind the batching, at the head's segment.** -/
theorem held_head (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {Lk : Link S Claim} (hLk : c.links[24]? = some Lk) {Xl : LinkH}
    (e3 : Bs.G₀.built[24]? = some Xl) (p : K9.Where) {z : ProofFile.InstPub} {s t' : S}
    (hw : Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z)
      (14 * 24 + (if 24 = 24 then 11 else 9)) (z, s))
    {tl : HTailF2} (ht : s.tl? = some tl) (d : Fmt.Drawn)
    (hbt : (K9.batch K9.atS p (claimsInBy Lk.each Lk.hear Lk.order)).decide s [⟨[], d⟩] [] =
      .ok t') : BehindHeld tl t' := by
  obtain ⟨Lk', X', e1, hX, ties, tC, tD, tP, hord⟩ := head_seat hS hR O
  obtain rfl : Lk = Lk' := Option.some.inj (hLk.symm.trans e1)
  obtain rfl : Xl = X' := Option.some.inj (e3.symm.trans hX)
  obtain ⟨tl0, Fk, g0, nbW, Wn, ht0, hF, hg0, D⟩ := allFront_at_all hS hR O hOk (by omega) e3 hw
  obtain rfl : tl = tl0 := Option.some.inj (ht.symm.trans ht0)
  obtain ⟨funs, -, hf, -⟩ := LinkJoin.headSkel_at_batch hS hR O (z := z) (s' := s) (reach_raw hw)
  have hT : ∀ a0, K9.atS.get? s = some a0 → a0.L.list.nt.size = Fk.trees.size :=
    fun a0 h0 => listSize_at_batch hS hR O (by omega) e3 (reach_raw hw) Fk a0 hF h0
  obtain ⟨asks, hU2⟩ := headWants_at_wrap hS hR O hOk ⟨z, hw⟩ ht
  exact behindHeld_of (by rw [hord]; rfl) (head_pre Lk _ 0 _ 4 _ _ ties tC tD tP)
    (head_post Lk _ 0 _ 4 _ _ ties) ties.tEq p s t' tl Fk funs ht hF hf d hbt
    (allHeld_at_head Lk _ 0 _ 4 _ _ ties tC tD tP hord p
      (fun u rs => (K9.batch K9.atS p (claimsInBy Lk.each Lk.hear Lk.order)).decide u rs [])
      s t' tl Fk funs (fun _ _ h => h) ht hF hf g0 hg0 nbW Wn D hT asks hU2 d hbt)

/-- **The ledger behind a yes** has the number of slots of the ledger in front, and as many
coefficients as slots. -/
theorem ledger_behind {l k : ℕ} {Lk : Link S Claim} {p : K9.Where}
    {w : K9.SegSort × ℕ × K9.TWhere} (Sd : SeatedFree c Z l k Lk p w) {s t : S} {x : E}
    {y : S × K9.Part × List Claim} {G Fk : Fork}
    (hb : BatBehind p (claimsInBy Lk.each Lk.hear Lk.order) s x y G t) (hF : s.fork? = some Fk) :
    G.ns = Fk.ns ∧ G.LS.size = G.ns := by
  obtain ⟨t₁, hd, hg, he⟩ := gathered_split p _ s x y hb.gathered
  obtain ⟨a, ha, -⟩ := (draw_iff p s x).1 ⟨t₁, hd⟩
  obtain ⟨a₁, h1, f⟩ := draw_facts p s t₁ x a ha hd
  obtain ⟨a₂, h2, k⟩ := Sd.keeps t₁ y.1 y.2.2 a₁ hg h1
  obtain rfl : a₂ = y.2.1 := Option.some.inj (h2.symm.trans he)
  have hFa : a.F = Fk := Option.some.inj ((K9.get_fork s a ha).symm.trans hF)
  have hs := addAll_sizes y.2.2 y.2.1.F G (addList_older _ _ _ hb.added)
  have hn : y.2.1.F.ns = Fk.ns := by rw [k.ns, f.ns, hFa]
  refine ⟨hb.all.ns.trans hn, ?_⟩
  rw [hs.1, hb.all.ns, k.LS, k.ns, f.sized]

/-- **Every guard of the three tests beside the share, behind the run "K8.lsTail".** -/
theorem k8_rest_behind (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 25) {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) {z : ProofFile.InstPub} {s : S}
    (hw : Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z)
      (14 * l + (if l = 24 then 11 else 9) + 1) (z, s)) :
    ∃ (tl : HTailF2) (G : Fork), tlForkP.get? s = some (tl, G) ∧
      K8Rest (ProofFile.k8NU Bs.G₀ Xl) { tl with lsTail := G.LS.extract tl.slotA tl.slotB } G := by
  obtain ⟨Lk, p, w, Sd⟩ := free_at_seat_all hS hR O l hl
  have eb : 14 * l + (if l = 24 then 9 else 7) + 2 = 14 * l + (if l = 24 then 11 else 9) := by
    split <;> omega
  have hb : c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? =
      some (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)) := eb ▸ Sd.batching
  obtain ⟨s₀, Rs, cl, r0, -, hstep, -⟩ := reach_last_words hw hb
  obtain ⟨rr, tr, -, -, -, y, G, hbat, -, -⟩ := behind_of_step Sd 0 s₀ s Rs cl _ hstep
  have hyes : (K9.batch K9.atS p (claimsInBy Lk.each Lk.hear Lk.order)).decide s₀
      [⟨[], drawnOne (E.ofTriple tr)⟩] [] = .ok s := by
    rw [hbat.state]
    exact batch_join p _ s₀ _ y G hbat.gathered hbat.added
  obtain ⟨tlS, Fk, g0, nbW, Wn, ht, hF, hg0, D⟩ := allFront_at_all hS hR O hOk hl e3 r0
  have hH : BehindHeld tlS s := by
    by_cases h24 : l = 24
    · subst h24
      exact held_head hS hR O hOk Sd.link e3 p r0 ht _ hyes
    · rcases Nat.even_or_odd' l with ⟨g, rfl | rfl⟩
      · exact held_lay hS hR O hOk (by omega) Sd.link e3 p r0 ht _ hyes
      · exact held_att hS hR O hOk (by omega) Sd.link e3 p r0 ht _ hyes
  obtain ⟨tl', G', hget, hA, hP, hbl⟩ := hH
  obtain ⟨e1, e2⟩ := (tlFork_iff s tl' G').1 hget
  obtain rfl : G' = G := Option.some.inj (e2.symm.trans hbat.ledger)
  obtain ⟨hns, hsz⟩ := ledger_behind Sd hbat hF
  have hSt := static_at_batch hS hR O hl e3 (reach_raw r0) ht hF (static_at_built hS O hl e3)
  have hslot : tlS.slotB ≤ Fk.ns := by
    by_cases h24 : l = 24
    · subst h24
      exact slot_at_head_seg hS hR O hOk r0 ht hF
    · have r9 := reach_raw r0
      rw [if_neg h24] at r9
      exact slot_at_batch hS hR O hOk (by omega) r9 ht hF
  have hnU := lengths_lot_at_batch hS hR O hl e3 (reach_raw r0) ht
  refine ⟨tl', G', hget, ?_⟩
  have hb2 : ∀ u, blank u { tl' with lsTail := G'.LS.extract tl'.slotA tl'.slotB } = blank u tlS :=
    fun u => (blank_lsTail u tl' _).trans (hbl u)
  have eg : LinkJoin.g9 { tl' with lsTail := G'.LS.extract tl'.slotA tl'.slotB } =
      LinkJoin.g9 tlS := by
    have h3 := congrArg LinkJoin.g9 (hb2 tlS)
    rwa [LinkJoin.g9_blank, LinkJoin.g9_blank] at h3
  have hSt2 := LinkJoin.static_congr eg rfl hSt
  have eB : tl'.slotB = tlS.slotB := congrArg (·.slotB) (hbl tlS)
  have eU : tl'.nUF = tlS.nUF := congrArg (·.nUF) (hbl tlS)
  have hP2 : OnBytes.Tie.Pv.Tail.Port.Powered
      { tl' with lsTail := G'.LS.extract tl'.slotA tl'.slotB } G'.theta :=
    ⟨hP.vp, hP.vt, hP.rowX, hP.loX, hP.eqFirst, hP.shape⟩
  exact k8Rest_of_held rfl (by show tl'.slotB ≤ G'.LS.size; omega) hSt2.blocks hP2 hSt2.coef
    (by show (_ == tl'.nUF) = true; rw [eU]; exact hnU) hA

/-- **THE NAMED TESTS ACCEPT BEHIND THE RUN "K8.lsTail"**, where the share is silent. -/
theorem k8_valsS_behind (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 25) {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) {z : ProofFile.InstPub} {s s₁ : S}
    (hw : Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z)
      (14 * l + (if l = 24 then 11 else 9) + 1) (z, s))
    (hsh : k8Share (ProofFile.k8NU Bs.G₀ Xl) s = none)
    (h₁ : bareRun k8LsTail.2 s = .ok s₁) : valsS (ProofFile.k8NU Bs.G₀ Xl) s₁ = true := by
  obtain ⟨tl, G, hget, hR8⟩ := k8_rest_behind hS hR O hOk hl e3 hw
  obtain ⟨e1, e2⟩ := (tlFork_iff s tl G).1 hget
  have hsh' := hsh
  rw [share_at _ e1 e2] at hsh'
  have hf1 : k8First tl (ProofFile.k8NU Bs.G₀ Xl) G = none := by
    cases h : k8First tl (ProofFile.k8NU Bs.G₀ Xl) G with
    | none => rfl
    | some _ => rw [h] at hsh'; exact nomatch hsh'
  have hf2 : k8Second tl G = none := by
    rw [hf1] at hsh'
    exact hsh'
  obtain ⟨Fc, hFc⟩ := tests_of_share (by rw [k8First_slot]; exact hf1)
    (by rw [k8Second_slot]; exact hf2) hR8
  obtain ⟨g, jo, nbW, Wn, hg, hjo, hW, rfl, -, hV⟩ := tests_iff.1 hFc
  have hmem : ("K8.lsTail", bareRun k8LsTail.2) ∈
      (K8.whole (ProofFile.k8ParW Z Bs.G₀ Xl l)).after := by
    rw [after_whole]
    exact List.mem_cons_self
  obtain ⟨q, hq, rfl⟩ := (sits_lsTail _ _ hmem s s₁).1 h₁
  obtain ⟨f1, -, f3⟩ := parts_of hq
  have et : q.tl = tl := Option.some.inj (f1.symm.trans e1)
  have ef : q.F = G := Option.some.inj (f3.symm.trans e2)
  unfold valsS
  rw [part_set hq]
  show valsAt _ { q.tl with lsTail := q.F.LS.extract q.tl.slotA q.tl.slotB } q.F = true
  rw [et, ef]
  unfold valsAt
  rw [hg, hjo, hW]
  exact hV

/-- What the named tests read of a state is the segment's own part. -/
theorem partOf_of_here {x y : S} (h : x.here = y.here) : partOf x = partOf y := by
  have e1 : x.tl? = y.tl? := by
    unfold S.tl?
    rw [h]
  have e2 : x.fork? = y.fork? := by
    unfold S.fork?
    rw [h]
  have e3 : S.funs? x = S.funs? y := by
    unfold S.funs?
    rw [h]
  have e : tlForkP.get? x = tlForkP.get? y := by
    show (x.tl?.bind fun p => x.fork?.map fun q => (p, q)) =
      (y.tl?.bind fun p => y.fork?.map fun q => (p, q))
    rw [e1, e2]
  show ((tlForkP.get? x).bind fun q => (S.funs? x).map fun funs => (⟨q.1, funs, q.2⟩ : K8Part)) =
    ((tlForkP.get? y).bind fun q => (S.funs? y).map fun funs => (⟨q.1, funs, q.2⟩ : K8Part))
  rw [e, e3]

/-- **The layers' run "free-slot" leaves what the named tests read.** -/
theorem valsS_free {hp : Layer.HPlan2} {nU : Array Nat} {s₁ s₂ : S}
    (h : Johnson.AtFull.Shape.freeRunH hp s₁ = .ok s₂) : valsS nU s₂ = valsS nU s₁ := by
  unfold Johnson.AtFull.Shape.freeRunH at h
  cases hq : OnBytes.Desc.First.K4.part? s₁ with
  | none =>
    rw [hq] at h
    exact nomatch h
  | some q =>
    rw [hq] at h
    obtain ⟨a, ha, e⟩ : ∃ a, s₁.here = .lay a ∧ q.1 = a := by
      unfold OnBytes.Desc.First.K4.part? at hq
      split at hq
      · rename_i a ha
        exact ⟨a, ha, by rw [← Option.some.inj hq]⟩
      · exact nomatch hq
    cases hf : OnBytes.Desc.First.K4.freeSlot OnBytes.Desc.First.K4.seatOwn hp q with
    | error m =>
      have h' : (Except.map (OnBytes.Desc.First.K4.setPart s₁)
        (OnBytes.Desc.First.K4.freeSlot OnBytes.Desc.First.K4.seatOwn hp q)) = .ok s₂ := h
      rw [hf] at h'
      exact nomatch h'
    | ok q' =>
      have h' : (Except.map (OnBytes.Desc.First.K4.setPart s₁)
        (OnBytes.Desc.First.K4.freeSlot OnBytes.Desc.First.K4.seatOwn hp q)) = .ok s₂ := h
      rw [hf] at h'
      have e2 : OnBytes.Desc.First.K4.setPart s₁ q' = s₂ := Except.ok.inj h'
      have eq : q' = q := by
        unfold OnBytes.Desc.First.K4.freeSlot at hf
        obtain ⟨o, -, h2⟩ := VerifiableInference.Desc.K9L.ok_bind hf
        obtain ⟨u, -, h3⟩ := VerifiableInference.Desc.K9L.ok_bind h2
        exact (Except.ok.inj h3).symm
      have hh : s₂.here = s₁.here := by
        rw [← e2, eq, ha, ← e]
        rfl
      unfold valsS
      rw [partOf_of_here hh]

/-- **The same behind the layers' run "free-slot".** -/
theorem k8_valsS_free (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 25) {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) {z : ProofFile.InstPub}
    {s s₁ s₂ : S} {hp : Layer.HPlan2}
    (hw : Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z)
      (14 * l + (if l = 24 then 11 else 9) + 1) (z, s))
    (hsh : k8Share (ProofFile.k8NU Bs.G₀ Xl) s = none)
    (h₁ : bareRun k8LsTail.2 s = .ok s₁) (h₂ : Johnson.AtFull.Shape.freeRunH hp s₁ = .ok s₂) :
    valsS (ProofFile.k8NU Bs.G₀ Xl) s₂ = true := by
  rw [valsS_free h₂]
  exact k8_valsS_behind hS hR O hOk hl e3 hw hsh h₁

end

end AtFullSide.K8.Term

#print axioms AtFullSide.K8.Term.layers_seat_k4
#print axioms AtFullSide.K8.Term.att_seat
#print axioms AtFullSide.K8.Term.head_seat
#print axioms AtFullSide.K8.Term.held_lay
#print axioms AtFullSide.K8.Term.held_att
#print axioms AtFullSide.K8.Term.held_head
#print axioms AtFullSide.K8.Term.ledger_behind
#print axioms AtFullSide.K8.Term.k8_rest_behind
#print axioms AtFullSide.K8.Term.k8_valsS_behind
#print axioms AtFullSide.K8.Term.partOf_of_here
#print axioms AtFullSide.K8.Term.valsS_free
#print axioms AtFullSide.K8.Term.k8_valsS_free
