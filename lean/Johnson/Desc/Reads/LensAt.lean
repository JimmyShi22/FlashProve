-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Reads/LensAt.lean: the test on lengths (`lensB`, Reads/Stated.lean) at the list of
tables that the description's text makes for the output head, from the sizes of the points that the
text reads.

What is shown is a step: it speaks of the written text `K8.ReadsQuiet.tables`
(Johnson/Desc/K8/ReadsQuiet.lean).
  `tables_more`: a yes of that text: what it computes on the way is there, la = ls + lt, the long
    point has la coordinates, and the tables are what `addAsk` makes of the fifteen lines `asksH`
    (Johnson/Road/HeadReads.lean).
  `plane_size`: where the lookup's point number e has kT + cK + 5 coordinates, the weights under
    which the planes are read there are 2 ^ lm.
  `tail_size`: the last k coordinates of a point, where they are there, are k.
  `cost_sizes`: the two vectors of the positions with a cost are as long as the table of equality
    weights of their point.
  `lens_of_tables`: **the test on lengths says yes**, and every table lies in the third vector,
    where: x.Zl has ls + lt coordinates; the positions' parts of the key points of the three calls
    that the text reads have lt; the four points PV, tV.r, tN.r, tH.r have lt; and the lookup's two
    points zb0 and zb1 have kT + cK + 5.

Limits. The sizes are premises. Nothing on soundness.


-/
import Johnson.Desc.Reads.FoldAll
import Johnson.Desc.K8.ReadsQuietLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Reads.AtSeat

open OnBytes (E zeroE)
open OnBytes.Model (eqTab longPhi longPoint)
open OnBytes.Model.Head (Shape HL HPlanH2 Covered Tables costWeights ztOf zjOf callNo)
open OnBytes.Road (eqTab_size)
open OnBytes.Road.Hd (addAsk asksH)
open VerifiableInference.Desc (Own.tailOf Own.cutTail Own.planeWeights)
open VerifiableInference.Desc.K8 (ReadsQuiet.tables ReadsQuiet.bind_ok ReadsQuiet.named_ok
  ReadsQuiet.need_ok)

/-- **What a yes of the text that makes the head's tables says.** -/
theorem tables_more {h : Shape} {L : HL} {hp : HPlanH2} {cov : Covered}
    {x : OnBytes.Model.Head.Heard} {t : Tables} (e : ReadsQuiet.tables h L hp cov x = .ok t) :
    ∃ (ZV : Array E) (lowN : Array E × Array E) (qFC qROW : ℕ) (b0 b1 : Array E),
      Own.tailOf x.wpl.r h.la = some ZV ∧ Own.cutTail (zjOf L x.g1 x.qN) h.ls = some lowN ∧
      (longPoint lowN.2 x.tN.r).size = h.la ∧ h.la = h.ls + h.lt ∧
      callNo L "CNF" = some qFC ∧ callNo L "ROW" = some qROW ∧
      Own.planeWeights x.g1 h.lmbH 0 = some b0 ∧ Own.planeWeights x.g1 h.lmbH 1 = some b1 ∧
      (asksH h L x ZV (longPoint lowN.2 x.tN.r) (costWeights cov (ztOf h L x.g1 x.qH)).1
        (costWeights cov (ztOf h L x.g1 x.qH)).2.2 qFC qROW b0 b1).foldlM
          (addAsk hp.tl.mats) {} = some t := by
  unfold ReadsQuiet.tables at e
  obtain ⟨_, _, e⟩ := ReadsQuiet.bind_ok e
  obtain ⟨ZV, p2, e⟩ := ReadsQuiet.bind_ok e
  obtain ⟨lowN, p3, e⟩ := ReadsQuiet.bind_ok e
  obtain ⟨_, p4, e⟩ := ReadsQuiet.bind_ok e
  obtain ⟨qFC, p5, e⟩ := ReadsQuiet.bind_ok e
  obtain ⟨qROW, p6, e⟩ := ReadsQuiet.bind_ok e
  obtain ⟨b0, p7, e⟩ := ReadsQuiet.bind_ok e
  obtain ⟨b1, p8, e⟩ := ReadsQuiet.bind_ok e
  obtain ⟨t', e3, e⟩ := ReadsQuiet.bind_ok e
  obtain ⟨_, _, e⟩ := ReadsQuiet.bind_ok e
  simp only [pure, Except.pure, Except.ok.injEq] at e
  subst e
  have j4 := ReadsQuiet.need_ok p4
  simp only [Bool.and_eq_true, beq_iff_eq] at j4
  exact ⟨ZV, lowN, qFC, qROW, b0, b1, ReadsQuiet.named_ok p2, ReadsQuiet.named_ok p3, j4.1, j4.2,
    ReadsQuiet.named_ok p5, ReadsQuiet.named_ok p6, ReadsQuiet.named_ok p7,
    ReadsQuiet.named_ok p8, ReadsQuiet.named_ok e3⟩

/-- The weights under which the planes are read are 2 ^ lm. -/
theorem plane_size {g : OnBytes.Model.Forest.Heard} {lm e : ℕ} {b : Array E}
    (hb : Own.planeWeights g lm e = some b)
    (hz : (if e = 0 then g.zb0 else g.zb1).size = g.shape.kT + g.shape.cK + 5) :
    b.size = 2 ^ lm := by
  unfold VerifiableInference.Desc.Own.planeWeights at hb
  dsimp only at hb
  by_cases hc : (lm < 5 || lm > g.shape.kT + 5) = true
  · rw [if_pos hc] at hb
    cases hb
  · rw [if_neg hc] at hb
    have hc' : ¬ (lm < 5 ∨ lm > g.shape.kT + 5) := by simpa using hc
    have e1 := (Option.some.inj hb).symm
    subst e1
    rw [eqTab_size, Array.size_append, Array.size_extract, Array.size_extract, hz]
    congr 1
    omega

/-- The last k coordinates of a point are k. -/
theorem tail_size {z ZV : Array E} {k : ℕ} (h : Own.tailOf z k = some ZV) : ZV.size = k := by
  unfold VerifiableInference.Desc.Own.tailOf VerifiableInference.Desc.Own.cutTail at h
  by_cases hk : k > z.size
  · rw [if_pos hk] at h
    cases h
  · rw [if_neg hk] at h
    have e : z.extract (z.size - k) z.size = ZV := Option.some.inj h
    rw [← e, Array.size_extract]
    omega

/-- The two vectors of the positions with a cost. -/
theorem cost_sizes (cov : Covered) (z : Array E) :
    (costWeights cov z).1.size = 2 ^ z.size ∧ (costWeights cov z).2.2.size = 2 ^ z.size := by
  unfold costWeights
  simp [eqTab_size]

/-- **The two tests on the public list, at the head's tables.** -/
theorem lens_of_tables {h : Shape} {L : HL} {hp : HPlanH2} {cov : Covered}
    {x : OnBytes.Model.Head.Heard} {t : Tables} (e : ReadsQuiet.tables h L hp cov x = .ok t)
    (hZl : x.Zl.size = h.ls + h.lt)
    (hFC : ∀ q, callNo L "CNF" = some q → (ztOf h L x.g1 q).size = h.lt)
    (hROW : ∀ q, callNo L "ROW" = some q → (ztOf h L x.g1 q).size = h.lt)
    (hH : (ztOf h L x.g1 x.qH).size = h.lt) (hsPV : x.PV.size = h.lt)
    (hsTV : x.tV.r.size = h.lt) (hsTN : x.tN.r.size = h.lt) (hsTH : x.tH.r.size = h.lt)
    (hzb0 : x.g1.zb0.size = x.g1.shape.kT + x.g1.shape.cK + 5)
    (hzb1 : x.g1.zb1.size = x.g1.shape.kT + x.g1.shape.cK + 5) :
    lensB t.funs = true ∧ allU3B t.funs = true := by
  obtain ⟨ZV, lowN, qFC, qROW, b0, b1, p2, -, p4, hla, p5, p6, p7, p8, hf⟩ := tables_more e
  refine ⟨lens_of_fold hf fun a ha => ?_, allU3_of_fold hf⟩
  have hT : ∀ z : Array E, z.size = h.lt → (eqTab z).size = h.T := fun z hz => by
    rw [eqTab_size, hz]
    rfl
  unfold asksH at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · show (longPhi x.Zl h.ls h.lt).size = 2 ^ h.la
    rw [longPhi_size _ hZl, hla]
  · show ((Array.range (2 ^ h.la)).map _).size = 2 ^ h.la
    simp
  · show (longPhi ZV h.ls h.lt).size = 2 ^ h.la
    rw [longPhi_size _ ((tail_size p2).trans hla), hla]
  · show (longPhi (longPoint lowN.2 x.tN.r) h.ls h.lt).size = 2 ^ h.la
    rw [longPhi_size _ (p4.trans hla), hla]
  · exact hT _ (hFC _ p5)
  · exact hT _ hsTH
  · exact hT _ (hROW _ p6)
  · exact hT _ hsPV
  · exact hT _ hsTV
  · exact hT _ hsTN
  · show (costWeights cov (ztOf h L x.g1 x.qH)).1.size = h.T
    rw [(cost_sizes _ _).1, hH]
    rfl
  · show (costWeights cov (ztOf h L x.g1 x.qH)).2.2.size = h.T
    rw [(cost_sizes _ _).2, hH]
    rfl
  · exact plane_size p7 hzb0
  · exact plane_size p8 hzb1
  · show (OnBytes.Model.Forest.phiP h.lmbH).size = 2 ^ h.lmbH
    simp [OnBytes.Model.Forest.phiP]

end VerifiableInference.Reads.AtSeat

#print axioms VerifiableInference.Reads.AtSeat.tables_more
#print axioms VerifiableInference.Reads.AtSeat.plane_size
#print axioms VerifiableInference.Reads.AtSeat.tail_size
#print axioms VerifiableInference.Reads.AtSeat.cost_sizes
#print axioms VerifiableInference.Reads.AtSeat.lens_of_tables
