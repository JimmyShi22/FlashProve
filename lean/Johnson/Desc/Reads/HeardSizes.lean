-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Reads/HeardSizes.lean: the sizes of the four heard points that `Lies`
(Reads/HeadAtRecord.lean) asks are a law of the output head's own hearing.

What is shown. Steps: they speak of the kind's written hearing `Head.hear`
(Johnson/Desc/Kinds/Head.lean) and of its decision `decideBy` (Johnson/Desc/Kinds/HeadFrame.lean).
  `decideBy_more`: what a yes of the decision is: the letters in front of the hearing are there; the
    hearing returns on the state's ledger and the rounds; the ledger and what was heard are laid.
  `heard_sizes`: **where the hearing returns on a ledger that is well laid, and the lookup's point
    zt has lt coordinates: pV has lt coordinates, the squares' challenges are lNI + lPd + lt, the
    products' are lt, and the first lt of the logits' challenges are lt.** By the library's laws on
    the parts of the hearing (`hear_parts`, `norm_parts`, `drawPoint_size`, `level_r_size`,
    `sum_r_size`, under Johnson/Desc/Kinds/Law/).
  `core_of_kind`: **`Core` (Reads/LiesBehind.lean) behind a yes of the kind's own decision and a yes
    of the block of a commitment with the reads' quiet step behind it**, as `core_of_pieces` there,
    with the four sizes not premises.

Count, in `core_of_kind`. Of the 21 clauses eighteen follow. Three are premises: cols; the sizes of
the lookup's two points on the planes. One more premise speaks of a state: the ledger in front of
the head's own rounds is well laid. Two are public: hJ and hlsJ at call 0.

Limits. The three and the ledger's being well laid are shown by nothing here. That the two texts
stand one behind the other in the seated description is not shown. No state of a run is shown.
Nothing on soundness.


-/
import Johnson.Desc.Reads.LiesBehind
import Johnson.Desc.Kinds.Law.Cut
import Johnson.Desc.Kinds.Law.NormHear
import Johnson.Desc.Kinds.Law.NormSquares
import Johnson.Desc.Kinds.Law.SumLaw
import Johnson.Desc.Kinds.HeadKind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Reads.AtSeat

open OnBytes.Model (Fork)
open OnBytes.Model.Head (Shape HL)
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.K8 (ReadsQuiet.head ReadsQuiet.bind_ok ReadsQuiet.named_ok)
open VerifiableInference.Desc.Kinds
open VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Head.Law

/-- **What a yes of the decision is.** -/
theorem decideBy_more {T : Type} {rounds : Given → List Round} {hear : Given → Hear HeardAll}
    {weights : Given → Behind → SumOnMatrix} {p : Par} {L : Head.Seat T} {s s' : T}
    {rs : List Fmt.RoundView} (h : decideBy rounds hear weights p L s rs = .ok s') :
    ∃ (g : Given) (H : HeardAll) (F : Fork) (left : List Fmt.RoundView) (s1 s2 : T),
      given p L s = .ok g ∧ hear g (L.ledger s) rs = some (H, F, left) ∧
      L.setLedger s F = .ok s1 ∧ L.setHeard s1 H = .ok s2 ∧
      s' = L.setWeightClaim s2 (weights g ⟨H.1, H.2.1, H.2.2⟩) := by
  unfold decideBy at h
  obtain ⟨g, hg, h⟩ := ReadsQuiet.bind_ok h
  obtain ⟨_, _, h⟩ := ReadsQuiet.bind_ok h
  obtain ⟨⟨H, F, left⟩, h3, h⟩ := ReadsQuiet.bind_ok h
  obtain ⟨_, _, h⟩ := ReadsQuiet.bind_ok h
  obtain ⟨s1, e1, h⟩ := ReadsQuiet.bind_ok h
  obtain ⟨s2, e2, h⟩ := ReadsQuiet.bind_ok h
  exact ⟨g, H, F, left, s1, s2, hg, ReadsQuiet.named_ok h3, e1, e2, (Except.ok.inj h).symm⟩

/-- **The sizes of the four heard points.** -/
theorem heard_sizes [Sizes] [Policy] [Request] [Token] [FinalNorm.In] {F G : Fork}
    {rs left : List Fmt.RoundView} {H : HeardAll} (hW : WellLaid F)
    (h : Head.hear F rs = some (H, G, left)) (hzt : (FinalNorm.zt).size = Norm.lt) :
    H.1.pV.size = Norm.lt ∧ H.1.squares.r.size = Norm.lNI + Norm.lPd + Norm.lt ∧
      H.1.products.r.size = Norm.lt ∧ (H.2.2.logits.r.extract 0 Norm.lt).size = Norm.lt := by
  obtain ⟨Fa, Fb, l1, hNorm, _, _, _, hsL, _⟩ := Came.hear_parts hW h
  obtain ⟨p0, p1, tS, p2, tP, _, _, Fc, _, h0, _, _, h3, _, h5, _⟩ := norm_parts hW hNorm
  have hz : H.1.pV.size = Norm.lt := drawPoint_size h0
  have hq := level_r_size h3
  have hr : H.1.products.r.size = Norm.lt := (Came.sum_r_size h5).trans hz
  have hl := Came.sum_r_size hsL
  refine ⟨hz, ?_, hr, ?_⟩
  · rw [hq]
    unfold zS halves
    rw [Array.size_append, Array.size_append, Array.size_replicate, hz]
    have e0 : (Norm.lNI : ℕ) = 0 := rfl
    rw [e0]
    rfl
  · rw [Array.size_extract, hl, Array.size_append, hzt]
    omega

/-- **Core, behind the kind's own decision and the block of the reads' sending.** -/
theorem core_of_kind (Z : Fill) (hZ : Z.tab = planTab Z.h Z.hp.tl.mats)
    (place : VerifiableInference.Desc.Place) {weights : Given → Behind → SumOnMatrix}
    {rounds : Given → List Round} {s0 s2 s4 : S} {rs4 : List Fmt.RoundView}
    (h4 : decideBy rounds (fun _ => Head.hear) weights (parOf Z.h Z.work) (seatAt Z.h Z.iU3) s0
      rs4 = .ok s2)
    (hWL : WellLaid ((seatAt Z.h Z.iU3).ledger s0))
    (hJ0 : (Z.L.calls.getD 0 default).lJ =
      (letI := sizesOf Z.h; lJ (OnBytes.Model.Head.keyFloor Z.h) (callKeys 0)))
    (hlsJ0 : Z.h.ls ≤ (Z.L.calls.getD 0 default).lJ)
    (P : VerifiableInference.Desc.K1.Par) (link moment : ℕ) (arrays : Option (List ℕ))
    {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))}
    (h5 : (VerifiableInference.Desc.K8.ReadsQuiet.behind
      (VerifiableInference.Desc.K1.commitAtS P link moment arrays)
      (ReadsQuiet.head ⟨place, Z.h, Z.L, Z.hp⟩)).decide s2 rs gs = .ok s4)
    (hcols : ∀ o, s4.here = .head o → ∃ tr, o.F.trees[Z.iU3]? = some tr ∧ tr.K = Z.cols)
    (hzb : ∀ o x, s2.here = .head o → o.x = some x →
      x.g1.zb0.size = x.g1.shape.kT + x.g1.shape.cK + 5 ∧
      x.g1.zb1.size = x.g1.shape.kT + x.g1.shape.cK + 5) :
    ∃ o cov x t, Core Z s4 o cov x t := by
  refine core_of_pieces Z hZ place h4 P link moment arrays h5 hcols fun o x ho hx => ?_
  obtain ⟨z0, z1⟩ := hzb o x ho hx
  obtain ⟨g0, H, F, left, s1, s2', hg, hh, -, e2, hs2⟩ := decideBy_more h4
  have hs2' : s2 = s2' := hs2
  subst hs2'
  obtain ⟨z, y, -, -, hP, hgE⟩ := Came.given_ok _ _ _ _ hg
  subst hgE
  have hz : Z.h.ls + Z.h.lt ≤ z.1.size := by
    obtain ⟨p1, p2⟩ := hP 0 _ (Came.call_get (by decide))
    exact size_of_tail (z.2 0) z.1 (J := (Z.L.calls.getD 0 default).lJ) (by rw [hJ0]; exact p1)
      p2 hlsJ0
  have hzt : (@fromLookup (sizesOf Z.h) (OnBytes.Model.Head.keyFloor Z.h) z.1 z.2).norm.zt.size =
      Z.h.lt := last_size z.1 (n := Z.h.lt) (Nat.le_trans (Nat.le_add_left _ _) hz)
  obtain ⟨a1, a2, a3, a4⟩ := @heard_sizes (sizesOf Z.h) (parOf Z.h Z.work).policy (requestOf s0)
    ⟨y⟩ (@fromLookup (sizesOf Z.h) (OnBytes.Model.Head.keyFloor Z.h) z.1 z.2).norm _ _ _ _ _ hWL
    hh hzt
  obtain ⟨o2, x2, q2, hx2, -, -, -, -, p1, p2, p3, p4⟩ := laid_by_hearing Z.h Z.iU3 e2
  have eo : o = o2 := by
    rw [q2] at ho
    exact (VerifiableInference.Desc.First.Here.head.inj ho).symm
  subst eo
  have ex : x = x2 := by
    rw [hx2] at hx
    exact (Option.some.inj hx).symm
  subst ex
  exact ⟨by rw [p1]; exact a1, by rw [p2]; exact a2, by rw [p3]; exact a3, by rw [p4]; exact a4, z0,
    z1⟩

end VerifiableInference.Reads.AtSeat

#print axioms VerifiableInference.Reads.AtSeat.decideBy_more
#print axioms VerifiableInference.Reads.AtSeat.heard_sizes
#print axioms VerifiableInference.Reads.AtSeat.core_of_kind
