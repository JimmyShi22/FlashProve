-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/FallAtSeatHead.lean: THE SMALLNESS TEST: THE COUNT OF
Johnson/Desc/K8/Honest/FallCount.lean AT THE BATCHING BLOCK THAT THE PROOF FILE's DESCRIPTION SEATS
AT THE HEAD's SEGMENT. A lemma; none of the library's goals. No prover stands in it; nothing on
completeness, soundness or hiding. An assembly: no new argument.

The letters are those of an opening of the description (IM.Open). The statement is that of
Johnson/P1K8R/FallAtSeat.lean's `fall_at_seat`, at segment number 24, the head's, which has nine
blocks in front of its batching.
  `head_u3`   the head's plan's array of reads is number 0: out of `public_H_units`
      (Johnson/P1K8R/UnitsAtPlans.lean)
  **`fall_at_seat_head`**   in the goals' scope: the segment Lk, the numbers p of its batching, the
      built entry X; the flat list's entry 14 * 24 + 11 is Lk's batching at the frame's function of
      claims, the entry behind it decides as Lk.runBehind; and (1) THE COUNT and (2) "a yes of
      Lk.runBehind at t says that `selfUnits` had not said no at t", as in `fall_at_seat`
By: IM.k9_of, LPFK9.k09_sits · LPFK9.head_ties_at · head_24
(Johnson/Desc/Kinds/Law/K6PubInScope.lean) · OnPublicFiles.readersAt_head, OnPublicFiles.at_planes_is,
OnPublicFiles.at_objects_is · `fall_few_head` (Johnson/Desc/K8/Honest/FallHead.lean) · `behind_head`
(FallAfterAll.lean).
WHAT IS LEFT: FallAtSeat.lean's list, at the head's segment; its (a) is shown in
Johnson/P1K8R/UnitsAtBatchAll.lean.

-/
import Johnson.P1K8R.FallAtSeat
import Johnson.P1K8R.UnitsAtPlans
import Johnson.Desc.K8.Honest.FallHead
import Johnson.Desc.K8.Honest.FallAfterAll
import Johnson.Desc.First.Link.Law.SortK3Planes
import Johnson.Desc.First.Link.Law.SortK3PlanesRun
import Johnson.Desc.Kinds.Law.K6PubInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest
open VerifiableInference.Desc.Kinds.Head (callerReaders planesAt)
open VerifiableInference.Desc.Kinds.Head.Law.InScope (head_24)
open OnBytes.Tie.Pv.Tail.Port (topOf)

/-- The head's plan's array of reads is number 0. -/
theorem head_u3 {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}
    (h : Verify.publicOf pol KL layout = .ok X) : X.H.tl.ix.U.getD 2 none = some 0 := by
  have k := public_H_units h
  simp only [unitsLaid, Bool.and_eq_true, beq_iff_eq] at k
  exact k.1.1.1.1.1.2

/-- **The count at the seated block of the head's segment.** -/
theorem fall_at_seat_head {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)}
    {c : Chain S Claim} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∃ (Lk : Link S Claim) (p : K9.Where) (X : OnBytes.Model.Stages.LinkH),
      c.links[24]? = some Lk ∧ IM.k9At Z 24 = some p ∧ Bs.G₀.built.toList[24]? = some X ∧
      c.blocksInOrder[14 * 24 + Lk.hear.length + 2]? =
        some (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)) ∧
      (∃ b, c.blocksInOrder[14 * 24 + Lk.hear.length + 3]? = some b ∧
        ∀ s rs gs, b.decide s rs gs = Lk.runBehind s) ∧
      Lk.hear.length = 9 ∧
      (∀ (s : S) (tU d : Nat),
        (∀ tl, s.tl? = some tl → unitsLaid (ProofFile.k8NU Bs.G₀ X) tl tU = true) →
        (∀ tl F funs, s.tl? = some tl → s.fork? = some F → s.funs? = some funs →
          F.planClaimsF + topOf tl funs ≤ d + 1) →
        Prob.cnt (fun x : Cb.Gl.E =>
          askBehind (fun t rs => (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)).decide t rs [])
            (zeroUnitAt (ProofFile.k8NU Bs.G₀ X)) s [chiAt x] = true) ≤
          (ProofFile.k8NU Bs.G₀ X).getD 2 0 * d) ∧
      (∀ t t', Lk.runBehind t = .ok t' → zeroUnitAt (ProofFile.k8NU Bs.G₀ X) t = false) := by
  have hl : 24 < 25 := by omega
  have hsub : IM.subAt 24 = .head := rfl
  obtain ⟨Lk, p, w, T, e1, e2, -, -, -, -, hb, hflat, -, -, -, hord, hordA, hlen, -⟩ :=
    (IM.k9_of hS hR O).2 24 hl
  obtain ⟨Lk₂, p₂, Q, -, -, hsit⟩ := LPFK9.k09_sits hS hR O 24 hl
  obtain rfl : Lk = Lk₂ := Option.some.inj (e1.symm.trans hsit.link)
  have hs25 := IM.subs_scope hS hR O 24 hl
  rw [hsub] at hs25 hord hordA hlen
  have h9 : Lk.hear.length = 9 := by
    rw [hlen]
    rfl
  have hU3 := head_u3 O.public
  obtain ⟨Lk', X, e1', hX, ties⟩ := LPFK9.head_ties_at O.made O.places O.chain 24 hs25 0 hU3
  obtain rfl : Lk = Lk' := Option.some.inj (e1.symm.trans e1')
  obtain ⟨h4, hN⟩ := head_24 hS O.public
  have hH : K3.isHead Bs.G₀.W 24 = true := by
    unfold K3.isHead
    rw [h4, hN]
    rfl
  have tC : ∀ run, LinkJoin.At Lk (2, "objects") run → LinkJoin.Under run K9.objectsCalls := by
    intro run hrun
    have hrun' : LinkJoin.At Lk (IM.k3Ix 24 false, "objects") run := hrun
    rw [OnPublicFiles.at_objects_is hS hR O hl false e1 hrun', objectsRun_at.1]
    exact LinkJoin.under_refl _
  have tD : ∀ run, LinkJoin.At Lk (7, "objects") run → LinkJoin.Under run K9.objectsDigits := by
    intro run hrun
    have hrun' : LinkJoin.At Lk (IM.k3Ix 24 true, "objects") run := hrun
    rw [OnPublicFiles.at_objects_is hS hR O hl true e1 hrun', objectsRun_at.2]
    exact LinkJoin.under_refl _
  have tP : ∀ run, LinkJoin.At Lk (2, "planes") run →
      ∃ lm, LinkJoin.Under run (K9.planesCalls lm (callerReaders (planesAt 0))) := by
    intro run hrun
    have hrun' : LinkJoin.At Lk (IM.k3Ix 24 false, "planes") run := hrun
    obtain ⟨q, -, rfl⟩ := OnPublicFiles.at_planes_is hS hR O hl e1 (OnPublicFiles.readersAt_head hH hU3) hrun'
    exact ⟨q.lm, LinkJoin.under_refl _⟩
  refine ⟨Lk, p, X, e1, e2, hX, hflat, ⟨Lk.behindB, hsit.flat₂, fun _ _ _ => rfl⟩, h9, ?_, ?_⟩
  · intro s tU d hU hd
    refine fall_few_head Lk _ 0 _ 4 _ (ProofFile.k8NU Bs.G₀ X) ties tC tD tP p _ s tU d hord ?_ hU hd
    intro rs t ht
    have k9ne : KindName.K9 ≠ KindName.K7 := by decide
    exact ((IM.yes_alone (hb (claimsInBy Lk.each Lk.hear Lk.order)) k9ne s t rs []).1 ht).1
  · intro t t' ht
    exact behind_head Lk _ 0 _ 4 _ (ProofFile.k8NU Bs.G₀ X) ties hordA t t' ht

end P1K8

#print axioms P1K8.head_u3
#print axioms P1K8.fall_at_seat_head
