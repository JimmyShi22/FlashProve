-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/FallAtSeatAtt.lean: THE SMALLNESS TEST: THE COUNT OF
Johnson/Desc/K8/Honest/FallCount.lean AT THE BATCHING BLOCK THAT THE PROOF FILE's DESCRIPTION SEATS
AT AN ATTENTION SEGMENT. A lemma; none of the library's goals. No prover stands in it; nothing on
completeness, soundness or hiding. An assembly: no new argument.

The letters are those of an opening of the description (IM.Open). The statement is that of
Johnson/P1K8R/FallAtSeat.lean's `fall_at_seat`, at an attention segment.
  **`fall_at_seat_att`**   in the goals' scope, at l < 25 with IM.subAt l = .attention: the segment
      Lk, the numbers p of its batching, the built entry X; the flat list's entry 14 l + 9 is Lk's
      batching at the frame's function of claims, the entry behind it decides as Lk.runBehind; and
      (1) THE COUNT: at every state s such that whatever data of the smallness test it holds pass
          `unitsLaid` at nU := ProofFile.k8NU Bs.G₀ X: at most nU[2] * d field elements are challenges at
          which that seated block's decision says yes and `selfUnits` says no behind it, for every d
          with (the number of claims that the ledger holds as the plan's) + (the indices of the
          smallness test's equations) ≤ d + 1 at whatever s holds;
      (2) a yes of Lk.runBehind at t says that `selfUnits` had not said no at t
By: IM.k9_of, LPFK9.k09_sits · LPFK9.att_ties_at · Att.P.att_only, Att.P.built_att (which group the
segment is) · LinkJoin.at_join_is, OnPublicFiles.at_planes_is with H2K5.Door.readersAt_att,
OnPublicFiles.at_objects_is (which runs the lookups' blocks state) · `fall_few_att`
(Johnson/Desc/K8/Honest/FallAtt.lean) · `behind_att` (FallAfterAll.lean).
WHAT IS LEFT: FallAtSeat.lean's list, at an attention segment; its (a) is shown in
Johnson/P1K8R/UnitsAtBatchAll.lean.

-/
import Johnson.P1K8R.FallAtSeat
import Johnson.Desc.K8.Honest.FallAtt
import Johnson.Desc.K8.Honest.FallAfterAll
import Johnson.Desc.First.Link.Law.SortK3Join
import Johnson.Desc.First.Link.Law.SortK3Planes
import Johnson.Desc.First.Att.Door.Law.K5RestOpen
import Johnson.H2K5R.LawAtEntry

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest
open VerifiableInference.Desc.First.Att
open OnBytes.Tie.Pv.Tail.Port (topOf)

/-- **The count at the seated block of an attention segment.** -/
theorem fall_at_seat_att {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)}
    {c : Chain S Claim} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (l : ℕ) (hl : l < 25)
    (hsub : IM.subAt l = .attention) :
    ∃ (Lk : Link S Claim) (p : K9.Where) (X : OnBytes.Model.Stages.LinkH),
      c.links[l]? = some Lk ∧ IM.k9At Z l = some p ∧ Bs.G₀.built.toList[l]? = some X ∧
      c.blocksInOrder[14 * l + Lk.hear.length + 2]? =
        some (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)) ∧
      (∃ b, c.blocksInOrder[14 * l + Lk.hear.length + 3]? = some b ∧
        ∀ s rs gs, b.decide s rs gs = Lk.runBehind s) ∧
      Lk.hear.length = 7 ∧
      (∀ (s : S) (tU d : Nat),
        (∀ tl, s.tl? = some tl → unitsLaid (ProofFile.k8NU Bs.G₀ X) tl tU = true) →
        (∀ tl F funs, s.tl? = some tl → s.fork? = some F → s.funs? = some funs →
          F.planClaimsF + topOf tl funs ≤ d + 1) →
        Prob.cnt (fun x : Cb.Gl.E =>
          askBehind (fun t rs => (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)).decide t rs [])
            (zeroUnitAt (ProofFile.k8NU Bs.G₀ X)) s [chiAt x] = true) ≤
          (ProofFile.k8NU Bs.G₀ X).getD 2 0 * d) ∧
      (∀ t t', Lk.runBehind t = .ok t' → zeroUnitAt (ProofFile.k8NU Bs.G₀ X) t = false) := by
  obtain ⟨Lk, p, w, T, e1, e2, -, -, -, -, hb, hflat, -, -, -, hord, hordA, hlen, -⟩ :=
    (IM.k9_of hS hR O).2 l hl
  obtain ⟨Lk₂, p₂, Q, -, -, hsit⟩ := LPFK9.k09_sits hS hR O l hl
  obtain rfl : Lk = Lk₂ := Option.some.inj (e1.symm.trans hsit.link)
  have hs25 := IM.subs_scope hS hR O l hl
  rw [hsub] at hs25 hord hordA hlen
  have h7 : Lk.hear.length = 7 := by
    rw [hlen]
    cases (l == 0) <;> rfl
  obtain ⟨Lk', Xl, Ap, X, e1', hXl, -, hA, hX, ties⟩ :=
    LPFK9.att_ties_at O.made O.places O.chain l hs25
  obtain rfl : Lk = Lk' := Option.some.inj (e1.symm.trans e1')
  obtain ⟨h4, g, hg, rfl⟩ := Att.P.att_only O.pub O.blank hs25
  obtain ⟨Xl', hXl', -, hgX, -⟩ := Att.P.built_att O.pub O.blank h4 hg
  obtain rfl : Xl' = Xl := Option.some.inj (hXl'.symm.trans hXl)
  rw [hgX] at hA
  have h24 : 2 * g + 1 ≠ 24 := by omega
  have tC : ∀ run, LinkJoin.At Lk (1, "objects") run → LinkJoin.Under run K9.objectsCalls := by
    intro run hrun
    have hrun' : LinkJoin.At Lk (IM.k3Ix (2 * g + 1) false, "objects") run := by
      simpa [IM.k3Ix, h24] using hrun
    rw [OnPublicFiles.at_objects_is hS hR O hl false e1 hrun', objectsRun_at.1]
    exact LinkJoin.under_refl _
  have tD : ∀ run, LinkJoin.At Lk (6, "objects") run → LinkJoin.Under run K9.objectsDigits := by
    intro run hrun
    have hrun' : LinkJoin.At Lk (IM.k3Ix (2 * g + 1) true, "objects") run := by
      simpa [IM.k3Ix, h24] using hrun
    rw [OnPublicFiles.at_objects_is hS hR O hl true e1 hrun', objectsRun_at.2]
    exact LinkJoin.under_refl _
  have tJ : ∀ run, LinkJoin.At Lk (2, "join") run →
      LinkJoin.Under run
        (K9.joinCalls (Att.P.keysOfK (Att.P.seatCO (Att.P.parCOf Ap)) (Att.P.parCOf Ap))) := by
    intro run hrun
    rw [LinkJoin.at_join_is O h4 hg hA e1 hrun]
    exact LinkJoin.under_refl _
  have tP : ∀ run, LinkJoin.At Lk (1, "planes") run →
      ∃ lm, LinkJoin.Under run
        (K9.planesCalls lm
          (Att.P.readersOfK (Att.P.seatCO (Att.P.parCOf Ap)) (Att.P.parCOf Ap))) := by
    intro run hrun
    have hrun' : LinkJoin.At Lk (IM.k3Ix (2 * g + 1) false, "planes") run := by
      simpa [IM.k3Ix, h24] using hrun
    obtain ⟨q, -, rfl⟩ :=
      OnPublicFiles.at_planes_is hS hR O hl e1 (H2K5.Door.readersAt_att h4 hA) hrun'
    exact ⟨q.lm, LinkJoin.under_refl _⟩
  refine ⟨Lk, p, X, e1, e2, hX, hflat, ⟨Lk.behindB, hsit.flat₂, fun _ _ _ => rfl⟩, h7, ?_, ?_⟩
  · intro s tU d hU hd
    refine fall_few_att Lk (Att.P.parCOf Ap) (ProofFile.k8NU Bs.G₀ X) p _ s tU d ties tC tD tJ tP hord
      ?_ hU hd
    intro rs t ht
    have k9ne : KindName.K9 ≠ KindName.K7 := by decide
    exact ((IM.yes_alone (hb (claimsInBy Lk.each Lk.hear Lk.order)) k9ne s t rs []).1 ht).1
  · intro t t' ht
    exact behind_att Lk (Att.P.parCOf Ap) (ProofFile.k8NU Bs.G₀ X) ties hordA t t' ht

end P1K8

#print axioms P1K8.fall_at_seat_att
