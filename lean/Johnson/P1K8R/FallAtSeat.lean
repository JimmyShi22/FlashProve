-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/FallAtSeat.lean: THE SMALLNESS TEST: THE COUNT OF
Johnson/Desc/K8/Honest/FallCount.lean AT THE BATCHING BLOCK THAT THE PROOF FILE's DESCRIPTION SEATS
AT A FEED-FORWARD SEGMENT. A lemma; none of the library's goals. No prover stands in it; nothing on
completeness, soundness or hiding. An assembly: no new argument.

The letters are those of an opening of the description (Johnson/IMR/SeatOpen.lean: IM.Open): c its
first chain, Bs.G₀ the ground off the public files.
  `objectsRun_at`   the lookup's run "objects" at either seat is the library's K9.objectsCalls |
      K9.objectsDigits (by rfl)
  **`fall_at_seat`**   at each feed-forward segment l (l < 25, IM.subAt l = .layers) there are the
      segment Lk, the numbers p of its batching (IM.k9At Z l = some p) and the built entry X, such
      that the block at number 14 l + (the hearing blocks) + 2 of the chain's flat list is Lk's
      batching at the frame's own function of claims, the block at the next number is the frame's
      block behind the batching, and
      (1) THE COUNT: at every state s such that whatever data of the smallness test it holds pass
          `unitsLaid` at nU := ProofFile.k8NU Bs.G₀ X: at most nU[2] * d field elements are challenges at
          which THAT SEATED BLOCK's decision says yes and `selfUnits` says no behind it, for every d
          with (the number of claims that the ledger holds as the plan's) + (the indices of the
          smallness test's equations) ≤ d + 1 at whatever data, ledger and list of tables s holds;
      (2) a yes of the block behind the batching says that `zeroUnitAt` was false at the state that
          it was handed: "where an entry has the weight 0 the verifier refuses". The other way
          ("where none has, it does not refuse for that") is not said here.
  By: IM.k9_of with IM.yes_alone (the seated batching is K9.batch K9.atS p g under the seat's
  guards; the orders are the driver's) · LPFK9.k09_sits (the block behind) · LPFK9.layers_ties_at
  (which run stands where) · OnPublicFiles.at_objects_is (the two runs "objects") · `fall_few_layers` ·
  `behind_layers`.
WHAT IS LEFT, AND SHOWN OF NOTHING HERE. (a) That the data in a state which the chain's own blocks
reach in front of the batching pass `unitsLaid` (shown in Johnson/P1K8R/UnitsAtBatch.lean). (b) The
tie of the exponents' bound to the plan: (the plan's number of claims) + (the equations' indices) =
p.rows. (c) The count is at the block's decision at no columns and at the round as `chiAt` gives it:
that a step of the chain hands it just such a round, and that every challenge of the round's shape
is `chiAt x` for just one x. (d) In the goals' scope (the full size), at the format's second hash function,
in the format's field 2, at feed-forward segments alone. (e) Of the verifier's tests behind the
adding this one alone; a challenge at which the block itself refuses is not counted.

-/
import Johnson.Desc.K8.Honest.FallLayersAny
import Johnson.Desc.K8.Honest.FallAfter
import Johnson.LPFK9R.TiesWholeAt
import Johnson.LPFK9R.Sits
import Johnson.Desc.First.Link.Law.SortK3Objects

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest
open OnBytes.Tie.Pv.Tail.Port (topOf)

/-- The lookup's run "objects" at the calls' and at the digits' seat is the library's own. -/
theorem objectsRun_at :
    OnPublicFiles.objectsRun (OnPublicFiles.seatOf K3Lot.ofForm false) = K9.objectsCalls ∧
      OnPublicFiles.objectsRun (OnPublicFiles.seatOf K3Lot.ofForm true) = K9.objectsDigits := ⟨rfl, rfl⟩

/-- **The count at the seated block.** -/
theorem fall_at_seat {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)}
    {c : Chain S Claim} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (l : ℕ) (hl : l < 25)
    (hsub : IM.subAt l = .layers) :
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
  obtain ⟨Lk', p4, X, e1', -, hX, ties⟩ := LPFK9.layers_ties_at O.made O.places O.chain l hs25
  obtain rfl : Lk = Lk' := Option.some.inj (e1.symm.trans e1')
  have h24 : l ≠ 24 := by
    intro e
    rw [e] at hsub
    exact absurd hsub (by decide)
  have tC : ∀ run, LinkJoin.At Lk (1, "objects") run → LinkJoin.Under run K9.objectsCalls := by
    intro run hrun
    have hrun' : LinkJoin.At Lk (IM.k3Ix l false, "objects") run := by
      simpa [IM.k3Ix, h24] using hrun
    rw [OnPublicFiles.at_objects_is hS hR O hl false e1 hrun', objectsRun_at.1]
    exact LinkJoin.under_refl _
  have tD : ∀ run, LinkJoin.At Lk (6, "objects") run → LinkJoin.Under run K9.objectsDigits := by
    intro run hrun
    have hrun' : LinkJoin.At Lk (IM.k3Ix l true, "objects") run := by
      simpa [IM.k3Ix, h24] using hrun
    rw [OnPublicFiles.at_objects_is hS hR O hl true e1 hrun', objectsRun_at.2]
    exact LinkJoin.under_refl _
  refine ⟨Lk, p, X, e1, e2, hX, hflat, ⟨Lk.behindB, hsit.flat₂, fun _ _ _ => rfl⟩, h7, ?_, ?_⟩
  · intro s tU d hU hd
    refine fall_few_layers Lk p4 (ProofFile.k8NU Bs.G₀ X) p _ s tU d ties tC tD hord ?_ hU hd
    intro rs t ht
    have k9ne : KindName.K9 ≠ KindName.K7 := by decide
    exact ((IM.yes_alone (hb (claimsInBy Lk.each Lk.hear Lk.order)) k9ne s t rs []).1 ht).1
  · intro t t' ht
    exact behind_layers Lk p4 (ProofFile.k8NU Bs.G₀ X) ties hordA t t' ht

end P1K8

#print axioms P1K8.objectsRun_at
#print axioms P1K8.fall_at_seat
