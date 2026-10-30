-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/UnitsAtBatch.lean: THE SMALLNESS TEST: AT EVERY STATE THAT THE FIRST CHAIN's OWN
BLOCKS REACH IN FRONT OF A FEED-FORWARD SEGMENT's BATCHING THE PUBLIC TEST `unitsLaid`
(Johnson/Desc/K8/Honest/FallCount.lean) SAYS YES; AND SO THE COUNT OF THAT FILE HOLDS THERE. Lemmas;
none of the library's goals. No prover stands in them; nothing on completeness, soundness or hiding.

"Reached": Reach 0 c.blocksInOrder (ProofFile.startS Z) k (z, s) (Johnson/Top/H0/Walk/Reach.lean): s is a state
that the flat list's blocks hand on, step by step, from the start at the statement's public part z,
and stands in front of block number k. The letters are those of an opening of the description
(IM.Open). IT STANDS ON THE LIBRARY's `planned_at_batch`
(Johnson/Desc/First/Link/Law/PlannedAtDraw.lean): at every state reached at a segment's batching's
number every reading of the smallness test's data that reads planned fields alone (`Planned`) has
the value that it has at the built segment's own planned data. What `unitsLaid` reads is such a
reading.
  `unitsView`, `unitsLaid_view`, `keeps4_view`, `planned_view`   what the test reads of the data; it
      is `Planned`
  `units_of_view`   from the six fields to the test
  **`units_at_batch`**   in the goals' scope, at l < 25 with IM.subAt l = .layers, at every (z, s)
      reached at 14 l + 9: s holds data tl with unitsLaid (ProofFile.k8NU Bs.G₀ X) tl 0 = true, X the
      built entry
  **`fall_at_reached`**   so at such a state at most nU[2] * d field elements are challenges at
      which the seated batching block's decision says yes and `selfUnits` says no behind it, for
      every d with (the number of claims that the ledger holds as the plan's) + (the indices of the
      smallness test's equations) ≤ d + 1
By: `planned_at_batch` · IM.ground_named, IM.ground_tails (Johnson/IMR/PureJoin.lean, K8Seat.lean:
the built entry's sort, group and planned data) · `public_G_units` (UnitsAtPlan.lean) ·
`fall_at_seat` (FallAtSeat.lean).
WHAT IS LEFT: FallAtSeat.lean's list, but for its (a).

-/
import Johnson.P1K8R.UnitsAtPlan
import Johnson.P1K8R.FallAtSeat
import Johnson.Desc.First.Link.Law.PlannedAtDraw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8 VerifiableInference.Desc.First.K8.Ready
open VerifiableInference.Desc.First.K8.Honest
open OnBytes.Tie.Pv.Tail.Port (topOf)
open Johnson.Desc.First.Walk.Tied (Reach)

/-- What `unitsLaid` reads of the smallness test's data. -/
def unitsView (tl : HTailF2) := (tl.ix, tl.tabFirst, tl.tabLen, tl.nUF, tl.NM, tl.gtTree)

theorem unitsLaid_view {a b : HTailF2} (h : unitsView a = unitsView b) (nU : Array Nat) (tU : Nat) :
    unitsLaid nU a tU = unitsLaid nU b tU := by
  simp only [unitsView, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  unfold unitsLaid
  rw [h1, h2, h3, h4, h5, h6]

theorem keeps4_view : Keeps4 unitsView := fun _ _ _ _ _ => rfl

/-- It reads planned fields alone. -/
theorem planned_view : LinkJoin.Planned unitsView :=
  ⟨keeps4_view, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ => rfl⟩

/-- From the six fields to the test. -/
theorem units_of_view {s : S} {tlP : HTailF2} {nU : Array Nat}
    (hv : readTl unitsView s = some (unitsView tlP)) (hU : unitsLaid nU tlP 0 = true) :
    ∃ tl, s.tl? = some tl ∧ unitsLaid nU tl 0 = true := by
  unfold readTl at hv
  cases hts : s.tl? with
  | none =>
    rw [hts] at hv
    exact absurd hv (by simp)
  | some tl =>
    rw [hts] at hv
    exact ⟨tl, rfl, by rw [unitsLaid_view (Option.some.inj hv)]; exact hU⟩

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **At every state reached in front of a feed-forward segment's batching the test says yes.** -/
theorem units_at_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    (hsub : IM.subAt l = .layers) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + 9) (z, s)) :
    ∃ (X : LinkH) (tl : HTailF2), Bs.G₀.built.toList[l]? = some X ∧ s.tl? = some tl ∧
      unitsLaid (ProofFile.k8NU Bs.G₀ X) tl 0 = true := by
  obtain ⟨g, hg, rfl⟩ : ∃ g, g < 12 ∧ l = 2 * g := by
    unfold IM.subAt at hsub
    split at hsub
    · cases hsub
    · split at hsub
      · exact ⟨l / 2, by omega, by omega⟩
      · cases hsub
  obtain ⟨hN, -⟩ := IM.ground_named hS hR O.pub O.blank
  obtain ⟨X, -, e3, hk, hXg, -⟩ := hN g hg
  obtain ⟨hT, -⟩ := IM.ground_tails hS hR O.pub O.blank
  obtain ⟨hp, -, X', -, ehp, -, e3', htl, -⟩ := hT g hg
  obtain rfl : X = X' := Option.some.inj (e3.symm.trans e3')
  have hv := LinkJoin.planned_at_batch planned_view hS hR O (x := (2 * g, 4, 2))
    (List.mem_map.2 ⟨2 * g, List.mem_range.2 hl, by
      rw [if_neg (by omega : ¬ 2 * g = 24), if_neg (by omega : ¬ 2 * g = 24)]⟩) e3 (z, s) h
  rw [htl] at hv
  have hnU : ProofFile.k8NU Bs.G₀ X = hp.nU := by
    unfold ProofFile.k8NU
    simp [hk, hXg, ehp]
  obtain ⟨tl, hts, hU⟩ := units_of_view hv (public_G_units O.public g hp ehp)
  exact ⟨X, tl, by rw [Array.getElem?_toList]; exact e3, hts, by rw [hnU]; exact hU⟩

/-- **The count at every state reached in front of a feed-forward segment's batching.** -/
theorem fall_at_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    (hsub : IM.subAt l = .layers) :
    ∃ (Lk : Link S Claim) (p : K9.Where) (X : LinkH),
      c.links[l]? = some Lk ∧ IM.k9At Z l = some p ∧ Bs.G₀.built.toList[l]? = some X ∧
      c.blocksInOrder[14 * l + 9]? = some (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)) ∧
      ∀ (z : ProofFile.InstPub) (s : S) (d : Nat), Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + 9) (z, s) →
        (∀ tl F funs, s.tl? = some tl → s.fork? = some F → s.funs? = some funs →
          F.planClaimsF + topOf tl funs ≤ d + 1) →
        Prob.cnt (fun x : Cb.Gl.E =>
          askBehind (fun t rs => (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)).decide t rs [])
            (zeroUnitAt (ProofFile.k8NU Bs.G₀ X)) s [chiAt x] = true) ≤
          (ProofFile.k8NU Bs.G₀ X).getD 2 0 * d := by
  obtain ⟨Lk, p, X, e1, e2, hX, hflat, -, h7, hcount, -⟩ := fall_at_seat hS hR O l hl hsub
  rw [h7] at hflat
  refine ⟨Lk, p, X, e1, e2, hX, hflat, fun z s d hr hd => ?_⟩
  obtain ⟨X', tl, hX', hts, hU⟩ := units_at_batch hS hR O hl hsub hr
  obtain rfl : X = X' := Option.some.inj (hX.symm.trans hX')
  refine hcount s 0 d (fun tl' ht' => ?_) hd
  obtain rfl : tl = tl' := Option.some.inj (hts.symm.trans ht')
  exact hU

end

end P1K8

#print axioms P1K8.planned_view
#print axioms P1K8.units_at_batch
#print axioms P1K8.fall_at_reached
