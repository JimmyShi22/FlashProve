-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K8/MatsScope.lean: the honest side of the smallness test (K8): IN THE
GOALS' SCOPE THE TWO LISTS OF Johnson/Desc/ProofFile/Honest/K8/MatsMeet.lean ARE ONE: at the public
part that the proof file's own maker makes at the format's second hash function, and at the ground for a
request of zeros (`blankBy`, Johnson/Desc/ProofFile/Pub.lean), the plan of link l in the public
parameters (`K3.tlOf`) is the plan of the built segment number l. So there the list of matrices that
the kind "lookup" makes (`K3.matsOwn`) stands entry for entry and in order at the block's own
matrices, and the test `matsMeetB` says yes. A joining of the library's laws; none of its goals.

  `tlOf_at_pub`   at the public part's own built segment number l below 25: K3.tlOf Z.p.X l = X.tl.
                   By `tlAt_built` and `blank_at` (Johnson/Desc/First/Link/Law/K9DigStatic.lean),
                   `pub_public` (Johnson/Desc/ProofFile/Law/MakerPublic.lean) and `pub_builtOf`
                   (Johnson/Desc/ProofFile/Law/PlainIsPlanned.lean). THE FIRST LINES OF ITS PROOF
                   ARE WRITTEN A FURTHER TIME: they are those by which the library's `k9_at_pub`
                   (Johnson/Desc/First/Link/Law/K9AtPub.lean) reaches the same four
  **`tlOf_at_blank`**   the same at the ground's segment: K3.tlOf G.W l = X.tl, whatever makes the
                   routines. By `built_tl` (Johnson/Desc/First/Link/Law/K9RowsAskLaw.lean) and
                   `blankBy_W` (MakerPublic.lean)
  **`matsOwn_meets_blank`**   so `matsOwn_meets` holds there with no premise on the lists
  **`matsMeetB_blank`**   at the ground that the description's lots are made at: matsMeetB G = true.
                   That it has 25 segments: `IM.ground_gets` (Johnson/IMR/PureJoin.lean)
Limits. IN SCOPE ALONE, SO AT THE FULL SIZE ALONE: NOTHING AT THE SMALL EXAMPLE. At the earlier hash
alone. At the ground for a request of zeros alone: of the ground that the tests on an instance
return (`holdBy`) nothing is said, though its text lays the same two fields. ON PUBLIC DATA ALONE.
That any files are in scope is no theorem here. All limits of MatsMeet.lean but the one on the two
lists stand here too: nothing on whether a key names the right cells.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.MatsMeet
import Johnson.Desc.First.Link.Law.K9AtPub
import Johnson.Desc.First.Link.Law.K9RowsAskLaw
import Johnson.IMR.PureJoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open OnBytes.Model (TMat)
open OnBytes.Model.Stages (LinkH)

variable {P : _root_.VerifierAndGoals.PublicFiles} {lay : ByteArray} {Z : Pub}

/-- At the public part's own built segment. -/
theorem tlOf_at_pub (hS : _root_.VerifierAndGoals.InScope P = true)
    (hpub : pureRoad.pub OnBytes.secondHashFunction P.pol lay P.KL = .ok Z) {l : Nat} (hl : l < 25)
    {X : LinkH} (hX : Z.p.built.links[l]? = some X) : K3.tlOf Z.p.X l = X.tl := by
  obtain ⟨pp, hR⟩ := _root_.H2K.Sizes.inScope_readFiles hS
  have hW : OnBytes.Model.Verify.publicOf P.pol P.KL (some lay) = .ok Z.p.X :=
    (VerifiableInference.PlanWritten.publicOfO_older P.pol P.KL (some lay)).symm.trans
      (ProofFile.Law.pub_public hpub)
  obtain ⟨b, hb, e⟩ := ProofFile.Law.pub_builtOf hpub
  have hX' : (ProofFile.Law.blankB b).links[l]? = some X := by
    rw [e]
    exact hX
  obtain ⟨c, hc, t, -, -⟩ := VerifiableInference.Desc.K9Asks.blank_at hX'
  rw [tlOf_of_tlAt (VerifiableInference.Desc.K9Asks.tlAt_built hS hR hW hb hl hc), t]

/-- **At the ground for a request of zeros, whatever makes the routines.** -/
theorem tlOf_at_blank (hS : _root_.VerifierAndGoals.InScope P = true)
    (hpub : pureRoad.pub OnBytes.secondHashFunction P.pol lay P.KL = .ok Z) {mk : LinksBy} {G : Ground}
    (hG : blankBy mk Z = some G) {l : Nat} (hl : l < 25) {X : LinkH}
    (hX : G.built[l]? = some X) : K3.tlOf G.W l = X.tl := by
  obtain ⟨X', hX', e⟩ := VerifiableInference.Desc.K9Asks.built_tl hG hX
  rw [ProofFile.Law.blankBy_W hG, tlOf_at_pub hS hpub hl hX', e]

/-- **Entry for entry and in order, with no premise on the lists.** -/
theorem matsOwn_meets_blank (hS : _root_.VerifierAndGoals.InScope P = true)
    (hpub : pureRoad.pub OnBytes.secondHashFunction P.pol lay P.KL = .ok Z) {mk : LinksBy} {G : Ground}
    (hG : blankBy mk Z = some G) {l : Nat} (hl : l < 25) {X : LinkH}
    (hX : G.built[l]? = some X) :
    (K3.matsOwn G.W l).length = (k8Par Z G X l).ks.length ∧
      smallFits (k8Par Z G X l, K3.matsOwn G.W l) = true ∧
      ∀ (mu : Nat) (M : TMat), X.tl.mats[mu]? = some M →
        (K3.matsOwn G.W l)[mu]? =
            some ((K3.ownerOf G.W l M).1, (K3.ownerOf G.W l M).2, M.ttOff) ∧
          (k8Par Z G X l).ks[mu]? = some M.k ∧ (k8Par Z G X l).ms[mu]? = some M.m :=
  matsOwn_meets Z G X l (by rw [tlOf_at_blank hS hpub hG hl hX])

/-- **The test says yes at the ground that the description's lots are made at.** -/
theorem matsMeetB_blank (hS : _root_.VerifierAndGoals.InScope P = true)
    (hpub : pureRoad.pub OnBytes.secondHashFunction P.pol lay P.KL = .ok Z) {G : Ground}
    (hG : blankBy pureRoad.links Z = some G) : matsMeetB G = true := by
  obtain ⟨pp, hR⟩ := _root_.H2K.Sizes.inScope_readFiles hS
  have h25 : G.built.size = 25 := (_root_.IM.ground_gets hS hR hpub hG).1
  rw [matsMeetB_iff]
  intro y hy
  have h := List.mem_zipIdx_iff_getElem?.1 hy
  rw [Array.getElem?_toList] at h
  have hlt : y.2 < G.built.size := (Array.getElem?_eq_some_iff.1 h).1
  rw [tlOf_at_blank hS hpub hG (by omega) h]

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.tlOf_at_pub
#print axioms ProofFile.Honest.K8.tlOf_at_blank
#print axioms ProofFile.Honest.K8.matsOwn_meets_blank
#print axioms ProofFile.Honest.K8.matsMeetB_blank
