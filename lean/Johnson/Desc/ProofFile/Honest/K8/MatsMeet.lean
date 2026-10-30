-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K8/MatsMeet.lean: the honest side of the smallness test (K8): THE LIST
OF MATRICES THAT THE KIND "LOOKUP" MAKES FOR A LINK (`K3.matsOwn`,
Johnson/Desc/ProofFile/Honest/K3/WitOwner.lean: for each entry its owner's segment, its name there,
its first column there) HELD AGAINST THE LIST THAT THE SMALLNESS TEST's BLOCK HAS AT A PLACE
(`ProofFile.k8Par`, Johnson/Desc/ProofFile/Lot/K8.lean). THE ONE SEAM: `K3.matsOwn` walks the list in the
public parameters' plan of the link (`K3.tlOf`); the block takes its numbers of columns and of rows
off the list in the built segment's plan. WHERE THESE TWO LISTS ARE ONE, THE NAMES STAND ENTRY FOR
ENTRY AND IN ORDER AT THE BLOCK's OWN MATRICES. No maker is written here. Lemmas by unfolding, and
one test with code; none of the library's goals.

  `tlOf_getD`   `K3.tlOf` is the library's `tlAt` (Johnson/Desc/First/Look/Laid.lean), with the
                   empty plan where that has none. Kin, not called: `K3.tlAt_tlOf`
                   (Johnson/Desc/ProofFile/Honest/K3/Law/OwnerKeyIs.lean) says it of the lists'
                   entries, one by one; this says it of the whole plan
  `tlOf_of_tlAt`   so tlAt W l = some t ⊢ K3.tlOf W l = t: the form in which the library's
                   `tlAt_built` (Johnson/Desc/First/Link/Law/K9DigStatic.lean) ends: not called here
  `matsOwn_matsBy`   the two lists are one ⊢ K3.matsOwn G.W l is `matsBy`
                   (Johnson/Desc/ProofFile/Honest/K8/MatsBy.lean) at the lookup's own key
  **`matsOwn_meets`**   the two lists are one ⊢ as many names as the place has matrices · the public
                   premise at the seat (`smallFits`, Honest/K8/Part.lean) says yes · at every number
                   mu: where the built segment's list has the entry M, the names have at mu the key
                   of M, and the block has at mu M's number of columns and M's number of rows
  `matsOwn_here`   at an entry that passes the lookup's own test on a mark (`K3.markFitsB`,
                   Honest/K3/WitFits.lean) and is not borrowed, the key is: this segment's number,
                   the entry's own name, column 0
  **`matsMeetB G`**   THE TEST, WITH CODE, ON A GROUND: at every built segment the two lists are
                   equal, entry for entry
  `matsMeetB_iff`   what its yes means
  **`matsOwn_fits`**   matsMeetB G = true ⊢ at every built segment, in the order in which the lot's
                   honest side walks them: `smallFits` says yes at K3.matsOwn
Limits. ON PUBLIC DATA ALONE. THAT THE TWO LISTS ARE ONE IS A PREMISE OR THE TEST's YES: SHOWN OF NO
GROUND HERE; the test has been run at no public files. At the full size the library's `tlAt_built`
ends in the equation of the two plans, in its scope, of what `publicOf` and `builtOf` return: that a
ground's public parameters and built segments are these is not said here; of the ground for a
request of zeros Johnson/Desc/ProofFile/Honest/K8/MatsScope.lean says it. Nothing on whether a key
names the right cells: nothing holds it against a layout or a committed table; that an `aId` names
the owner as the key reads it is read off the makers of the plans' lists (WitOwner.lean's own
limit). IT STANDS OVER FILES OF THE KIND "LOOKUP" THAT ARE NO PART OF THE LIBRARY YET: it is no
better than they, and follows them if they turn. Nothing on what a half plays.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.MatsBy
import Johnson.Desc.ProofFile.Honest.K3.WitFits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open OnBytes.Model (TMat HTailF2)
open OnBytes.Model.Stages (LinkH)

/-- `K3.tlOf` is the library's `tlAt`, with the empty plan where that has none. -/
theorem tlOf_getD (W : OnBytes.Model.Verify.Public) (l : Nat) :
    K3.tlOf W l = (VerifiableInference.Desc.First.Look.tlAt W l).getD {} := by
  unfold K3.tlOf VerifiableInference.Desc.First.Look.tlAt K3.linkH K3.stepOf
  dsimp only
  split <;> split <;> first | rfl | (split <;> rfl)

/-- The form in which the library's law on the built segments ends. -/
theorem tlOf_of_tlAt {W : OnBytes.Model.Verify.Public} {l : Nat} {t : HTailF2}
    (h : VerifiableInference.Desc.First.Look.tlAt W l = some t) : K3.tlOf W l = t := by
  rw [tlOf_getD, h]
  rfl

/-- Where the two lists are one, the lookup's list is `matsBy` at the lookup's own key. -/
theorem matsOwn_matsBy (Z : Pub) (G : Ground) (X : LinkH) (l : Nat)
    (h : (K3.tlOf G.W l).mats = X.tl.mats) :
    K3.matsOwn G.W l =
      matsBy (fun _ G l M => ((K3.ownerOf G.W l M).1, (K3.ownerOf G.W l M).2, M.ttOff))
        Z G X l := by
  unfold K3.matsOwn matsBy
  rw [h]

/-- **ENTRY FOR ENTRY AND IN ORDER, WHERE THE TWO LISTS ARE ONE.** -/
theorem matsOwn_meets (Z : Pub) (G : Ground) (X : LinkH) (l : Nat)
    (h : (K3.tlOf G.W l).mats = X.tl.mats) :
    (K3.matsOwn G.W l).length = (k8Par Z G X l).ks.length ∧
      smallFits (k8Par Z G X l, K3.matsOwn G.W l) = true ∧
      ∀ (mu : Nat) (M : TMat), X.tl.mats[mu]? = some M →
        (K3.matsOwn G.W l)[mu]? =
            some ((K3.ownerOf G.W l M).1, (K3.ownerOf G.W l M).2, M.ttOff) ∧
          (k8Par Z G X l).ks[mu]? = some M.k ∧ (k8Par Z G X l).ms[mu]? = some M.m := by
  rw [matsOwn_matsBy Z G X l h]
  refine ⟨matsBy_length _ Z G X l, smallFits_matsBy _ Z G X l, fun mu M hM => ⟨?_, ?_, ?_⟩⟩
  · simp [matsBy_get, hM]
  · simp [k8Par, hM]
  · simp [k8Par, hM]

/-- At an entry that passes the lookup's test on a mark and is not borrowed. -/
theorem matsOwn_here (W : OnBytes.Model.Verify.Public) (l : Nat) (M : TMat)
    (hf : K3.markFitsB W l M = true) (hk : M.kind = 0) :
    ((K3.ownerOf W l M).1, (K3.ownerOf W l M).2, M.ttOff) = (l, M.name, 0) := by
  have h0 : M.ttOff = 0 := by
    unfold K3.markFitsB at hf
    rw [if_pos (by simp [hk])] at hf
    exact beq_iff_eq.1 hf
  rw [K3.ownerOf_own W l M (by rw [hk]; decide), h0]

/-- **THE TEST: at every built segment the two lists are equal, entry for entry.** -/
def matsMeetB (G : Ground) : Bool :=
  G.built.toList.zipIdx.all fun y => (K3.tlOf G.W y.2).mats == y.1.tl.mats

/-- What its yes means. -/
theorem matsMeetB_iff (G : Ground) :
    matsMeetB G = true ↔ ∀ y ∈ G.built.toList.zipIdx, (K3.tlOf G.W y.2).mats = y.1.tl.mats := by
  simp only [matsMeetB, List.all_eq_true, beq_iff_eq]

/-- **Under the test the public premise at the seat holds at every built segment.** -/
theorem matsOwn_fits (Z : Pub) (G : Ground) (h : matsMeetB G = true) :
    ∀ y ∈ G.built.toList.zipIdx, smallFits (k8Par Z G y.1 y.2, K3.matsOwn G.W y.2) = true :=
  fun y hy => (matsOwn_meets Z G y.1 y.2 ((matsMeetB_iff G).1 h y hy)).2.1

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.tlOf_getD
#print axioms ProofFile.Honest.K8.tlOf_of_tlAt
#print axioms ProofFile.Honest.K8.matsOwn_matsBy
#print axioms ProofFile.Honest.K8.matsOwn_meets
#print axioms ProofFile.Honest.K8.matsOwn_here
#print axioms ProofFile.Honest.K8.matsMeetB_iff
#print axioms ProofFile.Honest.K8.matsOwn_fits
