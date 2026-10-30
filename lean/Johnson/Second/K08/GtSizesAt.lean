-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Second/K08/GtSizesAt.lean: ONE MORE TEST ON THE PUBLIC PARAMETERS FOR THE APPROXIMATE RANGE PROOF's LAWS, WITH ITS LAW AND ITS EVALUATION (it pays MakesOwes.gt, Johnson/P1K8R/MakesAt.lean): at every planned value of the sub-protocol's part of the verifier's state there are JUST AS MANY numbers of symbol arrays as matrices: tl.gtTree.size = tl.NM. (planFitsB (Johnson/Desc/First/K8/PlanFits.lean) asks only NM ≤ size.)
  gtSizesAllB W     the test, to K8's files' letter: at each plan of a layers' sub-proof (W.G), at the seam of each plan of an attention sub-proof (W.A), at the head's plan (W.H).
  gtSizes_of_B    gtSizesAllB W = true → at every tlP that is a layers' entry's, an attention entry's seam's, or the head's: tlP.gtTree.size = tlP.NM. THE PREMISE ON tlP IS THE BODY OF P1K8S.PlanVal W tlP (Johnson/P1K8R/FrontAtSeat.lean), WRITTEN OUT, so that this file needs none of what that file imports: PlanVal is a def: a term of it is taken as it stands.
  rows · asDue      the test whole · its three conjuncts apart · the sizes · the head's two numbers · negative tests at the head's value: gtTree := #[] · NM one more.
  THE EVALUATIONS (#eval prints; #guard holds): VerifierAndGoals.storedPublicFiles · VerifierAndGoals.zGap · the library's small example.
Limits. AN EVALUATION AT ONE VALUE IS NO THEOREM. Three public files; no byte of a proof; no weight. DUE: the test and its conjuncts true; both negative tests false. No soundness is claimed.

-/
import OnBytes.Model.VerifyPublic
import Johnson.Desc.First.State
import Ladder.Stored
import OnBytes.Tie.Pv.Plan.PlanLayoutSmall
import OnBytes.Tie.Pv.Plan.PlanKits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Second.K08
open OnBytes OnBytes.Model

def gtSizesAllB (W : Verify.Public) : Bool :=
  (W.G.all fun hp => hp.tl.gtTree.size == hp.tl.NM) &&
    (W.A.all fun a => a.seam.tl.gtTree.size == a.seam.tl.NM) && (W.H.tl.gtTree.size == W.H.tl.NM)


theorem gtSizes_of_B {W : Verify.Public} (h : gtSizesAllB W = true) (tlP : HTailF2)
    (hv : (∃ (g : Nat) (hp : Layer.HPlan2), W.G[g]? = some hp ∧ tlP = hp.tl) ∨
      (∃ (g : Nat) (a : Attention.Plan), W.A[g]? = some a ∧ tlP = a.seam.tl) ∨ tlP = W.H.tl) :
    tlP.gtTree.size = tlP.NM := by
  unfold gtSizesAllB at h
  simp only [Bool.and_eq_true, Array.all_eq_true_iff_forall_mem, beq_iff_eq] at h
  obtain ⟨⟨hG, hA⟩, hH⟩ := h
  rcases hv with ⟨g, hp, e, rfl⟩ | ⟨g, a, e, rfl⟩ | rfl
  · exact hG hp (Array.mem_of_getElem? e)
  · exact hA a (Array.mem_of_getElem? e)
  · exact hH

structure GtRows where
  whole : Bool
  layers : Bool
  attention : Bool
  head : Bool
  sizeG : Nat
  sizeA : Nat
  headTrees : Nat
  headNM : Nat
  /-- negative tests: each must be false -/
  noTrees : Bool
  moreNM : Bool
  deriving Repr

def gtRows (pol lay KL : ByteArray) : Except String GtRows :=
  match Verify.publicOf pol KL (some lay) with
  | .ok W =>
    .ok { whole := gtSizesAllB W
          layers := W.G.all fun hp => hp.tl.gtTree.size == hp.tl.NM
          attention := W.A.all fun a => a.seam.tl.gtTree.size == a.seam.tl.NM
          head := W.H.tl.gtTree.size == W.H.tl.NM
          sizeG := W.G.size, sizeA := W.A.size
          headTrees := W.H.tl.gtTree.size, headNM := W.H.tl.NM
          noTrees := gtSizesAllB { W with H := { W.H with tl := { W.H.tl with gtTree := #[] } } }
          moreNM := gtSizesAllB { W with H := { W.H with tl := { W.H.tl with NM := W.H.tl.NM + 1 } } } }
  | .error e => .error e

def gtAsDue (pol lay KL : ByteArray) (g a : Nat) : Bool :=
  match gtRows pol lay KL with
  | .ok r => r.whole && r.layers && r.attention && r.head && r.sizeG == g && r.sizeA == a &&
      !r.noTrees && !r.moreNM
  | .error _ => false

-- THE EVALUATIONS
#eval gtRows VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.lay VerifierAndGoals.storedPublicFiles.KL
#guard gtAsDue VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.lay VerifierAndGoals.storedPublicFiles.KL 12 12
#eval gtRows VerifierAndGoals.zGap.pol VerifierAndGoals.zGap.lay VerifierAndGoals.zGap.KL
#guard gtAsDue VerifierAndGoals.zGap.pol VerifierAndGoals.zGap.lay VerifierAndGoals.zGap.KL 12 12
open OnBytes.Tie.Pv.Plan in
#eval gtRows (textOf policyS) layoutS.toUTF8 (wordsFile scalesS)
open OnBytes.Tie.Pv.Plan in
#guard gtAsDue (textOf policyS) layoutS.toUTF8 (wordsFile scalesS) 2 2

end Second.K08

#print axioms Second.K08.gtSizes_of_B
