-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/ReadsRoomInScope.lean: THE TEST readsRoomC OF Law/ReadsEntInT.lean ACCEPTS AT
THE SEGMENTS' STRUCTURES AS THE VERIFIER BUILDS THEM OF ITS PUBLIC PART (OnBytes/Model/
VerifyStages.lean: builtOf), AT THE LAYOUT IN THE FIRST CHAIN's PARAMETERS; AND THE OUTPUT HEAD's
VECTOR OF READS STANDS IN ITS LIST OF ARRAYS UNDER THE NAME "U3". Statements and proofs.

By Law/ReadsRoomOfBuilt.lean's reads_named_of_built (the law on buildLinksH, at the last segment),
OnBytes/Tie/Pv/Keeps/LinksOrder.lean's listLinksH_with (the head's segment is the last, number
2 NGr), Law/ReadsNamed.lean's public_third (the head's plan numbers its third vector as array 0) and
Law/ReadsArray.lean's public_array (that array has one row and as many columns as the vector is
long).

  reads_room_of_public   at any files at which publicOf returns, with attention covered.
  reads_room_in_scope    at all public files in the goals' scope: at segment 24.

WHAT IT IS NOT. Facts on public parameters alone. Nothing on soundness. UNDER THE LIBRARY's
publicOf. That builtOf returns is a PREMISE. It speaks of built.links and of
chains.proof.first.layout: that a law's letters (a composed meaning's built and layout) ARE these is
whoever fills them in's to say.
LETTERS. No letter stands under "there is".

-/
import Johnson.Desc.Kinds.Law.ReadsRoomOfBuilt
import Johnson.Desc.Kinds.Law.ReadsEntInT
import Johnson.Desc.Kinds.Law.ReadsNamed
import Johnson.Desc.Kinds.Law.ReadsArray
import Johnson.Desc.Kinds.Law.K6PubInScope
import OnBytes.Tie.Pv.Keeps.LinksOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law.InScope

open OnBytes
open OnBytes.Model.Verify (publicOf builtOf linksOf)
open OnBytes.TieK (ok_of_bind)

/-- **At any files at which the public part is made, with attention covered.** -/
theorem reads_room_of_public {pol KL : ByteArray} {lay : Option ByteArray}
    {X : OnBytes.Model.Verify.Public} {chains : OnBytes.Model.Verify.Chains}
    {built : OnBytes.Model.Stages.LinksH} (h : publicOf pol KL lay = .ok X) (h4 : X.p4 = true)
    (hb : builtOf X chains = .ok built) :
    ((built.links.map (·.arrayOf)).getD (2 * X.NGr) #[])[0]? = some (2 * X.NGr, "U3") ∧
      readsRoomC X chains.proof.first.layout
        ((built.links.map (·.arrayOf)).getD (2 * X.NGr) #[]) = true := by
  unfold builtOf at hb
  obtain ⟨l₀, hl, hb⟩ := ok_of_bind hb
  unfold linksOf at hl
  rw [h4] at hl
  obtain ⟨_, _, z, _, e⟩ := OnBytes.L5.LinksOrder.listLinksH_with _ _ _ _ _ hl
  have T : X.H.tl.ix.U.getD 2 none = some 0 := ReadsNamed.public_third h
  obtain ⟨c1, tr, A, c2, c3, c4, c5⟩ := Built.reads_named_of_built hb z e (t := 0) T
  obtain ⟨p0, pK, pR, _⟩ := ReadsArray.public_array h
  have c2' : X.H.Fp.trees[0]? = some tr := c2
  have etr : X.H.Fp.trees.getD 0 {} = tr := by
    rw [Array.getD_eq_getD_getElem?, c2']
    rfl
  rw [etr] at pK pR
  refine ⟨c1, ?_⟩
  have e0 : readsOf X = 0 := by
    unfold readsOf
    rw [T]
    rfl
  unfold readsRoomC
  rw [e0, c1]
  show ((reqArray chains.proof.first.layout (2 * X.NGr) "U3").any fun A =>
    Decidable.decide (0 < A.sizeI) && Decidable.decide (X.H.nU.getD 2 0 ≤ A.sizeC)) = true
  rw [c3]
  show (Decidable.decide (0 < A.sizeI) && Decidable.decide (X.H.nU.getD 2 0 ≤ A.sizeC)) = true
  rw [c4, c5, pR, pK]
  simp

/-- **AT ALL PUBLIC FILES IN THE GOALS' SCOPE: AT SEGMENT 24.** -/
theorem reads_room_in_scope {Z : VerifierAndGoals.PublicFiles} {lay : Option ByteArray}
    {X : OnBytes.Model.Verify.Public} {chains : OnBytes.Model.Verify.Chains}
    {built : OnBytes.Model.Stages.LinksH} (hZ : VerifierAndGoals.InScope Z = true)
    (h : publicOf Z.pol Z.KL lay = .ok X) (hb : builtOf X chains = .ok built) :
    ((built.links.map (·.arrayOf)).getD 24 #[])[0]? = some (24, "U3") ∧
      readsRoomC X chains.proof.first.layout
        ((built.links.map (·.arrayOf)).getD 24 #[]) = true := by
  obtain ⟨h4, hN⟩ := head_24 hZ h
  have K := reads_room_of_public h h4 hb
  rw [hN] at K
  exact K

end VerifiableInference.Desc.Kinds.Head.Law.InScope

#print axioms VerifiableInference.Desc.Kinds.Head.Law.InScope.reads_room_of_public
#print axioms VerifiableInference.Desc.Kinds.Head.Law.InScope.reads_room_in_scope
