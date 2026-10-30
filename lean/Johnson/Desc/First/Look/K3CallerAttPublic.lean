-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3CallerAttPublic.lean: WHAT IS ASKED OF THE PUBLIC DATA AT AN ATTENTION
LINK's
CALLS (AttOK, Johnson/Desc/First/Look/K3CallerAtt.lean), AT THE PLACE THAT lookAt MAKES OF A RECORD
THAT Verify.publicOf RETURNS: three of its five fields are laws; two stay premises. Statements and
proofs. NO SOUNDNESS IS CLAIMED.

Why. AttOK's five fields were had by five tests at shipped example sets. Three of them no public
file can make fail: shape, planes, masksIn. The other two, «there are the library's four calls» and
the library's condition between the lookup's record and the segment's sizes, hang on the parameter
file's own lines of calls: the verifier program takes other lists (its reader admits from one to
twelve lines; Johnson/Road/Lane5AttLaid.lean's head says so of UsualCalls).

Main names:
  `planes_toBool`: Forest.planeCols returns where 5 ≤ lm ≤ kT + 5.
  `attOK_public`: publicOf = ok X, lookAt X i false = some x at an attention link, x.fs.NC = 4 and
    attFitsB S x.fs = true give AttOK set x S tl D rad, for every set, tl, D, rad.
  `four_public`: under the library's UsualCalls at the plan's configuration the plan's record has
    four calls. `attOK_usual`: attOK_public with that in the place of «NC = 4».

Limits. One direction: from publicOf's equation. attFitsB STAYS A PREMISE. UsualCalls is no test of
the verifier program. S, tl, D, rad are letters in AttOK: of its fields fits alone reads S, and none
reads tl, D or rad. Nothing on AttReadsOK.
Not claimed: anything on completeness or hiding.

-/
import Johnson.Desc.First.Look.K3CallerMasksLaw
import Johnson.Road.Lane5SameCalls

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Look
open OnBytes OnBytes.Model

/-- The program's test on the planes' packing returns inside the two bounds. -/
theorem planes_toBool {fs : Forest.Shape} {lm : ℕ} (h5 : 5 ≤ lm) (hl : lm ≤ fs.kT + 5) :
    (Forest.planeCols fs lm).toBool = true := by
  unfold Forest.planeCols
  rw [if_neg (by
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    omega)]
  rfl

section
variable {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public} {i : ℕ} {x : Place}

/-- **Three fields are laws; two stay premises.** -/
theorem attOK_public (h : Verify.publicOf pol KL layout = .ok X) (e : lookAt X i false = some x)
    (hn : i ≠ (if X.p4 then 2 else 1) * X.NGr) (h0 : i % (if X.p4 then 2 else 1) ≠ 0)
    {S : Attention.Shape} (h4 : x.fs.NC = 4) (hf : attFitsB S x.fs = true)
    (set : Params.Setting) (tl : HTailF2) (D : Sent) (rad : OracleShape → Nat) :
    AttOK set x S tl D rad := by
  obtain ⟨a, tl', -, -, hp⟩ := att_planes h e hn h0
  obtain ⟨b5, bl, -⟩ := planesAtB_iff.1 hp
  exact ⟨att_shape set h e hn h0, h4, planes_toBool b5 bl, hf,
    of_decide_eq_true (att_masks h e hn h0)⟩

/-- Under the usual call list the plan's record has four calls. -/
theorem four_public (h : Verify.publicOf pol KL layout = .ok X) (g : ℕ) (a : Attention.Plan)
    (hg : X.A[g]? = some a) (U : Road.L5.UsualCalls a.S.cf) : a.fs.NC = 4 := by
  obtain ⟨sc, lines, cf, a0, -, -, -, hp, ha, -, -⟩ := _root_.Fo.Pub.public_A h g a hg
  obtain ⟨hS, -⟩ := _root_.Fo.Pub.planA_shapeHid _ _ cf a0 hp
  have hcf : a0.S.cf = cf := (_root_.Fo.Pub2.shapeOf_shapeHid hS).2
  have eS : a.S = a0.S := by rw [ha]
  have eF : a.fs = a0.fs := by rw [ha]
  rw [eS, hcf] at U
  rw [eF]
  exact (Road.L5.nc_of_hid hS).trans (Road.L5.four_of_hid hS U).size

/-- attOK_public with the usual call list in the place of «NC = 4». -/
theorem attOK_usual (h : Verify.publicOf pol KL layout = .ok X) (e : lookAt X i false = some x)
    (hn : i ≠ (if X.p4 then 2 else 1) * X.NGr) (h0 : i % (if X.p4 then 2 else 1) ≠ 0)
    (U : ∀ a, X.A[i / (if X.p4 then 2 else 1)]? = some a → Road.L5.UsualCalls a.S.cf)
    {S : Attention.Shape} (hf : attFitsB S x.fs = true)
    (set : Params.Setting) (tl : HTailF2) (D : Sent) (rad : OracleShape → Nat) :
    AttOK set x S tl D rad := by
  obtain ⟨a, hg, -, e1, -⟩ := lookAt_att e hn h0
  refine attOK_public h e hn h0 ?_ hf set tl D rad
  rw [e1]
  exact four_public h _ a hg (U a hg)

end

end VerifiableInference.Desc.First.Look

#print axioms VerifiableInference.Desc.First.Look.planes_toBool
#print axioms VerifiableInference.Desc.First.Look.attOK_public
#print axioms VerifiableInference.Desc.First.Look.four_public
#print axioms VerifiableInference.Desc.First.Look.attOK_usual
