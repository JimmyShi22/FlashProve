-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AT NO FILLING: ON PUBLIC DATA ALONE, IN THE GOALS' SCOPE: no prover and no filling is read.
Johnson/Desc/ProofFile/Honest/K3/Term/LinkScalarsInScope.lean: the kind "lookup" (K3): how many
scalars a layers' link and an attention link send between their two lookups, at all public files in
the goals' scope: written numbers. Two closed facts on numerals, each with a control; theorems; no
definition.

Why. The first scalar of a link's lookup on the digits is the link's number of scalars less that
lookup's own (`lookAt`, Johnson/Desc/First/Look/LookAt.lean). The planner adds the link's number up
of three: the lookup on the calls, the link's own rounds, the lookup on the digits. Here the middle
one is shown to be a written number in scope.

What is shown.
  `layersOwnScalarsWritten`: a closed fact: the planner's terms for a layers' link's own rounds, at
    the written numbers, add up to 765. `layersOwnScalarsWrittenCanFail`: a control: with one round
    more in the batched sumcheck they do not.
  `layersSlotsAtTheWrittenNumbers`: at every layout and reads with the thirteen written numbers:
    `Layer.slotsOf` is the lookup's scalars, 765 (766 in the first group), and the last argument.
  `layersLinkScalarsInScope`: **in scope, g < 12: hp.ns = elems X.y.fo + 765 | 766 + elems f9.**
  `attentionOwnScalarsWritten`: a closed fact: the stages of an attention link's own rounds, at the
    eleven written numbers, take 1072 scalars, whatever the field rows.
    `attentionOwnScalarsWrittenCanFail`: a control: with 16 bits for 17 they do not.
  `attentionLinkScalarsInScope`: **in scope, g < 12: a.ns = elems a.fs + 1072 + elems f9.**

How the proof goes. The layers: `planG_slots` (Johnson/Road/K4/Riders/LookInByMake.lean): the plan's
number is `Layer.slotsOf`; `refPub_in_scope` (Johnson/Road/K4/RefInScope.lean): in scope the layout,
the reads and the layout of the committed matrix are the makers' at a shape that agrees with the
reference sizes, and K4's text covers the record; `dimIs_layerNumbers`
(Johnson/Road/K4/PlanSizes.lean) and `readsOf_mu`: so each number that `slotsOf` reads is a numeral.
Attention: `planIs_tiles` (Johnson/Desc/First/Att/K05PlanOfPublic.lean) and `own_in_scope`
(Johnson/Desc/First/Att/Row/K5OwnInScope.lean).

Hypotheses that remain. `scope`, `read`, `publicRecord`: the files are in scope, are read, and
`publicOf` returns X at them. `groupBelow`: g < 12. The plan stands at g.

Limits. The default table of scales (`Inst.Model.Scl.ref`) is not struck in this file, as it is in its sisters:
`dimIs_layerNumbers` takes a table as an instance; the ends name no scale, so nothing hangs on which table that is. The two
lookups' own scalars stay `Forest.elems` of their shapes. The head's link is not
spoken of. The full size alone: that limit comes with the scope.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Road.K4.RefInScope
import Johnson.Road.K4.PlanSizes
import Johnson.Road.K4.Riders.LookInByMake
import Johnson.Desc.First.Att.K05PlanOfPublic
import Johnson.Desc.First.Att.Row.K5OwnInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Term
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Lay Reads HPlan2 slotsOf lamSOf nclOf shownByTerms)
open Inst.Model.FFSeg (Dim)

/-! ## 1 The layers -/

/-- **A closed fact**: the planner's terms for the own rounds of a layers' link, at the written
numbers. -/
theorem layersOwnScalarsWritten :
    ledNS 5 * 8 + layerSlots 26 + ledNP 5 * 8 + tscSlots 10 (ledNO 5 * 8) 2 + tscSlots 10 266 1 +
      sumcheckSlots .sum2 23 37 2 + layerSlots 26 + layerSlots 24 + wsForkSlots 18 = 765 := by
  decide

/-- A control: with one round more in the batched sumcheck the sum is another. -/
theorem layersOwnScalarsWrittenCanFail :
    ledNS 5 * 8 + layerSlots 26 + ledNP 5 * 8 + tscSlots 10 (ledNO 5 * 8) 2 + tscSlots 10 266 1 +
      sumcheckSlots .sum2 24 37 2 + layerSlots 26 + layerSlots 24 + wsForkSlots 18 ≠ 765 := by
  decide

/-- At the thirteen written numbers the planner's sum is the lookup's scalars, the written number,
and its last argument. -/
theorem layersSlotsAtTheWrittenNumbers (y : Lay) (rd : Reads) (g lk small : Nat)
    (limbs : y.h.xl = 5) (routed : y.h.p3 = true) (instances : y.NI = 8) (tokens : y.h.lt = 10)
    (normsLayer : rd.muV = 26) (withTerms : rd.tscCalls.isEmpty = false)
    (shown : shownByTerms y rd = 266) (batched : lamSOf y = 23) (mixtures : y.LamM = 2)
    (claims : nclOf y g - (if g == 0 then 1 else 0) = 32) (gated : rd.muH = 26)
    (gatedSecond : rd.muH2 = 24) (merge : lk = 18) :
    slotsOf y rd g lk small = Forest.elems y.fo + (if g = 0 then 766 else 765) + small := by
  have closed := layersOwnScalarsWritten
  unfold slotsOf
  simp only [limbs, routed, instances, tokens, normsLayer, withTerms, shown, batched, mixtures,
    gated, gatedSecond, merge, if_true, Bool.false_eq_true, if_false]
  by_cases first : g = 0
  · subst first
    simp only [beq_self_eq_true, if_true] at claims ⊢
    have ends : 2 + 1 + 2 + nclOf y 0 - 1 = 37 := by omega
    rw [ends]
    omega
  · have notFirst : (g == 0) = false := beq_false_of_ne first
    simp only [notFirst, Bool.false_eq_true, if_false, if_neg first] at claims ⊢
    have ends : 2 + 1 + 2 + nclOf y g - 0 = 37 := by omega
    rw [ends]
    omega

variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {X : Verify.Public}

/-- **IN SCOPE A LAYERS' LINK SENDS: ITS LOOKUP ON THE CALLS, 765 SCALARS (766 IN THE FIRST GROUP),
ITS LOOKUP ON THE DIGITS.** -/
theorem layersLinkScalarsInScope (scope : VerifierAndGoals.InScope Z = true)
    (read : VerifierAndGoals.readFiles Z = .ok pp) (publicRecord : Verify.publicOf Z.pol Z.KL lay = .ok X)
    {g : Nat} (groupBelow : g < 12) {hp : HPlan2} (groupPlan : X.G[g]? = some hp) :
    hp.ns = Forest.elems X.y.fo + (if g = 0 then 766 else 765) + Forest.elems hp.tl.f9 := by
  have record := OnBytes.Road.K4.refPub_in_scope scope read publicRecord groupBelow
  obtain ⟨s0, lines, -⟩ := record.lines hp groupPlan
  have line := lines #[]
  obtain ⟨batchedIs, claimsAre, slots⟩ := OnBytes.Road.K4.Riders.planG_slots _ _ _ _
    (Fo.Pub.public_G publicRecord g hp groupPlan)
  have sizes := OnBytes.Road.K4.dimIs_layerNumbers (P := X.layers) (hp := hp) (g := g) line.hy
    record.covers line.hrd line.Z batchedIs claimsAre
  obtain ⟨limbs, routed, -⟩ := OnBytes.Road.K4.covers_shape record.covers
  obtain ⟨normsLayer, gated, gatedSecond⟩ := Fo.readsOf_mu (y := X.layers.y) (rd := X.layers.rd)
    line.hrd
  have withTerms : X.layers.rd.tscCalls.isEmpty = false := by
    have covered := record.covers
    unfold OnBytes.Desc.First.K4.covers at covered
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at covered
    exact covered.2
  have tokens : X.layers.y.h.lt = 10 := sizes.lt.symm
  have layersBits : X.layers.y.h.ll = 2 := sizes.ll.symm
  have instancesBits : X.layers.rd.lNI = 3 := sizes.lNI.symm
  have normsBits : X.layers.y.lPd = 13 := sizes.lPd.symm
  have gatedBits : X.layers.y.lPf = 14 := sizes.lPf.symm
  have gatedSecondBits : X.layers.y.lfe = 13 := sizes.lfe.symm
  have never : 1 + (if X.layers.y.h.p3 then X.layers.y.LamM else 0) = 3 := sizes.never.symm
  rw [routed, if_pos rfl] at never
  rw [slots]
  exact layersSlotsAtTheWrittenNumbers X.layers.y X.layers.rd g X.layers.wsLay.lk _ limbs routed
    sizes.NI.symm tokens
    (by rw [normsLayer, instancesBits, normsBits, tokens]) withTerms sizes.shown.symm
    (batchedIs.symm.trans sizes.lamS.symm) (by omega)
    (by rw [← claimsAre]; exact sizes.claims.symm)
    (by rw [gated, layersBits, gatedBits, tokens])
    (by rw [gatedSecond, layersBits, gatedSecondBits, tokens])
    (OnBytes.Road.wsLayOf_units line.hlw).1

/-! ## 2 Attention -/

open VerifiableInference.Desc.First.Att.P (script slotsOf planIs_tiles planIs_public) in
/-- **A closed fact**: the stages of an attention link's own rounds, at the eleven written numbers,
take 1072 scalars, whatever the field rows. -/
theorem attentionOwnScalarsWritten (rows : Nat) :
    slotsOf (script { H2K5.Row.ownW with rows := rows }) = 1072 := by
  show slotsOf (script H2K5.Row.ownW) = 1072
  decide +kernel

open VerifiableInference.Desc.First.Att.P (script slotsOf) in
/-- A control: with 16 bits for 17 the stages take another number. -/
theorem attentionOwnScalarsWrittenCanFail :
    slotsOf (script { H2K5.Row.ownW with bits := 16 }) ≠ 1072 := by
  decide +kernel

open VerifiableInference.Desc.First.Att.P (planIs_tiles planIs_public) in
/-- **IN SCOPE AN ATTENTION LINK SENDS: ITS LOOKUP ON THE CALLS, 1072 SCALARS, ITS LOOKUP ON THE
DIGITS.** -/
theorem attentionLinkScalarsInScope (scope : VerifierAndGoals.InScope Z = true)
    (read : VerifierAndGoals.readFiles Z = .ok pp) (publicRecord : Verify.publicOf Z.pol Z.KL lay = .ok X)
    {g : Nat} (groupBelow : g < 12) {a : Attention.Plan} (groupPlan : X.A[g]? = some a) :
    a.ns = Forest.elems a.fs + 1072 + Forest.elems a.seam.tl.f9 := by
  have tiles := planIs_tiles (planIs_public publicRecord) groupPlan
  rw [H2K5.Row.own_in_scope scope read publicRecord groupBelow groupPlan,
    attentionOwnScalarsWritten] at tiles
  exact tiles

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.layersOwnScalarsWritten
#print axioms ProofFile.Honest.K3.Term.layersOwnScalarsWrittenCanFail
#print axioms ProofFile.Honest.K3.Term.layersSlotsAtTheWrittenNumbers
#print axioms ProofFile.Honest.K3.Term.layersLinkScalarsInScope
#print axioms ProofFile.Honest.K3.Term.attentionOwnScalarsWritten
#print axioms ProofFile.Honest.K3.Term.attentionOwnScalarsWrittenCanFail
#print axioms ProofFile.Honest.K3.Term.attentionLinkScalarsInScope
