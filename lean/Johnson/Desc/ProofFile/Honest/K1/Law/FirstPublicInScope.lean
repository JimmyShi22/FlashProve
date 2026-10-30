-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/FirstPublicInScope.lean: SEVEN OF THE EIGHTEEN PUBLIC PREMISES
OF tieRowsS_first (Johnson/Desc/ProofFile/Honest/K1/Law/TieRowsFirstS.lean), PAID IN THE GOALS'
SCOPE, AT THE DESCRIPTION's OWN GROUND, AT THE EARLIER HASH; ONE OF THEM (hquiet) AT EVERY GROUND,
OFF THREE OTHERS. Two statements and their proofs. No definition. Public data alone: no thread, no
run, no witness.

  quiet_layers_of_kind    AT EVERY GROUND: at a link of the layers' sort whose group has a plan hp,
                          the quiet block behind the reads' sending is the layers' own, at hp's
                          record: IM.k1Quiet G l X = layers ⟨⟨1, some l, 4, .K1⟩, hp.tl⟩. The sister
                          of the library's quiet_of_kind
                          (Johnson/Desc/K1/Law/OwnHeldAtSendings.lean), which has the head's sort.
                          IT PAYS hquiet OFF hY, hk, hG, WHERE THE BLOCK's LINK DATA ARE THE
                          GROUND's OWN AT THAT LINK
  first_public_in_scope   in the goals' scope (hS, hR), where the public part Z is made at the
                          earlier hash (hZ) and the description's blank ground G₀ of it (hG): link 0
                          has built data Y of sort 0 and group 0; group 0 has a plan hp₀; the plan's
                          marks and numbers of parts hold of G₀.W; the codes' lengths pass at
                          G₀.first; the quiet block at link 0 is the layers' at hp₀'s record: hY ·
                          hk · hG · hMarks · hParts · hlen · hquiet; and Y.g = 0

BY CALLS, ALL OF THE LIBRARY's: IM.ground_named, IM.ground_publicK, IM.blank_ground
(Johnson/IMR/PureJoin.lean) · Meaning.scope_plans24 (Johnson/Goal/Meaning/PlanNames.lean) ·
planMarks_in_scope, partsFit_in_scope (Johnson/Goal/HonestTrace/) · lengthsOk_of_pub
(Johnson/Goal/Numbers/LengthsOkWritten.lean).

Limits. THE SCOPE IS A HYPOTHESIS. THE GROUND IS THE DESCRIPTION's BLANK ONE: that it is the ground
of the prover that a filling makes is another file's. ELEVEN OF THE EIGHTEEN ARE NOT HERE: hb · hn ·
hown · hne · hmom · hap · hs · hsa · ok · hsg · h3. Nothing on soundness, on completeness or on any
other property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.IMR.PureJoin
import Johnson.IMR.K1Seat
import Johnson.Desc.K8.ReadsQuietAt
import Johnson.Goal.HonestTrace.PlanMarksInScope
import Johnson.Goal.HonestTrace.FromCellsInScope
import Johnson.Goal.Numbers.LengthsOkWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes VerifiableInference.Desc
open OnBytes.Model.Layer (HPlan2)
open OnBytes.Model.Stages (LinkH)
open OnBytes.HonestTrace (PlanMarks PartsFit planMarks_in_scope partsFit_in_scope)
open VerifiableInference.Desc.K8 (ReadsQuiet.blockAt)
open VerifiableInference.Desc.K8.ReadsQuiet (layers)

/-- **The quiet step behind a layers' segment's reads.** -/
theorem quiet_layers_of_kind (G : ProofFile.Ground) (l : ℕ) (X : LinkH) (hX : G.built[l]? = some X)
    (hk : X.kind = 0) {hp : HPlan2} (hG : G.W.G[X.g]? = some hp) :
    IM.k1Quiet G l X = layers ⟨⟨1, some l, 4, .K1⟩, hp.tl⟩ := by
  have hL : (G.built.toList.map fun Y => (Y.kind, Y.g))[l]? = some (X.kind, X.g) := by
    rw [List.getElem?_map, Array.getElem?_toList, hX]
    rfl
  unfold IM.k1Quiet ProofFile.readsQuietAt ReadsQuiet.blockAt
  simp [hk, hL, hG, ProofFile.orLoud]

/-- **Seven public premises at link 0, in the goals' scope.** -/
theorem first_public_in_scope {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {Z : ProofFile.Pub} {G₀ : ProofFile.Ground} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀) :
    ∃ (Y : LinkH) (hp₀ : HPlan2), G₀.built[0]? = some Y ∧ Y.kind = 0 ∧ Y.g = 0 ∧
      G₀.W.G[Y.g]? = some hp₀ ∧ PlanMarks G₀.W ∧ PartsFit G₀.W ∧
      G₀.first.codes.lengthsOk = true ∧
      IM.k1Quiet G₀ 0 Y = layers ⟨⟨1, some 0, 4, .K1⟩, hp₀.tl⟩ := by
  have hX := IM.ground_publicK hZ hG
  obtain ⟨Y, -, hY, hk, hg, -, -, -, -, -⟩ := (IM.ground_named hS hR hZ hG).1 0 (by decide)
  obtain ⟨⟨hp₀, hp⟩, -⟩ := Meaning.scope_plans24 hS hR hX 0 (by decide)
  obtain ⟨-, -, -, -, eF⟩ := IM.blank_ground hG
  have hG' : G₀.W.G[Y.g]? = some hp₀ := by rw [hg]; exact hp
  refine ⟨Y, hp₀, hY, hk, hg, hG', planMarks_in_scope hS hR hX, partsFit_in_scope hS hR hX, ?_,
    quiet_layers_of_kind G₀ 0 Y hY hk hG'⟩
  rw [eF]
  exact VerifiableInference.Desc.K13.Law.lengthsOk_of_pub hZ

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.quiet_layers_of_kind
#print axioms ProofFile.Honest.K1.first_public_in_scope
