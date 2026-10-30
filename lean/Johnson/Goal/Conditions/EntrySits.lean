-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Conditions/EntrySits.lean: THE ENTRY FILE: THE TIES FROM THE LAW TO THE CONSTANT THAT THE SEAT CALLS: three ties and the row EntrySound at the record (Johnson/Goal/Conditions/RowsAtTheRecord.lean), IN ONE FILE, OVER A SET OF THIS PROJECT's LEAN FILES, WITH THE SEAT LAID (Johnson/Goal/Description/LinkDec.lean: linkDecisionAtFiles Zk := Desc.K15.linkDecisionAtParameterFile Zk.pol).
  entry_slot_is_the_links_text   AT EVERY Z: linkDecisionAtFiles (asDescriptionFiles Z) = Desc.K15.linkDecisionAtParameterFile Z.pol: BY DEFINITION.
  K15_sits        IN SCOPE: the seat's decision IS the constant of which the kind's law speaks: fun rr => decDescFullV frP (linkDeclaredRounds frP) (linkRoundsMatchPlan frP recordPlan) (recX rr): under the seat's one wrapper recX (by decWritten_inScope)
  K15_sits_keys   the same as the written description's run at the keys written of the two records (by decWritten_keys_scope)
  hole_entrySound AT EVERY Z, c₀, m₀: the compiler's hypothesis entrySound at the description: two calls: dec_the_at (GatesAtThe.lean) · entrySoundOfFullD_written_paid
  entrySound      the constant EntrySound (Johnson/Goal/Conditions/RowsAtTheRecord.lean)
WHAT THESE ARE NOT: EntrySound is met by any decision that never says yes: it is soundness alone; that linkDecisionAtParameterFile says yes at an honest entry file is EVALUATED (in runs outside this file); no theorem of this library shows it. LIMITS THAT TRAVEL: EntryAtWritten.lean's: the statement on codes is filled by Cb.Gl.bchks46At (lean/LIMITS.md, L15) · the bound counts work · an interactive protocol's round-by-round soundness, at the full size.
OBJECT: FlashProve.linkDecisionAtFiles · USER: the top's row EntrySound · LETTERS: none.
-/
import Johnson.Goal.Conditions.EntryWrittenPaid
import Johnson.Goal.Conditions.EntryWrittenLaw
import Johnson.Desc.Link.LinkWrittenKeys
import Johnson.Goal.Conditions.GatesAtThe
import Johnson.Goal.Conditions.RowsAtTheRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

noncomputable section
open scoped ENNReal

namespace FlashProve
open VerifierAndGoals VerifierAndGoals.Fit FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker
open _root_.Run
open OnBytes.Tie
open _root_.Iop (Dig)
open _root_.Desc.K15 (linkDecisionAtParameterFile decWritten_inScope decWritten_keys_scope frP linkDeclaredRounds linkRoundsMatchPlan linkDescriptionAt)

theorem entry_slot_is_the_links_text : ∀ Z : PublicFiles, linkDecisionAtFiles (asDescriptionFiles Z) = linkDecisionAtParameterFile Z.pol := fun _ => rfl

theorem K15_sits {Z : PublicFiles} (hZ : InScope Z = true) :
    linkDecisionAtFiles (asDescriptionFiles Z) = fun rr => _root_.Desc.K15.decDescFullV frP (linkDeclaredRounds frP) (linkRoundsMatchPlan frP OnBytes.Params.recordPlan) (recX rr) :=
  (entry_slot_is_the_links_text Z).trans (decWritten_inScope hZ)

theorem K15_sits_keys {Z : PublicFiles} (hZ : InScope Z = true) :
    linkDecisionAtFiles (asDescriptionFiles Z) = fun rr V => (linkDescriptionAt frP (linkDeclaredRounds frP) (linkRoundsMatchPlan frP OnBytes.Params.recordPlan)).run
      (keyOf (fun β : NZ => β.val) rr.1, { keyOf (fun β : NZ => β.val) rr.2 with item := 1 }) V :=
  (entry_slot_is_the_links_text Z).trans (decWritten_keys_scope hZ)

theorem hole_entrySound (c₀ : Digest) (m₀ : List (Dig 256)) :
    ∀ Z : PublicFiles, CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings c₀ m₀)) :=
  fun Z => entrySoundOfFullD_written_paid Z.pol (b := protocolDataWellFormed (asDescriptionFiles Z)) (dec_the_at Z _ (entry_slot_is_the_links_text Z))
    ((dataAtFiles flashProveData Z).inputFieldsAtReadings c₀ m₀)

theorem entrySound : VerifierAndGoals.AtTheName.EntrySound := fun Z _ _ => hole_entrySound theC0 theM0 Z

end FlashProve

#print axioms FlashProve.entry_slot_is_the_links_text
#print axioms FlashProve.K15_sits
#print axioms FlashProve.K15_sits_keys
#print axioms FlashProve.hole_entrySound
#print axioms FlashProve.entrySound
