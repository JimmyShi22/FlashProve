-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Goal/Conditions/KeyOpenHolds.lean: at the closed term VerifierAndGoals.theDescription, WITH THE KEY
FILE's SEAT LAID: THE THREE LAWS OF THE PROXIMITY TESTS BEHIND THE FIRST CHAIN (rows 2.9, 2.10, 3.2)
ARE PROVED AT THE SEAT: KeyOpenAt Z holds at every Z in scope where protocolDataWellFormed says yes; KeyOpen holds;
SO THE ROW KeySound STANDS WITH NO LAW UNPROVED. Calls alone.


Main names.
  keyOpenAt_holds: InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true → KeyOpenAt Z: each field by
    a call (LPFD.r2_9_at_name, r2_10_at_name, r3_2_at_name,
    Johnson/Top/Fire/Code/RowsK12AtName.lean) at the written terms of KeyAtTheSeatWritten.lean:
    their fourteen binders are met by what the seat gives (OpenLawAtZ's own hypotheses),
    by scope, and by pin_at_seat.
  keyOpen_holds: KeyOpen.
  keySound_holds: KeySound: NO PREMISE.
  keySound_at_holds: InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true → the row KeySound's own body at
    Z, written out.
  keySound_at_live_holds: InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true → that body: with InScope
    alone in front: the form of the hypothesis on the key file in the top at one Z (TopAtZ.lean).
Object: KeySound. User: the top's hypothesis on the key file falls. Letters: none.

Limits. A theorem may be true and empty. KeySound asks something only at a Z in scope where protocolDataWellFormed
says yes: a theorem at the written copies (AtFullSide/Top/); as bytes evaluated, not proved.
Each of the 21 laws beneath is guarded by its border's whole promise and speaks only where its piece
says yes. For each of the 21 laws one example is known: a statement in its border's promise at which
the law's own piece accepts. The examples were evaluated by Lean's interpreter, not proved: Lean's
kernel has checked none of them. The files that ran these evaluations are not in this repository, so
a reader cannot run them again from it. The stored key file that they read is
examples/full-size/ivk/key.bin, with the public files under examples/full-size/config/. All use one
stored honest key file of the full size, made from synthetic weights. Their oracles and transcripts
were constructed for the evaluation; they do not come from a run of the prover. The 21 were not all
evaluated over the same Lean files. Row 3.0's sub-protocol declares no round, so there
"the piece accepts" says only that the step's decision accepts. The examples show that each law
applies to at least one statement, and nothing more: not why the proximity tests' errors lie below
the bound that is written into the laws. The 21 laws are theorems of other files of this library.
What KeySound says is CompilerSoundnessConditionStatements.keySound
of the named system: one of three rows beneath the top on soundness; it is not that top. Nothing on
soundness of the release is claimed here.
The statement on codes. The bounds in the laws beneath rest on this library's proof of the statement
on codes (a bound on the mutual correlated agreement of Reed-Solomon codes below the Johnson radius;
lean/LIMITS.md, L15), at these places at least: the count of bad fold points at the round "LIN
point" (row 2.1), through Cb.Bridge.foldErr_ix (Johnson/Bridge/FoldErrIx.lean), and the proximity
tests, the first chain's (row 1.15) and the three behind it (rows 2.9, 2.10, 3.2), through
Cb.Gl.bchks46At (Cb/Bridge/GlCodesProved.lean). That proof rests on files under ThirdParty/
adapted from ArkLib and Mathlib (L15).
None of this appears as a hypothesis in this file's statements.

-/
import Johnson.Goal.Conditions.KeySoundOfOpenAt
import Johnson.Top.Fire.Code.RowsK12AtName

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped ENNReal

namespace VerifierAndGoals.AtTheName
open VerifierAndGoals VerifierAndGoals.Fit FlashProve FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker
open _root_.Run
open VerifiableInference.Desc

/-- **THE THREE LAWS AT ONE Z: PROVED.** -/
theorem keyOpenAt_holds (Z : PublicFiles) (hs : InScope Z = true) (hl : protocolDataWellFormed (asDescriptionFiles Z) = true) :
    KeyOpenAt Z where
  r2_9 := fun _ _ X N P e₁ e₂ e₃ e₄ e₅ hD hp hw _ ha _ c₁ k₁ c₂ k₂ c₃ k₃ _ _ _ q₁ q₂ q₃ _ _ _ =>
    LPFD.r2_9_at_name X N P (dataAtFiles flashProveData Z).DK c₁ k₁ c₂ k₂ c₃ k₃ (LPFD.encN X P) LPFD.radN q₁ q₂
      q₃ hs (Johnson.RunOne.Law.ReadAtO.readOf_publicOfO e₁) e₂ e₃ e₅ e₄ hp hw hD
      (pin_at_seat Z hs hl) ha
  r2_10 := fun _ _ X N P e₁ e₂ e₃ e₄ e₅ hD hp hw _ ha _ c₁ k₁ c₂ k₂ c₃ k₃ _ _ _ q₁ q₂ q₃ _ _ _ =>
    LPFD.r2_10_at_name X N P (dataAtFiles flashProveData Z).DK c₁ k₁ c₂ k₂ c₃ k₃ (LPFD.encN X P) LPFD.radN q₁ q₂
      q₃ hs (Johnson.RunOne.Law.ReadAtO.readOf_publicOfO e₁) e₂ e₃ e₅ e₄ hp hw hD
      (pin_at_seat Z hs hl) ha
  r3_2 := fun _ _ X N P e₁ e₂ e₃ e₄ e₅ hD hp hw _ ha _ c₁ k₁ c₂ k₂ c₃ k₃ _ _ _ q₁ q₂ q₃ _ _ _ =>
    LPFD.r3_2_at_name X N P (dataAtFiles flashProveData Z).DK c₁ k₁ c₂ k₂ c₃ k₃ q₁ q₂ q₃
      hs (Johnson.RunOne.Law.ReadAtO.readOf_publicOfO e₁) e₂ e₃ e₅ e₄ hp hw hD (pin_at_seat Z hs hl)
      ha

/-- **KeyOpen HOLDS.** -/
theorem keyOpen_holds : KeyOpen := keyOpen_iff_at.2 keyOpenAt_holds

/-- **THE ROW KeySound, WITH NO LAW UNPROVED AND NO PREMISE.** -/
theorem keySound_holds : KeySound := keySound_of_open keyOpen_holds

/-- **The row's own body at one Z.** -/
theorem keySound_at_holds (Z : PublicFiles) (hs : InScope Z = true) (hl : protocolDataWellFormed (asDescriptionFiles Z) = true) :
    CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings theC0 theM0)) :=
  keySound_at Z hs hl (keyOpenAt_holds Z hs hl)

/-- **The same with InScope alone in front.** -/
theorem keySound_at_live_holds (Z : PublicFiles) (hs : InScope Z = true) :
    protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings theC0 theM0)) :=
  fun hl => keySound_at_holds Z hs hl

end VerifierAndGoals.AtTheName

#print axioms VerifierAndGoals.AtTheName.keyOpenAt_holds
#print axioms VerifierAndGoals.AtTheName.keyOpen_holds
#print axioms VerifierAndGoals.AtTheName.keySound_holds
#print axioms VerifierAndGoals.AtTheName.keySound_at_holds
#print axioms VerifierAndGoals.AtTheName.keySound_at_live_holds
