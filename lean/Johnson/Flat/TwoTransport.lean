-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/TwoTransport.lean: the key file's and the entry file's named hypotheses on soundness
(Johnson/Top/InnerCompiledVerifier.lean), at an input made of three protocols, from the soundness of a typed
protocol: a transport in one direction.

Four theorems, general in `F : Files C`. The first two are `sound_carry` (OnBytes/Slice/Carry.lean)
at `F.key` and `F.entry`. What is asked: (s) a typed protocol Q' is round-by-round sound for a
language L', with the error counts ε; (l) a statement whose translation is in L' is in the file's
language; (a) WHAT THE FILE's VERIFIER ACCEPTS HAS AN IMAGE THAT THE TYPED VERIFIER ACCEPTS, along
maps of transcripts round by round (`Carry`); (b) at most w written verifier messages go to one
typed message (`Carry.Fib`); (c) the counts ε, each times its w (a shared round's counted once for
each leaf of the call's request tree), are at most εs as shares of the written rounds' verifier
messages.

`keySound_carryS`, `entrySound_carryS`: the same where Q' lacks rounds of the file's (the silent
rounds).

Limits: one direction. THE FOUR ARE TOOLS: ONE OF THEM, `keySound_carryS`, IS CALLED
(`keySound_of_runMeets`, Johnson/Flat/WholeRun.lean, which leaves its premises as premises); NOTHING
IN THIS LIBRARY CALLS THE OTHER THREE (`keySound_carry`, `entrySound_carry`, `entrySound_carryS`)
YET; and by themselves
they say nothing of the shipped verifier: a later file must supply their premises. In the first two
theorems Q' has as many rounds as the file's protocol. For the proof file the hypothesis is in the
form for batches: it goes chain by chain (OnBytes/Flat/CarrySkip.lean: `backS`, `backS_know`;
OnBytes/TypedOracleCompiler/Joined/MidLinks.lean: `proofSound_at_links`, which asks that nothing comes late); no
theorem here.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.InnerInputOfThreeProtocols
import OnBytes.Slice.Carry
import OnBytes.Flat.CarrySkip

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal

namespace VerifiableInference.OnPublicFiles
open Hiop OnBytes.Flat OnBytes.Slice
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {C : ConfigurationWithOutOfDomainSample} (F : Files C) (P : F.Provers) (T : InnerCompilerInputFieldsOverThreeProtocols F P) (U : SoundnessAnalysisFieldsOverThreeProtocols F P)

/-- The key file's hypothesis, from a typed protocol's soundness. -/
theorem keySound_carry {X' : Type} {E' : ExtSpec} (Q' : InteractiveOracleProof X' E')
    (M : C.Rec → C.E0.Str → Carry F.key.shape Q'.shape) (ws : Err F.key.shape)
    (fib : ∀ rec y, (M rec y).Fib ws) (fx : C.Rec → X') (fy : C.E0.Str → E'.Str)
    (L' : X' → E'.Str → Prop) (ε : Err Q'.shape) (sound : Q'.Sound L' ε)
    (lang : ∀ rec y, L' (fx rec) (fy y) → C.coll y rec.1 ∨ C.D y rec ≠ none)
    (yes : ∀ rec y τ, F.key.accept rec y τ = true →
      ∃ τ', (M rec y).tr τ = some τ' ∧ Q'.accept (fx rec) (fy y) τ' = true)
    (below : Err.Below (Err.timesShared (2 ^ T.W.depthReqT) F.annT
      (mulErr F.key.shape Q'.shape ws ε)) U.εs) :
    CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataOfThreeProtocols F P T U) :=
  ⟨_, below, sound_carry F.key Q' M ws fib fx fy _ L' ε lang yes sound⟩

/-- The entry file's hypothesis, from a typed protocol's soundness. -/
theorem entrySound_carry {X' : Type} {E' : ExtSpec} (Q' : InteractiveOracleProof X' E')
    (M : C.Rec × C.Rec → (twoExternalStrings C.n C.Sg).Str → Carry F.entry.shape Q'.shape)
    (ws : Err F.entry.shape) (fib : ∀ rr y, (M rr y).Fib ws) (fx : C.Rec × C.Rec → X')
    (fy : (twoExternalStrings C.n C.Sg).Str → E'.Str) (L' : X' → E'.Str → Prop) (ε : Err Q'.shape)
    (sound : Q'.Sound L' ε)
    (lang : ∀ rr y, L' (fx rr) (fy y) →
      C.D y.1 rr.1 = none ∨ C.coll y.2 rr.2.1 ∨ C.D y.2 rr.2 = C.D y.1 rr.1)
    (yes : ∀ rr y τ, F.entry.accept rr y τ = true →
      ∃ τ', (M rr y).tr τ = some τ' ∧ Q'.accept (fx rr) (fy y) τ' = true)
    (below : Err.Below (Err.timesShared (2 ^ T.W.depthReqL) F.annL
      (mulErr F.entry.shape Q'.shape ws ε)) U.εs) :
    CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataOfThreeProtocols F P T U) :=
  ⟨_, below, sound_carry F.entry Q' M ws fib fx fy _ L' ε lang yes sound⟩

/-- The key file's hypothesis, from the soundness of a typed protocol that may lack rounds of the
file's (`CarryS`, OnBytes/Flat/CarrySkip.lean). ε': the error counts of the file's own rounds. -/
theorem keySound_carryS {X' : Type} {E' : ExtSpec} (Q' : InteractiveOracleProof X' E')
    (M : C.Rec → C.E0.Str → CarryS F.key.shape Q'.shape) (ε : Err Q'.shape)
    (ε' : Err F.key.shape) (fits : ∀ rec y, (M rec y).Fits ε ε') (fx : C.Rec → X')
    (fy : C.E0.Str → E'.Str) (L' : X' → E'.Str → Prop) (sound : Q'.Sound L' ε)
    (lang : ∀ rec y, L' (fx rec) (fy y) → C.coll y rec.1 ∨ C.D y rec ≠ none)
    (yes : ∀ rec y τ, F.key.accept rec y τ = true →
      ∃ τ', (M rec y).tr τ = some τ' ∧ Q'.accept (fx rec) (fy y) τ' = true)
    (below : Err.Below (Err.timesShared (2 ^ T.W.depthReqT) F.annT ε') U.εs) :
    CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataOfThreeProtocols F P T U) :=
  ⟨ε', below, sound_carryS F.key Q' M ε ε' fits fx fy _ L' lang yes sound⟩

/-- The entry file's hypothesis, the like. -/
theorem entrySound_carryS {X' : Type} {E' : ExtSpec} (Q' : InteractiveOracleProof X' E')
    (M : C.Rec × C.Rec → (twoExternalStrings C.n C.Sg).Str → CarryS F.entry.shape Q'.shape)
    (ε : Err Q'.shape) (ε' : Err F.entry.shape) (fits : ∀ rr y, (M rr y).Fits ε ε')
    (fx : C.Rec × C.Rec → X') (fy : (twoExternalStrings C.n C.Sg).Str → E'.Str) (L' : X' → E'.Str → Prop)
    (sound : Q'.Sound L' ε)
    (lang : ∀ rr y, L' (fx rr) (fy y) →
      C.D y.1 rr.1 = none ∨ C.coll y.2 rr.2.1 ∨ C.D y.2 rr.2 = C.D y.1 rr.1)
    (yes : ∀ rr y τ, F.entry.accept rr y τ = true →
      ∃ τ', (M rr y).tr τ = some τ' ∧ Q'.accept (fx rr) (fy y) τ' = true)
    (below : Err.Below (Err.timesShared (2 ^ T.W.depthReqL) F.annL ε') U.εs) :
    CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataOfThreeProtocols F P T U) :=
  ⟨ε', below, sound_carryS F.entry Q' M ε ε' fits fx fy _ L' lang yes sound⟩

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.keySound_carryS
#print axioms VerifiableInference.OnPublicFiles.keySound_carry
#print axioms VerifiableInference.OnPublicFiles.entrySound_carry
