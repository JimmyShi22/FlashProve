-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/WholeRun.lean: a whole file as data (`reductionOfWholeFile`, OnBytes/Maker/Whole.lean) is
round-by-round sound, if a typed protocol is, one law joins the file's decision to the typed one,
and the maps between their rounds and the translation of their languages are as asked; and the key
file's named hypothesis on soundness (`CompilerSoundnessConditionStatements.keySound`, Johnson/Top/InnerCompiledVerifier.lean) at the three
protocols of `filesOf` (Johnson/EntryRec/AtFiles.lean), from that law and eight premises more.

Why. A file as data has its written rounds' data D and a decision `run` on the three chains' views.
Soundness is proved of a typed protocol (in the uses: over field elements), which is never run: the
text of which soundness is proved; the law below joins it to the file's decision.
Johnson/Flat/CarrySWhole.lean reads the written rounds as typed rounds (`wholeMap`, `wholeView`) and
pays all that such a reading asks "but for the typed verifier's yes". That yes is named here as one
law, and spent.

Definitions, statements and proofs.
  `RunMeets`: THE LAW: where the file's verifier says yes at a written transcript τ, the typed
    decision acc' says yes at the image `wholeView D tF tJ t3 M₁ M₂ M₃ τ`.
  `wholeRun_yes`: what the file's verifier accepts has an image along `wholeMap` that the typed
    verifier accepts: the image by `tr_whole_of_out`, the yes by the law.
  `wholeRun_sound`: the file's protocol is round-by-round sound at the written counts `wholeErr`,
    from the law, `Maps.OK` of the three lists of maps, the translation of the languages and the
    typed protocol's soundness. By `sound_carryS` (OnBytes/Flat/CarrySkip.lean) and `fits_whole`.
  `keySound_of_runMeets`: `CompilerSoundnessConditionStatements.keySound` at `filesOf Kc .two DK DP …`, general in all its
    letters. By `keySound_carryS` (Johnson/Flat/TwoTransport.lean) and `below_file_shared`
    (OnBytes/Flat/CarrySFileN.lean). The first and the last chain's counts are bounded by
    `Maps.Held`, with the work counted. The bound on the shared chain's counts, each taken once for
    each leaf of the call's request tree, is a premise.
  `runMeets_top`: at a typed decision that accepts all, every run meets the law. `runMeets_bot`: a
    run that never says yes meets it at every typed decision.
A control, with every premise paid at a round that has proof of work: Johnson/Flat/WholeRunToy.lean.

What kind of law it is. A law between TWO TEXTS, run and acc': the premise "yes" of
`keySound_carryS`, with the image named. It stands UNDER the file's verifier's own yes, which holds
the three chains' tests of work, at every D (the yes is spelled out in `wholeIOR_out_eq`,
OnBytes/Maker/RowWhole.lean): a chain's view does not show a round's bits of
work, so a law that asked an image wherever the views fit could be met only by a run that never says
yes. It is meant to be proved block by block: run a composition of tests on views, each with one law
to its block's typed test at the block's stretch of the image. Each such law must give the block's
output, which is the next block's statement, not only that the typed test passes: else the laws do
not chain. That is a plan, no content of this file: HERE acc' IS ANY DECISION WHOSE PROTOCOL IS
SOUND; that it is a composition of the library's proved blocks is said nowhere in this file. The
law's sibling on the road by links is the premise `decides` of `keySound_at`
(OnBytes/TypedOracleCompiler/Joined/TwoChains.lean).

Does not show: the law at any run of a file of the format. `runMeets_top` shows only that the law
alone forces no run to say no. At its typed decision the other premises hold in two degenerate cases
alone (an argument; no theorem). Either L' holds everywhere: then by `lang` every word collides or
decodes. Or some typed round's count is all its verifier's messages: then εs is at least that
round's 2^-work. SO THE SECOND CASE IS SHUT ONLY WHERE εs IS BELOW EVERY ROUND's 2^-work (on the
shared chain: times 2 ^ depthReqT); where it is not, the theorem can be had from the proof of work
alone. εs and the rounds' work are letters here: the comparison is owed with the data. A run that
never says yes meets the law at every acc' (`runMeets_bot`): true and useless; only a run on honest
files tells. THE COUNT OF THE SHARED CHAIN IS THE COARSE ONE: every shared round pays 2 ^ depthReqT.
It costs nothing at depth 0 (Johnson/Flat/KeySoundDepth.lean [not in this library] says where the
depth is 0); where the depth is large and the shared chain's counts are near εs, `below₂` cannot be
met, and the finer rule is wanted (OnBytes/Flat/CarrySFileN.lean's own limit). No maps are made
here, at any data. A written round that the maps skip is in no image: what a run tests there is
mirrored by no typed test. Not shown: that `Maps` are wide enough: each map is blind to the rounds
before and to the statement (Johnson/Flat/CarrySWhole.lean's own limit). That the typed protocol is
sound, or asks enough. That the file's verifier accepts anything. The typed protocol is given by its
fields over s₁' ++ (s₂' ++ s₃'), so that no equation of shapes is carried; of these bl', er', rd'
are read by nothing here.
Nothing on the proof file's hypothesis, which is in the form for batches; the law itself can be
stated there too. Nothing on an honest prover or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.CarrySWhole
import Johnson.Flat.TwoTransport
import Johnson.EntryRec.AtFiles
import OnBytes.Flat.CarrySFileN
import OnBytes.Maker.WholeLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

namespace OnBytes.Flat
open Iop Prob _root_.Run _root_.Run.PQ OnBytes.Maker OnBytes.Slice

section
variable (D : WholeD) {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3) {s₁' s₂' s₃' : Shape}
  (M₁ : Maps D.ds₁ s₁') (M₂ : Maps D.ds₂ s₂') (M₃ : Maps D.ds₃ s₃')
  {Xi X' : Type} {E' : ExtSpec} (silent : Xi → TF → TJ → T3 → Bool)
  (run : Xi → View → View → View → Bool) (fx : Xi → X')
  (fy : (oneExternalString (2 ^ D.a) SgX).Str → E'.Str)
  (acc' : X' → E'.Str → Tr (s₁' ++ (s₂' ++ s₃')) → Bool)

/-- **The law**: where the file's verifier says yes, the typed decision says yes at the image. -/
def RunMeets : Prop :=
  ∀ (x : Xi) (y : (oneExternalString (2 ^ D.a) SgX).Str) (τ : Tr (chainsOf (ckP .two) D tF tJ t3).sh),
    (reductionOfWholeFile (ckP .two) D tF tJ t3 silent run).out x y τ = some () →
      acc' (fx x) (fy y) (wholeView D tF tJ t3 M₁ M₂ M₃ τ) = true

/-- Under the law (`meets`): what the file's verifier accepts (`h`) has an image that the typed
verifier accepts. -/
theorem wholeRun_yes (meets : RunMeets D tF tJ t3 M₁ M₂ M₃ silent run fx fy acc') (x : Xi)
    (y : (oneExternalString (2 ^ D.a) SgX).Str) (τ : Tr (chainsOf (ckP .two) D tF tJ t3).sh)
    (h : (reductionOfWholeFile (ckP .two) D tF tJ t3 silent run).toInteractiveOracleProof.accept x y τ = true) :
    ∃ τ', (wholeMap D tF tJ t3 M₁ M₂ M₃).tr τ = some τ' ∧ acc' (fx x) (fy y) τ' = true := by
  have h' : ((reductionOfWholeFile (ckP .two) D tF tJ t3 silent run).out x y τ).isSome = true := h
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 h'
  cases u
  exact ⟨_, tr_whole_of_out D tF tJ t3 M₁ M₂ M₃ silent run x y τ hu, meets x y τ hu⟩

/-- **The file's protocol is sound round by round**, from six premises: the law (`meets`); `Maps.OK`
of the three lists of maps (`ok₁`, `ok₂`, `ok₃`); the translation of the languages (`lang`); the
typed protocol's soundness (`sound`). A typed protocol whose shape unfolds to s₁' ++ (s₂' ++ s₃') is
handed in by its fields. -/
theorem wholeRun_sound (meets : RunMeets D tF tJ t3 M₁ M₂ M₃ silent run fx fy acc')
    (bl' : OPos (s₁' ++ (s₂' ++ s₃')) → Bool)
    (er' : X' → Rho (s₁' ++ (s₂' ++ s₃')) → Finset E'.Pos)
    (rd' : X' → Rho (s₁' ++ (s₂' ++ s₃')) → Plains (s₁' ++ (s₂' ++ s₃')) →
      Finset (OPos (s₁' ++ (s₂' ++ s₃'))))
    (ok₁ : M₁.OK) (ok₂ : M₂.OK) (ok₃ : M₃.OK) (δ₁ : Err s₁') (δ₂ : Err s₂') (δ₃ : Err s₃')
    (L : Xi → (oneExternalString (2 ^ D.a) SgX).Str → Prop) (L' : X' → E'.Str → Prop)
    (lang : ∀ x y, L' (fx x) (fy y) → L x y)
    (sound : (⟨s₁' ++ (s₂' ++ s₃'), bl', er', rd', acc'⟩ : InteractiveOracleProof X' E').Sound L'
      (Err.app δ₁ (Err.app δ₂ δ₃))) :
    (reductionOfWholeFile (ckP .two) D tF tJ t3 silent run).toInteractiveOracleProof.Sound L
      (wholeErr D tF tJ t3 M₁ M₂ M₃ δ₁ δ₂ δ₃) :=
  sound_carryS (reductionOfWholeFile (ckP .two) D tF tJ t3 silent run).toInteractiveOracleProof
    (⟨s₁' ++ (s₂' ++ s₃'), bl', er', rd', acc'⟩ : InteractiveOracleProof X' E')
    (fun _ _ => wholeMap D tF tJ t3 M₁ M₂ M₃) (Err.app δ₁ (Err.app δ₂ δ₃))
    (wholeErr D tF tJ t3 M₁ M₂ M₃ δ₁ δ₂ δ₃)
    (fun _ _ => fits_whole D tF tJ t3 ok₁ ok₂ ok₃ δ₁ δ₂ δ₃)
    fx fy L L' lang (wholeRun_yes D tF tJ t3 M₁ M₂ M₃ silent run fx fy acc' meets) sound

/-- At a typed decision that accepts all, every run meets the law: the law alone forces no run to
say no. -/
theorem runMeets_top : RunMeets D tF tJ t3 M₁ M₂ M₃ silent run fx fy (fun _ _ _ => true) :=
  fun _ _ _ _ => rfl

/-- A run that never says yes meets the law at every typed decision: true and useless. -/
theorem runMeets_bot :
    RunMeets D tF tJ t3 M₁ M₂ M₃ silent (fun _ _ _ _ => false) fx fy acc' := by
  intro x y τ h
  have h2 := (Option.ite_none_right_eq_some.1 h).1
  simp only [Bool.and_false] at h2
  exact absurd h2 Bool.false_ne_true

end

end OnBytes.Flat

namespace VerifiableInference.OnPublicFiles
open Hiop OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.RunA
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ

variable {a : ℕ} (Kc : ConfLetters a) (DK DP : WholeD)
  {TFk TJk T3k TFp TJp T3p : Type} (tFk : TFk) (tJk : TJk) (t3k : T3k) (tFp : TFp) (tJp : TJp)
  (t3p : T3p) (silK : Kc.conf.Rec → TFk → TJk → T3k → Bool)
  (runK : Kc.conf.Rec → PQ.View → PQ.View → PQ.View → Bool)
  (silP : Kc.conf.X × Kc.conf.Rec → TFp → TJp → T3p → Bool)
  (runP : Kc.conf.X × Kc.conf.Rec → PQ.View → PQ.View → PQ.View → Bool)
  (eL : LinkProtocolWithLeafCoding Kc.conf.Rec a) (N : ℕ) (early : Kc.conf.X → Kc.conf.X) (late : Option ℕ)
  (P : (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL N early
    late).Provers)
  (T : InnerCompilerInputFieldsOverThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL N early
                                    late) P)
  (U : SoundnessAnalysisFieldsOverThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL N early
                                     late) P)

/-- **The key file's named hypothesis on soundness at the three protocols of `filesOf`**, from nine
premises: the law at the key file's data and decision (`meets`); `Maps.OK` of the three lists of
maps (`ok₁`, `ok₂`, `ok₃`); the translation of the languages (`lang`); a typed protocol's soundness
(`sound`); three bounds on counts at εs. `held₁`, `held₃`: the first and the last chain's typed
counts, with the sampler's bias and the rounds' work, are shares of at most εs. `below₂`: the shared
chain's written counts, each taken once for each leaf of the call's request tree, are shares of at
most εs. -/
theorem keySound_of_runMeets {s₁' s₂' s₃' : Shape} (M₁ : Maps (DK.at a).ds₁ s₁')
    (M₂ : Maps (DK.at a).ds₂ s₂') (M₃ : Maps (DK.at a).ds₃ s₃') {X' : Type} {E' : ExtSpec}
    (fx : Kc.conf.Rec → X') (fy : (oneExternalString (2 ^ (DK.at a).a) SgX).Str → E'.Str)
    (acc' : X' → E'.Str → Tr (s₁' ++ (s₂' ++ s₃')) → Bool)
    (meets : RunMeets (DK.at a) tFk tJk t3k M₁ M₂ M₃ silK runK fx fy acc')
    (bl' : OPos (s₁' ++ (s₂' ++ s₃')) → Bool)
    (er' : X' → Rho (s₁' ++ (s₂' ++ s₃')) → Finset E'.Pos)
    (rd' : X' → Rho (s₁' ++ (s₂' ++ s₃')) → Plains (s₁' ++ (s₂' ++ s₃')) →
      Finset (OPos (s₁' ++ (s₂' ++ s₃'))))
    (ok₁ : M₁.OK) (ok₂ : M₂.OK) (ok₃ : M₃.OK) (δ₁ : Err s₁') (δ₂ : Err s₂') (δ₃ : Err s₃')
    (L' : X' → E'.Str → Prop)
    (lang : ∀ rec y, L' (fx rec) (fy y) → Kc.conf.coll y rec.1 ∨ Kc.conf.D y rec ≠ none)
    (sound : (⟨s₁' ++ (s₂' ++ s₃'), bl', er', rd', acc'⟩ : InteractiveOracleProof X' E').Sound L'
      (Err.app δ₁ (Err.app δ₂ δ₃)))
    (held₁ : M₁.Held U.εs δ₁)
    (below₂ : Err.Below (Err.times (2 ^ T.W.depthReqT) (M₂.err δ₂)) U.εs)
    (held₃ : M₃.Held U.εs δ₃) :
    CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataOfThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP runP
                                                               eL N early late) P T U) :=
  keySound_carryS (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL N early
      late) P T U (⟨s₁' ++ (s₂' ++ s₃'), bl', er', rd', acc'⟩ : InteractiveOracleProof X' E')
    (fun _ _ => wholeMap (DK.at a) tFk tJk t3k M₁ M₂ M₃) (Err.app δ₁ (Err.app δ₂ δ₃))
    (wholeErr (DK.at a) tFk tJk t3k M₁ M₂ M₃ δ₁ δ₂ δ₃)
    (fun _ _ => fits_whole (DK.at a) tFk tJk t3k ok₁ ok₂ ok₃ δ₁ δ₂ δ₃) fx fy L' sound lang
    (wholeRun_yes (DK.at a) tFk tJk t3k M₁ M₂ M₃ silK runK fx fy acc' meets)
    (below_file_shared (chainsOf_laws (ckP .two) (DK.at a) tFk tJk t3k) (2 ^ T.W.depthReqT)
      (M₁.below_err ok₁ δ₁ held₁) below₂ (M₃.below_err ok₃ δ₃ held₃))

end VerifiableInference.OnPublicFiles

#print axioms OnBytes.Flat.wholeRun_sound
#print axioms VerifiableInference.OnPublicFiles.keySound_of_runMeets
