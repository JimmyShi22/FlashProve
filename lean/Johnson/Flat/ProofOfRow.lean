-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/ProofOfRow.lean: the proof file's named hypothesis on soundness (`CompilerSoundnessConditionStatements.proofSound`,
Johnson/Top/InnerCompiledVerifier.lean) at the three protocols of `filesOf` (Johnson/EntryRec/AtFiles.lean),
where the proof file's decision says yes only where three runs in a row say yes, one on each hash
chain's view. A SHEET OF STATEMENTS: definitions, and propositions written as `def … : Prop`.
NOTHING IS PROVED IN THIS FILE.

Why. The key file's hypothesis has a road from one law on its decision (`keySound_of_runMeets`,
Johnson/Flat/WholeRun.lean). The proof file's is in the form for batches and goes chain by chain:
`proofSound_top_links` (Johnson/TypedOracleCompiler/Joined/ProofLinksTop.lean) takes a list of three reductions over
the chains' written rounds. Here that list is a value of the library: the three chains of a file as
three stages in a row (`rowOf`, OnBytes/Maker/Row.lean), read as reductions (`Row.links`,
OnBytes/TypedOracleCompiler/Joined/OfLinks.lean), at three runs that are letters. They are meant to be the three
chains' own folds of a description: one text, with no second, typed text beside it: that is a plan,
no content of this file (Limits).

The letters. Those of `filesOf`; L₁, L₂: the trees left behind the first and the second chain; run₁,
run₂, run₃: the three runs, with the types X₁, X₂ of what they hand on; S: the relations,
conditions, extractors and lists of errors of which the three chains' clauses speak (`Row.Snd`); k₁,
k₂: the keys of what the first and the second chain hand on; toW: from the first relation's
witnesses to the configuration's.

Main names.
  `rowP`, `linksP`: the row and the list. The row's own tests on what the three silent rounds send
    say yes always: the file's verifier tests these itself.
  `RunGives`: where the file's decision says yes on three views, the three runs in a row do.
  `EarlyKept`: the first run reads an instance through what `early` keeps.
  `RowTies`: under the file's verifier's yes at (x, rec): if what the three extractors give is a
    witness of the first relation at (early x, rec), its image is a witness of the object's relation
    at x itself.
  `witP`: the witness map, by name.
  THE STATEMENTS: `WholeMono` · `RowDecides` · `KnowsJComap` · `BatIs` · `ProofSoundOfRowNamed` (the
    clause with the witness map and the errors by name: no "there is") · `ProofSoundOfRow`.

Every "there is", walked. `CompilerSoundnessConditionStatements.proofSound` begins "there are a witness map and a list of
errors": in `ProofSoundOfRowNamed` they are `witP` and `(linksP …).err`. The object's relation has
"there is an index i with D y rec = some i": i is that value. `RunGives`, `EarlyKept`, `RowDecides`
have none. `Links.KnowsJ` is a structure of five fields, read as it lies: each of its three links
holds one "there are sets of bad values" (`KnowJ`, CompileK/Joined/ExtractKnow.lean): on the
premise's side: whoever shows `knows` names them.

Limits. NO VALUE OF THIS FRAME HAS RUN ON A REAL PROOF: run₁, run₂, run₃, the data DP and the lists
L₁, L₂ are letters, and no description is laid in. THAT A DESCRIPTION's DECISION MEETS `RunGives`
AND `EarlyKept` AT ITS OWN THREE FOLDS IS NOT STATED HERE: Johnson/Flat/ProofOfDescRuns.lean.
Nothing on acceptance: a decision that never says yes meets `RunGives` and `RowTies`, and the
conclusion then holds for nothing. `knows` is a premise: that any chain's fold has its clause is
another sheet's matter. ALL OF THE MEANING SITS IN `RowTies`: S.R₀ is a letter, and at a relation
that holds of everything `knows` is free and `RowTies` asks the object's relation outright. Where
the configuration lays no cells a witness has the type Unit, and the witness map says nothing. What
`early` drops of an instance stands in no run: it is reached through `RowTies` alone. Only late =
none. The second chain's errors are taken as S has them: what must be counted once for each slot has
to stand in that list. The keys are letters: at the trivial keys their laws are free, AND THE PRICE
IS IN THAT LIST: the shared chain's clause then comes by `LinkJ.ofShared`
(OnBytes/TypedOracleCompiler/Joined/LinkJ.lean), each of its rounds' errors taken N times: so the second bound asks
of each shared round's own error, as a share, at most U.εs / N. ON THAT ROAD THE THEOREM AT THE FULL
SIZE IS EXPECTED TRUE AND EMPTY AT 2^-128 WITH 64 SLOTS (a reading of this file;
the heads of CompileK/Joined/ExtractKnow.lean and Johnson/Flat/TwoSizes.lean: the fold's term at the
shared point fills that bound to within about a bit; a union bound over the slots cannot reach it).
The goals' chain of numbers asks U.εs ≤ (5/4) · 2^-73 alone (Johnson/Flat/CountAtFrame.lean): at
such a bound, with 64 slots, each shared round's own error has to be at most some 2^-79 (arithmetic
on the statements: 2^-73 / 64 = 2^-79; no round is evaluated): not expected empty; BUT NO LEVEL OF
128 BITS FOLLOWS: that wants the road that pays once. THE ROAD THAT PAYS ONCE: keys that bind what
the slots share: `FileKnowsJOfGood` (Johnson/Desc/Sound/FileBatch.lean, the rule of composition's)
ends in `KnowsJ` at the key "the shared chain's own first record with the stored table", at the
shared chain's blocks' errors with no factor; its premises are met by no block of the protocol yet.
UNLIKE `keySound` AND `entrySound` THE HYPOTHESIS DOES NOT SHOW THE FACTOR: it hides in S.ε₂.
`knows` IS ASKED OF A ROW WITHOUT THE FILE's TEST ON THE SILENT ROUNDS: so also at transcripts whose
silent rounds carry another record's answers. The three runs read no silent round's message
(`rowOf_out_eq`, OnBytes/Maker/RowWhole.lean: these messages stand in the row's three tests alone),
and the record enters by the instance; `FileKnows` (Johnson/Desc/Sound/FileRule.lean) is general in
the row's three tests. Nothing says that U.εs is small, or below a round's share of proof of work:
`knows` and the three bounds are met by "bad: every challenge that passes the work" as soon as U.εs
is at least the least round's share of work: SO "PAID" MEANS SOMETHING ONLY WITH U.εs STATED BELOW
THAT. At instances that are a subtype (the requests) `knows` at `firstRel` has a second arm to meet:
Johnson/Flat/TiesAtReq.lean. `KnowsJComap` is a tool for the caller: the two main statements take
`knows` already read record by record.
Terms: lean/GLOSSARY.md.

-/
import Johnson.TypedOracleCompiler.Joined.ProofLinksTop
import Johnson.EntryRec.AtFiles
import OnBytes.Maker.RowWhole
import OnBytes.Maker.WholeLaws
import OnBytes.TypedOracleCompiler.Joined.OfLinks

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal

namespace VerifiableInference.OnPublicFiles
open Hiop OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.RunA TypedOracleCompiler.Joined
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ
open _root_.Compile.Joined (Chains Desc)
open _root_.CompileK.Joined (Row)

/-! ## 1 Two statements that name no file -/

/-- The slot's tests in front of the decision do not read the instance, but for the test on what the
silent rounds send: so a yes at x under `run` is a yes at x' under `run'` and no such test, if run's
yes at x gives run''s at x' on all views. -/
def WholeMono : Prop :=
  ∀ (C : CK) (D : WholeD) (TF TJ T3 : Type) (tF : TF) (tJ : TJ) (t3 : T3) (Y : Type)
    (silent : Y → TF → TJ → T3 → Bool) (run run' : Y → PQ.View → PQ.View → PQ.View → Bool)
    (x x' : Y), (∀ v₁ v₂ v₃, run x v₁ v₂ v₃ = true → run' x' v₁ v₂ v₃ = true) →
    ∀ (y : (oneExternalString (2 ^ D.a) SgX).Str) (τ : Tr (chainsOf C D tF tJ t3).sh),
      (reductionOfWholeFile C D tF tJ t3 silent run).out x y τ = some () →
        (reductionOfWholeFile C D tF tJ t3 (fun _ _ _ _ => true) run').out x' y τ = some ()

/-- The list for the statements of a batch goes over to the description with the instance read
through a map. (For the plain list: `Links.Knows.comap`, OnBytes/TypedOracleCompiler/Joined/LandRec.lean.) -/
def KnowsJComap : Prop :=
  ∀ (G : Chains) (Y Y' : Type) (E : ExtSpec) (C : Links G (Y × E.Str)) (N : ℕ) (κ₁ κ₂ : Type)
    (k₁ : C.A₁ → κ₁) (k₂ : C.A₂ → κ₂) (f : Y' → Y),
    C.KnowsJ N k₁ k₂ → (C.comap f).KnowsJ N k₁ k₂

/-! ## 2 The row and the list -/

variable {a : ℕ} (Kc : ConfLetters a) (DK DP : WholeD)
  {TFk TJk T3k TFp TJp T3p : Type} (tFk : TFk) (tJk : TJk) (t3k : T3k) (tFp : TFp) (tJp : TJp)
  (t3p : T3p) (silK : Kc.conf.Rec → TFk → TJk → T3k → Bool)
  (runK : Kc.conf.Rec → PQ.View → PQ.View → PQ.View → Bool)
  (silP : Kc.conf.X × Kc.conf.Rec → TFp → TJp → T3p → Bool)
  (runP : Kc.conf.X × Kc.conf.Rec → PQ.View → PQ.View → PQ.View → Bool)
  (eL : LinkProtocolWithLeafCoding Kc.conf.Rec a) (N : ℕ) (early : Kc.conf.X → Kc.conf.X)
  (L₁ L₂ : List LeftT) {X₁ X₂ : Type}
  (run₁ : Kc.conf.X × Kc.conf.Rec → PQ.View → Option X₁) (run₂ : X₁ → PQ.View → Option X₂)
  (run₃ : X₂ → PQ.View → Bool)

/-- The proof file's three chains as three stages in a row, at the three runs. -/
abbrev rowP : Row (chainsOf (ckP .two) (DP.at a) tFp tJp t3p) (Kc.conf.X × Kc.conf.Rec)
    (oneExternalString (2 ^ (DP.at a).a) SgX) :=
  rowOf (ckP .two) (DP.at a) tFp tJp t3p L₁ L₂ (fun _ _ => true) (fun _ _ => true)
    (fun _ _ => true) run₁ run₂ run₃

variable (S : (rowP Kc DP tFp tJp t3p L₁ L₂ run₁ run₂ run₃).Snd)

/-- The three stages as the list of three reductions that the top takes. -/
abbrev linksP : Links (chainsOf (ckP .two) (DP.at a) tFp tJp t3p)
    ((Kc.conf.X × Kc.conf.Rec) × (oneExternalString (2 ^ (DP.at a).a) SgX).Str) :=
  (rowP Kc DP tFp tJp t3p L₁ L₂ run₁ run₂ run₃).links S

/-! ## 3 The premises on the decision -/

/-- Where the file's decision says yes on three views, the three runs in a row say yes. -/
def RunGives : Prop :=
  ∀ x v₁ v₂ v₃, runP x v₁ v₂ v₃ = true → runRow run₁ run₂ run₃ x v₁ v₂ v₃ = true

/-- The first run reads an instance through what `early` keeps. (The instance enters the three runs
at the first alone.) -/
def EarlyKept : Prop :=
  ∀ x rec v, run₁ (early x, rec) v = run₁ (x, rec) v

/-- The witness map: the three chains' extractors in a row, the last chain's first, at the early
part of the instance; then toW. -/
def witP (toW : S.W₀ → Kc.conf.Cells) (b : Kc.conf.X × Kc.conf.Rec)
    (y : (oneExternalString (2 ^ (DP.at a).a) SgX).Str)
    (τ : Tr (chainsOf (ckP .two) (DP.at a) tFp tJp t3p).sh) : Kc.conf.Cells :=
  toW ((linksP Kc DP tFp tJp t3p L₁ L₂ run₁ run₂ run₃ S).ext ((early b.1, b.2), y) τ ())

/-- Under the file's verifier's yes at (x, rec): if what the three extractors give is a witness of
the first relation at (early x, rec) (asked where the first condition holds there), then the word
does not decode with the record, or it decodes to an index at which the witness map's value meets
the relaxed relation AT x. -/
def RowTies (toW : S.W₀ → Kc.conf.Cells) : Prop :=
  ∀ x rec (y : (oneExternalString (2 ^ (DP.at a).a) SgX).Str)
    (τ : Tr (chainsOf (ckP .two) (DP.at a) tFp tJp t3p).sh),
    (reductionOfWholeFile (ckP .two) (DP.at a) tFp tJp t3p silP runP).out (x, rec) y τ = some () →
    (S.on₀ ((early x, rec), y) → S.R₀ ((early x, rec), y)
      ((linksP Kc DP tFp tJp t3p L₁ L₂ run₁ run₂ run₃ S).ext ((early x, rec), y) τ ())) →
    Kc.conf.D y rec = none ∨ ∃ i, Kc.conf.D y rec = some i ∧
      Kc.conf.Rno i x (witP Kc DP tFp tJp t3p early L₁ L₂ run₁ run₂ run₃ S toW (x, rec) y τ)

/-! ## 4 The statements -/

/-- **Where the file's verifier says yes at (x, rec), the three chains in a row put out at
(early x, rec).** From: the data and the two lists of trees fit (`RowFit`); `RunGives`; `EarlyKept`.
Meant by: `WholeMono`; `rowOf_of_whole` (OnBytes/Maker/RowWhole.lean); `Row.all_out`
(OnBytes/TypedOracleCompiler/Joined/OfLinks.lean). -/
def RowDecides : Prop :=
  RowFit (DP.at a) L₁ L₂ → RunGives Kc runP run₁ run₂ run₃ → EarlyKept Kc early run₁ →
  ∀ x rec (y : (oneExternalString (2 ^ (DP.at a).a) SgX).Str)
    (τ : Tr (chainsOf (ckP .two) (DP.at a) tFp tJp t3p).sh),
    (reductionOfWholeFile (ckP .two) (DP.at a) tFp tJp t3p silP runP).out (x, rec) y τ = some () →
      (linksP Kc DP tFp tJp t3p L₁ L₂ run₁ run₂ run₃ S).all.out ((early x, rec), y) τ = some ()

variable (P : (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL N early
    none).Provers)
  (T : InnerCompilerInputFieldsOverThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL N early
                                    none) P)
  (U : SoundnessAnalysisFieldsOverThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL N early
                                     none) P)

/-- The object's session is the batch protocol of the proof file's verifier. -/
def BatIs : Prop :=
  ((filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL N early none).withProvers P).onlineBatch =
    (wholeDesc (ckP .two) (DP.at a) tFp tJp t3p silP runP).batch

variable {κ₁ κ₂ : Type} (k₁ : X₁ × (rowP Kc DP tFp tJp t3p L₁ L₂ run₁ run₂ run₃).E₁.Str → κ₁)
  (k₂ : X₂ × (rowP Kc DP tFp tJp t3p L₁ L₂ run₁ run₂ run₃).E₂.Str → κ₂)

/-- **The clause, with the witness map and the errors by name.** Premises: fit · gives · kept ·
knows (the list for the statements of a batch, record by record) · ties · below (each chain's list
of errors, as shares, at most εs). Conclusion: the errors in a row are at most εs; and for each
record the session with that record in all slots is round-by-round knowledge sound in the form for
batches, at N slots, with `early`, nothing coming late, for the relaxed relation at the decoded
index, with the witness map `witP`, at these errors. -/
def ProofSoundOfRowNamed (toW : S.W₀ → Kc.conf.Cells) : Prop :=
  RowFit (DP.at a) L₁ L₂ → RunGives Kc runP run₁ run₂ run₃ → EarlyKept Kc early run₁ →
  (∀ rec, ((linksP Kc DP tFp tJp t3p L₁ L₂ run₁ run₂ run₃ S).comap
    fun x : Kc.conf.X => (x, rec)).KnowsJ N k₁ k₂) →
  RowTies Kc DP tFp tJp t3p silP runP early L₁ L₂ run₁ run₂ run₃ S toW →
  Err.Below S.ε₁ U.εs → Err.Below S.ε₂ U.εs → Err.Below S.ε₃ U.εs →
  Err.Below (linksP Kc DP tFp tJp t3p L₁ L₂ run₁ run₂ run₃ S).err U.εs ∧
    ∀ rec : Kc.conf.Rec,
      ((wholeDesc (ckP .two) (DP.at a) tFp tJp t3p silP runP).batch.comap
        fun x : Kc.conf.X => (x, rec)).SndBKT N early none
        (fun x y w => Kc.conf.D y rec = none ∨ ∃ i, Kc.conf.D y rec = some i ∧ Kc.conf.Rno i x w)
        (fun x y τ => witP Kc DP tFp tJp t3p early L₁ L₂ run₁ run₂ run₃ S toW (x, rec) y τ)
        (linksP Kc DP tFp tJp t3p L₁ L₂ run₁ run₂ run₃ S).err

/-- **The proof file's named hypothesis on soundness at the three protocols of `filesOf`**, nothing
coming late, from the same eight premises. Meant by: `RowDecides`; `BatIs`; `worst_le`
(Compile/Joined/Worst.lean); `proofSound_top_links` (Johnson/TypedOracleCompiler/Joined/ProofLinksTop.lean). -/
def ProofSoundOfRow (toW : S.W₀ → Kc.conf.Cells) : Prop :=
  RowFit (DP.at a) L₁ L₂ → RunGives Kc runP run₁ run₂ run₃ → EarlyKept Kc early run₁ →
  (∀ rec, ((linksP Kc DP tFp tJp t3p L₁ L₂ run₁ run₂ run₃ S).comap
    fun x : Kc.conf.X => (x, rec)).KnowsJ N k₁ k₂) →
  RowTies Kc DP tFp tJp t3p silP runP early L₁ L₂ run₁ run₂ run₃ S toW →
  Err.Below S.ε₁ U.εs → Err.Below S.ε₂ U.εs → Err.Below S.ε₃ U.εs →
  CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataOfThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP runP
                                                             eL N early none) P T U)

end VerifiableInference.OnPublicFiles

#check @VerifiableInference.OnPublicFiles.WholeMono
#check @VerifiableInference.OnPublicFiles.KnowsJComap
#check @VerifiableInference.OnPublicFiles.RowDecides
#check @VerifiableInference.OnPublicFiles.BatIs
#check @VerifiableInference.OnPublicFiles.ProofSoundOfRowNamed
#check @VerifiableInference.OnPublicFiles.ProofSoundOfRow
