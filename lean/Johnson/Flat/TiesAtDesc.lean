-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/TiesAtDesc.lean: `TieFins` (Johnson/Flat/TiesSheet.lean) where the proof file's
decision is a description's (`FileDescription.run`, Johnson/Desc/Block.lean). A SHEET OF STATEMENTS:
definitions, and propositions written as `def … : Prop`. NOTHING IS PROVED IN THIS FILE (the proofs:
Johnson/Flat/TiesAtDescProofs.lean).

Why. `TieFins` says: under the file's verifier's yes the token that the transcript names is the
instance's own. TiesSheet.lean leaves "names" a letter (said). Here it is a named function: what the
reply's block of the description is shown of the first chain's written rounds, read by rd
(`FileDescription.Hears.said`, Johnson/Desc/Sound/FoldHeard.lean).

The letters, beside those of TiesSheet.lean. F: a description at the instances with their records.
rd: the token that the reply's block's rounds name. H: the record of data and laws `F.Hears`.

Main names.
  `saidP₁`: the token that a transcript of the first chain (with its silent round) names.
  `saidP`: the same of a transcript of the whole file: of its first chain's part.
  `EndsOfRun F`: where F's decision says yes, its first chain's fold has ended and its last test has
    said yes at that end. A reading of `FileDescription.runEnd`'s text.
  `TieFinsAtDesc`: `EndsOfRun F` gives `TieFins` at runP := F.run and said := `saidP`.

Every "there is", walked. `EndsOfRun` ends in "there are three ends": they are the values of
`FileDescription.runEnd`, which is a function: determined. `TieFinsAtDesc` has none.

Limits. Those of FoldHeard.lean: NO MEMBER OF `F.Hears` IS LAID AT A DESCRIPTION OF THE PROTOCOL (at
a toy: Johnson/Desc/Sound/HearsToy.lean [not in this library]). The
data DP are a letter: nothing here asks that they are made of F's declared rounds
(`FileDescription.data`, Johnson/Desc/BlockSlot.lean). Nothing on `TieReads`: that the extractors' yield
holds the same token is a law on the first chain's extractor (`FirstReads`), to be asked at said₁ :=
`saidP₁`. Nothing on acceptance, on an honest prover or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.TiesSheet
import Johnson.Desc.Sound.FoldHeard

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.OnPublicFiles
open Hiop OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.RunA TypedOracleCompiler.Joined
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ
open _root_.Compile.Joined (Chains Desc)
open _root_.CompileK.Joined (Row)

/-- Where a description's decision says yes: its first chain's fold, from the first state of the
instance's public part, on the first view with the sealing round put back, has ended; and its last
test has said yes at the instance and that end. -/
def EndsOfRun {Xi : Type} (F : VerifiableInference.Desc.FileDescription Xi) : Prop :=
  ∀ x v₁ v₂ v₃, F.run x v₁ v₂ v₃ = true → ∃ e₁ e₂ e₃,
    VerifiableInference.Desc.chainAt "the first chain" 0 F.first.blocksInOrder (F.start₁ (F.pub x))
      (VerifiableInference.Desc.withEmptySealRound v₁) = .ok e₁ ∧ F.fin x e₁ e₂ e₃ = true

variable {a : ℕ} (Kc : ConfLetters a) (DP : WholeD)
  {TFp TJp T3p : Type} (tFp : TFp) (tJp : TJp) (t3p : T3p)
  (silP : Kc.conf.X × Kc.conf.Rec → TFp → TJp → T3p → Bool)
  (F : VerifiableInference.Desc.FileDescription (Kc.conf.X × Kc.conf.Rec))
  {Tok : Type} (drop : Kc.conf.X → Tok) (rd : List Fmt.RoundView → Option Tok)
  (H : F.Hears (fun b => drop b.1) rd)

/-- The token that a transcript of the first chain names: what the reply's block is shown of the
chain's written rounds as a view has them, read by rd. The silent round in front is not read. -/
def saidP₁ (τ₁ : Tr (chainsOf (ckP .two) (DP.at a) tFp tJp t3p).c₁) : Option Tok :=
  H.said ⟨rvT (ckP .two) (DP.at a).ds₁ τ₁.2.2, []⟩

/-- The token that a transcript of the whole file names: its first chain's. -/
def saidP (τ : Tr (chainsOf (ckP .two) (DP.at a) tFp tJp t3p).sh) : Option Tok :=
  saidP₁ Kc DP tFp tJp t3p F drop rd H
    (Tr.fst (s := (chainsOf (ckP .two) (DP.at a) tFp tJp t3p).c₁) τ)

/-- **`TieFins` at a description that hears the reply.** -/
def TieFinsAtDesc : Prop :=
  EndsOfRun F →
    TieFins Kc DP tFp tJp t3p silP F.run drop (saidP Kc DP tFp tJp t3p F drop rd H)

end VerifiableInference.OnPublicFiles
