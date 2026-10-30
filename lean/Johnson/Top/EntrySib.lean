-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/EntrySib.lean: the entry file's part of three files (`LinkProtocolWithLeafCodingAndQueryLayout`,
Johnson/EntryRec/AtMaker.lean) laid at the written link over letters (`linkProtocolOfRoundData`,
OnBytes/Flat/LinkSib.lean); and that the object and the wiring of the three files are then those at
which the entry's arm is said.

The three files' object, interface and wiring (`filesM`, `LM`, `wireM`) take the entry file's part
as a letter p. The entry's arm (Johnson/Top/ArmLinkK.lean, TieArmSibK.lean)
is said at an object `LrG T` whose Link is the written link over letters, and
at the wiring `wireOf2` with Link's wire record `wSib` and the bodies `bodiesSib`
(Johnson/EntryRec/OklaSib.lean). Here p is laid so that the two meet, by unfolding. For proofs only;
the program does not import this file.

Main names.
 `linkProtocolWithWireOfRoundData`     the entry's part: the written link over letters; every round marked local; a symbol
                as its leaf's own string of bits (`StringsList.embT`, `prjT`); K + 1 blocks;
                the wire record `sibW` (OnBytes/K/Arm/SameSib.lean).
 `restM`        what the three files' object holds beside its word length and alphabet, as a
                `RestR`: at any entry's part p.
 `objM_LrG`     the three files' object is `LrG (restM …)`.
 `wireM_sib`    at `linkProtocolWithWireOfRoundData` the wiring `wireM` is `wireOf2` with the key file's and the proof
                file's own wire records, `wSib`, and `bodiesSib` at the two files' own maps of
                bodies.
 `pbLM`         the correspondence `pbSib` (OnBytes/K/Arm/SibMaps.lean) of Link's plain parts, typed
                over `LM` at `linkProtocolWithWireOfRoundData`.

Not claimed. That `kM … ≤ K` at any K (`hK` is a premise). The laws of the entry's wire record
(`LinkWireOK`) and of its maps of bodies at `linkProtocolWithWireOfRoundData`. That the configuration's seeds and answers
are those of a ground of the entry's link: the statements on the entry's arm
(Johnson/Top/TieArmSibK.lean) are said at such a configuration alone. The
equation of the typed interface `LM` with the carrier over `LrG (restM …)` is not stated:
`wireM_sib` and `pbLM` are typed across it by unfolding. Nothing on soundness.

Terms: lean/GLOSSARY.md.


-/
import Johnson.Maker.Page.Type
import Johnson.EntryRec.OklaSib
import OnBytes.K.Arm.SameSib
import OnBytes.K.Arm.SibMaps

set_option autoImplicit false

noncomputable section

namespace OnBytes.K.Arm
open _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Slice
open TypedOracleCompiler.Compile.Batch.Cms OnBytes.Flat OnBytes.RunA OnBytes.Maker OnBytes.Maker.Page
open TypedOracleCompiler.Run.PQ (XD SOf)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run
open _root_.Run.PQ (View SgX CK XO)
open Hiop

attribute [local instance] ConfLetters.finRnd ConfLetters.neRnd ConfLetters.finPad
  ConfLetters.nePad ConfLetters.finSeed ConfLetters.neSeed

/-- The entry file's part at the written link over letters. -/
def linkProtocolWithWireOfRoundData {a : ℕ} (C : CK) (ds : List TypedOracleCompiler.Run.PQ.RD) (xs : List XO) {R : Type}
    (dec2 : R × R → View → Bool) (salt kmin K : ℕ) (hK : kmin ≤ K)
    (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) : LinkProtocolWithLeafCodingAndQueryLayout R a kmin where
  QL := linkProtocolOfRoundData C ds a xs dec2
  aL := _root_.Run.Twin.allLo (SOf C ds)
  embL := TypedOracleCompiler.StringsList.embT salt C ds
  prjL := TypedOracleCompiler.StringsList.prjT salt C ds
  K := K
  hK := hK
  wL := sibW C ds a xs K chal dec2

variable {a : ℕ} (Kc : ConfLetters a) (f : _root_.Fmt.Fld)
  {TFk TJk T3k TFp TJp T3p : Type} (tFk : TFk) (tJk : TJk) (t3k : T3k) (tFp : TFp) (tJp : TJp)
  (t3p : T3p) (silK : Kc.conf.Rec → TFk → TJk → T3k → Bool)
  (silP : Kc.conf.X × Kc.conf.Rec → TFp → TJp → T3p → Bool) (key : Kc.conf.Rec → TableKey)
  (k : Params.KeyChains) (rec₀ : Kc.conf.Rec) (c : Params.ProofChains)
  (block : Kc.conf.X → Blk Proof.FirstEnd) (z₀ : Kc.conf.X × Kc.conf.Rec)

section Any
variable (p : LinkProtocolWithLeafCodingAndQueryLayout Kc.conf.Rec a (kM Kc f key k rec₀ c block z₀)) (N : ℕ)
  (early : Kc.conf.X → Kc.conf.X) (late : Option ℕ)
  (P : (filesM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early late).Provers)

/-- What the three files' object holds beside its word length and its alphabet. -/
abbrev restM : RestR Kc.conf.I Kc.conf.X (Kc.conf.Pad × Kc.conf.Rnd) Kc.conf.Seed Kc.conf.Ans a
    p.QL :=
  (lettersOf Kc f (dataK Kc key k rec₀) (dataP Kc key c block z₀) tFk tJk t3k tFp tJp t3p silK
      (runKM Kc key k rec₀) silP (runPM Kc key c block z₀) p.toLinkProtocolWithLeafCoding N early late P).rest

/-- The three files' object is `LrG` of it. -/
theorem objM_LrG :
    (filesM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early late).withProvers P =
      LrG (restM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early late P) :=
  obj_objF Kc f (dataK Kc key k rec₀) (dataP Kc key c block z₀) tFk tJk t3k tFp tJp t3p silK
    (runKM Kc key k rec₀) silP (runPM Kc key c block z₀) p.toLinkProtocolWithLeafCoding N early late P

end Any

section Sib
variable (C : CK) (ds : List TypedOracleCompiler.Run.PQ.RD) (xs : List XO)
  (dec2 : Kc.conf.Rec × Kc.conf.Rec → View → Bool) (salt K : ℕ)
  (hK : kM Kc f key k rec₀ c block z₀ ≤ K) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (N : ℕ)
  (early : Kc.conf.X → Kc.conf.X) (late : Option ℕ)
  (P : (filesM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀
    (linkProtocolWithWireOfRoundData C ds xs dec2 salt (kM Kc f key k rec₀ c block z₀) K hK chal) N early late).Provers)

/-- The rest of the three files' object at the written link over letters. -/
abbrev restSibM : RestR Kc.conf.I Kc.conf.X (Kc.conf.Pad × Kc.conf.Rnd) Kc.conf.Seed Kc.conf.Ans a
    (linkProtocolOfRoundData C ds a xs dec2) :=
  restM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀
    (linkProtocolWithWireOfRoundData C ds xs dec2 salt (kM Kc f key k rec₀ c block z₀) K hK chal) N early late P

/-- At the written link over letters the three files' wiring is the wiring at which the entry's arm
is said, with the key file's and the proof file's own wire records and maps of bodies. -/
theorem wireM_sib (depthReq depthReqT depthReqL : ℕ) :
    wireM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀
        (linkProtocolWithWireOfRoundData C ds xs dec2 salt (kM Kc f key k rec₀ c block z₀) K hK chal) N early late P salt
        depthReq depthReqT depthReqL =
      wireOf2
        (L := LrG (restSibM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ C ds xs
          dec2 salt K hK chal N early late P))
        (aT := (chainsOf (ckP f) ((dataK Kc key k rec₀).at a) tFk tJk t3k).ann)
        (aL := _root_.Run.Twin.allLo (SOf C ds)) (K + 1)
        (wqWhole (ckP f) K (chalP f K) ((dataK Kc key k rec₀).at a) tFk tJk t3k silK
          (runKM Kc key k rec₀))
        (wSib (restSibM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ C ds xs dec2
          salt K hK chal N early late P) K chal)
        (wqWhole (ckP f) K (chalP f K) ((dataP Kc key c block z₀).at a) tFp tJp t3p silP
          (runPM Kc key c block z₀))
        a depthReq depthReqT depthReqL
        (bodiesSib (restSibM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ C ds xs
          dec2 salt K hK chal N early late P) salt
          (SCode.emb _ (scWhole salt (ckP f) ((dataK Kc key k rec₀).at a) tFk tJk t3k))
          (SCode.prj _ (scWhole salt (ckP f) ((dataK Kc key k rec₀).at a) tFk tJk t3k))
          (SCode.emb _ (scWhole salt (ckP f) ((dataP Kc key c block z₀).at a) tFp tJp t3p))
          (SCode.prj _ (scWhole salt (ckP f) ((dataP Kc key c block z₀).at a) tFp tJp t3p))) :=
  rfl

/-- Link's plain parts over the three files' typed interface, against those over the description's
own letters. -/
def pbLM (D : XD) (hC : C = D.C) (hds : ds = D.ds) :
    PlainPart (shapeOf (LM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀
               (linkProtocolWithWireOfRoundData C ds xs dec2 salt (kM Kc f key k rec₀ c block z₀) K hK chal) N early late P)
               .link)
      (annOf (LM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀
        (linkProtocolWithWireOfRoundData C ds xs dec2 salt (kM Kc f key k rec₀ c block z₀) K hK chal) N early late P)
        .link) ≃
      PlainPart (_root_.Run.Twin.up (SOf D.C D.ds)) (RoundSplits.allLocal (_root_.Run.Twin.up (SOf D.C D.ds))) :=
  pbSib D C ds hC hds

end Sib

end OnBytes.K.Arm
