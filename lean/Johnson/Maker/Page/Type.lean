-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Maker/Page/Type.lean: the type of a family of typed oracle functions at the two makers'
values and an entry's part: what a function "typed query to the answer of a hash on the format's own
string" must have, to be put under the compiled verifier with a record at these values.

  `LM ..`: the typed interface: the carrier (`typedOracleCarrier`, Johnson/TypedOracleCompiler/RecCompile/Carrier.lean) of the
    object `(filesM ..).withProvers P` (Johnson/EntryRec/AtMaker.lean), a leaf's body a string of bits, at
    the object's own two annotations.
  `FamM ..`: the families of oracle functions over it, at `p.K + 1` blocks an answer.
  `wireM_K`: that number is the wiring `wireM`'s (Johnson/EntryRec/AtMakerA.lean), by unfolding: so
    a g of the type `FamM ..` is what `.det g` takes at the verifiers `verifyOfflineProof`, `verifyLinkProof`, `verifyOnlineProof` at
    `wireM`.
  `famM_is`: the same as an equation of types, by unfolding.
  `pb_test`, `pb_onl`, `pb_link`: the plain parts of the typed interface under the three tags are
    the plain parts of the three files' own rounds at their own annotations, by unfolding. The
    verifiers `verifyOfflineProof`, `verifyOnlineProof` (Johnson/TypedOracleCompiler/RecCompile/CmsAns.lean) and `verifyLinkProof` (LinkAns.lean) pass `id`
    where a plain part is embedded: so its read-back is the identity.
  `lm_late`, `lm_late_none`: the round behind which the rest of an instance is named is the files'
    own letter `late`, by unfolding; where that is `none`, the typed interface names no round.
    (`verifyOfflineProof` and `verifyLinkProof` hand no instance to a chain at all: they pass `fun _ => none`; `verifyOnlineProof` passes
    `xinBA`.)

Definitions, six equations by unfolding and one consequence. No family is given here.


-/
import Johnson.EntryRec.AtMakerA

set_option autoImplicit false

namespace OnBytes.Maker.Page

open _root_.Run _root_.Run.PQ Iop Hiop OnBytes.Maker OnBytes.Flat OnBytes.RunA

attribute [local instance] ConfLetters.finRnd ConfLetters.neRnd ConfLetters.finPad
  ConfLetters.nePad ConfLetters.finSeed ConfLetters.neSeed

variable {a : ℕ} (Kc : ConfLetters a) (f : _root_.Fmt.Fld)
  {TFk TJk T3k TFp TJp T3p : Type} (tFk : TFk) (tJk : TJk) (t3k : T3k) (tFp : TFp) (tJp : TJp)
  (t3p : T3p) (silK : Kc.conf.Rec → TFk → TJk → T3k → Bool)
  (silP : Kc.conf.X × Kc.conf.Rec → TFp → TJp → T3p → Bool) (key : Kc.conf.Rec → TableKey)
  (k : Params.KeyChains) (rec₀ : Kc.conf.Rec) (c : Params.ProofChains)
  (block : Kc.conf.X → Blk Proof.FirstEnd) (z₀ : Kc.conf.X × Kc.conf.Rec) (p : LinkProtocolWithLeafCodingAndQueryLayout Kc.conf.Rec a
    (kM Kc f key k rec₀ c block z₀)) (N : ℕ) (early : Kc.conf.X → Kc.conf.X) (late : Option ℕ)
  (P : (filesM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early
    late).Provers)

/-- **The typed interface at the two makers' values and an entry's part.** -/
noncomputable abbrev LM :=
  TypedOracleCompiler.Compile.Batch.Cms.typedOracleCarrier
    ((filesM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early late).withProvers P)
    (List Bool)
    (filesM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early late).annT
    (filesM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early late).annL

/-- **The families of typed oracle functions over it.** -/
abbrev FamM : Type :=
  Rom.Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 (p.K + 1)
    (LM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early late P))

/-- The number of blocks is the wiring's. -/
theorem wireM_K (salt depthReq depthReqT depthReqL : ℕ) :
    (wireM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early late P salt
      depthReq depthReqT depthReqL).K = p.K + 1 := rfl

/-- A family over the wiring's own number of blocks is a `FamM`. -/
theorem famM_is (salt depthReq depthReqT depthReqL : ℕ) :
    Rom.Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256
      (wireM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early late P salt
        depthReq depthReqT depthReqL).K
      (LM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early late P)) =
    FamM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early late P := rfl

/-- **A plain part of the typed interface under the tag "test" is a plain part of the key file's own
rounds**, by unfolding: nothing is embedded. -/
theorem pb_test :
    TypedOracleCompiler.Compile.Batch.PlainPart (TypedOracleCompiler.Compile.Batch.shapeOf
                       (LM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early late P) .test)
      (TypedOracleCompiler.Compile.Batch.annOf
        (LM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early late P)
        .test) =
    TypedOracleCompiler.Compile.Batch.PlainPart (chainsOf (ckP f) (dataK Kc key k rec₀) tFk tJk t3k).sh
      (chainsOf (ckP f) (dataK Kc key k rec₀) tFk tJk t3k).ann := rfl

/-- The same under the tag "onl", for the proof file. -/
theorem pb_onl :
    TypedOracleCompiler.Compile.Batch.PlainPart (TypedOracleCompiler.Compile.Batch.shapeOf
                       (LM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early late P) .onl)
      (TypedOracleCompiler.Compile.Batch.annOf
        (LM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early late P)
        .onl) =
    TypedOracleCompiler.Compile.Batch.PlainPart (chainsOf (ckP f) (dataP Kc key c block z₀) tFp tJp t3p).sh
      (chainsOf (ckP f) (dataP Kc key c block z₀) tFp tJp t3p).ann := rfl

/-- The same under the tag "link", for the entry file. -/
theorem pb_link :
    TypedOracleCompiler.Compile.Batch.PlainPart (TypedOracleCompiler.Compile.Batch.shapeOf
                       (LM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early late P) .link)
      (TypedOracleCompiler.Compile.Batch.annOf
        (LM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early late P)
        .link) =
    TypedOracleCompiler.Compile.Batch.PlainPart p.QL.shape p.aL := rfl

/-- The round behind which the rest of an instance is named is the files' own letter. -/
theorem lm_late :
    (LM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early late P).late =
      late := rfl

/-- Where the files name no such round, the typed interface names none. -/
theorem lm_late_none (h : late = none) (n : ℕ) :
    (LM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early late P).late ≠
      some n := by
  rw [lm_late, h]
  exact fun e => by cases e

end OnBytes.Maker.Page
