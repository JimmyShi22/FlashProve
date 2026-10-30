-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Flat/LinkSibAt.lean: the link over pairs of records (`linkSib`, OnBytes/Flat/LinkSib.lean),
at the shape of `LinkX`, at the full size and at the small example: written terms,
their soundness for the language of the compiled verifier's link, and that their verifiers are
local.

Main names (the small example's have Small for Full):
  `wFull`: a description whose rounds are the written rounds (`frFmt`: 41; `srFmt`: 24) and whose
    first tree has the number 0; its other fields are fillers, which the rounds' data do not read.
    It is not `OnBytes.K.wFull` | `wSmall` (Johnson/Top/TieSeedSizes.lean),
      which are wires.
  `dsFull`: the rounds' data of `wFull`, carried over by `PQ.ofLib`. Lean makes code for
    it and for `linkSibFull`. OnBytes/Flat/LinkSibAccepts.lean runs `linkSibSmall`; no file of this
    library runs `linkSibFull`, and this file stands in a noncomputable section, where Lean does not
    report it if a definition gets no code.
  `rdsFull_eq`, `dsFull_eq`: these data are `frRd 0`, …, `frRd 5`, `frC.rds`, of which the chain's
    theorems speak; the second says it of the carried list.
  `decFullX`: the decision at an instance: the program's own decision of the link at the two keys
    written of the instance.
  `linkSibFull`: `linkSib` at the kit of the second field, `dsFull`, the depth of the tables' code,
    the written stored openings, and `decFullX`.
  `decFullX_recX`: at the instance made of two records the decision is the program's at the keys
    written of the two records.
  `soundAt_full`: soundness instance by instance at these letters, under the hypothesis on codes.
  `linkSibFull_sound`: there is a list of counts, one for each round, each below 2^-128, with which
    `linkSibFull` is sound for "the first table's decoder finds nothing, or the copy collides at its
    seed, or both decoders find the same", at the configuration of any claims A and rest R.
  `linkSibFull_local`.
  `letters_full`: the four letters are those of `entryXD recordGround c`, at every c.

Hypothesis: `Cb.BCHKS46At GF GE`, for the two theorems on soundness.

Limits: nothing on an honest prover; nothing on a wire or a compiled verifier. The typed numbers in
`frFmt` | `srFmt` are not made from a parameter file here. The proofs of `rdsFull_eq` |
`rdsSmall_eq` name the dry run of the verifier program's link: they rest on `fr_fmt` | `sr_fmt`
(OnBytes/Slice/FullRecSz.lean | SmallRecSz.lean), by which the dry run's rounds are the written
ones. The stored openings are `frD.xs` | `srD.xs`, and to evaluate these is to make that dry
run. The decision is a run of the verifier program's link. It and the stored openings name
`recordRead` | `smallRecordRead`, which hold a typed 32-byte digest of three public files; the
decision does not read that digest (`decRun_full` | `decRun_small`, OnBytes/Flat/LinkSibRun.lean).
Each count bounds the error of one round, not the chance of a false proof. At six rounds of the full
size and four of the small, 32 of the 128 bits are proof of work, not shown to be worth its bits.
Terms: lean/GLOSSARY.md.
-/
import OnBytes.Flat.LinkSib
import OnBytes.TypedOracleCompiler.Slice.EntryRow13JohFull
import OnBytes.TypedOracleCompiler.Slice.EntryRow13JohSmall
import OnBytes.TypedOracleCompiler.Slice.EntryHomeFull
import OnBytes.TypedOracleCompiler.Slice.EntryHomeSmall

set_option autoImplicit false

noncomputable section

namespace OnBytes.Flat
open OnBytes.Slice TypedOracleCompiler.Slice TypedOracleCompiler.Run OnBytes.Tie
open OnBytes.Params (recordRead smallRecordRead)
open _root_.Iop (Err InteractiveOracleProof twoExternalStrings)
open _root_.Run (ckP)
open _root_.Run.PQ (View SgX)
open scoped ENNReal

/-! ## The full size -/

/-- A description whose rounds are the written rounds `frFmt`. The other fields are fillers: the
rounds' data depend on a description's rounds and on the number of its first tree alone
(`Run.rds_congr`). -/
def wFull : _root_.Fmt.Spec :=
  { label := 0, plan := ⟨.two, 0, 0, 0, 0, 0, []⟩, params := ByteArray.empty,
    statement := ByteArray.empty, rand := .inFile, firstTree := 0, cfg := ByteArray.empty,
    rounds := frFmt }

/-- The rounds' data, written. -/
abbrev dsFull : List PQ.RD := (_root_.Run.PQ.rds wFull).map PQ.ofLib

/-- The written rounds' data are those of the link's five rounds, the batching's and the chain's:
the list `frRds` (OnBytes/Slice/LinkFamily.lean), spelt out. -/
theorem rdsFull_eq : _root_.Run.PQ.rds wFull =
    frRd 0 :: frRd 1 :: frRd 2 :: frRd 3 :: frRd 4 :: frRd 5 :: frC.rds := by
  rw [show _root_.Run.PQ.rds wFull = _root_.Run.PQ.rds frBase from
    _root_.Run.rds_congr _ _ rfl rfl, ← fr_ds, fr_ds_C]

/-- The same of the carried list. -/
theorem dsFull_eq : dsFull =
    (frRd 0 :: frRd 1 :: frRd 2 :: frRd 3 :: frRd 4 :: frRd 5 :: frC.rds).map PQ.ofLib :=
  congrArg (List.map PQ.ofLib) rdsFull_eq

/-- The decision at an instance. -/
def decFullX (x : XE AnsT 29 1) : View → Bool :=
  (linkVerify recordRead.link (keysOfX frS.P.v 29 1 (anT frS.P.v 1) x).1
    (keysOfX frS.P.v 29 1 (anT frS.P.v 1) x).2).decides (Entry.start recordRead)

/-- The link over pairs of records at the shape of `LinkX`, at the full size. -/
abbrev linkSibFull :
    InteractiveOracleProof (RecP NZ frS.P.v 29 1 × RecP NZ frS.P.v 29 1) (twoExternalStrings (2 ^ frS.P.T.a) SgX) :=
  linkSib (v := frS.P.v) (ckP .two) dsFull frS.P.T.a frD.xs decFullX

/-- At the instance made of two records: the program's decision at the keys written of them. -/
theorem decFullX_recX (rr : RecP NZ frS.P.v 29 1 × RecP NZ frS.P.v 29 1) :
    decFullX (recX rr) = (linkVerify recordRead.link (keyOf (fun β : NZ => β.val) rr.1)
      { keyOf (fun β : NZ => β.val) rr.2 with item := 1 }).decides (Entry.start recordRead) := by
  unfold decFullX
  rw [keys_recX]

/-- The four letters are those of the entry's description, at every digest. -/
theorem letters_full (c : ByteArray) :
    (entryXD recordGround c).C = ckP .two ∧ (entryXD recordGround c).ds = dsFull ∧
      (entryXD recordGround c).a = frS.P.T.a ∧ (entryXD recordGround c).xs = frD.xs :=
  ⟨congrArg ckP (full_four c).1, (full_four c).2.1.trans dsFull_eq.symm, (full_four c).2.2.1,
    (full_four c).2.2.2⟩

set_option maxRecDepth 40000 in
/-- Soundness instance by instance at the written letters. This is said under the hypotheses that
stand in the statement itself, which this comment does not list; it is no claim that they hold. -/
theorem soundAt_full (hA : Cb.BCHKS46At GF GE) :
    SoundAt frS.P.T frS.P.v frS.eM 29 1 decFullX (((2 : ℝ≥0∞)⁻¹) ^ 128) (ckP .two) dsFull
      frS.P.T.a frD.xs := by
  obtain ⟨hf, hds, ha, hxs⟩ := full_four ByteArray.empty
  have h := soundAt_at frS.P.T frS.P.v frS.eM 29 1 decFullX _ (entryXD recordGround ByteArray.empty)
    (fr_row13_key hA (anT frS.P.v 1) _ hf hds ha hxs (keysOfX frS.P.v 29 1 (anT frS.P.v 1))
      fun x => ⟨rfl, rfl,
        keyHasR_keyOf (recOf frS 29 1 (anT frS.P.v 1) x).1 _ rfl rfl Shapes.zFull_lg 0,
        keyHasR_keyOf (recOf frS 29 1 (anT frS.P.v 1) x).2 _ rfl rfl Shapes.zFull_lg 1⟩)
  rw [(letters_full ByteArray.empty).1, hds, ← dsFull_eq, ha, hxs] at h
  exact h

/-- It is sound for the language of the compiled verifier's link, with each round's count below
2^-128; at six rounds 32 of these bits are proof of work, which is not shown to be worth its bits.
This is said under the hypotheses that stand in the statement; it is no claim that they hold. -/
theorem linkSibFull_sound (hA : Cb.BCHKS46At GF GE) {X : Type}
    (A : (frS.toDecR frZ 402653181).Claims X) (R : (frS.toDecR frZ 402653181).RelationsAndEncoding A) :
    ∃ ε : Err linkSibFull.shape,
      linkSibFull.Sound
        (fun rr y => (DecR.configurationOfStoredTable A R).D y.1 rr.1 = none ∨ (DecR.configurationOfStoredTable A R).coll y.2 rr.2.1 ∨
          (DecR.configurationOfStoredTable A R).D y.2 rr.2 = (DecR.configurationOfStoredTable A R).D y.1 rr.1) ε ∧
        Err.Below ε (((2 : ℝ≥0∞)⁻¹) ^ 128) :=
  linkSib_sound frS.P.T frS.P.v frS.eM 29 1 decFullX _ A R _ _ _ (soundAt_full hA)

/-- Its verifier is local. -/
theorem linkSibFull_local : linkSibFull.IsLocal := linkSib_local _ _ _ _ _

/-! ## The small example -/

/-- A description whose rounds are the written rounds `srFmt`. But for the number of the first tree
the other fields are fillers. -/
def wSmall : _root_.Fmt.Spec :=
  { label := 0, plan := ⟨.two, 0, 0, 0, 0, 0, []⟩, params := ByteArray.empty,
    statement := ByteArray.empty, rand := .inFile, firstTree := 0, cfg := ByteArray.empty,
    rounds := srFmt }

/-- The rounds' data, written. -/
abbrev dsSmall : List PQ.RD := (_root_.Run.PQ.rds wSmall).map PQ.ofLib

/-- The written rounds' data are those of the link's five rounds, the batching's and the chain's:
the list `srRds` (OnBytes/Slice/LinkFamily.lean), spelt out. -/
theorem rdsSmall_eq : _root_.Run.PQ.rds wSmall =
    srRd 0 :: srRd 1 :: srRd 2 :: srRd 3 :: srRd 4 :: srRd 5 :: srC.rds := by
  rw [show _root_.Run.PQ.rds wSmall = _root_.Run.PQ.rds srBase from
    _root_.Run.rds_congr _ _ rfl rfl, ← sr_ds, sr_ds_C]

/-- The same of the carried list. -/
theorem dsSmall_eq : dsSmall =
    (srRd 0 :: srRd 1 :: srRd 2 :: srRd 3 :: srRd 4 :: srRd 5 :: srC.rds).map PQ.ofLib :=
  congrArg (List.map PQ.ofLib) rdsSmall_eq

/-- The decision at an instance. -/
def decSmallX (x : XE AnsT 19 1) : View → Bool :=
  (linkVerify smallRecordRead.link (keysOfX srS.P.v 19 1 (anT srS.P.v 1) x).1
    (keysOfX srS.P.v 19 1 (anT srS.P.v 1) x).2).decides (Entry.start smallRecordRead)

/-- The link over pairs of records at the shape of `LinkX`, at the small example. -/
abbrev linkSibSmall :
    InteractiveOracleProof (RecP NZ srS.P.v 19 1 × RecP NZ srS.P.v 19 1) (twoExternalStrings (2 ^ srS.P.T.a) SgX) :=
  linkSib (v := srS.P.v) (ckP .two) dsSmall srS.P.T.a srD.xs decSmallX

/-- At the instance made of two records: the program's decision at the keys written of them. -/
theorem decSmallX_recX (rr : RecP NZ srS.P.v 19 1 × RecP NZ srS.P.v 19 1) :
    decSmallX (recX rr) = (linkVerify smallRecordRead.link (keyOf (fun β : NZ => β.val) rr.1)
      { keyOf (fun β : NZ => β.val) rr.2 with item := 1 }).decides
        (Entry.start smallRecordRead) := by
  unfold decSmallX
  rw [keys_recX]

/-- The four letters are those of the entry's description, at every digest. -/
theorem letters_small (c : ByteArray) :
    (entryXD smallRecordGround c).C = ckP .two ∧ (entryXD smallRecordGround c).ds = dsSmall ∧
      (entryXD smallRecordGround c).a = srS.P.T.a ∧ (entryXD smallRecordGround c).xs = srD.xs :=
  ⟨congrArg ckP (small_four c).1, (small_four c).2.1.trans dsSmall_eq.symm, (small_four c).2.2.1,
    (small_four c).2.2.2⟩

set_option maxRecDepth 40000 in
/-- Soundness instance by instance at the written letters. This is said under the hypotheses that
stand in the statement itself, which this comment does not list; it is no claim that they hold. -/
theorem soundAt_small (hA : Cb.BCHKS46At GF GE) :
    SoundAt srS.P.T srS.P.v srS.eM 19 1 decSmallX (((2 : ℝ≥0∞)⁻¹) ^ 128) (ckP .two) dsSmall
      srS.P.T.a srD.xs := by
  obtain ⟨hf, hds, ha, hxs⟩ := small_four ByteArray.empty
  have h := soundAt_at srS.P.T srS.P.v srS.eM 19 1 decSmallX _
    (entryXD smallRecordGround ByteArray.empty)
    (sr_row13_key hA (anT srS.P.v 1) _ hf hds ha hxs (keysOfX srS.P.v 19 1 (anT srS.P.v 1))
      fun x => ⟨rfl, rfl,
        keyHasR_keyOf (recOf srS 19 1 (anT srS.P.v 1) x).1 _ rfl rfl Shapes.zSmall_lg 0,
        keyHasR_keyOf (recOf srS 19 1 (anT srS.P.v 1) x).2 _ rfl rfl Shapes.zSmall_lg 1⟩)
  rw [(letters_small ByteArray.empty).1, hds, ← dsSmall_eq, ha, hxs] at h
  exact h

/-- It is sound for the language of the compiled verifier's link, with each round's count below
2^-128; at four rounds 32 of these bits are proof of work, which is not shown to be worth its bits.
This is said under the hypotheses that stand in the statement; it is no claim that they hold. -/
theorem linkSibSmall_sound (hA : Cb.BCHKS46At GF GE) {X : Type}
    (A : (srS.toDecR srZ 524285).Claims X) (R : (srS.toDecR srZ 524285).RelationsAndEncoding A) :
    ∃ ε : Err linkSibSmall.shape,
      linkSibSmall.Sound
        (fun rr y => (DecR.configurationOfStoredTable A R).D y.1 rr.1 = none ∨ (DecR.configurationOfStoredTable A R).coll y.2 rr.2.1 ∨
          (DecR.configurationOfStoredTable A R).D y.2 rr.2 = (DecR.configurationOfStoredTable A R).D y.1 rr.1) ε ∧
        Err.Below ε (((2 : ℝ≥0∞)⁻¹) ^ 128) :=
  linkSib_sound srS.P.T srS.P.v srS.eM 19 1 decSmallX _ A R _ _ _ (soundAt_small hA)

/-- Its verifier is local. -/
theorem linkSibSmall_local : linkSibSmall.IsLocal := linkSib_local _ _ _ _ _

end OnBytes.Flat
