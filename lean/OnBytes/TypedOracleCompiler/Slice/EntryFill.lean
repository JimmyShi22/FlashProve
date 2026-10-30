-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/EntryFill.lean: some of the letters of OnBytes/TypedOracleCompiler/Slice/EntryDelivers.lean
filled: pins with the port's own label; the implementation is the page of
OnBytes/TypedOracleCompiler/Run/EntryPage.lean, typed as `EntryAt.m`; with it the hypotheses of `entry_delivers` on
the page: `one`, `blocks`, and the page's half of `clean`.

`EntryAt` (EntryDelivers.lean) holds what an entry's part is made of, as letters: among them a
description D, the type of leaves' bodies, and an implementation m of the typed oracles by one
oracle, over the interface `LXEs` at D.K + 1 blocks. This file takes bodies that are strings and
answers that are lists of triples. The sibling is a second form of the library's soundness
road, under OnBytes/TypedOracleCompiler/.
 - `pinsE`: pins, as a function of the configuration's digest, the link's parameter digest and what
   stands behind the root in a table's name; the label is the port's `Params.labelLink`: so the type
   `EntryFb.PinsE` is not empty;
 - `pageForE`: the page at these pins and OnBytes/TypedOracleCompiler/Run/KeyLeaves.lean's code of leaves, as an
   implementation over `LXEs` at D.K + 1 blocks: it types as `EntryAt.m` by unfolding;
 - `pageForE_one`, `pageForE_blocks` (at most D.K + 2), `pageForE_not_public`, `pageForE_call`: what
   `entry_delivers` asks of the page, but for `reads`; clean's half on the page;
 - `pageForE_leaf`: a leaf query's string, for a file's salt of whole bytes;
 - `pageForE_first`: under conditions (see its docstring), at the block of the tail, the link's
   first typed query has the string of the call that gives a link's chain its first value
   (`Fmt.firstValueW`): the hash under 160 with `Params.labelLink`, on pd's bytes, the program's own
   `Params.Link.statement` of the two tables, an empty record and a run value of 32 bytes; that pd
   and the run value are those of a reading is not said here; `pageForE_round`, `pageForE_vertex`:
   EntryPage.lean's equations said again at the page.

Main definitions: `pinsE`, `pageForE`.
Main theorems: `pageForE_one`, `pageForE_blocks`, `pageForE_not_public`, `pageForE_call`,
`pageForE_leaf`, `pageForE_first`, `pageForE_round`, `pageForE_vertex`.

Not claimed. `clean` whole: that the judge's run never asks the spare oracle, and that a part's
public strings are calls under 169 with a start of 32 bytes. `reads`, `flat`, soundness, the typing:
nothing. cfg, pd, `rest`, `back` and n, the bits of a file's salt, stay arguments; nothing ties them
to a configuration or to hash values. THE PINS ARE LOOSER THAN AN ENTRY FILE IS: `rest` is free
beside cfg, though in a table's name it begins with it; n is free beside the plan's salt; the
description D itself holds a label, a digest and a salt's length, and nothing ties the pins to
these. The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it
builds on definitions of Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.EntryDelivers
import OnBytes.TypedOracleCompiler.Run.EntryPage
import OnBytes.TypedOracleCompiler.Run.KeyLeaves

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Slice.EntryFill
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Slice
open TypedOracleCompiler.Run.EntryFb TypedOracleCompiler.Run.EntryPage TypedOracleCompiler.Run.Apart
open TypedOracleCompiler.Run.KeyPage (NotSix)
open TypedOracleCompiler.Run.FirstAnswers (T3)
open TypedOracleCompiler.Run.PQ (XD)
open OnBytes.Slice (seedEntry)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run

variable {lg s : ℕ} (D : XD) (d₁ : Sd1 lg s)

/-- The interface of `EntryAt` at bodies that are strings and answers that are lists of triples. -/
abbrev Ls := LXEs (An := List T3) (Bd := List Bool) lg s D d₁

/-- Pins, with the port's label of a link's chain. -/
def pinsE (cfg : ByteArray) (hcfg : cfg.size = 32) (pd : Dig 256) (rest : ByteArray) :
    PinsE D (earlyTwo (A := List T3 × List T3) d₁) (seedEntry lg s) where
  cfg := cfg
  hcfg := hcfg
  pd := pd
  l := OnBytes.Params.labelLink
  hR := by decide
  hlt := by decide
  rest := rest

variable (cfg : ByteArray) (hcfg : cfg.size = 32) (pd : Dig 256) (rest : ByteArray) (n : ℕ)
  (back : StrCode (AllPts 256 (D.K + 1) (Ls D d₁)))

/-- The interface without its bodies: the library's, of which `Ls` is the form with strings. -/
abbrev L0 : _root_.Iop.BatchProtocol Unit ((List T3 × List T3) × (Sd1 lg s × Sd1 lg s)) :=
  (Ls D d₁).toBatchProtocol

/-- The page, over the interface of `EntryAt`, at D.K + 1 blocks. n: the bits of a file's salt.
-/
def pageForE : OracleCoding (typedOracleFamily 256 (D.K + 1) (Ls D d₁)) 256 :=
  implE (pinsE D d₁ cfg hcfg pd rest) (d₁, d₁) (D.K + 1)
    (KeyLeaves.leavesAt (L0 D d₁) n cfg) back

/-- A leaf's and a vertex's answer is one block, taken as it is. -/
theorem pageForE_one : OneBlock (pageForE D d₁ cfg hcfg pd rest n back) :=
  oneBlock_implE _ _ _ _ _

/-- No answer has more than D.K + 2 blocks. -/
theorem pageForE_blocks (o : TypedOracleCompiler.Compile.Batch.OracleName) :
    (pageForE D d₁ cfg hcfg pd rest n back).blocks o ≤ D.K + 2 :=
  implE_blocks _ _ _ _ _ o

/-- No typed query but the spare oracle's has a string with another tag than the page's six that
does not begin with the byte 2. -/
theorem pageForE_not_public (o : TypedOracleCompiler.Compile.Batch.OracleName) (ho : o ≠ .other)
    (q : domOf 256 (Ls D d₁) o) (j : Fin (blk (D.K + 1) o)) (t : List Bool)
    (ht : tag16 t ≠ t160 ∧ tag16 t ≠ t162 ∧ tag16 t ≠ t164 ∧ tag16 t ≠ t166 ∧ tag16 t ≠ t173 ∧
      tag16 t ≠ TypedOracleCompiler.Run.t174) (h2 : ¬ bitsOfByte 2 <+: t) :
    (pageForE D d₁ cfg hcfg pd rest n back).code o q j ≠ t :=
  implE_not_public _ _ _ _ _ o ho q j t ht h2

/-- The string of a call under 169, 172 or 179 (any number with another tag than the six), either
half, a start of 32 bytes, is a point of the spare oracle, written as itself, and the string of no
other typed query. -/
theorem pageForE_call (m : ℕ) (hm : NotSix m) (half : UInt8) (hh : half = 0 ∨ half = 1) (t i : ℕ)
    (st bs : ByteArray) (hst : st.size = 32) :
    (∀ j, (pageForE D d₁ cfg hcfg pd rest n back).code .other
        (bytesToBits (_root_.Fmt.oStr half m t i st bs)) j =
        bytesToBits (_root_.Fmt.oStr half m t i st bs)) ∧
      ∀ (o : TypedOracleCompiler.Compile.Batch.OracleName), o ≠ .other → ∀ (q : domOf 256 (Ls D d₁) o)
        (j : Fin (blk (D.K + 1) o)),
        (pageForE D d₁ cfg hcfg pd rest n back).code o q j ≠
          bytesToBits (_root_.Fmt.oStr half m t i st bs) :=
  implE_call _ _ _ _ _ m hm half hh t i st bs hst

/-- A leaf query at which the code of leaves writes has the bits of the format's string of the
call that `Strings.call2` gives, for a file's salt of whole bytes. -/
theorem pageForE_leaf (k : ℕ) (hn : n = 8 * k) (q : LeafIn (Ls D d₁)) (t : List Bool)
    (h : (KeyLeaves.leafCode (L0 D d₁) n cfg).put q = some t) (j : Fin 1) :
    (pageForE D d₁ cfg hcfg pd rest n back).code .leaf q j = t ∧
      ∃ c, Strings.call2 (L0 D d₁) q = some c ∧ t = bytesToBits (strOf c) :=
  ⟨implE_leaf _ _ _ _ back q t h j, KeyLeaves.leafCode_str _ n cfg k hn q t h⟩

/-- THE LINK's FIRST TYPED QUERY AT THE PAGE HAS THE STRING OF THE CALL THAT GIVES A LINK's CHAIN
ITS FIRST VALUE (`Fmt.firstValueW`; a reader makes two calls before it, under 169 and 172), with
the fixed value twice in the seeds' place: at two tables whose roots are two digests' bytes, with
fewer than 2 ^ 32 answers each, and a run value of 32 bytes as the typed salt: at the block of the
tail the string is `Fmt.oStr` of the hash under 160 with the port's label of a link's chain, on pd's
bytes, THE PROGRAM's OWN STATEMENT `Params.Link.statement`, an empty record and the run value. -/
theorem pageForE_first (first further : OnBytes.Params.TableName) (c₀ c₁ : Dig 256)
    (h₀ : first.root = digToBytes c₀) (h₁ : further.root = digToBytes c₁)
    (l₀ : first.answers.length < 2 ^ 32) (l₁ : further.answers.length < 2 ^ 32) (run : ByteArray)
    (hr : run.size = 32) :
    (pageForE D d₁ cfg hcfg pd rest n back).code (.fb .link)
        ⟨0, .f1 [c₀, c₁] (some ((first.answers.map OnBytes.E.triple, further.answers.map OnBytes.E.triple),
          (d₁, d₁))) (bytesToBits run), [], p0E D (earlyTwo d₁) (seedEntry lg s)⟩
        (Fin.last (D.K + 1)) =
      bytesToBits (_root_.Fmt.oStr 0 160 0 OnBytes.Params.labelLink _root_.Fmt.zero32
        (_root_.Fmt.firstBytes (digToBytes pd) (OnBytes.Params.Link.statement first further)
          ByteArray.empty (some run))) := by
  have hl : (bytesToBits run).length = 256 := by rw [length_bytesToBits, hr]
  have h := implE_first (pinsE D d₁ cfg hcfg pd rest) (d₁, d₁) (D.K + 1)
    (KeyLeaves.leavesAt (L0 D d₁) n cfg) back c₀ c₁ (first.answers.map OnBytes.E.triple)
    (further.answers.map OnBytes.E.triple) (bytesToBits run) (by rw [List.length_map]; exact l₀)
    (by rw [List.length_map]; exact l₁) (Or.inr hl)
  have hs : _root_.Fmt.tableItem "the first table" (digToBytes c₀) (first.answers.map OnBytes.E.triple) ++
      _root_.Fmt.tableItem "the further table" (digToBytes c₁) (further.answers.map OnBytes.E.triple) =
      OnBytes.Params.Link.statement first further := by
    unfold OnBytes.Params.Link.statement
    rw [h₀, h₁]
  have hv : runOf (bytesToBits run) = some run :=
    runOf_saltOf (some run) fun r e0 => by rw [← Option.some.inj e0]; exact hr
  rw [hs, hv] at h
  exact h

/-- The written round k at the page: `EntryPage.implE_round` at D.K + 1 and the port's label. -/
theorem pageForE_round (hK : D.K + 1 < 2 ^ 48) (k : Fin D.ds.length) (hi : k.val + 1 < 2 ^ 64)
    (hw : (D.ds.get k).entry.work < 256) (ρ : Bits) (hρ : ρ.length = 256) (rt : List (Dig 256))
    (z : PlainIn.PlainD (D.ds.get k))
    (hok : PQ.okRound (D.ds.get k).entry.work (D.ds.get k).items rt z = true)
    (j : Fin (D.K + 1 + 1)) :
    (pageForE D d₁ cfg hcfg pd rest n back).code (.fb .link)
        ⟨k.val + 1, .f2 none ρ, rt, inE D (earlyTwo d₁) (seedEntry lg s) k z⟩ j =
      bytesToBits (_root_.Fmt.oStr
        (UInt8.ofNat ((blockTo (KeyPageRounds.ordOf (D.ds.get k)) (D.K + 1) j).val % 2))
        162 OnBytes.Params.labelLink (k.val + 1) (bitsToBytes ρ)
        (PQ.bytesL (rt.map digToBytes) (D.ds.get k).items
            (GPlain.old (b := (D.ds.get k).entry.work) z) ++
          _root_.Fmt.tail (D.ds.get k).kind (D.ds.get k).entry.work
            (GPlain.nonce (b := (D.ds.get k).entry.work) z)
            ((blockTo (KeyPageRounds.ordOf (D.ds.get k)) (D.K + 1) j).val / 2))) :=
  implE_round (pinsE D d₁ cfg hcfg pd rest) (d₁, d₁) (D.K + 1) _ back hK k hi hw ρ hρ rt z hok j

/-- A vertex query on two strings of 256 bits at the page. -/
theorem pageForE_vertex (l r : Bits) (hl : l.length = 256) (hr : r.length = 256) (j : Fin 1) :
    (pageForE D d₁ cfg hcfg pd rest n back).code .node (l, r) j =
      bytesToBits (_root_.Fmt.oStr 0 166 0 0 cfg (bitsToBytes l ++ bitsToBytes r)) :=
  implE_vertex (pinsE D d₁ cfg hcfg pd rest) (d₁, d₁) (D.K + 1) _ back l r hl hr j

end TypedOracleCompiler.Slice.EntryFill
