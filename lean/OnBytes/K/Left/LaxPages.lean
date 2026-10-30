-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Left/LaxPages.lean: the laws that the walks of an entry's typed string ask of the page's
family (OnBytes/TypedOracleCompiler/Slice/EntryWhole.lean: `assembleS_walks`, `stoOkE_of_read`), at vertices and at
the leaves of a stored table: the family's answer is the hash that the format's reader computes.

First at any oracle g on strings of bits: the family is the one read out of g through the entry's
page (`EntryFill.pageForE`), the reader's hash is the one made of g (`RowsG.hOfG`). Then at the
family that runs (`famOf`, OnBytes/TypedOracleCompiler/Slice/EntryRunTop.lean), which is that family at the oracle
made from Lean's BLAKE2b.

Main names:
  `page_node`, `page_nodeLaw`: a vertex's answer; `NodeLaw` at the hash under 166 with the
    configuration's digest as the start.
  `page_stored`: the hypothesis `hleaf` of `stoOkE_of_read`, to the letter (by `RowsE3.stoE_law`).
  `size_hOfG`: the hash made of g has the format's lengths (the hypothesis `hz`).
  `famOf_atPage`, `famOf_nodeLaw`, `famOf_stored`: the same at the family that runs.
  `famOf_stoOk`: `StoOkE` for an opening of a stored table that the format's reader has read.

Limits: the leaves of the chain's own trees are in OnBytes/K/Left/LaxPagesOwn.lean. The stored
leaves' law asks that the shape is a stored tree's with the number 0 and the description's depth, a
width below 2^24, a depth of at most 63 and a salt of fewer than 2^11 bytes. That the reader has
read an opening (`ReadAs`), its root, its columns' and salts' lengths are hypotheses. Nothing on any
file, on soundness or on any hash's strength.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.EntryRunTop
import OnBytes.TypedOracleCompiler.Slice.EntryWhole
import OnBytes.TypedOracleCompiler.Run.RowsE3

set_option autoImplicit false

namespace OnBytes.K.Left
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Slice
open TypedOracleCompiler.Slice.EntryFill TypedOracleCompiler.Run.PageG TypedOracleCompiler.Run.Apart
open TypedOracleCompiler.Run.RowsG (hOfG size_oB node_of_code)
open TypedOracleCompiler.Run.EntryPageSafe (famSafe_eq)
open TypedOracleCompiler.Run.FirstAnswers (T3)
open TypedOracleCompiler.Run.PQ (XD bodyS)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run

/-- The hash made of an oracle on bits has the format's lengths. -/
theorem size_hOfG (g : Fam (rom 256)) (n t i : ℕ) (st bs : ByteArray) :
    (hOfG g n t i st bs).size = _root_.Fmt.dlen n := by
  show (_root_.Fmt.HO (oB (g ())) n t i st bs).size = _
  unfold _root_.Fmt.HO _root_.Fmt.dlen
  split
  · rw [ByteArray.size_append, size_oB, size_oB]
  · exact size_oB g _

variable {lg s : ℕ} (D : XD) (d₁ : Sd1 lg s) (cfg : ByteArray)
  (hcfg : cfg.size = 32) (pd : Dig 256) (rest : ByteArray) (n : ℕ)
  (back : StrCode (AllPts 256 (D.K + 1) (Ls D d₁))) (g : Fam (rom 256))

/-- A vertex's answer at the page: the hash under 166. -/
theorem page_node (l r : Bits) (hl : l.length = 256) (hr : r.length = 256) :
    (readBlocks (pageForE D d₁ cfg hcfg pd rest n back) g TypedOracleCompiler.Compile.Batch.OracleName.node
        ((l, r) : Bits × Bits) : Dig 256) =
      bytesToDig (hOfG g 166 0 0 cfg (bitsToBytes l ++ bitsToBytes r)) :=
  node_of_code _ g (l, r) 166 0 0 cfg _ (by decide)
    (pageForE_vertex D d₁ cfg hcfg pd rest n back l r hl hr 0)

/-- The law at vertices. -/
theorem page_nodeLaw : NodeLaw (readBlocks (pageForE D d₁ cfg hcfg pd rest n back) g)
    (fun l r => hOfG g 166 0 0 cfg (l ++ r)) where
  node := page_node D d₁ cfg hcfg pd rest n back g
  size := fun _ _ => size_hOfG g 166 0 0 cfg _

/-- The law at a stored table's leaves: `stoOkE_of_read`'s `hleaf`. sB: the bytes of a file's
salt. sh: a stored tree's shape with the number 0. -/
theorem page_stored (sB : ℕ) (hn : n = 8 * sB) (sh : _root_.Fmt.Shape) (h1 : sh.stored = true)
    (h2 : sh.tree = 0) (hW : sh.W < 2 ^ 24) (ha : 2 ^ sh.a + 2 ^ sh.a ≤ 2 ^ 64)
    (h8 : sB / 8 < 2 ^ 8) (x : ℕ) (col : List UInt64) (salt : ByteArray) (hx : x < 2 ^ sh.a)
    (hc : col.length = sh.W) (hs : salt.size = sB) :
    (readBlocks (pageForE D d₁ cfg hcfg pd rest n back) g TypedOracleCompiler.Compile.Batch.OracleName.leaf
        (⟨(bodyS sh.a sB).embE (x, col), leafSalt cfg salt⟩ : LeafIn (Ls D d₁)) : Dig 256) =
      bytesToDig (leafAtH (hOfG g) sh cfg x col salt) :=
  RowsE3.stoE_law (pinsE D d₁ cfg hcfg pd rest) (d₁, d₁) (D.K + 1) n back g sB
    TypedOracleCompiler.Strings.cX hn sh h1 h2 hW ha h8 x col salt hx hc hs

/-! ## At the family that runs -/

variable [DecidableEq (Sd1 lg s)] (hD : D.base.cfg.size = 32) (sh : OnBytes.Params.IndexShape)

/-- The family that runs is the page's family at the oracle made from Lean's BLAKE2b. -/
theorem famOf_atPage : EntryRunTop.famOf D hD d₁ sh =
    readBlocks (pageForE D d₁ (EntryRunTop.cfgOf D) hD (EntryRunTop.pdOf D)
      (EntryRunTop.restAt D sh) (8 * EntryRunTop.saltOf D) (EntryRunTop.backOf D d₁)) oBits :=
  famSafe_eq _ _ _ _ _ _ _ _

/-- The law at vertices, at the family that runs. -/
theorem famOf_nodeLaw : NodeLaw (EntryRunTop.famOf D hD d₁ sh)
    (fun l r => hOfG oBits 166 0 0 D.base.cfg (l ++ r)) := by
  rw [famOf_atPage]
  exact page_nodeLaw D d₁ (EntryRunTop.cfgOf D) hD (EntryRunTop.pdOf D) (EntryRunTop.restAt D sh)
    (8 * EntryRunTop.saltOf D) (EntryRunTop.backOf D d₁) oBits

/-- The law at a stored table's leaves, at the family that runs. f: a stored tree's shape with the
number 0 and the description's depth. -/
theorem famOf_stored (f : _root_.Fmt.Shape) (h1 : f.stored = true) (h2 : f.tree = 0)
    (hd : f.a = D.a) (hW : f.W < 2 ^ 24) (ha : 2 ^ f.a + 2 ^ f.a ≤ 2 ^ 64)
    (h8 : D.base.plan.salt / 8 < 2 ^ 8) (x : ℕ) (col : List UInt64) (salt : ByteArray)
    (hx : x < 2 ^ f.a) (hc : col.length = f.W) (hs : salt.size = D.base.plan.salt) :
    (EntryRunTop.famOf D hD d₁ sh TypedOracleCompiler.Compile.Batch.OracleName.leaf
        (⟨(bodyS D.a D.base.plan.salt).embE (x, col), leafSalt D.base.cfg salt⟩ :
          LeafIn (Ls D d₁)) : Dig 256) =
      bytesToDig (leafAtH (hOfG oBits) f D.base.cfg x col salt) := by
  rw [famOf_atPage, ← hd]
  exact page_stored D d₁ (EntryRunTop.cfgOf D) hD (EntryRunTop.pdOf D) (EntryRunTop.restAt D sh)
    (8 * EntryRunTop.saltOf D) (EntryRunTop.backOf D d₁) oBits D.base.plan.salt rfl f h1 h2 hW ha h8
    x col salt hx hc hs

/-- An opening of a stored table that the format's reader has read is in order at the family that
runs. -/
theorem famOf_stoOk {cms : List (Dig 256)} {op : OpAt}
    (R : ReadAs (hOfG oBits) D.base.cfg D.base.cfg op) (h1 : op.sh.stored = true)
    (h2 : op.sh.tree = 0) (hd : op.sh.a = D.a) (hW : op.sh.W < 2 ^ 24)
    (ha : 2 ^ op.sh.a + 2 ^ op.sh.a ≤ 2 ^ 64) (h8 : D.base.plan.salt / 8 < 2 ^ 8)
    (hr : cms.getD (whichOf D op) default = bytesToDig op.out.root)
    (hcol : ∀ c ∈ op.out.cols, c.length = op.sh.W)
    (hsalt : ∀ sl ∈ op.out.salts, sl.size = D.base.plan.salt) :
    StoOkE (EntryRunTop.famOf D hD d₁ sh) (fun l r => hOfG oBits 166 0 0 D.base.cfg (l ++ r))
      (bodyS D.a D.base.plan.salt).embE D.a D.base.cfg cms D op :=
  stoOkE_of_read (size_hOfG oBits) D.base.plan.salt R hd hr hcol hsalt
    (famOf_stored D d₁ hD sh op.sh h1 h2 hd hW ha h8)

end OnBytes.K.Left
