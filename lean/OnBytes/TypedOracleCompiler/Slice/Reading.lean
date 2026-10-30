-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/Reading.lean: ways of reading an external string off what a trace determines at
the leaves under a root, over the sibling's types. OnBytes/Slice/Reading.lean said again, WITH ONE
PARAMETER MORE: in the sibling a leaf's body has a type of the interface's choosing, so a reading is
a reading FOR A WAY `embE` OF WRITING A STORED SYMBOL INTO A BODY.

The sibling's compiler reads the string under a root in one way (`extEnc`): at each leaf it keeps
what the wire's `prjE` reads from the body that the trace determines there, whatever the salt. The
clauses of OnBytes/TypedOracleCompiler/Slice/PlainClause.lean are stated for any reading in the sense of this file:
a function of what stands at the leaves, with a test `keeps` on position, symbol and salt, and the
law that at a leaf whose body is `embE` of a kept symbol the string read has that symbol.

Main definitions: `Reading`, `Reading.at`, `Reading.wide` (the sibling's own; it asks besides that
the wire's `prjE` reads back what its `embE` writes), `Reading.byLeaf` (leaf by leaf, through a
function `keep`).
Main theorems: `Reading.wide_at`, `Reading.byLeaf_at`; for every reading, what is read does not
change where what stands at the leaves does not: `Reading.at_congr`, `Reading.at_stable`,
`Reading.at_before`, `Reading.at_ann`, `Reading.at_single`.

Not claimed. No reading but the sibling's own is given; `byLeaf` is a form, and no `keep` is given.
A reading is worth what its test is worth (see `Reading`). A reading is given the leaves at all
numbers, also those from the string's length on, and may hang on them. Nothing on strings of a byte
format.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Compile.Batch.Sound
import OnBytes.TypedOracleCompiler.Compile.Batch.Local
import OnBytes.TypedOracleCompiler.Compile.Batch.GlueTools

set_option autoImplicit false

namespace TypedOracleCompiler.Slice
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- A way of reading the external string off what a trace determines at the leaves under a root.
Nothing ties `of` to the leaves where `keeps` fails: with a test that never holds, every function is
a reading, a constant one too; the third clause of `PlainAt` (OnBytes/TypedOracleCompiler/Slice/PlainClause.lean)
then speaks only of accepted strings without external openings, and of a string that need have
nothing to do with the trace. Nothing is asked of `embE`: where it writes one body for two symbols,
the law lets `keeps` hold of at most one of them at a position and salt. What a clause at R is worth
is what R is worth. -/
structure Reading (L : BatchProtocolWithLeafBody I X) (embE : L.Symbol → L.Bd) where
  /-- the string, from what stands at each leaf (nothing where the trace determines nothing) -/
  of : (ℕ → Option (LeafIn L)) → Fin L.wordLength → L.Symbol
  /-- the test on position, symbol and salt -/
  keeps : Fin L.wordLength → L.Symbol → Bits → Prop
  /-- at a leaf whose body is `embE` of a kept symbol the string has that symbol -/
  law : ∀ f p a sl, f p.val = some ⟨embE a, sl⟩ → keeps p a sl → of f p = a

/-- The string that R reads off the trace under the root cm, in a tree of the wiring's depth for L's
string. -/
def Reading.at {embE : L.Symbol → L.Bd} (R : Reading L embE) (W : QueryLayout lam L) (tr : Tc W)
    (cm : Dig lam) : Fin L.wordLength → L.Symbol :=
  R.of fun j => extLeaf tr W.depth cm j

/-- The sibling's own reading: what the wire's `prjE` reads from the body at a leaf is kept,
whatever the salt. It is built with the external part of the wiring of L's Batch. That part's three
laws are asked (`W.B.ext.OK`); one is used: a string built from symbols has these symbols. Asked
besides: `prjE` reads back what `embE` writes. -/
def Reading.wide {W : QueryLayout lam L} (h : W.B.ext.OK) (hE : ∀ s, W.prjE (W.embE s) = some s) :
    Reading L W.embE where
  of := fun f => W.B.ext.build fun q => (f q.val).bind fun z => W.prjE z.body
  keeps := fun _ _ _ => True
  law := fun f p a _ hf _ => h.build_rd _ p a (by rw [hf]; exact hE a)

/-- The sibling's own reading gives the sibling's `extEnc`. -/
theorem Reading.wide_at {W : QueryLayout lam L} (h : W.B.ext.OK)
    (hE : ∀ s, W.prjE (W.embE s) = some s) (tr : Tc W) (cm : Dig lam) :
    (Reading.wide h hE).at W tr cm = extEnc W tr cm :=
  rfl

/-- The reading that has at position p what `keep p` makes of the leaf p, and what the wiring's
`build` puts there where the trace determines no leaf or `keep` gives nothing. `keep` is free: it
may make a symbol of a body that `embE` writes for no symbol, or another symbol than the one that
the body was written for. The test `keeps` holds exactly where it gives back the symbol from the
body that `embE` writes for it. The same law of Batch's wiring is used as in `Reading.wide`. -/
def Reading.byLeaf {W : QueryLayout lam L} (h : W.B.ext.OK) (embE : L.Symbol → L.Bd)
    (keep : ℕ → LeafIn L → Option L.Symbol) : Reading L embE where
  of := fun f => W.B.ext.build fun q => (f q.val).bind (keep q.val)
  keeps := fun p a sl => keep p.val ⟨embE a, sl⟩ = some a
  law := fun f p a sl hf hk => h.build_rd _ p a (by rw [hf]; exact hk)

/-- What a reading by leaves reads. -/
theorem Reading.byLeaf_at {W : QueryLayout lam L} (h : W.B.ext.OK) (embE : L.Symbol → L.Bd)
    (keep : ℕ → LeafIn L → Option L.Symbol) (tr : Tc W) (cm : Dig lam) :
    (Reading.byLeaf h embE keep).at W tr cm =
      W.B.ext.build fun q => (extLeaf tr W.depth cm q.val).bind (keep q.val) :=
  rfl

section
variable {embE : L.Symbol → L.Bd} (R : Reading L embE) {W : QueryLayout lam L}

/-- Two traces that determine the same at every leaf under the root are read alike. -/
theorem Reading.at_congr {tr tr' : Tc W} {cm : Dig lam}
    (h : ∀ j, extLeaf tr W.depth cm j = extLeaf tr' W.depth cm j) :
    R.at W tr cm = R.at W tr' cm := by
  show R.of _ = R.of _
  congr 1
  funext j
  exact h j

/-- Outside a clash in a hash tree, what is read under a root that occurs in a beginning of the
trace is the same there and at the end. -/
theorem Reading.at_stable {tr' tr : Tc W} {cm : Dig lam} (h : ¬ EM tr) (hp : tr' <+: tr)
    (ho : (evM lam W.K L).OccursIn tr' cm) : R.at W tr' cm = R.at W tr cm :=
  R.at_congr fun j => extLeaf_stable h hp ho _ j

/-- Outside a clash in a hash tree, what is read under a root that occurs before a challenge query,
or at it, is the same before that query and at the end. -/
theorem Reading.at_before {tr pre post : Tc W} {t : Tag} {q : FbIn lam L t} {a : FsAns lam W.K}
    (htr : tr = pre ++ fbE t q a :: post) (hM : ¬ EM tr) {cm : Dig lam}
    (hc : (evM lam W.K L).OccursIn (pre ++ [fbE t q a]) cm) : R.at W pre cm = R.at W tr cm :=
  R.at_congr fun j => extLeaf_before htr hM hc _ j

/-- An entry of the oracle `ann` at the end of a trace changes nothing in what is read. -/
theorem Reading.at_ann (tr : Tc W) (c : Dig lam) (u : Unit) (cm : Dig lam) :
    R.at W (tr ++ [annE W c u]) cm = R.at W tr cm :=
  R.at_congr fun j => extLeaf_ann tr c u _ cm j

/-- What is read hangs only on the entries at oracles whose answer is one block, if the leaf and the
node oracle are such. -/
theorem Reading.at_single (m : OracleCoding (typedOracleFamily lam W.K L) lam) (hl : m.blocks OracleName.leaf = 1)
    (hn : m.blocks OracleName.node = 1) (tr : Tc W) (cm : Dig lam) :
    R.at W (single m tr) cm = R.at W tr cm :=
  R.at_congr fun j => extLeaf_single m hl hn tr _ cm j

end

end TypedOracleCompiler.Slice
