-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/Reading.lean: ways of reading an external string off what a trace determines at the
leaves under a root.

The library's compiler reads the string under a root in one way (`Compile.Batch.extEnc`): at each
leaf it keeps the symbol that the trace determines there, whatever the salt. The clauses of
BatchClause.lean and of two further files of this project that are not in this library are stated
for any reading
in
the sense of this file: a function of what stands at the leaves, with a test `keeps` on position,
symbol and salt, and the law that at a leaf which holds a kept symbol the string read has that
symbol.

Main definitions: `Reading`, `Reading.at`, `Reading.wide` (the library's own), `Reading.byLeaf`
(leaf by leaf, through a function `keep`).
Main theorems: `Reading.wide_at`, `Reading.byLeaf_at`; for every reading, what is read does not
change where what stands at the leaves does not: `Reading.at_congr`, `Reading.at_stable`,
`Reading.at_before`, `Reading.at_ann`, `Reading.at_single`.

Not claimed. No reading but the library's own is given; `byLeaf` is a form, and no `keep` is given.
A reading is worth what its test is worth (see `Reading`). A reading is given the leaves at all
numbers, also those from the string's length on, and may hang on them. Nothing on strings of a byte
format.

-/
import OnBytes.Slice.LinkClause
import Compile.Batch.Local
import Compile.Batch.GlueTools

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Rom Prob Compile Compile.Batch

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

/-- A way of reading the external string off what a trace determines at the leaves under a root.
Nothing ties `of` to the leaves where `keeps` fails: with a test that never holds, every function is
a reading, a constant one too; the third clause of `PlainAt`, `PairAt` and `BatchAt`
(BatchClause.lean, and two further files of this project that are not in this library) then speaks
only of
accepted
strings without external openings, and of a string that need have nothing to do with the trace. What
a clause at R is worth is what R is worth. -/
structure Reading (L : BatchProtocol I X) where
  /-- the string, from what stands at each leaf (nothing where the trace determines nothing) -/
  of : (ℕ → Option (LeafIn L)) → Fin L.wordLength → L.Symbol
  /-- the test on position, symbol and salt -/
  keeps : Fin L.wordLength → L.Symbol → Bits → Prop
  /-- at a leaf that holds a kept symbol the string has that symbol -/
  law : ∀ f p a sl, f p.val = some ⟨some (.inl a), sl⟩ → keeps p a sl → of f p = a

/-- The string that R reads off the trace under the root cm, in a tree of the wiring's depth for L's
string. -/
def Reading.at (R : Reading L) (W : QueryLayout lam L) (tr : Tc W) (cm : Dig lam) : Fin L.wordLength → L.Symbol :=
  R.of fun j => extLeaf tr W.depth cm j

/-- The library's own reading: every symbol that stands at its leaf is kept, whatever the salt. It
is built with the external part of the wiring of L's Batch. That part's three laws are asked
(`W.B.ext.OK`); one is used: a string built from symbols has these symbols. -/
def Reading.wide {W : QueryLayout lam L} (h : W.B.ext.OK) : Reading L where
  of := fun f => W.B.ext.build fun q => match f q.val with
    | some ⟨some (.inl s), _⟩ => some s
    | _ => none
  keeps := fun _ _ _ => True
  law := fun f p a _ hf _ => h.build_rd _ p a (by simp only [hf])

/-- The library's own reading gives the library's `extEnc`. -/
theorem Reading.wide_at {W : QueryLayout lam L} (h : W.B.ext.OK) (tr : Tc W) (cm : Dig lam) :
    (Reading.wide h).at W tr cm = extEnc W tr cm :=
  rfl

/-- The reading that has at position p what `keep p` makes of the leaf p, and what the wiring's
`build` puts there where the trace determines no leaf or `keep` gives nothing. `keep` is free: it
may make a symbol of a leaf that holds no symbol of the string (a prover's symbol, padding), or
another than the leaf's own. The test `keeps` holds exactly where it gives back the leaf's own
symbol. The same law of Batch's wiring is used as in `Reading.wide`. -/
def Reading.byLeaf {W : QueryLayout lam L} (h : W.B.ext.OK) (keep : ℕ → LeafIn L → Option L.Symbol) :
    Reading L where
  of := fun f => W.B.ext.build fun q => (f q.val).bind (keep q.val)
  keeps := fun p a sl => keep p.val ⟨some (.inl a), sl⟩ = some a
  law := fun f p a sl hf hk => h.build_rd _ p a (by rw [hf]; exact hk)

/-- What a reading by leaves reads. -/
theorem Reading.byLeaf_at {W : QueryLayout lam L} (h : W.B.ext.OK) (keep : ℕ → LeafIn L → Option L.Symbol)
    (tr : Tc W) (cm : Dig lam) :
    (Reading.byLeaf h keep).at W tr cm =
      W.B.ext.build fun q => (extLeaf tr W.depth cm q.val).bind (keep q.val) :=
  rfl

section
variable (R : Reading L) {W : QueryLayout lam L}

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
theorem Reading.at_single (m : OracleCoding (spec lam W.K L) lam) (hl : m.blocks OracleName.leaf = 1)
    (hn : m.blocks OracleName.node = 1) (tr : Tc W) (cm : Dig lam) :
    R.at W (single m tr) cm = R.at W tr cm :=
  R.at_congr fun j => extLeaf_single m hl hn tr _ cm j

end

end OnBytes.Slice
