-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/ByWalks.lean: a part of the sibling's compiler whose reading goes by leaves is
made of the walks of one look.

`Part.toO_byWalks` of OnBytes/Slice/ByWalks.lean and four declarations of OnBytes/Slice/SameAt.lean
said again over the sibling (OnBytes/TypedOracleCompiler/). `Part.toO_byWalks` is that file's text with `Batch.`
written `TypedOracleCompiler.Compile.Batch.`. The four turn, since in the sibling a leaf's body has a type of the
interface's choosing: `keepAll W` keeps what the wire's `prjE` reads from the body;
`Reading.ByLeaves` takes the way of writing as an argument; `Reading.byLeaf_byLeaves` is said at the
wire's `embE`; `Reading.wide_byLeaves` holds by definition. Left out: `Reading.byLeaf_all_at`,
`Reading.at_same_of`, `at_same` (two parts are compared by walks) and the four at descriptions of
the entry.

With it a part of the sibling's compiler can be compared with a part of the library's:
`sameRaw_of_walks` (OnBytes/Slice/WalksO.lean) takes two looks, of whatever compilers, and asks that
they read the same strings as the same vertices and, string by string and place by place, the same
symbols.

What is not claimed. That any two looks agree. The wire's law on `prjE` is one-sided (it reads back
what `embE` writes): `keepAll W` may keep a symbol from a body that `embE` writes for no symbol,
where the library's `keepAll` keeps stored symbols alone. Whoever shows that two looks agree at
`keepAll W` owes the converse (`StoredGet.e_get`, OnBytes/TypedOracleCompiler/Run/PageXJoin.lean). The step from
`SameStored` of that file to the two hypotheses of `sameRaw_of_walks` is made in
OnBytes/TypedOracleCompiler/Slice/LooksAgree.lean, for two implementations over the sibling. What the head of
OnBytes/Slice/ByWalks.lean does not claim. The compiler under OnBytes/TypedOracleCompiler/ is the one that
`innerCompiledVerifier` is made with; it builds on definitions of Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Slice.WalksO
import OnBytes.TypedOracleCompiler.Slice.Part
import OnBytes.TypedOracleCompiler.Slice.SameRead

set_option autoImplicit false

namespace TypedOracleCompiler.Slice
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop MeasureTheory
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open scoped ENNReal
open OnBytes.Slice (PartO Raw rawOf Look)
open TypedOracleCompiler.Run (OneBlock)

section
variable {I X : Type} {lam : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- The reading of a leaf query that keeps what the wire's `prjE` reads from the body, at every
place and whatever the salt. -/
def keepAll (W : QueryLayout lam L) : ℕ → LeafIn L → Option L.Symbol := fun _ q => W.prjE q.body

/-- The reading R goes by leaves: its string is g of what `keep j` makes of the leaf query at
each place j, and of nothing else. -/
structure Reading.ByLeaves {embE : L.Symbol → L.Bd} (R : Reading L embE)
    (keep : ℕ → LeafIn L → Option L.Symbol)
    (g : (ℕ → Option L.Symbol) → Fin L.wordLength → L.Symbol) : Prop where
  /-- the string that R makes of the leaves is g of what `keep` makes of them -/
  of_eq : ∀ f, R.of f = g fun j => (f j).bind (keep j)

/-- `Reading.byLeaf` goes by leaves, with the wiring's way of building a string from symbols. -/
theorem Reading.byLeaf_byLeaves {W : QueryLayout lam L} (h : W.B.ext.OK)
    (keep : ℕ → LeafIn L → Option L.Symbol) :
    (Reading.byLeaf (embE := W.embE) h keep).ByLeaves keep fun φ => W.B.ext.build fun q => φ q.val
        :=
  ⟨fun _ => rfl⟩

/-- The sibling's own reading goes by leaves, at `keepAll W`. -/
theorem Reading.wide_byLeaves {W : QueryLayout lam L} (h : W.B.ext.OK)
    (hE : ∀ s, W.prjE (W.embE s) = some s) :
    (Reading.wide h hE).ByLeaves (keepAll W) fun φ => W.B.ext.build fun q => φ q.val :=
  ⟨fun _ => rfl⟩

end

variable {lam : ℕ} {γ Sg : Type}

/-- A part whose reading goes by leaves is made of walks, at the look
through its implementation, in the perfect tree of its wiring's depth. Asked: one block for a leaf's
and a vertex's answer, taken as it is (`OneBlock`); the reading goes by leaves (`Reading.ByLeaves`).
The symbols are carried to the shared type by the part's match u, and back inside `mk`. -/
theorem Part.toO_byWalks (s : Part lam γ Sg) (h : OneBlock s.m)
    {keep : ℕ → LeafIn s.L → Option s.L.Symbol} {g : (ℕ → Option s.L.Symbol) → Fin s.L.wordLength → s.L.Symbol}
    (B : s.J.R.ByLeaves keep g) :
    s.toO.ByWalks (lookOf s.m) (posOf s.W.depth) (fun j q => (keep j q).map s.u)
      (fun φ => rawOf s.u (g fun j => (φ j).map s.u.symm)) where
  raw_eq := fun σ cm => by
    show rawOf s.u (s.J.R.of fun j => TypedOracleCompiler.Compile.Batch.extLeaf (singleTr s.m σ) s.W.depth cm j) = _
    rw [B.of_eq]
    refine congrArg (fun f => rawOf s.u (g f)) (funext fun j => ?_)
    rw [extLeaf_eq_walk s.m h]
    show ((lookOf s.m).walk σ (posOf s.W.depth j) cm).bind (keep j) =
      (((lookOf s.m).walk σ (posOf s.W.depth j) cm).bind fun q => (keep j q).map s.u).map s.u.symm
    cases (lookOf s.m).walk σ (posOf s.W.depth j) cm with
    | none => rfl
    | some q =>
      show keep j q = ((keep j q).map s.u).map s.u.symm
      rw [Option.map_map, Equiv.symm_comp_self, Option.map_id]
      rfl

end TypedOracleCompiler.Slice
