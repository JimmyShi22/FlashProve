-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/LooksAgree.lean: two implementations over the sibling that spell stored leaves and
vertices alike give two looks that agree.

Why. Two parts of the join read one raw string if their readings are made of the walks of two looks
that agree (`sameRaw_of_walks`, OnBytes/Slice/WalksO.lean): both looks read the same strings as the
same vertices, and, string by string, the same stored symbols. OnBytes/TypedOracleCompiler/Run/PageXJoin.lean says
of two implementations that they SPELL vertices and stored leaves alike (`SameStored`), and shows it
of two encodings (`sameStored_impl`). This file makes the step from the one to the other. Over the
library it is `sameRead_of_stored` (OnBytes/Slice/SameStored.lean), where only a stored symbol's
body is read as a stored symbol, by the bodies' type. Over the sibling a body has a type of the
interface's choosing, and that must be asked: the reading `get` of a body reads back what `e` writes
AND READS NOTHING ELSE (`StoredGet`, both laws).

Main theorem: `looks_of_stored`.

What is not claimed. That any two implementations meet `SameStored`, or any reading `StoredGet`. At
the wire's own `prjE` the second law of `StoredGet` is no law of a wiring: it is owed by whoever
chooses the bodies. Both implementations are over the sibling. For a part of the sibling beside a
part of the library's compiler, as the join's `hKE` and `hEF` ask beside the entry's `flE`, the like
is not written here; for the entry's own part in both compilers: OnBytes/TypedOracleCompiler/Slice/TieLooks.lean,
TieRaw.lean. Nothing on tree shapes, on places or on how a raw string is made of what is found:
`sameRaw_of_walks` asks these beside. No probability. The compiler under OnBytes/TypedOracleCompiler/ is the one
that `innerCompiledVerifier` is made with; it builds on definitions of Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.ByWalks

set_option autoImplicit false

namespace TypedOracleCompiler.Slice
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop MeasureTheory
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open scoped ENNReal
open OnBytes.Slice (PartO Raw rawOf Look inv_iff_code SameRaw sameRaw_of_walks)
open TypedOracleCompiler.Run (OneBlock SameStored StoredGet)

variable {I₁ X₁ I₂ X₂ Sg : Type} {lam K₁ K₂ : ℕ} {L₁ : BatchProtocolWithLeafBody I₁ X₁} {L₂ : BatchProtocolWithLeafBody I₂ X₂}

/-- One half of the second clause of `looks_of_stored`. -/
theorem leaf_of_stored {m₁ : OracleCoding (typedOracleFamily lam K₁ L₁) lam} {m₂ : OracleCoding (typedOracleFamily lam K₂ L₂) lam}
    {e₁ : Sg → L₁.Bd} {e₂ : Sg → L₂.Bd} {get₁ : L₁.Bd → Option Sg} {get₂ : L₂.Bd → Option Sg}
    (h₂ : OneBlock m₂)
    (hst : ∀ (x : Sg) (salt : Bits) j₁ j₂, m₁.code TypedOracleCompiler.Compile.Batch.OracleName.leaf ⟨e₁ x, salt⟩ j₁ =
      m₂.code TypedOracleCompiler.Compile.Batch.OracleName.leaf ⟨e₂ x, salt⟩ j₂)
    (g₁ : StoredGet e₁ get₁) (g₂ : StoredGet e₂ get₂) (s : List Bool) (y : Sg)
    (h : ((lookOf m₁).leaf s).bind (fun q => get₁ q.body) = some y) :
    ((lookOf m₂).leaf s).bind (fun q => get₂ q.body) = some y := by
  obtain ⟨q, hq, hy⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨k, hk⟩ := (inv_iff_code m₁ s TypedOracleCompiler.Compile.Batch.OracleName.leaf q).1 ((lookOf_leaf m₁ s q).1 hq)
  have hb : q = ⟨e₁ y, q.salt⟩ := by
    cases q with
    | mk body salt => exact congrArg (fun b => (⟨b, salt⟩ : LeafIn L₁)) (g₁.e_get body y hy)
  rw [hb] at hk
  have h2 : (lookOf m₂).leaf s = some ⟨e₂ y, q.salt⟩ :=
    (lookOf_leaf m₂ s _).2 ((inv_iff_code m₂ s TypedOracleCompiler.Compile.Batch.OracleName.leaf _).2
      ⟨⟨0, by rw [h₂.leaf1]; omega⟩, hk.trans (hst _ _ _ _)⟩)
  rw [h2]
  exact g₂.get_e y

/-- Two implementations that spell stored leaves and vertices alike give two looks that agree:
both read the same strings as the same vertices, and, string by string, what `get₁` reads from the
body of the first's leaf is what `get₂` reads from the body of the second's. These are the two
hypotheses of `sameRaw_of_walks` at readings that do not look at the place. Asked: one block for a
leaf's and a vertex's answer in both; `SameStored`; both laws of `StoredGet` for both readings. -/
theorem looks_of_stored {m₁ : OracleCoding (typedOracleFamily lam K₁ L₁) lam} {m₂ : OracleCoding (typedOracleFamily lam K₂ L₂) lam}
    {e₁ : Sg → L₁.Bd} {e₂ : Sg → L₂.Bd} {get₁ : L₁.Bd → Option Sg} {get₂ : L₂.Bd → Option Sg}
    (h₁ : OneBlock m₁) (h₂ : OneBlock m₂) (h : SameStored m₁ m₂ e₁ e₂)
    (g₁ : StoredGet e₁ get₁) (g₂ : StoredGet e₂ get₂) :
    (∀ s, (lookOf m₁).node s = (lookOf m₂).node s) ∧
      ∀ s, ((lookOf m₁).leaf s).bind (fun q => get₁ q.body) =
        ((lookOf m₂).leaf s).bind fun q => get₂ q.body := by
  constructor
  · intro s
    refine Option.ext fun x => ?_
    rw [lookOf_node, lookOf_node, inv_iff_code, inv_iff_code]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨⟨0, by rw [h₂.node1]; omega⟩, hk.trans (h.node _ _ _ _)⟩
    · rintro ⟨k, hk⟩
      exact ⟨⟨0, by rw [h₁.node1]; omega⟩, hk.trans (h.node _ _ _ _).symm⟩
  · intro s
    refine Option.ext fun y => ⟨leaf_of_stored h₂ h.stored g₁ g₂ s y,
      leaf_of_stored h₁ (fun x salt j₁ j₂ => (h.stored x salt j₂ j₁).symm) g₂ g₁ s y⟩

end TypedOracleCompiler.Slice
