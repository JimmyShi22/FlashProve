-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/TieLooks.lean: a look through an implementation of the sibling's typed oracles and
a look through one of the library's agree, if the two spell vertices and stored leaves alike. The
compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on
definitions of Compile/.

"The line": the files of OnBytes/Slice/ and OnBytes/Tie/, over the library's compiler. "The
sibling": the files of OnBytes/TypedOracleCompiler/: the library's compiler said again, with a list of roots in a
query and a leaf's body of a type that the interface chooses.

After `looks_of_stored` and `leaf_of_stored` (OnBytes/TypedOracleCompiler/Slice/LooksAgree.lean), which have two
implementations of the sibling's. Here the second is the library's: its leaf's stored symbol is read
by the line's `storedSym`; `storedSym_eq_some` stands for the law `e_get` of `StoredGet`, and
`get_e` holds by definition. The conclusion is the two hypotheses of `sameRaw_of_walks`
(OnBytes/Slice/WalksO.lean), which names no typed family.

TURNED (1). `looks_cross`.

WHAT IS NOT SAID. That any two implementations meet the hypotheses (OnBytes/TypedOracleCompiler/Slice/TieEscape.lean
has them at the two pages of one description). No probability.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.TieEscape
import OnBytes.TypedOracleCompiler.Slice.LooksAgree
import OnBytes.Slice.ByWalks

set_option autoImplicit false

namespace TypedOracleCompiler.Slice
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open OnBytes.Slice (PartO Raw rawOf Look inv_iff_code SameRaw sameRaw_of_walks storedSym
  storedSym_eq_some)
open TypedOracleCompiler.Run (OneBlock StoredGet)

/-! ## Two looks, one through an implementation of each family -/

section
variable {I₁ X₁ I₂ X₂ : Type} {lam K₁ K₂ : ℕ} {L₁ : BatchProtocolWithLeafBody I₁ X₁} {L₂ : _root_.Iop.BatchProtocol I₂ X₂}
  {m₁ : OracleCoding (typedOracleFamily lam K₁ L₁) lam} {m₂ : OracleCoding (_root_.Compile.Batch.spec lam K₂ L₂) lam}
  {e₁ : L₂.Symbol → L₁.Bd} {get₁ : L₁.Bd → Option L₂.Symbol}

/-- An implementation of the sibling's typed oracles and one of the library's that spell stored
leaves and vertices alike give two looks that agree: both read the same strings as the same
vertices; string by string, what `get₁` reads from the body of the first's leaf is the stored
symbol in the second's. Asked: one block for a leaf's and a vertex's answer in both; a vertex query
on two digests has one string in both; a leaf query on a stored symbol has one string in both, for
every symbol and EVERY salt; both laws of `StoredGet` on the sibling's side. -/
theorem looks_cross (h₁ : OneBlock m₁) (h₂ : OnBytes.Slice.OneBlock m₂)
    (hnode : ∀ (a b : Dig lam) j₁ j₂, m₁.code OracleName.node (List.ofFn a, List.ofFn b) j₁ =
      m₂.code _root_.Compile.Batch.OracleName.node (List.ofFn a, List.ofFn b) j₂)
    (hst : ∀ (x : L₂.Symbol) (salt : Bits) j₁ j₂, m₁.code OracleName.leaf ⟨e₁ x, salt⟩ j₁ =
      m₂.code _root_.Compile.Batch.OracleName.leaf ⟨some (.inl x), salt⟩ j₂)
    (g₁ : StoredGet e₁ get₁) :
    (∀ s, (lookOf m₁).node s = (OnBytes.Slice.lookOf m₂).node s) ∧
      ∀ s, ((lookOf m₁).leaf s).bind (fun q => get₁ q.body) =
        ((OnBytes.Slice.lookOf m₂).leaf s).bind storedSym := by
  constructor
  · intro s
    refine Option.ext fun x => ?_
    rw [lookOf_node, OnBytes.Slice.lookOf_node, inv_iff_code, inv_iff_code]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨⟨0, by rw [h₂.node1]; omega⟩, hk.trans (hnode _ _ _ _)⟩
    · rintro ⟨k, hk⟩
      exact ⟨⟨0, by rw [h₁.node1]; omega⟩, hk.trans (hnode _ _ _ _).symm⟩
  · intro s
    refine Option.ext fun y => ⟨fun h => ?_, fun h => ?_⟩
    · obtain ⟨q, hq, hy⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨k, hk⟩ := (inv_iff_code m₁ s OracleName.leaf q).1 ((lookOf_leaf m₁ s q).1 hq)
      have hb : q = ⟨e₁ y, q.salt⟩ := by
        cases q with
        | mk body salt => exact congrArg (fun b => (⟨b, salt⟩ : LeafIn L₁)) (g₁.e_get body y hy)
      rw [hb] at hk
      have h2 : (OnBytes.Slice.lookOf m₂).leaf s = some ⟨some (.inl y), q.salt⟩ :=
        (OnBytes.Slice.lookOf_leaf m₂ s _).2 ((inv_iff_code m₂ s _root_.Compile.Batch.OracleName.leaf _).2
          ⟨⟨0, by rw [h₂.leaf1]; omega⟩, hk.trans (hst _ _ _ _)⟩)
      rw [h2]
      rfl
    · obtain ⟨q, hq, hy⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨k, hk⟩ := (inv_iff_code m₂ s _root_.Compile.Batch.OracleName.leaf q).1
        ((OnBytes.Slice.lookOf_leaf m₂ s q).1 hq)
      rw [(storedSym_eq_some q y).1 hy] at hk
      have h2 : (lookOf m₁).leaf s = some ⟨e₁ y, q.salt⟩ :=
        (lookOf_leaf m₁ s _).2 ((inv_iff_code m₁ s OracleName.leaf _).2
          ⟨⟨0, by rw [h₁.leaf1]; omega⟩, hk.trans (hst _ _ _ _).symm⟩)
      rw [h2]
      exact g₁.get_e y

end

end TypedOracleCompiler.Slice
