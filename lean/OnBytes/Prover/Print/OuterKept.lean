-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Prover/Print/OuterKept.lean: WHAT THE PRINTER ASKS OF AN OUTER TREE "AS ITS COMMITTER HAS
KEPT IT", WHERE THAT TREE IS THE PROVER's OWN BUILDER's (treeO, OnBytes/Prover/Defs.lean) OVER GIVEN
LEAVES: it follows from a condition on the table and on the leaves' salts alone.

Main names.
  TableOwes cfg y sl P   at every place p with P p: the salt of leaf p begins with the
    configuration's digest, is whole bytes behind it and has at most 256 + 8 * 64 bits; the symbol
    at p names p; the column's words are below the prime; the column is shorter than 2^64.
  kept_inp, kept_path    the kept tree's leaves are the given ones; a path has the tree's depth.
  outer_one              the clause "outer" of WholeOwes (OnBytes/Prover/Print/Owed.lean) at one
    table.

Does not show: that a table or its salts meet TableOwes. Nothing on soundness or completeness.
Terms: lean/GLOSSARY.md.

-/
import OnBytes.Prover.Print.Owed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Prover.Print

open _root_.Run _root_.Run.PQ Rom
open _root_.Compile (pathOf)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch
open OnBytes.Maker OnBytes.Maker.Carrier
open OnBytes.Prover

/-- What is asked of a table and its leaves' salts, at the places P. -/
def TableOwes (cfg : ByteArray) {n : ℕ} (y : Fin n → SgX) (sl : ℕ → Bits) (P : Fin n → Prop) :
    Prop :=
  ∀ p, P p → SaltFrom cfg (sl p.val) ∧ (sl p.val).length ≤ 256 + 8 * 64 ∧ (y p).1 = p.val ∧
    (∀ w ∈ (y p).2, Carrier.okF w) ∧ (y p).2.length < 2 ^ 64

section
variable {I X : Type} {K : ℕ} {L : BatchProtocolWithLeafBody I X} (g : Fam (typedOracleFamily 256 K L)) (a : ℕ)
  (inp : ℕ → LeafIn L)

theorem kept_inp : ((treeO (K := K) a inp).det g).inp = inp := (treeO_at g a inp).2

theorem kept_path (j : ℕ) : (pathOf ((treeO (K := K) a inp).det g).lv j).length = a :=
  (treeO_at g a inp).1.length_path j

/-- **The clause "outer" at one table.** -/
theorem outer_one (cfg : ByteArray) (y : Fin (2 ^ a) → SgX) (sl : ℕ → Bits)
    (P : Fin (2 ^ a) → Prop) (hs : ∀ j, (inp j).salt = sl j) (ha : a < 2 ^ 64)
    (h : TableOwes cfg y sl P) (p : Fin (2 ^ a)) (hp : P p) :
    SaltFrom cfg (((treeO (K := K) a inp).det g).inp ((weOne a).leaf p)).salt ∧ (y p).1 = p.val ∧
      CanonO (y p).2 (((treeO (K := K) a inp).det g).inp ((weOne a).leaf p)).salt
        (pathOf ((treeO (K := K) a inp).det g).lv ((weOne a).leaf p)) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h p hp
  rw [kept_inp, hs]
  exact ⟨h1, h3, h4, h5, h2, by rw [kept_path]; exact ha⟩

end

end OnBytes.Prover.Print

#print axioms OnBytes.Prover.Print.TableOwes
#print axioms OnBytes.Prover.Print.kept_inp
#print axioms OnBytes.Prover.Print.kept_path
#print axioms OnBytes.Prover.Print.outer_one
