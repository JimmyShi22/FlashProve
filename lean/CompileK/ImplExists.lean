-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/ImplExists.lean: the typed oracles of the compiler can be made from one oracle as soon as
their points are countable.

Definitions, one statement (`Compile.Batch.Spec.exists_impl`) and its proof. A tool for guards
against empty theorems. A point is an oracle, a query to it and the number of a block of the answer
(`Pts`, Compile/Batch/ImplOf.lean).

Why: the theorems over one random oracle (CompileK/Main.lean and what is built on it) speak of
every implementation m : OracleCoding (spec lam K L) lam of the family of typed oracles whose leaf and node
oracles (`OracleName.leaf`, `OracleName.node`) have one block. Compile/Batch/ImplOf.lean builds one from two
injective codes with parsers (`StrCode`, Rom/Hotel.lean), of the points of the real oracles and of
the ghost names.

Main names:
  `StrCode.ofCountable`: every countable type has such a code, by choice: a number for each element,
    written in unary; the parser is classical.
  `implAny lam K L`: the implementation from these two codes, if both types of points are countable.
  `Spec.exists_impl`: under the same two hypotheses its leaf and node oracles have one block: so
    the theorems' quantifier "for every m with one-block leaf and node oracles" does not run over
    the empty set.

Limits: this file does not say that the points are countable: two hypotheses (instances), to be met
at the interface in hand (finite or countable positions, alphabets, plain parts and instances). The
code is no proposal for a program: nothing can be computed with it.

Terms: lean/GLOSSARY.md.
-/
import Compile.Batch.ImplOf

set_option autoImplicit false

noncomputable section

namespace Rom

open Classical in
/-- Every countable type has an injective code with a parser. -/
def StrCode.ofCountable (A : Type) [Countable A] : StrCode A where
  put := fun a => List.replicate ((exists_injective_nat A).choose a) true
  parse := fun s =>
    if h : ∃ a,
      List.replicate ((exists_injective_nat A).choose a) true = s then some h.choose else none
  parse_put := fun a => by
    have h : ∃ a', List.replicate ((exists_injective_nat A).choose a') true =
        List.replicate ((exists_injective_nat A).choose a) true := ⟨a, rfl⟩
    rw [dif_pos h]
    have h2 := congrArg List.length h.choose_spec
    rw [List.length_replicate, List.length_replicate] at h2
    exact congrArg some ((exists_injective_nat A).choose_spec h2)
  put_parse := fun s a hs => by
    by_cases h : ∃ a, List.replicate ((exists_injective_nat A).choose a) true = s
    · rw [dif_pos h] at hs
      cases hs
      exact h.choose_spec
    · rw [dif_neg h] at hs
      cases hs

end Rom

namespace Compile.Batch
open Iop Rom

variable {I X : Type}

/-- An implementation over one oracle, by choice. -/
def implAny (lam K : ℕ) (L : BatchProtocol I X) [Countable (RealPts lam K L)] [Countable (GhostPts lam K L)] :
    OracleCoding (spec lam K L) lam :=
  implOf lam K L (StrCode.ofCountable _) (StrCode.ofCountable _)

namespace Spec

def exists_impl : Prop :=
  ∀ (I X : Type) (lam K : ℕ) (L : BatchProtocol I X)
      [Countable (RealPts lam K L)] [Countable (GhostPts lam K L)],
    (implAny lam K L).blocks OracleName.leaf = 1 ∧ (implAny lam K L).blocks OracleName.node = 1

end Spec

theorem exists_impl : Spec.exists_impl := fun _ _ _ _ _ _ _ => ⟨rfl, rfl⟩

end Compile.Batch
