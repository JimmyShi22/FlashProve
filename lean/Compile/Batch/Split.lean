-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/Split.lean: which part of an oracle answer of the compiled scheme is secret until
release (`Rom.Split`, Rom/Defer.lean, for `Compile.Batch.spec`). (Words of this library:
lean/GLOSSARY.md.)

The chaining value of a Fiat-Shamir answer, the slot value, which is the whole answer of g, and the
digests of a request tree enter later queries. So in a Fiat-Shamir answer the hash blocks are
visible, the chaining value a token; an answer of g or of a leaf or node oracle is a token as a
whole. A program that needs such a digest as a string reveals the token at once; this releases
nothing.

Notation: `Rom.Split S`: its fields: `Vis o`: a type; `tl o`: a natural number; `split o`: an
equivalence `S.Rng o ≃ Vis o × (Fin (tl o) → Bool)` (Rom/Defer.lean); `visOf`, `tlOf`: the fields
`Vis` and `tl` of `split lam K L`; `lam`, `K`: natural numbers: digests have `lam` bits; an answer
of `fb t` is K hash blocks and a chaining value (the head of Compile/Batch/Oracles.lean); `L`: an
`BatchProtocol I X`: the record of protocols (Test, Link, Batch; Iop/Batch.lean); token, reveal, release:
`Tok`, `Step.reveal`, `releaseAll`: the rules in the head of Rom/Defer.lean; `g t`, `rleaf`,
`rnode`: the oracle of the slot value in the joining round; the oracles of the request tree, a
Merkle tree over the slots of one batch (the head of Compile/Batch/Oracles.lean).
-/
import Compile.Batch.Oracles
noncomputable section -- Lean tags what it cannot compile

namespace Compile.Batch
open Iop Rom

variable {I X : Type}

def visOf (lam K : ℕ) : OracleName → Type
  | .leaf => Unit
  | .node => Unit
  | .rleaf => Unit
  | .rnode => Unit
  | .fb _ => Fin K → Dig lam
  | .fbw _ _ => Fin K → Dig lam
  | .g _ => Unit
  | .ann => Unit
  | .other => Dig lam

def tlOf (lam : ℕ) : OracleName → ℕ
  | .leaf => lam
  | .node => lam
  | .rleaf => lam
  | .rnode => lam
  | .fb _ => lam
  | .fbw _ _ => lam
  | .g _ => lam
  | .ann => 0
  | .other => 0

def split (lam K : ℕ) (L : BatchProtocol I X) : Split (spec lam K L) where
  Vis := visOf lam K
  tl := tlOf lam
  split := fun o => match o with
    | .leaf => (Equiv.punitProd (Dig lam)).symm
    | .node => (Equiv.punitProd (Dig lam)).symm
    | .rleaf => (Equiv.punitProd (Dig lam)).symm
    | .rnode => (Equiv.punitProd (Dig lam)).symm
    | .fb _ => Equiv.refl _
    | .fbw _ _ => Equiv.refl _
    | .g _ => (Equiv.punitProd (Dig lam)).symm
    | .ann => (Equiv.prodUnique Unit (Fin 0 → Bool)).symm
    | .other => (Equiv.prodUnique (Dig lam) (Fin 0 → Bool)).symm

end Compile.Batch
