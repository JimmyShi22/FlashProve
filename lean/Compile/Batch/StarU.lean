-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/StarU.lean: the compiled scheme whose prover makes no query and builds no tree for an
empty slot. Definitions only. (Words of this library: lean/GLOSSARY.md.)

`PpJU`, `PpU`, `PU`: the prover `PpJ`, `Pp`, `P` of Compile/Batch/Star.lean with `proveBU`
(Compile/Batch/ProverU.lean) in place of `proveB`. `argBU`: the scheme (C, `PU`, V) with C and V of
Compile/Batch/Star.lean. Keys, proofs and their types are those of `argB`. What changes: the header
of Compile/Batch/ProverU.lean. Test and Link, which C runs, have one slot, which is full: C does not
change.

Limits: nothing is proved here.
-/
import Compile.Batch.ProverU
import Compile.Batch.Star

noncomputable section

namespace Compile.Batch
open Iop Rom

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}
variable (W : QueryLayout lam L) (WP : WireBP L) (p : Params)

/-- the batch, once the copy j and the placement σ are sampled -/
def PpJU (k : IskH lam L) (fr : ℕ → Bool) (xs : List X) (j : ℕ) (σ : Equiv.Perm (Fin L.maxBatchSize)) :
    St lam W.K L (List (Prf lam L)) :=
  match k.leaves[j]? with
  | none => pure (xs.map fun _ => ⟨j, default, none, none⟩)
  | some lf =>
      (proveBU p.sMT p.sFS Tag.onl L.onlineBatch L.honestOnlineBatchProver W.B WP.B
          (fun q a => some (.inr ⟨Tag.onl, ⟨q, a⟩⟩)) id some W.depthReq [lf.node.tree]
          (k.i, lf.node.r) (slotFlags σ fr) (slotsOfReq σ xs)).bind fun πs =>
      pure ((List.range xs.length).map fun a =>
        ⟨j, lf.node.tree.root, lf.piL, if h : a < L.maxBatchSize then πs.getD (σ ⟨a, h⟩).val none else none⟩)

/-- the prover, as a token program (`Step`, Rom/Defer.lean): a uniform copy, a sampled placement
(uniform if `WP.perm` has `Enum.OK`, Iop/Wire.lean), one execution of Batch -/
def PpU (k : IskH lam L) (fr : ℕ → Bool) (xs : List X) : St lam W.K L (List (Prf lam L)) :=
  Step.sample p.M fun j => (drawT WP.perm).bind fun σ => PpJU W WP p k fr xs j.val σ

/-- the oracle algorithm that `erase` makes of the prover's program -/
def PtokU (k : ISK lam L) (b : List (X × Unit)) : TypedOracleComputation lam W.K L (ZKCP.Gen.Slots (Prf lam L) b) :=
  (erase (PpU W WP p k.1 (fun _ => true) (b.map Prod.fst)) k.2).bind fun o =>
    pure (fitLen ⟨0, default, none, none⟩ b.length o.1)
/-- the prover: `PtokU` with every query to a ghost name `fbw t k` turned into the query to the
Fiat-Shamir oracle `fb t` (`realQ`, Compile/Batch/Oracles.lean), as P of Compile/Batch/Star.lean;
`PtokU` itself is not an algorithm of the scheme -/
def PU (k : ISK lam L) (b : List (X × Unit)) : TypedOracleComputation lam W.K L (ZKCP.Gen.Slots (Prf lam L) b) :=
  realQ (PtokU W WP p k b)

/-- The compiled scheme without queries for empty slots. -/
def argBU : ZKCP.Gen.Arg (spec lam W.K L) I X Unit (IVK lam L) (ISK lam L) (Prf lam L) where
  C := C W WP p
  P := PU W WP p
  V := V W p

end Compile.Batch
