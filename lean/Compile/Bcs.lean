-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  Compile/Bcs.lean: what the compiled prover keeps of a Merkle tree (`TreeH`), an opened position
  (`Opening`), and the strict format at external oracles (`strictExt`). The compiled prover and
  verifier: Compile/Batch/Prover.lean, Compile/Batch/Verifier.lean (words of this library:
  lean/GLOSSARY.md).
-/
import Compile.Oracles
import Compile.MerkleM

noncomputable section

namespace Compile
open Iop Rom

variable {I X : Type} {lam K : ℕ}

/-! ## Trees, on the prover's side -/

/-- what the prover keeps of one tree: all levels of digests, and for each leaf its salt token with
the (empty) tail token -/
structure TreeH (lam : ℕ) where
  levels : List (List (Dig lam))
  salts : List (Option (Tok × Tok))

def TreeH.root {lam : ℕ} (t : TreeH lam) : Dig lam := rootOf t.levels

/-- an opened position: symbol, salt, sibling digests -/
structure Opening (lam : ℕ) (σ : Type) where
  sym : σ
  salt : Bits
  path : List (Dig lam)

/-! ## The strict format -/

/-- every opening at a position of the list we.all is at a position that is read, and its salt has
exactly sMT bits -/
def strictExt (sMT : ℕ) {E : ExtSpec} (we : WireE E) (isRead : E.Pos → Bool)
    (g : E.Pos → Option (Opening lam E.Sym)) : Bool :=
  we.all.all fun p => match g p with
    | none => true
    | some op => isRead p && decide (op.salt.length = sMT)

end Compile
