-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/JoinDraws.lean: a bound on the numbers of hash blocks that the challenge samplers of a list of
rounds read (Iop/Draw.lean). The bound is `Shape.Draws.LeW w m ds`: the first round has at most
w * m blocks, the others at most m. Here w is the number of old rounds for which the first round
already counts (the argument w of `XPlan.maxRunFrom`, Iop/Recut.lean); if the bound holds before a
plan P, then by Iop/RecutDraws.lean no round after P has more than `P.maxRunFrom w * m` blocks.
(Words of this library: lean/GLOSSARY.md.)
  `Shape.Draws.leW_one`   it holds at w = 1 if every round has at most m blocks
Notation: `lam : ℕ`: a hash block is `Dig lam` (Iop/Wire.lean): lam bits; `BS lam C`: a structure
(Iop/Draw.lean): a challenge sampler for the type C: the element of C is φ of b uniform blocks of
lam bits; `d.b : ℕ`: the field `b` of `d : BS lam r.Chal`; `s.Draws lam : Type` (`Shape.Draws`,
there): one sampler for each round; `Shape.Draws.maxB s ds : ℕ` (there): the largest number of
blocks of a round; `P : XPlan s` (Iop/Recut.lean): a plan of splits and merges for the list of
rounds s, the original list; the old rounds are those of s, the new ones those of `P.shape` (there:
the new list of rounds); `P.maxRunFrom w : ℕ` (there): the largest number of old rounds whose errors
are in a new round, if the first round already counts for w old rounds.
Limits: nothing is said on how the blocks are obtained, as in Iop/Draw.lean.
-/
import Iop.BatchJoinProofs
import Iop.BatchWireDrawOK

namespace Iop
open Prob
open scoped ENNReal

variable {lam : ℕ}


/-- the first round has at most w * m blocks, the others at most m -/
def Shape.Draws.LeW (w m : ℕ) : {s : Shape} → s.Draws lam → Prop
  | [], _ => True
  | _ :: s, (d, ds) => d.b ≤ w * m ∧ Shape.Draws.maxB s ds ≤ m

theorem Shape.Draws.leW_one :
    ∀ {s : Shape} (ds : s.Draws lam) {m : ℕ}, Shape.Draws.maxB s ds ≤ m → Shape.Draws.LeW 1 m ds
  | [], _, _, _ => trivial
  | _ :: _, (_, _), _, h =>
    ⟨by rw [Nat.one_mul]; exact (le_max_left _ _).trans h, (le_max_right _ _).trans h⟩


variable {I X : Type} {L : BatchProtocol I X}

variable {dr : L.Draws lam}



end Iop
