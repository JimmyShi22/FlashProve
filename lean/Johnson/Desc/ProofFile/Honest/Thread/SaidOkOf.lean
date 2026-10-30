-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/SaidOkOf.lean: THE LETTERS OF THE THREADS GIVE `SaidOk`. Each
kind's law at `lettersHead` takes a letter with `Said → SaidOk`. Here is that premise, once for each
letter.

  `saidOk_of_field`, `saidOk_of_walk`, `saidOk_of_fieldAnd`, `saidOk_of_walkAnd`

What these are. Lemmas on our own definitions, by the letters' first clause. None is one of the
library's goals, and they prove nothing about soundness, completeness, hiding or any other property
of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.ClauseNext

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (OpenedColumn)

variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)
  {B : Coins Bk → Mid W X → List OpenedColumn → Prop} {m₀ : Coins Bk → Mid W X}
  {C : Nat → Coins Bk → Mid W X → Prop}

theorem saidOk_of_field (b : Nat) (k : Coins Bk) (m : Mid W X) (h : SaidField T B b k m) :
    SaidOk b k m := h.1

theorem saidOk_of_walk (b : Nat) (k : Coins Bk) (m : Mid W X) (h : SaidWalk T B m₀ b k m) :
    SaidOk b k m := h.1.1

theorem saidOk_of_fieldAnd (b : Nat) (k : Coins Bk) (m : Mid W X)
    (h : SaidFieldAnd T B C b k m) : SaidOk b k m := h.1.1

theorem saidOk_of_walkAnd (b : Nat) (k : Coins Bk) (m : Mid W X)
    (h : SaidWalkAnd T B m₀ C b k m) : SaidOk b k m := h.1.1.1

end ProofFile.Honest

#print axioms ProofFile.Honest.saidOk_of_field
#print axioms ProofFile.Honest.saidOk_of_walk
#print axioms ProofFile.Honest.saidOk_of_fieldAnd
#print axioms ProofFile.Honest.saidOk_of_walkAnd
