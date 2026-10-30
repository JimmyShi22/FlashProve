-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
The premises are not shown to be satisfiable here: no run is in this file.
Johnson/Desc/First/Look/K3AsksDoorLaw.lean: WHAT A YES OF EACH OF THE LOOKUPS' THREE ENTRY TESTS
(Johnson/Desc/First/Look/K3AsksDoor.lean) GIVES: the premises on public data that the lookups' laws
name, at the public plan Z. Statements and proofs. Ties of texts: no error term. NO SOUNDNESS IS
CLAIMED. It stands outside what a verifier runs.

OBJECT: the three functions of K3AsksDoor.lean.
USER: Johnson/HB/LLHARD/Q38E/DigAtHead.lean (digEntry_gives).
LETTERS: Z free.
Compiled with the whole library.


Main names:
  `digEntry_is`, `readsEntry_is`, `headEntry_is`: each test IS its row at Z.p.X (and sentOf Z): by
    rfl.
  `digEntry_gives`, `readsEntry_gives`, `headEntry_gives`: DigOK at every link; readsB at every
    attention link; HeadOK at the output head.

Limits. One way.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3AsksDoor
import Johnson.Desc.First.Look.K3AsksLaw
import Johnson.Desc.First.Look.K3AsksHeadLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3Asks
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Look (lookAt tlAt)
open VerifiableInference.Desc.Kinds.Head.Law (sizesOf HeadOK)

theorem digEntry_is (Z : ProofFile.Pub) : digEntry Z = digRow Z.p.X (sentOf Z) := rfl

theorem readsEntry_is (Z : ProofFile.Pub) : readsEntry Z = readsRow Z.p.X (sentOf Z) := rfl

theorem headEntry_is (Z : ProofFile.Pub) : headEntry Z = headRow Z.p.X := rfl

/-- **THE TEST ON THE DIGITS.** -/
theorem digEntry_gives {Z : ProofFile.Pub} (h : digEntry Z = true) :
    ∀ rad : OracleShape → Nat, ∀ i < linksOf Z.p.X,
      ∃ x tl, First.Look.digAt Z.p.X i = some (x, tl) ∧
        First.Look.DigOK (Params.settingOf Z.p.X.P.frame) x tl (sentOf Z).up rad Cb.Gl.p :=
  fun rad => asks_dig h rad

/-- **THE TEST ON THE GUARDS OF THE READING.** -/
theorem readsEntry_gives {Z : ProofFile.Pub} (h : readsEntry Z = true) :
    ∀ rad : OracleShape → Nat, ∀ i ∈ attLinks Z.p.X,
      ∃ x tl, lookAt Z.p.X i false = some x ∧ tlAt Z.p.X i = some tl ∧
        First.Look.readsB x tl (sentOf Z).up rad = true :=
  fun rad => asks_reads h rad

/-- **THE TEST ON THE OUTPUT HEAD's CALLS.** -/
theorem headEntry_gives {Z : ProofFile.Pub} (h : headEntry Z = true) :
    ∃ x, Kinds.Head.Law.headAt Z.p.X = some x ∧
      @Kinds.Head.Law.headB (sizesOf Z.p.X.hS) (Head.keyFloor Z.p.X.hS) x.fs = true ∧
      @HeadOK (sizesOf Z.p.X.hS) (Params.settingOf Z.p.X.P.frame) x (Head.keyFloor Z.p.X.hS) :=
  asks_head h

end VerifiableInference.Desc.K3Asks

#print axioms VerifiableInference.Desc.K3Asks.digEntry_gives
#print axioms VerifiableInference.Desc.K3Asks.readsEntry_gives
#print axioms VerifiableInference.Desc.K3Asks.headEntry_gives
