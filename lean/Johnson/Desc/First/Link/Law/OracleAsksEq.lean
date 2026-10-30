-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/OracleAsksEq.lean: `OracleAsks` (OracleRides.lean) OVER AN ACCEPTING
STEP OF THE ONE EQUATION's SUB-PROTOCOL (our files call a sub-protocol a block), which turns the
statement: from the table's own test on its numbers (`fenceFit`), the piece's first tree, and two
sentences on the two parameters: the committed table's decoder reads nothing of the verifier's
state; the OOD samples' reader reads of it no more than the statement's codes and, of each oracle
message, its shape, its mark «sampled» and its stored sample rows, and the book of the oracle
messages' places. A theorem; FenceAt.lean's `oracleAsks_of` for the fourth sub-protocol.

What is said.
  `oracleAsks_eq`: **`OracleAsks cs decT smp Nm links pl z k base s s'` at an accepting step from s
    to s' of a block each of whose accepting steps is the one equation's.**

Limits. The two sentences are on parameters that are letters in the composed meaning: shown here of
no term. `fenceFit`'s yes and
«the plan's count of trees at the place is no more than the piece's first tree» are premises.
Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.FenceAt
import Johnson.Desc.First.Link.Law.DoorBlind
import Johnson.Desc.First.Link.Law.EqLays

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open Johnson.Pack (sigOf)
open VerifiableInference.Desc.K9 (atS Where)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Numbers fenceFit)

variable {P Cells : Type} (cs : OnBytes.Codes)
  (decT : (ℕ → Option (ℕ × List UInt64)) → P × S → Option Cells)
  (smp : P × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)

/-- **OracleAsks over the one equation's accepting step.** -/
theorem oracleAsks_eq {Cl : Type} (Nm : Numbers) (links : List ModelPart) (pl : List Place) (z : P)
    (k base : ℕ) (h : fenceFit Nm links pl = true) (hk : k ≤ pl.length)
    (hb : Nm.treesAt pl[k]? ≤ base) (hd : ∀ c (s s' : S), decT c (z, s') = decT c (z, s))
    (hs : ∀ s s' : S, SameBy tri s.st s'.st → s'.book = s.book → smp (z, s') = smp (z, s))
    (pw : Where)
    (b₃ : Block S Cl)
    (hb₃ : ∀ ft s rs cols x, b₃.step ft s rs cols = .ok x →
      (K9.oneEquation (Cl := Cl) atS pw).step ft s rs cols = .ok x)
    (ft : ℕ) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : S) (j : ℕ)
    (hstep : b₃.step ft s rs cols = .ok (s', j)) :
    OracleAsks cs decT smp Nm links pl z k base s s' := by
  obtain ⟨_, _, e, _⟩ := eq_both pw b₃ hb₃ tri_blind ft s rs cols s' j hstep
  obtain ⟨_, _, _, _, _, El⟩ := eq_lays pw b₃ hb₃ ft s rs cols s' j hstep
  exact ⟨fence_of_fit Nm links pl h k base hk hb, fun c => hd c s s', hs s s' e El.book⟩

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.oracleAsks_eq
