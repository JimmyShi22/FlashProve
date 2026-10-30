-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/FenceAt.lean: THE FIRST OF THE THREE PREMISES OF `OracleAsks`
(OracleRides.lean: every tenant whose pin is open sits in a commitment tree below the piece's first
tree) FROM THE TABLE's OWN TEST ON ITS NUMBERS (`fenceFit`, Johnson/Desc/First/FenceFit.lean) AND
«the piece's first tree is no lower than the plan's count of trees at its place». And the other two
where the two parameters read of the verifier's state the statement and the book alone. Theorems.

What is said.
  `fence_of_fit`: the fence. `oracleAsks_of`: **`OracleAsks` at two states that stand in `Rb`**,
    from `fenceFit`'s yes, the piece's first tree, and «the committed table's decoder and the OOD
    samples' reader are functions of the public part, the statement and the book».

Limits. `fenceFit`'s yes at the numbers that are made of a plan is the table's files'. That the two
parameters read no more is a sentence on parameters that are letters in the composed meaning: shown
of no term. At the one equation's sub-protocol, which turns the statement, `oracleAsks_of` does not
serve. Nothing on soundness.

-/
import Johnson.Desc.First.FenceFit
import Johnson.Desc.First.Link.Law.OracleRides

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open Johnson.Pack (sigOf)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Numbers start openSets sampledIn fenceFit fenceFit_at)

/-- The fence, from the table's own test. -/
theorem fence_of_fit (Nm : Numbers) (links : List ModelPart) (pl : List Place)
    (h : fenceFit Nm links pl = true) (k base : ℕ) (hk : k ≤ pl.length)
    (hb : Nm.treesAt pl[k]? ≤ base) :
    ∀ x ∈ sampledIn Nm ((openSets links pl (start links))[k]?.getD []), x.1 < base :=
  fun x hx => Nat.lt_of_lt_of_le (fenceFit_at Nm links pl h k hk x hx) hb

variable {P Cells : Type} (cs : OnBytes.Codes)
  (decT : (ℕ → Option (ℕ × List UInt64)) → P × S → Option Cells)
  (smp : P × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)

/-- **OracleAsks at two states that stand in Rb.** -/
theorem oracleAsks_of (Nm : Numbers) (links : List ModelPart) (pl : List Place) (z : P) (k base : ℕ)
    (h : fenceFit Nm links pl = true) (hk : k ≤ pl.length) (hb : Nm.treesAt pl[k]? ≤ base)
    (hd : ∀ c (s s' : S), s'.st = s.st → s'.book = s.book → decT c (z, s') = decT c (z, s))
    (hs : ∀ s s' : S, s'.st = s.st → s'.book = s.book → smp (z, s') = smp (z, s))
    (s s' : S) (R : Rb s s') : OracleAsks cs decT smp Nm links pl z k base s s' :=
  ⟨fence_of_fit Nm links pl h k base hk hb, fun c => hd c s s' R.st R.book, hs s s' R.st R.book⟩

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.fence_of_fit
#print axioms VerifiableInference.Desc.LinkJoin.oracleAsks_of
