-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/HasRowAtPubAll.lean: K01_law, row
P.hasRow at the composed function of all layers' tests with code (`pubAll`,
Johnson/Desc/First/PubAll.lean). Two statements with their proofs.

  `pubAll_hasRow`: at the item hasRow m the composed function is the test `hasRow` at the plan's
    numbers `D.d1`: by the make.
  `pub_hasRow_later`: true in front of an accept of a sub-protocol (our files: a block) with
    `KeepsRow`, so true behind. Members: a later moment's sub-protocol;
    the reads' place's joined one.

Limits. As in HasRowAtLater.lean. K01_law is not proved by this. Nothing on soundness.

-/
import Johnson.Desc.K1.Law.HasRowAtLater
import Johnson.Desc.First.PubAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open VerifiableInference.Desc.First (S Pub PubData pubAll)
open Johnson.Desc.First.Walk.Law (hasRow)

variable {Cl Pp : Type}

/-- At the item hasRow m the composed function is the test on the pending row. -/
theorem pubAll_hasRow (D : PubData) (base : Pub → Pp × S → Bool) (m : Nat) (a : Pp × S) :
    pubAll D base (.hasRow m) a = hasRow D.d1.lay (D.d1.ncl m) D.d1.lin a.2 := rfl

/-- **hasRow m at the composed function**: true in front of a yes of B, so true behind. -/
theorem pub_hasRow_later {B : Block S Cl} (hB : KeepsRow B) (D : PubData)
    (base : Pub → Pp × S → Bool) (m : Nat) (x x' : Pp × S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : B.decide x.2 rs gs = .ok x'.2)
    (h0 : pubAll D base (.hasRow m) x = true) : pubAll D base (.hasRow m) x' = true := by
  rw [pubAll_hasRow] at h0 ⊢
  exact hasRow_of_alike (hB _ _ _ _ h) h0

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.pubAll_hasRow
#print axioms VerifiableInference.Desc.K1.pub_hasRow_later
