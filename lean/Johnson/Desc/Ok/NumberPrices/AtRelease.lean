-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Ok/NumberPrices/AtRelease.lean: the one part of `PricesNamed`
(Johnson/Goal/Numbers/NumberPricesAt.lean [not in this library]) that speaks of public files, with
the three files as
letters, in a file of its own, so that it can be taken and evaluated alone.

WHERE THINGS STAND. No file under this folder imports a file under Ladder/: where the three public
files occur they are the letters pol, lay, KL; where a bound on a round's error occurs it is a
literal. `PricesAtRelease`, `PricesAtGap`, `PricesRungs`, `pricesRungs`, `PricesNamed`,
`pricesNamed_of`, `prices_at_release`, `below_step`, `pricedAt_of_release`, wherever a head under
this folder names them, stand in Johnson/Goal/Numbers/NumberPricesAt.lean [not in this library].

THE THEOREMS HERE ARE TOOLS. No line under Owed/ [not in this library] is to be laid on them.

Definitions, and two theorems. NO STATEMENT AT NAMED FILES IS PROVED HERE OR ELSEWHERE.
  `PricesAt pol lay KL`, of three public files pol lay KL. There are m, DK, DP such that, clause by
    clause:
    (1) the planner makes m of the three files: madeOf pol lay KL = .ok m;
    (2) the public test on the plan's prices says yes: Desc.madeOk m.p.chains.made = true;
    (3) the public test on the format's words says yes: Desc.fitOk m.p.chains.made = true;
    (4) the data of the key file's rounds are made: dataKAt m = .ok DK;
    (5) the data of the proof file's rounds are made: dataPAt m = .ok DP;
    (6), (7) neither are the data of three empty lists: DK.ds₃ ≠ [], DP.ds₃ ≠ [].
  `PricesAtRelease`, `PricesAtGap` (Johnson/Goal/Numbers/NumberPricesAt.lean [not in this library]):
    `PricesAt` at the
    stored full-size files, and at the same files with the other named policy.
  `pricesAtOk pol lay KL`: the seven clauses as ONE test with code.
  `ne_nil_of_not_isEmpty`: a tool.
  `pricesAt_of_ok`: if that test says yes, PricesAt pol lay KL holds. So an evaluation of
    `pricesAtOk` at the stored full-size files to true inside Lean's kernel would prove
    `PricesAtRelease`; a compiled run that prints true is evidence and no proof. `pricesAtOk` RAN
    true, compiled, at both named sets of files: evidence at ONE value of c, the format's own
    digest, and no proof. `pricesOwnOk` was run by nobody.

Why (6) and (7). Where the makers' tests (`okAt`, OnBytes/Maker/Files.lean) say no, `dataKAt` and
`dataPAt` do not refuse: they return the data of three empty lists, of which every law on rounds
holds idly. Where they say yes the third list has a round (`someFit`, same file).

What of OnBytes/Model/ is used. The statements bear `madeOf`, `dataKAt`, `dataPAt`
(Johnson/G/RoundsOfPlan.lean) and `m.p.chains.made`: `m.p` is a `Model.Verify.Planned`
(OnBytes/Model/Verify.lean), `.chains` a `Model.Verify.Chains` (OnBytes/Model/VerifyChains.lean).
The routine that is CALLED: `madeOf` calls `Model.Verify.planned` (OnBytes/Model/Verify.lean), whose
first step is `publicOf` (OnBytes/Model/VerifyPublic.lean), and `sendsOf` (Johnson/G/Sends.lean),
which calls `planned` once more. All of it is a function of the public files alone: the making of
the plans. As the Limits of Johnson/G/RoundsOfPlan.lean say under "The hash": two hashes are called
on that road, both as concrete functions: the format's hash, for the digest of the three files, and,
in `publicOf`, the second hash function, which hashes the public tables and refuses if a digest is
not the one in the parameter file's lines. So whether clause (1) returns a value can hang on an
answer of the second hash function. Through Johnson/G/RoundsOfPlan.lean 59 files under
OnBytes/Model/ are reached, by a walk of the import lines not held against the library that ships.

A yes at two sets of files serves these two sets. At the other public files in scope of the goals
nothing here gives any of the seven clauses: there a description has to ASK them.

Limits. THIS SPEAKS OF THE PLAN AT THE FORMAT's OWN DIGEST OF THE THREE FILES. A verifier that asks
a hash function drawn at random for the files' digest plans at whatever digest that function gives.
The seven clauses, with the library's test on the lengths of the parameter bytes beside them, hold
at every digest of 32 bytes if they hold at the format's own: `pricesAt_every_digest`, and with one
set of data and records for all: `pricedAt_one` (Johnson/Desc/Ok/NumberPrices/AtDigest.lean), whose
own limits stand there. THE TEST TO RUN FOR THAT IS `pricesOwnOk` (same file), which has that test
on the lengths in it, not `pricesAtOk`. It names no description of the protocol and no written round
of one. What follows from it: `prices_at` (Johnson/Desc/Ok/NumberPrices/Proved.lean),
`pricedAt_of_pricesAt` (Johnson/Desc/Ok/NumberPrices/AtData.lean); at the named files:
Johnson/Goal/Numbers/NumberPricesAt.lean [not in this library]. Nothing on soundness.


-/
import Johnson.Desc.MadeOk
import Johnson.Desc.FitOk
import Johnson.G.RoundsOfPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Number
open Johnson.G.OfPlan

/-- At three public files: the plan is made; the two public tests say yes of it; the data of the key
file's and of the proof file's rounds are made of it, and are not those of three empty lists. -/
def PricesAt (pol lay KL : ByteArray) : Prop :=
  ∃ m DK DP, madeOf pol lay KL = .ok m ∧
    Desc.madeOk m.p.chains.made = true ∧ Desc.fitOk m.p.chains.made = true ∧
    dataKAt m = .ok DK ∧ dataPAt m = .ok DP ∧ DK.ds₃ ≠ [] ∧ DP.ds₃ ≠ []

/-- The seven clauses of `PricesAt` as one test, with code. -/
def pricesAtOk (pol lay KL : ByteArray) : Bool :=
  match madeOf pol lay KL with
  | .ok m =>
    Desc.madeOk m.p.chains.made && Desc.fitOk m.p.chains.made &&
      match dataKAt m, dataPAt m with
      | .ok DK, .ok DP => !DK.ds₃.isEmpty && !DP.ds₃.isEmpty
      | _, _ => false
  | .error _ => false

/-- A list of which `isEmpty` says no is not the empty list. -/
theorem ne_nil_of_not_isEmpty {α : Type} {l : List α} (h : (!l.isEmpty) = true) : l ≠ [] := by
  rintro rfl
  cases h

/-- A yes of the test gives the statement. -/
theorem pricesAt_of_ok {pol lay KL : ByteArray} (h : pricesAtOk pol lay KL = true) : PricesAt pol
    lay KL := by
  unfold pricesAtOk at h
  split at h
  · rename_i m hm
    have c1 := Bool.and_eq_true_iff.1 h
    have c2 := Bool.and_eq_true_iff.1 c1.1
    have h3 := c1.2
    split at h3
    · rename_i DK DP hK hP
      have c3 := Bool.and_eq_true_iff.1 h3
      exact ⟨m, DK, DP, hm, c2.1, c2.2, hK, hP, ne_nil_of_not_isEmpty c3.1,
        ne_nil_of_not_isEmpty c3.2⟩
    · cases h3
  · cases h

end VerifiableInference.Number

#print axioms VerifiableInference.Number.ne_nil_of_not_isEmpty
#print axioms VerifiableInference.Number.pricesAt_of_ok
