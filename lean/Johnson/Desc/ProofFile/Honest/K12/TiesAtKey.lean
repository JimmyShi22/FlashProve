-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/TiesAtKey.lean: a test: the equations on a book's entries under
which the two parts' readers agree (`tiesB`, AgreeBook.lean in this folder) hold at the key file's
book of coins (`keyBook`, E2E/KeyBook.lean), at the full size's written sizes, at the three of its
four proximity tests whose first fold's fresh table has come earlier: the test on the ranges, the
one on the folded row, and the own one: by the kernel's own evaluation (`decide +kernel`). One
executable definition, two theorems and three evaluations (`#guard`). Not general: one book, at one
written value of the sizes.

In the list: a book (`ProverCoinCounts`, in the frame, Johnson/Desc/ProofFile/Honest/Frame.lean) is public data.
An entry of it (`Ahead`) is a block of its owner's coins that one other part, its spender, is given
too, marked as spent or as carried. A part (`Part`, the frame) is the prover's side of some rounds
in a row; a proximity test has two (`firstPart`, `restPart`: Parts.lean in this folder), with the
numbers 0 and 1 at the test's place (`Place`: where a sub-protocol is in a description).
`tiesB Bk pl n` returns a `Bool`: it compares the fields `owner`, `start` and `count` of the entries
that the book Bk has for the two parts at the place pl; n is the number of members. A job
(`TestJob`, Test.lean in this folder) is what a caller supplies for its proximity test; its members
(the field `members`) are the oracle messages of the test's group. `jobRanges`, `jobFolded`,
`jobOmega` and `jobOwn` (E2E/KeyTestSizes.lean) are four written jobs; of a job only `p.place` and
`members.length` are read here. `fullPub` (E2E/KeyBookAtWritten.lean) is `KeyPub.of` at the
library's written sizes `keyFull`: an `Option` of the data of which the book is made (`KeyPub`,
E2E/KeyBook.lean). `atFull f` (E2E/KeyBookAtWritten.lean) is `(fullPub.map f).getD false`.

  `full_ties`: `atFull tiesThree = true`: `tiesThree` is true at the book of the written sizes.
    `atFull` is false where `fullPub` is `none`: the theorem is not true for lack of a book
  `ties_ranges`: for every K with `fullPub = some K`: `tiesB` is true at `keyBook K`, at the place
    of `jobRanges` (the test on the ranges) and at its number of members
  `tiesThree K`: a definition: `tiesB (keyBook K)` at the places of `jobRanges`, `jobFolded` and
    `jobOwn`, each at its job's number of members; true where all three are

Negative tests, by Lean's evaluator: at the book without its carried entries `tiesB` is false at all
three; at one member more than the job has it is false at all three; at the fourth place, where the
first fold sends its own table and the first part spends nothing, it is false. In the Lean text the
book without its carried entries is `keyBook K false`, and the fourth place is that of `jobOmega`.

By what. `full_ties` is proved by `decide +kernel`: Lean's kernel evaluates `atFull tiesThree`, and
with it `KeyPub.of` and `keyBook` (E2E/KeyBook.lean), `tiesB` (AgreeBook.lean), and `spentE` and
`carryE` (Johnson/Desc/ProofFile/Honest/Law/Rule/Cell.lean), by which `tiesB` lists a part's
entries. `ties_ranges` unfolds `atFull` in `full_ties`, rewrites by its hypothesis hK and takes the
element `jobRanges` of the list by `List.all_eq_true`.

Limits.
- At written values. `fullPub` is computed at `keyFull`; nothing here says that these are the sizes
  at the public files. The jobs' places and members are written values: see the limits of
  E2E/KeyTestSizes.lean.
- The book's carried entries are a proposal: see the limits of E2E/KeyBook.lean.
- `tiesB` is one of the hypotheses of `agree_of_ties` (AgreeBook.lean): the hypothesis on the job's
  rows (hrows) is not treated here. Nor are the two others: that `lendRow` returns (h), and
  k = h + g at the first stage (hk).
- `ties_ranges` takes from `full_ties` the test on the ranges only. The test on the folded row and
  the own one have no lemma of their own.
- Nothing here ties `jobRanges.p` to `pKR` (Sim/KeyPlaceFacts.lean in this folder).
- A `#guard` is an evaluation by Lean's evaluator, outside the kernel: it leaves no theorem. So
  none of the three negative tests is a theorem.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AgreeBook
import E2E.KeyBookHeldK12

set_option autoImplicit false

namespace ProofFile.Honest.K12
open AtPublicFiles.KeyBook (atFull keyBook fullPub KeyPub)
open AtPublicFiles.KeyTest (jobRanges jobFolded jobOmega jobOwn)

/-- The three places whose fresh table has come earlier. `tiesB` at the book `keyBook K`, at each
job's place and number of members; true where all three are. -/
def tiesThree (K : KeyPub) : Bool :=
  [jobRanges, jobFolded, jobOwn].all fun J => tiesB (keyBook K) J.p.place J.members.length

set_option maxRecDepth 100000 in
theorem full_ties : atFull tiesThree = true := by decide +kernel

/-- **`tiesB` is true at the key file's book, at the written sizes, at the test on the ranges.**
hK: K is what `fullPub` returns. -/
theorem ties_ranges (K : KeyPub) (hK : fullPub = some K) :
    tiesB (keyBook K) jobRanges.p.place jobRanges.members.length = true := by
  have h := full_ties
  unfold atFull at h
  rw [hK] at h
  exact List.all_eq_true.1 h jobRanges (by simp)

-- negative: the book without its carried entries
#guard atFull fun K => [jobRanges, jobFolded, jobOwn].all fun J =>
  !tiesB (keyBook K false) J.p.place J.members.length
-- negative: one member more than the job has
#guard atFull fun K => [jobRanges, jobFolded, jobOwn].all fun J =>
  !tiesB (keyBook K) J.p.place (J.members.length + 1)
-- where the first fold sends its own table the first part spends nothing
#guard atFull fun K => !tiesB (keyBook K) jobOmega.p.place jobOmega.members.length

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.full_ties
#print axioms ProofFile.Honest.K12.ties_ranges
#print axioms ProofFile.Honest.K12.tiesThree
