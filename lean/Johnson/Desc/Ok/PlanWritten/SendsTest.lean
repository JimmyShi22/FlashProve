-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Ok/PlanWritten/SendsTest.lean: tests with code: the lists of sendings of oracle
messages that are made at the public files (the fields `key` and `proof` of `OfPlan.Made`,
Johnson/G/RoundsOfPlan.lean) are the written ones of the full size (`keySendsFull`,
`proofSendsFull`, Johnson/G/SendsWritten.lean), compared whole. Definitions alone.

What it is for. Several tests and laws read these lists: where a sending stands among the
rounds, its label, what is sent with its shapes, the two entries around it, the chain's codes. The
lists are a function of the sizes and of the lists of rounds, but Lean's kernel does not bring that
function's value at the full size to a written form: it would walk 48,391 rounds. So that the lists
are the written ones is asked when the verifier runs; facts on the written lists are then small
enough for the kernel.

Why the comparison is written out. `Sending` and `ChainSends` (Johnson/G/Sends.lean) bear no
decidable equality where they are declared, and a file beneath the verifier's list of tests is to
hold definitions alone, with no instance. Each field's own type bears one where it is declared. That
no field and no sending is left out is a theorem: an accept gives the equation of whole values
(Johnson/Desc/Ok/PlanWritten/SendsTestLaws.lean).

Definitions.
  `sameSending`: five fields: the number of the entry "SEND seed", the label, what is sent, that
    entry, the entry behind it. `sameSends`: two lists, place by place; unequal lengths: reject.
  `sameChain`: the file's name, the chain's number, the codes, the sendings. `sameThree`: a file's
    three chains.
  `proofSendsIs m`, `keySendsIs m`: a file's three lists are the written ones. `sendsIs m`: both.
    BARE: none asks at which size the public files are: at another size than the full one each
    rejects. The caller guards them by the test on the key of the scan of the parameter file.

Limits. `OfPlan.Made` keeps six lists: the list of the copy's file's one chain is made and dropped
(`madeOf`): it is not compared. Nothing on soundness.
-/
import Johnson.G.SendsWritten
import Johnson.G.RoundsOfPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.PlanWritten
open Johnson.G

/-- The five fields of two sendings are the same. -/
def sameSending (a b : Sending) : Bool :=
  decide (a.entry = b.entry) && decide (a.label = b.label) && decide (a.sent = b.sent) &&
    decide (a.seed = b.seed) && decide (a.behind = b.behind)

/-- Two lists of sendings have one length and, place by place, the same sendings. -/
def sameSends : List Sending → List Sending → Bool
  | [], [] => true
  | a :: l, b :: m => sameSending a b && sameSends l m
  | _, _ => false

/-- Two chains' codes and sendings are the same. -/
def sameChain (a b : ChainSends) : Bool :=
  decide (a.file = b.file) && decide (a.chain = b.chain) && decide (a.codes = b.codes) &&
    sameSends a.sends b.sends

/-- So are a file's three chains'. -/
def sameThree (a b : ChainSends × ChainSends × ChainSends) : Bool :=
  sameChain a.1 b.1 && sameChain a.2.1 b.2.1 && sameChain a.2.2 b.2.2

/-- **The proof file's three lists of sendings are the written ones.** -/
def proofSendsIs (m : OfPlan.Made) : Bool := sameThree m.proof proofSendsFull

/-- **The key file's three lists of sendings are the written ones.** -/
def keySendsIs (m : OfPlan.Made) : Bool := sameThree m.key keySendsFull

/-- Both. -/
def sendsIs (m : OfPlan.Made) : Bool := keySendsIs m && proofSendsIs m

end VerifiableInference.PlanWritten
