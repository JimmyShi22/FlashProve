-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Lane5SoundLedger.lean

At the library's own relaxed relation with the cost ledger: a request that is built from a prompt
and output tokens and has a witness of that relation meets its policy; at the policy of exact match
its output tokens are the integer model's.

WHAT THIS WEIGHS. The two statements are the library's own: its step from that relation to "true
under the policy" ("Policy.ledger_forces") and two lemmas of its front. The named hypotheses of
Lane5Holes.lean are cut out of the relation and glued again on the way; they do no work here. That a
protocol's accepted proofs have witnesses of this relation holds the whole meaning, and this file's
two theorems do not speak of it. Of the protocol at public files Z it is shown in this form: in
scope, where the files are read and protocolDataWellFormed says yes, the protocol is knowledge sound as an IOP, for
every value of the object's honest provers, at relationAtFiles Z, each round's error at most 2^-128
of all that round's challenges, the bits of proof of work among them (soundAsIOPAtFiles,
E2E/SoundAsIOPAtFilesProofs.lean); relationAtFiles Z unfolds, by definitions, to: the matrix is in
range and holds an index at which some trace meets this relation, at the protocol's prime and the
files' table and policy. The limits in the head of E2E/SoundAsIOPAtFiles.lean hold: among them, the
relation is a relaxed one, at the files' policy, some policies in scope forbid little (at some,
every well-formed request meets the policy at the all-zero weights), and no bound on a prover's
probability is stated there.

The relation "Policy.LedgerRel.Rno" at the protocol's prime says of a witness: r < e; every cell is
an integer below 2^18 in absolute value; every identity of the model with the ledger's head is 0
modulo the prime and every key is an entry of its table.

Main theorems:
* "sound_ledger": at a lawful table of scales, valid settings that are the table's, and a policy
  with "Policy.PolCond": for every index, prompt, output, padding and request: if "requestOfTokens"
  builds the request and some witness meets the relation, "Policy.MeetsPolicy" holds of prompt and
  output at the weights that the index holds.
* "sound_ledger_exact": at a lawful table and "AcceptancePolicy.exact": then, for every position of the output,
  "IntegerModel.nextToken" on the prompt followed by the output before that position is the
  output's token there.

Not claimed by this file's theorems: that any protocol's verifier accepts only requests with a
witness of this relation (what is shown elsewhere: WHAT THIS WEIGHS). A lawful table of scales is a
premise. The library proves its reference table lawful ("lawful_sRef",
Cm/Rel2Guards.lean). That the words of a scale file give a lawful table is shown at named inputs —
the written words (lawful_kit, FormsKeysLaw.lean), the verifier's entry where publicOf returns under
PublicAt (lawful_of_at, Lane5TopPub.lean), a table a reader has tested (lawful_of_read, Scope.lean;
lawful_scalesOf, OfIndex.lean), the files' and the settings' own (lawful_ppAtFiles,
Flat/PolicyAtFrame.lean; lawful_ppBack, ToTensors.lean) — and at no arbitrary parameter file. The
index ranges over "Cm.Idx", the well-formed tables of weights alone. All is at the reference sizes.

-/
import Johnson.Road.Lane5Sound
import Johnson.Road.Lane5HolesMet

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open Inst.Model
open VerifiableInference

/-- **Sound, at the relaxed relation with the cost ledger.** This is said under the hypotheses that
stand in the statement itself, which this comment does not list; it is no claim that they hold. -/
theorem sound_ledger {scales : Cm.Scales} (lawful : scales.Lawful)
    {settings : IntegerTransformer.Settings} (valid : settingsAreValid settings = true)
    (tie : settingsOf scales = settings) {pol : AcceptancePolicy} (hpol : Policy.PolCond pol) :
    ∀ (i : Cm.Idx) (x' : List Token × List Token) (a : List Token) (x : Instance ppref),
      requestOfTokens x' a = some x →
        (∃ w, Policy.LedgerRel.Rno Cb.Gl.p (Policy.ppOf scales pol) i x w) →
          Policy.MeetsPolicy settings pol (weightsOfIndex valid i) x'.1 x'.2 :=
  sound_of_holes lawful valid tie hpol (holes_met_read scales pol)

/-- **Sound at exact match, at the relaxed relation with the cost ledger.** This is said under the
hypotheses that stand in the statement itself, which this comment does not list; it is no claim that
they hold. -/
theorem sound_ledger_exact {scales : Cm.Scales} (lawful : scales.Lawful) :
    ∀ (i : Cm.Idx) (x' : List Token × List Token) (a : List Token) (x : Instance ppref),
      requestOfTokens x' a = some x →
        (∃ w, Policy.LedgerRel.Rno Cb.Gl.p (Policy.ppOf scales AcceptancePolicy.exact) i x w) →
          ∀ position (h : position < x'.2.length),
            IntegerModel.nextToken scales i.index (x'.1 ++ x'.2.take position) =
              some x'.2[position] :=
  sound_of_holes_exact lawful (holes_met_read scales AcceptancePolicy.exact)

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.sound_ledger
#print axioms OnBytes.Road.L5.sound_ledger_exact
