-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/Port7.lean: the kind's joined law in the library's own terms, general in the
decision; the kind's own decision meets it; a decision that says yes to all and one that says no to
all fail it.

Main names: CommitSoundPort, commitSoundPort; yesAll_fails_port, noAll_fails_port.

What is not claimed. The law is of a sending whose answers come in a round of their own, right
behind the round of its seeds: where a plan lets a sending's answers ride in a round of another
kind, it is not this text that runs. The form reads the statement alone: what the decision writes
into the book of trees is in WritesLaw (Tries.lean), what a row says in says_iff and says_port. The
words are the messages' tables with 0 beyond the real rows and places (tabOf). The two silly
decisions fail at the form's first half; a copy that lays no row fails at the last clause
(PortTries2.lean [not in this library]). One answer a message.
The radii and the words sent are arguments; that a message
is in the list of the word sent is a premise. From a hash's blocks to seeds: not here. Nothing on an
honest prover or on hiding.
-/
import Johnson.Desc.K1.Law.Port6

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open OnBytes.Slice Johnson.Pack Cb Cb.Ood Prob

/-- **The joined law's form, in the library's terms.** On what a yes hangs; and under the one
Boolean on the plan and the radii, for all words sent: there is a set of bad seeds, within the
stated number, that hangs on the words alone, such that behind a yes at rounds that fit, whose drawn
seeds read as joint seeds that are not bad: what stood in the statement stands; and for each sampled
message and any two messages of its word's list: the message is marked, and if the tables of both
meet all rows laid on it they are one message. -/
def CommitSoundPort (dec : Dec) : Prop :=
  WhenLaw dec ∧
  ∀ (P : Par) (rad : Nat → Nat), condPort P rad = true →
    ∀ f : ∀ k, (portOmZ P.codes (shapeAt P k) (rad k.val)).Str,
    ∃ bad : Seeds P → Prop, cnt bad ≤ errPort P rad ∧
      ∀ (L : Type) (owed : Option Nat) (d d' : DState L) (r₁ r₂ : Fmt.RoundView) (ids : Array Nat)
        (ρ : Seeds P), roundsFit (rounds P) [r₁, r₂] = true →
        dec L P owed d [r₁, r₂] = .ok (ids, d') → ReadsAs P r₁ ρ → ¬ bad ρ →
        Kept d d' ∧ ∀ k, sampledAt P k → ∀ (w w' : Means.Words GE)
          (msg msg' : (portCode P.codes (shapeAt P k)).J → GE),
          w (d.st.oracles.size + k.val) = tabOf P.codes (shapeAt P k) msg →
          w' (d.st.oracles.size + k.val) = tabOf P.codes (shapeAt P k) msg' →
          (portOmZ P.codes (shapeAt P k) (rad k.val)).InList (f k) msg →
          (portOmZ P.codes (shapeAt P k) (rad k.val)).InList (f k) msg' →
          ∃ x, d'.st.oracles[d.st.oracles.size + k.val]? = some x ∧ x.sampled = true ∧
            (Means.AllSay rdE d'.st x.sampleRows.toList w →
              Means.AllSay rdE d'.st x.sampleRows.toList w' → msg = msg')

/-- **The kind's own decision meets it.** -/
theorem commitSoundPort : CommitSoundPort fun _ => decideSend := by
  refine ⟨whenLaw, fun P rad hC f => ⟨BadPort P rad f, badPort_count P rad hC f, ?_⟩⟩
  intro L owed d d' r₁ r₂ ids ρ hfit hyes hρ hgood
  refine ⟨?_, fun k hk w w' msg msg' hw hw' hl hl' =>
    unique_behind_port P rad f owed d d' r₁ r₂ ids hC hfit hyes ρ hρ hgood k hk w w' msg msg' hw hw'
      hl hl'⟩
  obtain ⟨_, _, rfl⟩ := (decideSend_iff P owed d d' r₁ r₂ ids).1 hyes
  exact kept_behind P d _ _

theorem yesAll_fails_port : ¬ CommitSoundPort yesAll := fun h => yesAll_fails_when h.1
theorem noAll_fails_port : ¬ CommitSoundPort noAll := fun h => noAll_fails_when h.1

end VerifiableInference.Desc.K1
