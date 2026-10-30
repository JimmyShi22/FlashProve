-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P2LawR/SampleBehindOk.lean: THE EARNING OF sampleAtB (Johnson/P2LawR/SampleBehind.lean) WITH
THE SEEDS' READING STRUCK: in its place one fact on the drawn words: every seed's factor is spelt by
canonical words. One theorem. A joining.

Why. `sampleAtB_behind` asks joint seeds ρ that the round's draw reads as (`K1.ReadsAs`). Whoever
holds an accepting step of a sending sub-protocol has no ρ in hand. There are such ρ where the
factors' words are canonical and no factor is spelt by three words 0 (`K1.reads_exists`,
Johnson/Desc/K1/Law/Sound.lean); the second is a clause of the decision's own accept
(`K1.decideSend_iff`, Johnson/Desc/K1/Law/Writes3.lean).

  `sampleAtB_behind_ok`: hC · hfit · hyes as in `sampleAtB_behind` · hok : every factor in
    `K1.seedsOf P r₁` passes `okE` · k · hk · `SampleStep` ⊢ the test accepts in the state behind.

Limits. hfit (the two rounds fit the sending's list of rounds) and hok STAY: neither is drawn here
from the decision's accept. (By reading, the decision takes the seeds as they are cut off whatever
was drawn; no example in Lean shows an accept at which the conclusion fails.)
`SampleStep` is a premise. No example. Nothing on soundness.
-/
import Johnson.P2LawR.SampleBehind
import Johnson.Desc.K1.Law.Sound

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P2Law
open Cb Cb.Ood OnBytes OnBytes.Slice Johnson.Pack
open VerifiableInference.Desc
open ToldDesc (sampleAtB)

/-- **The earning, from an accept at rounds that fit and factors whose words are canonical.** -/
theorem sampleAtB_behind_ok {L : Type} (P : K1.Par) (rad : Nat → Nat) (owed : Option Nat)
    (d d' : _root_.Desc.Plain.DState L) (r₁ r₂ : Fmt.RoundView) (ids : Array Nat)
    (hC : K1.condPort P rad = true) (hfit : roundsFit (K1.rounds P) [r₁, r₂] = true)
    (hyes : K1.decideSend P owed d [r₁, r₂] = .ok (ids, d'))
    (hok : ∀ s ∈ K1.seedsOf P r₁, okE s.2 = true) (k : Fin (K1.shapesOf P).length)
    (hk : K1.sampledAt P k)
    (hL : SampleStep P.codes (K1.shapeAt P k) (d.st.oracles.size + k.val)) :
    sampleAtB P.codes (K1.shapeAt P k) d'.st (d.st.oracles.size + k.val) = true := by
  obtain ⟨⟨_, _, hnz, _, _⟩, _, _⟩ := (K1.decideSend_iff P owed d d' r₁ r₂ ids).1 hyes
  obtain ⟨ρ, hρ⟩ := K1.reads_exists P r₁ hok hnz
  exact sampleAtB_behind P rad owed d d' r₁ r₂ ids hC hfit hyes ρ hρ k hk hL

end P2Law
