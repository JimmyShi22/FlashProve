-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P2LawR/SampleBehind.lean: THE EARNING OF sampleAtB: behind an accept of a sending's decision
the test `ToldDesc.sampleAtB` (Johnson/ToldDescR/RcLastCode.lean) accepts each new sampled message,
at the sending's codes and the list of rounds' shape. One definition, two theorems. Joinings.

Why. `sampleTwoB`, a conjunct of the test on the first chain's last state that the last table
spends, asks `sampleAtB` of two messages. It is kept along the chain
(Johnson/ToldDescR/SmpWalk.lean); here it is earned where a message is sent.

  `SampleStep cs sh o`: THE LAST STEP, AS A NAMED PREMISE: whatever message is sampled, and has as
    its one sample row `Send.form`'s row at a seed that is long enough and whose factor reads as a
    unit of the field, passes `H2K.Pin.sampleL` at the seat ⟨o, sh, 0, 0, default, 0⟩. It reads no
    state: a fact on cs and sh. (At a shape with rows of one kind:
    Johnson/Desc/K12/Law/SampleOfSeed.lean's `sampleL_of_seed`, under four tests on cs and sh.)
  `sampleAtB_of_seedIs`: `K1.SeedIs cs sh St o ρ y`, `K1.Tie cs sh` and `SampleStep cs sh o` give
    `sampleAtB cs sh St o = true`, at any statement St. By `seed_of_seedIs`
    (Johnson/Desc/Sound/SeedAtSeam.lean).
  `sampleAtB_behind`: under the premises of `K1.seedIs_behind` (Johnson/Desc/K1/Law/SeedIs.lean),
    sign for sign, and `SampleStep` at the new message's number: the test accepts in the state
    behind.

Limits. `SampleStep` is a premise. That the seeds read (`ReadsAs`) is a premise. One answer a
message. No example. Nothing on soundness.
-/
import Johnson.Desc.Sound.SeedAtSeam
import Johnson.Desc.K1.Law.SeedIs
import Johnson.ToldDescR.ThreeAtW

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P2Law
open Cb Cb.Ood OnBytes OnBytes.Slice Johnson.Pack
open VerifiableInference.Desc
open H2K.First (Seat1 ok)
open H2K.Pin (sampleL)
open ToldDesc (sampleAtB)

/-- **The last step**: a sampled message whose one sample row is the program's row at a seed passes
the test on a member's sample. -/
def SampleStep (cs : Codes) (sh : OracleShape) (o : Nat) : Prop :=
  ∀ (x : OnBytes.Oracle) (seed : SampleSeed) (row0 : OnBytes.Row) (tt : E) (β : GEˣ),
    x.sampled = true → Send.form cs sh o seed 0 = some row0 →
    x.sampleRows.toList = [{ row0 with target := tt }] → bitsZ cs sh ≤ seed.z.length →
    (β : GE) = readE seed.beta → ok (sampleL cs ⟨o, sh, 0, 0, default, 0⟩ x) = true

/-- **From the sendings' invariant to the test's accept**, at any statement. -/
theorem sampleAtB_of_seedIs {cs : Codes} {sh : OracleShape} {St : Statement} {o : Nat}
    {ρ : (Fin (bitsZ cs sh) → GE) × GEˣ} {y : GE} (hT : K1.Tie cs sh)
    (h : K1.SeedIs cs sh St o ρ y) (hL : SampleStep cs sh o) : sampleAtB cs sh St o = true := by
  obtain ⟨x, seed, row0, tt, hx, hsh, hs, hf, hr, hl, hb, _, _⟩ :=
    _root_.Desc.K14.Law.Fence.seed_of_seedIs hT h
  unfold sampleAtB
  rw [hx]
  simp only [hsh, decide_true, Bool.true_and]
  exact hL x seed row0 tt ρ.2 hs hf hr hl hb

/-- **Behind an accept of the sending's decision the test accepts each new sampled message.** -/
theorem sampleAtB_behind {L : Type} (P : K1.Par) (rad : Nat → Nat) (owed : Option Nat)
    (d d' : _root_.Desc.Plain.DState L) (r₁ r₂ : Fmt.RoundView) (ids : Array Nat)
    (hC : K1.condPort P rad = true) (hfit : roundsFit (K1.rounds P) [r₁, r₂] = true)
    (hyes : K1.decideSend P owed d [r₁, r₂] = .ok (ids, d')) (ρ : K1.Seeds P)
    (hρ : K1.ReadsAs P r₁ ρ) (k : Fin (K1.shapesOf P).length) (hk : K1.sampledAt P k)
    (hL : SampleStep P.codes (K1.shapeAt P k) (d.st.oracles.size + k.val)) :
    sampleAtB P.codes (K1.shapeAt P k) d'.st (d.st.oracles.size + k.val) = true := by
  obtain ⟨y, h⟩ := K1.seedIs_behind P rad owed d d' r₁ r₂ ids hC hfit hyes ρ hρ k hk
  exact sampleAtB_of_seedIs (K1.cond_tie P rad hC k hk) h hL

end P2Law
