-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/MarkLive.lean: THE MARK AT THE OWN ROUNDS OF AN ATTENTION
SEGMENT (kind K5) FOR THE SLOTS THAT ITS OWN RUNS MAKE LIVE, AS A TERM OF THE STRUCTURE `Mark`
(Johnson/Desc/ProofFile/Honest/Law/Marks.lean), with what a count takes of it and with what its
silence gives.

The event: at one of the rounds of `liveRounds` (Johnson/Desc/K5/Honest/Law/LiveCount.lean) the one
element drawn is 0 (or its words are not below the prime). The verifier refuses nothing there. Where
it does not happen, the state in front of the segment's batching has `HeldLive`
(Johnson/Desc/K5/Honest/Law/LiveState.lean), under which the laws of that file make each slot of the
segment's own window live in one named run.

Main names:
  `mkLive`: **the mark.** place: the member. test: of the member's own challenges alone; it reads
    neither those in front nor a key point. share: A WRITTEN PAIR OF NUMBERS, NO BOUND: 1 for each
    listed round, over the number of field elements, with the factor that a count at strings of
    hash blocks bears.
  `mkLive_walk`, `mkLive_drop`: it speaks only where the test on one round says yes at a listed
    round, in two forms; the first at this kind's copy of the walk `anyBad`
    (Johnson/Desc/K5/Honest/Law/MarkForm.lean).
  `mkLive_silent`: where it is silent, the list has all listed rounds and `BetaNz` holds, `k5Live`
    says yes.
  `mkLive_held`: **WHAT ITS SILENCE GIVES, AT THE STATE IN FRONT OF THE BATCHING.**

Limits. NO SENTENCE ON A MEASURE STANDS HERE: nothing holds the share against the test. THE FORM OF
THE SHARE IS A GUESS at what a count takes for "the element is 0". `BetaNz`
(Johnson/Desc/K5/Honest/Law/LiveMark.lean) and hlen are premises here; MarksFit.lean beside this
file pays both from the frame's test `drawsFit`. That each listed round's declared entry draws one
element, which may be 0: `live_entry` (Johnson/Desc/K5/Honest/Law/LiveEntries.lean). `mkLive_held`
is conditional as `held_at_batch` (Johnson/Desc/K5/Honest/Law/HeldAtBatch.lean).
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.Law.Marks
import Johnson.Desc.K5.Honest.Law.LiveMark
import Johnson.Desc.K5.Honest.Law.HeldAtBatch

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.First
open H2K5.Honest (liveRounds k5Live speaksL bad0 anyBad speaksL_anyBad speaksL_drop
  k5Live_of_silent BetaNz Chal Reads HeldLive held_at_batch)
open P5J (AtMgA TS)

/-- **The mark.** l: the segment's number in the first chain. x: the plan's numbers of its own
rounds. -/
def mkLive (l : ℕ) (x : OnBytes.Params.AttentionRounds) : Mark where
  place := ⟨1, some l, 3, .K5⟩
  test := fun _ own =>
    if speaksL x own then some "a challenge that a slot's coefficient is made of is 0" else none
  share := ⟨1 * (liveRounds x).length * (2 ^ 128 + 1) ^ 3, Code.pGold ^ 3 * (2 ^ 128) ^ 3⟩

/-- The mark's test speaks just where `speaksL` says yes. -/
theorem mkLive_test (l : ℕ) (x : OnBytes.Params.AttentionRounds) (fr own : List Fmt.Drawn) :
    ((mkLive l x).test fr own).isSome = speaksL x own := by
  show (if speaksL x own then some _ else none : Option String).isSome = _
  cases speaksL x own <;> rfl

/-- **It speaks only where the walk over all the member's challenges meets a listed round at which
the test on one round says yes.** No premise. -/
theorem mkLive_walk (l : ℕ) (x : OnBytes.Params.AttentionRounds) :
    ∀ fr own, ((mkLive l x).test fr own).isSome = true →
      anyBad bad0 (fun i => decide (i ∈ liveRounds x)) 0 own = true := by
  intro fr own h
  rw [mkLive_test] at h
  exact speaksL_anyBad h

/-- The same by the cut of one entry out of the list. No premise. -/
theorem mkLive_drop (l : ℕ) (x : OnBytes.Params.AttentionRounds) :
    ∀ fr own, ((mkLive l x).test fr own).isSome = true →
      ∃ r ∈ liveRounds x, ((own.drop r).take 1).any bad0 = true := by
  intro fr own h
  rw [mkLive_test] at h
  exact speaksL_drop h

/-- Where it is silent, the list has all the listed rounds, and the premise on the second list
holds, the test on the rounds says yes. Conditional: hlen; h; hb. -/
theorem mkLive_silent (l : ℕ) {x : OnBytes.Params.AttentionRounds} (zk : Array (Array E))
    {fr own : List Fmt.Drawn} (hlen : ∀ n ∈ liveRounds x, n < own.length)
    (h : (mkLive l x).test fr own = none) (hb : BetaNz x ⟨zk, own⟩) :
    k5Live x ⟨zk, own⟩ = true := by
  refine k5Live_of_silent zk hlen ?_ hb
  rw [← mkLive_test l x fr own, h]
  rfl

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : Look.Place} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
include h

/-- **WHAT THE MARK's SILENCE GIVES, AT THE STATE IN FRONT OF THE BATCHING.** Conditional: as
`held_at_batch`; own: the challenges of the first's rounds: hc: they hold what these rounds drew;
hlen: all listed rounds are among them; hs: the mark is silent at them, whatever stands in front;
hb: the premise on the rounds of the further variables. -/
theorem mkLive_held {g : ℕ} (hg : g < 12) {a : Attention.Plan}
    (ea : (P5J.At.X Zp).A[g]? = some a) {b4 b5 b6 b7 b8 : Block S ProofFile.Cl}
    (f4 : cF.blocksInOrder[14 * (2 * g + 1) + 4]? = some b4)
    (f5 : cF.blocksInOrder[14 * (2 * g + 1) + 5]? = some b5)
    (f6 : cF.blocksInOrder[14 * (2 * g + 1) + 6]? = some b6)
    (f7 : cF.blocksInOrder[14 * (2 * g + 1) + 7]? = some b7)
    (f8 : cF.blocksInOrder[14 * (2 * g + 1) + 8]? = some b8) {s4 s5 s6 s7 s8 s9 : S}
    {rs4 rs5 rs6 rs7 rs8 : List Fmt.RoundView} {gs4 gs5 gs6 gs7 gs8 : List (List (ℕ × List UInt64))}
    (d4 : b4.decide s4 rs4 gs4 = .ok s5) (d5 : b5.decide s5 rs5 gs5 = .ok s6)
    (d6 : b6.decide s6 rs6 gs6 = .ok s7) (d7 : b7.decide s7 rs7 gs7 = .ok s8)
    (d8 : b8.decide s8 rs8 gs8 = .ok s9) {att : AttOwn} (e4 : s4.here = .att att)
    (hz : OnBytes.Model.Road.Sized att.F) (zk : Array (Array E)) {fr own : List Fmt.Drawn}
    (hc : Reads ⟨zk, own⟩ rs4) (hlen : ∀ n ∈ liveRounds a.own, n < own.length)
    (hs : (mkLive (2 * g + 1) a.own).test fr own = none) (hb : BetaNz a.own ⟨zk, own⟩) :
    HeldLive a.own att.F.next s9 :=
  held_at_batch h hg ea f4 f5 f6 f7 f8 d4 d5 d6 d7 d8 e4 hz ⟨zk, own⟩ hc
    (mkLive_silent (2 * g + 1) zk hlen hs hb)

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.mkLive_test
#print axioms ProofFile.Honest.K5.mkLive_walk
#print axioms ProofFile.Honest.K5.mkLive_drop
#print axioms ProofFile.Honest.K5.mkLive_silent
#print axioms ProofFile.Honest.K5.mkLive_held
