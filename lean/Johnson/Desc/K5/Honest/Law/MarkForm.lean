-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/MarkForm.lean: THE TEST `speaks`
(Johnson/Desc/K5/Honest/Law/MarkTest.lean) IN THE FORM IN WHICH A COUNT OVER A MEMBER's LISTED
ROUNDS TAKES A TEST, AND WHAT THE LISTED ROUNDS DRAW. No state, no chain, no prover in it.

Why. The count of the draws at which an event on challenges happens is not this file's work. It
takes: a test on one round's challenge; a list of rounds; that the whole speaks only where a walk
over ALL the member's challenges, from number 0, meets a listed round at which that test says yes;
and, of each listed round, the list of its draws.

Main names:
  `anyBad`: that walk. ITS TEXT IS NOT THIS FILE's OWN: it is the definition of the same name in the
    work on the measure of the smallness test's kind, copied to the letter. THEY ARE TWO CONSTANTS:
    that they are equal is a short induction on the list, OWED in whichever file first imports both;
    the other definition's file is imported by nothing here.
  `anyBad_of_at`: the walk says yes where a listed round that is there is bad.
  `speaks_anyBad`: **where `speaks` says yes, the walk does**, at the test `bad01` and the list
    `readRounds`.
  `read_draws`: **a listed round's draws: one element, which may be 0, and no matrix entry**, at
    every kind of round but two. `read_kind`: the kind that the round's name has is neither.
  `read_logN`: the entry's word on positions is 0.

Limits. No count and no probability. What is said of a round is said of the entry as
`read_round` (Johnson/Desc/K5/Honest/Law/ReadEntries.lean) has it; how a declared round becomes the
data over which a measure is taken is not spoken of.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.MarkTest
import Johnson.Desc.K5.Honest.Law.ReadEntries

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.First.Att.P (Geo)

/-- The walk over a member's challenges from number j on: at some round that mk lists, bad says yes.
On where its text comes from: see the head. -/
def anyBad (bad : Fmt.Drawn → Bool) (mk : ℕ → Bool) : ℕ → List Fmt.Drawn → Bool
  | _, [] => false
  | j, x :: l => (mk j && bad x) || anyBad bad mk (j + 1) l

/-- The walk says yes where a listed round that is there is bad. -/
theorem anyBad_of_at (bad : Fmt.Drawn → Bool) (mk : ℕ → Bool) :
    ∀ (own : List Fmt.Drawn) (j n : ℕ) (dr : Fmt.Drawn), own[n]? = some dr → mk (j + n) = true →
      bad dr = true → anyBad bad mk j own = true
  | [], _, _, _, h, _, _ => nomatch h
  | x :: l, j, 0, dr, h, hm, hb => by
    obtain rfl : x = dr := Option.some.inj h
    show ((mk j && bad x) || anyBad bad mk (j + 1) l) = true
    rw [show mk j = true from hm, hb]
    rfl
  | x :: l, j, n + 1, dr, h, hm, hb => by
    show ((mk j && bad x) || anyBad bad mk (j + 1) l) = true
    rw [anyBad_of_at bad mk l (j + 1) n dr h (by rw [← hm]; congr 1; omega) hb, Bool.or_true]

/-- **WHERE THE WHOLE SPEAKS, THE WALK OVER ALL THE MEMBER's CHALLENGES SAYS YES**, at the test on
one round and the list of rounds. No premise beside the yes. -/
theorem speaks_anyBad {x : OnBytes.Params.AttentionRounds} {g : Geo} {own : List Fmt.Drawn}
    (h : speaks x g own = true) :
    anyBad bad01 (fun i => decide (i ∈ readRounds x g)) 0 own = true := by
  obtain ⟨n, hn, dr, ho, hb⟩ := speaks_only h
  exact anyBad_of_at _ _ own 0 n dr ho (by rw [Nat.zero_add]; exact decide_eq_true hn) hb

/-- **A listed round's draws**: one element, which may be 0; no position; no matrix entry.
Conditional: the kind is neither that of seeds nor the sealed one. w: the policy's bits of work. -/
theorem read_draws (w : ℕ) {k : Fmt.Kind} (h1 : k ≠ .seeds) (h2 : k ≠ .sealed) :
    Fmt.dsOf { MaskedSum.entry "PSC round" 3 1 0 with work := w } k = [.elem, .trits 0] := by
  unfold Fmt.dsOf Fmt.dsElems
  rw [if_neg h1, if_neg h2]
  rfl

/-- The kind that the round's name has. -/
theorem read_kind : Fmt.kindOf "PSC round" = some .elems := by decide

/-- The entry's word on positions. -/
theorem read_logN (w : ℕ) :
    ({ MaskedSum.entry "PSC round" 3 1 0 with work := w } : Fmt.Entry).logN = 0 := rfl

end H2K5.Honest

#print axioms H2K5.Honest.anyBad_of_at
#print axioms H2K5.Honest.speaks_anyBad
#print axioms H2K5.Honest.read_draws
#print axioms H2K5.Honest.read_kind
#print axioms H2K5.Honest.read_logN
