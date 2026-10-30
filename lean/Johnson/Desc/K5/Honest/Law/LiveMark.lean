-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/LiveMark.lean: THE FIRST LIST OF THE TEST `k5Live`
(Johnson/Desc/K5/Honest/Law/LiveCount.lean) AS A TEST THAT SPEAKS ROUND BY ROUND ON A LIST OF DRAWN
CHALLENGES: the list of the own rounds' challenges of an attention segment (kind K5), one entry a
round. No state, no chain, no prover in it.

Why. `k5Live` asks of two lists of rounds that the one element drawn is not 0. At the rounds of the
first (`liveRounds`) the format lets 0 be drawn: there the event "it is 0" has to be counted. At
those of the second (`betaRounds`: the round of a sumcheck's further variable) the entry counts the
element as never 0, and the verifier's general step refuses a 0: no event is to be counted there.
So the test that is counted bears the first list alone, and the second is a premise by name.

Main names:
  `bad0`: **the test on one round's challenge**: the first element that it shows fails `nzE`
    (Johnson/Desc/K5/Honest/Law/Live.lean): a word of it is not below the prime, or it is the
    word 0.
  `speaksL`: **the whole**: at one of the rounds of `liveRounds` that the list has, `bad0` says yes.
  `speaksL_only`, `speaksL_drop`, `speaksL_anyBad`: it speaks only so, in three forms.
  `bad0_elem`: **at a challenge that shows just the field element x: x = 0.**
  `BetaNz`: the premise on the second list.
  `k5Live_of_silent`: **where the whole is silent, the list has all the listed rounds, and
    `BetaNz` holds, `k5Live` says yes.**

How. The text is that of Johnson/Desc/K5/Honest/Law/MarkTest.lean and MarkForm.lean, with the test
on one element and the list of rounds exchanged.

Limits. No count and no probability. `BetaNz` IS SHOWN HERE OF NOTHING. It is meetable: the test
`drawsFit` on a list of challenges at a member's declared rounds
(Johnson/Desc/ProofFile/Honest/Frame.lean) asks both halves of `nzE` at such a round: the general
step's test on "never 0", and that every word of an element is below the prime; it also gives hlen
(`live_len_of_fit`, Johnson/Desc/ProofFile/Honest/K5/Law/MarksFit.lean). The lemma that gives
`BetaNz`: `betaNz_of_fit` (Johnson/Desc/ProofFile/Honest/K5/Law/BetaFit.lean). A list that is too
short for a listed round is passed over in silence: so hlen is asked.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.MarkForm
import Johnson.Desc.K5.Honest.Law.LiveCount

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes (E zeroE okE isZeroE)

/-- **The test on one round's challenge.** -/
def bad0 (dr : Fmt.Drawn) : Bool := !nzE (firstOfDrawn dr)

/-- **The whole**: at one of the listed rounds that the list has, the test on one round says yes. -/
def speaksL (x : OnBytes.Params.AttentionRounds) (own : List Fmt.Drawn) : Bool :=
  (liveRounds x).any fun n => (own[n]?).any bad0

/-- **It speaks only where the test on one round says yes at a listed round that is there.** -/
theorem speaksL_only {x : OnBytes.Params.AttentionRounds} {own : List Fmt.Drawn}
    (h : speaksL x own = true) : ∃ n ∈ liveRounds x, ∃ dr, own[n]? = some dr ∧ bad0 dr = true := by
  unfold speaksL at h
  obtain ⟨n, hn, e⟩ := List.any_eq_true.1 h
  cases ho : own[n]? with
  | none =>
    rw [ho] at e
    cases e
  | some dr =>
    rw [ho] at e
    exact ⟨n, hn, dr, ho, e⟩

/-- The same by the cut of one entry out of the list. -/
theorem speaksL_drop {x : OnBytes.Params.AttentionRounds} {own : List Fmt.Drawn}
    (h : speaksL x own = true) : ∃ r ∈ liveRounds x, ((own.drop r).take 1).any bad0 = true := by
  obtain ⟨n, hn, dr, ho, hb⟩ := speaksL_only h
  refine ⟨n, hn, List.any_eq_true.2 ⟨dr, ?_, hb⟩⟩
  have h0 : ((own.drop n).take 1)[0]? = some dr := by
    rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_zero]
    exact ho
  exact List.mem_of_getElem? h0

/-- The same by the walk over all the member's challenges. -/
theorem speaksL_anyBad {x : OnBytes.Params.AttentionRounds} {own : List Fmt.Drawn}
    (h : speaksL x own = true) :
    anyBad bad0 (fun i => decide (i ∈ liveRounds x)) 0 own = true := by
  obtain ⟨n, hn, dr, ho, hb⟩ := speaksL_only h
  exact anyBad_of_at _ _ own 0 n dr ho (by rw [Nat.zero_add]; exact decide_eq_true hn) hb

/-- **What the test on one round says of a challenge that shows just one field element.**
Conditional: h: the test's yes; he: the challenge shows x, written in words below the prime. -/
theorem bad0_elem {dr : Fmt.Drawn} {x : Cb.Gl.E} (h : bad0 dr = true)
    (he : dr.elems = [OnBytes.Slice.ofE x]) : x = 0 := by
  have e1 : firstOfDrawn dr = OnBytes.Slice.writeE x := by
    unfold firstOfDrawn
    rw [he]
    simp [OnBytes.Slice.writeE]
  unfold bad0 nzE at h
  rw [e1, OnBytes.Slice.okE_writeE] at h
  cases h0 : isZeroE (OnBytes.Slice.writeE x) with
  | true =>
    rw [← OnBytes.Slice.readE_writeE x, (OnBytes.Slice.isZeroE_eq _).1 h0]
    exact OnBytes.Slice.readE_zero
  | false =>
    rw [h0] at h
    cases h

/-- **The premise on the second list**: what the round of each sumcheck's further variable drew
passes the test on one element. -/
def BetaNz (x : OnBytes.Params.AttentionRounds) (c : Chal) : Prop :=
  ∀ n ∈ betaRounds x, nzE (c.one n) = true

/-- **WHERE THE WHOLE IS SILENT, THE LIST HAS ALL THE LISTED ROUNDS, AND THE PREMISE ON THE SECOND
LIST HOLDS, THE TEST `k5Live` SAYS YES**, at the honest side's structure of challenges with that
list, whatever its key points. Conditional: hlen; h; hb. -/
theorem k5Live_of_silent {x : OnBytes.Params.AttentionRounds} (zk : Array (Array E))
    {own : List Fmt.Drawn} (hlen : ∀ n ∈ liveRounds x, n < own.length)
    (h : speaksL x own = false) (hb : BetaNz x ⟨zk, own⟩) : k5Live x ⟨zk, own⟩ = true := by
  unfold k5Live
  refine List.all_eq_true.2 fun n hn => ?_
  rcases List.mem_append.1 hn with hn | hn
  · obtain ⟨dr, ho⟩ : ∃ dr, own[n]? = some dr := ⟨_, List.getElem?_eq_getElem (hlen n hn)⟩
    rw [one_at_own zk ho]
    unfold speaksL at h
    have h1 := List.any_eq_false.1 h n hn
    rw [ho] at h1
    have h2 : bad0 dr = false := by simpa using h1
    unfold bad0 at h2
    simpa using h2
  · exact hb n hn

end H2K5.Honest

#print axioms H2K5.Honest.speaksL_only
#print axioms H2K5.Honest.speaksL_drop
#print axioms H2K5.Honest.speaksL_anyBad
#print axioms H2K5.Honest.bad0_elem
#print axioms H2K5.Honest.k5Live_of_silent
