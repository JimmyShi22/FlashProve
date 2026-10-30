-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/MarkTest.lean: THE TEST `k5Reads`
(Johnson/Desc/K5/Honest/Law/ReadRounds.lean) AS A TEST THAT SPEAKS ROUND BY ROUND ON A LIST OF DRAWN
CHALLENGES: the list of the own rounds' challenges of an attention segment (kind K5), one entry a
round. No state, no chain, no prover in it.

Why. An event on challenges at which the verifier refuses nothing, and which is to be counted, is
stated as a test on the member's own drawn challenges. Whoever counts it wants: a test `bad` on ONE
round's challenge; a list of rounds; that the whole speaks only where `bad` says yes at a listed
round THAT IS THERE; and what `bad` says of a challenge that shows one field element.

Main names:
  `firstOfDrawn`: the first element that a round's challenge shows; the word 0 if it shows none.
  `bad01`: **the test on one round's challenge**: that element fails `nz01`
    (Johnson/Desc/K5/Honest/Law/EqTabNz.lean): a word of it is not below the prime, or it is the
    word 0, or the word 1.
  `speaks`: **the whole**: at one of the rounds of `readRounds` that the list has, `bad01` says yes.
  `speaks_only`, `speaks_drop`: it speaks only so: by the round's entry; by the cut of one entry.
  `bad01_elem`: **at a challenge that shows just the field element x: x = 0 or x = 1.**
  `reads_of_silent`: **where it is silent, and the list has all the listed rounds, `k5Reads` says
    yes.**

Limits. No count and no probability. A list that is too short for a listed round is passed over in
silence: so `reads_of_silent` asks hlen. That a round's challenge shows just one element is said
by the declared round (`read_round`, Johnson/Desc/K5/Honest/Law/ReadEntries.lean), not here.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.ReadRounds
import OnBytes.Slice.KeyOfRecBack

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes (E zeroE oneE okE isZeroE)
open VerifiableInference.Desc.First.Att.P (Geo)

/-- The first element that a round's challenge shows; the word 0 if it shows none. -/
def firstOfDrawn (dr : Fmt.Drawn) : E := (dr.elems.toArray.map E.ofTriple).getD 0 zeroE

/-- **The test on one round's challenge.** -/
def bad01 (dr : Fmt.Drawn) : Bool := !nz01 (firstOfDrawn dr)

/-- **The whole**: at one of the listed rounds that the list has, the test on one round says yes. -/
def speaks (x : OnBytes.Params.AttentionRounds) (g : Geo) (own : List Fmt.Drawn) : Bool :=
  (readRounds x g).any fun n => (own[n]?).any bad01

/-- What the honest side's structure of challenges reads at a round that the list has. -/
theorem one_at_own (zk : Array (Array E)) {own : List Fmt.Drawn} {n : ℕ} {dr : Fmt.Drawn}
    (h : own[n]? = some dr) : (⟨zk, own⟩ : Chal).one n = firstOfDrawn dr := by
  unfold Chal.one Chal.many firstOfDrawn
  show ((((own[n]?).map (·.elems)).getD []).toArray.map E.ofTriple).getD 0 zeroE = _
  rw [h]
  rfl

/-- **It speaks only where the test on one round says yes at a listed round that is there.** -/
theorem speaks_only {x : OnBytes.Params.AttentionRounds} {g : Geo} {own : List Fmt.Drawn}
    (h : speaks x g own = true) :
    ∃ n ∈ readRounds x g, ∃ dr, own[n]? = some dr ∧ bad01 dr = true := by
  unfold speaks at h
  obtain ⟨n, hn, e⟩ := List.any_eq_true.1 h
  cases ho : own[n]? with
  | none =>
    rw [ho] at e
    cases e
  | some dr =>
    rw [ho] at e
    exact ⟨n, hn, dr, ho, e⟩

/-- The same by the cut of one entry out of the list. -/
theorem speaks_drop {x : OnBytes.Params.AttentionRounds} {g : Geo} {own : List Fmt.Drawn}
    (h : speaks x g own = true) :
    ∃ r ∈ readRounds x g, ((own.drop r).take 1).any bad01 = true := by
  obtain ⟨n, hn, dr, ho, hb⟩ := speaks_only h
  refine ⟨n, hn, List.any_eq_true.2 ⟨dr, ?_, hb⟩⟩
  have h0 : ((own.drop n).take 1)[0]? = some dr := by
    rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_zero]
    exact ho
  exact List.mem_of_getElem? h0

/-- An element whose three words are 1, 0, 0 is the word 1. -/
theorem isOneE_eq {w : E} (h : isOneE w = true) : w = oneE := by
  simp only [isOneE, Bool.and_eq_true, beq_iff_eq] at h
  exact E.ext3 h.1.1 h.1.2 h.2

/-- **What the test on one round says of a challenge that shows just one field element.**
Conditional: h: the test's yes; he: the challenge shows x, written in words below the prime. -/
theorem bad01_elem {dr : Fmt.Drawn} {x : Cb.Gl.E} (h : bad01 dr = true)
    (he : dr.elems = [OnBytes.Slice.ofE x]) : x = 0 ∨ x = 1 := by
  have e1 : firstOfDrawn dr = OnBytes.Slice.writeE x := by
    unfold firstOfDrawn
    rw [he]
    simp [OnBytes.Slice.writeE]
  unfold bad01 nz01 at h
  rw [e1, OnBytes.Slice.okE_writeE] at h
  cases h0 : isZeroE (OnBytes.Slice.writeE x) with
  | true =>
    left
    rw [← OnBytes.Slice.readE_writeE x, (OnBytes.Slice.isZeroE_eq _).1 h0]
    exact OnBytes.Slice.readE_zero
  | false =>
    cases h1 : isOneE (OnBytes.Slice.writeE x) with
    | true =>
      right
      rw [← OnBytes.Slice.readE_writeE x, isOneE_eq h1]
      exact OnBytes.Slice.readE_one
    | false =>
      rw [h0, h1] at h
      cases h

/-- **WHERE THE WHOLE IS SILENT, AND THE LIST HAS ALL THE LISTED ROUNDS, THE TEST `k5Reads` SAYS
YES**, at the honest side's structure of challenges with that list, whatever its key points.
Conditional: hlen; h. -/
theorem reads_of_silent {x : OnBytes.Params.AttentionRounds} {g : Geo} (zk : Array (Array E))
    {own : List Fmt.Drawn} (hlen : ∀ n ∈ readRounds x g, n < own.length)
    (h : speaks x g own = false) : k5Reads x g ⟨zk, own⟩ = true := by
  unfold k5Reads
  refine List.all_eq_true.2 fun n hn => ?_
  obtain ⟨dr, ho⟩ : ∃ dr, own[n]? = some dr := ⟨_, List.getElem?_eq_getElem (hlen n hn)⟩
  rw [one_at_own zk ho]
  unfold speaks at h
  have h1 := List.any_eq_false.1 h n hn
  rw [ho] at h1
  have h2 : bad01 dr = false := by simpa using h1
  unfold bad01 at h2
  simpa using h2

end H2K5.Honest

#print axioms H2K5.Honest.one_at_own
#print axioms H2K5.Honest.speaks_only
#print axioms H2K5.Honest.speaks_drop
#print axioms H2K5.Honest.isOneE_eq
#print axioms H2K5.Honest.bad01_elem
#print axioms H2K5.Honest.reads_of_silent
