-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/MarkWide.lean: six definitions, and statements on lists with
their proofs.

What is here. A mark (`Mark`, Honest/Law/Marks.lean) is a test on the challenges in front of a
member and on the member's own, laid at a place, with a stated share. A mark is silent where its
test returns none. A fall (`Fall`, Honest/Side.lean) is a test on the verifier's state in front of a
member and on that member's challenges, laid at a place, with a stated share of its own. This is A
WIDER MARK AT THE MEMBER OF THE LAYERS' OWN ROUNDS (kind K4), in the form of `k4Mark`
(Law/Mark.lean): it speaks where, in one of a list of that member's rounds, the sampled element
shows as 0 or as 1. THE LIST IS CUT OFF THE VERIFIER's OWN TABLE OF K4's ROUNDS
(OnBytes/Desc/First/K4/Rounds.lean) BY A TEST ON A ROW: the row draws one element, and none by the
rule that never gives 0 (`k4PlainOne`); AND ONE SUCH ROUND IS LEFT OUT (`k4CoinRound`): the "PSC
epsilon" of the second token sumcheck. There, by reading, K4's hearing itself tests the drawn
element and refuses it at 0 ("coin-zero", OnBytes/Desc/First/K4/Hear.lean), and the fall `k4Fall`
counts that (`k4CoinZero`, Honest/K4/Part.lean): the number that is left out is, by definition, the
very term that `k4CoinZero` reads, so the mark and `k4Fall` stand at different rounds
(`k4Wide_not_coin`). `k4WideRounds_iff` says of every number i that it is listed just if the table's
row number i is such a row and i is not that round: so the list cannot part from the table, and no
comparison of the plan's numbers is asked. A round that draws a point, under another name than "PSC
epsilon", is listed just where the point has one coordinate (`k4Wide_point`). Where la ≤ muV every
round that `k4Mark` lists is listed (`k4MarkRounds_sub_wide`), so this mark's silence gives that
mark's (`k4Wide_silent_narrow`). What silence gives on the member's own challenges: at each listed
round the test on a round says no (`k4Wide_silent`). The place is `k4Mark`'s.

  `k4PlainOne d`   the test on a row.
  `k4Listed p j l`   the numbers, from j on, of the members of l at which p says yes.
  `k4CoinRound Q`   the round that is left out: the number that `k4CoinZero` reads.
  `k4WideRounds Q`   the listed rounds, by their numbers in K4's own list of rounds, from 0.
  `k4WideTest Q own`, `k4MarkWide Q`   the test; the mark.
  `k4MarkWide_test`, `k4MarkWide_share`   the mark's two fields, unfolded.
  `k4Listed_mem`, `k4Listed_length`, `k4Listed_nodup`   what is listed; how many; none twice.
  `k4CoinRound_eq`, `k4CoinRound_row`   the round that is left out: its number; its row's name.
  `k4WideRounds_iff`   **listed just if the table's row draws one element by the plain rule and the
      round is not the one that is left out.**
  `k4Wide_not_coin`   **the round at which K4's fall reads is not listed.**
  `k4Wide_point`   a round that draws a point.
  `k4MarkRounds_sub_wide`, `k4Wide_silent_narrow`   against `k4Mark`.
  `k4Wide_silent`   **what silence gives on the member's own challenges.**
  `k4MarkWide_blind`, `k4MarkWide_place`   what the mark does not read; its place.

Not shown here. FOUR FILES OF THIS FOLDER THAT ARE NAMED BELOW ARE NO PART OF THE LIBRARY YET:
Law/MarkWideCount.lean, Law/MarkWideTable.lean, Law/MarkWideDebt.lean, Law/TapeAccepts.lean. How
many rounds are listed: Law/MarkWideCount.lean. Which rows are such rows by their names:
Law/MarkWideTable.lean. The sentence that bounds the measure of the challenges at which the mark
speaks: Law/MarkWideDebt.lean, conditional. WHAT THE MARK's SILENCE GIVES AT A STATE OF THE VERIFIER
IS NOT SHOWN HERE: Law/Live/LiveOfYes.lean (at the state behind K4's block), over
Law/Live/TapeOfMark.lean (on the tape that the block hands to its hearing), conditional; nothing
here ties a member of the list `own` of challenges to what K4's hearing lays into the state. THAT
K4's OWN MEMBER REJECTS FOR NO LISTED ELEMENT IS NOT SHOWN HERE; THERE IS A STATEMENT, NOT SPENT
HERE: K4's hearing returns at every value of every other element that its rounds draw, under
premises on the plan, on the tape's shape (names and numbers alone), on the ledger in front and on
what the lookup returned, none of which reads an element that K4's rounds draw: of the premises of
`hear_returns` (Johnson/Desc/First/K4/Returns/Whole.lean) two alone are on sampled values, one on
the lookup's points and one on that one element, and `coin_tape` (Law/TapeAccepts.lean) pays the
second where `k4CoinZero` is silent. (A third test of the hearing is made of sampled points, listed
elements among them, and holds at every point: Honest/K4/Part.lean's head.) K4's OWN MEMBER IS
MEANT. K4's OWN TEST "free-slot" RUNS IN A LATER MEMBER (`k4FreeSlotFall`, Honest/K4/Part.lean) AND,
BY READING, CAN REFUSE WHERE A LISTED ELEMENT IS 0 OR 1: THAT IS WHAT THE MARK IS FOR: it is counted
so that that fall can be bounded where the mark is silent. OF THE ROUND THAT IS LEFT OUT THE MARK
SAYS NOTHING: neither that its element is not 0 nor that it is not 1. A ROUND THAT DRAWS A POINT OF
SEVERAL COORDINATES IS NOT LISTED: of these coordinates the mark says nothing. Nor is a round listed
whose element is drawn by the rule that never gives 0, or that draws nothing. WHERE THE LIST `own`
HAS NO MEMBER AT A LISTED NUMBER THE TEST PASSES THAT ROUND BY: at the empty list the mark is
silent. The test compares words as they are: an element whose words are not below the prime may read
as 0 and pass it (the words (p, 0, 0)). By reading, one that reads as 1 does not pass, whatever its
words: a difference's words lie below the prime. Not stated here. THE SHARE IS A STATED NUMBER, NO
BOUND, written as a product; it is not evaluated here. By reading: the mark reads the plan hp
through the table (how many rounds the batched sumcheck has), which `k4Mark` does not; it reads
neither r0 nor seg (`k4MarkWide_blind`).

Kin. `k4Listed` walks a list as `rowsNamed` (Johnson/Desc/K4/Honest/Front.lean) walks the table: the
numbers of the members that pass a test; there the test is on the row's name and the walk is written
with `zipIdx` (`idxOf`, Johnson/Desc/K4/Honest/Law/PtsSizes.lean, is that walk from any number on,
with the like law on how many, `idxOf_length`, and a law on one listed row, `idx_at`); no statement
that we know ties the two. What the test on a round says of the element as a member of the field:
Law/MarkWideElem.lean. The marks of all twelve groups as one list: `k4MarksWide`
(Law/K4MarksWide.lean).

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.Mark
import Johnson.Desc.ProofFile.Honest.K4.Law.StartsAre

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes.Desc.First.K4 (pointRd)
open OnBytes.Desc.First.K4.Honest

/-- **The test on a row of the verifier's table**: it draws one element, and none by the rule that
never gives 0. -/
def k4PlainOne (d : OnBytes.Desc.First.K4.Rd) : Bool := d.drawn == 1 && d.notZero == 0

/-- The numbers, from j on, of the members of a list at which a test says yes. -/
def k4Listed {α : Type} (p : α → Bool) : Nat → List α → List Nat
  | _, [] => []
  | j, x :: l => if p x then j :: k4Listed p (j + 1) l else k4Listed p (j + 1) l

/-- **The round that is left out**: the number at which `k4CoinZero` (Honest/K4/Part.lean) reads the
member's own challenges. -/
def k4CoinRound (Q : K4Pub) : Nat := (starts Q).getD 2 0

/-- **The listed rounds**, by their numbers in K4's own list of rounds, from 0. -/
def k4WideRounds (Q : K4Pub) : List Nat :=
  (k4Listed k4PlainOne 0 (OnBytes.Desc.First.K4.rounds Q.P Q.hp Q.g)).filter fun i =>
    i != k4CoinRound Q

/-- **The mark's test**, of the member's own challenges. -/
def k4WideTest (Q : K4Pub) (own : List Fmt.Drawn) : Option String :=
  if (k4WideRounds Q).any fun i => (own[i]?).any zeroOrOne then
    some ("K4: an element that the layers' own rounds sample alone in its round is 0 or 1 " ++
      "(counted; K4's own member does not reject for it)")
  else none

/-- **The wider mark at K4's own member.** The share: a stated number, written as a product in the
number of listed rounds. -/
def k4MarkWide (Q : K4Pub) : Mark :=
  ⟨k4Place Q, fun _ own => k4WideTest Q own,
    ⟨2 * (k4WideRounds Q).length * (2 ^ 128 + 1) ^ 3, Code.pGold ^ 3 * (2 ^ 128) ^ 3⟩⟩

/-- The mark's test, unfolded. -/
theorem k4MarkWide_test (Q : K4Pub) (fr own : List Fmt.Drawn) :
    (k4MarkWide Q).test fr own = k4WideTest Q own := by
  simp only [k4MarkWide]

/-- The mark's share, unfolded. -/
theorem k4MarkWide_share (Q : K4Pub) : (k4MarkWide Q).share =
    ⟨2 * (k4WideRounds Q).length * (2 ^ 128 + 1) ^ 3, Code.pGold ^ 3 * (2 ^ 128) ^ 3⟩ := by
  simp only [k4MarkWide]

/-- What is listed: j + k, where the test says yes at member number k. -/
theorem k4Listed_mem {α : Type} (p : α → Bool) : ∀ (l : List α) (j i : Nat),
    i ∈ k4Listed p j l ↔ ∃ k d, i = j + k ∧ l[k]? = some d ∧ p d = true
  | [], j, i => by
    constructor
    · intro h
      cases h
    · rintro ⟨k, d, _, h, _⟩
      rw [List.getElem?_nil] at h
      cases h
  | x :: l, j, i => by
    have ih := k4Listed_mem p l (j + 1) i
    constructor
    · intro h
      have h' : i ∈ (if p x then j :: k4Listed p (j + 1) l else k4Listed p (j + 1) l) := h
      by_cases hx : p x = true
      · rw [if_pos hx] at h'
        rcases List.mem_cons.1 h' with e | h2
        · exact ⟨0, x, e, List.getElem?_cons_zero, hx⟩
        · obtain ⟨k, d, e, hd, hp⟩ := ih.1 h2
          exact ⟨k + 1, d, by omega, by rw [List.getElem?_cons_succ]; exact hd, hp⟩
      · rw [if_neg hx] at h'
        obtain ⟨k, d, e, hd, hp⟩ := ih.1 h'
        exact ⟨k + 1, d, by omega, by rw [List.getElem?_cons_succ]; exact hd, hp⟩
    · rintro ⟨k, d, e, hd, hp⟩
      show i ∈ (if p x then j :: k4Listed p (j + 1) l else k4Listed p (j + 1) l)
      cases k with
      | zero =>
        rw [List.getElem?_cons_zero] at hd
        obtain rfl : x = d := Option.some.inj hd
        rw [if_pos hp]
        exact List.mem_cons.2 (Or.inl e)
      | succ k =>
        rw [List.getElem?_cons_succ] at hd
        have h2 : i ∈ k4Listed p (j + 1) l := ih.2 ⟨k, d, by omega, hd, hp⟩
        by_cases hx : p x = true
        · rw [if_pos hx]
          exact List.mem_cons_of_mem _ h2
        · rw [if_neg hx]
          exact h2

/-- How many are listed. -/
theorem k4Listed_length {α : Type} (p : α → Bool) : ∀ (l : List α) (j : Nat),
    (k4Listed p j l).length = l.countP p
  | [], _ => rfl
  | x :: l, j => by
    show (if p x then j :: k4Listed p (j + 1) l else k4Listed p (j + 1) l).length = _
    by_cases hx : p x = true
    · rw [if_pos hx, List.length_cons, k4Listed_length p l (j + 1), List.countP_cons_of_pos hx]
    · rw [if_neg hx, k4Listed_length p l (j + 1), List.countP_cons_of_neg hx]

/-- None is listed twice. -/
theorem k4Listed_nodup {α : Type} (p : α → Bool) : ∀ (l : List α) (j : Nat),
    (k4Listed p j l).Nodup
  | [], _ => List.nodup_nil
  | x :: l, j => by
    show (if p x then j :: k4Listed p (j + 1) l else k4Listed p (j + 1) l).Nodup
    by_cases hx : p x = true
    · rw [if_pos hx]
      refine List.nodup_cons.2 ⟨?_, k4Listed_nodup p l (j + 1)⟩
      intro h
      obtain ⟨k, _, e, _, _⟩ := (k4Listed_mem p l (j + 1) j).1 h
      omega
    · rw [if_neg hx]
      exact k4Listed_nodup p l (j + 1)

/-- The round that is left out, as a number: the first round of masked sumcheck number 2, from 0. -/
theorem k4CoinRound_eq (Q : K4Pub) : k4CoinRound Q = k4StartAt Q 2 := by
  unfold k4CoinRound
  rw [starts_eq]
  rfl

/-- The table's row at the round that is left out bears the name "PSC epsilon". -/
theorem k4CoinRound_row (Q : K4Pub) :
    ∃ d, (OnBytes.Desc.First.K4.rounds Q.P Q.hp Q.g)[k4CoinRound Q]? = some d ∧
      d.name = .pscEpsilon := by
  have hm : k4CoinRound Q ∈ starts Q := by
    rw [k4CoinRound_eq, starts_eq]
    exact List.mem_map.2 ⟨2, by simp, rfl⟩
  unfold starts rowsNamed at hm
  obtain ⟨⟨d, j⟩, hf, e⟩ := List.mem_map.1 hm
  obtain ⟨hz, hn⟩ := List.mem_filter.1 hf
  have hd : (OnBytes.Desc.First.K4.rounds Q.P Q.hp Q.g)[j]? = some d := by
    simpa using (List.mk_mem_zipIdx_iff_getElem?.1 hz)
  have e' : j = k4CoinRound Q := e
  rw [e'] at hd
  exact ⟨d, hd, by simpa using hn⟩

/-- **A NUMBER IS LISTED JUST IF THE TABLE's ROW OF THAT NUMBER DRAWS ONE ELEMENT, AND NONE BY THE
RULE THAT NEVER GIVES 0, AND THE NUMBER IS NOT THAT OF THE ROUND THAT IS LEFT OUT.** -/
theorem k4WideRounds_iff (Q : K4Pub) (i : Nat) :
    i ∈ k4WideRounds Q ↔ (∃ d, (OnBytes.Desc.First.K4.rounds Q.P Q.hp Q.g)[i]? = some d ∧
      d.drawn = 1 ∧ d.notZero = 0) ∧ i ≠ k4CoinRound Q := by
  unfold k4WideRounds
  rw [List.mem_filter, k4Listed_mem, bne_iff_ne]
  constructor
  · rintro ⟨⟨k, d, e, hd, hp⟩, hne⟩
    obtain rfl : i = k := by omega
    unfold k4PlainOne at hp
    rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hp
    exact ⟨⟨d, hd, hp.1, hp.2⟩, hne⟩
  · rintro ⟨⟨d, hd, h1, h2⟩, hne⟩
    refine ⟨⟨i, d, by omega, hd, ?_⟩, hne⟩
    unfold k4PlainOne
    rw [h1, h2]
    rfl

/-- **THE ROUND AT WHICH K4's FALL READS IS NOT LISTED.** -/
theorem k4Wide_not_coin (Q : K4Pub) : k4CoinRound Q ∉ k4WideRounds Q := fun h =>
  ((k4WideRounds_iff Q _).1 h).2 rfl

/-- CONDITIONAL: on h and hr. A round that draws a point is listed just where the point has one
coordinate. -/
theorem k4Wide_point (Q : K4Pub) {i n : Nat} {r : OnBytes.Model.RoundName}
    (h : (OnBytes.Desc.First.K4.rounds Q.P Q.hp Q.g)[i]? = some (pointRd r n))
    (hr : r ≠ .pscEpsilon) : i ∈ k4WideRounds Q ↔ n = 1 := by
  rw [k4WideRounds_iff]
  constructor
  · rintro ⟨⟨d, hd, h1, _⟩, _⟩
    obtain rfl : pointRd r n = d := Option.some.inj (h.symm.trans hd)
    exact h1
  · intro e
    refine ⟨⟨_, h, e, rfl⟩, fun ei => ?_⟩
    obtain ⟨d, hd, hn⟩ := k4CoinRound_row Q
    rw [← ei, h] at hd
    obtain rfl : pointRd r n = d := Option.some.inj hd
    exact hr hn

/-- CONDITIONAL: on hla. Every round that `k4Mark` lists is listed. -/
theorem k4MarkRounds_sub_wide (Q : K4Pub) (hla : Q.P.y.h.la ≤ Q.P.rd.muV) :
    ∀ i ∈ k4MarkRounds Q, i ∈ k4WideRounds Q := fun i hi =>
  (k4WideRounds_iff Q i).2 ⟨⟨_, k4MarkRounds_rows Q hla i hi, rfl, rfl⟩, fun ei => by
    obtain ⟨d, hd, hn⟩ := k4CoinRound_row Q
    rw [← ei, k4MarkRounds_rows Q hla i hi] at hd
    obtain rfl := Option.some.inj hd
    cases hn⟩

/-- CONDITIONAL: on h. **WHAT SILENCE GIVES ON THE MEMBER's OWN CHALLENGES**: at each listed round
the test on a round says no. -/
theorem k4Wide_silent (Q : K4Pub) {fr own : List Fmt.Drawn}
    (h : (k4MarkWide Q).test fr own = none) :
    ∀ i ∈ k4WideRounds Q, ∀ dr, own[i]? = some dr → zeroOrOne dr = false := by
  intro i hi dr hd
  cases hz : zeroOrOne dr with
  | false => rfl
  | true =>
    rw [k4MarkWide_test] at h
    unfold k4WideTest at h
    rw [if_pos (List.any_eq_true.2 ⟨i, hi, by rw [hd]; exact hz⟩)] at h
    cases h

/-- CONDITIONAL: on hla and h. The wider mark's silence gives the silence of `k4Mark`. -/
theorem k4Wide_silent_narrow (Q : K4Pub) (hla : Q.P.y.h.la ≤ Q.P.rd.muV)
    {fr own : List Fmt.Drawn} (h : (k4MarkWide Q).test fr own = none) :
    (k4Mark Q).test fr own = none := by
  show k4MarkTest Q own = none
  unfold k4MarkTest
  rw [if_neg]
  intro hc
  obtain ⟨i, hi, hx⟩ := List.any_eq_true.1 hc
  cases ho : own[i]? with
  | none =>
    rw [ho] at hx
    cases hx
  | some dr =>
    rw [ho] at hx
    have hz := k4Wide_silent Q h i (k4MarkRounds_sub_wide Q hla i hi) dr ho
    have hx' : zeroOrOne dr = true := hx
    rw [hz] at hx'
    cases hx'

/-- **THE MARK READS NEITHER r0 NOR seg**: at two public data that agree in the five other fields it
is one structure. -/
theorem k4MarkWide_blind (P : OnBytes.Model.Layer.Pub) (hp : OnBytes.Model.Layer.HPlan2)
    (g link piece a a' s s' : Nat) :
    k4MarkWide ⟨P, hp, g, link, piece, a, s⟩ = k4MarkWide ⟨P, hp, g, link, piece, a', s'⟩ :=
  rfl

/-- The place is that of `k4Mark`. -/
theorem k4MarkWide_place (Q : K4Pub) : (k4MarkWide Q).place = (k4Mark Q).place := rfl

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4PlainOne
#print axioms ProofFile.Honest.K4.k4Listed
#print axioms ProofFile.Honest.K4.k4CoinRound
#print axioms ProofFile.Honest.K4.k4WideRounds
#print axioms ProofFile.Honest.K4.k4WideTest
#print axioms ProofFile.Honest.K4.k4MarkWide
#print axioms ProofFile.Honest.K4.k4MarkWide_test
#print axioms ProofFile.Honest.K4.k4MarkWide_share
#print axioms ProofFile.Honest.K4.k4Listed_mem
#print axioms ProofFile.Honest.K4.k4Listed_length
#print axioms ProofFile.Honest.K4.k4Listed_nodup
#print axioms ProofFile.Honest.K4.k4CoinRound_eq
#print axioms ProofFile.Honest.K4.k4CoinRound_row
#print axioms ProofFile.Honest.K4.k4WideRounds_iff
#print axioms ProofFile.Honest.K4.k4Wide_not_coin
#print axioms ProofFile.Honest.K4.k4Wide_point
#print axioms ProofFile.Honest.K4.k4MarkRounds_sub_wide
#print axioms ProofFile.Honest.K4.k4Wide_silent
#print axioms ProofFile.Honest.K4.k4Wide_silent_narrow
#print axioms ProofFile.Honest.K4.k4MarkWide_blind
#print axioms ProofFile.Honest.K4.k4MarkWide_place
