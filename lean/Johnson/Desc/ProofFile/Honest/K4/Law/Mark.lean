-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/Mark.lean: A MARK AT THE MEMBER OF THE LAYERS' OWN ROUNDS (kind
K4): IT SPEAKS WHERE, IN ONE OF A LIST OF THAT MEMBER's ROUNDS, THE SAMPLED ELEMENT SHOWS AS 0 OR AS
1. CONDITIONAL: `k4MarkRounds_rows` (on la ≤ muV) and `zeroOrOne_elem`.

What is here. A mark (`Mark`, Honest/Law/Marks.lean) at the member of the layers' own rounds (kind
K4): a test on the challenges in front of a member and on the member's own, laid at a place, with a
stated share. This one speaks where, in one of a list of that member's rounds, the sampled element
shows as 0 or as 1. The listed rounds are numbers in the member's own list of rounds, from 0: the
last la rounds of the variables of the first product layer's masked sumcheck, and the lt rounds of
the variables of each of the two token sumchecks. `k4MarkRounds_rows` holds these numbers against
the verifier's table of K4's rounds (OnBytes/Desc/First/K4/Rounds.lean): where la ≤ muV each is a
row that sends two scalars and samples one element, none by the rule that never gives 0.
`zeroOrOne_elem`: where the test on a round speaks at a written field element, that element is 0 or
1. Definitions, and statements on lists and words with their proofs. The sentence that bounds the
measure of the challenges at which the mark speaks stands, CONDITIONAL, in Law/MarkDebt.lean.

  `k4First Q`        how many rounds stand in front of the first message of scalars: 3 in the first
      group of layers, else 1.
  `k4MarkRounds Q`   the listed rounds.
  `zeroOrOne R`      a challenge's first sampled element shows as 0 or as 1; false where it has
      none.
  `k4MarkTest Q own`, `k4Mark Q`   the test; the mark.
  `k4MarkRounds_length`   there are la + 2 lt of them.
  `zeroOrOne_elem`   where the test on a round speaks at a written field element x, x is 0 or 1.
  `at_skip`, `at_copies`, `k4_rounds_cut`   the verifier's table cut at the three listed stretches.
  `k4MarkRounds_rows`     each listed number's row of the verifier's table.

Kin. Law/MarkWide.lean has a wider mark in this one's form, whose list is cut off the verifier's
table by a test on a row: where la ≤ muV every round that is listed here is listed there
(`k4MarkRounds_sub_wide`), so that mark's silence gives this one's (`k4Wide_silent_narrow`).
`k4First Q` has the body of the library's `k0 Q.g` (OnBytes/Desc/First/K4/NormsTape.lean), in which
`k4StartAt` (Law/StartsAre.lean) is written; that file is not imported here, and no statement that
its writers know of ties the two names. The library cuts the same table in other ways: `rounds_eq`
(Johnson/Desc/First/K4/Returns/Whole.lean: five stretches, one for each function of the hearing),
`rounds_eq` (Johnson/Road/K4/DsTailR.lean: the points' rows, then the rest), and `rounds_zero` to
`rounds_join2` (Johnson/Desc/K4/Honest/Law/PtsSizes.lean: in front of five rows); none lays the
three stretches of rounds of a variable apart. `at_skip` ITSELF STANDS IN THE LIBRARY TWICE THAT ITS
WRITERS KNOW OF, THE SAME SENTENCE UP TO THE BOUND LETTERS: `append_at`
(Johnson/RunOne/Sound/KeyEightLight.lean) and `getElem?_append_at`
(Johnson/RunOne/Sound/KeyMapAtFK.lean); neither file lies beneath this one. At lists of stages, with
"= some s" at both ends: `get_behind` (Honest/K3/Parts/Index.lean).

Not shown here. NO CHANCE IS COUNTED IN THIS FILE. WHAT THIS MARK's SILENCE GIVES AT ANY STATE OF
THE VERIFIER IS NOT SHOWN HERE, NOR IN ANY FILE THAT ITS WRITERS KNOW OF; for the wider mark see the
head of Law/MarkWide.lean. That la ≤ muV (the hypothesis of `k4MarkRounds_rows`) is not shown in
this file: Law/MarkPlan.lean, which is no part of the library yet, shows it of every plan with
routed experts (p3) whose layout and numbers of reads the program's functions return; where la is
more than muV the first stretch of the list runs into the rows in front of that sumcheck's
variables, and beyond k4First + 3 + muV the subtraction is cut at 0. The test compares words as they
are: an element whose words are not below the prime may read as 0 and pass it (the words (p, 0, 0)).
By reading, one that reads as 1 does not pass, whatever its words: a difference's words lie below
the prime. Not stated here. THE SHARE IS A STATED NUMBER, NO BOUND, written as a product; it is not
evaluated here. The verifier has no test of this event: a mark is counted, not tested by the
verifier. THAT THE VERIFIER REJECTS NOTHING WHERE THE MARK SPEAKS IS NOT SAID: by reading, K4's own
test "free-slot", in a later member (`k4FreeSlotFall`, Honest/K4/Part.lean), can refuse where a
sampled element is 0 or 1: the head of Law/MarkWide.lean. The words "the verifier does not reject"
in the test's text are for a print and say no more than this paragraph's sentence on the verifier's
tests.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Part
import Johnson.Desc.ProofFile.Honest.Law.Marks
import OnBytes.Slice.ProgField

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E isZeroE subE oneE)
open OnBytes.Desc.First.K4 (pointRd batchRd masked layerRds)
open OnBytes.Model (ledNS ledNP ledNO)
open OnBytes.Model.Layer (nEndT)
open OnBytes.Desc.First.K4.Honest

/-- How many rounds stand in front of the round with the first message of scalars. -/
def k4First (Q : K4Pub) : Nat := if Q.g == 0 then 3 else 1

/-- **The listed rounds**, by their numbers in K4's own list of rounds, from 0. -/
def k4MarkRounds (Q : K4Pub) : List Nat :=
  List.range' (k4First Q + 3 + Q.P.rd.muV - Q.P.y.h.la) Q.P.y.h.la ++
    List.range' (k4First Q + 8 + Q.P.rd.muV) Q.P.y.h.lt ++
    List.range' (k4First Q + 11 + Q.P.rd.muV + Q.P.y.h.lt) Q.P.y.h.lt

/-- A challenge's first sampled element shows as 0 or as 1. False where it has no element. -/
def zeroOrOne (R : Fmt.Drawn) : Bool :=
  match R.elems.head? with
  | some t => isZeroE (E.ofTriple t) || isZeroE (subE (E.ofTriple t) oneE)
  | none => false

/-- **The mark's test**, of the member's own challenges. -/
def k4MarkTest (Q : K4Pub) (own : List Fmt.Drawn) : Option String :=
  if (k4MarkRounds Q).any fun i => (own[i]?).any zeroOrOne then
    some ("K4: a coordinate of a point that the layers' own rounds sample is 0 or 1 " ++
      "(counted; the verifier does not reject)")
  else none

/-- **The mark at K4's own member.** The share: a stated number, written as a product in the number
of listed rounds. -/
def k4Mark (Q : K4Pub) : Mark :=
  ⟨k4Place Q, fun _ own => k4MarkTest Q own,
    ⟨2 * (k4MarkRounds Q).length * (2 ^ 128 + 1) ^ 3, Code.pGold ^ 3 * (2 ^ 128) ^ 3⟩⟩

theorem k4MarkRounds_length (Q : K4Pub) :
    (k4MarkRounds Q).length = Q.P.y.h.la + 2 * Q.P.y.h.lt := by
  unfold k4MarkRounds
  rw [List.length_append, List.length_append, List.length_range', List.length_range',
    List.length_range']
  omega

/-- **Where the test on a round speaks at a written field element x, x is 0 or 1.** -/
theorem zeroOrOne_elem (dr : Fmt.Drawn) (x : Cb.Gl.E) (h : zeroOrOne dr = true)
    (he : dr.elems = [OnBytes.Slice.ofE x]) : x = 0 ∨ x = 1 := by
  unfold zeroOrOne at h
  rw [he] at h
  have h' : (isZeroE (E.ofTriple (OnBytes.Slice.ofE x)) ||
      isZeroE (subE (E.ofTriple (OnBytes.Slice.ofE x)) oneE)) = true := h
  have ex : OnBytes.Model.Reading.gl.val (E.ofTriple (OnBytes.Slice.ofE x)) = x :=
    (OnBytes.Slice.readE_ofTriple _).trans (OnBytes.Slice.toE_ofE x)
  rw [Bool.or_eq_true] at h'
  rcases h' with h0 | h1
  · left
    rw [← ex]
    exact OnBytes.Slice.readE_of_isZeroE _ h0
  · right
    have e := OnBytes.Slice.readE_of_isZeroE _ h1
    have e' : OnBytes.Model.Reading.gl.val (subE (E.ofTriple (OnBytes.Slice.ofE x)) oneE) = 0 := e
    rw [OnBytes.Model.Reading.gl.sub, OnBytes.Model.Reading.gl.one, ex] at e'
    exact sub_eq_zero.1 e'

/-- Behind a list of n members, entry n + i of the joined list is entry i of the second. -/
theorem at_skip {α : Type} (A T : List α) (n i : Nat) (h : A.length = n) :
    (A ++ T)[n + i]? = T[i]? := by
  subst h
  rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

/-- Entry j of n copies of r with a list behind them. -/
theorem at_copies {α : Type} (n : Nat) (r : α) (T : List α) (j : Nat) (hj : j < n) :
    (List.replicate n r ++ T)[j]? = some r := by
  rw [List.getElem?_append_left (by rw [List.length_replicate]; exact hj),
    List.getElem?_replicate, if_pos hj]

/-- **The verifier's table, cut at the three stretches of rounds of a variable that are listed.** -/
theorem k4_rounds_cut (Q : K4Pub) : ∃ A B C D : List OnBytes.Desc.First.K4.Rd,
    A.length = k4First Q + 3 ∧ B.length = 5 ∧ C.length = 3 ∧
    OnBytes.Desc.First.K4.rounds Q.P Q.hp Q.g =
      A ++ (List.replicate Q.P.rd.muV { name := .pscRound, sent := 2 } ++ (B ++
        (List.replicate Q.P.y.h.lt { name := .pscRound, sent := 2 } ++ (C ++
          (List.replicate Q.P.y.h.lt { name := .pscRound, sent := 2 } ++ D))))) := by
  refine ⟨[pointRd .zero Q.P.y.h.lt] ++
      (if Q.g == 0 then [pointRd .zero (Q.P.y.ls + Q.P.y.h.lt),
        pointRd .zero (Q.P.y.lPd - Q.P.y.ls)] else []) ++
      [batchRd (ledNS Q.P.y.h.xl * Q.P.y.NI) (ledNS Q.P.y.h.xl), pointRd .join Q.P.rd.lNI,
        { name := .pscEpsilon, sent := 1 }],
    [{ name := .pscY, sent := 2, notZero := 1 }, { name := .pscValues, sent := 2, drawn := 0 },
      { name := .line }, batchRd (ledNP Q.P.y.h.xl * Q.P.y.NI) (ledNP Q.P.y.h.xl * Q.P.y.NI),
      { name := .pscEpsilon, sent := 2 }],
    [{ name := .pscY, sent := 2, notZero := 1 },
      { name := .pscValues, sent := ledNO Q.P.y.h.xl * Q.P.y.NI, drawn := 0 },
      { name := .pscEpsilon, sent := 2 }],
    [{ name := .pscY, sent := 1, notZero := 1 },
      { name := .pscValues, sent := nEndT Q.P.y, drawn := 0 }] ++ [batchRd 0 2] ++
      masked Q.hp.lamS 1 2 (2 + (1 + Q.P.y.LamM) + (Q.hp.NCL - if Q.g == 0 then 1 else 0)) ++
      layerRds Q.P.rd.muH ++ [pointRd .join (Q.P.y.h.ll - 1)] ++ layerRds Q.P.rd.muH2 ++
      [batchRd (if Q.g == 0 then 1 else 0) Q.hp.NCL] ++ masked Q.P.wsLay.lk 1 1 1,
    ?_, rfl, rfl, ?_⟩
  · unfold k4First
    cases (Q.g == 0) <;> rfl
  · unfold OnBytes.Desc.First.K4.rounds
    cases (Q.g == 0) <;> simp [layerRds, masked]

/-- **Each listed number's row of the verifier's table is a round of a masked sumcheck's variable**:
it sends two scalars and samples one element, none by the rule that never gives 0. CONDITIONAL: the
first product layer has at least la variables. -/
theorem k4MarkRounds_rows (Q : K4Pub) (hla : Q.P.y.h.la ≤ Q.P.rd.muV) :
    ∀ i ∈ k4MarkRounds Q, (OnBytes.Desc.First.K4.rounds Q.P Q.hp Q.g)[i]? =
      some { name := .pscRound, sent := 2 } := by
  intro i hi
  obtain ⟨A, B, C, D, hA, hB, hC, e⟩ := k4_rounds_cut Q
  rw [e]
  unfold k4MarkRounds at hi
  rw [List.mem_append, List.mem_append] at hi
  rcases hi with (h | h) | h
  · obtain ⟨h1, h2⟩ := List.mem_range'_1.1 h
    obtain ⟨j, rfl⟩ : ∃ j, i = (k4First Q + 3) + j := ⟨i - (k4First Q + 3), by omega⟩
    rw [at_skip A _ _ j hA]
    exact at_copies _ _ _ j (by omega)
  · obtain ⟨h1, h2⟩ := List.mem_range'_1.1 h
    obtain ⟨j, rfl⟩ : ∃ j, i = (k4First Q + 3) + (Q.P.rd.muV + (5 + j)) :=
      ⟨i - (k4First Q + 8 + Q.P.rd.muV), by omega⟩
    rw [at_skip A _ _ _ hA, at_skip _ _ _ _ List.length_replicate, at_skip B _ _ j hB]
    exact at_copies _ _ _ j (by omega)
  · obtain ⟨h1, h2⟩ := List.mem_range'_1.1 h
    obtain ⟨j, rfl⟩ : ∃ j, i = (k4First Q + 3) + (Q.P.rd.muV + (5 + (Q.P.y.h.lt + (3 + j)))) :=
      ⟨i - (k4First Q + 11 + Q.P.rd.muV + Q.P.y.h.lt), by omega⟩
    rw [at_skip A _ _ _ hA, at_skip _ _ _ _ List.length_replicate, at_skip B _ _ _ hB,
      at_skip _ _ _ _ List.length_replicate, at_skip C _ _ j hC]
    exact at_copies _ _ _ j (by omega)

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4First
#print axioms ProofFile.Honest.K4.k4MarkRounds
#print axioms ProofFile.Honest.K4.zeroOrOne
#print axioms ProofFile.Honest.K4.k4MarkTest
#print axioms ProofFile.Honest.K4.k4Mark
#print axioms ProofFile.Honest.K4.k4MarkRounds_length
#print axioms ProofFile.Honest.K4.zeroOrOne_elem
#print axioms ProofFile.Honest.K4.at_skip
#print axioms ProofFile.Honest.K4.at_copies
#print axioms ProofFile.Honest.K4.k4_rounds_cut
#print axioms ProofFile.Honest.K4.k4MarkRounds_rows
