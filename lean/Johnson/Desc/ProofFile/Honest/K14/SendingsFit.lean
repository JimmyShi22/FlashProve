-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/SendingsFit.lean: what the two sendings' parts of
Honest/K14/Sendings.lean send has the shape that a sending of the shared chain declares, at all
parameters at which the sending's codes are the plan's (Q.codes = P.codes, a premise of seed_fits):
each of the part's two messages passes the test Sending.fits (Honest/Frame.lean), which the frame's
function play asks of every message. That sentence is four statements read together (says_send,
send_declared, seed_fits, answer_fits); no statement of this file joins them. Seven statements with
their proofs; no definition.

  send_declared   what a sending of the shared chain declares (sendAt,
                  Johnson/Desc/K14/Blocks.lean): two rounds: K1's "SEND seed", with the oracle
                  messages that the chain states for its trees, and K1's "SEND answer", with none
  seed_fits       where the sending's codes are the plan's: no item in the clear and the part's
                  tables fit the first
  sum_filter_ne, range_answers, length_answersOf, answer_fits   the part's OOD answers are as many
                  as the second round cuts, and fit it
  says_send       what the part's two moves return: never an error

The tables' half of seed_fits holds by construction: where the two lists of codes are one, the
part's tables and the chain's declared oracle messages take their lengths and widths from one
function of the same notices (Johnson/Desc/Own/Trees.lean: treesMade). At a sending with other codes
the two come from two different calls of it, and nothing is said. Where treesMade returns nothing,
both lists are empty and the test is passed with no table.

Nearest kin in the library: sum_filter_ne says what sum_filter_nz
(Johnson/Desc/K14/Honest/ChainMet.lean) says, with other names for the letters.
Who calls them: send_declared and says_send, which hold by unfolding, are called by no other file.

What is not claimed. That play returns: it asks more (the book's lending, the stops). That a table's
symbols have the stated width for a reason other than their type. Nothing on a verifier's decision,
on soundness or on hiding.
-/
import Johnson.Desc.ProofFile.Honest.K14.Sendings
import Johnson.Desc.K1.Law.When

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes (E zeroE)
open OnBytes.Slice (toE)
open VerifiableInference.Desc (K1.Par K1.seedEntry K1.answerEntry itemOf)
open Desc.K14 (P14 St sendAt oraclesOf)

/-- **What a sending of the shared chain declares.** -/
theorem send_declared (P : P14) (n : String) (Q : K1.Par) (inFront : Option Fmt.Entry)
    (groups : List (List Nat)) (behind : St → Array Nat → Option St) :
    (sendAt P n Q inFront groups behind).rounds.zip (sendAt P n Q inFront groups behind).oracles =
      [({ entry := K1.seedEntry Q }, oraclesOf P.codes Q.sent groups),
       ({ entry := K1.answerEntry Q }, [])] := rfl

/-- **Where the sending's codes are the plan's (hc), the first message fits**: no item in the clear,
and a table of the stated length and width for each tree. Where `treesMade` returns nothing there is
no tree, and the test is passed with no table. -/
theorem seed_fits (P : P14) (Q : K1.Par) (groups : List (List Nat)) (hc : Q.codes = P.codes)
    (L : Nat → Laid) :
    ({ vals := [], tables := sentTables Q.codes Q.sent L } : Sending).fits
      { entry := K1.seedEntry Q }
      (oraclesOf P.codes Q.sent groups) = true := by
  have h1 : (Fmt.DeclaredRound.items { entry := K1.seedEntry Q }).filter (· != .root) = [] := by
    simp [Fmt.DeclaredRound.items, Fmt.Entry.cut, K1.seedEntry]
  have h2 : (sentTables Q.codes Q.sent L).map (fun t => (t.logLength, t.words)) =
      (oraclesOf P.codes Q.sent groups).map fun o => (o.logLength, o.words) := by
    unfold sentTables oraclesOf
    rw [hc]
    cases VerifiableInference.Desc.Own.treesMade P.codes Q.sent with
    | none => rfl
    | some l => simp [List.map_map, Function.comp_def]
  unfold Sending.fits
  rw [h1, h2]
  simp

/-- A sum over a list is the sum over those of its members at which the summand is not 0. The same
statement as the library's `sum_filter_nz` (Johnson/Desc/K14/Honest/ChainMet.lean). -/
theorem sum_filter_ne (a : Nat → Nat) : ∀ l : List Nat,
    ((l.filter fun k => a k != 0).map a).sum = (l.map a).sum
  | [] => rfl
  | k :: l => by
    by_cases h : a k = 0
    · rw [List.filter_cons_of_neg (by simp [h]), List.map_cons, List.sum_cons, h, Nat.zero_add]
      exact sum_filter_ne a l
    · rw [List.filter_cons_of_pos (by simp [h]), List.map_cons, List.map_cons, List.sum_cons,
        List.sum_cons, sum_filter_ne a l]

/-- The messages' numbers of answers, by number, are those of the list of shapes. -/
theorem range_answers (Q : K1.Par) :
    ((List.range Q.sent.size).map fun k => (Q.sent.getD k default).shape.answers) =
      (VerifiableInference.Desc.K1.shapesOf Q).map (·.answers) := by
  apply List.ext_getElem
  · simp [VerifiableInference.Desc.K1.shapesOf]
  · intro i h1 _
    have hi : i < Q.sent.size := by simpa using h1
    simp [VerifiableInference.Desc.K1.shapesOf, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem hi]

/-- The part's OOD answers are as many as K1's parameters count. -/
theorem length_answersOf (Q : K1.Par) (L : Nat → Laid) (seeds : List (List E × E)) :
    (answersOf Q L seeds).length = Q.answers := by
  rw [VerifiableInference.Desc.K1.answers_sum, ← range_answers]
  unfold answersOf
  simp only [List.length_flatMap, List.length_map, List.length_range]
  exact sum_filter_ne (fun k => (Q.sent.getD k default).shape.answers) _

/-- **The second message fits**: the OOD answers, and no table. -/
theorem answer_fits (Q : K1.Par) (L : Nat → Laid) (seeds : List (List E × E)) :
    ({ vals := (answersOf Q L seeds).map fun y => .answer (toE y.triple), tables := [] } :
      Sending).fits { entry := K1.answerEntry Q } [] = true := by
  have h1 : (Fmt.DeclaredRound.items { entry := K1.answerEntry Q }).filter (· != .root) =
      List.replicate Q.answers .answer := by
    simp [Fmt.DeclaredRound.items, Fmt.Entry.cut, K1.answerEntry]
  have h2 : ∀ l : List E, ((l.map fun y => (Said.answer (toE y.triple))).map fun v =>
      itemOf v.got) = List.replicate l.length .answer := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih =>
      rw [List.map_cons, List.map_cons, List.length_cons, List.replicate_succ, ih]
      rfl
  unfold Sending.fits
  rw [h1, h2, length_answersOf]
  simp

/-- The part's two moves return these two messages, at all that they are handed: never an error. -/
theorem says_send (J : SendJob) (c : (sendingPart J).Coins) (s : Seen) (t : State Ask Unit) :
    (sendingPart J).moves.map (fun mv => mv.say c s t) =
      [.ok { vals := [], tables := sentTables J.Q.codes J.Q.sent (J.rows t (coinsE c.1).toArray) },
       .ok { vals := (answersOf J.Q (J.rows t (coinsE c.1).toArray)
          (VerifiableInference.Desc.K1.cutSeeds J.Q.coordinates J.Q.seeds
            (elems (t.lately 1)))).map fun y => .answer (toE y.triple), tables := [] }] := rfl

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.send_declared
#print axioms ProofFile.Honest.K14.seed_fits
#print axioms ProofFile.Honest.K14.sum_filter_ne
#print axioms ProofFile.Honest.K14.range_answers
#print axioms ProofFile.Honest.K14.length_answersOf
#print axioms ProofFile.Honest.K14.answer_fits
#print axioms ProofFile.Honest.K14.says_send
