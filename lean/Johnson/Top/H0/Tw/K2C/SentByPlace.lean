-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/SentByPlace.lean: code switching: seatNew N m r, THE seatN OF OTHER FILES'
ASSEMBLY OF THE TIES, IS THE LAYOUT's SEAT BY PLACE: A TEST WITH CODE ON THE NUMBERS AND THE LIST OF
ROUNDS, BY PLACE, and what it gives. The test sentFitB (Tw/K2C/SentFit.lean) holds N.sent m 0
against the layout's seats AS A SET; the third tie's field «seats» wants them BY PLACE. Definitions,
and theorems with their proofs. NO SUB-PROTOCOL IMPORTS THIS FILE.
  sentPlaceB N m pIn codes sent   THE TEST: sentFitB with «the same list» in the place of «the same
                    members»: N.sent m 0 IS the list of the layout's seats of all notices but the
                    last (the fold's mask), from the tree N.treesAt pIn on, in the order of sending
  sentPlaceOn · sentPlaceAll      the test at a list of code switches, and at all 25, at the numbers
                    that P1K2.numsAt gives: sentFitOn | sentFitAll's own text
  sentPlaceB_rows   the test does not read rowsAt: its value at { N with rowsAt := R }.withTold ps
                    told, the form of the composed meaning's numbers, is its value at
                    N.withTold ps told, where the files named under LIMITS evaluate it
  sent_of_place     what an acceptance says, as an equation of lists
  sentFit_of_place · sentFitAll_of_place   IT IMPLIES sentFitB | sentFitAll: in a list of conditions
                    it can take sentFitB's place; nothing that leans on sentFitB is lost
  sentPlaceAll_at   the test at one of the 25, from the test at all
  seatNew_is_layout so seatNew N m r (K2Caller/SeatsOfN.lean: N.sent (m + 1) 0 by place) is the
                    layout's seat by place, where the typed list is no longer than that list
  hS_seatNew        THE PREMISE hS OF hAt_at_place AND ITS ARMS (Tw/K2C/TieThreeAt.lean), AT
                    seatN := seatNew N m r: the seatN at which K2Caller/TieFourPadsAt.lean pays the
                    fourth tie's hE. m: the fourth tie's; the third tie's is m + 1
LEFT, BY NAME: the test's value (closed) · hlay (closed) · hl (closed; it follows from the test on
the members: Tw/K2C/ThreeTogether.lean) · hF (two clauses of K2.Fence, at the front) · hbase at
base := N.treesAt pIn (ThreeCounts.lean: hbase_at_place).
LIMITS. A NEW TEST: its value is a premise of every theorem here; at the stored full-size example:
evaluated in Johnson/Loose/PVK2/SentPlaceAtFull.lean | SentPlaceAtNums.lean (neither in this
library). STRONGER THAN M ALONE WANTS (K2.MembersLike reads N.sent m 0
as a set): the price of seatN := seatNew at every tie. NOT COVERED AT seatNew, here or in the files
named: the second and third ties' hσ (K2.SmpLike; its payer's test newSeatsB, Tw/K2C/SmpForms.lean,
is a further demand on seatN by place) · the law at a place's hseat and the letter base of wordsMade
| k2Piece · SeatFits. That N, codes and sent are those of the program that makes the list of rounds
is said by nothing here. No soundness is claimed. On hiding nothing.
-/
import Johnson.Top.H0.Tw.K2C.TieThreeSeatsAt
import Johnson.Top.H0.Tw.K2C.SentFit
import Johnson.Top.H0.K2Caller.SeatsOfN
import Johnson.Desc.First.BookNumbers

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers sameMembers)
open VerifiableInference.Desc.First.K2Hands
open _root_.Tw.K2 (switchNotices)

/-- **The test, by place.** -/
def sentPlaceB (N : Numbers) (m : ℕ) (pIn : Option VerifiableInference.Desc.Place) (codes : Codes)
    (sent : Array OracleNotice) : Bool :=
  match layTrees codes sent with
  | none => false
  | some lay => N.sent m 0 == (List.range (sent.size - 1)).map fun i =>
      (N.treesAt pIn + lay.tree.getD i 0, lay.part.getD i 0)

/-- The test at a list of code switches, at the numbers that numsAt gives: sentFitOn's text. -/
def sentPlaceOn (spots : List (ℕ × Option ℕ × ℕ)) (N : Numbers) (P : P1K2.Prep)
    (ps : List VerifiableInference.Desc.Place) : Bool :=
  spots.all fun t =>
    match P1K2.numsAt P t.2.1 with
    | none => false
    | some n => sentPlaceB N t.1 ps[t.2.2]? n.codes n.sent

/-- **The test at all 25.** -/
def sentPlaceAll (N : Numbers) (P : P1K2.Prep) (ps : List VerifiableInference.Desc.Place) : Bool :=
  sentPlaceOn K2.switchSpots N P ps

variable {N : Numbers} {m : ℕ} {pIn : Option VerifiableInference.Desc.Place} {codes : Codes}
  {sent : Array OracleNotice} {lay₀ : TreeLay}

/-- The test does not read rowsAt. -/
theorem sentPlaceB_rows (R : ℕ → VerifiableInference.Desc.First.RowClass → ℕ × ℕ)
    (ps : List VerifiableInference.Desc.Place)
    (told : List (List VerifiableInference.Desc.Oracle)) :
    sentPlaceB ({ N with rowsAt := R }.withTold ps told) m pIn codes sent =
      sentPlaceB (N.withTold ps told) m pIn codes sent := rfl

/-- What an acceptance says. -/
theorem sent_of_place (h : sentPlaceB N m pIn codes sent = true)
    (hlay : layTrees codes sent = some lay₀) :
    N.sent m 0 = (List.range (sent.size - 1)).map fun i =>
      (N.treesAt pIn + lay₀.tree.getD i 0, lay₀.part.getD i 0) := by
  unfold sentPlaceB at h
  rw [hlay] at h
  exact beq_iff_eq.1 h

/-- It implies the test sentFitB. -/
theorem sentFit_of_place (h : sentPlaceB N m pIn codes sent = true) :
    K2.sentFitB N m pIn codes sent = true := by
  unfold sentPlaceB at h
  unfold K2.sentFitB
  split at h
  · cases h
  · rename_i lay hl
    rw [hl]
    show sameMembers _ (N.sent m 0) = true
    rw [beq_iff_eq.1 h]
    unfold sameMembers
    rw [Bool.and_self]
    exact List.all_eq_true.2 fun x hx => List.contains_iff_mem.2 hx

/-- The test at one of the 25, from the test at all. -/
theorem sentPlaceAll_at {P : P1K2.Prep} {ps : List VerifiableInference.Desc.Place}
    (h : sentPlaceAll N P ps = true) {t : ℕ × Option ℕ × ℕ} (ht : t ∈ K2.switchSpots)
    {n : P1K2.Nums} (hn : P1K2.numsAt P t.2.1 = some n) :
    sentPlaceB N t.1 ps[t.2.2]? n.codes n.sent = true := by
  have e := List.all_eq_true.1 h t ht
  rw [hn] at e
  exact e

/-- At all 25 it implies the test sentFitB at all 25 (sentFitAll). -/
theorem sentFitAll_of_place {P : P1K2.Prep} {ps : List VerifiableInference.Desc.Place}
    (h : sentPlaceAll N P ps = true) : K2.sentFitAll N P ps = true := by
  refine List.all_eq_true.2 fun t ht => ?_
  have e := List.all_eq_true.1 h t ht
  cases hn : P1K2.numsAt P t.2.1 with
  | none =>
    rw [hn] at e
    cases e
  | some n =>
    rw [hn] at e
    exact sentFit_of_place e

/-- **seatNew is the layout's seat by place.** -/
theorem seatNew_is_layout (h : sentPlaceB N (m + 1) pIn codes sent = true)
    (hlay : layTrees codes sent = some lay₀) (r : SwRow) (hl : r.l.length ≤ sent.size - 1)
    (i : Fin r.l.length) :
    seatNew N m r i = (N.treesAt pIn + lay₀.tree.getD i.val 0, lay₀.part.getD i.val 0) := by
  have hi : i.val < sent.size - 1 := Nat.lt_of_lt_of_le i.2 hl
  unfold seatNew
  rw [sent_of_place h hlay, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hi]
  rfl

/-- **hS at seatN := seatNew N m r.** -/
theorem hS_seatNew {F : Frame} {P Cells Tok : Type} {r : SwRow} (p : K2.P2)
    (enter : Rec → Except String Rec) (Mg : Meaning P (Wit Cells Tok MsgT)) (links : List ModelPart)
    (ps : List VerifiableInference.Desc.Place) (z : P) (Rch : ℕ → Rec × F.E.Str → Prop) (k : ℕ)
    (h : sentPlaceB N (m + 1) pIn codes sent = true) (hlay : layTrees codes sent = some lay₀)
    (hl : r.l.length ≤ sent.size - 1)
    (hF : ∀ a, onQ N Mg links ps (fun s => (z, s)) k a → Rch k a → ¬ a.1.failed ≠ none →
      ∀ t, enter a.1 = .ok t → ∀ fx, K2.frontAt p t = some fx →
        switchNotices fx.T fx.others = sent ∧ fx.st.codes = codes)
    (hbase : ∀ a, onQ N Mg links ps (fun s => (z, s)) k a → Rch k a → ¬ a.1.failed ≠ none →
      ∀ t, enter a.1 = .ok t → p.firstTree + t.roots = N.treesAt pIn) :
    ∀ a, onQ N Mg links ps (fun s => (z, s)) k a → Rch k a → ¬ a.1.failed ≠ none →
      ∀ t, enter a.1 = .ok t → ∀ fx, K2.frontAt p t = some fx →
        ∀ lay, layTrees fx.st.codes (switchNotices fx.T fx.others) = some lay →
          ∀ i : Fin r.l.length,
            seatNew N m r i =
              (p.firstTree + (t.roots + lay.tree.getD i.val 0), lay.part.getD i.val 0) := by
  intro a ha hrc hm t et fx hf lay hlf i
  rw [seatNew_is_layout h hlay r hl i]
  exact hS_at_place (r := r) p enter N Mg links ps z Rch k (N.treesAt pIn) codes sent lay₀ hlay hF
    hbase a ha hrc hm t et fx hf lay hlf i

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.sentPlaceB_rows
#print axioms VerifiableInference.Desc.First.K2Caller.sent_of_place
#print axioms VerifiableInference.Desc.First.K2Caller.sentFit_of_place
#print axioms VerifiableInference.Desc.First.K2Caller.sentPlaceAll_at
#print axioms VerifiableInference.Desc.First.K2Caller.sentFitAll_of_place
#print axioms VerifiableInference.Desc.First.K2Caller.seatNew_is_layout
#print axioms VerifiableInference.Desc.First.K2Caller.hS_seatNew
