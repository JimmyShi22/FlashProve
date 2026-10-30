-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K6/Law/FrontScalars.lean: THE OUTPUT HEAD's OWN SUB-PROTOCOL (K6):
UNDER THE HYPOTHESIS h (`P5J.AtMgA`, Johnson/P5J/MgAtAll.lean): THE PARTS OF SEGMENT 24 THAT STAND
IN FRONT OF K6's PLACE, AS THE MAKER OF THE BOOK OF COINS CUTS THEM, HAVE 1,995 SCALARS OF THEIR
OWN; AND K6's MEMBER IS THERE. One definition, on public data; ten theorems.

  `partsOfEntries`      A SECOND TEXT OF `planParts` (Honest/BookEntries.lean), as a function of
                        what that reads of a sub-protocol: its place and its rounds' entries
  `k6_planParts_is`     GENERAL, NO HYPOTHESIS: THE TIE: planParts b is that function at b's own
  `k6_own_append`       GENERAL: the own scalars of two lists of parts add up
  `k6_drop_cons`        GENERAL: a list from its member number n on
  `k6_sel`              GENERAL: a filter and a takeWhile at a list of which five members are named
  `k6_front_closed`     A CLOSED FACT, BY LEAN's KERNEL: at the written entries the four members in
                        front have 0, 0, 0 and 1,995 scalars of their own
  `k6_links_closed`     A CLOSED FACT: none of the written cut's first 337 rows stands in link 24;
                        the cut has 358 rows
  `k6_member_get`       under h: the first chain's flat list has a member at every number below 358
  `k6_place_341`        under h: member 341 stands at K6's place
  `k6_member_there`     under h: a member of the flat list stands at K6's place
  `k6_front_scalars`    **under h: ownScalarsOf (partsInFront cF.blocksInOrder 24 IM.k6Place) = 1995**

By. `k6_entries_337` … `k6_entries_340`, `k6_member_at` (Honest/K6/Law/RoundsWritten.lean);
`pins_of_laid` (Johnson/Goal/Skeleton/PinsOfLaid.lean); `ownScalarsOf`, `partsInFront`,
`ownScalarsOf_cons` (Honest/BookRowKit.lean).

Limits.
  * `partsOfEntries` IS A SECOND TEXT, OF PUBLIC DATA, written so that Lean's kernel can evaluate it
    at closed letters: the tie, not the eye, holds it to the first.
  * THE NUMERALS REST ON EVALUATIONS IN LEAN's KERNEL (`decide +kernel`) over the library's written
    rows and entries, under a raised `maxRecDepth`: two here at the two closed facts, two more in
    `k6_place_341`.
  * h: the full size and the format's second hash function alone.
  * Public numbers alone: nothing on a coin, an entry of the book, a value or a run.
  * It imports by name no module under lean/Johnson/Goal/; IT CALLS `pins_of_laid`, WHICH IS
    DECLARED THERE; such modules lie in its import closure.
  * Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.BookRowKit
import Johnson.Desc.ProofFile.Honest.K6.Law.RoundsWritten
import Johnson.IMR.K6Seat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K6
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.PlanWritten (cutOf cutFirstFull)
open OnBytes.Maker (WholeD)

/-- **A second text of `planParts`**, as a function of the place and the rounds' entries. Public
data alone. -/
def partsOfEntries (pl : Place) (es : List Fmt.Entry) : List PartAt :=
  (stretchesBy (es.map fun e => (e.name, (e.msg - 32 * e.roots - 24 * e.answers) / 24))
    (cutOfNames pl.kind (es.map (·.name)))).zipIdx.map fun y => ⟨⟨pl, y.2⟩, y.1⟩

/-- GENERAL, NO HYPOTHESIS. **The tie.** -/
theorem k6_planParts_is {S Cl : Type} (b : Block S Cl) :
    planParts b = partsOfEntries b.place (b.rounds.map (·.entry)) := by
  unfold planParts partsOfEntries partsCut
  rw [List.map_map, List.map_map]
  rfl

/-- GENERAL. The own scalars of two lists of parts add up. -/
theorem k6_own_append (A B : List PartAt) :
    ownScalarsOf (A ++ B) = ownScalarsOf A + ownScalarsOf B := by
  induction A with
  | nil =>
    rw [List.nil_append]
    show ownScalarsOf B = 0 + ownScalarsOf B
    omega
  | cons q A ih =>
    rw [List.cons_append, BookRow.ownScalarsOf_cons, BookRow.ownScalarsOf_cons, ih]
    omega

/-- GENERAL. A list from its member number n on. -/
theorem k6_drop_cons {α : Type} : ∀ {l : List α} {n : Nat} {a : α}, l[n]? = some a →
    l.drop n = a :: l.drop (n + 1)
  | [], _, _, h => by simp at h
  | y :: ys, 0, a, h => by
    have e : y = a := by simpa using h
    rw [e]
    rfl
  | y :: ys, n + 1, a, h => by
    have h' : ys[n]? = some a := by simpa using h
    simpa using k6_drop_cons h'

/-- GENERAL. Of a list whose front the filter empties and whose next five members it keeps, the
takeWhile that stops at the fifth leaves the four. -/
theorem k6_sel {α : Type} (f g : α → Bool) (A R : List α) (a0 a1 a2 a3 a4 : α)
    (hA : A.filter f = []) (f0 : f a0 = true) (f1 : f a1 = true) (f2 : f a2 = true)
    (f3 : f a3 = true) (f4 : f a4 = true) (g0 : g a0 = true) (g1 : g a1 = true)
    (g2 : g a2 = true) (g3 : g a3 = true) (g4 : g a4 = false) :
    ((A ++ a0 :: a1 :: a2 :: a3 :: a4 :: R).filter f).takeWhile g = [a0, a1, a2, a3] := by
  simp [List.filter_append, hA, f0, f1, f2, f3, f4, g0, g1, g2, g3, g4]

set_option maxRecDepth 1000000 in
/-- **A closed fact at the library's written entries**: the own scalars of the four members of
segment 24 in front of K6. -/
theorem k6_front_closed :
    ownScalarsOf (partsOfEntries ⟨1, some 24, 0, .frame⟩ ((P5T.esFull.1.drop 46286).take 0)) = 0 ∧
    ownScalarsOf (partsOfEntries ⟨1, some 24, 1, .K7⟩ ((P5T.esFull.1.drop 46286).take 1)) = 0 ∧
    ownScalarsOf (partsOfEntries ⟨1, some 24, 2, .K2⟩ ((P5T.esFull.1.drop 46287).take 2)) = 0 ∧
    ownScalarsOf (partsOfEntries ⟨1, some 24, 3, .K3⟩ ((P5T.esFull.1.drop 46289).take 1080)) =
      1995 := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **A closed fact at the library's written cut**: none of its first 337 rows stands in link 24; it
has 358 rows. -/
theorem k6_links_closed :
    ((cutFirstFull.take 337).all fun y => y.2.1.link != some 24) = true ∧
      cutFirstFull.length = 358 := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- CONDITIONAL: the hypothesis h. The flat list has a member at every number below 358. -/
theorem k6_member_get (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {n : Nat} (hn : n < 358) :
    ∃ b, cF.blocksInOrder[n]? = some b := by
  have hc : cutOf cF.blocksInOrder = cutFirstFull := (P5J.pins_of_laid h.scope h.laid).2
  have hl : cF.blocksInOrder.length = 358 := by
    have e := congrArg List.length hc
    unfold cutOf at e
    rw [List.length_map, k6_links_closed.2] at e
    exact e
  exact ⟨cF.blocksInOrder[n]'(by omega), List.getElem?_eq_getElem (by omega)⟩

set_option maxRecDepth 100000 in
/-- CONDITIONAL: h; hb. Member 341 stands at K6's place. -/
theorem k6_place_341 (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    {b : Block P5J.TS ProofFile.Cl} (hb : cF.blocksInOrder[341]? = some b) : b.place = IM.k6Place :=
  (k6_member_at (p := ⟨1, some 24, 4, .K6⟩) (len := 82) (pre := 47369) h hb (by decide +kernel)
    (by decide +kernel)).1

/-- CONDITIONAL: the hypothesis h. **K6's member is there.** -/
theorem k6_member_there (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∃ b ∈ cF.blocksInOrder, b.place = IM.k6Place := by
  obtain ⟨b, hb⟩ := k6_member_get h (n := 341) (by omega)
  exact ⟨b, List.mem_of_getElem? hb, k6_place_341 h hb⟩

/-- CONDITIONAL: the hypothesis h. **The parts of segment 24 in front of K6's place have 1,995
scalars of their own.** -/
theorem k6_front_scalars (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ownScalarsOf (partsInFront cF.blocksInOrder 24 IM.k6Place) = 1995 := by
  have hc : cutOf cF.blocksInOrder = cutFirstFull := (P5J.pins_of_laid h.scope h.laid).2
  obtain ⟨b0, h0⟩ := k6_member_get h (n := 337) (by omega)
  obtain ⟨b1, h1⟩ := k6_member_get h (n := 338) (by omega)
  obtain ⟨b2, h2⟩ := k6_member_get h (n := 339) (by omega)
  obtain ⟨b3, h3⟩ := k6_member_get h (n := 340) (by omega)
  obtain ⟨b4, h4⟩ := k6_member_get h (n := 341) (by omega)
  obtain ⟨p0, e0⟩ := k6_entries_337 h h0
  obtain ⟨p1, e1⟩ := k6_entries_338 h h1
  obtain ⟨p2, e2⟩ := k6_entries_339 h h2
  obtain ⟨p3, e3⟩ := k6_entries_340 h h3
  have p4 := k6_place_341 h h4
  -- the flat list, cut at 337
  have ecut : cF.blocksInOrder = cF.blocksInOrder.take 337 ++ b0 :: b1 :: b2 :: b3 :: b4 :: cF.blocksInOrder.drop 342 := by
    have d0 : cF.blocksInOrder.drop 337 = b0 :: cF.blocksInOrder.drop 338 := k6_drop_cons h0
    have d1 : cF.blocksInOrder.drop 338 = b1 :: cF.blocksInOrder.drop 339 := k6_drop_cons h1
    have d2 : cF.blocksInOrder.drop 339 = b2 :: cF.blocksInOrder.drop 340 := k6_drop_cons h2
    have d3 : cF.blocksInOrder.drop 340 = b3 :: cF.blocksInOrder.drop 341 := k6_drop_cons h3
    have d4 : cF.blocksInOrder.drop 341 = b4 :: cF.blocksInOrder.drop 342 := k6_drop_cons h4
    rw [← d4, ← d3, ← d2, ← d1, ← d0]
    exact (List.take_append_drop 337 cF.blocksInOrder).symm
  -- none of the first 337 stands in link 24
  have hfront : (cF.blocksInOrder.take 337).filter (fun b => b.place.link == some 24) = [] := by
    rw [List.filter_eq_nil_iff]
    intro a ha hq
    have hall := k6_links_closed.1
    rw [← hc] at hall
    unfold cutOf at hall
    rw [← List.map_take, List.all_map] at hall
    have h5 : (a.place.link != some 24) = true := List.all_eq_true.1 hall a ha
    exact absurd h5 (by simp [bne, hq])
  obtain ⟨c0, c1, c2, c3⟩ := k6_front_closed
  have f0 : (b0.place.link == some 24) = true := by rw [p0]; rfl
  have f1 : (b1.place.link == some 24) = true := by rw [p1]; rfl
  have f2 : (b2.place.link == some 24) = true := by rw [p2]; rfl
  have f3 : (b3.place.link == some 24) = true := by rw [p3]; rfl
  have f4 : (b4.place.link == some 24) = true := by rw [p4]; rfl
  have g0 : (b0.place != IM.k6Place) = true := by rw [p0]; decide
  have g1 : (b1.place != IM.k6Place) = true := by rw [p1]; decide
  have g2 : (b2.place != IM.k6Place) = true := by rw [p2]; decide
  have g3 : (b3.place != IM.k6Place) = true := by rw [p3]; decide
  have g4 : (b4.place != IM.k6Place) = false := by rw [p4]; decide
  have esel : ((cF.blocksInOrder.filter fun b => b.place.link == some 24).takeWhile
      fun b => b.place != IM.k6Place) = [b0, b1, b2, b3] := by
    rw [ecut]
    exact k6_sel (fun b => b.place.link == some 24) (fun b => b.place != IM.k6Place) _ _ b0 b1 b2 b3
      b4 hfront f0 f1 f2 f3 f4 g0 g1 g2 g3 g4
  unfold partsInFront
  rw [esel]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [k6_own_append, k6_own_append, k6_own_append, k6_planParts_is b0, k6_planParts_is b1,
    k6_planParts_is b2, k6_planParts_is b3, p0, p1, p2, p3, e0, e1, e2, e3, c0, c1, c2, c3]

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.partsOfEntries
#print axioms ProofFile.Honest.K6.k6_planParts_is
#print axioms ProofFile.Honest.K6.k6_own_append
#print axioms ProofFile.Honest.K6.k6_drop_cons
#print axioms ProofFile.Honest.K6.k6_sel
#print axioms ProofFile.Honest.K6.k6_front_closed
#print axioms ProofFile.Honest.K6.k6_links_closed
#print axioms ProofFile.Honest.K6.k6_member_get
#print axioms ProofFile.Honest.K6.k6_place_341
#print axioms ProofFile.Honest.K6.k6_member_there
#print axioms ProofFile.Honest.K6.k6_front_scalars
