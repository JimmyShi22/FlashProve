-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/HeldAtOpening.lean: TWO CLAUSES OF THE PROMISE OF THE TABLE OF JOINTS
(Johnson/Desc/First/Borders.lean: `rowsHeld`, `membersHeld`) BEHIND THE BLOCK NAMED "G0:1"
(`openingZero`, Johnson/Desc/K1/Law/OpeningZero.lean): the first block of the chain at which they
are not idle. Statements with their proofs.
Main names:
  `sameMembers_iff`, `rowsDue_zero`: on the table's own two functions.
  `openingZero_group`: what the joined block does to the groups (`Opened`,
    Johnson/Desc/K1/Law/GroupAtRecord.lean).
  `openingZero_rowsHeld`: **the rows**: where segment 0's is the one segment with an open class of
    rows behind, none of its open classes lies in the group's list, and THE PLAN's NUMBER OF SEGMENT
    0's GROUP IS THE NUMBER OF GROUPS IN FRONT.
  `openingZero_membersHeld`: **the members**: where besides the book in front has a place for every
    message, and the plan's tenants whose pins are open behind are just the seats of the segment's
    own messages (`ownSeatsB`: a test with code on the plan, AT THE RECORD's OWN COUNT OF THESE
    MESSAGES AND OF THE BOOK's TREES).

MARK: WHAT THE PROMISE IN FRONT DOES NOT GIVE (by reading `onAt`): (i) how many groups the
statement has in front of this block; (ii) how many messages of its own the record's frame has at
the first moment (`s.check.frame.atMoment 0`: the block tests its announcement against the plan's
as one list, not this count). Both are premises here. Both are true of the chain's first record by
its make: so they can stand in the sentence of `Pub.noneSent`, which is open from the start to
this block.

What is not claimed. These premises. The promise's other clauses behind the block. Nothing on
soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K1.Law.GroupAtRecord
import Johnson.Desc.First.Borders

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open VerifiableInference.Desc.First (S Item Numbers)
open Johnson.Desc.First.Walk (LayPar)
open Johnson.Desc.First.Walk.Tied (openedZeroGives)

variable {Cl : Type}

/-- Two lists have the same members. -/
theorem sameMembers_iff (a b : List (Nat × Nat)) :
    First.sameMembers a b = true ↔ ∀ x, x ∈ a ↔ x ∈ b := by
  unfold First.sameMembers
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
  constructor
  · rintro ⟨h1, h2⟩ x
    exact ⟨fun hx => List.contains_iff_mem.1 (h1 x hx), fun hx => List.contains_iff_mem.1 (h2 x hx)⟩
  · intro h
    exact ⟨fun x hx => List.contains_iff_mem.2 ((h x).1 hx),
      fun x hx => List.contains_iff_mem.2 ((h x).2 hx)⟩

/-- Where no open class of segment m lies in the group's list, the list is due no row. -/
theorem rowsDue_zero (N : Numbers) (m : Nat) : ∀ (O : List Item),
    (∀ c, Item.row m c ∈ O → c.inList = false) → First.rowsDue N O m = 0 := by
  have key : ∀ (O : List Item) (k : Nat), (∀ c, Item.row m c ∈ O → c.inList = false) →
      O.foldl (fun k i => match i with
        | .row m' c => if m' == m && c.inList then k + (N.rowsAt m c).2 else k
        | _ => k) k = k := by
    intro O
    induction O with
    | nil => intro k _; rfl
    | cons i O ih =>
      intro k h
      have hO := ih k fun c hc => h c (List.mem_cons_of_mem _ hc)
      rw [List.foldl_cons]
      cases i with
      | row m' c =>
        have hk : (if m' == m && c.inList then k + (N.rowsAt m c).2 else k) = k := by
          by_cases e : m' = m
          · subst e
            rw [h c List.mem_cons_self]
            simp
          · simp [e]
        show List.foldl _ (if m' == m && c.inList then k + (N.rowsAt m c).2 else k) O = k
        rw [hk]
        exact hO
      | _ => exact hO
  intro O h
  exact key O 0 h

/-- What the joined block does to the groups. -/
theorem openingZero_group {q : Params.First} {gp : GPar} {nm : String} {X : LayPar}
    {fvs : List Bool} {kCol : Nat} {s t : S} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (openingZero q gp nm X fvs kCol : Block S Cl).decide s [r₁, r₂] gs = .ok t) :
    Opened s.st (s.check.frame.atMoment 0).length t.st ∧
      (s.check.frame.atMoment 0).length < (firstPar q gp).sent.size := by
  obtain ⟨s₁, g₁, h1, h2⟩ := openingZero_mid h
  obtain ⟨_, _, ⟨_, _, e3, _⟩, _⟩ := openedZeroGives X fvs kCol s₁ t h2
  obtain ⟨a, _, b⟩ := firstAtS_group q gp s s₁ r₁ r₂ g₁ h1
  rw [e3]
  exact ⟨a, b⟩

/-- **THE ROWS.** -/
theorem openingZero_rowsHeld {q : Params.First} {gp : GPar} {nm : String} {X : LayPar}
    {fvs : List Bool} {kCol : Nat} {s t : S} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (openingZero q gp nm X fvs kCol : Block S Cl).decide s [r₁, r₂] gs = .ok t)
    (N : Numbers) (O : List Item) (hseg : First.rowSegs O = [0])
    (hno : ∀ c, Item.row 0 c ∈ O → c.inList = false) (hg : N.groupAt 0 = s.st.groups.size) :
    First.rowsHeld N O t = true := by
  obtain ⟨G, g1, g2, g3, _⟩ := (openingZero_group h).1.made
  unfold First.rowsHeld
  rw [hseg, List.all_cons, List.all_nil, Bool.and_true, hg, g1]
  show (!G.inRun && G.rows.size == First.rowsDue N O 0 && O.all _) = true
  rw [g2, g3, rowsDue_zero N 0 O hno]
  simp only [Bool.not_false, Bool.true_and, Array.size_empty, beq_self_eq_true]
  refine List.all_eq_true.2 fun i hi => ?_
  cases i with
  | row m' c =>
    show (!(m' == 0 && c.inList) || _) = true
    by_cases e : m' = 0
    · subst e
      rw [hno c hi]
      simp
    · simp [e]
  | _ => rfl

/-- **The plan's tenants whose pins are open are just the seats of the segment's own messages**: a
test with code: own: how many these are; nT: the book's trees in front. -/
def ownSeatsB (N : Numbers) (O : List Item) (P : Par) (own nT : Nat) : Bool :=
  First.sameMembers
    ((List.range own).map fun i => (nT + (layOf P).tree.getD i 0, (layOf P).part.getD i 0))
    ((List.range 3).flatMap fun t => if O.contains (.pin 0 t) then N.sent 0 t else [])

/-- **THE MEMBERS.** -/
theorem openingZero_membersHeld {q : Params.First} {gp : GPar} {nm : String} {X : LayPar}
    {fvs : List Bool} {kCol : Nat} {s t : S} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (openingZero q gp nm X fvs kCol : Block S Cl).decide s [r₁, r₂] gs = .ok t)
    (N : Numbers) (O : List Item) (hseg : First.rowSegs O = [0])
    (hg : N.groupAt 0 = s.st.groups.size) (hb : s.book.place.size = s.st.oracles.size)
    (hP : ownSeatsB N O (firstPar q gp) (s.check.frame.atMoment 0).length s.book.trees.size =
      true) :
    First.membersHeld N O t = true := by
  obtain ⟨⟨_, _, G, g1, _, _, g4⟩, hlt⟩ := openingZero_group h
  have hB := (openingZero_rec h).2.2.2.2.1
  have hplace : ∀ i, i < (s.check.frame.atMoment 0).length →
      t.book.place[s.st.oracles.size + i]? = some (s.book.trees.size +
        (layOf (firstPar q gp)).tree.getD i 0, (layOf (firstPar q gp)).part.getD i 0) :=
    fun i hi => hB.newer hb (by omega)
  unfold First.membersHeld
  rw [hseg, List.all_cons, List.all_nil, Bool.and_true, hg, g1]
  show (G.members.toList.all (fun o => (t.book.place[o]?).isSome) &&
    First.sameMembers (G.members.toList.filterMap fun o => t.book.place[o]?) _) = true
  rw [Bool.and_eq_true]
  refine ⟨List.all_eq_true.2 fun o ho => ?_, (sameMembers_iff _ _).2 fun x => ?_⟩
  · obtain ⟨o1, o2⟩ := (g4 o).1 ho
    have e := hplace (o - s.st.oracles.size) (by omega)
    rw [show s.st.oracles.size + (o - s.st.oracles.size) = o by omega] at e
    rw [e]
    rfl
  · rw [← (sameMembers_iff _ _).1 hP x, List.mem_filterMap, List.mem_map]
    constructor
    · rintro ⟨o, ho, hx⟩
      obtain ⟨o1, o2⟩ := (g4 o).1 ho
      have e := hplace (o - s.st.oracles.size) (by omega)
      rw [show s.st.oracles.size + (o - s.st.oracles.size) = o by omega, hx] at e
      exact ⟨o - s.st.oracles.size, List.mem_range.2 (by omega), (Option.some.inj e).symm⟩
    · rintro ⟨i, hi, rfl⟩
      have hi' := List.mem_range.1 hi
      exact ⟨s.st.oracles.size + i, (g4 _).2 ⟨by omega, by omega⟩, hplace i hi'⟩

end VerifiableInference.Desc.K1
