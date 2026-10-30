-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/SentPromise.lean: THE SMALLNESS TEST: EVERY SEAT OF THE LIST THAT ITS LAW
TAKES OFF THE VERIFIER'S STATE IS A TENANT THAT THE SEGMENT SENDS AT MOMENT 0 OR 1: OUT OF THE FIRST
TABLE'S PROMISE. Statements with their proofs; one test with code.

Main names (namespace `VerifiableInference.Desc.First.K8`).
  `seat_placed`: a seat of `Named.seatFn` is `book.place[o]?` of a message o of `Named.msgs tl L`:
    by the make of `Named.members`.
  **`sent_of_members`**: THE CORE, in letters: under the promise's test `membersHeld N O s`
    (Johnson/Desc/First/Borders.lean), where a class of rows of segment m is open (hrow), its group
    is made (hG), `pin m 2` is not open (h2), and the messages of `Named.msgs tl L` are members of
    that group (hmem): ∀ i, ∃ t ∈ [0, 1], `Named.seatFn rad s.st s.book tl L i ∈ N.sent m t`.
  `frontOpenB links ps k l`: the test: l is among `rowSegs` of the items open at border k, and `pin
    l 2` is not among these. `frontOpenB_full`: it accepts at all twenty-five draws of the full
    size: BY LEAN'S KERNEL. `front_open_full`: the two facts, for l ≤ 24.
  `membersHeld_of_onQ`: the promise at a state without a mark holds the test. **`sent_of_onQ`**: the
    three joined, at `Sound.linksFull`, its written list of places and `drawAt l`
    (Johnson/Desc/First/K8/TiePromise.lean).

Every "there is", walked. t: one of 0, 1: tied by `seat ∈ N.sent m t`.
WHAT IS NOT PAID HERE: hG and hmem: two facts on the verifier's state in front of the draw (the
segment's group is made; the link's own and kept messages in which the arrays lie have joined it).
`Named.namedB` is not spent.
CAN THE PREMISES BE MET TOGETHER? Not shown here.
Limits. `sameMembers` compares as sets: nothing is said on how often a seat stands. Nothing on
soundness or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.K8.TiePromise
import Johnson.Desc.First.K8.LawNamed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8
open OnBytes OnBytes.Model
open OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Item Meaning Numbers start openSets rowSegs membersHeld
  sameMembers flatPlacesOf)

/-- A seat of the list is the book's place of one of the list's messages. -/
theorem seat_placed (rad : OracleShape → ℕ) (St : Statement) (book : TreeBook) (tl : HTailF2)
    (L : LinkCtx) (i : Fin (Named.listOf rad St book tl L).length) :
    ∃ o ∈ Named.msgs tl L, book.place[o]? = some (Named.seatFn rad St book tl L i) := by
  have hx : Named.seatFn rad St book tl L i ∈ Named.seatsOf St book tl L := List.get_mem _ _
  unfold Named.seatsOf at hx
  obtain ⟨x, hxm, e⟩ := List.mem_map.1 hx
  unfold Named.members at hxm
  obtain ⟨o, ho, e2⟩ := List.mem_filterMap.1 hxm
  obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 e2
  refine ⟨o, ho, ?_⟩
  rw [← e]
  unfold Named.memberAt at hy
  split at hy
  · rename_i z jt _ hp
    cases hy
    exact hp
  · cases hy

/-- **THE CORE.** -/
theorem sent_of_members (N : Numbers) (O : List Item) (s : S) (m : ℕ) (rad : OracleShape → ℕ)
    (tl : HTailF2) (L : LinkCtx) (G : Group) (hM : membersHeld N O s = true)
    (hrow : m ∈ rowSegs O) (hG : s.st.groups[N.groupAt m]? = some G)
    (h2 : O.contains (.pin m 2) = false)
    (hmem : ∀ o ∈ Named.msgs tl L, o ∈ G.members.toList) :
    ∀ i, ∃ t ∈ [0, 1], Named.seatFn rad s.st s.book tl L i ∈ N.sent m t := by
  intro i
  obtain ⟨o, ho, hp⟩ := seat_placed rad s.st s.book tl L i
  have h := List.all_eq_true.1 hM m hrow
  simp only [hG, Bool.and_eq_true] at h
  have h1 := (Bool.and_eq_true _ _ ▸ h.2 : _ ∧ _).1
  have hin : Named.seatFn rad s.st s.book tl L i ∈
      G.members.toList.filterMap fun o => s.book.place[o]? :=
    List.mem_filterMap.2 ⟨o, hmem o ho, hp⟩
  have hc := List.all_eq_true.1 h1 _ hin
  obtain ⟨t, ht, hs⟩ := List.mem_flatMap.1 (List.contains_iff_mem.1 hc)
  have ht3 : t < 3 := List.mem_range.1 ht
  by_cases hO : O.contains (.pin m t) = true
  · rw [if_pos hO] at hs
    have hne : t ≠ 2 := by
      rintro rfl
      rw [h2] at hO
      cases hO
    refine ⟨t, ?_, hs⟩
    have : t = 0 ∨ t = 1 := by omega
    rcases this with rfl | rfl <;> simp
  · rw [if_neg hO] at hs
    cases hs

/-- The test: a class of rows of the segment is open at border k, and its third pin is not. -/
def frontOpenB (links : List ModelPart) (ps : List Place) (k l : ℕ) : Bool :=
  decide (l ∈ rowSegs ((openSets links ps (start links))[k]?.getD [])) &&
    !((openSets links ps (start links))[k]?.getD []).contains (.pin l 2)

theorem frontOpenB_full :
    ((List.range 25).all fun l =>
      frontOpenB linksFull (flatPlacesOf linksFull true) (drawAt l) l) = true := by
  decide +kernel

/-- **THE CLOSED FACTS**, at the full size, in front of kind K8's draw of every segment. -/
theorem front_open_full (l : ℕ) (hl : l ≤ 24) :
    l ∈ rowSegs ((openSets linksFull (flatPlacesOf linksFull true)
        (start linksFull))[drawAt l]?.getD []) ∧
      ((openSets linksFull (flatPlacesOf linksFull true)
        (start linksFull))[drawAt l]?.getD []).contains (.pin l 2) = false := by
  have h := List.all_eq_true.1 frontOpenB_full l (List.mem_range.2 (Nat.lt_succ_of_le hl))
  unfold frontOpenB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  exact h

/-- The promise at a state without a mark holds the test on the groups' members. -/
theorem membersHeld_of_onQ {A P W : Type} {Fr : Frame} (N : Numbers) (Mg : Meaning P W)
    (links : List ModelPart) (ps : List Place) (get : A → P × First.S) (k : ℕ) (a : A × Fr.E.Str)
    (h : onQ N Mg links ps get k a) (hm : (get a.1).2.failed = none) :
    membersHeld N ((openSets links ps (start links))[k]?.getD []) (get a.1).2 = true := by
  rcases h.2 with h' | h'
  · exact absurd hm h'
  · have e := h'.1
    simp only [Bool.and_eq_true] at e
    exact e.1.1.1.2

/-- **OUT OF THE PROMISE, AT THE FULL SIZE, IN FRONT OF THE DRAW OF SEGMENT l.** -/
theorem sent_of_onQ {A P W : Type} {Fr : Frame} (N : Numbers) (Mg : Meaning P W)
    (get : A → P × First.S) (l : ℕ) (hl : l ≤ 24) (a : A × Fr.E.Str)
    (h : onQ N Mg linksFull (flatPlacesOf linksFull true) get (drawAt l) a)
    (hm : (get a.1).2.failed = none) (rad : OracleShape → ℕ) (tl : HTailF2) (L : LinkCtx)
    (G : Group) (hG : (get a.1).2.st.groups[N.groupAt l]? = some G)
    (hmem : ∀ o ∈ Named.msgs tl L, o ∈ G.members.toList) :
    ∀ i, ∃ t ∈ [0, 1],
      Named.seatFn rad (get a.1).2.st (get a.1).2.book tl L i ∈ N.sent l t :=
  sent_of_members N _ _ l rad tl L G (membersHeld_of_onQ N Mg _ _ get _ a h hm)
    (front_open_full l hl).1 hG (front_open_full l hl).2 hmem

end VerifiableInference.Desc.First.K8

#print axioms VerifiableInference.Desc.First.K8.seat_placed
#print axioms VerifiableInference.Desc.First.K8.sent_of_members
#print axioms VerifiableInference.Desc.First.K8.frontOpenB_full
#print axioms VerifiableInference.Desc.First.K8.front_open_full
#print axioms VerifiableInference.Desc.First.K8.membersHeld_of_onQ
#print axioms VerifiableInference.Desc.First.K8.sent_of_onQ
