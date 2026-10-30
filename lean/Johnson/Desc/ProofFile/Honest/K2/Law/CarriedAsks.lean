-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/CarriedAsks.lean: the kind "the code switch" (K2): THE KIND's
TESTS ON THE BOOK's CARRYING ENTRIES, AS NAMED TESTS WITH CODE, PLACE BY PLACE OVER THE KIND's LOT:
the book's entries by which a switch's part carries, in the book's order, held against the part's
own list (`SwitchPlace.front`, Honest/K2/Half.lean), number by number. PUBLIC DATA ALONE: a book,
places, counts. Definitions; statements with their proofs.

  `switchRunAt`       the whole run of a message in the sending of the switch whose part stands at
                      an address; nothing where no place of the list has its part there
  `carriedEntryFits`  at one place and one member of its front: the entry of that number has the
                      member's name, owner and count; and, where `switchRunAt` answers, that run
  `carriedFits`       THE TEST AT ONE PLACE: as many entries as members; each in its place
  `carriedSame`       A SECOND TEST, AT TWO PLACES: number by number, the second's entries name the
                      runs that the first's name
  `switchCarriedAsks` for whoever evaluates at a policy file and a book: all named tests
  `allNumbered_at`        a tool
  `carriedFits_at`    what the first test's yes gives at one member
  `carriedFits_named` so the entries' names and counts ARE `p.carries`: what the frame's `lend`
                      walks in step: it refuses there neither by name nor by count nor by the
                      lists' lengths
  `carriedFits_entry`, `carriedFits_run`, `switchRunAt_of`   owner and count; the run
  `carriedSame_gives` what the second test's yes gives
  `frontOf_prefix`, `switchFront_is`, `front_prefix`   at two places of the lot, the one with the
                      smaller link's front is a beginning of the other's
  `switchCarriedAsks_facts`   where every named test says yes

THE HOLE. At an owner that is no switch (the first segment's messages are the shared sending's)
`switchRunAt` answers nothing, and the first test holds name, owner and count alone: NOT THE START.
The second test has no such hole: it compares one place's entry with the other place's and never
asks which run that is.

THE SECOND TEST PRESUMES THE ORDER OF SENDING: that what a switch carries is, number by number, a
beginning of what a later switch carries. `front_prefix` says so of our own lists. Of a book's
entries it is what the test asks.

By: `entryRunIs`, `entryRunIs_gives` (Honest/Small/EntryRunIs.lean) · `carryE`
(Honest/Law/Rule/Cell.lean, the frame's authors'): the list that `lendPart` hands `lend`. Kin:
`switchBookAsks` (Honest/K2/Law/PlanBook.lean): the kind's tests on the entries whose OWNER is a
switch's part: it reads runs, no name and no number.

Limits. The tests are evaluated nowhere here: whoever evaluates lays the description's own book.
`lend` can refuse at a fourth place, the cut of the owner's run: not touched here. Nothing on the
entries by which a part spends. Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.K2.Half
import Johnson.Desc.ProofFile.Honest.K2.Fresh
import Johnson.Desc.ProofFile.Honest.Small.EntryRunIs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2

/-! ## 1 The tests -/

/-- The whole run of message number m in the sending of the switch whose part stands at a; nothing
where no place of the list has its part there. -/
def switchRunAt (ps : List SwitchPlace) (a : Addr) (m : Nat) : Option (Due × Due) :=
  (ps.find? fun p₀ => (⟨p₀.place, 0⟩ : Addr) == a).map fun p₀ =>
    wholeRun p₀.sizes.codes (switchSent p₀.sizes p₀.others)
      (switchFresh p₀.sizes p₀.others p₀.foldVars) m

/-- At one place and one member x = (owner, message, count) of its front, number i. Two
sources state the count, the member of the front and the owner's sending: the entry's is compared
with each. -/
def carriedEntryFits (Bk : ProverCoinCounts) (ps : List SwitchPlace) (p : SwitchPlace) (i : Nat)
    (x : Addr × Nat × Due) : Bool :=
  (((carryE Bk ⟨p.place, 0⟩)[i]?).any fun e =>
    e.name == carriedName x.1 x.2.1 ⟨p.place, 0⟩ && e.owner == x.1 && e.count == x.2.2) &&
    (switchRunAt ps x.1 x.2.1).all fun r => entryRunIs (carryE Bk ⟨p.place, 0⟩) i x.1 r.1 r.2

/-- **THE TEST AT ONE PLACE**: as many entries as members; each in its place. -/
def carriedFits (Bk : ProverCoinCounts) (ps : List SwitchPlace) (p : SwitchPlace) : Bool :=
  (carryE Bk ⟨p.place, 0⟩).length == p.front.length &&
    p.front.zipIdx.all fun y => carriedEntryFits Bk ps p y.2 y.1

/-- **A SECOND TEST, AT TWO PLACES**: number by number, what p carries names the runs that p₀'s
entries name: whichever runs these are: so it has no hole at an owner that is no switch. -/
def carriedSame (Bk : ProverCoinCounts) (p₀ p : SwitchPlace) : Bool :=
  (carryE Bk ⟨p₀.place, 0⟩).zipIdx.all fun y =>
    entryRunIs (carryE Bk ⟨p.place, 0⟩) y.2 y.1.owner y.1.start y.1.count

/-- **ALL NAMED TESTS OF THE KIND's LOT**, place by place. -/
def switchCarriedAsks (Z : Pub) (G : Ground) (Bk : ProverCoinCounts) : List (String × Bool) :=
  (switchPlaces Z G).map fun p =>
    ("K2, into group " ++ toString p.link ++ ": the book's carried entries",
      carriedFits Bk (switchPlaces Z G) p &&
        (switchPlaces Z G).all fun p₀ => decide (p.link < p₀.link) || carriedSame Bk p₀ p)

/-! ## 2 What their yes gives -/

/-- A test that holds of a numbered list holds at each member, by its number. -/
theorem allNumbered_at {α : Type} (f : α × Nat → Bool) :
    ∀ (l : List α) (s : Nat), (l.zipIdx s).all f = true →
      ∀ (i : Nat) (x : α), l[i]? = some x → f (x, s + i) = true
  | [], _, _, i, x, hx => by simp at hx
  | a :: l, s, h, i, x, hx => by
    rw [List.zipIdx_cons, List.all_cons, Bool.and_eq_true] at h
    cases i with
    | zero =>
      have e : a = x := by simpa using hx
      rw [← e]
      exact h.1
    | succ n =>
      have e : s + (n + 1) = s + 1 + n := by omega
      rw [e]
      exact allNumbered_at f l (s + 1) h.2 n x (by simpa using hx)

/-- **At one member.** -/
theorem carriedFits_at {Bk : ProverCoinCounts} {ps : List SwitchPlace} {p : SwitchPlace}
    (h : carriedFits Bk ps p = true) {i : Nat} {x : Addr × Nat × Due}
    (hx : p.front[i]? = some x) :
    ∃ e, (carryE Bk ⟨p.place, 0⟩)[i]? = some e ∧ e.name = carriedName x.1 x.2.1 ⟨p.place, 0⟩ ∧
      e.owner = x.1 ∧ e.count = x.2.2 ∧
      ∀ r, switchRunAt ps x.1 x.2.1 = some r → e.start = r.1 ∧ e.count = r.2 := by
  unfold carriedFits at h
  rw [Bool.and_eq_true] at h
  have hf := allNumbered_at (fun y => carriedEntryFits Bk ps p y.2 y.1) p.front 0 h.2 i x hx
  rw [Nat.zero_add] at hf
  have hf' : carriedEntryFits Bk ps p i x = true := hf
  unfold carriedEntryFits at hf'
  rw [Bool.and_eq_true] at hf'
  cases he : (carryE Bk ⟨p.place, 0⟩)[i]? with
  | none =>
    rw [he] at hf'
    simp only [Option.any_none, Bool.false_eq_true, false_and] at hf'
  | some e =>
    have h1 := hf'.1
    rw [he] at h1
    simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq] at h1
    refine ⟨e, rfl, h1.1.1, h1.1.2, h1.2, fun r hr => ?_⟩
    have h2 := hf'.2
    rw [hr] at h2
    obtain ⟨e', he', -, t2, t3⟩ := entryRunIs_gives (show entryRunIs _ i x.1 r.1 r.2 = true from h2)
    rw [he] at he'
    have ee : e = e' := Option.some.inj he'
    rw [ee]
    exact ⟨t2, t3⟩

/-- **WHAT `lend` WALKS IN STEP.** -/
theorem carriedFits_named {Bk : ProverCoinCounts} {ps : List SwitchPlace} {p : SwitchPlace}
    (h : carriedFits Bk ps p = true) : (carryE Bk ⟨p.place, 0⟩).map (·.named) = p.carries := by
  have hl : (carryE Bk ⟨p.place, 0⟩).length = p.front.length := by
    have h' := h
    unfold carriedFits at h'
    rw [Bool.and_eq_true] at h'
    exact beq_iff_eq.1 h'.1
  apply List.ext_getElem?
  intro i
  unfold SwitchPlace.carries
  rw [List.getElem?_map, List.getElem?_map]
  cases hx : p.front[i]? with
  | none =>
    have hi : p.front.length ≤ i := List.getElem?_eq_none_iff.1 hx
    rw [List.getElem?_eq_none_iff.2 (by omega)]
    rfl
  | some x =>
    obtain ⟨e, he, t1, -, t3, -⟩ := carriedFits_at h hx
    rw [he]
    show some (e.name, e.count) = some (carriedName x.1 x.2.1 ⟨p.place, 0⟩, x.2.2)
    rw [t1, t3]

theorem carriedFits_entry {Bk : ProverCoinCounts} {ps : List SwitchPlace} {p : SwitchPlace}
    (h : carriedFits Bk ps p = true) {i : Nat} {x : Addr × Nat × Due}
    (hx : p.front[i]? = some x) :
    ∃ e, (carryE Bk ⟨p.place, 0⟩)[i]? = some e ∧ e.owner = x.1 ∧ e.count = x.2.2 := by
  obtain ⟨e, he, -, t2, t3, -⟩ := carriedFits_at h hx
  exact ⟨e, he, t2, t3⟩

theorem carriedFits_run {Bk : ProverCoinCounts} {ps : List SwitchPlace} {p : SwitchPlace}
    (h : carriedFits Bk ps p = true) {i : Nat} {x : Addr × Nat × Due}
    (hx : p.front[i]? = some x) {r : Due × Due} (hr : switchRunAt ps x.1 x.2.1 = some r) :
    ∃ e, (carryE Bk ⟨p.place, 0⟩)[i]? = some e ∧ e.owner = x.1 ∧ e.start = r.1 ∧ e.count = r.2 := by
  obtain ⟨e, he, -, t2, -, t⟩ := carriedFits_at h hx
  exact ⟨e, he, t2, (t r hr).1, (t r hr).2⟩

/-- The run, at the first place of the list whose part stands at the address. -/
theorem switchRunAt_of {ps : List SwitchPlace} {a : Addr} {p₀ : SwitchPlace}
    (h : (ps.find? fun q => (⟨q.place, 0⟩ : Addr) == a) = some p₀) (m : Nat) :
    switchRunAt ps a m = some
      (dueBefore p₀.sizes.codes (switchSent p₀.sizes p₀.others)
        (switchFresh p₀.sizes p₀.others p₀.foldVars) m,
      messageDue p₀.sizes.codes ((switchSent p₀.sizes p₀.others).getD m default).shape
        (foldAt (switchFresh p₀.sizes p₀.others p₀.foldVars) m)) := by
  unfold switchRunAt
  rw [h]
  rfl

/-- **What the second test's yes gives.** -/
theorem carriedSame_gives {Bk : ProverCoinCounts} {p₀ p : SwitchPlace} (h : carriedSame Bk p₀ p = true)
    (i : Nat) (e₀ : Ahead) (he₀ : (carryE Bk ⟨p₀.place, 0⟩)[i]? = some e₀) :
    ∃ e, (carryE Bk ⟨p.place, 0⟩)[i]? = some e ∧
      e.owner = e₀.owner ∧ e.start = e₀.start ∧ e.count = e₀.count := by
  unfold carriedSame at h
  have hf := allNumbered_at
    (fun y => entryRunIs (carryE Bk ⟨p.place, 0⟩) y.2 y.1.owner y.1.start y.1.count) _ 0 h i e₀ he₀
  rw [Nat.zero_add] at hf
  exact entryRunIs_gives hf

/-! ## 3 Our own lists -/

theorem frontOf_prefix (codes : OnBytes.Codes) (f₀ : OnBytes.ReqFrame) (sps : List Spot)
    {l₀ l : Nat} (h : l₀ ≤ l) : frontOf codes f₀ sps l₀ <+: frontOf codes f₀ sps l := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  unfold frontOf
  rw [List.range_add, List.flatMap_append]
  exact List.prefix_append _ _

/-- Two places of the lot have their fronts of one list of letters. -/
theorem switchFront_is {Z : Pub} {G : Ground} {p₀ p : SwitchPlace} (h₀ : p₀ ∈ switchPlaces Z G)
    (h : p ∈ switchPlaces Z G) :
    ∃ codes f₀ sps, p₀.front = frontOf codes f₀ sps p₀.link ∧
      p.front = frontOf codes f₀ sps p.link := by
  revert h₀ h
  unfold switchPlaces
  cases hP : P1K2.prepOf Z G with
  | none =>
    intro h₀
    simp at h₀
  | some P =>
    cases hs : spotsOf Z.cuts with
    | none =>
      intro h₀
      simp at h₀
    | some sps =>
      intro h₀ h
      simp only [List.mem_map] at h₀ h
      obtain ⟨s₀, -, rfl⟩ := h₀
      obtain ⟨s, -, rfl⟩ := h
      exact ⟨P.z.codes, { shape := P.z.request, groups := OnBytes.reqGroups P.z.request }, sps,
        rfl, rfl⟩

theorem front_prefix {Z : Pub} {G : Ground} {p₀ p : SwitchPlace} (h₀ : p₀ ∈ switchPlaces Z G)
    (h : p ∈ switchPlaces Z G) (hl : p₀.link ≤ p.link) : p₀.front <+: p.front := by
  obtain ⟨codes, f₀, sps, e₀, e⟩ := switchFront_is h₀ h
  rw [e₀, e]
  exact frontOf_prefix codes f₀ sps hl

/-! ## 4 Where every named test says yes -/

theorem switchCarriedAsks_facts {Z : Pub} {G : Ground} {Bk : ProverCoinCounts}
    (h : ∀ t ∈ switchCarriedAsks Z G Bk, t.2 = true) :
    ∀ p ∈ switchPlaces Z G, carriedFits Bk (switchPlaces Z G) p = true ∧
      ∀ p₀ ∈ switchPlaces Z G, p₀.link ≤ p.link → carriedSame Bk p₀ p = true := by
  intro p hp
  have ht := h _ (List.mem_map.2 ⟨p, hp, rfl⟩)
  have ht' : (carriedFits Bk (switchPlaces Z G) p &&
      (switchPlaces Z G).all fun p₀ =>
        decide (p.link < p₀.link) || carriedSame Bk p₀ p) = true := ht
  rw [Bool.and_eq_true] at ht'
  refine ⟨ht'.1, fun p₀ hp₀ hl => ?_⟩
  have hq := List.all_eq_true.1 ht'.2 p₀ hp₀
  rw [Bool.or_eq_true] at hq
  rcases hq with hq | hq
  · exact absurd (of_decide_eq_true hq) (by omega)
  · exact hq

end ProofFile.Honest.K2

#print axioms ProofFile.Honest.K2.switchRunAt
#print axioms ProofFile.Honest.K2.carriedEntryFits
#print axioms ProofFile.Honest.K2.carriedFits
#print axioms ProofFile.Honest.K2.carriedSame
#print axioms ProofFile.Honest.K2.switchCarriedAsks
#print axioms ProofFile.Honest.K2.allNumbered_at
#print axioms ProofFile.Honest.K2.carriedFits_at
#print axioms ProofFile.Honest.K2.carriedFits_named
#print axioms ProofFile.Honest.K2.carriedFits_entry
#print axioms ProofFile.Honest.K2.carriedFits_run
#print axioms ProofFile.Honest.K2.switchRunAt_of
#print axioms ProofFile.Honest.K2.carriedSame_gives
#print axioms ProofFile.Honest.K2.frontOf_prefix
#print axioms ProofFile.Honest.K2.switchFront_is
#print axioms ProofFile.Honest.K2.front_prefix
#print axioms ProofFile.Honest.K2.switchCarriedAsks_facts
