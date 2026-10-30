-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/LotOnce.lean: CONDITIONAL in its last two statements alone. One
definition, private, for the tests at the foot; and statements with their proofs.

What is here. NO TWO HALVES OF K4's LOT's HONEST SIDE (`k4HLot`, Honest/K4/Part.lean: the lot of the
feed-forward layers' own rounds, sub-protocol K4; a half is the prover's side for one member of the
chain, a lot lays the halves of one kind) STAND AT ONE PLACE, AND NONE STANDS AT A PLACE OF ANOTHER
KIND's HALF: at every public part Z, all segments' data G and all of the lot's parameters: NO
HYPOTHESIS. The frame's test before a run (`readyTests`, Honest/Frame.lean) rejects a prover of
which two halves stand at one place (`twice`), over all lots' halves together: this is the share of
that test that falls to K4's lot. Why it holds: the lot's own list (`k4From`,
Johnson/Desc/ProofFile/Lot/K4.lean) gives each pair the number of its segment in the list: at most
one pair for each number, and the numbers rise; the public data copy that number, and a half's place
is made of it.

  `once_filterMap`   a tool: where the keys of a list have no double, neither have the keys of a
     filterMap of it whose results bear their source's key
  `one_at_most`, `twice_of_once`   a tool: `twice` finds nothing where the halves' places have no
     double
  `k4From_links_once`   the numbers in the lot's own list have no double
  `k4HLot_places_once`   **the places of the lot's halves have no double**
  `k4HLot_no_twice`   **`twice` of the lot's halves is empty**
  `k4HLot_apart`, `k4HLot_apart_behind`   **no half of the lot shares its place with a half of a
     list that has no place of the kind K4**: the lot in front of that list; behind it

Limits. Of this one lot's halves and of their places alone: nothing on which places have a half, on
how many there are, or on what a half plays: where the lot lays nothing the statements hold of
nothing. That they do not speak of nothing stands in Law/LotTwelve.lean, which imports this file:
under the library's hypothesis on the public files, at the ground that is made of the public part,
the lot lays just twelve halves, one at each of the kind's twelve places (`k4HLot_twelve`,
`k4HLot_places_perm`). THE STEPS FROM THE LOTS' SHARES TO ALL LOTS' HALVES TOGETHER ARE NOT HERE.
That another lot has no place of the kind K4 is a hypothesis of the last two. The four lines with
#guard try `twice` at lists made by hand (`toyHalf`): it finds a double where one is laid.

Kin. THE THREE TOOLS ARE IN THE LIBRARY ALREADY, THE STATEMENTS TO THE LETTER, UNDER OTHER NAMES, in
other kinds' files: `filterMap_once`, `at_most_one`, `twice_of_nodup` (Honest/K5/Law/LotClean.lean);
`twice_of_once` also as `twice_nil` (Honest/K3/Law/Coverage.lean; Honest/K10/LotAll.lean). Two of
the three are laws on the frame's own `Placed` and `twice` (Honest/Frame.lean). They are typed anew
here because this file builds on none of these three: the lightest of them would bring more than a
thousand modules beneath it.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.LotKind
import Johnson.Desc.ProofFile.Honest.K4.Law.LotFind
import Johnson.Desc.ProofFile.Lot.K4One

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes.Desc.First.K4.Honest
open OnBytes.Model.Stages (LinkH)
open VerifiableInference.Desc (Place)

/-- Where the keys of a list have no double, neither have the keys of a filterMap of it whose
results bear their source's key. k: the key of a source; m: of a result. -/
theorem once_filterMap {ι α κ : Type} (f : ι → Option α) (k : ι → κ) (m : α → κ)
    (hm : ∀ i x, f i = some x → m x = k i) :
    ∀ l : List ι, (l.map k).Nodup → ((l.filterMap f).map m).Nodup
  | [], _ => List.nodup_nil
  | i :: l, h => by
    rw [List.map_cons, List.nodup_cons] at h
    have ih := once_filterMap f k m hm l h.2
    cases e : f i with
    | none =>
      rw [List.filterMap_cons_none e]
      exact ih
    | some x =>
      rw [List.filterMap_cons_some e, List.map_cons, List.nodup_cons]
      refine ⟨fun hx => h.1 ?_, ih⟩
      obtain ⟨y, hy, ey⟩ := List.mem_map.1 hx
      obtain ⟨j, hj, ej⟩ := List.mem_filterMap.1 hy
      refine List.mem_map.2 ⟨j, hj, ?_⟩
      rw [← hm j y ej, ey, hm i x e]

variable {V W X : Type}

/-- Where the places have no double, at most one half stands at a place. -/
theorem one_at_most : ∀ hs : List (Placed V W X), (hs.map (·.place)).Nodup →
    ∀ a : Place, (hs.filter fun x => x.place == a).length ≤ 1
  | [], _, _ => Nat.zero_le _
  | x :: hs, h, a => by
    rw [List.map_cons, List.nodup_cons] at h
    by_cases e : (x.place == a) = true
    · have e1 : (x :: hs).filter (fun y => y.place == a) = x :: hs.filter fun y => y.place == a :=
        List.filter_cons_of_pos e
      have e0 : hs.filter (fun y => y.place == a) = [] := by
        rw [List.filter_eq_nil_iff]
        intro y hy hya
        exact h.1 (List.mem_map.2 ⟨y, hy, (beq_iff_eq.1 hya).trans (beq_iff_eq.1 e).symm⟩)
      rw [e1, e0]
      exact Nat.le_refl _
    · have e1 : (x :: hs).filter (fun y => y.place == a) = hs.filter fun y => y.place == a :=
        List.filter_cons_of_neg e
      rw [e1]
      exact one_at_most hs h.2 a

/-- **`twice` finds nothing where the halves' places have no double.** -/
theorem twice_of_once {hs : List (Placed V W X)} (h : (hs.map (·.place)).Nodup) :
    twice hs = [] := by
  unfold twice
  have e : ((hs.map (·.place)).filter fun a =>
      decide (1 < (hs.filter fun x => x.place == a).length)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro a _ hb
    exact absurd (of_decide_eq_true hb) (Nat.not_lt.2 (one_at_most hs h a))
  rw [e]
  rfl

/-- **The numbers in the lot's own list have no double.** -/
theorem k4From_links_once (Z : Pub) (G : Ground) :
    ∀ (l : List LinkH) (n : Nat) (last : Option String),
      ((k4From Z G l n last).map (·.2.link)).Nodup
  | [], _, _ => by
    unfold k4From
    exact List.nodup_nil
  | Y :: rest, n, last => by
    unfold k4From
    split
    · split
      · rw [List.singleton_append, List.map_cons, List.nodup_cons]
        refine ⟨fun hm => ?_, k4From_links_once Z G rest (n + 1) _⟩
        obtain ⟨y, hy, e⟩ := List.mem_map.1 hm
        have q := k4From_link_ge Z G rest (n + 1) _ y hy
        have e' : y.2.link = n := e
        omega
      · rw [List.nil_append]
        exact k4From_links_once Z G rest (n + 1) _
    · exact k4From_links_once Z G rest (n + 1) last

variable {W₀ Rc Tr X' : Type}

/-- **THE PLACES OF THE LOT's HALVES HAVE NO DOUBLE.** No hypothesis. -/
theorem k4HLot_places_once (cells : Tr → Cells) (weights : W₀ → Weights)
    (look : Pub → Ground → K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard) (Z : Pub)
    (G : Ground) :
    (((k4HLot (Rc := Rc) (X := X') cells weights look).halves Z G).map (·.place)).Nodup := by
  have h0 : ((k4From Z G G.built.toList 0 none).map fun x =>
      (some x.2.link : Option Nat)).Nodup := by
    have q := (k4From_links_once Z G G.built.toList 0 none).map (Option.some_injective Nat)
    rw [List.map_map] at q
    exact q
  have h1 := once_filterMap
    (fun x : Bool × OnBytes.Desc.First.K4.Par => ((k4PubOf Z x.2).filter k4TableFits).map
      (k4Half (Rc := Rc) (X := X') cells weights k4Tokens (look Z G)))
    (fun x => (some x.2.link : Option Nat)) (fun z => z.place.link)
    (fun x z e => by
      obtain ⟨Q, hQ', rfl⟩ := Option.map_eq_some_iff.1 e
      obtain ⟨hQ, -⟩ := Option.filter_eq_some_iff.1 hQ'
      show (some Q.link : Option Nat) = some x.2.link
      rw [k4PubOf_link hQ])
    _ h0
  refine List.Nodup.of_map (fun a : Place => a.link) ?_
  rw [List.map_map]
  exact h1

/-- **`twice` OF THE LOT's HALVES IS EMPTY**, in the form of the frame's test. No hypothesis. -/
theorem k4HLot_no_twice (cells : Tr → Cells) (weights : W₀ → Weights)
    (look : Pub → Ground → K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard) (Z : Pub)
    (G : Ground) :
    twice ((k4HLot (Rc := Rc) (X := X') cells weights look).halves Z G) = [] :=
  twice_of_once (k4HLot_places_once cells weights look Z G)

/-- **No half of the lot shares its place with a half of a list that has no place of the kind K4.**
CONDITIONAL: on h. -/
theorem k4HLot_apart {V' W' Y' : Type} (cells : Tr → Cells) (weights : W₀ → Weights)
    (look : Pub → Ground → K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard) (Z : Pub)
    (G : Ground) {hs : List (Placed V' W' Y')} (h : ∀ y ∈ hs, y.place.kind ≠ .K4) :
    ∀ x ∈ (k4HLot (Rc := Rc) (X := X') cells weights look).halves Z G,
      ∀ y ∈ hs, x.place ≠ y.place := fun x hx y hy e =>
  h y hy (by rw [← e]; exact k4HLot_kind cells weights look Z G x hx)

/-- The same with the lot behind the other list. CONDITIONAL: on h. -/
theorem k4HLot_apart_behind {V' W' Y' : Type} (cells : Tr → Cells) (weights : W₀ → Weights)
    (look : Pub → Ground → K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard) (Z : Pub)
    (G : Ground) {hs : List (Placed V' W' Y')} (h : ∀ y ∈ hs, y.place.kind ≠ .K4) :
    ∀ y ∈ hs, ∀ x ∈ (k4HLot (Rc := Rc) (X := X') cells weights look).halves Z G,
      y.place ≠ x.place := fun y hy x hx e =>
  k4HLot_apart cells weights look Z G h x hx y hy e.symm

/-! ## `twice` at lists made by hand -/

/-- A half without parts at the place with that number of a segment. -/
private def toyHalf (l : Nat) : Placed Unit Unit Unit := ⟨⟨1, some l, 3, .K4⟩, []⟩

#guard twice [toyHalf 0, toyHalf 2, toyHalf 4] == []
#guard twice ([] : List (Placed Unit Unit Unit)) == []
-- negative tests: a double is found; once, though it stands three times
#guard twice [toyHalf 0, toyHalf 2, toyHalf 0] == [⟨1, some 0, 3, .K4⟩]
#guard twice [toyHalf 2, toyHalf 2, toyHalf 4, toyHalf 2] == [⟨1, some 2, 3, .K4⟩]

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.once_filterMap
#print axioms ProofFile.Honest.K4.one_at_most
#print axioms ProofFile.Honest.K4.twice_of_once
#print axioms ProofFile.Honest.K4.k4From_links_once
#print axioms ProofFile.Honest.K4.k4HLot_places_once
#print axioms ProofFile.Honest.K4.k4HLot_no_twice
#print axioms ProofFile.Honest.K4.k4HLot_apart
#print axioms ProofFile.Honest.K4.k4HLot_apart_behind
#print axioms ProofFile.Honest.K4.toyHalf
