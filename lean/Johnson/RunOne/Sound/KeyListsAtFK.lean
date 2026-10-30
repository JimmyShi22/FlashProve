-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Sound/KeyListsAtFK.lean: THE KEY FILE's
DESCRIPTION's BLOCK STRUCTURE AS THREE WHOLE LISTS: for each of the three chains, the places and the
numbers of rounds of ALL its blocks, in order, are the rows of the table `wanted`, which two
other files make of the public values (Johnson/Desc/Key/WantedFirst.lean, WantedLater.lean).
THE FIRST LAW THAT SPENDS `wantedOk`.

What is said.
  `split3`: three lists in a row equal three lists in a row, the i-th of each marked i throughout:
    they are equal one by one.
  `wantedFirst_chain`, `wantedShared_chain`, `wantedSecond_chain`: the tables' rows bear chain 1,
    2, 3.
  `desc_lists`: at every X N P: the tests on the plan and `wantedOk` say yes: so each chain's list
    of (place, number of rounds) is its table.
  `desc_rounds`: the same of the numbers of rounds alone.
  `pull_lists`: the same of `(Key.descriptionFromSource X N P).pull Key.keyInstanceOfOutOfDomainSample` (the frame's `FK X N P`): a pull turns
    the instances' type alone: its three chains are these very chains.
  `laidFixed_lists`: where the key file's piece is laid: at the X N P that it hands on.

Limits. At letters X N P: the tables are functions of `X.Y.k.oneTime` and `X.Y.k.shared.lin`; that
these are the full size's in scope is not shown here, and no closed list is written. What a block at
a place DOES no table says: `wantedOk` holds a block's place and its NUMBER of rounds, not the
rounds: two blocks with equally many rounds that are exchanged before they are stamped pass. Nothing
on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Key.SlotIs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Sound

open OnBytes VerifiableInference.Desc

/-- A list all of whose members are marked i, filtered by the mark j. -/
theorem filter_mark {α : Type} (f : α → ℕ) (i j : ℕ) (l : List α) (h : ∀ x ∈ l, f x = i) :
    l.filter (fun x => f x == j) = if i = j then l else [] := by
  by_cases e : i = j
  · rw [if_pos e]
    exact List.filter_eq_self.2 fun x hx => by rw [h x hx, e]; exact beq_self_eq_true j
  · rw [if_neg e]
    exact List.filter_eq_nil_iff.2 fun x hx => by
      rw [h x hx]
      exact fun hh => e (beq_iff_eq.1 hh)

/-- **Three lists in a row, each marked throughout with its number, are told apart.** -/
theorem split3 {α : Type} (f : α → ℕ) (a₁ a₂ a₃ w₁ w₂ w₃ : List α)
    (ha₁ : ∀ x ∈ a₁, f x = 1) (ha₂ : ∀ x ∈ a₂, f x = 2) (ha₃ : ∀ x ∈ a₃, f x = 3)
    (hw₁ : ∀ x ∈ w₁, f x = 1) (hw₂ : ∀ x ∈ w₂, f x = 2) (hw₃ : ∀ x ∈ w₃, f x = 3)
    (h : a₁ ++ a₂ ++ a₃ = w₁ ++ w₂ ++ w₃) : a₁ = w₁ ∧ a₂ = w₂ ∧ a₃ = w₃ := by
  have key : ∀ j : ℕ, (a₁ ++ a₂ ++ a₃).filter (fun x => f x == j) =
      (w₁ ++ w₂ ++ w₃).filter (fun x => f x == j) := fun j => by rw [h]
  refine ⟨?_, ?_, ?_⟩
  · have := key 1
    simpa [List.filter_append, filter_mark f 1 1 _ ha₁, filter_mark f 2 1 _ ha₂,
      filter_mark f 3 1 _ ha₃, filter_mark f 1 1 _ hw₁, filter_mark f 2 1 _ hw₂,
      filter_mark f 3 1 _ hw₃] using this
  · have := key 2
    simpa [List.filter_append, filter_mark f 1 2 _ ha₁, filter_mark f 2 2 _ ha₂,
      filter_mark f 3 2 _ ha₃, filter_mark f 1 2 _ hw₁, filter_mark f 2 2 _ hw₂,
      filter_mark f 3 2 _ hw₃] using this
  · have := key 3
    simpa [List.filter_append, filter_mark f 1 3 _ ha₁, filter_mark f 2 3 _ ha₂,
      filter_mark f 3 3 _ ha₃, filter_mark f 1 3 _ hw₁, filter_mark f 2 3 _ hw₂,
      filter_mark f 3 3 _ hw₃] using this

theorem wantedFirst_chain (one : Params.OneTime) : ∀ r ∈ Key.wantedFirst one, r.1.chain = 1 := by
  intro r hr
  unfold Key.wantedFirst at hr
  simp only [List.mem_append, List.mem_cons, List.mem_flatMap, List.not_mem_nil, or_false] at hr
  rcases hr with ((((h | h) | ⟨x, -, h⟩) | (h | h | h)) | h) | h
  · rw [h]
  · rw [h]
  · unfold Key.wantedLink at h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h <;> rw [h]
  · rw [h]
  · rw [h]
  · rw [h]
  · split at h
    · rw [List.mem_singleton.1 h]
    · cases h
  · rw [h]

theorem wantedShared_chain (S : Params.LinShape) : ∀ r ∈ Key.wantedShared S, r.1.chain = 2 := by
  intro r hr
  unfold Key.wantedShared at hr
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with ((h | h | h | h | h | h | h | h | h | h) | h) | h
  all_goals first
    | rw [h]
    | (split at h
       · rw [List.mem_singleton.1 h]
       · cases h)

theorem wantedSecond_chain (S : Params.LinShape) : ∀ r ∈ Key.wantedSecond S, r.1.chain = 3 := by
  intro r hr
  unfold Key.wantedSecond at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h | h | h <;> rw [h]

/-- A chain's list of blocks as rows (place, number of rounds). -/
def rowsOf {S Cl : Type} (bs : List (Block S Cl)) : List (Place × ℕ) :=
  bs.map fun b => (b.place, b.rounds.length)

theorem placesOf_rows {S Cl : Type} (bs : List (Block S Cl)) :
    (placesOf bs).map (·.2) = rowsOf bs := by
  unfold placesOf rowsOf
  rw [List.map_map]
  rfl

/-- What `placesOk` says of a chain's list: every block bears the chain's number. -/
theorem rows_chain {S Cl : Type} (bs : List (Block S Cl)) (n : ℕ)
    (h : ((placesOf bs).all fun p => p.2.1.chain == n) = true) :
    ∀ r ∈ rowsOf bs, r.1.chain = n := by
  intro r hr
  obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hr
  exact beq_iff_eq.1 (List.all_eq_true.1 h (b.name, b.place, b.rounds.length)
    (List.mem_map.2 ⟨b, hb, rfl⟩))

/-- **At any description**: the tests on the plan and `wantedOk` say yes, and the table is three
tables in a row that bear chain 1, 2, 3: each chain's rows are its table. -/
theorem lists_of_wanted {Xi : Type} (F : FileDescription Xi) (w₁ w₂ w₃ : List (Place × ℕ))
    (hF : F.wanted = w₁ ++ w₂ ++ w₃) (h₁ : ∀ r ∈ w₁, r.1.chain = 1) (h₂ : ∀ r ∈ w₂, r.1.chain = 2)
    (h₃ : ∀ r ∈ w₃, r.1.chain = 3) (hp : F.placesOk = true) (hw : F.wantedOk = true) :
    rowsOf F.first.blocksInOrder = w₁ ∧ rowsOf F.shared.blocksInOrder = w₂ ∧ rowsOf F.second.blocksInOrder = w₃ := by
  unfold FileDescription.placesOk at hp
  simp only [Bool.and_eq_true] at hp
  obtain ⟨⟨⟨c₁, c₂⟩, c₃⟩, -⟩ := hp
  have e : rowsOf F.first.blocksInOrder ++ rowsOf F.shared.blocksInOrder ++ rowsOf F.second.blocksInOrder =
      w₁ ++ w₂ ++ w₃ := by
    have h0 : F.places.map (·.2) = F.wanted := beq_iff_eq.1 hw
    unfold FileDescription.places at h0
    rw [List.map_append, List.map_append, placesOf_rows, placesOf_rows, placesOf_rows, hF] at h0
    exact h0
  exact split3 (fun r => r.1.chain) _ _ _ _ _ _ (rows_chain _ 1 c₁) (rows_chain _ 2 c₂)
    (rows_chain _ 3 c₃) h₁ h₂ h₃ e

/-- `placesOk` is a clause of the tests on the plan. -/
theorem placesOk_of_planOk {Xi : Type} (F : FileDescription Xi) (h : F.planOk = true) :
    F.placesOk = true := by
  unfold FileDescription.planOk FileDescription.planOkCore at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.2

/-- **The key file's description's three whole lists**, at every X N P. -/
theorem desc_lists (X : Key.Source) (N : H2U.PlaceNums) (P : Key.LaterPlaces)
    (hp : (Key.descriptionFromSource X N P).planOk = true) (hw : (Key.descriptionFromSource X N P).wantedOk = true) :
    rowsOf (Key.descriptionFromSource X N P).first.blocksInOrder = Key.wantedFirst X.Y.k.oneTime ∧
      rowsOf (Key.descriptionFromSource X N P).shared.blocksInOrder = Key.wantedShared X.Y.k.shared.lin ∧
      rowsOf (Key.descriptionFromSource X N P).second.blocksInOrder = Key.wantedSecond X.Y.k.shared.lin :=
  lists_of_wanted _ _ _ _ rfl (wantedFirst_chain _) (wantedShared_chain _) (wantedSecond_chain _)
    (placesOk_of_planOk _ hp) hw

/-- The numbers of rounds alone. -/
theorem rounds_of_rows {S Cl : Type} (bs : List (Block S Cl)) :
    bs.map (·.rounds.length) = (rowsOf bs).map (·.2) := by
  unfold rowsOf
  rw [List.map_map]
  rfl

/-- **The numbers of rounds of all blocks, chain by chain**, at every X N P. -/
theorem desc_rounds (X : Key.Source) (N : H2U.PlaceNums) (P : Key.LaterPlaces)
    (hp : (Key.descriptionFromSource X N P).planOk = true) (hw : (Key.descriptionFromSource X N P).wantedOk = true) :
    (Key.descriptionFromSource X N P).first.blocksInOrder.map (·.rounds.length) =
        (Key.wantedFirst X.Y.k.oneTime).map (·.2) ∧
      (Key.descriptionFromSource X N P).shared.blocksInOrder.map (·.rounds.length) =
        (Key.wantedShared X.Y.k.shared.lin).map (·.2) ∧
      (Key.descriptionFromSource X N P).second.blocksInOrder.map (·.rounds.length) =
        (Key.wantedSecond X.Y.k.shared.lin).map (·.2) := by
  obtain ⟨h₁, h₂, h₃⟩ := desc_lists X N P hp hw
  exact ⟨by rw [rounds_of_rows, h₁], by rw [rounds_of_rows, h₂], by rw [rounds_of_rows, h₃]⟩

/-- The same of the description pulled to the records (the frame's `FK X N P`): a pull turns the
instances' type alone. -/
theorem pull_lists (X : Key.Source) (N : H2U.PlaceNums) (P : Key.LaterPlaces)
    (hp : (Key.descriptionFromSource X N P).planOk = true) (hw : (Key.descriptionFromSource X N P).wantedOk = true) :
    rowsOf ((Key.descriptionFromSource X N P).pull Key.keyInstanceOfOutOfDomainSample).first.blocksInOrder = Key.wantedFirst X.Y.k.oneTime ∧
      rowsOf ((Key.descriptionFromSource X N P).pull Key.keyInstanceOfOutOfDomainSample).shared.blocksInOrder = Key.wantedShared X.Y.k.shared.lin ∧
      rowsOf ((Key.descriptionFromSource X N P).pull Key.keyInstanceOfOutOfDomainSample).second.blocksInOrder = Key.wantedSecond X.Y.k.shared.lin :=
  desc_lists X N P hp hw

/-- **Where the key file's piece is laid**: at the X N P that it hands on, whose run is the laid
decision, the three whole lists are the tables. -/
theorem laidFixed_lists (Z : Model.Verify.Public) (lay : ByteArray) (D : Maker.WholeD)
    (r : Key.KeyRun) (h : Key.keyDataAndDecisionAtFixedDigest Z lay = .ok (D, r)) :
    ∃ X N P, r = ((Key.descriptionFromSource X N P).pull Key.keyInstanceOfOutOfDomainSample).run ∧
      (Key.descriptionFromSource X N P).data "key file" = .ok D ∧
      rowsOf (Key.descriptionFromSource X N P).first.blocksInOrder = Key.wantedFirst X.Y.k.oneTime ∧
      rowsOf (Key.descriptionFromSource X N P).shared.blocksInOrder = Key.wantedShared X.Y.k.shared.lin ∧
      rowsOf (Key.descriptionFromSource X N P).second.blocksInOrder = Key.wantedSecond X.Y.k.shared.lin := by
  obtain ⟨m, X, N, P, -, -, -, -, -, hp, hw, -, -, hd, hr⟩ := Key.laidFixed_is Z lay D r h
  exact ⟨X, N, P, hr, hd, desc_lists X N P hp hw⟩

end Johnson.RunOne.Sound

#print axioms Johnson.RunOne.Sound.split3
#print axioms Johnson.RunOne.Sound.lists_of_wanted
#print axioms Johnson.RunOne.Sound.desc_lists
#print axioms Johnson.RunOne.Sound.desc_rounds
#print axioms Johnson.RunOne.Sound.pull_lists
#print axioms Johnson.RunOne.Sound.laidFixed_lists
