-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Sound/KeyEightLight.lean: UNDER THE TESTS
ON THE PLAN THE KEY FILE's SHARED CHAIN HOLDS THE KIND K14's EIGHT BLOCKS, at the unpulled
description `Key.descriptionFromSource X N P`: THE STATEMENTS OF Johnson/RunOne/Sound/KeyEightAtDesc.lean AND
KeyEightMore.lean OVER A LIGHT IMPORT (Johnson/Desc/Key/SlotIs.lean alone; not the frame's files),
in a namespace of their own, so that no full name is borne twice where both are imported.

A COPY, BY DESIGN. `atClaim` here is the text of the frame's `atClaim` (`bareB b.retype`:
Johnson/RunOne/Sound/KeyLaterAtFK.lean, KeyMapAtFK.lean) unfolded. The two were tied by the kernel
(`atClaim_light`, by rfl) in KeyEightTie.lean, a file that is not in this library: no theorem here ties them. WHOEVER TURNS ONE TURNS BOTH.

What is said.
  `atClaim b`: the block b as the shared chain's flat list lays it: retyped to the file's claims and
    made bare. SIX FIELDS PASS UNTURNED (`atClaim_decide`, `atClaim_rounds`, `atClaim_place`,
    `atClaim_name`, `atClaim_oracles`, `atClaim_before`). TWO DO NOT: `planOk` (it asks more: no
    claims; bare) and `claims` (none).
  `shared_flat`: the shared chain's flat list, written out.
  `blocks_length`, `blocks_names`: where `Desc.K14.blocks Q` can be said it is a list of eight, with
    these names. THE EIGHT NAMES ARE K14's FILES' WORDS, SPELLED IN THE STATEMENT: a turn of one
    there breaks `blocks_names` and `desc_point`, and must. No other proof here spells a word of
    other files.
  `blocks_of_planOk`: under the tests on the plan it can be said: where it cannot, the chain holds
    one block whose own test on the plan is false.
  `desc_eight`, `desc_eight_named`: seat 1 + j holds `atClaim b` for the list's member b number j.
  `desc_front`: seat 0's decision is that of `Key.sharedFront X.chains`. No premise.
  `desc_point`: seat 1 is "LIN point", the first of `Desc.K14.blocksOr`, with its decision spelled.

Limits. What the eight do is the kind K14's laws'. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Key.SlotIs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Sound.Light

open OnBytes VerifiableInference.Desc

/-- A block at the key file's type of claims, as the flat list lays it. -/
abbrev atClaim {S : Type} (b : Block S Unit) : Block S Key.Claim :=
  { (b.retype : Block S Key.Claim) with
    planOk := (b.retype : Block S Key.Claim).planOk && (b.retype : Block S Key.Claim).hasNoClaimsAndNothingAfter }

theorem atClaim_decide {S : Type} (b : Block S Unit) : (atClaim b).decide = b.decide := rfl

theorem atClaim_rounds {S : Type} (b : Block S Unit) : (atClaim b).rounds = b.rounds := rfl

theorem atClaim_place {S : Type} (b : Block S Unit) : (atClaim b).place = b.place := rfl

theorem atClaim_name {S : Type} (b : Block S Unit) : (atClaim b).name = b.name := rfl

theorem atClaim_oracles {S : Type} (b : Block S Unit) : (atClaim b).oracles = b.oracles := rfl

theorem atClaim_before {S : Type} (b : Block S Unit) : (atClaim b).before = b.before := rfl

/-- The kind's parameters at the key file. -/
abbrev parAt (X : Key.Source) (P : Key.LaterPlaces) : _root_.Desc.K14.P14 :=
  Key.sharedPar X.chains (Key.beforeSharedPoint P)

/-- **The shared chain's flat list, written out.** -/
theorem shared_flat (X : Key.Source) (N : H2U.PlaceNums) (P : Key.LaterPlaces) :
    ∃ b₀, b₀.decide = (Key.sharedFront X.chains).decide ∧
      (Key.descriptionFromSource X N P).shared.blocksInOrder =
        [b₀] ++ ((_root_.Desc.K14.blocksOr (parAt X P) ++ Key.sharedTests P).map atClaim ++
          [atClaim (Key.sharedChain X.chains P).last]) := by
  refine ⟨{ ((Key.sharedChain X.chains P).retype : Chain _ Key.Claim).first with
    planOk := ((Key.sharedChain X.chains P).retype : Chain _ Key.Claim).first.planOk &&
      ((Key.sharedChain X.chains P).retype : Chain _ Key.Claim).first.hasNoClaimsAndNothingAfter }, rfl, ?_⟩
  show _ :: [] ++ [] ++ ((Key.sharedChain X.chains P).back.map Block.retype).map _ ++ [_] = _
  rw [List.append_nil, List.map_map]
  rfl

theorem append_at {α : Type} (a b : List α) (n j : ℕ) (h : a.length = n) :
    (a ++ b)[n + j]? = b[j]? := by
  subst h
  rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

/-- Where the kind's blocks can be said they are eight. -/
theorem blocks_length (Q : _root_.Desc.K14.P14) (bl : List (Block _root_.Desc.K14.St Unit))
    (h : _root_.Desc.K14.blocks Q = some bl) : bl.length = 8 := by
  unfold _root_.Desc.K14.blocks at h
  cases hu : _root_.Desc.K14.withU Q.S with
  | none =>
    rw [hu] at h
    cases h
  | some u =>
    rw [hu] at h
    obtain rfl := Option.some.inj h
    rfl

/-- The eight blocks' names, in order. -/
theorem blocks_names (Q : _root_.Desc.K14.P14) (bl : List (Block _root_.Desc.K14.St Unit))
    (h : _root_.Desc.K14.blocks Q = some bl) :
    bl.map (·.name) = ["LIN point", "send o_u", "(rec_gamma)", "LOC", "send o_omega", "joins",
      "LIN zeta", "SPLIT"] := by
  unfold _root_.Desc.K14.blocks at h
  cases hu : _root_.Desc.K14.withU Q.S with
  | none =>
    rw [hu] at h
    cases h
  | some u =>
    rw [hu] at h
    obtain rfl := Option.some.inj h
    rfl

/-- A description's tests on the plan hold of each block of its shared chain. -/
theorem blocksOk_shared {Xi : Type} (F : FileDescription Xi) (h : F.planOk = true) :
    blocksOk F.shared.blocksInOrder = true := by
  unfold FileDescription.planOk FileDescription.planOkCore at h
  simp only [Bool.and_eq_true] at h
  tauto

/-- **Under the tests on the plan the kind's blocks can be said.** The stand-by block is not spelled
here: its name is K14's files' word and may turn. -/
theorem blocks_of_planOk (X : Key.Source) (N : H2U.PlaceNums) (P : Key.LaterPlaces)
    (hp : (Key.descriptionFromSource X N P).planOk = true) :
    ∃ bl, _root_.Desc.K14.blocks (parAt X P) = some bl := by
  cases hb : _root_.Desc.K14.blocks (parAt X P) with
  | some bl => exact ⟨bl, rfl⟩
  | none =>
    exfalso
    have hall := blocksOk_shared (Key.descriptionFromSource X N P) hp
    obtain ⟨b₀, -, hf⟩ := shared_flat X N P
    rw [hf] at hall
    unfold blocksOk at hall
    have key : ∀ x ∈ _root_.Desc.K14.blocksOr (parAt X P), (atClaim x).planOk = true := by
      intro x hx
      have hm : atClaim x ∈ [b₀] ++
          ((_root_.Desc.K14.blocksOr (parAt X P) ++ Key.sharedTests P).map atClaim ++
            [atClaim (Key.sharedChain X.chains P).last]) :=
        List.mem_append_right _ (List.mem_append_left _
          (List.mem_map.2 ⟨x, List.mem_append_left _ hx, rfl⟩))
      exact (Bool.and_eq_true_iff.1 ((List.all_eq_true.1 hall) _ hm)).1
    unfold _root_.Desc.K14.blocksOr at key
    rw [hb] at key
    have k : false = true := key _ (List.mem_singleton.2 rfl)
    cases k

/-- **Under the tests on the plan the shared chain holds the kind's eight blocks.** -/
theorem desc_eight (X : Key.Source) (N : H2U.PlaceNums) (P : Key.LaterPlaces)
    (hp : (Key.descriptionFromSource X N P).planOk = true) :
    ∃ bl, _root_.Desc.K14.blocks (parAt X P) = some bl ∧ bl.length = 8 ∧
      ∀ (j : ℕ) (b : Block _root_.Desc.K14.St Unit), bl[j]? = some b →
        (Key.descriptionFromSource X N P).shared.blocksInOrder[1 + j]? = some (atClaim b) := by
  obtain ⟨bl, hbl⟩ := blocks_of_planOk X N P hp
  refine ⟨bl, hbl, blocks_length _ bl hbl, fun j b hb => ?_⟩
  obtain ⟨b₀, -, hf⟩ := shared_flat X N P
  have hj : j < bl.length := (List.getElem?_eq_some_iff.1 hb).1
  have hor : _root_.Desc.K14.blocksOr (parAt X P) = bl := by
    unfold _root_.Desc.K14.blocksOr
    rw [hbl]
    rfl
  refine (congrArg (fun l => l[1 + j]?) hf).trans ((append_at [b₀] _ 1 j rfl).trans ?_)
  rw [hor, List.getElem?_append_left (by rw [List.length_map, List.length_append]; omega),
    List.getElem?_map, List.getElem?_append_left hj, hb]
  rfl

/-- A list of eight, spelled. -/
theorem eight_spelled {α : Type} (l : List α) (h : l.length = 8) :
    ∃ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈, l = [a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈] := by
  match l, h with
  | [a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈], _ => exact ⟨_, _, _, _, _, _, _, _, rfl⟩

/-- **`desc_eight` at the eight seats.** -/
theorem desc_eight_named (X : Key.Source) (N : H2U.PlaceNums) (P : Key.LaterPlaces)
    (hp : (Key.descriptionFromSource X N P).planOk = true) :
    ∃ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈,
      _root_.Desc.K14.blocks (parAt X P) = some [b₁, b₂, b₃, b₄, b₅, b₆, b₇, b₈] ∧
      (Key.descriptionFromSource X N P).shared.blocksInOrder[1]? = some (atClaim b₁) ∧
      (Key.descriptionFromSource X N P).shared.blocksInOrder[2]? = some (atClaim b₂) ∧
      (Key.descriptionFromSource X N P).shared.blocksInOrder[3]? = some (atClaim b₃) ∧
      (Key.descriptionFromSource X N P).shared.blocksInOrder[4]? = some (atClaim b₄) ∧
      (Key.descriptionFromSource X N P).shared.blocksInOrder[5]? = some (atClaim b₅) ∧
      (Key.descriptionFromSource X N P).shared.blocksInOrder[6]? = some (atClaim b₆) ∧
      (Key.descriptionFromSource X N P).shared.blocksInOrder[7]? = some (atClaim b₇) ∧
      (Key.descriptionFromSource X N P).shared.blocksInOrder[8]? = some (atClaim b₈) := by
  obtain ⟨bl, hbl, hlen, hat⟩ := desc_eight X N P hp
  obtain ⟨b₁, b₂, b₃, b₄, b₅, b₆, b₇, b₈, rfl⟩ := eight_spelled bl hlen
  exact ⟨b₁, b₂, b₃, b₄, b₅, b₆, b₇, b₈, hbl, hat 0 _ rfl, hat 1 _ rfl, hat 2 _ rfl,
    hat 3 _ rfl, hat 4 _ rfl, hat 5 _ rfl, hat 6 _ rfl, hat 7 _ rfl⟩

/-- **Seat 0 of the shared chain**: a block whose decision is the shared front's. -/
theorem desc_front (X : Key.Source) (N : H2U.PlaceNums) (P : Key.LaterPlaces) :
    ∃ b₀, (Key.descriptionFromSource X N P).shared.blocksInOrder[0]? = some b₀ ∧
      b₀.decide = (Key.sharedFront X.chains).decide :=
  ⟨_, rfl, rfl⟩

/-- **Seat 1 of the shared chain**: the kind's first block, "LIN point", with its decision
spelled. -/
theorem desc_point (X : Key.Source) (N : H2U.PlaceNums) (P : Key.LaterPlaces)
    (hp : (Key.descriptionFromSource X N P).planOk = true) :
    ∃ b, (Key.descriptionFromSource X N P).shared.blocksInOrder[1]? = some (atClaim b) ∧ b.name = "LIN point" ∧
      (_root_.Desc.K14.blocksOr (parAt X P))[0]? = some b ∧
      b.decide = fun d rs _ =>
        _root_.Desc.K14.why (_root_.Desc.K14.linPointL (parAt X P).par d)
          (_root_.Desc.K14.linPoint (parAt X P).par d rs) := by
  obtain ⟨bl, hbl, -, hat⟩ := desc_eight X N P hp
  have hbl' := hbl
  unfold _root_.Desc.K14.blocks at hbl'
  cases hu : _root_.Desc.K14.withU (parAt X P).S with
  | none =>
    rw [hu] at hbl'
    cases hbl'
  | some u =>
    rw [hu] at hbl'
    obtain rfl := Option.some.inj hbl'
    refine ⟨_, hat 0 _ rfl, rfl, ?_, rfl⟩
    unfold _root_.Desc.K14.blocksOr
    rw [hbl]
    rfl

end Johnson.RunOne.Sound.Light

#print axioms Johnson.RunOne.Sound.Light.shared_flat
#print axioms Johnson.RunOne.Sound.Light.blocks_length
#print axioms Johnson.RunOne.Sound.Light.blocks_names
#print axioms Johnson.RunOne.Sound.Light.blocks_of_planOk
#print axioms Johnson.RunOne.Sound.Light.desc_eight
#print axioms Johnson.RunOne.Sound.Light.desc_eight_named
#print axioms Johnson.RunOne.Sound.Light.desc_front
#print axioms Johnson.RunOne.Sound.Light.desc_point
