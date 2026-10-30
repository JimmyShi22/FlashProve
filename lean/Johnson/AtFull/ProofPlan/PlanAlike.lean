-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/ProofPlan/PlanAlike.lean: THE TESTS ON THE PLAN OF A FILE's DESCRIPTION
(`FileDescription.planOk`, Johnson/Desc/Block.lean) PASS AT ONE DESCRIPTION WHERE THEY PASS AT ANOTHER THAT
IS ALIKE TO THEM. General in both descriptions. Definitions, statements and proofs.

Why. The tests read of a block its place, rounds, oracles, before and its own test, and of the file
its fields fileOk, plans and tableDepth: never a block's decision, nor what its runs of claims do.
So they can be asked at a written description whose blocks decide nothing, and carried from there.

Whose pattern. `Alike` and `OneChainFileDescription.planOk_alike` (Johnson/Desc/K15/SendOwnLaw.lean) say the like of
two blocks of one type of state and of claim, with equal names, and of a file of one chain. Here:
blocks of two types; three chains; no name (`placesOk` reads of a place its chain, link and piece).

  `Alike₂ b b'`: place, rounds, oracles and before are equal; where b's own test passes, b' 's does.
  `PlanAlike W F`: fileOk passes at F where it does at W; plans and tableDepth are equal; the three
    flat lists are alike, block by block.
  `alike₂_rounds`, `alike₂_place`, `alike₂_sent`, `alike₂_oracles`, `alike₂_before`,
    `alike₂_blocksOk`, `alike₂_last`: what alike lists share.
  `inChain_places`, `triples_places`, `placesOk_alike₂`: the test on the places.
  `FileDescription.planOk_alike₂`: MAIN. `FileDescription.planWord_alike₂`: so the refusal's words are none.
  `Alike₂.refl`, `alike₂_refl`, `PlanAlike.refl`: every description is alike to itself: the relation
    can be met.

WHERE THE WEIGHT GOES. The theorem is bookkeeping. It carries every test but two: fileOk, and in
`blocksOk` a block's own test (`shaped`, the other half of `blocksOk`, is carried). Where W's are
the literal true, `PlanAlike W F` asks outright that F's fileOk passes and that each of F's blocks
passes its own test.

Limits. No description is named. `wantedOk` and `owedOk` stand beside `planOk`, not in it: nothing
is said of them. Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import Mathlib.Data.List.Forall2
import Johnson.Desc.Block

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc

variable {S Cl S' Cl' : Type}

/-- What the tests on the plan read of a block, but for its own test: between blocks of two types of
state and of claim. -/
def Alike₂ (b : Block S Cl) (b' : Block S' Cl') : Prop :=
  b.place = b'.place ∧ b.rounds = b'.rounds ∧ b.oracles = b'.oracles ∧ b.before = b'.before ∧
    (b.planOk = true → b'.planOk = true)

/-- F is, to the tests on the plan, as W is. -/
structure PlanAlike {Xi Xi' : Type} (W : FileDescription Xi) (F : FileDescription Xi') : Prop where
  fileOk : W.fileOk = true → F.fileOk = true
  plans : W.plans = F.plans
  depth : W.tableDepth = F.tableDepth
  first : List.Forall₂ Alike₂ W.first.blocksInOrder F.first.blocksInOrder
  shared : List.Forall₂ Alike₂ W.shared.blocksInOrder F.shared.blocksInOrder
  second : List.Forall₂ Alike₂ W.second.blocksInOrder F.second.blocksInOrder

/-! ### what alike lists share -/

theorem alike₂_rounds (l : List (Block S Cl)) (l' : List (Block S' Cl'))
    (h : List.Forall₂ Alike₂ l l') : l.flatMap (·.rounds) = l'.flatMap (·.rounds) := by
  induction h with
  | nil => rfl
  | @cons b b' l l' hb _ ih => simp only [List.flatMap_cons, hb.2.1, ih]

theorem alike₂_place (l : List (Block S Cl)) (l' : List (Block S' Cl'))
    (h : List.Forall₂ Alike₂ l l') : l.map (·.place) = l'.map (·.place) := by
  induction h with
  | nil => rfl
  | @cons b b' l l' hb _ ih => simp only [List.map_cons, hb.1, ih]

theorem alike₂_sent (l : List (Block S Cl)) (l' : List (Block S' Cl'))
    (h : List.Forall₂ Alike₂ l l') : sentOf l = sentOf l' := by
  induction h with
  | nil => rfl
  | @cons b b' l l' hb _ ih =>
    unfold sentOf at ih ⊢
    simp only [List.flatMap_cons, hb.2.2.1, ih]

theorem alike₂_oracles (l : List (Block S Cl)) (l' : List (Block S' Cl'))
    (h : List.Forall₂ Alike₂ l l') : oraclesOf l = oraclesOf l' := by
  induction h with
  | nil => rfl
  | @cons b b' l l' hb _ ih =>
    unfold oraclesOf at ih ⊢
    simp only [List.flatMap_cons, hb.2.2.1, ih]

theorem alike₂_before (D : List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound)
    (O : List Oracle × List Oracle × List Oracle) (c : Nat) (l : List (Block S Cl))
    (l' : List (Block S' Cl')) (h : List.Forall₂ Alike₂ l l') :
    ∀ n, beforeAt D O c n l = beforeAt D O c n l' := by
  induction h with
  | nil => intro n; rfl
  | @cons b b' l l' hb _ ih =>
    intro n
    unfold beforeAt
    rw [hb.2.2.2.1, hb.2.1, ih]

theorem alike₂_blocksOk (l : List (Block S Cl)) (l' : List (Block S' Cl'))
    (h : List.Forall₂ Alike₂ l l') (hk : blocksOk l = true) : blocksOk l' = true := by
  induction h with
  | nil => rfl
  | @cons b b' l l' hb _ ih =>
    unfold blocksOk at hk ih ⊢
    simp only [List.all_cons, Bool.and_eq_true] at hk ⊢
    refine ⟨⟨hb.2.2.2.2 hk.1.1, ?_⟩, ih hk.2⟩
    have : b'.shaped = b.shaped := by unfold Block.shaped; rw [hb.2.1, hb.2.2.1]
    rw [this]
    exact hk.1.2

/-- The last blocks of two chains whose flat lists are alike declare the same rounds. -/
theorem alike₂_last {c : Chain S Cl} {c' : Chain S' Cl'}
    (h : List.Forall₂ Alike₂ c.blocksInOrder c'.blocksInOrder) : c.last.rounds = c'.last.rounds := by
  have h' := List.forall₂_reverse_iff.2 h
  unfold Chain.blocksInOrder at h'
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append] at h'
  cases h' with
  | cons hb _ => exact hb.2.1

/-! ### the test on the places -/

theorem inChain_places (n : Nat) (bs : List (Block S Cl)) :
    ((placesOf bs).all fun p => p.2.1.chain == n) =
      ((bs.map (·.place)).all fun a => a.chain == n) := by
  unfold placesOf
  simp only [List.all_map]
  rfl

theorem triples_places (bs : List (Block S Cl)) :
    ((placesOf bs).map fun p => (p.2.1.chain, p.2.1.link, p.2.1.piece)) =
      ((bs.map (·.place)).map fun a => (a.chain, a.link, a.piece)) := by
  unfold placesOf
  simp only [List.map_map]
  rfl

theorem placesOk_alike₂ {Xi Xi' : Type} {W : FileDescription Xi} {F : FileDescription Xi'}
    (h₁ : W.first.blocksInOrder.map (·.place) = F.first.blocksInOrder.map (·.place))
    (h₂ : W.shared.blocksInOrder.map (·.place) = F.shared.blocksInOrder.map (·.place))
    (h₃ : W.second.blocksInOrder.map (·.place) = F.second.blocksInOrder.map (·.place)) :
    W.placesOk = F.placesOk := by
  unfold FileDescription.placesOk FileDescription.places
  simp only [List.map_append, inChain_places, triples_places, h₁, h₂, h₃]

/-! ### the tests on the plan -/

/-- **The tests on the plan pass at F where they pass at W.** -/
theorem FileDescription.planOk_alike₂ {Xi Xi' : Type} {W : FileDescription Xi} {F : FileDescription Xi'}
    (h : PlanAlike W F) (hW : W.planOk = true) : F.planOk = true := by
  have eD : W.roundsDeclaredByBlocks = F.roundsDeclaredByBlocks := by
    unfold FileDescription.roundsDeclaredByBlocks
    rw [alike₂_rounds _ _ h.first, alike₂_rounds _ _ h.shared, alike₂_rounds _ _ h.second]
  have o₁ := alike₂_oracles _ _ h.first
  have o₂ := alike₂_oracles _ _ h.shared
  have o₃ := alike₂_oracles _ _ h.second
  have eL : W.labelsOk = F.labelsOk := by
    unfold FileDescription.labelsOk FileDescription.lastChainFirstTreeNumber
    rw [eD]
  have eP : W.placesOk = F.placesOk :=
    placesOk_alike₂ (alike₂_place _ _ h.first) (alike₂_place _ _ h.shared)
      (alike₂_place _ _ h.second)
  have eB : W.beforeOk = F.beforeOk := by
    unfold FileDescription.beforeOk
    simp only [eD, o₁, o₂, o₃]
    rw [alike₂_before _ _ 0 _ _ h.first 0, alike₂_before _ _ 1 _ _ h.shared 0,
      alike₂_before _ _ 2 _ _ h.second 0]
  have eK : W.treeSharingOk = F.treeSharingOk := by
    unfold FileDescription.treeSharingOk FileDescription.roots
    rw [eD, o₁, o₂, o₃]
  have eR : W.readsOk = F.readsOk := by
    unfold FileDescription.readsOk
    rw [eD]
  have eS : W.sentFit = F.sentFit := by
    unfold FileDescription.sentFit
    rw [eD, alike₂_sent _ _ h.first, alike₂_sent _ _ h.shared, alike₂_sent _ _ h.second]
  unfold FileDescription.planOk at hW ⊢
  rw [Bool.and_eq_true] at hW ⊢
  obtain ⟨hc, hs⟩ := hW
  refine ⟨?_, ?_⟩
  · unfold FileDescription.planOkCore at hc ⊢
    rw [← eD, ← h.plans, ← h.depth, ← eL, ← eP, ← eB, ← eK, ← eR, ← eS]
    simp only [Bool.and_eq_true] at hc ⊢
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩, c7⟩, c8⟩, c9⟩, c10⟩, c11⟩, c12⟩, c13⟩,
      c14⟩ := hc
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h.fileOk c1, alike₂_blocksOk _ _ h.first c2⟩,
      alike₂_blocksOk _ _ h.shared c3⟩, alike₂_blocksOk _ _ h.second c4⟩, c5⟩, c6⟩, c7⟩, c8⟩, c9⟩,
      c10⟩, c11⟩, c12⟩, c13⟩, c14⟩
  · unfold FileDescription.sealLast at hs ⊢
    rw [← alike₂_last h.first]
    exact hs

/-- **So the refusal's words on the plan are none at F.** -/
theorem FileDescription.planWord_alike₂ {Xi Xi' : Type} {W : FileDescription Xi} {F : FileDescription Xi'}
    (h : PlanAlike W F) (hW : W.planOk = true) : F.planWord = none := by
  unfold FileDescription.planWord
  rw [if_pos (FileDescription.planOk_alike₂ h hW)]

/-! ### the relation can be met -/

theorem Alike₂.refl (b : Block S Cl) : Alike₂ b b := ⟨rfl, rfl, rfl, rfl, id⟩

theorem alike₂_refl : ∀ l : List (Block S Cl), List.Forall₂ Alike₂ l l
  | [] => .nil
  | b :: l => .cons (Alike₂.refl b) (alike₂_refl l)

theorem PlanAlike.refl {Xi : Type} (F : FileDescription Xi) : PlanAlike F F :=
  ⟨id, rfl, rfl, alike₂_refl _, alike₂_refl _, alike₂_refl _⟩

end VerifiableInference.Desc

#print axioms VerifiableInference.Desc.alike₂_rounds
#print axioms VerifiableInference.Desc.alike₂_place
#print axioms VerifiableInference.Desc.alike₂_sent
#print axioms VerifiableInference.Desc.alike₂_oracles
#print axioms VerifiableInference.Desc.alike₂_before
#print axioms VerifiableInference.Desc.alike₂_blocksOk
#print axioms VerifiableInference.Desc.alike₂_last
#print axioms VerifiableInference.Desc.inChain_places
#print axioms VerifiableInference.Desc.triples_places
#print axioms VerifiableInference.Desc.placesOk_alike₂
#print axioms VerifiableInference.Desc.FileDescription.planOk_alike₂
#print axioms VerifiableInference.Desc.FileDescription.planWord_alike₂
#print axioms VerifiableInference.Desc.Alike₂.refl
#print axioms VerifiableInference.Desc.alike₂_refl
#print axioms VerifiableInference.Desc.PlanAlike.refl
