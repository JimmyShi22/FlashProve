-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/BlockSlotOpens.lean: round by round, the data that the description's own road has made
hold the declared rounds' stored tables and their openings by number.

`OfData` (Johnson/Desc/BlockSlot.lean) says of a whole chain, through all draws, that the slot's
wants are the declared rounds' wants. A piece of a chain is made of its own stretch of the data,
round by round: for that the fact is wanted round-wise. `OpensAre F D` is that fact; `opensOfData`
shows it under the one premise `F.data file = .ok D`.

Limits. It says nothing of a round's entry, kind, items or trees. A rule for every description: no
description of the protocol is here. Nothing on soundness.

-/
import Johnson.Desc.BlockSlotProofs

set_option autoImplicit false

namespace VerifiableInference.Desc
open OnBytes OnBytes.Maker
open OnBytes.Three (tagRoot tagRun rootsIn)

/-- A round's data hold the declared round's stored tables, and its openings by their numbers over
the file. chain: 0, 1, 2. -/
def RoundOpens {Xi : Type} (F : FileDescription Xi) (chain : ℕ) (d : RDT) (r : Fmt.DeclaredRound) : Prop :=
  d.stored = r.stored ∧ d.opens = r.opens.map fun o => numAt F.t₁ F.t₂ chain o.2

/-- The statement: round by round, chain by chain. At the first chain the data have no sealing
round: the declared rounds are taken without their last. -/
def OpensAre {Xi : Type} (F : FileDescription Xi) (D : WholeD) : Prop :=
  List.Forall₂ (RoundOpens F 0) D.ds₁ F.roundsDeclaredByBlocks.1.dropLast ∧
    List.Forall₂ (RoundOpens F 1) D.ds₂ F.roundsDeclaredByBlocks.2.1 ∧ List.Forall₂ (RoundOpens F 2) D.ds₃ F.roundsDeclaredByBlocks.2.2

/-- The statement: under one premise. -/
def OpensOfData : Prop :=
  ∀ (Xi : Type) (F : FileDescription Xi) (file : String) (D : WholeD), F.data file = .ok D → OpensAre F D

theorem to_opens {Xi : Type} (F : FileDescription Xi) (chain : ℕ) (W : Three.Whole) {ds : List Three.RDL}
    {l : List Fmt.DeclaredRound} (h : List.Forall₂ (RoundIs W (numAt F.t₁ F.t₂ chain)) ds l) :
    List.Forall₂ (RoundOpens F chain) (ds.map rdtOf) l := by
  induction h with
  | nil => exact .nil
  | cons hr _ ih => exact .cons ⟨hr.1, hr.2.1⟩ ih

/-- **`OpensOfData` holds.** -/
theorem opensOfData : OpensOfData := by
  intro Xi F file D h
  obtain ⟨⟨R₁, R₂, R₃⟩, hR, hk, rfl⟩ := data_ok h
  obtain ⟨w₁, w₂, w₃⟩ := writtenOf_ok hR
  have hf : Three.Whole.fits R₁ R₂ R₃ 2 = true := (okAt_parts hk).fits
  have e₁ : rootsIn R₁ = F.t₁ := rootsIn_eq w₁ (fits_roots hf (0, R₁) (by simp))
  have e₂ : rootsIn R₂ = F.t₂ := rootsIn_eq w₂ (fits_roots hf (1, R₂) (by simp))
  have hst : standIns F.roundsDeclaredByBlocks =
      [((List.range (rootsIn R₁)).map tagRoot, tagRun 1),
       ((List.range (rootsIn R₂)).map tagRoot, tagRun 2)] := by
    rw [e₁, e₂]; rfl
  rw [hst] at w₃
  have c₁ : List.Forall₂ (RoundIs (Three.Whole.of R₁ R₂ R₃) (numAt F.t₁ F.t₂ 0))
      (Three.Whole.of R₁ R₂ R₃).ds₁ F.roundsDeclaredByBlocks.1 := by
    rw [← e₁, ← e₂]
    exact chain_is _ _ 0 0 (namesGo₀ _ _) w₁
      fun z hz => fits_trees hf z (List.mem_append_left _ hz)
  have c₂ : List.Forall₂ (RoundIs (Three.Whole.of R₁ R₂ R₃) (numAt F.t₁ F.t₂ 1))
      (Three.Whole.of R₁ R₂ R₃).ds₂ F.roundsDeclaredByBlocks.2.1 := by
    rw [← e₁, ← e₂]
    exact chain_is _ _ _ 0 (namesGo₁ _ _) w₂
      fun z hz => fits_trees hf z (List.mem_append_right _ (List.mem_append_left _ hz))
  have c₃ : List.Forall₂ (RoundIs (Three.Whole.of R₁ R₂ R₃) (numAt F.t₁ F.t₂ 2))
      (Three.Whole.of R₁ R₂ R₃).ds₃ F.roundsDeclaredByBlocks.2.2 := by
    rw [← e₁, ← e₂]
    exact chain_is _ _ _ _ (namesGo₂ _ _) w₃
      fun z hz => fits_trees hf z (List.mem_append_right _ (List.mem_append_right _ hz))
  exact ⟨to_opens F 0 _ (forall₂_dropLast c₁), to_opens F 1 _ c₂, to_opens F 2 _ c₃⟩

end VerifiableInference.Desc

#print axioms VerifiableInference.Desc.opensOfData
