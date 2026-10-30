-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/LabelsAtKeyW.lean: the one premise on labels of the proximity test's game in
the labels' form (`LabelsPub`, GameLabels.lean), at the closed full-size place of the key file's
third chain's own test (`piKWFull`, Johnson/Desc/K12/Law/PlacesKeyFull.lean). A definition,
statements and proofs.

Why. `k12_gameV` | `k12_gameSeatV` | `k12_game_alikeV` promise
nothing and are general in a letter nl: «each declared opening's source, numbered over the file, is
nl of its label, and lies below base». Nothing there asks that the sources be the chain's own. At
this place all three openings of the first switch are TAKEN OVER from earlier chains; their labels
are 0, 5 and 1: three labels, all different: so such an nl exists.
  Called: `H2K.Pub.opens_KW` (Johnson/Desc/K12/Law/RoundsAtKeyPlaces.lean):
  the
    first switch's declared openings there, as (label, source): by the kernel.
  `nlKW t₁`: label 1 ↦ t₁ + 1 (the shared chain's tree number 1); every other label ↦ itself (the
    first chain's trees are numbered from 0).
  `labels_KW`: LabelsPub piKWFull (numAt t₁ t₂ 2) (nlKW t₁) base, where 5 < base, t₁ + 1 < base.
  `labels_KW_not`: a control: at nl := id the premise fails wherever 0 < t₁.
What it is not. The place is a closed term typed off a print of the planner's value: that it IS the
key file's place is another file's. The game's other premises at this place (AtPlace at the tile,
the tests on the radii, the bound) are not here. What the numbering by labels costs is spent by the
seam's payer: «nl of the label that the book's tree at a member's place bears is the seat's tree
over the file». No soundness is claimed. Nothing on hiding.

-/
import Johnson.Desc.K12.Coin.GameLabels
import Johnson.Desc.K12.Law.RoundsAtKeyPlaces

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.First (opensOf)
open H2K.Member (piKWFull)

/-- From a label to the tree's number over the file. -/
def nlKW (t₁ ℓ : ℕ) : ℕ := if ℓ = 1 then t₁ + 1 else ℓ

/-- **The labels' premise at the key file's third chain's own test.** -/
theorem labels_KW (t₁ t₂ base : ℕ) (h0 : 5 < base) (h1 : t₁ + 1 < base) :
    LabelsPub piKWFull (numAt t₁ t₂ 2) (nlKW t₁) base := by
  intro a rest hs o ho
  have e' : (opensOf piKWFull a.k).map (fun o => (o.1.tree, o.2)) =
      [(0, .taken 0 0), (5, .taken 0 5), (1, .taken 1 1)] := by
    have e := H2K.Pub.opens_KW
    simp only [H2K.Pub.opensAt, hs] at e
    exact e
  have hm : (o.1.tree, o.2) ∈ (opensOf piKWFull a.k).map fun o => (o.1.tree, o.2) :=
    List.mem_map.2 ⟨o, ho, rfl⟩
  rw [e'] at hm
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
  rcases hm with ⟨a1, a2⟩ | ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rw [a1, a2] <;>
    simp only [numAt, nlKW] <;> constructor <;> simp <;> omega

/-- A control: the labels read as they stand will not do. -/
theorem labels_KW_not (t₁ t₂ base : ℕ) (h : 0 < t₁) :
    ¬ LabelsPub piKWFull (numAt t₁ t₂ 2) id base := by
  intro H
  cases hs : piKWFull.nums.stages with
  | nil =>
    have e := H2K.Pub.opens_KW
    simp only [H2K.Pub.opensAt, hs] at e
    cases e
  | cons a rest =>
    have e' : (opensOf piKWFull a.k).map (fun o => (o.1.tree, o.2)) =
        [(0, .taken 0 0), (5, .taken 0 5), (1, .taken 1 1)] := by
      have e := H2K.Pub.opens_KW
      simp only [H2K.Pub.opensAt, hs] at e
      exact e
    have hm : ((1 : ℕ), Fmt.TreeSource.taken 1 1) ∈
        (opensOf piKWFull a.k).map fun o => (o.1.tree, o.2) := by
      rw [e']
      simp
    obtain ⟨o, ho, eo⟩ := List.mem_map.1 hm
    have h1 := (H a rest hs o ho).1
    have a1 : o.1.tree = 1 := congrArg Prod.fst eo
    have a2 : o.2 = .taken 1 1 := congrArg Prod.snd eo
    rw [a1, a2] at h1
    simp [numAt] at h1
    omega

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.labels_KW
#print axioms VerifiableInference.Desc.K12.Coin.labels_KW_not
