-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/ToldDescR/Retype.lean: WHAT STAYS OF A CHAIN
WITHOUT LINKS WHEN IT IS CARRIED TO ANOTHER TYPE OF CLAIMS (`Chain.retype`, Johnson/Desc/Block.lean).

Why. In Johnson/Desc/Block.lean a file's description has one type of claims for its three
chains, and the frame of the proof file's description lays the two later chains, which their files
type at `Unit`, by `Chain.retype`. So a fact on a seat's own chain (its places, its rounds, its
blocks' tests on the plan) reaches the description's chain only through these equations.
Main names.
  `flat_retype_by`      two readings that agree block by block read the same list off the carried
                        chain's flat list as off the chain's own
  `flat_retype_map`     so does whatever reads of a block neither its test on the plan nor its claims
  `places_retype` · `rounds_retype` · `length_retype`   that rule at the place, the rounds, the length
  `blocksOk_retype`     `blocksOk` says the same of both flat lists
  `flat_retype`         the carried chain's flat list is the chain's own, block by block carried
Limits. Tools: they hold of every chain without links, so they say nothing of the protocol. Nothing
is said here of a chain that has a link.

-/
import Johnson.Desc.BlockLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ToldDesc
open VerifiableInference.Desc (Block Chain Link Place blocksOk)

variable {σ Cl Cl' α : Type}

/-- **Two readings that agree block by block read the same off both flat lists.** g' reads a block
at the new type of claims, g at the old one. `h₁`: they agree at the first block, whose carried form
asks one test more; `hg`: they agree at every other block as the flat list lays it. -/
theorem flat_retype_by (c : Chain σ Cl) (hl : c.links = []) (g : Block σ Cl → α)
    (g' : Block σ Cl' → α)
    (h₁ : g' (c.retype : Chain σ Cl').first.asBare = g c.first.asBare)
    (hg : ∀ b : Block σ Cl, g' (b.retype : Block σ Cl').asBare = g b.asBare) :
    (c.retype : Chain σ Cl').blocksInOrder.map g' = c.blocksInOrder.map g := by
  have hm : ∀ l : List (Block σ Cl),
      List.map (g' ∘ Block.asBare ∘ Block.retype) l = List.map (g ∘ Block.asBare) l :=
    fun l => List.map_congr_left fun b _ => hg b
  have h₄ : g' (c.retype : Chain σ Cl').last.asBare = g c.last.asBare := hg _
  have r₁ : (c.retype : Chain σ Cl').front = c.front.map Block.retype := rfl
  have r₂ : (c.retype : Chain σ Cl').back = c.back.map Block.retype := rfl
  have r₃ : (c.retype : Chain σ Cl').links = [] := rfl
  rw [Chain.flat_eq, Chain.flat_eq, hl, r₁, r₂, r₃]
  simp only [List.flatMap_nil, List.append_nil, List.map_cons, List.map_append, List.map_nil,
    List.map_map, hm, h₁, h₄]

/-- **What reads neither the test on the plan nor the claims reads the same off both flat lists.**
g and g' are the same reading at the two types of claims: `hg` says so, at every pair of answers of
the test on the plan. -/
theorem flat_retype_map (c : Chain σ Cl) (hl : c.links = []) (g : Block σ Cl → α)
    (g' : Block σ Cl' → α)
    (hg : ∀ (b : Block σ Cl) (x y : Bool),
      g' { (b.retype : Block σ Cl') with planOk := x } = g { b with planOk := y }) :
    (c.retype : Chain σ Cl').blocksInOrder.map g' = c.blocksInOrder.map g :=
  flat_retype_by c hl g g' (hg _ _ _) fun b => hg b _ _

/-- The places. -/
theorem places_retype (c : Chain σ Cl) (hl : c.links = []) :
    (c.retype : Chain σ Cl').blocksInOrder.map (·.place) = c.blocksInOrder.map (·.place) :=
  flat_retype_map c hl _ _ fun _ _ _ => rfl

/-- The declared rounds. -/
theorem rounds_retype (c : Chain σ Cl) (hl : c.links = []) :
    (c.retype : Chain σ Cl').blocksInOrder.map (·.rounds) = c.blocksInOrder.map (·.rounds) :=
  flat_retype_map c hl _ _ fun _ _ _ => rfl

/-- The length. -/
theorem length_retype (c : Chain σ Cl) (hl : c.links = []) :
    (c.retype : Chain σ Cl').blocksInOrder.length = c.blocksInOrder.length := by
  have e := congrArg List.length (places_retype (Cl' := Cl') c hl)
  rwa [List.length_map, List.length_map] at e

/-- A block as the flat list lays it, carried or not, answers `blocksOk`'s question alike. -/
theorem ok_retype (b : Block σ Cl) :
    ((b.retype : Block σ Cl').asBare.planOk && (b.retype : Block σ Cl').asBare.shaped) =
      (b.asBare.planOk && b.asBare.shaped) := by
  show ((b.planOk && b.claims.isEmpty) && (true && b.after.isEmpty) && b.shaped) =
    ((b.planOk && (b.claims.isEmpty && b.after.isEmpty)) && b.shaped)
  simp only [Bool.true_and, Bool.and_assoc]

/-- **`blocksOk` says the same of both flat lists.** -/
theorem blocksOk_retype (c : Chain σ Cl) (hl : c.links = []) :
    blocksOk (c.retype : Chain σ Cl').blocksInOrder = blocksOk c.blocksInOrder := by
  have h₁ : ((c.retype : Chain σ Cl').first.asBare.planOk &&
      (c.retype : Chain σ Cl').first.asBare.shaped) =
      (c.first.asBare.planOk && c.first.asBare.shaped) := by
    show (((c.first.planOk && c.first.claims.isEmpty) && c.links.isEmpty) &&
        (true && c.first.after.isEmpty) && c.first.shaped) =
      ((c.first.planOk && (c.first.claims.isEmpty && c.first.after.isEmpty)) && c.first.shaped)
    rw [hl]
    simp only [List.isEmpty_nil, Bool.true_and, Bool.and_true, Bool.and_assoc]
  have e := flat_retype_by (Cl' := Cl') c hl (fun b => b.planOk && b.shaped)
    (fun b => b.planOk && b.shaped) h₁ ok_retype
  have k := congrArg (fun l : List Bool => l.all id) e
  simp only [List.all_map] at k
  exact k

/-- Carried, then laid outside the links, is laid outside the links, then carried. -/
theorem asBare_retype (b : Block σ Cl) :
    (b.retype : Block σ Cl').asBare = (b.asBare.retype : Block σ Cl') := by
  have e : ((b.planOk && b.claims.isEmpty) && (true && b.after.isEmpty)) =
      ((b.planOk && (b.claims.isEmpty && b.after.isEmpty)) && b.claims.isEmpty) := by
    cases b.planOk <;> cases b.claims.isEmpty <;> cases b.after.isEmpty <;> rfl
  exact congrArg (fun x => ({ (b.retype : Block σ Cl') with planOk := x } : Block σ Cl')) e

/-- **The carried chain's flat list is the chain's own flat list, each block carried.** -/
theorem flat_retype (c : Chain σ Cl) (hl : c.links = []) :
    (c.retype : Chain σ Cl').blocksInOrder = c.blocksInOrder.map Block.retype := by
  have h₁ : (c.retype : Chain σ Cl').first.asBare = (c.first.asBare.retype : Block σ Cl') := by
    have e : (((c.first.planOk && c.first.claims.isEmpty) && c.links.isEmpty) &&
        (true && c.first.after.isEmpty)) =
        ((c.first.planOk && (c.first.claims.isEmpty && c.first.after.isEmpty)) &&
          c.first.claims.isEmpty) := by
      rw [hl]
      cases c.first.planOk <;> cases c.first.claims.isEmpty <;> cases c.first.after.isEmpty <;> rfl
    exact congrArg (fun x => ({ (c.first.retype : Block σ Cl') with planOk := x } : Block σ Cl')) e
  have k := flat_retype_by (Cl' := Cl') c hl Block.retype id h₁ asBare_retype
  rwa [List.map_id] at k

end ToldDesc

#print axioms ToldDesc.asBare_retype
#print axioms ToldDesc.flat_retype
#print axioms ToldDesc.flat_retype_by
#print axioms ToldDesc.flat_retype_map
#print axioms ToldDesc.places_retype
#print axioms ToldDesc.rounds_retype
#print axioms ToldDesc.length_retype
#print axioms ToldDesc.ok_retype
#print axioms ToldDesc.blocksOk_retype
