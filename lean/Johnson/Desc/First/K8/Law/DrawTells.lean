-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/K8/Law/DrawTells.lean: THE APPROXIMATE RANGE PROOF's DRAW (the kind K8): THE
SUB-PROTOCOL AT THE DRAW's NUMBER TELLS NO ORACLE MESSAGE: so the counts of trees and of messages
behind it are those in front of it, at all 25 links, at the closed constant's numbers `P5J.At.N Zp
c`. Theorems with their proofs; no definition. They are two
premises, hT and hM, of `drawBlind_mg` (Johnson/P1K8R/BlindAtMg.lean).

  `whole_tells_nothing`: `(K8.whole p).oracles.flatten = []`: by its text.
  `told_of_alone`: a block that is laid alone over `K8.whole p` tells nothing, at its number in the
    flat list: `hear_at_flat`, `alone_oracles` (Johnson/IMR/FlatIx.lean, SeatForm.lean).
  **`told_at_draw`** (1): in the goals' scope, at the opening of the IOP as written in Lean that
    `ProofFile.onlineDescription` returns, l ≤ 24: `(c.blocksInOrder.map fun b => b.oracles.flatten)[ixOf l]? = some []`:
    `k8_of_layers`, `k8_of_attention`, `k8_of_head` (Johnson/IMR/K8Seat.lean), `flatIx_scope`
    (Johnson/IMR/FlatScope.lean). `ixOf`: Johnson/P1K8R/Tied.lean.
  `draw_places_full`: by the kernel: the written list of places has a place at `ixOf l` and at `ixOf
    l + 1`, each at its own first occurrence, at all 25 links.
  **`draw_withTold`** (2): NO PREMISE BUT hT: at any numbers `N₀.withTold ps told` with `told[ixOf
    l]? = some []`: by `MgAt.withTold_next` (Sound/MgAt/K11Tells.lean: general in the list and in
    the number).
  **`draw_at_N`** (3): (1) and (2) at `P5J.At.N Zp c`: `P5J.At.told_is`; `Second.Seam.links_one`
    (`P5J.fullLinks = Sound.linksFull`). Zp IS FREE: the proof reads what c's blocks tell alone.

Limits. Nothing on soundness. On the public data and the blocks' declared oracle messages alone: no
state of the verifier is read. (1) and (3) are in the goals' scope, under the opening.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P1K8R.Tied
import Johnson.Desc.Sound.MgAt.K11Tells
import Johnson.Second.Seam.LinksOne
import Johnson.P5J.LettersAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.K8.Law
open VerifiableInference.Desc (Block Chain Link FileDescription Place Oracle)
open VerifiableInference.Desc.First (S Numbers flatPlacesOf)
open VerifiableInference.Desc.Sound (linksFull)
open P1K8T (ixOf)
open ProofFile (Cl)

/-- The kind, whole, tells no oracle message. -/
theorem whole_tells_nothing (p : ParW) : (whole p).oracles.flatten = [] := rfl

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

theorem told_of_alone {l i k : ℕ} {Lk : Link S Cl} {b : Block S Cl} {p : ParW} {name : String}
    {a : Place} (e1 : c.links[l]? = some Lk) (e2 : Lk.hear[i]? = some b)
    (ef : IM.flatIx c l i = k) (hla : IM.LaidAlone ProofFile.sameReply b (whole p) name a) :
    (c.blocksInOrder.map fun b => b.oracles.flatten)[k]? = some [] := by
  have h3 := IM.hear_at_flat e1 e2
  rw [ef] at h3
  rw [List.getElem?_map, h3]
  show some b.oracles.flatten = some []
  rw [IM.alone_oracles hla]
  rfl

/-- **(1) The sub-protocol at the draw's number tells nothing.** -/
theorem told_at_draw (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l ≤ 24) :
    (c.blocksInOrder.map fun b => b.oracles.flatten)[ixOf l]? = some [] := by
  by_cases h24 : l = 24
  · subst h24
    obtain ⟨Lk, b, Xl, e1, e2, -, hla, -⟩ := IM.k8_of_head hS hR O
    exact told_of_alone e1 e2 (IM.flatIx_scope hS hR O (by decide) 5) hla
  · have ei : ixOf l = 14 * l + 4 + 2 := by
      unfold ixOf
      rw [if_neg h24]
    rw [ei]
    by_cases he : l % 2 = 0
    · obtain ⟨Lk, b, Xl, _, e1, e2, -, hla, -⟩ := IM.k8_of_layers hS hR O (l / 2) (by omega)
      rw [show 2 * (l / 2) = l by omega] at e1 hla
      exact told_of_alone e1 e2 (IM.flatIx_scope hS hR O hl 4) hla
    · obtain ⟨Lk, b, Xl, _, e1, e2, -, hla, -⟩ := IM.k8_of_attention hS hR O (l / 2) (by omega)
      rw [show 2 * (l / 2) + 1 = l by omega] at e1 hla
      exact told_of_alone e1 e2 (IM.flatIx_scope hS hR O hl 4) hla

end

/-- The written list has a place at the draw's number and at the next, each at its own first
occurrence: at all 25 links, by the kernel. -/
theorem draw_places_full : ((List.range 25).all fun l =>
    match (flatPlacesOf linksFull true)[ixOf l]?, (flatPlacesOf linksFull true)[ixOf l + 1]? with
    | some p, some p' => (flatPlacesOf linksFull true).idxOf p == ixOf l &&
        (flatPlacesOf linksFull true).idxOf p' == ixOf l + 1
    | _, _ => false) = true := by decide +kernel

/-- **(2) At numbers off what the sub-protocols tell: behind the draw as in front of it.** -/
theorem draw_withTold (N₀ : Numbers) (told : List (List Oracle)) {l : ℕ} (hl : l ≤ 24)
    (hT : told[ixOf l]? = some []) :
    (N₀.withTold (flatPlacesOf linksFull true) told).treesAt
        (flatPlacesOf linksFull true)[ixOf l + 1]? =
      (N₀.withTold (flatPlacesOf linksFull true) told).treesAt
        (flatPlacesOf linksFull true)[ixOf l]? ∧
    (N₀.withTold (flatPlacesOf linksFull true) told).msgsAt
        (flatPlacesOf linksFull true)[ixOf l + 1]? =
      (N₀.withTold (flatPlacesOf linksFull true) told).msgsAt
        (flatPlacesOf linksFull true)[ixOf l]? := by
  have h := List.all_eq_true.1 draw_places_full l (List.mem_range.2 (by omega))
  cases e1 : (flatPlacesOf linksFull true)[ixOf l]? with
  | none => rw [e1] at h; cases h
  | some p =>
    cases e2 : (flatPlacesOf linksFull true)[ixOf l + 1]? with
    | none => rw [e1, e2] at h; cases h
    | some p' =>
      rw [e1, e2] at h
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      exact VerifiableInference.Desc.Sound.MgAt.withTold_next N₀ _ told p p' (ixOf l) h.1 h.2 hT

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **(3) At the closed constant's numbers: behind the draw as in front of it.** -/
theorem draw_at_N (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (Zp : ProofFile.Pub) {l : ℕ}
    (hl : l ≤ 24) :
    (P5J.At.N Zp c).treesAt (flatPlacesOf linksFull true)[ixOf l + 1]? =
        (P5J.At.N Zp c).treesAt (flatPlacesOf linksFull true)[ixOf l]? ∧
      (P5J.At.N Zp c).msgsAt (flatPlacesOf linksFull true)[ixOf l + 1]? =
        (P5J.At.N Zp c).msgsAt (flatPlacesOf linksFull true)[ixOf l]? := by
  have e : P5J.At.ps = flatPlacesOf linksFull true := by
    unfold P5J.At.ps
    rw [Second.Seam.links_one.1]
  unfold P5J.At.N
  rw [e, P5J.At.told_is]
  exact draw_withTold _ _ hl (told_at_draw hS hR O hl)

end

end VerifiableInference.Desc.First.K8.Law

#print axioms VerifiableInference.Desc.First.K8.Law.whole_tells_nothing
#print axioms VerifiableInference.Desc.First.K8.Law.told_of_alone
#print axioms VerifiableInference.Desc.First.K8.Law.told_at_draw
#print axioms VerifiableInference.Desc.First.K8.Law.draw_places_full
#print axioms VerifiableInference.Desc.First.K8.Law.draw_withTold
#print axioms VerifiableInference.Desc.First.K8.Law.draw_at_N
