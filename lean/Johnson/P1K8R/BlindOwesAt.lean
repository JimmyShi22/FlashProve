-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/BlindOwesAt.lean: WHAT IS LEFT OF THE SMALLNESS TEST's FIELD "blind" AT THE CLOSED
CONSTANT OF THE COMPOSED MEANING (`BlindOwes`, Johnson/P1K8R/BlindJoin.lean: wt, readers, fence,
trees, msgs), SORT OF SEGMENT BY SORT OF SEGMENT, FROM THE HEAD `P5J.AtMgA`, wt AND fence.
A joining of several other files' theorems.
  `headLink_at`: from the head: `headLink (At.X Zp) = 24`. (The text of `headLink_in_scope`,
    Johnson/P5J/RowsAtMg.lean, by `Meaning.scope_plans`: typed again in four lines, so that this
    file does not hang on that file's cone.)
  `blindOwes_layers`: **at the 12 feed-forward links l = 2 g: wt and fence give `BlindOwes`.**
  `blindOwes_attention`: **at the 12 attention links l = 2 g + 1: the like.**
  `blindOwes_head`: **at the output head's link 24: the like.**
  `blindOwes_all`: **AT EACH l ≤ 24: wt and fence give `BlindOwes h l base`.**
Proved inside: readers (Johnson/P1K8R/ReadersAll.lean, WalkK5.lean, WalkK6.lean); trees and msgs
(`draw_at_N`, Johnson/Desc/First/K8/Law/DrawTells.lean). Taken from the head's own fields: the
opening's letters, the scope, and "the ground's public data are the constant's" (`IM.Open.W`).
Limits. At `OnBytes.secondHashFunction` alone. wt and fence are shown nowhere here. A member of the head `AtMgA`
is proved at `storedPublicFiles` and `zGap` alone (at secondHashFunction; side library AtFullSide/Top/). The other premises
here follow from the head; no file joins them to a member. Nothing on soundness or on hiding.

-/
import Johnson.P1K8R.BlindJoin
import Johnson.P1K8R.ReadersAll
import Johnson.P1K8R.WalkK5
import Johnson.P1K8R.WalkK6
import Johnson.Desc.First.K8.Law.DrawTells
import Johnson.Goal.Meaning.PlanShapes

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace P1K8T

open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat
open VerifiableInference.Desc (Chain Strs Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S flatPlacesOf sampledIn openSets start)
open VerifiableInference.Desc.First.K8
open VerifiableInference.Desc.K9 (statesOfLink)
open VerifiableInference.OnPublicFiles (headLink)
open ProofFile (Cl)
open P5J (AtMgA mgAtAll)

section
variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}

theorem headLink_at (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀) :
    headLink (P5J.At.X Zp) = 24 := by
  obtain ⟨p4, ng, -⟩ := Meaning.scope_plans h.scope h.reads h.pubOne
  unfold headLink
  rw [p4, ng]
  rfl

theorem blindOwes_layers (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀) (g : ℕ) (hg : g < 12)
    (base : ℕ)
    (hwt : ∀ z s t y y' w, Drawn s t → SameBelow base y y' → h.𝔇.wt (2 * g) (z, t) y' w →
      h.𝔇.wt (2 * g) (z, s) y w)
    (hf : ∀ y ∈ sampledIn (P5J.At.N Zp cF) ((openSets linksFull (flatPlacesOf linksFull true)
      (start linksFull))[ixOf (2 * g)]?.getD []), y.1 < base) : BlindOwes h (2 * g) base := by
  obtain ⟨Bs, bs, O⟩ := h.laid.opened
  have hd := Law.draw_at_N h.scope h.reads O Zp (l := 2 * g) (by omega)
  exact ⟨hwt, readers_const_layers _ _ _ _ _ _ _ _ _ _ _ _ _ _ h.scope h.reads O (headLink_at h) O.W
    g hg, hf, hd.1, hd.2⟩

theorem blindOwes_attention (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀) (g : ℕ) (hg : g < 12)
    (base : ℕ)
    (hwt : ∀ z s t y y' w, Drawn s t → SameBelow base y y' → h.𝔇.wt (2 * g + 1) (z, t) y' w →
      h.𝔇.wt (2 * g + 1) (z, s) y w)
    (hf : ∀ y ∈ sampledIn (P5J.At.N Zp cF) ((openSets linksFull (flatPlacesOf linksFull true)
      (start linksFull))[ixOf (2 * g + 1)]?.getD []), y.1 < base) :
    BlindOwes h (2 * g + 1) base := by
  obtain ⟨Bs, bs, O⟩ := h.laid.opened
  have hd := Law.draw_at_N h.scope h.reads O Zp (l := 2 * g + 1) (by omega)
  exact ⟨hwt, readers_const_attention _ _ _ _ _ _ _ _ _ _ _ _ _ _ h.scope h.reads O (headLink_at h)
    O.W g hg (k5_states_blind h.scope h.reads O g hg), hf, hd.1, hd.2⟩

theorem blindOwes_head (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀) (base : ℕ)
    (hwt : ∀ z s t y y' w, Drawn s t → SameBelow base y y' → h.𝔇.wt 24 (z, t) y' w →
      h.𝔇.wt 24 (z, s) y w)
    (hf : ∀ y ∈ sampledIn (P5J.At.N Zp cF) ((openSets linksFull (flatPlacesOf linksFull true)
      (start linksFull))[ixOf 24]?.getD []), y.1 < base) :
    BlindOwes h 24 base := by
  obtain ⟨Bs, bs, O⟩ := h.laid.opened
  have hd := Law.draw_at_N h.scope h.reads O Zp (l := 24) (Nat.le_refl 24)
  exact ⟨hwt, readers_const_head2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ h.scope h.reads O (headLink_at h)
    callerReaders_blind (k6_states_blind h.scope h.reads O), hf, hd.1, hd.2⟩

/-- **AT EACH OF THE 25 LINKS: wt AND THE FENCE GIVE `BlindOwes`.** -/
theorem blindOwes_all (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀) {l : ℕ} (hl : l ≤ 24)
    (base : ℕ)
    (hwt : ∀ z s t y y' w, Drawn s t → SameBelow base y y' → h.𝔇.wt l (z, t) y' w →
      h.𝔇.wt l (z, s) y w)
    (hf : ∀ y ∈ sampledIn (P5J.At.N Zp cF) ((openSets linksFull (flatPlacesOf linksFull true)
      (start linksFull))[ixOf l]?.getD []), y.1 < base) : BlindOwes h l base := by
  rcases Nat.lt_or_ge l 24 with h24 | h24
  · rcases Nat.even_or_odd' l with ⟨g, rfl | rfl⟩
    · exact blindOwes_layers h g (by omega) base hwt hf
    · exact blindOwes_attention h g (by omega) base hwt hf
  · obtain rfl : l = 24 := Nat.le_antisymm hl h24
    exact blindOwes_head h base hwt hf

end

end P1K8T

#print axioms P1K8T.headLink_at
#print axioms P1K8T.blindOwes_layers
#print axioms P1K8T.blindOwes_attention
#print axioms P1K8T.blindOwes_head
#print axioms P1K8T.blindOwes_all
