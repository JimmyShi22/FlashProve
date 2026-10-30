-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Key/KeyBattBy.lean: THE KEY FILE's ROW 1.16 (batt.1.batt := Key.batchTableRows): THE SEAT MEETS THE ONE PREMISE ON THE BLOCK OF THE KIND K13's LAW (Johnson/Desc/K13/Law/GoodAny.lean: goodIn_any asks ByBatt b P partF rowB).
Carried by hand from Johnson/RunOne/KeyBattBy.lean, which is not in this library, to the library names over the one base; with byBatt_held: the same of the block AS A PIECE HOLDS IT (Sound.held: the words' test in front; the instance beside the state).
  lensLaw_key · pileOpt · byBatt_batch · ByBatt.held · byBatt_held
EMPTY WHERE the seat refuses all. Nothing on soundness.
-/
import Johnson.Desc.K13.Law.GoodAny
import Johnson.Desc.Key.KeyAndThen
import Johnson.Desc.Key.KeyLensLaws
import Johnson.Desc.Sound.PaidAtDesc

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Key
open OnBytes OnBytes.Params
open VerifiableInference.Desc.K13.Law (ByBatt LensLaw lensLaw_of_same byBatt_joined partIn rowOut)

variable {β Cl : Type}

theorem lensLaw_key : LensLaw (batchLens (β := β)) :=
  lensLaw_of_same _ fun t p p' hg h1 h2 h3 h4 => lens_get_set_same t p p' hg h1 h2 h3 h4

/-- What layPile leaves, as an option. -/
def pileOpt (keysOf : β → List (List Lkp.Keys)) (one : OneTime) (t : ChainState β) : Option (ChainState β) :=
  match layPile keysOf one t with
  | .ok t₁ => some t₁
  | .error _ => none

/-- **The seat meets the law's one premise on the block.** -/
theorem byBatt_batch (keysOf : β → List (List Lkp.Keys)) (one : OneTime) (N : Pieces) (sent : Nat) :
    ByBatt (batchTableRows (Cl := Cl) keysOf one N sent) (batchWhere one N sent)
      (fun t => (pileOpt keysOf one t).bind (partIn (batchLens (β := β)))) (rowOut (batchLens (β := β))) := by
  have hJ := byBatt_joined (Cl := Cl) (batchLens (β := β)) lensLaw_key (batchWhere one N sent) "the front and the batching" "the kind's three"
  have hB := hJ.behind (quietAt "the rows on the table" ⟨1, none, (batchWhere one N sent).piece, .K13⟩ (layPile keysOf one)) "batt.1.batt" rfl (pileOpt keysOf one)
    (fun t rs gs t₁ h => by
      have h' : layPile keysOf one t = .ok t₁ := h
      unfold pileOpt
      rw [h'])
  refine ⟨fun t t' rs gs h => hB.yes t t' rs gs ?_⟩
  rw [← joined4_decide "the rows and the front" "the rows, the front and the batching" "batt.1.batt"]
  exact h

/-- **The premise rides to the block as a piece holds it.** -/
theorem _root_.VerifiableInference.Desc.K13.Law.ByBatt.held {T Pb : Type} {b : Block T Cl} {P : K13.Where} {partF : T → Option K13.Part} {rowB : T → List TensorRow}
    (h : ByBatt b P partF rowB) : ByBatt (Sound.held (P := Pb) b) P (fun a => partF a.2) (fun a => rowB a.2) where
  yes := by
    intro t t' rs gs hd
    have hd' : ((Sound.below b).decide t.2 rs gs).map (fun s => (t.1, s)) = .ok t' := hd
    cases hb : (Sound.below b).decide t.2 rs gs with
    | error e => rw [hb] at hd'; cases hd'
    | ok s' =>
      rw [hb] at hd'
      obtain rfl : (t.1, s') = t' := Except.ok.inj hd'
      have hb' : (if viewWordsBelowPrime ⟨rs, (gs.flatMap id).map fun c => (0, c.1, c.2)⟩ then b.decide t.2 rs gs else .error "a word is not below the prime") = .ok s' := hb
      split at hb'
      · exact h.yes _ _ _ _ hb'
      · cases hb'

theorem byBatt_held {Pb : Type} (keysOf : β → List (List Lkp.Keys)) (one : OneTime) (N : Pieces) (sent : Nat) :
    ByBatt (Sound.held (P := Pb) (batchTableRows (Cl := Cl) keysOf one N sent)) (batchWhere one N sent)
      (fun a => (pileOpt keysOf one a.2).bind (partIn (batchLens (β := β)))) (fun a => rowOut (batchLens (β := β)) a.2) :=
  (byBatt_batch keysOf one N sent).held

end VerifiableInference.Desc.Key

#print axioms VerifiableInference.Desc.Key.byBatt_batch
#print axioms VerifiableInference.Desc.Key.byBatt_held
