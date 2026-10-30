-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoTallyDoor.lean.
The closing routines of a sub-proof's check leave the number of claims added and the number of
claims planned as they were.

`Tally` (OnBytes/Tie/Pv/Lookup/Ends/FoTally.lean) of HTailF2.selfTestF, tileSelfTestF, coefficientsF
and of doorTerms; `TallyL` (OnBytes/Tie/Pv/Lookup/Ends/FoTallyLink.lean) of doorH. coefficientsF
changes the whole state by a function that is written with loops; `forIn_id`, `forIn_idA`,
`bindId`: a property that each step of such a loop keeps is kept by the loop.
Does not say: anything on the equation that doorH passes to the chain.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoTallyLink
import OnBytes.Model.Tail

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun

/-- What a step of a loop leaves. -/
def stepLeft {σ : Type} : ForInStep σ → σ
  | .done b => b
  | .yield b => b

theorem forIn_id {α σ : Type} (P : σ → Prop) (f : α → σ → Id (ForInStep σ))
    (hf : ∀ a s, P s → P (stepLeft (f a s))) : ∀ (l : List α) (s : σ), P s → P (forIn l s f : Id σ)
  | [], s, h => by
    rw [List.forIn_nil]
    exact h
  | a :: l, s, h => by
    rw [List.forIn_cons]
    have h1 := hf a s h
    show P (match f a s with
      | .done b => b
      | .yield b => (forIn l b f : Id σ))
    generalize f a s = r at h1
    cases r with
    | done b => exact h1
    | yield b => exact forIn_id P f hf l b h1

theorem forIn_idA {α σ : Type} (P : σ → Prop) (f : α → σ → Id (ForInStep σ))
    (hf : ∀ a s, P s → P (stepLeft (f a s))) (l : Array α) (s : σ) (h : P s) :
    P (forIn l s f : Id σ) := by
  rw [← Array.forIn_toList]
  exact forIn_id P f hf _ s h

theorem bindId {β γ : Type} {P : β → Prop} {Q : γ → Prop} {x : Id β} {k : β → Id γ} (hx : P x)
    (hk : ∀ b, P b → Q (k b)) : Q (x >>= k) := hk x hx

theorem onRow_cl {F s : Fork} (h : TallyRel F s) (t r : Nat) (f : HRow → HRow) :
    TallyRel F (HTailF2.onRow s t r f) := h

theorem Tally.coefficientsF (tl : HTailF2) : Tally tl.coefficientsF := by
  unfold HTailF2.coefficientsF
  refine (Tally.getO _).bind fun g => Tally.modify fun F => ?_
  refine bindId (P := TallyRel F) (Q := TallyRel F)
    (forIn_id (TallyRel F) _ (fun n s hs => ?_) _ _ (TallyRel.refl F)) fun r1 h1 => ?_
  · dsimp only
    split
    · split
      · exact onRow_cl hs _ _ _
      · exact hs
    · exact hs
  refine bindId (P := TallyRel F) (Q := TallyRel F)
    (forIn_id (TallyRel F) _ (fun q s hs => ?_) _ _ h1) fun r2 h2 => ?_
  · refine bindId (P := TallyRel F) (Q := fun x => TallyRel F (stepLeft x))
      (forIn_idA (TallyRel F) _ (fun p s' hs' => ?_) _ _ hs) fun r hr => hr
    exact onRow_cl hs' _ _ _
  refine bindId (P := TallyRel F) (Q := TallyRel F) (forIn_id (TallyRel F) _ (fun e s hs => ?_) _ _
    (onRow_cl (onRow_cl h2 _ _ _) _ _ _)) fun r3 h3 => ?_
  · exact onRow_cl hs _ _ _
  refine bindId (P := TallyRel F) (Q := TallyRel F) (forIn_id (TallyRel F) _ (fun mu s hs => ?_) _ _
    (onRow_cl h3 _ _ _)) fun r4 h4 => h4
  exact onRow_cl hs _ _ _

theorem Tally.selfTestF (tl : HTailF2) (nU : Array Nat) : Tally (tl.selfTestF nU) := by tally
theorem Tally.tileSelfTestF (tl : HTailF2) : Tally tl.tileSelfTestF := by tally
theorem Tally.doorTerms (born : Nat) (array : String) (X : HTree) :
    Tally (doorTerms born array X) := by tally
theorem TallyL.doorH (n : Nat) : TallyL (doorH n) := by tally

end Fo
