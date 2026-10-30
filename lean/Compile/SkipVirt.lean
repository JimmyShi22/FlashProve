-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/SkipVirt.lean: the relation `Skip` under renumberings of tokens (tokens: `Step`,
Rom/Defer.lean).

A token is a number (`Tok`, Rom/Defer.lean: "the value of token i is at place i", `DSt.vals`). A
challenger runs a stateless prover's program under a renumbering of tokens (`virt`,
Compile/Step1_life2_Virt.lean): the program is shown the numbers that it would see if the δ strings
after the first N₀ did not exist. If c₂ is c₁ without work that is never shown (`Rom.Skip`,
Rom/Skip.lean), the same holds of virt N₀ δ₁ c₁ and virt N₀ δ₂ c₂, whatever δ₁ and δ₂ are, for the
correspondence of tokens (`Wd`, there: "how the tokens of two programs correspond") renumbered
likewise (conditions: the row of `Skip.virt`).
  `liftW N₀ δ₁ δ₂ w`   that correspondence
  `Skip.virt`          the statement, for a conclusion Q that does not depend on it and N₀ ≤ w.n₁,
                       N₀ ≤ w.n₂
-/
import Rom.Skip
import Compile.Step1_life2_Virt

namespace Compile
open Rom
open Life2 (virt up)

variable {S : OSpec} {sp : Split S} {α₁ α₂ : Type}

/-- the correspondence w, renumbered by the renumberings of the two programs -/
def liftW (N₀ δ₁ δ₂ : ℕ) (w : Wd) : Wd :=
  ⟨w.n₁ + δ₁, w.n₂ + δ₂,
    fun a b => ∃ a' b', w.ρ a' b' ∧ a = up N₀ δ₁ a' ∧ b = up N₀ δ₂ b',
    fun a => ∃ a', w.dd a' ∧ a = up N₀ δ₁ a',
    fun a b => ∃ a' b', w.sl a' b' ∧ a = up N₀ δ₁ a' ∧ b = up N₀ δ₂ b'⟩

theorem up_sub {N₀ δ t n : ℕ} (hN : N₀ ≤ n) (ht : n + δ ≤ t) : up N₀ δ (t - δ) = t := by
  unfold up
  rw [if_neg (by omega)]
  omega

theorem forall₂_lift {N₀ δ₁ δ₂ : ℕ} {w : Wd} {l₁ l₂ : List Tok} (h : List.Forall₂ w.ρ l₁ l₂) :
    List.Forall₂ (liftW N₀ δ₁ δ₂ w).ρ (l₁.map (up N₀ δ₁)) (l₂.map (up N₀ δ₂)) := by
  induction h with
  | nil => exact .nil
  | cons hab _ ih => exact .cons ⟨_, _, hab, rfl, rfl⟩ ih

theorem rel_lift {N₀ δ₁ δ₂ : ℕ} {w : Wd} {a b : Tok} (h : w.rel a b) :
    (liftW N₀ δ₁ δ₂ w).rel (up N₀ δ₁ a) (up N₀ δ₂ b) :=
  h.imp (fun x => ⟨a, b, x, rfl, rfl⟩) fun x => ⟨a, b, x, rfl, rfl⟩

theorem hid_lift {N₀ δ₁ δ₂ : ℕ} {w : Wd} {a : Tok} (h : w.hid a) :
    (liftW N₀ δ₁ δ₂ w).hid (up N₀ δ₁ a) :=
  h.imp (fun x => ⟨a, x, rfl⟩) fun ⟨b, x⟩ => ⟨up N₀ δ₂ b, a, b, x, rfl, rfl⟩

theorem forall₂_rel_lift {N₀ δ₁ δ₂ : ℕ} {w : Wd} {l₁ l₂ : List Tok} (h : List.Forall₂ w.rel l₁ l₂) :
    List.Forall₂ (liftW N₀ δ₁ δ₂ w).rel (l₁.map (up N₀ δ₁)) (l₂.map (up N₀ δ₂)) := by
  induction h with
  | nil => exact .nil
  | cons hab _ ih => exact .cons (rel_lift hab) ih

theorem lift_shut_le {N₀ δ₁ δ₂ : ℕ} {w : Wd} {t₁ t₂ : ℕ} (hN₁ : N₀ ≤ w.n₁) (hN₂ : N₀ ≤ w.n₂)
    (h₁ : w.n₁ + δ₁ ≤ t₁) (h₂ : w.n₂ + δ₂ ≤ t₂) :
    liftW N₀ δ₁ δ₂ (w.shut (t₁ - δ₁) (t₂ - δ₂)) ≤ (liftW N₀ δ₁ δ₂ w).shut t₁ t₂ where
  n₁ := by show t₁ - δ₁ + 1 + δ₁ ≤ t₁ + 1; omega
  n₂ := by show t₂ - δ₂ + 1 + δ₂ ≤ t₂ + 1; omega
  ρ := fun _ _ h => h
  dd := fun _ h => h
  sl := by
    rintro a b ⟨a', b', hab | ⟨rfl, rfl⟩, rfl, rfl⟩
    · exact Or.inl ⟨a', b', hab, rfl, rfl⟩
    · exact Or.inr ⟨up_sub hN₁ h₁, up_sub hN₂ h₂⟩

theorem lift_pair_le {N₀ δ₁ δ₂ : ℕ} {w : Wd} {t₁ t₂ : ℕ} (hN₁ : N₀ ≤ w.n₁) (hN₂ : N₀ ≤ w.n₂)
    (h₁ : w.n₁ + δ₁ ≤ t₁) (h₂ : w.n₂ + δ₂ ≤ t₂) :
    liftW N₀ δ₁ δ₂ (w.pair (t₁ - δ₁) (t₂ - δ₂)) ≤ (liftW N₀ δ₁ δ₂ w).pair t₁ t₂ where
  n₁ := by show t₁ - δ₁ + 1 + δ₁ ≤ t₁ + 1; omega
  n₂ := by show t₂ - δ₂ + 1 + δ₂ ≤ t₂ + 1; omega
  ρ := by
    rintro a b ⟨a', b', hab | ⟨rfl, rfl⟩, rfl, rfl⟩
    · exact Or.inl ⟨a', b', hab, rfl, rfl⟩
    · exact Or.inr ⟨up_sub hN₁ h₁, up_sub hN₂ h₂⟩
  dd := fun _ h => h
  sl := fun _ _ h => h

theorem lift_dead_le {N₀ δ₁ δ₂ : ℕ} {w : Wd} {t₁ : ℕ} (hN₁ : N₀ ≤ w.n₁) (h₁ : w.n₁ + δ₁ ≤ t₁) :
    liftW N₀ δ₁ δ₂ (w.dead (t₁ - δ₁)) ≤ (liftW N₀ δ₁ δ₂ w).dead t₁ where
  n₁ := by show t₁ - δ₁ + 1 + δ₁ ≤ t₁ + 1; omega
  n₂ := Nat.le_refl _
  ρ := fun _ _ h => h
  dd := by
    rintro a ⟨a', ha | rfl, rfl⟩
    · exact Or.inl ⟨a', ha, rfl⟩
    · exact Or.inr (up_sub hN₁ h₁)
  sl := fun _ _ h => h

/-- `Skip` under two renumberings of tokens, if N₀ ≤ w.n₁ and N₀ ≤ w.n₂ and Q does not depend on the
correspondence. -/
theorem Skip.virt {Q : α₁ → α₂ → Prop} (N₀ δ₁ δ₂ : ℕ) {w : Wd} {c₁ : Step S sp α₁}
    {c₂ : Step S sp α₂} (h : Skip (fun _ => Q) w c₁ c₂) :
    N₀ ≤ w.n₁ → N₀ ≤ w.n₂ →
    Skip (fun _ => Q) (liftW N₀ δ₁ δ₂ w) (virt N₀ δ₁ c₁) (virt N₀ δ₂ c₂) := by
  induction h with
  | pure h => exact fun _ _ => .pure h
  | sample n _ ih => exact fun h₁ h₂ => .sample n fun r => ih r h₁ h₂
  | plain o q _ ih => exact fun h₁ h₂ => .plain o q fun r => ih r h₁ h₂
  | fresh ℓ _ ih =>
    intro hN₁ hN₂
    refine .fresh ℓ fun t₁ t₂ h₁ h₂ => ?_
    have g₁ : _ + δ₁ ≤ t₁ := h₁
    have g₂ : _ + δ₂ ≤ t₂ := h₂
    exact (ih (t₁ - δ₁) (t₂ - δ₂) (by omega) (by omega)
        (by show N₀ ≤ t₁ - δ₁ + 1; omega) (by show N₀ ≤ t₂ - δ₂ + 1; omega)).mono
      (lift_pair_le hN₁ hN₂ g₁ g₂) fun _ _ _ _ _ hq => hq
  | marked o pt inj ht hus _ ih =>
    intro hN₁ hN₂
    refine .marked o pt inj (rel_lift ht) (forall₂_rel_lift hus) fun v t₁ t₂ h₁ h₂ => ?_
    have g₁ : _ + δ₁ ≤ t₁ := h₁
    have g₂ : _ + δ₂ ≤ t₂ := h₂
    exact (ih v (t₁ - δ₁) (t₂ - δ₂) (by omega) (by omega)
        (by show N₀ ≤ t₁ - δ₁ + 1; omega) (by show N₀ ≤ t₂ - δ₂ + 1; omega)).mono
      (lift_pair_le hN₁ hN₂ g₁ g₂) fun _ _ _ _ _ hq => hq
  | markedS o pt inj ht hus _ ih =>
    intro hN₁ hN₂
    refine .markedS o pt inj (rel_lift ht) (forall₂_rel_lift hus) fun v t₁ t₂ h₁ h₂ => ?_
    have g₁ : _ + δ₁ ≤ t₁ := h₁
    have g₂ : _ + δ₂ ≤ t₂ := h₂
    exact (ih v (t₁ - δ₁) (t₂ - δ₂) (by omega) (by omega)
        (by show N₀ ≤ t₁ - δ₁ + 1; omega) (by show N₀ ≤ t₂ - δ₂ + 1; omega)).mono
      (lift_shut_le hN₁ hN₂ g₁ g₂) fun _ _ _ _ _ hq => hq
  | reveal hts _ ih => exact fun h₁ h₂ => .reveal (forall₂_lift hts) fun vs => ih vs h₁ h₂
  | sampleL n _ ih => exact fun h₁ h₂ => .sampleL n fun r => ih r h₁ h₂
  | freshL ℓ _ ih =>
    intro hN₁ hN₂
    refine .freshL ℓ fun t₁ h₁ => ?_
    have g₁ : _ + δ₁ ≤ t₁ := h₁
    exact (ih (t₁ - δ₁) (by omega) (by show N₀ ≤ t₁ - δ₁ + 1; omega) hN₂).mono
      (lift_dead_le hN₁ g₁) fun _ _ _ _ _ hq => hq
  | markedL o us₁ pt inj ht _ ih =>
    intro hN₁ hN₂
    refine .markedL o _ pt inj (hid_lift ht) fun v t₁ h₁ => ?_
    have g₁ : _ + δ₁ ≤ t₁ := h₁
    exact (ih v (t₁ - δ₁) (by omega) (by show N₀ ≤ t₁ - δ₁ + 1; omega) hN₂).mono
      (lift_dead_le hN₁ g₁) fun _ _ _ _ _ hq => hq
  | markedF o us₁ pt inj ht _ ih =>
    intro hN₁ hN₂
    refine .markedF o _ pt inj (hid_lift ht) fun v t₁ t₂ h₁ h₂ => ?_
    have g₁ : _ + δ₁ ≤ t₁ := h₁
    have g₂ : _ + δ₂ ≤ t₂ := h₂
    exact (ih v (t₁ - δ₁) (t₂ - δ₂) (by omega) (by omega)
        (by show N₀ ≤ t₁ - δ₁ + 1; omega) (by show N₀ ≤ t₂ - δ₂ + 1; omega)).mono
      (lift_pair_le hN₁ hN₂ g₁ g₂) fun _ _ _ _ _ hq => hq

end Compile
