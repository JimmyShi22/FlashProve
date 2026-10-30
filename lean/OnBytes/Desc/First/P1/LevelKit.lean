-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Desc/First/P1/LevelKit.lean: small things that the laws of a layer of a product tree and of
a token sumcheck (LevelLaw.lean, TscLaw.lean) both use. Definitions, statements and proofs.

  `held_equality`, `held_atZero`: the weights of these rounds pass the two tests that every round
    makes of its weight.
  `hidingWalk_length`: the hiding polynomial has just `hidingEntries` coefficients.
  `shown_some`, `foldlM_some_all`, `filledA_of_publicPart`: a form whose public part is there names
    filled slots alone.
  `slot_worldOf`: the hidden value under a slot, in the world of a ledger: what is shown less the
    factor times the mask entry. This is the definition of that world.
  `levelXs`, `twos_level`, `held_level`: the two weights of each of a layer's rounds.

It holds no law.
-/
import OnBytes.Desc.First.P1.FlSpec
import OnBytes.Desc.First.P1.PscProducts
import OnBytes.Tie.Pv.Psc.PscHeld
import OnBytes.Tie.Pv.Lookup.Forest.FoForm

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace OnBytes.Desc.First.P1
open OnBytes OnBytes.Model OnBytes.K.Kc Polynomial
open OnBytes.PscRun (Sized Filled hideRun_ok)

variable {K : Type} [Field K] (ρ : Reading K)

/-! ### Small things -/

theorem held_equality (z : E) (d : ℕ) (h : 2 ≤ d) : Held (OnBytes.Psc.Weight.equality z d) :=
  ⟨(OnBytes.PscRun.fits_equality z d).mpr h, OnBytes.PscRun.weightHeld_equality z d⟩

theorem held_atZero (d : ℕ) (h : 2 ≤ d) : Held (OnBytes.Psc.Weight.atZero d) :=
  held_equality zeroE d h

/-- The hiding polynomial has just `hidingEntries` coefficients. -/
theorem hidingWalk_length : ∀ vr : List (OnBytes.Psc.Weight × E), vr ≠ [] →
    (∀ x ∈ vr, 1 ≤ x.1.d) →
    (OnBytes.Psc.hidingWalk vr).1.length = OnBytes.Psc.hidingEntries (vr.map (·.1))
  | [], h, _ => absurd rfl h
  | [(w, g)], _, hd => by
    have h1 : 1 ≤ w.d := hd (w, g) (by simp)
    show (OnBytes.Psc.powers oneE g w.d).length = 1 + ([w].map fun w => w.d - 1).sum
    rw [powers_eq, powersFrom_length]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega
  | (w, g) :: y :: rest, _, hd => by
    have ih := hidingWalk_length (y :: rest) (by simp) fun x hx => hd x (by simp [hx])
    show (OnBytes.Psc.powers (mulE (OnBytes.Psc.hidingWalk (y :: rest)).2 g) g (w.d - 1) ++
      (OnBytes.Psc.hidingWalk (y :: rest)).1).length =
        1 + ((w :: (y :: rest).map (·.1)).map fun w => w.d - 1).sum
    rw [List.length_append, powers_eq, powersFrom_length,
      List.map_cons, List.sum_cons]
    unfold OnBytes.Psc.hidingEntries at ih
    omega

theorem shown_some {F : Fork} {j : ℕ} {y : E} (h : F.shown j = some y) :
    j < F.ns ∧ Filled F j ∧ y = F.vp.getD j zeroE := by
  unfold Fork.shown at h
  split at h
  · rename_i hc
    rw [Bool.and_eq_true, decide_eq_true_eq] at hc
    exact ⟨hc.1, hc.2, (Option.some.inj h).symm⟩
  · exact absurd h (by simp)

theorem foldlM_some_all {α σ : Type} {f : σ → α → Option σ} {P : α → Prop}
    (H : ∀ s a s', f s a = some s' → P a) : ∀ (l : List α) (s s' : σ), l.foldlM f s = some s' →
    ∀ x ∈ l, P x
  | [], _, _, _, _, hx => by simp at hx
  | a :: l, s, s', h, x, hx => by
    rw [List.foldlM_cons] at h
    cases hq : f s a with
    | none => simp [hq] at h
    | some t =>
      rw [hq] at h
      have h2 : l.foldlM f t = some s' := by simpa using h
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact H s x t hq
      · exact foldlM_some_all H l t s' h2 x hx'

/-- A form whose public part is there names filled slots alone. -/
theorem filledA_of_publicPart {F : Fork} {C : Aff} {T : E} (h : F.publicPart C = some T) :
    Fo.FilledA F C := by
  unfold Fork.publicPart at h
  rw [← Array.foldlM_toList] at h
  refine foldlM_some_all (P := fun x : Nat × E => x.1 < F.ns ∧ Filled F x.1) ?_ _ _ _ h
  intro s a s' hs
  cases hq : F.shown a.1 with
  | none => simp [hq] at hs
  | some y => exact ⟨(shown_some hq).1, (shown_some hq).2.1⟩

/-- The hidden value under a slot, in the world of a ledger. -/
theorem slot_worldOf (H : Fork) (mask : ℕ → K) (entry : ℕ → ℕ → ℕ → K) (j : ℕ) :
    (H.worldOf ρ mask entry).slot j =
      ρ.val (H.vp.getD j zeroE) - ρ.val (H.mf.getD j zeroE) * mask j := rfl

/-- The two weights of each of a layer's rounds. -/
def levelXs (mu : Nat) (rho : Array E) (order : List Nat) : List (K × K) :=
  order.map fun v => (1 - ρ.val (rho.getD (mu - 1 - v) zeroE), ρ.val (rho.getD (mu - 1 - v) zeroE))

theorem twos_level (mu : Nat) (rho : Array E) : ∀ order : List Nat,
    Twos 3 ((levelWs mu rho order).map (wtOf ρ)) (levelXs ρ mu rho order)
  | [] => trivial
  | v :: order =>
    ⟨two_equality ρ _ 3 (by omega), le_refl 3, twos_level mu rho order⟩

theorem held_level (mu : Nat) (rho : Array E) (order : List Nat) :
    ∀ w ∈ levelWs mu rho order, Held w := by
  intro w hw
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp hw
  exact held_equality _ 3 (by omega)

end OnBytes.Desc.First.P1
