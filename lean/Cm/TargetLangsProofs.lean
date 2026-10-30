-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/TargetLangsProofs.lean: lemmas on the index's side of Cm/TargetLangs.lean.

Main names:
  `targetHeld_body`, `targetHeld_congr`: the entries of an index hold it, if the characteristic of
    F is at least 256 and different entries have different places; what a table holds is read at
    the places alone.

Limits: what the head of Cm/TargetLangs.lean lists as not said is not said here either.
-/
import Cm.TargetLangs

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm

open Inst.Model Inst.Model.All Iop Prob Hiop Cb
open Inst.Model.Layout (kRef hRef)

/-- an entry of an index is a signed byte -/
theorem idx_byte (i : Idx) (q : TargetEnt) : -128 ≤ i.val q.1 q.2 ∧ i.val q.1 q.2 < 128 := by
  have h := i.wf.1 q.1.val q.1.isLt q.2.val q.2.isLt
  have e : i.mat q.1.val q.2.val = i.val q.1 q.2 :=
    dif_pos (⟨q.1.isLt, q.2.isLt⟩ : q.1.val < hRef ∧ q.2.val < 2 ^ kRef)
  rw [e] at h
  constructor
  · have := h.1
    norm_num at this
    exact this
  · have := h.2
    norm_num at this
    exact this

/-- a signed byte is read back from its image in a field of characteristic at least 256 -/
theorem byte_cast_inj {F : Type} [Field F] (p : ℕ) [CharP F p] (hp : 256 ≤ p) {a b : ℤ}
    (ha : -128 ≤ a ∧ a < 128) (hb : -128 ≤ b ∧ b < 128) (h : (a : F) = (b : F)) : a = b := by
  have h0 : ((a - b : ℤ) : F) = 0 := by rw [Int.cast_sub, h, sub_self]
  have hd : (p : ℤ) ∣ a - b := (CharP.intCast_eq_zero_iff F p (a - b)).1 h0
  have hp' : (256 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp
  have hz : a - b = 0 := Int.eq_zero_of_abs_lt_dvd hd (by
    rw [abs_lt]
    constructor <;> omega)
  omega

section
variable {F E : Type} [Field F] [Field E] [Algebra F E]
  (Cf₀ : LdCf F E) (pl : TargetEnt → Cf₀.Row × Cf₀.Lay)

theorem targetBody_at (hinj : Function.Injective (targetAt Cf₀ pl)) (i : Idx) (q : TargetEnt) :
    targetBody Cf₀ pl i (targetAt Cf₀ pl q) = ((i.val q.1 q.2 : ℤ) : F) := by
  have hex : ∃ q', targetAt Cf₀ pl q' = targetAt Cf₀ pl q := ⟨q, rfl⟩
  have hq : hex.choose = q := hinj hex.choose_spec
  have e : targetBody Cf₀ pl i (targetAt Cf₀ pl q) = ((i.val hex.choose.1 hex.choose.2 : ℤ) : F) :=
    dif_pos hex
  rw [e, hq]

theorem targetHeld_body (p : ℕ) [CharP F p] (hp : 256 ≤ p)
    (hinj : Function.Injective (targetAt Cf₀ pl)) (i : Idx) :
    targetHeld Cf₀ pl (targetBody Cf₀ pl i) = some i := by
  have hex : ∃ i' : Idx,
      ∀ q, targetBody Cf₀ pl i (targetAt Cf₀ pl q) = ((i'.val q.1 q.2 : ℤ) : F) :=
    ⟨i, targetBody_at Cf₀ pl hinj i⟩
  have e : targetHeld Cf₀ pl (targetBody Cf₀ pl i) = some hex.choose := dif_pos hex
  have hi : hex.choose = i := by
    apply Subtype.ext
    funext y c
    have h1 := hex.choose_spec (y, c)
    rw [targetBody_at Cf₀ pl hinj i (y, c)] at h1
    exact (byte_cast_inj p hp (idx_byte i (y, c)) (idx_byte hex.choose (y, c)) h1).symm
  rw [e, hi]

open Classical in
theorem targetPick_congr (P Q : Idx → Prop) (e : P = Q) :
    (if h : ∃ i, P i then some h.choose else none : Option Idx) =
      (if h : ∃ i, Q i then some h.choose else none) := by
  subst e
  rfl

theorem targetHeld_congr (a a' : Cf₀.Row × Cf₀.J₀ → F)
    (h : ∀ q, a (targetAt Cf₀ pl q) = a' (targetAt Cf₀ pl q)) :
    targetHeld Cf₀ pl a = targetHeld Cf₀ pl a' :=
  targetPick_congr (fun i : Idx => ∀ q, a (targetAt Cf₀ pl q) = ((i.val q.1 q.2 : ℤ) : F))
    (fun i : Idx => ∀ q, a' (targetAt Cf₀ pl q) = ((i.val q.1 q.2 : ℤ) : F))
    (funext fun _ => propext (forall_congr' fun q => by rw [h q]))

end

theorem targetHeld_reads {F E : Type} [Field F] [Field E] [Algebra F E] (Cf₀ : LdCf F E)
    (pl : TargetEnt → Cf₀.Row × Cf₀.Lay) (a a' : Cf₀.Row × Cf₀.J₀ → F)
    (hh : ∀ r l, a (r, Cf₀.lay l) = a' (r, Cf₀.lay l)) :
    targetHeld Cf₀ pl a = targetHeld Cf₀ pl a' :=
  targetHeld_congr Cf₀ pl a a' fun q => hh (pl q).1 (pl q).2

end Cm
