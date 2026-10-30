-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/Catches2.lean: a message's sample map: the library's rows with pads at the
message's own numbers, with the library's property.

Main names: Msg.v_both, v_single, vertex_lt, vertex_inj; proper, J₀, idx, idx_lt, idx_inj; Msg.Z;
Z_okOn_F (pads of three entries: on the vectors whose pads lie in the base field), Z_okOn_E (pads of
one entry: on all vectors).
Nothing on a sample is proved anew: the property is the library's ood_okOn_padPow
(Cb/Gen/OodDecPadPowProofs.lean), with theta_indep (OnBytes/Slice/RecordOK.lean).

What is not claimed. The entries proper count the rows of a table beyond the real ones. Nothing on a
protocol, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.Catches

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open OnBytes.Slice Cb Cb.Ood Prob

/-! ## The vertices are different -/

theorem Msg.v_both (m : Msg) (hb : (m.K != 0 && m.Kzk != 0) = true) :
    m.v = max m.mainBits m.maskBits + 1 := by
  unfold Msg.v
  rw [if_pos hb]

theorem Msg.v_single (m : Msg) (hb : (m.K != 0 && m.Kzk != 0) = false) (part : Part)
    (hp : m.has part = true) : m.v = m.bits part := by
  unfold Msg.v
  rw [hb, if_neg Bool.false_ne_true]
  cases part
  · have hK : (m.K != 0) = true := hp
    rw [hK, Bool.true_and] at hb
    have : m.Kzk = 0 := by simpa using hb
    simp [Msg.bits, Msg.maskBits, this]
  · have hZ : (m.Kzk != 0) = true := hp
    rw [hZ, Bool.and_true] at hb
    have : m.K = 0 := by simpa using hb
    simp [Msg.bits, Msg.mainBits, this]

theorem Msg.vertex_lt (m : Msg) (part : Part) (j : Nat) (hp : m.has part = true)
    (hj : j < 2 ^ m.bits part) : m.vertex part j < 2 ^ m.v := by
  unfold Msg.vertex
  cases hb : (m.K != 0 && m.Kzk != 0)
  · rw [m.v_single hb part hp]
    simpa using hj
  · have hv := m.v_both hb
    have hle : 2 ^ m.bits part ≤ 2 ^ (m.v - 1) := by
      refine Nat.pow_le_pow_right (by decide) ?_
      rw [hv]
      cases part
      · exact Nat.le_max_left _ _
      · exact Nat.le_max_right _ _
    have h2 : 2 ^ m.v = 2 * 2 ^ (m.v - 1) := by
      rw [hv, Nat.add_sub_cancel, Nat.pow_succ, Nat.mul_comm]
    cases part <;> simp <;> omega

theorem Msg.vertex_inj (m : Msg) (part part' : Part) (j j' : Nat) (hp : m.has part = true)
    (hp' : m.has part' = true) (hj : j < 2 ^ m.bits part) (hj' : j' < 2 ^ m.bits part')
    (h : m.vertex part j = m.vertex part' j') : part = part' ∧ j = j' := by
  unfold Msg.vertex at h
  cases hb : (m.K != 0 && m.Kzk != 0)
  · rw [hb] at h
    have hjj : j = j' := by simpa using h
    refine ⟨?_, hjj⟩
    cases part <;> cases part' <;> first | rfl | skip
    · have h1 : (m.K != 0) = true := hp
      have h2 : (m.Kzk != 0) = true := hp'
      rw [h1, h2] at hb
      cases hb
    · have h1 : (m.K != 0) = true := hp'
      have h2 : (m.Kzk != 0) = true := hp
      rw [h1, h2] at hb
      cases hb
  · rw [hb] at h
    have hv := m.v_both hb
    have hle : ∀ p : Part, 2 ^ m.bits p ≤ 2 ^ (m.v - 1) := fun p => by
      refine Nat.pow_le_pow_right (by decide) ?_
      rw [hv]
      cases p
      · exact Nat.le_max_left _ _
      · exact Nat.le_max_right _ _
    have l1 := hle part
    have l2 := hle part'
    cases part <;> cases part' <;> simp at h <;> first | exact ⟨rfl, h⟩ | omega

/-! ## The sample map -/

/-- The entries proper of a table: those that are no pad's. -/
def Msg.proper (m : Msg) (part : Part) : Finset Nat :=
  (Finset.range (m.size part)).filter fun j => m.isPad part j = false

theorem Msg.mem_proper (m : Msg) (part : Part) (j : Nat) :
    j ∈ m.proper part ↔ m.has part = true ∧ j < 2 ^ m.bits part ∧ m.isPad part j = false := by
  unfold Msg.proper Msg.size
  by_cases hp : m.has part = true <;> simp [hp]

/-- The entries proper of both tables. -/
abbrev Msg.J₀ (m : Msg) : Type := {j // j ∈ m.proper .main} ⊕ {j // j ∈ m.proper .mask}

/-- The vertex of an entry proper. -/
def Msg.idx (m : Msg) : m.J₀ → Nat :=
  Sum.elim (fun j => m.vertex .main j.1) fun j => m.vertex .mask j.1

theorem Msg.idx_lt (m : Msg) (q : m.J₀) : m.idx q < 2 ^ m.v := by
  rcases q with j | j
  · have h := (m.mem_proper _ _).1 j.2
    exact m.vertex_lt .main j.1 h.1 h.2.1
  · have h := (m.mem_proper _ _).1 j.2
    exact m.vertex_lt .mask j.1 h.1 h.2.1

theorem Msg.idx_inj (m : Msg) : Function.Injective m.idx := by
  intro q q' h
  rcases q with j | j <;> rcases q' with j' | j'
  · have a := (m.mem_proper _ _).1 j.2
    have b := (m.mem_proper _ _).1 j'.2
    exact congrArg Sum.inl (Subtype.ext (m.vertex_inj _ _ _ _ a.1 b.1 a.2.1 b.2.1 h).2)
  · have a := (m.mem_proper _ _).1 j.2
    have b := (m.mem_proper _ _).1 j'.2
    exact nomatch (m.vertex_inj _ _ _ _ a.1 b.1 a.2.1 b.2.1 h).1
  · have a := (m.mem_proper _ _).1 j.2
    have b := (m.mem_proper _ _).1 j'.2
    exact nomatch (m.vertex_inj _ _ _ _ a.1 b.1 a.2.1 b.2.1 h).1
  · have a := (m.mem_proper _ _).1 j.2
    have b := (m.mem_proper _ _).1 j'.2
    exact congrArg Sum.inr (Subtype.ext (m.vertex_inj _ _ _ _ a.1 b.1 a.2.1 b.2.1 h).2)

/-- **The message's sample map**: the library's rows with pads, at the message's own numbers. -/
@[reducible] noncomputable def Msg.Z (m : Msg) : Sample GE (m.J₀ ⊕ Fin m.answers × Fin m.e) :=
  Sample.padPow GE (Fin m.v) m.J₀ (Fin m.e) GEˣ (fun q t => (m.idx q).testBit t.val)
    (fun t => readE (thetaE t.val)) Units.val m.answers

theorem Msg.pl_inj (m : Msg) :
    Function.Injective fun (q : m.J₀) (t : Fin m.v) => (m.idx q).testBit t.val :=
  fun q q' h => m.idx_inj (testBit_inj m.v (m.idx_lt q) (m.idx_lt q') fun t => congrFun h t)

theorem theta_indep3 (e : Nat) (h : e = 3) :
    Function.Injective (padVal (F := GF) fun t : Fin e => readE (thetaE t.val)) := by
  subst h
  exact theta_indep

theorem theta_indep1 (e : Nat) (h : e = 1) :
    Function.Injective (padVal (F := GE) fun t : Fin e => readE (thetaE t.val)) := by
  subst h
  intro c c' hc
  funext t
  have ht : t = 0 := Subsingleton.elim _ _
  subst ht
  simpa [padVal, readE_theta_zero] using hc

/-- Pads of three entries: the property on the vectors whose pads' entries lie in the base field. -/
theorem Msg.Z_okOn_F (m : Msg) (h : m.e = 3) : m.Z.OKOn (PadInF GF) :=
  ood_okOn_padPow GF GE (Fin m.v) m.J₀ (Fin m.e) GEˣ _ _ Units.val m.answers m.pl_inj
    (fun _ _ h => Units.ext h) (fun β => β.ne_zero) (theta_indep3 m.e h)

/-- Pads of one entry: the property on all vectors. -/
theorem Msg.Z_okOn_E (m : Msg) (h : m.e = 1) : m.Z.OKOn (PadInF GE) :=
  ood_okOn_padPow GE GE (Fin m.v) m.J₀ (Fin m.e) GEˣ _ _ Units.val m.answers m.pl_inj
    (fun _ _ h => Units.ext h) (fun β => β.ne_zero) (theta_indep1 m.e h)

end VerifiableInference.Desc.K1
