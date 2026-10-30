-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/Port8.lean: the two forms of the kind's bad seeds meet: with each list taken as
the tables of the messages in the library's list of the word sent, a bad seed of the form with lists
as letters is a bad seed in the library's terms; and tables of two messages that are one vector of
the sample map are tables of one message.

Main names: listOf; vec_ext, tabOf_inj; bad_port.

What is not claimed. One answer a message. Nothing on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.Port7

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open OnBytes.Slice Johnson.Pack Cb Cb.Ood Prob

/-- The lists as tables: the tables of the messages in the library's list of the word sent. A number
that is no message's of the place has the empty list. -/
def listOf (P : Par) (rad : Nat → Nat)
    (f : ∀ k, (portOmZ P.codes (shapeAt P k) (rad k.val)).Str) (n : Nat)
    (u : Part → Nat → GE) : Prop :=
  ∃ (h : n < (shapesOf P).length) (msg : (portCode P.codes (shapeAt P ⟨n, h⟩)).J → GE),
    (portOmZ P.codes (shapeAt P ⟨n, h⟩) (rad n)).InList (f ⟨n, h⟩) msg ∧
      u = tabOf P.codes (shapeAt P ⟨n, h⟩) msg

/-- Tables that are one vector of the sample map agree on every entry of both tables. -/
theorem vec_ext (m : Msg) (u u' : Part → Nat → GE) (h : m.vec u = m.vec u') (part : Part)
    (j : Nat) (hp : m.has part = true) (hj : j < 2 ^ m.bits part) : u part j = u' part j := by
  cases hpad : m.isPad part j
  · cases part
    · exact congrFun h (Sum.inl (Sum.inl ⟨j, (m.mem_proper _ _).2 ⟨hp, hj, hpad⟩⟩))
    · exact congrFun h (Sum.inl (Sum.inr ⟨j, (m.mem_proper _ _).2 ⟨hp, hj, hpad⟩⟩))
  · obtain ⟨rfl, k, t, hk, ht, rfl⟩ := (m.isPad_iff _ _).1 hpad
    exact congrFun h (Sum.inr (⟨k, hk⟩, ⟨t, ht⟩))

/-- **Two messages whose tables are one vector of the sample map are one message.** -/
theorem tabOf_inj (cs : Codes) (s : OracleShape) (msg msg' : (portCode cs s).J → GE)
    (h : (Msg.of cs s).vec (tabOf cs s msg) = (Msg.of cs s).vec (tabOf cs s msg')) :
    msg = msg' := by
  funext j
  rcases j with x | x
  · have h0 : 0 < s.mainRows := by have := x.1.isLt; omega
    have h0' : s.mainRows ≠ 0 := Nat.pos_iff_ne_zero.1 h0
    have e := vec_ext _ _ _ h .main (x.1.val + 2 ^ k1 s * x.2.val)
      (by simp [Msg.has, Msg.of, h0']) (by rw [bits_main cs s h0]; exact main_lt cs s x)
    have a := tabAt_loc (k1 s) (le_two_pow_ceilLog2 _)
      (fun y : Fin s.mainRows × Fin (pMain cs s).ell => msg (Sum.inl y)) x
    have b := tabAt_loc (k1 s) (le_two_pow_ceilLog2 _)
      (fun y : Fin s.mainRows × Fin (pMain cs s).ell => msg' (Sum.inl y)) x
    exact a.symm.trans (e.trans b)
  · have h0 : 0 < s.maskRows := by have := x.1.isLt; omega
    have h0' : s.maskRows ≠ 0 := Nat.pos_iff_ne_zero.1 h0
    have e := vec_ext _ _ _ h .mask (x.1.val + 2 ^ k2 s * x.2.val)
      (by simp [Msg.has, Msg.of, h0']) (by rw [bits_mask cs s h0]; exact mask_lt cs s x)
    have a := tabAt_loc (k2 s) (le_two_pow_ceilLog2 _)
      (fun y : Fin s.maskRows × Fin (pMask cs s).ell => msg (Sum.inr y)) x
    have b := tabAt_loc (k2 s) (le_two_pow_ceilLog2 _)
      (fun y : Fin s.maskRows × Fin (pMask cs s).ell => msg' (Sum.inr y)) x
    exact a.symm.trans (e.trans b)

/-- **A bad seed of the form with lists as letters, at the library's lists, is a bad seed in the
library's terms.** -/
theorem bad_port (P : Par) (rad : Nat → Nat) (hC : condPort P rad = true)
    (f : ∀ k, (portOmZ P.codes (shapeAt P k) (rad k.val)).Str) (ρ : Seeds P)
    (h : Bad P (listOf P rad f) ρ) : BadPort P rad f ρ := by
  obtain ⟨k, hk, x, x', ⟨u, ⟨hn, msg, hl, rfl⟩, rfl⟩, ⟨u', ⟨_, msg', hl', rfl⟩, rfl⟩, hne, hv⟩ := h
  refine ⟨k, hk, msg, msg', hl, hl', fun e => hne (by rw [e]), funext fun _ => ?_⟩
  have hT := cond_tie P rad hC k hk
  have h1 : 0 < P.seeds := one_le_seeds P k hk
  have ha : 0 < (msgAt P k).answers := Nat.pos_of_ne_zero hk
  have hb := bits_le_coordinates P k hk
  have key : ∀ mm : (portCode P.codes (shapeAt P k)).J → GE,
      (portZ P.codes (shapeAt P k)).val (seedAt P (bitsZ P.codes (shapeAt P k)) ρ) mm () =
        (msgAt P k).Z.val (ownSeeds (msgAt P k).answers (msgAt P k).v ρ)
          ((msgAt P k).vec (tabOf P.codes (shapeAt P k) mm)) ⟨0, ha⟩ := by
    intro mm
    rw [port_val hT, (msgAt P k).val_eq hT.some hT.fits]
    have e1 : seedAt P (bitsZ P.codes (shapeAt P k)) ρ =
        (fun t => pointOf (ρ ⟨0, h1⟩).1 t.val, (ρ ⟨0, h1⟩).2) := by
      unfold seedAt ownSeeds
      exact dif_pos h1
    have e2 : ownSeeds (msgAt P k).answers (msgAt P k).v ρ ⟨0, ha⟩ =
        (fun t => pointOf (ρ ⟨0, h1⟩).1 t.val, (ρ ⟨0, h1⟩).2) := by
      unfold ownSeeds
      exact dif_pos h1
    rw [e1, e2]
    refine (Msg.of P.codes (shapeAt P k)).form_congr _ _ (fun t ht => ?_) _ _ _
    have ht2 : t < bitsZ P.codes (shapeAt P k) := by rw [← v_bitsZ]; exact ht
    have ht3 : t < (msgAt P k).v := ht
    simp only [pointOf, dif_pos ht2, dif_pos ht3]
  exact (key msg).trans ((congrFun hv ⟨0, ha⟩).trans (key msg').symm)

end VerifiableInference.Desc.K1
