-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/CountsFloor.lean: UNDER THE THEOREM ON CODES, TAKEN AS GIVEN (`Cb.BCHKS46At`: a
hypothesis of the theorems here, which this file does not prove): the counts of exceptional points
of a line at THE INTEGER PART of the bound.

OnBytes/Slice/CountsBchks.lean and OnBytes/Slice/MaskBchks.lean get the named hypothesis
`Sg.CountsAt` from that hypothesis, at every whole number that is at least the real number
`bchksBound`. A count is a whole number, so it is at most the bound's integer part. This file says
the four theorems again for every whole number that is at least that integer part, which asks less.
So a price that covers `bchksBound` itself covers the count. The text is that of `mca_bchks_self`,
`mcaOn_rs_bchks`, `mca_bchks_rep` and `Sg.countsAt_bchks_all`, with `Nat.le_floor` where those
compare two real numbers.

Main theorems: `mca_bchks_self_fl`, `mcaOn_rs_bchks_fl`, `mca_bchks_rep_fl`, `Sg.countsAt_bchks_fl`,
`Sg.countsAt_floor`.

Not claimed. THIS IS NO PROOF OF SOUNDNESS AT THE JOHNSON RADIUS. All that the two files' heads do
not claim. `bchksBound` is evaluated nowhere here: no number is stated.

-/
import OnBytes.Slice.MaskBchks

set_option autoImplicit false

namespace OnBytes.Slice
open Cb Prob Polynomial
open Cb.CodeListRS

/-- `mca_bchks_self` for every whole number b that is at least the integer part of `bchksBound`. -/
theorem mca_bchks_self_fl (hA : BCHKS46At GF GE) (Cd : Fmt.M1.Code) (ha : Cd.a ≤ 32)
    (hk : 0 < Cd.r + Cd.l - 1) (e : ℕ) (he : 0 < e)
    (hj : 2 ^ Cd.a * (Cd.r + Cd.l - 1) < (2 ^ Cd.a - e) ^ 2) (b : ℕ)
    (hb : ⌊bchksBound (2 ^ Cd.a) (Cd.r + Cd.l - 1) e⌋₊ ≤ b) : (ldOf Cd Cd.a).MCAat e b := by
  intro f₀ f₁
  have hK : 0 < Cd.r + Cd.l := by omega
  have h := hA (2 ^ Cd.a) (Cd.r + Cd.l - 1) e (ptOf Cd.a) (ptOf_inj Cd.a ha) hk he hj
    (fun x => (ldOf Cd Cd.a).T f₀ x ()) (fun x => (ldOf Cd Cd.a).T f₁ x ())
  refine le_trans (cnt_mono fun θ hθ => ?_) ((Nat.le_floor h).trans hb)
  obtain ⟨S, hS, h1, hn⟩ := hθ
  rw [Fintype.card_fin] at hS
  exact ⟨S, hS, (onCode_iff_onRS Cd hK _ S).1 h1, fun hc =>
    hn ⟨(onCode_iff_onRS Cd hK _ S).2 hc.1, (onCode_iff_onRS Cd hK _ S).2 hc.2⟩⟩

/-- `mcaOn_rs_bchks` for every whole number b that is at least the integer part of `bchksBound`. -/
theorem mcaOn_rs_bchks_fl (hA : BCHKS46At GF GE) (Cd : Fmt.M1.Code) (a K : ℕ) (hle : Cd.a ≤ a)
    (ha : a ≤ 32) (hK : 0 < K) (e : ℕ) (he : 0 < e) (hj : 2 ^ a * K < (2 ^ a - e) ^ 2) (b : ℕ)
    (hb : ⌊bchksBound (2 ^ a) K e⌋₊ ≤ b) :
    Code.MCAOn Unit (Code.rsCode ⟨repPt Cd a, repPt_inj Cd a hle ha⟩ K) e b := by
  intro f₀ f₁
  have hinj : Function.Injective fun x : Fin (2 ^ a) => unitPt a (turn Cd.a (a - Cd.a) x.val) :=
    fun x y hxy => repPt_inj Cd a hle ha (congrArg (algebraMap GF GE) hxy)
  have h := hA (2 ^ a) K e _ hinj hK he hj (f₀ ()) (f₁ ())
  refine le_trans (cnt_mono fun θ hθ => ?_) ((Nat.le_floor h).trans hb)
  obtain ⟨S, hS, h1, hn⟩ := hθ
  rw [Fintype.card_fin] at hS
  exact ⟨S, hS, (agreeOn_rs_iff _ K _ S).1 (h1 ()), fun hc => hn
    ⟨fun _ => (agreeOn_rs_iff _ K _ S).2 hc.1, fun _ => (agreeOn_rs_iff _ K _ S).2 hc.2⟩⟩

/-- `mca_bchks_rep` for every whole number b that is at least the integer part of `bchksBound`. -/
theorem mca_bchks_rep_fl (hA : BCHKS46At GF GE) (Cd : Fmt.M1.Code) (a : ℕ) (hle : Cd.a ≤ a)
    (ha : a ≤ 32) (hk : 0 < Cd.r + Cd.l - 1) (e : ℕ) (he : 0 < e)
    (hd : e < 2 ^ a - 2 ^ (a - Cd.a) * (Cd.r + Cd.l - 1))
    (hj : 2 ^ a * (2 ^ (a - Cd.a) * (Cd.r + Cd.l - 1)) < (2 ^ a - e) ^ 2) (b : ℕ)
    (hb : ⌊bchksBound (2 ^ a) (2 ^ (a - Cd.a) * (Cd.r + Cd.l - 1)) e⌋₊ ≤ b) :
    (ldRep Cd a).MCAat e
      (b + listMax (2 ^ a) (2 ^ a - 2 ^ (a - Cd.a) * (Cd.r + Cd.l - 1)) e) := by
  have hK : 0 < Cd.r + Cd.l := by omega
  have hmd := Code.minDist_rsCode (L := GE) ⟨repPt Cd a, repPt_inj Cd a hle ha⟩
    (2 ^ (a - Cd.a) * (Cd.r + Cd.l - 1))
  have hJ : InJohnson (Fintype.card (Fin (2 ^ a)))
      (Fintype.card (Fin (2 ^ a)) - 2 ^ (a - Cd.a) * (Cd.r + Cd.l - 1)) e := by
    rw [Fintype.card_fin]
    unfold InJohnson
    have h1 : 2 ^ a - (2 ^ a - 2 ^ (a - Cd.a) * (Cd.r + Cd.l - 1)) =
        2 ^ (a - Cd.a) * (Cd.r + Cd.l - 1) := by omega
    rw [h1]
    exact hj
  have hsub := mcaOn_subcode_list hmd (by rw [Fintype.card_fin]; exact hd)
    (repCode_le Cd a (Cd.r + Cd.l - 1) hle ha)
    (mcaOn_rs_bchks_fl hA Cd a _ hle ha (Nat.mul_pos (Nat.two_pow_pos _) hk) e he hj b hb)
    (pairNear_johnson hmd hJ)
  rw [Fintype.card_fin] at hsub
  intro f₀ f₁
  refine le_trans (cnt_mono fun θ hθ => ?_) (hsub (fun _ x => f₀ x ()) (fun _ x => f₁ x ()))
  obtain ⟨S, hS, h1, hno⟩ := hθ
  exact ⟨S, hS, fun _ => (onRep_iff Cd a hK _ S).1 h1, fun hc =>
    hno ⟨(onRep_iff Cd a hK _ S).2 (hc.1 ()), (onRep_iff Cd a hK _ S).2 (hc.2 ())⟩⟩

namespace Sg
variable {s : Sg}

/-- `Sg.countsAt_bchks_all` for whole numbers bC, bZ that are at least the integer parts of the two
values of `bchksBound`. -/
theorem countsAt_bchks_fl (hA : BCHKS46At GF GE) (h : s.Sized) (hp : s.Pos)
    (hkC : 0 < s.C.r + s.C.l - 1) (hkZ : 0 < s.Z.r + s.Z.l - 1) {e : ℕ} (he : 0 < e)
    (hj : s.InJ e) (bC bZ : ℕ)
    (hbC : ⌊bchksBound (2 ^ s.C.a) (s.C.r + s.C.l - 1) e⌋₊ ≤ bC)
    (hbZ : ⌊bchksBound (2 ^ s.C.a) (2 ^ (s.C.a - s.Z.a) * (s.Z.r + s.Z.l - 1)) e⌋₊ ≤ bZ) :
    s.CountsAt e bC (bZ + listMax (2 ^ s.C.a) s.dZ e) := by
  have hdC : s.d ≤ s.dC := min_le_left _ _
  have hdZ : s.d ≤ s.dZ := min_le_right _ _
  have hZ := dZ_eq h hp
  have h3 := h.roomC
  have h5 : e < s.d := hj.1
  have hle : 2 ^ (s.C.a - s.Z.a) * (s.Z.r + s.Z.l - 1) ≤ 2 ^ s.C.a - s.d := by
    generalize 2 ^ (s.C.a - s.Z.a) * (s.Z.r + s.Z.l - 1) = K at hZ ⊢
    generalize 2 ^ s.C.a = N at hZ ⊢
    omega
  constructor
  · refine mca_bchks_self_fl hA s.C h.small hkC e he ?_ bC hbC
    have h4 : s.C.r + s.C.l - 1 ≤ 2 ^ s.C.a - s.d := by
      unfold Sg.dC at hdC
      omega
    exact lt_of_le_of_lt (Nat.mul_le_mul_left _ h4) hj.2
  · rw [hZ]
    exact mca_bchks_rep_fl hA s.Z s.C.a h.short h.small hkZ e he (by rw [← hZ]; omega)
      (lt_of_le_of_lt (Nat.mul_le_mul_left _ hle) hj.2) bZ hbZ

/-- At the integer parts themselves. -/
theorem countsAt_floor (hA : BCHKS46At GF GE) (h : s.Sized) (hp : s.Pos)
    (hkC : 0 < s.C.r + s.C.l - 1) (hkZ : 0 < s.Z.r + s.Z.l - 1) {e : ℕ} (he : 0 < e)
    (hj : s.InJ e) :
    s.CountsAt e ⌊bchksBound (2 ^ s.C.a) (s.C.r + s.C.l - 1) e⌋₊
      (⌊bchksBound (2 ^ s.C.a) (2 ^ (s.C.a - s.Z.a) * (s.Z.r + s.Z.l - 1)) e⌋₊ +
        listMax (2 ^ s.C.a) s.dZ e) :=
  countsAt_bchks_fl hA h hp hkC hkZ he hj _ _ (Nat.le_refl _) (Nat.le_refl _)

end Sg

end OnBytes.Slice
