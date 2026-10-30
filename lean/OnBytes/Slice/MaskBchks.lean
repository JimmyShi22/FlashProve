-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/MaskBchks.lean: under the library's statement on Reed-Solomon codes as a hypothesis,
and nothing else assumed: the counts of exceptional points for a main row and for a repeated mask
row of a stage, at every radius other than 0 below the stage's Johnson radius.

OnBytes/Slice/BlocksJohnson.lean takes off the blocks of a proximity test below the Johnson radius
under a named hypothesis, `Sg.CountsAt`: two numbers bound the exceptional points of a line, one for
a main row, one for a mask row repeated to the main rows' length. OnBytes/Slice/CountsBchks.lean
leads the first back to the library's statement on codes (`Cb.BCHKS46At`, Cb/Gen/CodeListRSAt.lean;
proved in Cb/Bridge/, from files adapted from ArkLib and Mathlib (lean/LIMITS.md,
L15)),
and has the second only where 2 e is below the repeated mask code's own distance. This file has the
second at every radius below that code's Johnson radius. The repeated
mask code is a part of a Reed-Solomon code of the main rows' length and the mask code's rate
(`repCode_le`, OnBytes/Slice/NumbersHalf.lean, at points of its own numbering, which lie in GF). For
that larger code the statement on codes gives a count b. OnBytes/Slice/SubcodeList.lean passes from
a code to a part of it at the price of the list of pairs, with nothing assumed and at every radius
below the distance. The list of pairs is bounded by the Johnson bound, which is proved
(`pairNear_johnson`, from the library's `johnson_family`). So the mask row's count is b + L. That is
the form in which the planner books it (OnBytes/Params/Group.lean, `analysisAt`: the count and one
list size more). No theorem here ties the two. Under `Sg.AsGroup` (among its fields: the stage's
distance is that of its main rows) OnBytes/Slice/PricedRound.lean writes the count, rounded down, in
the planner's letters (`Sg.AsGroup.flZ`). Under `JohnsonGroup` OnBytes/Params/GroupPrices.lean
bounds a sum that holds it, divided by the field's size, by the planner's error of a fold's round
(up to the h-th) and of the last step's first round, where that error is not marked bad
(`fold_covers_floor`, `base_covers_floor`).

Main theorems.
 `pairNear_johnson`   the Johnson bound for pairs of words of a code. Nothing assumed.
 `agreeOn_rs_iff`     agreement with the library's `Code.rsCode` in the letters of `Cb.OnRS`.
 `mcaOn_rs_bchks`     under the statement on codes: the count for the larger Reed-Solomon code.
 `mca_bchks_rep`      under it: one repeated row has at most b + L exceptional points.
 `Sg.dZ_eq`           the repeated mask code's distance is the larger code's.
 `Sg.countsAt_bchks_all`   under it: `Sg.CountsAt` at every radius other than 0 below the stage's
                      Johnson radius.

Not claimed. This is no proof of soundness at the Johnson radius. `Cb.BCHKS46At` is a hypothesis of
every theorem here but `pairNear_johnson`, `agreeOn_rs_iff` and `Sg.dZ_eq`; no theorem of this file
has a proof of it laid in.
Cb/Bridge/ proves it from the files under ThirdParty/, which are adapted from ArkLib and Mathlib
(`bchks46At`, Cb/Bridge/CodeListRSProved.lean; lean/LIMITS.md, L15).
By the library's own comments it restates a theorem that a public preprint states with
an outline of a proof (IACR ePrint 2025/2055, Theorem 4.6, at M = 1); the two are not compared
here. It speaks of all lengths, degree bounds, radii and sets of points in GF: one false
instance would empty every theorem under it. `bchksBound` is a real number that is evaluated nowhere
here: no number is stated. That the counts here are the planner's is not shown (what is shown of the
two: the first paragraph's end), nor that the list in the mask row's count is at most `Sg.lstJ`. The
count pays the list also where the mask code has the main code's length. Both codes are asked to
have at least two coefficients. Nothing on the batching, a stored table, its link, a record, a proof
or a file.

-/
import Cb.Gen.JohnsonListProofs
import OnBytes.Slice.CountsBchks
import OnBytes.Slice.SubcodeList

set_option autoImplicit false

namespace OnBytes.Slice
open Cb Prob Polynomial
open Cb.CodeListRS

section
variable {E ι : Type} [Field E] [Fintype ι]

/-- The Johnson bound for pairs: below the Johnson radius for the number of positions and the
minimum distance d of the code D, a pair of words has at most `listMax` pairs of words of D near
it. -/
theorem pairNear_johnson [Finite E] {D : Submodule E (ι → E)} {d e : ℕ} (hd : Code.MinDist D d)
    (hj : InJohnson (Fintype.card ι) d e) (f₀ f₁ : ι → E) :
    cnt (PairNear D e f₀ f₁) ≤ listMax (Fintype.card ι) d e := by
  classical
  refine cnt_le_of_forall_finset fun Y hY => ?_
  have key := johnson_family {c : (ι → E) × (ι → E) // c.1 ∈ D ∧ c.2 ∈ D} ι (E × E)
    (fun c j => (c.1.1 j, c.1.2 j)) d e ?_ hj (fun j => (f₀ j, f₁ j))
    (Y.subtype fun c => c.1 ∈ D ∧ c.2 ∈ D) ?_
  · rw [Finset.card_subtype, Finset.filter_true_of_mem fun c hc => ⟨(hY c hc).1, (hY c hc).2.1⟩]
      at key
    exact key
  · intro i i' hne
    have hne' : i.1.1 ≠ i'.1.1 ∨ i.1.2 ≠ i'.1.2 := by
      by_contra hcon
      rw [not_or, not_not, not_not] at hcon
      exact hne (Subtype.ext (Prod.ext hcon.1 hcon.2))
    rcases hne' with h1 | h1
    · refine le_trans (hd _ (D.sub_mem i.2.1 i'.2.1) (sub_ne_zero.mpr h1))
        (cnt_mono fun j hj' hEq => hj' ?_)
      have hE : i.1.1 j = i'.1.1 j := congrArg Prod.fst hEq
      rw [Pi.sub_apply, hE, sub_self]
    · refine le_trans (hd _ (D.sub_mem i.2.2 i'.2.2) (sub_ne_zero.mpr h1))
        (cnt_mono fun j hj' hEq => hj' ?_)
      have hE : i.1.2 j = i'.1.2 j := congrArg Prod.snd hEq
      rw [Pi.sub_apply, hE, sub_self]
  · intro i hi
    obtain ⟨-, -, S, hS, h0, h1⟩ := hY i.1 (Finset.mem_subtype.1 hi)
    have h2 := cnt_add_card_le (P := fun j => (i.1.1 j, i.1.2 j) ≠ (f₀ j, f₁ j)) (S := S)
      fun j hj' hc => hc (by rw [h0 j hj', h1 j hj'])
    show cnt (fun j => (i.1.1 j, i.1.2 j) ≠ (f₀ j, f₁ j)) ≤ e
    omega

end

/-- On a set of positions a word agrees with a word of the Reed-Solomon code of degree at most K
exactly if it agrees there with a polynomial of degree at most K. -/
theorem agreeOn_rs_iff {n : ℕ} (D : Fin n ↪ GE) (K : ℕ) (u : Fin n → GE) (S : Finset (Fin n)) :
    u ∈ Code.agreeOn (Code.rsCode D K) S ↔ OnRS D K u S := by
  constructor
  · rintro ⟨w, ⟨p, hp, hw⟩, h⟩
    exact ⟨p, lt_of_le_of_lt (degree_le_of_natDegree_le hp)
      (WithBot.coe_lt_coe.2 (Nat.lt_succ_self K)), fun j hj => by rw [h j hj, hw j]⟩
  · rintro ⟨p, hp, h⟩
    refine ⟨fun x => p.eval (D x), ⟨p, ?_, fun _ => rfl⟩, h⟩
    by_cases h0 : p = 0
    · rw [h0, natDegree_zero]
      exact Nat.zero_le _
    · exact Nat.lt_succ_iff.1 ((natDegree_lt_iff_degree_lt h0).mpr hp)

/-- Under the statement on codes: the Reed-Solomon code of degree at most K > 0 at the points
`repPt`, at a radius e other than 0 with 2^a K < (2^a - e)^2, has at most b exceptional points on a
line, for every whole number b that is at least `bchksBound`. -/
theorem mcaOn_rs_bchks (hA : BCHKS46At GF GE) (Cd : Fmt.M1.Code) (a K : ℕ) (hle : Cd.a ≤ a)
    (ha : a ≤ 32) (hK : 0 < K) (e : ℕ) (he : 0 < e) (hj : 2 ^ a * K < (2 ^ a - e) ^ 2) (b : ℕ)
    (hb : bchksBound (2 ^ a) K e ≤ (b : ℝ)) :
    Code.MCAOn Unit (Code.rsCode ⟨repPt Cd a, repPt_inj Cd a hle ha⟩ K) e b := by
  intro f₀ f₁
  have hinj : Function.Injective fun x : Fin (2 ^ a) => unitPt a (turn Cd.a (a - Cd.a) x.val) :=
    fun x y hxy => repPt_inj Cd a hle ha (congrArg (algebraMap GF GE) hxy)
  have h := hA (2 ^ a) K e _ hinj hK he hj (f₀ ()) (f₁ ())
  refine le_trans (cnt_mono fun θ hθ => ?_) (Nat.cast_le.1 (h.trans hb))
  obtain ⟨S, hS, h1, hn⟩ := hθ
  rw [Fintype.card_fin] at hS
  exact ⟨S, hS, (agreeOn_rs_iff _ K _ S).1 (h1 ()), fun hc => hn
    ⟨fun _ => (agreeOn_rs_iff _ K _ S).2 hc.1, fun _ => (agreeOn_rs_iff _ K _ S).2 hc.2⟩⟩

/-- Under the statement on codes: one row under a code of length 2^b repeated to 2^a positions.
Write K for 2^(a - b) (r + l - 1), the degree bound of the Reed-Solomon code of length 2^a in which
the repeated code lies. At a radius e other than 0, below 2^a - K and with 2^a K < (2^a - e)^2, a
line has at most b + L exceptional points: b any whole number that is at least `bchksBound`, L the
Johnson bound on a list at the distance 2^a - K. -/
theorem mca_bchks_rep (hA : BCHKS46At GF GE) (Cd : Fmt.M1.Code) (a : ℕ) (hle : Cd.a ≤ a)
    (ha : a ≤ 32) (hk : 0 < Cd.r + Cd.l - 1) (e : ℕ) (he : 0 < e)
    (hd : e < 2 ^ a - 2 ^ (a - Cd.a) * (Cd.r + Cd.l - 1))
    (hj : 2 ^ a * (2 ^ (a - Cd.a) * (Cd.r + Cd.l - 1)) < (2 ^ a - e) ^ 2) (b : ℕ)
    (hb : bchksBound (2 ^ a) (2 ^ (a - Cd.a) * (Cd.r + Cd.l - 1)) e ≤ (b : ℝ)) :
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
    (mcaOn_rs_bchks hA Cd a _ hle ha (Nat.mul_pos (Nat.two_pow_pos _) hk) e he hj b hb)
    (pairNear_johnson hmd hJ)
  rw [Fintype.card_fin] at hsub
  intro f₀ f₁
  refine le_trans (cnt_mono fun θ hθ => ?_) (hsub (fun _ x => f₀ x ()) (fun _ x => f₁ x ()))
  obtain ⟨S, hS, h1, hno⟩ := hθ
  exact ⟨S, hS, fun _ => (onRep_iff Cd a hK _ S).1 h1, fun hc =>
    hno ⟨(onRep_iff Cd a hK _ S).2 (hc.1 ()), (onRep_iff Cd a hK _ S).2 (hc.2 ())⟩⟩

namespace Sg
variable {s : Sg}

/-- The number `Sg.dZ` is the number 2^a - K that `Code.minDist_rsCode` gives for the Reed-Solomon
code of the main rows' length in which the repeated mask code lies. -/
theorem dZ_eq (h : s.Sized) (hp : s.Pos) :
    s.dZ = 2 ^ s.C.a - 2 ^ (s.C.a - s.Z.a) * (s.Z.r + s.Z.l - 1) := by
  have hab : 2 ^ s.C.a = 2 ^ (s.C.a - s.Z.a) * 2 ^ s.Z.a := by
    rw [← pow_add]
    congr 1
    have := h.short
    omega
  have h1 := h.roomZ
  have h2 := hp.someZ
  have h3 : 2 ^ s.Z.a - (s.Z.r + s.Z.l) + 1 = 2 ^ s.Z.a - (s.Z.r + s.Z.l - 1) := by omega
  unfold Sg.dZ
  rw [h3, Nat.mul_sub, ← hab]

/-- **From the library's assumed statement alone to the named hypothesis**, at every radius e other
than 0 below the stage's Johnson radius, for a main and a mask code with at least two coefficients
each. bC and bZ: whole numbers that are at least `bchksBound` at the main code, and at the
Reed-Solomon code of the main rows' length in which the repeated mask code lies. The mask row's
count is bZ and the Johnson bound's list at that code's distance. -/
theorem countsAt_bchks_all (hA : BCHKS46At GF GE) (h : s.Sized) (hp : s.Pos)
    (hkC : 0 < s.C.r + s.C.l - 1) (hkZ : 0 < s.Z.r + s.Z.l - 1) {e : ℕ} (he : 0 < e)
    (hj : s.InJ e) (bC bZ : ℕ)
    (hbC : bchksBound (2 ^ s.C.a) (s.C.r + s.C.l - 1) e ≤ (bC : ℝ))
    (hbZ : bchksBound (2 ^ s.C.a) (2 ^ (s.C.a - s.Z.a) * (s.Z.r + s.Z.l - 1)) e ≤ (bZ : ℝ)) :
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
  · refine mca_bchks_self hA s.C h.small hkC e he ?_ bC hbC
    have h4 : s.C.r + s.C.l - 1 ≤ 2 ^ s.C.a - s.d := by
      unfold Sg.dC at hdC
      omega
    exact lt_of_le_of_lt (Nat.mul_le_mul_left _ h4) hj.2
  · rw [hZ]
    exact mca_bchks_rep hA s.Z s.C.a h.short h.small hkZ e he (by rw [← hZ]; omega)
      (lt_of_le_of_lt (Nat.mul_le_mul_left _ hle) hj.2) bZ hbZ

end Sg

end OnBytes.Slice
