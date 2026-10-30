-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/SimFold.lean: what the written verifier of a fold computes, in the field.

Fmt/M1Fold.lean holds the verifier's side of a fold as functions on triples of words. A fold is a
sumcheck in k variables with one hiding polynomial: each round sends two of the three coefficients
of a polynomial of degree 2, the verifier gets the third from the running claim, and at the end it
hands on a claim on three folded rows. This file reads each result in the field `GE` and gives it
in the terms of the library's fold (Cb/Ld/LdSum.lean), of its hiding polynomial
(Cb/Ld/LdHide.lean, Cb/Ld/LdHideShort.lean) and of its packing (Cb/Ld/LdSumPack.lean).
Inputs are read by `vec`, `lst` and `ptL` (OnBytes/Slice/SimBasic.lean, OnBytes/Slice/Stage.lean).

Main definitions.
 `fixOne k`       in each of k rounds the coefficient of X is the one that is not sent.
 `shortOf k q`    the messages of k rounds; round j sends the pair q j: the constant and the
                  coefficient of X^2.
 `ptK k z`        the first k members of a sequence, as a point of the sumcheck.
 `hidePlace h n`  the place, in the format's vector of weights, of each column of the library's
                  packing of the hiding polynomial into 2^h rows, for h + n variables of degree 2.
Main theorems.
 `toE_midCoeff`, `toE_nextClaim`   one round, written out.
 `toE_nextClaim_hev`   the new claim is the completed round polynomial at the drawn element.
 `toE_claimOf`    the claim after k rounds is the value with which the library's verifier ends, at
                  the completion of the short messages.
 `toE_tailProd`, `toE_tailProd_late`   the product of the later elements.
 `vec_hideVec`    the format's vector of weights is the library's `QwC`, each column at its place,
                  and 0 elsewhere. `hidePlace_inj`, `hidePlace_lt`, `hidePlace_surj`: the places are
                  different and fill the numbers below h + 2 n + 1.
 `vec_foldStep_c`, `vec_foldStep_d0`, `vec_foldStep_d1`, `toE_foldStep_t`   what a fold hands on:
                  the main form fixed at the point, times eps; the mask form fixed at the first h
                  coordinates, times eps and the later coordinates; the weights; the end value for
                  the first claim sigma + target * eps.
 `length_foldStep_g`, `lst_foldStep_g`, `ptL_foldStep_g`   the point that is handed on: the first k
                  drawn elements, a missing one counting as 0.
 `size_foldStep_c`, `size_foldStep_d0_eq`, `size_foldStep_d0`, `size_foldStep_d1`   the lengths.

Not claimed. Nothing on a protocol, and nothing on soundness. The statements on the masks have the
number of variables written as h + n, so they say nothing for h above k. `vec_hideVec` asks for a
list of exactly h + n elements, because the format's product runs to the list's end; a fold always
passes such a list. Nothing on the other field of the format.
-/
import Cb.Ld.LdHideShort
import Cb.Ld.LdHideProofs
import Cb.Ld.LdSumPackProofs
import OnBytes.Slice.SimBasic

set_option autoImplicit false

namespace OnBytes.Slice
open Fmt.M1 Cb

/-! ## The running claim -/

/-- The coefficient of X that the verifier gets back from the running claim. -/
theorem toE_midCoeff (claim : E) (q : E × E) :
    toE (midCoeff .two claim q) = toE claim - (toE q.1 + toE q.1) - toE q.2 := by
  unfold midCoeff
  rw [toE_subE, toE_subE, toE_addE]

/-- The running claim after one round, written out. -/
theorem toE_nextClaim (claim : E) (q : E × E) (g : E) :
    toE (nextClaim .two claim q g) =
      toE q.1 + ((toE claim - (toE q.1 + toE q.1) - toE q.2) * toE g
        + toE q.2 * (toE g * toE g)) := by
  unfold nextClaim
  rw [toE_addE, toE_addE, toE_mulE, toE_mulE, toE_mulE, toE_midCoeff]

/-- In every round the coefficient of X is left out; the sum of X over 0 and 1 is 1. -/
def fixOne : (k : ℕ) → HFixs (sVars GE 2 k)
  | 0 => ()
  | k + 1 => (((1 : Fin 3), (1 : GE)), fixOne k)

/-- The sum of X over 0 and 1 is 1. -/
theorem mon_one : (HVar.plain GE 2).mon (1 : Fin 3) = 1 := by
  show ∑ s : Bool, (1 : GE) * (if s then (1 : GE) else 0) ^ (1 : ℕ) = 1
  rw [Fintype.sum_bool]
  simp

/-- The choice of the power that is left out is one that the library admits. -/
theorem fixOne_ok : ∀ k : ℕ, HFixs.OK (sVars GE 2 k) (fixOne k)
  | 0 => trivial
  | k + 1 => ⟨(one_mul _).trans mon_one, fixOne_ok k⟩

/-- The short messages of k rounds: round j sends the constant (q j).1 and the coefficient (q j).2
of X^2. -/
def shortOf : (k : ℕ) → (ℕ → GE × GE) → SIdx (sVars GE 2 k) → GE
  | 0, _, i => i.elim
  | _ + 1, q, .inl t => if t.val = 0 then (q 0).1 else (q 0).2
  | k + 1, q, .inr i => shortOf k (fun j => q (j + 1)) i

/-- The first k members of a sequence, as a point of the sumcheck. -/
def ptK (k : ℕ) (z : ℕ → GE) : HPt (sVars GE 2 k) := sUn 2 k fun t : Fin k => z t.val

/-- The pair number j of a list of pairs, read in the field; (0, 0) beyond the end. -/
def lst2 (qs : List (E × E)) (j : ℕ) : GE × GE :=
  (toE (qs.getD j (Fmt.Fld.zeroE, Fmt.Fld.zeroE)).1,
    toE (qs.getD j (Fmt.Fld.zeroE, Fmt.Fld.zeroE)).2)

/-- A polynomial of degree 2 without its coefficient of X. -/
theorem hev_gap (a b y : GE) :
    hev (n := 2) ((1 : Fin 3).insertNth (α := fun _ => GE) 0
      (fun t : Fin 2 => if t.val = 0 then a else b)) y = a + y ^ 2 * b := by
  unfold hev
  rw [Fin.sum_univ_three]
  show y ^ 0 • a + y ^ 1 • (0 : GE) + y ^ 2 • b = a + y ^ 2 * b
  rw [pow_zero, one_smul, smul_zero, add_zero, smul_eq_mul]

/-- The round polynomial that the round equation completes, at a point. -/
theorem hev_fill (σ a b x : GE) :
    hev (hFill (HVar.plain GE 2) ((1 : Fin 3), (1 : GE)) σ
      (fun t : Fin 2 => if t.val = 0 then a else b)) x =
      a + ((σ - (a + a) - b) * x + b * (x * x)) := by
  show hev (n := 2) ((1 : Fin 3).insertNth (α := fun _ => GE)
    ((1 : GE) • (σ - (HVar.plain GE 2).phi ((1 : Fin 3).insertNth (α := fun _ => GE) 0
      (fun t : Fin 2 => if t.val = 0 then a else b))))
    (fun t : Fin 2 => if t.val = 0 then a else b)) x = _
  rw [hev_split, plain_phi GE GE 2, hev_gap, hev_gap, hev_gap]
  show a + x ^ 2 * b + x ^ 1 • ((1 : GE) • (σ - (a + 0 ^ 2 * b + (a + 1 ^ 2 * b)))) = _
  rw [one_smul, smul_eq_mul]
  ring

/-- One round. The new claim is the completed round polynomial at the drawn element. -/
theorem toE_nextClaim_hev (claim : E) (q : E × E) (g : E) :
    toE (nextClaim .two claim q g) =
      hev (hFill (HVar.plain GE 2) ((1 : Fin 3), (1 : GE)) (toE claim)
        (fun t : Fin 2 => if t.val = 0 then toE q.1 else toE q.2)) (toE g) := by
  rw [toE_nextClaim, hev_fill]

/-- The running claim after k rounds, with the rounds' pairs and elements as sequences. -/
def claimFn (k : ℕ) (first : E) (q : ℕ → E × E) (z : ℕ → E) : E :=
  (List.range k).foldl (fun cl j => nextClaim .two cl (q j) (z j)) first

/-- One round more: the first round is taken, then k rounds on the shifted sequences. -/
theorem claimFn_succ (k : ℕ) (first : E) (q : ℕ → E × E) (z : ℕ → E) :
    claimFn (k + 1) first q z =
      claimFn k (nextClaim .two first (q 0) (z 0)) (fun j => q (j + 1)) (fun j => z (j + 1)) := by
  unfold claimFn
  rw [List.range_succ_eq_map, List.foldl_cons, List.foldl_map]

/-- `toE_claimOf` with the rounds' pairs and elements as sequences. -/
theorem toE_claimFn : ∀ (k : ℕ) (first : E) (q : ℕ → E × E) (z : ℕ → E),
    toE (claimFn k first q z) =
      hFin (sVars GE 2 k) (toE first)
        (hComp (sVars GE 2 k) (fixOne k) (toE first)
          (shortOf k fun j => (toE (q j).1, toE (q j).2)) (ptK k fun t => toE (z t)))
        (ptK k fun t => toE (z t))
  | 0, _, _, _ => rfl
  | k + 1, first, q, z => by
    rw [claimFn_succ, toE_claimFn k, toE_nextClaim_hev]
    rfl

/-- The claim after k rounds is the value with which the library's verifier ends, at the long
messages that the short messages stand for. -/
theorem toE_claimOf (k : ℕ) (first : E) (qs : List (E × E)) (g : List E) :
    toE (claimOf .two k first qs g) =
      hFin (sVars GE 2 k) (toE first)
        (hComp (sVars GE 2 k) (fixOne k) (toE first) (shortOf k (lst2 qs)) (ptK k (lst g)))
        (ptK k (lst g)) :=
  toE_claimFn k first (fun j => qs.getD j (Fmt.Fld.zeroE, Fmt.Fld.zeroE))
    (fun j => g.getD j Fmt.Fld.zeroE)

/-! ## The products of the later elements -/

/-- A product that is built up from the left, started from s, read in the field. -/
theorem toE_tailFoldl (l : List E) (s : E) :
    toE (l.foldl (fun s a => Fmt.Fld.two.mulE s a) s) = toE s * (l.map toE).prod := by
  induction l generalizing s with
  | nil => simp
  | cons a l ih => rw [List.foldl_cons, ih, toE_mulE, List.map_cons, List.prod_cons, mul_assoc]

/-- The product of a list without its first l members, as a product over all places. -/
theorem prod_drop (g : List E) (l : ℕ) :
    ((g.drop l).map toE).prod = ∏ i ∈ Finset.range g.length, if l ≤ i then lst g i else 1 := by
  induction g generalizing l with
  | nil => simp
  | cons a g ih =>
    rw [List.length_cons, Finset.prod_range_succ']
    cases l with
    | zero =>
      have h0 := ih 0
      rw [List.drop_zero] at h0
      rw [List.drop_zero, List.map_cons, List.prod_cons, h0, mul_comm]
      simp only [Nat.zero_le, if_true]
      rfl
    | succ l =>
      rw [List.drop_succ_cons, ih l, if_neg (Nat.not_succ_le_zero l), mul_one]
      refine Finset.prod_congr rfl fun i _ => ?_
      simp only [Nat.add_le_add_iff_right]
      rfl

/-- The product of the members of a list from the place l on. -/
theorem toE_tailProd (g : List E) (l : ℕ) :
    toE (tailProd .two g l) = ∏ i ∈ Finset.range g.length, if l ≤ i then lst g i else 1 := by
  unfold tailProd
  rw [toE_tailFoldl, toE_oneE, one_mul, prod_drop]

/-- The same for a list of h + n members, from the place h + s on. -/
theorem toE_tailProd_late (h n : ℕ) (g : List E) (hg : g.length = h + n) (s : ℕ) :
    toE (tailProd .two g (h + s)) = ∏ t : Fin n, if s ≤ t.val then lst g (h + t.val) else 1 := by
  rw [toE_tailProd, hg, Finset.prod_range_add]
  have h1 : (∏ i ∈ Finset.range h, if h + s ≤ i then lst g i else 1) = 1 :=
    Finset.prod_eq_one fun i hi => if_neg (by have := Finset.mem_range.1 hi; omega)
  rw [h1, one_mul, Finset.prod_range]
  simp only [Nat.add_le_add_iff_left]

/-! ## The hiding weights -/

/-- The place of a column of the library's packing in the format's vector of weights. -/
def hidePlace (h n : ℕ) : PCol h n 1 → ℕ
  | .inl iq => 1 + iq.1.val
  | .inr (.inl tp) => if tp.1.val = 0 ∧ tp.2.val = 0 then 0 else h + 2 * tp.1.val + tp.2.val
  | .inr (.inr _) => if n = 0 then 0 else h + 2 * n

/-- Different columns have different places. -/
theorem hidePlace_inj (h n : ℕ) : Function.Injective (hidePlace h n) := by
  rintro (⟨i, q⟩ | ⟨t, p⟩ | u) (⟨i', q'⟩ | ⟨t', p'⟩ | u') hc
  all_goals
    simp only [hidePlace] at hc
  · have hi : i = i' := Fin.ext (by omega)
    rw [hi, Subsingleton.elim q q']
  · exfalso
    have := i.isLt
    split at hc <;> omega
  · exfalso
    have := i.isLt
    split at hc <;> omega
  · exfalso
    have := i'.isLt
    split at hc <;> omega
  · have := p.isLt
    have := p'.isLt
    have ht : t = t' := Fin.ext (by split at hc <;> split at hc <;> omega)
    have hp : p = p' := Fin.ext (by split at hc <;> split at hc <;> omega)
    rw [ht, hp]
  · exfalso
    have := t.isLt
    have := p.isLt
    split at hc <;> split at hc <;> omega
  · exfalso
    have := i'.isLt
    split at hc <;> omega
  · exfalso
    have := t'.isLt
    have := p'.isLt
    split at hc <;> split at hc <;> omega
  · rfl

/-- Every place is below h + 2 n + 1. -/
theorem hidePlace_lt (h n : ℕ) (c : PCol h n 1) : hidePlace h n c < h + 2 * n + 1 := by
  rcases c with ⟨i, q⟩ | ⟨t, p⟩ | u
  · have := i.isLt
    simp only [hidePlace]
    omega
  · have := t.isLt
    have := p.isLt
    simp only [hidePlace]
    split <;> omega
  · simp only [hidePlace]
    split <;> omega

/-- The format's vector of weights has the length n that it is asked for. -/
theorem size_hideVec (f : Fmt.Fld) (k h n : ℕ) (g : List E) : (hideVec f k h n g).size = n := by
  unfold hideVec
  exact Array.size_ofFn

/-- Every place below h + 2 n + 1 holds a column: there are as many columns as places. -/
theorem hidePlace_surj (h n j : ℕ) (hj : j < h + 2 * n + 1) : ∃ c, hidePlace h n c = j := by
  have hcard : Fintype.card (PCol h n 1) = Fintype.card (Fin (h + 2 * n + 1)) := by
    have e := ld_pack_card h n 1
    rw [Fintype.card_fin]
    omega
  have hinj : Function.Injective
      (fun c : PCol h n 1 => (⟨hidePlace h n c, hidePlace_lt h n c⟩ : Fin (h + 2 * n + 1))) :=
    fun c c' e => hidePlace_inj h n (congrArg Fin.val e)
  obtain ⟨c, hc⟩ := ((Fintype.bijective_iff_injective_and_card _).2 ⟨hinj, hcard⟩).2 ⟨j, hj⟩
  exact ⟨c, congrArg Fin.val hc⟩

/-- A list with one member sq 0, and then two members lin i, sq i for each i from 1 to n - 1. -/
def midL {α : Type} (lin sq : ℕ → α) (n : ℕ) : List α :=
  (List.range n).flatMap fun i => if i = 0 then [sq i] else [lin i, sq i]

section Layout
variable {α : Type} (a0 : α) (hd lin sq : ℕ → α) (one d : α) (h n : ℕ)

/-- One index more: at n = 0 the member sq 0 is added, else the two members lin n and sq n. -/
theorem midL_succ :
    midL lin sq (n + 1) = midL lin sq n ++ if n = 0 then [sq n] else [lin n, sq n] := by
  unfold midL
  rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]

/-- The list has 2 n - 1 members (none at n = 0). -/
theorem length_midL : (midL lin sq n).length = 2 * n - 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [midL_succ, List.length_append, ih]
    split <;> simp only [List.length_cons, List.length_nil] <;> omega

/-- The member sq t is at place 2 t, for t below n. -/
theorem midL_sq : ∀ t, t < n → (midL lin sq n)[2 * t]? = some (sq t) := by
  induction n with
  | zero => intro t ht; omega
  | succ n ih =>
    intro t ht
    rw [midL_succ]
    by_cases hlt : t < n
    · rw [List.getElem?_append_left (by rw [length_midL]; omega)]
      exact ih t hlt
    · have e : n = t := by omega
      subst e
      rw [List.getElem?_append_right (by rw [length_midL]; omega), length_midL]
      split
      · rename_i h0
        rw [h0]
        rfl
      · rw [show 2 * n - (2 * n - 1) = 1 by omega]
        rfl

/-- The member lin t, for t from 1 on, is at place 2 t - 1. -/
theorem midL_lin : ∀ t, 0 < t → t < n → (midL lin sq n)[2 * t - 1]? = some (lin t) := by
  induction n with
  | zero => intro t _ ht; omega
  | succ n ih =>
    intro t h0 ht
    rw [midL_succ]
    by_cases hlt : t < n
    · rw [List.getElem?_append_left (by rw [length_midL]; omega)]
      exact ih t h0 hlt
    · have e : n = t := by omega
      subst e
      rw [List.getElem?_append_right (by rw [length_midL]), length_midL, Nat.sub_self,
        if_neg (by omega)]
      rfl

/-- The order of the format's vector of weights: a first member, h members hd i, the list `midL`,
and a last member if n is not 0. -/
def layL : List α :=
  (a0 :: (List.range h).map hd) ++ (midL lin sq n ++ if 0 < n then [one] else [])

/-- The first member and the h members hd i are h + 1 members. -/
theorem length_head : (a0 :: (List.range h).map hd).length = h + 1 := by
  rw [List.length_cons, List.length_map, List.length_range]

/-- Place 0 holds the first member. -/
theorem layL_zero : (layL a0 hd lin sq one h n).getD 0 d = a0 := rfl

/-- Place 1 + i holds hd i, for i below h. -/
theorem layL_hd (i : ℕ) (hi : i < h) : (layL a0 hd lin sq one h n).getD (1 + i) d = hd i := by
  unfold layL
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_append_left (by rw [length_head]; omega), Nat.add_comm 1 i,
    List.getElem?_cons_succ, List.getElem?_map, List.getElem?_range hi]
  rfl

/-- From place h + 1 on: the list `midL` and then the last member. -/
theorem layL_back (j : ℕ) :
    (layL a0 hd lin sq one h n).getD (h + 1 + j) d =
      ((midL lin sq n ++ if 0 < n then [one] else [])[j]?).getD d := by
  unfold layL
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by rw [length_head]; omega), length_head,
    Nat.add_sub_cancel_left]

/-- Place h + 2 t + 1 holds sq t, for t below n. -/
theorem layL_sq (t : ℕ) (ht : t < n) :
    (layL a0 hd lin sq one h n).getD (h + 2 * t + 1) d = sq t := by
  rw [show h + 2 * t + 1 = h + 1 + 2 * t by omega, layL_back,
    List.getElem?_append_left (by rw [length_midL]; omega), midL_sq lin sq n t ht]
  rfl

/-- Place h + 2 t holds lin t, for t from 1 to n - 1. -/
theorem layL_lin (t : ℕ) (h0 : 0 < t) (ht : t < n) :
    (layL a0 hd lin sq one h n).getD (h + 2 * t) d = lin t := by
  rw [show h + 2 * t = h + 1 + (2 * t - 1) by omega, layL_back,
    List.getElem?_append_left (by rw [length_midL]; omega), midL_lin lin sq n t h0 ht]
  rfl

/-- Place h + 2 n holds the last member, if n is not 0. -/
theorem layL_one (hn : 0 < n) : (layL a0 hd lin sq one h n).getD (h + 2 * n) d = one := by
  rw [show h + 2 * n = h + 1 + (2 * n - 1) by omega, layL_back,
    List.getElem?_append_right (by rw [length_midL]), length_midL, Nat.sub_self, if_pos hn]
  rfl

/-- From place h + 2 n + 1 on nothing is held: the default d is read. -/
theorem layL_far (j : ℕ) (hj : h + 2 * n + 1 ≤ j) :
    (layL a0 hd lin sq one h n).getD j d = d := by
  obtain ⟨i, rfl⟩ : ∃ i, j = h + 1 + i := ⟨j - (h + 1), by omega⟩
  rw [layL_back, List.getElem?_eq_none]
  · rfl
  · rw [List.length_append, length_midL]
    split <;> simp only [List.length_cons, List.length_nil] <;> omega

end Layout

/-- The members of the format's vector of weights, before it is cut or filled to its length. -/
def hideL (f : Fmt.Fld) (h n : ℕ) (g : List E) : List E :=
  layL (tailProd f g h)
    (fun i => f.mulE (g.getD (i + 1 - 1) Fmt.Fld.zeroE) (tailProd f g h))
    (fun i => f.mulE (g.getD (h + 1 + i - 1) Fmt.Fld.zeroE) (tailProd f g (h + 1 + i)))
    (fun i => f.mulE (f.mulE (g.getD (h + 1 + i - 1) Fmt.Fld.zeroE)
      (g.getD (h + 1 + i - 1) Fmt.Fld.zeroE)) (tailProd f g (h + 1 + i)))
    Fmt.Fld.oneE h n

/-- Below its length the format's vector of weights has the members of `hideL`, and 0 after them. -/
theorem ent_hideVec (f : Fmt.Fld) (h n len : ℕ) (g : List E) (j : ℕ) (hj : j < len) :
    ent (hideVec f (h + n) h len g) j = (hideL f h n g).getD j Fmt.Fld.zeroE := by
  unfold ent hideVec hideL layL midL
  simp only [Nat.add_sub_cancel_left, Nat.lt_add_right_iff_pos, List.append_assoc]
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dif_pos hj]
  rfl

/-- Each column's weight is at the column's place. -/
theorem toE_hideL_at (h n : ℕ) (g : List E) (hg : g.length = h + n) (c : PCol h n 1) :
    toE ((hideL .two h n g).getD (hidePlace h n c) Fmt.Fld.zeroE) =
      QwC h n 1 (fun t : Fin (h + n) => lst g t.val) c := by
  have hlate : toE (tailProd .two g h) = ∏ t : Fin n, lst g (h + t.val) := by
    have e := toE_tailProd_late h n g hg 0
    rw [Nat.add_zero] at e
    rw [e]
    exact Finset.prod_congr rfl fun t _ => if_pos (Nat.zero_le _)
  rcases c with ⟨i, q⟩ | ⟨t, p⟩ | u
  · have hq : q.val = 0 := by have := q.isLt; omega
    show toE ((hideL .two h n g).getD (1 + i.val) Fmt.Fld.zeroE) =
      lst g i.val ^ (q.val + 1) * ∏ t : Fin n, lst g (h + t.val)
    unfold hideL
    rw [layL_hd _ _ _ _ _ _ _ _ _ i.isLt, toE_mulE, hlate, hq, Nat.zero_add, pow_one]
    rfl
  · have htail : toE (tailProd .two g (h + 1 + t.val)) =
        ∏ t' : Fin n, if t < t' then lst g (h + t'.val) else 1 := by
      have e := toE_tailProd_late h n g hg (t.val + 1)
      rw [show h + (t.val + 1) = h + 1 + t.val by omega] at e
      exact e
    have hidx : h + 1 + t.val - 1 = h + t.val := by omega
    show toE ((hideL .two h n g).getD
        (if t.val = 0 ∧ p.val = 0 then 0 else h + 2 * t.val + p.val) Fmt.Fld.zeroE) =
      lst g (h + t.val) ^ (p.val + 1) * ∏ t' : Fin n, if t < t' then lst g (h + t'.val) else 1
    unfold hideL
    by_cases h0 : t.val = 0 ∧ p.val = 0
    · rw [if_pos h0, layL_zero, hlate, h0.2, Nat.zero_add, pow_one,
        ← mon_split (fun t' : Fin n => lst g (h + t'.val)) t]
      exact Finset.prod_congr rfl fun t' _ =>
        (if_pos (show t ≤ t' from Fin.le_def.2 (by rw [h0.1]; exact Nat.zero_le _))).symm
    · rw [if_neg h0]
      by_cases hp : p.val = 0
      · rw [hp, Nat.add_zero (h + 2 * t.val), layL_lin _ _ _ _ _ _ _ _ _ (by omega) t.isLt,
          toE_mulE, htail, hidx, Nat.zero_add, pow_one]
        rfl
      · have hp1 : p.val = 1 := by have := p.isLt; omega
        rw [hp1, layL_sq _ _ _ _ _ _ _ _ _ t.isLt, toE_mulE, toE_mulE, htail, hidx, pow_two]
        rfl
  · show toE ((hideL .two h n g).getD (if n = 0 then 0 else h + 2 * n) Fmt.Fld.zeroE) = 1
    unfold hideL
    by_cases hn : n = 0
    · subst hn
      rw [if_pos rfl, layL_zero, hlate]
      rfl
    · rw [if_neg hn, layL_one _ _ _ _ _ _ _ _ (by omega)]
      exact toE_oneE

/-- The format's vector of weights is the library's, each column at its place, and 0 elsewhere.
Asked: the list g has exactly h + n elements, and j is below the vector's length. -/
theorem vec_hideVec (h n len : ℕ) (g : List E) (hg : g.length = h + n) (j : ℕ) (hj : j < len) :
    vec (hideVec .two (h + n) h len g) j =
      ∑ c : PCol h n 1, if hidePlace h n c = j
        then QwC h n 1 (fun t : Fin (h + n) => lst g t.val) c else 0 := by
  unfold vec
  rw [ent_hideVec .two h n len g j hj]
  by_cases hex : ∃ c, hidePlace h n c = j
  · obtain ⟨c, hc⟩ := hex
    rw [← hc, toE_hideL_at h n g hg c,
      Finset.sum_eq_single c (fun c' _ hne => if_neg fun e => hne (hidePlace_inj h n e))
        (fun hm => absurd (Finset.mem_univ c) hm), if_pos rfl]
  · have hfar : h + 2 * n + 1 ≤ j := by
      by_contra hlt
      exact hex (hidePlace_surj h n j (by omega))
    unfold hideL
    rw [layL_far _ _ _ _ _ _ _ _ _ hfar, toE_zeroE]
    exact (Finset.sum_eq_zero fun c _ => if_neg fun e => hex ⟨c, e⟩).symm

/-! ## What a fold hands on -/

/-- The first k members of a list, a missing one counting as 0. -/
theorem lst_firstK (k : ℕ) (g : List E) (t : ℕ) :
    lst ((List.range k).map fun j => g.getD j Fmt.Fld.zeroE) t = if t < k then lst g t else 0 := by
  unfold lst
  split
  · rename_i ht
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht]
    rfl
  · rename_i ht
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using ht)]
    exact toE_zeroE

/-- That list has k members. -/
theorem length_firstK (k : ℕ) (g : List E) :
    ((List.range k).map fun j => g.getD j Fmt.Fld.zeroE).length = k := by
  rw [List.length_map, List.length_range]

/-- `ptL` is `lst` at the first n indices. -/
theorem ptL_eq_lst (n : ℕ) (g : List E) (i : Fin n) : ptL n g i = lst g i.val := rfl

/-- The point that a fold hands on has k members. -/
theorem length_foldStep_g (f : Fmt.Fld) (k h : ℕ) (G : GRow) (sigma eps : E) (qs : List (E × E))
    (g : List E) : (foldStep f k h G sigma eps qs g).g.length = k :=
  length_firstK k g

/-- Its members are the first k drawn elements, a missing one counting as 0. -/
theorem lst_foldStep_g (f : Fmt.Fld) (k h : ℕ) (G : GRow) (sigma eps : E) (qs : List (E × E))
    (g : List E) (t : ℕ) :
    lst (foldStep f k h G sigma eps qs g).g t = if t < k then lst g t else 0 :=
  lst_firstK k g t

/-- As a point of n ≤ k coordinates it is the list of the drawn elements itself. -/
theorem ptL_foldStep_g (f : Fmt.Fld) (k h : ℕ) (G : GRow) (sigma eps : E) (qs : List (E × E))
    (g : List E) (n : ℕ) (hn : n ≤ k) : ptL n (foldStep f k h G sigma eps qs g).g = ptL n g :=
  funext fun i => (lst_foldStep_g f k h G sigma eps qs g i.val).trans
    (if_pos (Nat.lt_of_lt_of_le i.isLt hn))

/-- The same of its first m members, which fold the mask symbols of an opened column. -/
theorem ptL_foldStep_g_take (f : Fmt.Fld) (k h : ℕ) (G : GRow) (sigma eps : E)
    (qs : List (E × E)) (g : List E) (m n : ℕ) (hm : n ≤ m) (hn : n ≤ k) :
    ptL n ((foldStep f k h G sigma eps qs g).g.take m) = ptL n g := by
  rw [← ptL_foldStep_g f k h G sigma eps qs g n hn]
  funext i
  show toE (((foldStep f k h G sigma eps qs g).g.take m).getD i.val Fmt.Fld.zeroE) =
    toE ((foldStep f k h G sigma eps qs g).g.getD i.val Fmt.Fld.zeroE)
  rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (Nat.lt_of_lt_of_le i.isLt hm),
    ← List.getD_eq_getElem?_getD]

/-- The length of the folded main form. -/
theorem size_foldStep_c (f : Fmt.Fld) (k h : ℕ) (G : GRow) (sigma eps : E) (qs : List (E × E))
    (g : List E) : (foldStep f k h G sigma eps qs g).c.size = (G.c.size + 2 ^ k - 1) / 2 ^ k := by
  show (scaleV f eps (foldLow f ((List.range k).map fun j => g.getD j Fmt.Fld.zeroE) G.c)).size = _
  rw [size_scaleV, size_foldLow, length_firstK]

/-- The length of the folded mask form. -/
theorem size_foldStep_d0_eq (f : Fmt.Fld) (k h : ℕ) (G : GRow) (sigma eps : E)
    (qs : List (E × E)) (g : List E) :
    (foldStep f k h G sigma eps qs g).d0.size
      = (G.d.size + 2 ^ min h k - 1) / 2 ^ min h k := by
  show (scaleV f (f.mulE eps (tailProd f ((List.range k).map fun j => g.getD j Fmt.Fld.zeroE) h))
    (foldLow f (((List.range k).map fun j => g.getD j Fmt.Fld.zeroE).take h) G.d)).size = _
  rw [size_scaleV, size_foldLow, List.length_take, length_firstK]

/-- That length does not depend on what is sent or drawn. -/
theorem size_foldStep_d0 (f : Fmt.Fld) (k h : ℕ) (G : GRow) (sigma eps sigma' eps' : E)
    (qs qs' : List (E × E)) (g g' : List E) :
    (foldStep f k h G sigma eps qs g).d0.size = (foldStep f k h G sigma' eps' qs' g').d0.size := by
  rw [size_foldStep_d0_eq, size_foldStep_d0_eq]

/-- The main form that is handed on: the form of the row, fixed at the point, times eps. -/
theorem vec_foldStep_c (k h : ℕ) (G : GRow) (sigma eps : E) (qs : List (E × E)) (g : List E)
    (p : ℕ) :
    vec (foldStep .two k h G sigma eps qs g).c p =
      (∑ β : Fin k → Bool, vec G.c (Sz.rowNo β + 2 ^ k * p)
        * Alg.eqk (fun t : Fin k => lst g t.val) β) * toE eps := by
  show vec (scaleV .two eps
    (foldLow .two ((List.range k).map fun j => g.getD j Fmt.Fld.zeroE) G.c)) p = _
  rw [vec_scaleV, vec_foldLow, length_firstK, sum_range_cube, mul_comm]
  congr 1
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [eqW_congr k _ (lst g) _ fun t ht => (lst_firstK k g t).trans (if_pos ht), eqW_rowNo,
    mul_comm]

/-- The mask form that is handed on: the row's mask form, fixed at the first h coordinates,
times eps and the later coordinates. -/
theorem vec_foldStep_d0 (h n : ℕ) (G : GRow) (sigma eps : E) (qs : List (E × E)) (g : List E)
    (p : ℕ) :
    vec (foldStep .two (h + n) h G sigma eps qs g).d0 p =
      (∑ β : Fin h → Bool, vec G.d (Sz.rowNo β + 2 ^ h * p)
        * Alg.eqk (fun t : Fin h => lst g t.val) β)
        * (toE eps * ∏ t : Fin n, lst g (h + t.val)) := by
  show vec (scaleV .two (Fmt.Fld.two.mulE eps
      (tailProd .two ((List.range (h + n)).map fun j => g.getD j Fmt.Fld.zeroE) h))
    (foldLow .two (((List.range (h + n)).map fun j => g.getD j Fmt.Fld.zeroE).take h) G.d)) p = _
  have hlen : (((List.range (h + n)).map fun j => g.getD j Fmt.Fld.zeroE).take h).length = h := by
    rw [List.length_take, length_firstK]
    omega
  have hpt : ∀ t, t < h →
      lst (((List.range (h + n)).map fun j => g.getD j Fmt.Fld.zeroE).take h) t = lst g t := by
    intro t ht
    unfold lst
    rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt ht, ← List.getD_eq_getElem?_getD]
    exact (lst_firstK (h + n) g t).trans (if_pos (by omega))
  have hlate := toE_tailProd_late h n _ (length_firstK (h + n) g) 0
  rw [Nat.add_zero] at hlate
  rw [vec_scaleV, vec_foldLow, hlen, sum_range_cube, toE_mulE, hlate, mul_comm]
  congr 1
  · refine Finset.sum_congr rfl fun β _ => ?_
    rw [eqW_congr h _ (lst g) _ hpt, eqW_rowNo, mul_comm]
  · congr 1
    refine Finset.prod_congr rfl fun t _ => ?_
    rw [if_pos (Nat.zero_le _)]
    exact (lst_firstK (h + n) g _).trans (if_pos (by have := t.isLt; omega))

/-- The weights are as many as the entries of the folded mask form. -/
theorem size_foldStep_d1 (f : Fmt.Fld) (k h : ℕ) (G : GRow) (sigma eps : E) (qs : List (E × E))
    (g : List E) :
    (foldStep f k h G sigma eps qs g).d1.size = (foldStep f k h G sigma eps qs g).d0.size :=
  size_hideVec f k h _ _

/-- The form on the fresh mask that is handed on: the library's weights at the point. -/
theorem vec_foldStep_d1 (h n : ℕ) (G : GRow) (sigma eps : E) (qs : List (E × E)) (g : List E)
    (j : ℕ) (hj : j < (foldStep .two (h + n) h G sigma eps qs g).d0.size) :
    vec (foldStep .two (h + n) h G sigma eps qs g).d1 j =
      ∑ c : PCol h n 1, if hidePlace h n c = j
        then QwC h n 1 (fun t : Fin (h + n) => lst g t.val) c else 0 := by
  have hz : (fun t : Fin (h + n) =>
      lst ((List.range (h + n)).map fun j => g.getD j Fmt.Fld.zeroE) t.val)
      = fun t : Fin (h + n) => lst g t.val :=
    funext fun t => (lst_firstK (h + n) g t.val).trans (if_pos t.isLt)
  rw [← hz]
  exact vec_hideVec h n _ _ (length_firstK (h + n) g) j hj

/-- The target that is handed on: the end value for the first claim sigma + target * eps. -/
theorem toE_foldStep_t (k h : ℕ) (G : GRow) (sigma eps : E) (qs : List (E × E)) (g : List E) :
    toE (foldStep .two k h G sigma eps qs g).t =
      hFin (sVars GE 2 k) (toE sigma + toE G.t * toE eps)
        (hComp (sVars GE 2 k) (fixOne k) (toE sigma + toE G.t * toE eps) (shortOf k (lst2 qs))
          (ptK k (lst g)))
        (ptK k (lst g)) := by
  show toE (claimOf .two k (Fmt.Fld.two.addE sigma (Fmt.Fld.two.mulE eps G.t)) qs g) = _
  rw [toE_claimOf, toE_addE, toE_mulE, mul_comm (toE eps)]

end OnBytes.Slice

#print axioms OnBytes.Slice.fixOne_ok
#print axioms OnBytes.Slice.toE_nextClaim_hev
#print axioms OnBytes.Slice.toE_claimOf
#print axioms OnBytes.Slice.toE_tailProd_late
#print axioms OnBytes.Slice.hidePlace_inj
#print axioms OnBytes.Slice.hidePlace_surj
#print axioms OnBytes.Slice.vec_hideVec
#print axioms OnBytes.Slice.ptL_foldStep_g
#print axioms OnBytes.Slice.ptL_foldStep_g_take
#print axioms OnBytes.Slice.size_foldStep_c
#print axioms OnBytes.Slice.size_foldStep_d0
#print axioms OnBytes.Slice.size_foldStep_d1
#print axioms OnBytes.Slice.vec_foldStep_c
#print axioms OnBytes.Slice.vec_foldStep_d0
#print axioms OnBytes.Slice.vec_foldStep_d1
#print axioms OnBytes.Slice.toE_foldStep_t
