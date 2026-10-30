-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/NormSquares.lean.
WHAT IT DOES NOT SHOW. The law of the level's sumcheck itself: another file's. That the read of the
stream is true: a premise, entry by entry. No chance in this file: algebra alone.
WHAT IT IS. THE NORM's SUMCHECK "squares" AT THE HEAD's ONE NORM: WHAT ITS CALLER's FORMS ARE WORTH.
ext_eq_sum: the library's extension as a sum under the kind's weights. start_value: the start form
(Norm.squaresStart) is worth half^lPd times the batch of the nine hidden sums under gam's powers.
streams_batch: the third of Norm.squareForms' right side, through a true read of the stream at the
level's end point, is worth the extension at that point of the bridge's table of the squares
(OnBytes/Desc/First/NormBridge/BridgeTables.lean: sqTab at dataOf c), entry by entry.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.NormJoint
import Johnson.Desc.Kinds.Law.LevelLaw
import OnBytes.Desc.First.NormBridge.BridgeTables

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open OnBytes.Model (Aff Reading World Fork)
open Norm (lt ls d lPd T S2)
open Came (val)
open D6.Bridge (Data)

/-- The library's extension at a list of coordinates, as a sum under the kind's weights. -/
theorem ext_eq_sum (L : List K) (f : Nat → K) :
    Blocks.ext L.length f (Blocks.ofList L) = (Finset.range (2 ^ L.length)).sum fun X =>
      wt L X * f X := by
  unfold Blocks.ext
  exact Finset.sum_congr rfl fun X _ => by rw [wt_eq_eqN]

/-- A sum over the indices of a point in three parts. -/
theorem sum_three_parts (a b e : List K) (g : Nat → K) :
    ((Finset.range (2 ^ (a ++ b ++ e).length)).sum fun i => wt (a ++ b ++ e) i * g i) =
      (Finset.range (2 ^ a.length)).sum fun k => (Finset.range (2 ^ b.length)).sum fun j =>
        (Finset.range (2 ^ e.length)).sum fun t =>
          wt a k * wt b j * wt e t * g (2 ^ e.length * (2 ^ b.length * k + j) + t) := by
  rw [sum_two_parts (a ++ b) e g]
  have h := sum_two_parts a b fun J => (Finset.range (2 ^ e.length)).sum fun t =>
    wt e t * g (2 ^ e.length * J + t)
  have e1 : ((Finset.range (2 ^ (a ++ b).length)).sum fun J =>
      (Finset.range (2 ^ e.length)).sum fun t =>
        wt (a ++ b) J * wt e t * g (2 ^ e.length * J + t)) =
      (Finset.range (2 ^ (a ++ b).length)).sum fun J => wt (a ++ b) J *
        (Finset.range (2 ^ e.length)).sum fun t => wt e t * g (2 ^ e.length * J + t) :=
    Finset.sum_congr rfl fun J _ => by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun t _ => by ring
  rw [e1, h]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun t _ => by ring

variable [Sizes] [Policy] [Request] [Token]

theorem toList_three_parts (r : Point) (hls : ls ≤ lPd) (hr : r.size = lPd + lt) :
    r.toList = (r.extract 0 (lPd - ls)).toList ++ (r.extract (lPd - ls) lPd).toList ++
      (r.extract lPd (lPd + lt)).toList := by
  simp only [Array.toList_extract, List.extract_eq_take_drop, Nat.sub_zero, List.drop_zero,
    Nat.add_sub_cancel_left]
  have h3 : (r.toList.drop lPd).take lt = r.toList.drop lPd :=
    List.take_of_length_le (by simp [hr])
  have h2 : (r.toList.drop (lPd - ls)).take (lPd - (lPd - ls)) =
      (r.toList.take lPd).drop (lPd - ls) := by
    rw [List.drop_take]
  rw [h3, h2, List.take_eq_take_min]
  have h1 : r.toList.take (lPd - ls) = (r.toList.take lPd).take (lPd - ls) := by
    rw [List.take_take, Nat.min_eq_left (Nat.sub_le _ _)]
  rw [Nat.min_eq_left (by rw [Array.length_toList, hr]; omega), h1, List.take_append_drop,
    List.take_append_drop]

/-- **The streams' batch at the level's end point.** g: gam, read. ent: what entry number i of the
read of the stream is worth. -/
theorem streams_batch (c : NCells) (r : Point) (g : K) (hls : ls ≤ lPd) (hdS : S2 ∣ d)
    (hr : r.size = lPd + lt) (ent : Nat → K)
    (hent : ∀ i, i < 5 * d / S2 → ent i = (Finset.range S2).sum fun j =>
      (Finset.range T).sum fun t => rd (eq (r.extract (lPd - ls) lPd) j) *
        rd (eq (r.extract lPd (lPd + lt)) t) * ((c.stream (S2 * i + j) t : Int) : K)) :
    ((Finset.range (d / S2)).sum fun k => (Finset.range 5).sum fun l =>
      rd (eq (r.extract 0 (lPd - ls)) k) * g ^ l * ent (l * d / S2 + k)) =
      Blocks.ext (lPd + lt) ((dataOf c).sqTab lPd g) (ptK r) := by
  have hS2 : 0 < S2 := by unfold S2; positivity
  set La := (r.extract 0 (lPd - ls)).toList.map rd with hLa
  set Lb := (r.extract (lPd - ls) lPd).toList.map rd with hLb
  set Le := (r.extract lPd (lPd + lt)).toList.map rd with hLe
  have sa : (r.extract 0 (lPd - ls)).size = lPd - ls := by simp [hr]; omega
  have sb : (r.extract (lPd - ls) lPd).size = ls := by simp [hr]; omega
  have se : (r.extract lPd (lPd + lt)).size = lt := by simp [hr]
  have la : La.length = lPd - ls := by rw [hLa, List.length_map, Array.length_toList, sa]
  have lb : Lb.length = ls := by rw [hLb, List.length_map, Array.length_toList, sb]
  have le : Le.length = lt := by rw [hLe, List.length_map, Array.length_toList, se]
  have hL : r.toList.map rd = La ++ Lb ++ Le := by
    rw [hLa, hLb, hLe, ← List.map_append, ← List.map_append, ← toList_three_parts r hls hr]
  have hlen : (La ++ Lb ++ Le).length = lPd + lt := by
    rw [List.length_append, List.length_append, la, lb, le]
    omega
  unfold ptK
  rw [hL, ← hlen, ext_eq_sum, sum_three_parts, la, lb, le]
  -- the blocks beyond d / S2 hold zeros
  have hdk : d / S2 ≤ 2 ^ (lPd - ls) := by
    have h1 : d ≤ 2 ^ lPd := le_two_pow_clog2 d
    have h2 : (2 : Nat) ^ lPd = 2 ^ (lPd - ls) * S2 := by
      unfold S2
      rw [← pow_add]
      congr 1
      omega
    exact Nat.div_le_of_le_mul (by rw [Nat.mul_comm, ← h2]; exact h1)
  rw [← sum_ite_lt hdk]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk2 := Finset.mem_range.mp hk
  have hwa : wt La k = rd (eq (r.extract 0 (lPd - ls)) k) := wt_toList _ (by rw [sa]; exact hk2)
  have htab : ∀ j, j < S2 → ∀ t, t < T →
      (dataOf c).sqTab lPd g (2 ^ lt * (2 ^ ls * k + j) + t) =
        if k < d / S2 then (Finset.range 5).sum fun l =>
          g ^ l * ((c.stream (l * d + (S2 * k + j)) t : Int) : K) else 0 := by
    intro j hj t ht
    have hJ : 2 ^ ls * k + j < 2 ^ lPd := by
      have h2 : (2 : Nat) ^ lPd = 2 ^ ls * 2 ^ (lPd - ls) := by
        rw [← pow_add]
        congr 1
        omega
      have hj' : j < 2 ^ ls := hj
      rw [h2]
      calc 2 ^ ls * k + j < 2 ^ ls * k + 2 ^ ls := by omega
        _ = 2 ^ ls * (k + 1) := by ring
        _ ≤ 2 ^ ls * 2 ^ (lPd - ls) := Nat.mul_le_mul_left _ hk2
    have h := (dataOf c).sqTab_at lPd g 0 (2 ^ ls * k + j) t hJ ht
    have e0 : (0 * 2 ^ lPd + (2 ^ ls * k + j)) * 2 ^ (dataOf c).lt + t =
        2 ^ lt * (2 ^ ls * k + j) + t := by
      show (0 * 2 ^ lPd + (2 ^ ls * k + j)) * 2 ^ lt + t = _
      ring
    rw [e0] at h
    rw [h]
    have hiff : ((0 : Nat) < (dataOf c).NI ∧ 2 ^ ls * k + j < (dataOf c).d) ↔ k < d / S2 := by
      show ((0 : Nat) < 1 ∧ S2 * k + j < d) ↔ _
      obtain ⟨q, hq⟩ := hdS
      rw [hq, Nat.mul_div_cancel_left _ hS2]
      constructor
      · rintro ⟨_, h1⟩
        by_contra hc
        have : S2 * q ≤ S2 * k := Nat.mul_le_mul_left _ (by omega)
        omega
      · intro h1
        refine ⟨Nat.one_pos, ?_⟩
        calc S2 * k + j < S2 * k + S2 := by omega
          _ = S2 * (k + 1) := by ring
          _ ≤ S2 * q := Nat.mul_le_mul_left _ h1
    by_cases hc : k < d / S2
    · rw [if_pos (hiff.mpr hc), if_pos hc]
      rfl
    · rw [if_neg (fun h' => hc (hiff.mp h')), if_neg hc]
  by_cases hc : k < d / S2
  · rw [if_pos hc]
    have hidx : ∀ l, l < 5 → l * d / S2 + k < 5 * d / S2 := by
      intro l hl
      obtain ⟨q, hq⟩ := hdS
      rw [hq] at hc ⊢
      rw [Nat.mul_div_cancel_left _ hS2] at hc
      rw [show l * (S2 * q) = S2 * (l * q) by ring, show 5 * (S2 * q) = S2 * (5 * q) by ring,
        Nat.mul_div_cancel_left _ hS2, Nat.mul_div_cancel_left _ hS2]
      nlinarith
    have hsplit : ∀ l, S2 * (l * d / S2 + k) = l * d + S2 * k := by
      intro l
      rw [Nat.mul_add, Nat.mul_div_cancel' (Dvd.dvd.mul_left hdS l)]
    calc ((Finset.range 5).sum fun l =>
          rd (eq (r.extract 0 (lPd - ls)) k) * g ^ l * ent (l * d / S2 + k))
        = (Finset.range 5).sum fun l => (Finset.range S2).sum fun j => (Finset.range T).sum fun t =>
            wt La k * wt Lb j * wt Le t *
              (g ^ l * ((c.stream (l * d + (S2 * k + j)) t : Int) : K)) := by
          refine Finset.sum_congr rfl fun l hl => ?_
          rw [hent _ (hidx l (Finset.mem_range.mp hl)), Finset.mul_sum]
          refine Finset.sum_congr rfl fun j hj => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun t ht => ?_
          rw [hwa, wt_toList _ (by rw [sb]; exact Finset.mem_range.mp hj),
            wt_toList _ (by rw [se]; exact Finset.mem_range.mp ht), hsplit, Nat.add_assoc]
          ring
      _ = (Finset.range (2 ^ ls)).sum fun j => (Finset.range (2 ^ lt)).sum fun t =>
            wt La k * wt Lb j * wt Le t *
              (dataOf c).sqTab lPd g (2 ^ lt * (2 ^ ls * k + j) + t) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j hj => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun t ht => ?_
          rw [htab j (Finset.mem_range.mp hj) t (Finset.mem_range.mp ht), if_pos hc, Finset.mul_sum]
  · rw [if_neg hc]
    symm
    refine Finset.sum_eq_zero fun j hj => Finset.sum_eq_zero fun t ht => ?_
    rw [htab j (Finset.mem_range.mp hj) t (Finset.mem_range.mp ht), if_neg hc, mul_zero]

/-! ## The level's law at the kind's own three forms -/

open OnBytes.Desc.First.P1 (mle tot ext1 IsSum mle_ext1)
open Part.MaskedSum (Var Call weightsOf)
open Came (vsG vsG_d vsG_length sEndL coreL badLv badLv_length)

/-- An extension by mle, of a table on numbers, is the library's. -/
theorem mle_eq_ext (L : List K) (f : Nat → K) :
    mle L.length (fun b => f (idxOf b)) L = Blocks.ext L.length f (Blocks.ofList L) := by
  rw [mle_idx, ext_eq_sum]

section Letters
variable (c : NCells) (mask : Nat → E) (F0 : Fork) (pV : Point) (gam : E)

/-- The level's point at one norm: no coordinate on the norms; lPd halves; pV. -/
def zS : Point := (#[] : Point) ++ halves lPd ++ pV

def AtS : List Bool → K := fun b => (dataOf c).sqTab lPd (rd gam) (idxOf b)

def SmS : List K → K := fun rs =>
  mle ((vsG (zS pV)).length + 1)
      (ext1 (vsG (zS pV)).length (AtS c gam) (rd (mask (sEndL (zS pV) F0)))) rs *
    mle ((vsG (zS pV)).length + 1)
      (ext1 (vsG (zS pV)).length (AtS c gam) (rd (mask (sEndL (zS pV) F0 + 1)))) rs

def sigS : K := tot (weightsOf Reading.gl (vsG (zS pV))) fun b => AtS c gam b * AtS c gam b

theorem hSS : IsSum ((⟨0, vsG (zS pV), some ⟨2, 2⟩⟩ : Call).all.map (Var.wt Reading.gl))
    (SmS c mask F0 pV gam) (sigS c pV gam) :=
  Part.MaskedSum.isSum_product Reading.gl 0 (vsG (zS pV)) 2
    (fun v hv => by rw [vsG_d _ v hv]) _ _ _ _

/-- **The rule for the bad elements of "squares"**, by name: of the cells, the masks, the ledger in
front, pV, gam, and the start form's two values. -/
noncomputable def squaresRule (Tt : E) (Cv : K) : List Fmt.RoundView → List E :=
  badLv (zS pV) (SmS c mask F0 pV gam) (sigS c pV gam) (hSS c mask F0 pV gam) mask F0 Tt Cv

theorem squaresRule_length (Tt : E) (Cv : K) (h : List Fmt.RoundView) :
    (squaresRule c mask F0 pV gam Tt Cv h).length ≤
      ((h.getLast?.map fun r => r.vals.length).getD 0) + 1 :=
  badLv_length _ _ _ _ _ _ _ _ h

theorem zS_size (hz : pV.size = lt) : (zS pV).size = lPd + lt := by
  unfold zS halves
  simp [hz]

/-- The table's square, summed at the level's point: half^lPd times the extension at pV of the sum
over the features of the square of the limbs' batch. -/
theorem sigS_eq (hz : pV.size = lt) : sigS c pV gam = rd half ^ lPd *
    Blocks.ext lt (fun t => (Finset.range d).sum fun j =>
      ((Finset.range 5).sum fun l => rd gam ^ l * ((limbZ c t l j : Int) : K)) ^ 2) (ptK pV) := by
  have hw : weightsOf Reading.gl (vsG (zS pV)) =
      ((zS pV).toList.map rd).map fun x => (1 - x, x) := by
    unfold weightsOf vsG
    simp only [List.map_map]
    rfl
  have hlen : ((zS pV).toList.map rd).length = lPd + lt := by
    rw [List.length_map, Array.length_toList, zS_size pV hz]
  unfold sigS
  rw [hw, tot_pairs]
  have h := mle_eq_ext ((zS pV).toList.map rd) fun X =>
    (dataOf c).sqTab lPd (rd gam) X * (dataOf c).sqTab lPd (rd gam) X
  refine Eq.trans h ?_
  rw [hlen]
  have hmid : ∀ t, t < lPd →
      Blocks.ofList ((zS pV).toList.map rd) ((dataOf c).lNI + t) = rd half := by
    intro t ht
    show Blocks.ofList ((zS pV).toList.map rd) (0 + t) = _
    unfold Blocks.ofList zS
    rw [Nat.zero_add, Array.toList_append, Array.toList_append, List.map_append, List.map_append,
      map_rd_halves, rd_half]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left, ht]
  have he := (dataOf c).ext_sqTab lPd (le_two_pow_clog2 d) (le_refl 1) (rd gam) (rd half)
    (by rw [rd_half]; exact half_K) (Blocks.ofList ((zS pV).toList.map rd)) hmid
  have hidx : (dataOf c).lNI + lPd + (dataOf c).lt = lPd + lt := by
    show 0 + lPd + lt = _
    omega
  rw [hidx] at he
  rw [he]
  congr 1
  show (Finset.range 1).sum _ = _
  rw [Finset.sum_range_one]
  have e1 : Blocks.eqN (dataOf c).lNI 0 (Blocks.ofList ((zS pV).toList.map rd)) 0 = 1 := by
    show Blocks.eqN 0 0 _ 0 = 1
    simp [Blocks.eqN]
  rw [e1, one_mul]
  unfold Data.sqZ
  refine ext_congr_pt lt _ fun t ht => ?_
  show Blocks.ofList ((zS pV).toList.map rd) (0 + lPd + t) = ptK pV t
  unfold Blocks.ofList ptK Blocks.ofList zS
  rw [Array.toList_append, Array.toList_append, List.map_append, List.map_append, map_rd_halves]
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]

end Letters

open Part.MaskedSum (readAll challenges)
open Came (heardBy_cut round_some kG)

/-- A level's challenges are as many as its point's coordinates. -/
theorem level_r_size {z : Point} {start : Form} {F0 F1 : Fork} {t : List Fmt.RoundView} {S : Sum}
    (hlev : level z start F0 t = some (S, F1, [])) : S.r.size = z.size := by
  unfold level at hlev
  obtain ⟨cs, G1, l1, h1, k1⟩ := bind_some hlev
  obtain ⟨c, s⟩ := cs
  dsimp only at k1
  obtain ⟨ag, G2, l2, h2, k2⟩ := bind_some k1
  obtain ⟨a, g⟩ := ag
  dsimp only at k2
  obtain ⟨dn, G3, l3, h3, k3⟩ := bind_some k2
  obtain ⟨_, rfl, rfl⟩ := need_some h3
  obtain ⟨rfl, rfl, rfl⟩ := pure_some k3
  obtain ⟨e1, _, _⟩ := heardBy_cut h1
  obtain ⟨ld, Fa, G, hd, es, a1, a2, a3, a4, a5, a6, hs⟩ := heardBy_spec e1
  have hk : callOf 0 z 2 = ⟨0, vsG z, some ⟨2, 2⟩⟩ := rfl
  rw [hk] at a2 a4 hs
  obtain ⟨_, Tt', R, hpub, hread, hhd, hrun2⟩ := Part.MaskedSum.hear_spec a4
  obtain ⟨r0, used, rv, front, ht, hs0, hfl, hvr, hsv⟩ := Part.MaskedSum.readAll_spec hread
  have hlenR : R.rounds.length = (vsG z).length + 1 := by
    rw [hvr.length.2]
    show (vsG z ++ [Var.point OnBytes.zeroE 3]).length = _
    simp
  have hrlen : hd.r.length = (vsG z).length + 1 := by
    rw [hhd]
    show (R.rounds.map (·.2)).length = _
    rw [List.length_map, hlenR]
  have hv : (vsG z).length = z.size := by
    unfold vsG
    rw [List.length_map, Array.length_toList]
  show s.r.size = _
  rw [hs]
  show (challenges ⟨0, vsG z, some ⟨2, 2⟩⟩ hd).toArray.size = _
  rw [List.size_toArray]
  show (hd.r.take (vsG z).length).length = _
  rw [List.length_take, hrlen, hv]
  omega

section SquaresText
variable [FinalNorm.In] [Norm.Heard] [FinalNorm.Heard] [FinalNorm.Reads]

/-- The start form at one norm: half^lPd times the batch of the nine hidden sums. -/
theorem start_value (W : World K) :
    val W (Norm.squaresStart Norm.W Norm.gam #[]) =
      rd half ^ lPd * (Finset.range 9).sum fun s => rd Norm.gam ^ s * WtOf W s := by
  unfold Norm.squaresStart
  rw [Came.val_smulE, rd_pow, Came.val_sumTo]
  show _ * (Finset.range 1).sum _ = _
  rw [Finset.sum_range_one, Came.val_sumTo]
  have e : ∀ s, val W ((eq (#[] : Point) 0 * Norm.gam ^ s) • (Norm.W.getD (9 * 0 + s) {}).var) =
      rd Norm.gam ^ s * WtOf W s := by
    intro s
    have h1 : rd (eq (#[] : Point) 0) = 1 := by
      rw [rd_eq]
      simp [wt]
    rw [Came.val_smulE, rd_mul, rd_pow, h1, one_mul, Nat.mul_zero, Nat.zero_add]
    rfl
  rw [Finset.sum_congr rfl fun s _ => e s]

/-- Norm.squareForms at the head's one norm, written out. -/
theorem squareForms_eq :
    Norm.squareForms =
      [Norm.squares.left ((Norm.squares.end_ 0).shown * (Norm.squares.end_ 1).shown),
       (Norm.squares.end_ 0).var - (Norm.squares.end_ 1).var,
       (Norm.squares.end_ 0).var - sumTo 1 fun i => sumTo (d / S2) fun k => sumTo 5 fun l =>
         (eq (Norm.squares.r.extract 0 (Norm.lNI + lPd - ls)) (i * 2 ^ lPd / S2 + k) *
           Norm.gam ^ l) • Norm.limb i l k] := rfl

/-- The first end value is the table's extension at the challenges: the third form, with a true
read of the stream. -/
theorem squares_end0 (c : NCells) (hls : ls ≤ lPd) (hdS : S2 ∣ d) (W : World K)
    (hr : Norm.squares.r.size = lPd + lt)
    (hread : ∀ i, i < 5 * d / S2 → val W (FinalNorm.entry .streamAtSquares i) =
      rd (readAtN c (.stream, Norm.Read.streams.weights) i))
    (f2 : val W ((Norm.squares.end_ 0).var - sumTo 1 fun i => sumTo (d / S2) fun k =>
      sumTo 5 fun l =>
        (eq (Norm.squares.r.extract 0 (Norm.lNI + lPd - ls)) (i * 2 ^ lPd / S2 + k) *
          Norm.gam ^ l) • Norm.limb i l k) = 0) :
    val W (Norm.squares.end_ 0).var =
      Blocks.ext (lPd + lt) ((dataOf c).sqTab lPd (rd Norm.gam)) (ptK Norm.squares.r) := by
  have hN0 : Norm.lNI = 0 := rfl
  have hent : ∀ i, i < 5 * d / S2 → val W (FinalNorm.entry .streamAtSquares i) =
      (Finset.range S2).sum fun j => (Finset.range T).sum fun t =>
        rd (eq (Norm.squares.r.extract (lPd - ls) lPd) j) *
          rd (eq (Norm.squares.r.extract lPd (lPd + lt)) t) *
          ((c.stream (S2 * i + j) t : Int) : K) := by
    intro i hi
    rw [hread i hi]
    show rd (sumTo S2 fun j => sumTo T fun t =>
      eq (Norm.squares.r.extract (Norm.lNI + lPd - ls) (Norm.lNI + lPd)) j *
        eq (Norm.squares.r.extract (Norm.lNI + lPd) (Norm.lNI + lPd + lt)) t *
        ofInt (c.stream (S2 * i + j) t)) = _
    rw [hN0, Nat.zero_add, rd_sumTo]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [rd_sumTo]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [rd_mul, rd_mul, rd_ofInt]
  rw [Came.val_sub] at f2
  rw [sub_eq_zero.mp f2, Came.val_sumTo, Finset.sum_range_one, Came.val_sumTo,
    ← streams_batch c Norm.squares.r (rd Norm.gam) hls hdS hr _ hent]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Came.val_sumTo]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Came.val_smulE, rd_mul, rd_pow, hN0, Nat.zero_add, Nat.zero_mul, Nat.zero_div,
    Nat.zero_add]
  rfl

/-- The bridge's Squares at one norm, written out. -/
theorem squares_of_eq (c : NCells) (u : Nat → K) (Wt : Nat → K) (g : K) (v : Nat → K)
    (h : ((Finset.range 9).sum fun s => g ^ s * Wt s) =
      Blocks.ext lt (fun t => (Finset.range d).sum fun j =>
        ((Finset.range 5).sum fun l => g ^ l * ((limbZ c t l j : Int) : K)) ^ 2) u) :
    (dataOf c).Squares u Wt g v := by
  show (Finset.range 1).sum (fun i => Blocks.eqN 0 0 v i *
      (Finset.range 9).sum fun s => g ^ s * Wt (9 * i + s)) =
    (Finset.range 1).sum fun i => Blocks.eqN 0 0 v i *
      Blocks.ext lt (fun t => (Finset.range d).sum fun j =>
        ((Finset.range 5).sum fun l => g ^ l * ((limbZ c t l j : Int) : K)) ^ 2) u
  rw [Finset.sum_range_one, Finset.sum_range_one, ← h]
  simp

/-- **What the squares' level shows, of the kind's own three forms**: the batch of the nine hidden
sums is the extension at pV of the sum over the features of the square of the limbs' batch. The
cells, the masks, the ledger in front of the level, pV, gam, and the start form's two values (Tt on
what is shown, Cv on what is hidden) stand first; the rule for the bad elements is squaresRule. -/
theorem squares_eq (c : NCells) (mask : Nat → E) (F0 : Fork) (Tt : E) (Cv : K)
    (hWL : WellLaid F0) (hz : (Norm.pV).size = lt) (hls : ls ≤ lPd) (hdS : S2 ∣ d)
    {F1 : Fork} {t : List Fmt.RoundView} (W : World K)
    (hWs : ∀ j, F0.next ≤ j → j < sEndL (zS Norm.pV) F0 + 2 → W.slot j = rd (hidden F1 mask j))
    (hcan : Canonical t)
    (hlev : level (zS Norm.pV) (Norm.squaresStart Norm.W Norm.gam #[]) F0 t =
      some (Norm.squares, F1, []))
    (hT : F0.publicPart (Norm.squaresStart Norm.W Norm.gam #[]) = some Tt)
    (hC : val W (Norm.squaresStart Norm.W Norm.gam #[]) = Cv)
    (hread : ∀ i, i < 5 * d / S2 → val W (FinalNorm.entry .streamAtSquares i) =
      rd (readAtN c (.stream, Norm.Read.streams.weights) i))
    (hforms : ∀ f, f ∈ Norm.squareForms → val W f = 0)
    (hnb : NoBad (squaresRule c mask F0 Norm.pV Norm.gam Tt Cv) t) :
    ((Finset.range 9).sum fun s => rd Norm.gam ^ s * WtOf W s) =
      Blocks.ext lt (fun t => (Finset.range d).sum fun j =>
        ((Finset.range 5).sum fun l => rd Norm.gam ^ l * ((limbZ c t l j : Int) : K)) ^ 2)
        (ptK Norm.pV) := by
  rw [squareForms_eq] at hforms
  have f0 := hforms _ (List.mem_cons_self ..)
  have f1 := hforms _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have f2 := hforms _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  have hr : Norm.squares.r.size = lPd + lt := by rw [level_r_size hlev, zS_size _ hz]
  have g0 := squares_end0 c hls hdS W hr hread f2
  have g1 : val W (Norm.squares.end_ 1).var = val W (Norm.squares.end_ 0).var := by
    rw [Came.val_sub] at f1
    exact (sub_eq_zero.mp f1).symm
  have hlenr : (Norm.squares.r.toList.map rd).length = lPd + lt := by
    rw [List.length_map, Array.length_toList, hr]
  have hm : mle (lPd + lt) (AtS c Norm.gam) (Norm.squares.r.toList.map rd) =
      Blocks.ext (lPd + lt) ((dataOf c).sqTab lPd (rd Norm.gam)) (ptK Norm.squares.r) := by
    have h := mle_eq_ext (Norm.squares.r.toList.map rd) ((dataOf c).sqTab lPd (rd Norm.gam))
    rw [hlenr] at h
    exact h
  have hvl : (vsG (zS Norm.pV)).length = lPd + lt := by
    unfold vsG
    rw [List.length_map, Array.length_toList, zS_size _ hz]
  have hres := coreL (zS Norm.pV) (SmS c mask F0 Norm.pV Norm.gam) (sigS c Norm.pV Norm.gam)
    (hSS c mask F0 Norm.pV Norm.gam) mask F0 Tt Cv _ hWL W hWs hcan hlev hT hC _ f0
    (fun β hβ => by
      unfold SmS
      rw [Part.MaskedSum.product_at (vsG (zS Norm.pV)).length _ _ _ _ _ _
        (by rw [hlenr, hvl]), rd_mul, hβ 0 (by omega), hβ 1 (by omega), hvl, hm, Nat.add_zero]
      show _ = (val W (Norm.squares.end_ 0).var + _) * (val W (Norm.squares.end_ 1).var + _)
      rw [g1, g0]
      rfl) hnb
  rw [← hC, start_value, sigS_eq c _ _ hz] at hres
  have hh0 : rd half ^ lPd ≠ 0 := by
    apply pow_ne_zero
    rw [rd_half]
    exact inv_ne_zero (by
      intro h2
      have := half_K
      rw [h2] at this
      simp at this)
  exact mul_left_cancel₀ hh0 hres

end SquaresText

end VerifiableInference.Desc.Kinds.Head.Law
