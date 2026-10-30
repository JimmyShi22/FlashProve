-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/PiecesFam.lean: kind K5: "piece b is pair b": the pieces of a list in
a lookup call whose pieces are laid family by family (famAt, Johnson/Road/Lane5AttLaid.lean), with
their weights, written out: the sort by layer and head returns them in the order of the pairs.

Main names:
  `famPW HA l base n nc zk`: the n pieces of a family of 2^l keys each, laid from key number base on
    in a call of 2^nc keys: piece b has the layer b / HA, the head b % HA and the weight eqAt (the
    first nc - l coordinates of zk) ((base + b 2^l) >>> l).
  `pieces_fam`: where a call's list of pieces is A ++ famAt s … ++ B and no piece of A or B is of
    the list s: Attention.pieces c zk s is famPW ….
  `piecesAll_fam`: PiecesAll S of it, where HA is the shape's and n the number of pairs.
  `wp_fam`: piece b's weight.
  `val_eqAt`: eqAt, read by any reading, is the library's Blocks.eqN (the twin, for any reading, of
    readE_eqAt, OnBytes/Tie/Pv/Lookup/Ends/PortA2.lean).
  `val_wp_fam`: piece b's weight, read, is Blocks.eqN (nc - l) 0 v (base / 2^l + b) for every v that
    the key point reads as on its first nc - l coordinates.
Used: famAt, pcOf; List.mergeSort_of_pairwise; PiecesAll; bit_eq (PortA2.lean).

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Road.Lane5AttLaid
import Johnson.Road.Rows.AttEnds58Proofs
import OnBytes.Tie.Pv.Lookup.Ends.PortA2

set_option autoImplicit false

namespace K5Law
open OnBytes OnBytes.Model OnBytes.Attention OnBytes.Road OnBytes.Road.Rows
open OnBytes.Road.L5 (famAt pcOf)

/-- The pieces of a family with their weights, in the order of the pairs. -/
def famPW (HA l base n nc : ℕ) (zk : Array E) : List PW :=
  (List.range n).map fun b =>
    { lam := b / HA, a := b % HA, wp := eqAt (zk.extract 0 (nc - l)) ((base + b * 2 ^ l) >>> l) }

theorem seg_beq_self (s : Attention.Seg) : (s == s) = true := by cases s <;> rfl

theorem filterMap_fam_same (s : Attention.Seg) (HA l base n nc : ℕ) (zk : Array E) :
    ((famAt s HA l base n).filterMap fun pc =>
      if pc.seg == s then
        some ({ lam := pc.lam, a := pc.a,
                wp := eqAt (zk.extract 0 (nc - pc.b)) (pc.off >>> pc.b) } : PW)
      else none) = famPW HA l base n nc zk := by
  unfold famAt famPW
  rw [List.filterMap_map]
  rw [← List.filterMap_eq_map]
  refine List.filterMap_congr fun b _ => ?_
  show (if (s == s) = true then _ else _) = _
  rw [if_pos (seg_beq_self s)]
  rfl

theorem filterMap_none {α β : Type} (f : α → Option β) : ∀ l : List α, (∀ x ∈ l, f x = none) →
    l.filterMap f = []
  | [], _ => rfl
  | x :: l, h => by
    rw [List.filterMap_cons, h x List.mem_cons_self]
    exact filterMap_none f l fun y hy => h y (List.mem_cons_of_mem _ hy)

theorem le_pairs {HA b b' : ℕ} (h : b < b') :
    PW.le ⟨b / HA, b % HA, zeroE⟩ ⟨b' / HA, b' % HA, zeroE⟩ = true := by
  unfold PW.le
  have h1 : b / HA ≤ b' / HA := Nat.div_le_div_right (Nat.le_of_lt h)
  rcases Nat.lt_or_eq_of_le h1 with h2 | h2
  · simp [h2]
  · have e1 := Nat.div_add_mod b HA
    have e2 := Nat.div_add_mod b' HA
    rw [h2] at e1
    have h3 : b % HA ≤ b' % HA := by omega
    simp [h2, h3]

theorem famPW_sorted (HA l base n nc : ℕ) (zk : Array E) :
    (famPW HA l base n nc zk).Pairwise fun x y => PW.le x y = true := by
  unfold famPW
  rw [List.pairwise_map]
  exact List.pairwise_lt_range.imp fun h => le_pairs h

/-- **The pieces of a list in a call that is laid family by family.** -/
theorem pieces_fam {c : ACall} {s : Attention.Seg} {A B : List Attention.Piece} {HA l base n : ℕ}
    (hp : c.pcs.toList = A ++ famAt s HA l base n ++ B)
    (hA : ∀ pc ∈ A, (pc.seg == s) = false) (hB : ∀ pc ∈ B, (pc.seg == s) = false)
    (zk : Array E) : pieces c zk s = (famPW HA l base n c.call.n zk).toArray := by
  unfold pieces
  dsimp only
  rw [hp, List.filterMap_append, List.filterMap_append, filterMap_fam_same,
    filterMap_none _ A (fun pc h => by rw [hA pc h]; rfl),
    filterMap_none _ B (fun pc h => by rw [hB pc h]; rfl), List.nil_append, List.append_nil,
    List.mergeSort_of_pairwise (famPW_sorted _ _ _ _ _ _)]

theorem famPW_get (HA l base n nc : ℕ) (zk : Array E) {b : ℕ} (hb : b < n) :
    (famPW HA l base n nc zk).toArray[b]? = some ⟨b / HA, b % HA,
      eqAt (zk.extract 0 (nc - l)) ((base + b * 2 ^ l) >>> l)⟩ := by
  unfold famPW
  rw [List.getElem?_toArray, List.getElem?_map, List.getElem?_range hb]
  rfl

/-- **Piece b is pair b.** -/
theorem piecesAll_fam (S : Shape) {HA l base n nc : ℕ} (zk : Array E) (hHA : S.HA = HA)
    (hn : n = S.NP) : PiecesAll S (famPW HA l base n nc zk).toArray := by
  refine ⟨?_, fun b hb w hw => ?_⟩
  · unfold famPW
    rw [List.size_toArray, List.length_map, List.length_range, hn]
  · rw [famPW_get HA l base n nc zk (by rw [hn]; exact hb)] at hw
    have e := Option.some.inj hw
    rw [← e, hHA]
    exact ⟨rfl, rfl⟩

/-- Piece b's weight. -/
theorem wp_fam (HA l base n nc : ℕ) (zk : Array E) {b : ℕ} (hb : b < n) :
    ((famPW HA l base n nc zk).toArray.getD b default).wp =
      eqAt (zk.extract 0 (nc - l)) ((base + b * 2 ^ l) >>> l) := by
  rw [Array.getD_eq_getD_getElem?, famPW_get HA l base n nc zk hb]
  rfl

/-! ## The weights, read -/

variable {Kf : Type} [Field Kf] (ρ : Reading Kf)

theorem val_foldl_range (a : ℕ → E) (r : E) : ∀ m : ℕ,
    ρ.val ((List.range m).foldl (fun s i => mulE s (a i)) r) =
      ρ.val r * ∏ i ∈ Finset.range m, ρ.val (a i)
  | 0 => by
    rw [List.range_zero, List.foldl_nil, Finset.prod_range_zero, mul_one]
  | m + 1 => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ρ.mul,
      val_foldl_range a r m, Finset.prod_range_succ, mul_assoc]

/-- **eqAt, read, is the library's eqN.** -/
theorem val_eqAt (z : Array E) (idx : ℕ) :
    ρ.val (eqAt z idx) = Blocks.eqN z.size 0 (pt ρ z) idx := by
  have h0 : eqAt z idx = (List.range z.size).foldl (fun s i => mulE s
      (if (idx >>> (z.size - 1 - i)) % 2 == 1 then z.getD i zeroE
        else subE oneE (z.getD i zeroE))) oneE := rfl
  rw [h0, val_foldl_range, ρ.one, one_mul]
  unfold Blocks.eqN
  refine Finset.prod_congr rfl fun t _ => ?_
  rw [OnBytes.Ends.A.bit_eq, Nat.zero_add]
  cases idx.testBit (z.size - 1 - t)
  · simp only [Bool.false_eq_true, if_false, ρ.sub, ρ.one]
    rfl
  · simp only [if_true]
    rfl

theorem eqN_agree' (m : ℕ) (a a' : ℕ → Kf) (z : ℕ) (h : ∀ t < m, a t = a' t) :
    Blocks.eqN m 0 a z = Blocks.eqN m 0 a' z := by
  unfold Blocks.eqN
  refine Finset.prod_congr rfl fun t ht => ?_
  rw [Nat.zero_add, h t (Finset.mem_range.1 ht)]

/-- **Piece b's weight, read**: v: what the key point reads as on its first nc - l coordinates. -/
theorem val_wp_fam (HA l base n nc : ℕ) {zk : Array E} (hs : zk.size = nc) {v : ℕ → Kf}
    (hv : ∀ t < nc - l, pt ρ zk t = v t) (hd : 2 ^ l ∣ base) {b : ℕ} (hb : b < n) :
    ρ.val ((famPW HA l base n nc zk).toArray.getD b default).wp =
      Blocks.eqN (nc - l) 0 v (base / 2 ^ l + b) := by
  have hz : (zk.extract 0 (nc - l)).size = nc - l := by
    rw [Array.size_extract, hs]
    omega
  obtain ⟨d, rfl⟩ := hd
  have hi : (2 ^ l * d + b * 2 ^ l) >>> l = 2 ^ l * d / 2 ^ l + b := by
    rw [Nat.shiftRight_eq_div_pow, Nat.mul_div_cancel_left _ (Nat.two_pow_pos l),
      Nat.add_mul_div_right _ _ (Nat.two_pow_pos l), Nat.mul_div_cancel_left _ (Nat.two_pow_pos l)]
  rw [wp_fam HA l _ n nc zk hb, val_eqAt, hz, hi]
  refine eqN_agree' _ _ _ _ fun t ht => ?_
  rw [pt_extract ρ zk (by rw [hs]; omega) (by omega), Nat.zero_add]
  exact hv t ht

end K5Law

#print axioms K5Law.pieces_fam
#print axioms K5Law.piecesAll_fam
#print axioms K5Law.val_wp_fam
