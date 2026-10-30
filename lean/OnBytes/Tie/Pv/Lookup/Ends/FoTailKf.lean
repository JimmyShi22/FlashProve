-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoTailKf.lean.
What the runs of the smallness test's claim on its key vectors read is the extension of each call's
key vector at the call's point.

OnBytes/Tie/Pv/Lookup/Ends/FoTailJoinVal.lean shows that the hand-made claim of linJoin9 is worth
claimJoin at the letter kfRun: the sum over a call's pieces of the piece's weight times a run on the
piece's virtual row. This file shows, under the premises named at kf_ext, that kfRun is the
multilinear extension of the call's own key vector (Kp, OnBytes/Tie/Pv/Lookup/Digits/PortKeys.lean:
the digits as entries of the array ZZ) at the call's point. That this extension is the value of the
digits' key form is not stated here but in OnBytes/Tie/Pv/Lookup/Ends/FoTailDig.lean (kf_dig).

* eqOne_fold, eqOne_blocks: the byte-level eqOne, read in a field, is the library's Blocks.eqN,
  where the routine's own test of the index (eqIndexOK) passes.
* PieceOK tl q n p: what is asked of a piece's public numbers. It is a premise here; no statement
  of this file says that the pieces of a smallness test meet it.
* pieceKeys, kp_pwVec: the call's key vector is laid in pieces (pwVec,
  Cb/Pv/Lookup/Ends/Pieces.lean).
* kf_piece: kf_ext for one piece: its weight times its run is its weight times the extension of its
  keys.
* kf_ext: kfRun = Blocks.ext n (Kp tl μ q) at the call's point. Under: PieceOK of each piece; the
  pieces' key places lie apart; the point has n coordinates, n at most 63; and each piece's virtual
  row is the combination of its rows of ZZ under the equality weights of the point's coordinates for
  the rows (a hypothesis on the world: hV).

Not claimed: anything on completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoTailJoinVal
import OnBytes.Tie.Pv.Lookup.Ends.FoPieceExt
import OnBytes.Tie.Pv.Lookup.Ends.FoVirtRow
import OnBytes.Tie.Pv.Lookup.Forest.FoDig5

set_option autoImplicit false

namespace Fo
open TwV OnBytes OnBytes.Model OnBytes.Model.Forest OnBytes.DgP OnBytes.Ends Finset

section
variable {K : Type} [Field K] (ρ : Reading K)

/-- The fold of eqOne, from any state: coordinate number t goes with bit n - 1 - t. -/
theorem eqOne_fold (c : ℕ) : ∀ (l : List E) (s : E) (n : ℕ),
    ρ.val (l.foldl (fun (s : E × ℕ) zv =>
      (if c.testBit (s.2 - 1) then mulE s.1 zv else subE s.1 (mulE s.1 zv), s.2 - 1)) (s, n)).1 =
      ρ.val s * ∏ t ∈ range l.length,
        (if c.testBit (n - 1 - t) then ρ.val (l.getD t zeroE) else 1 - ρ.val (l.getD t zeroE))
  | [], s, n => by simp
  | zv :: l, s, n => by
    rw [List.foldl_cons, eqOne_fold c l, List.length_cons, Finset.prod_range_succ']
    have e : ∀ t, n - 1 - (t + 1) = n - 1 - 1 - t := fun t => by omega
    have P : ∀ t, (if c.testBit (n - 1 - (t + 1)) then ρ.val ((zv :: l).getD (t + 1) zeroE)
        else 1 - ρ.val ((zv :: l).getD (t + 1) zeroE)) =
        (if c.testBit (n - 1 - 1 - t) then ρ.val (l.getD t zeroE)
        else 1 - ρ.val (l.getD t zeroE)) := fun t => by rw [e t, List.getD_cons_succ]
    simp only [P, List.getD_cons_zero, Nat.sub_zero]
    by_cases hb : c.testBit (n - 1) = true
    · simp only [hb, if_true, ρ.mul]
      ring
    · simp only [hb, Bool.false_eq_true, if_false, ρ.sub, ρ.mul]
      ring

/-- A single equality weight, where the index is in range. -/
theorem eqOne_blocks (z : Array E) (c : ℕ) (hok : eqIndexOK z c = true) :
    ρ.val (eqOne z c) = Blocks.eqN z.size 0 (Blocks.ofList (rdL ρ z)) c := by
  unfold eqOne
  rw [if_pos hok, ← Array.foldl_toList]
  have r := eqOne_fold ρ c z.toList oneE z.size
  rw [ρ.one, one_mul] at r
  refine r.trans ?_
  unfold Blocks.eqN Blocks.ofList
  rw [Array.length_toList]
  refine prod_congr rfl fun t _ => ?_
  have e : ρ.val (z.toList.getD t zeroE) = (rdL ρ z).getD (0 + t) 0 := by
    rw [Nat.zero_add, ← rdL_getD]
    simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]
  rw [e]

end

/-- What is asked of a piece's public numbers. n: the number of bits of the call's key numbers. -/
structure PieceOK (tl : HTailF2) (q n : ℕ) (p : Piece) : Prop where
  tree : p.tree = tl.ix.ZZ
  c0 : p.c0 = q * tl.mz
  le : p.Cp ≤ p.CP
  pw : p.CP = 2 ^ clog2 p.CP
  rp : p.Rp = 2 ^ p.a
  b : p.b = p.a + clog2 p.CP
  bn : p.b ≤ n
  dvd : 2 ^ p.b ∣ p.off
  fit : p.off + 2 ^ p.b ≤ 2 ^ n

section
variable {K : Type} [Field K]

/-- The keys of one piece, by their numbers inside the piece. -/
def pieceKeys (tl : HTailF2) (μ : Ent3 → K) (q : ℕ) (p : Piece) (Y : ℕ) : K :=
  if Y / p.CP < p.Rp ∧ Y % p.CP < p.Cp then μ (tl.ix.ZZ, p.r0 + Y / p.CP, q * tl.mz + Y % p.CP)
  else 0

/-- The call's key vector is laid in pieces. -/
theorem kp_pwVec (tl : HTailF2) (μ : Ent3 → K) (q : ℕ) :
    Kp tl μ q = pwVec (fun p : Piece => p.off) (fun p => p.b) (pieceKeys tl μ q) 0 (piecesL tl q) :=
      by
  funext X
  rw [← pwVec_find]
  unfold Kp digInCall pieceK
  have e : (fun p : Piece => decide (p.off ≤ X) && decide (X < p.off + 2 ^ p.b)) =
      fun p : Piece => decide (p.off ≤ X ∧ X < p.off + 2 ^ p.b) :=
    funext fun p => (Bool.decide_and _ _).symm
  rw [e]
  cases (piecesL tl q).find? fun p : Piece => decide (p.off ≤ X ∧ X < p.off + 2 ^ p.b) with
  | none => rfl
  | some p =>
    show (match OnBytes.DgP.cut p q X with
      | some t => μ (tl.ix.ZZ, t.2.2, q * tl.mz + t.2.1)
      | none => 0) = pieceKeys tl μ q p (X - p.off)
    unfold OnBytes.DgP.cut pieceKeys
    split_ifs <;> rfl

end

section
variable {K : Type} [Field K] (ρ : Reading K) (W : World K)

/-- One piece: its weight times its run is its weight times the extension of its keys. -/
theorem kf_piece (tl : HTailF2) (g : Heard) (q : ℕ) (μ : Ent3 → K) (p : Piece)
    (hn : (g.zk.getD q #[]).size = (tl.zOf q).call.n) (h63 : (tl.zOf q).call.n ≤ 63)
    (hP : PieceOK tl q (tl.zOf q).call.n p)
    (hV : ∀ i < p.Cp, W.entry p.tree p.row (p.c0 + i) = ∑ r ∈ range p.Rp,
      (eqTabK (exL (rdL ρ (g.zk.getD q #[])) ((tl.zOf q).call.n - p.b)
        ((tl.zOf q).call.n - p.b + p.a))).getD r 0 * μ (tl.ix.ZZ, p.r0 + r, p.c0 + i)) :
    ρ.val (eqOne ((g.zk.getD q #[]).extract 0 ((tl.zOf q).call.n - p.b)) (p.off / 2 ^ p.b)) *
        runSum (fun i => ρ.val ((eqTab (joinZc tl g q p)).getD i zeroE) *
          W.entry p.tree p.row (p.c0 + i)) p.Cp 0 =
      wpAt (tl.zOf q).call.n p.off p.b (Blocks.ofList (rdL ρ (g.zk.getD q #[]))) *
        Blocks.ext p.b (pieceKeys tl μ q p)
          (innAt (tl.zOf q).call.n p.b (Blocks.ofList (rdL ρ (g.zk.getD q #[])))) := by
  obtain ⟨_, h0, hle, hpw, hrp, hb, hbn, hdv, hft⟩ := hP
  generalize hnn : (tl.zOf q).call.n = n at *
  generalize hzz : g.zk.getD q #[] = zk at *
  have hzl : (rdL ρ zk).length = n := by
    unfold rdL
    rw [List.length_map, Array.length_toList, hn]
  generalize hk : clog2 p.CP = k at *
  have hp2 : 0 < 2 ^ p.b := Nat.pos_of_ne_zero (by positivity)
  -- the piece's weight
  have e1 : ρ.val (eqOne (zk.extract 0 (n - p.b)) (p.off / 2 ^ p.b)) =
      wpAt n p.off p.b (Blocks.ofList (rdL ρ zk)) := by
    have hs : (zk.extract 0 (n - p.b)).size = n - p.b := by
      rw [Array.size_extract, hn]
      omega
    have hlt : p.off / 2 ^ p.b < 2 ^ (n - p.b) := by
      rw [Nat.div_lt_iff_lt_mul hp2, ← pow_add, Nat.sub_add_cancel hbn]
      omega
    rw [eqOne_blocks ρ _ _ (by
      unfold eqIndexOK
      rw [hs, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
      exact ⟨by omega, hlt⟩), hs]
    unfold wpAt
    refine eqN_congrB _ _ _ _ _ (fun t ht => ?_) _
    unfold Blocks.ofList
    rw [rdL_extract, Nat.zero_add, exL_getD _ _ _ _ (by omega), Nat.zero_add]
  -- the rows' and the columns' weights
  have e2 : ∀ r < 2 ^ p.a, (eqTabK (exL (rdL ρ zk) (n - p.b) (n - p.b + p.a))).getD r 0 =
      Blocks.eqN p.a 0 (innAt n p.b (Blocks.ofList (rdL ρ zk))) r := by
    intro r hr
    have hl : (exL (rdL ρ zk) (n - p.b) (n - p.b + p.a)).length = p.a := by
      rw [exL_len _ _ _ (by omega)]
      omega
    rw [tabK_blocks _ _ (by rw [hl]; exact hr), hl]
    refine eqN_congrB _ _ _ _ _ (fun t ht => ?_) _
    unfold Blocks.ofList innAt
    rw [Nat.zero_add, exL_getD _ _ _ _ (by omega)]
  have e3 : ∀ i < 2 ^ k, ρ.val ((eqTab (zk.extract (n - p.b + p.a) (n - p.b + p.a + k))).getD i
      zeroE) = Blocks.eqN k p.a (innAt n p.b (Blocks.ofList (rdL ρ zk))) i := by
    intro i hi
    have hl : (exL (rdL ρ zk) (n - p.b + p.a) (n - p.b + p.a + k)).length = k := by
      rw [exL_len _ _ _ (by omega)]
      omega
    rw [rdL_getD, eqTab_val, rdL_extract, tabK_blocks _ _ (by rw [hl]; exact hi), hl]
    refine eqN_congrB _ _ _ _ _ (fun t ht => ?_) _
    unfold Blocks.ofList innAt
    rw [Nat.zero_add, exL_getD _ _ _ _ (by omega), Nat.add_assoc]
  -- the extension of the piece's keys
  have e4 : Blocks.ext p.b (pieceKeys tl μ q p) (innAt n p.b (Blocks.ofList (rdL ρ zk))) =
      ∑ i ∈ range p.Cp, Blocks.eqN k p.a (innAt n p.b (Blocks.ofList (rdL ρ zk))) i *
        ∑ r ∈ range (2 ^ p.a), Blocks.eqN p.a 0 (innAt n p.b (Blocks.ofList (rdL ρ zk))) r *
          μ (tl.ix.ZZ, p.r0 + r, q * tl.mz + i) := by
    have := pieceKeys_ext p.a k p.Cp (hpw ▸ hle) (fun r i => μ (tl.ix.ZZ, p.r0 + r, q * tl.mz + i))
      (innAt n p.b (Blocks.ofList (rdL ρ zk)))
    rw [← this, hb]
    congr 1
    funext Y
    unfold pieceKeys
    rw [hpw, hrp]
  rw [e1, e4, runSum_range]
  congr 1
  refine sum_congr rfl fun i hi => ?_
  have hi' : i < p.Cp := mem_range.1 hi
  have hjz : joinZc tl g q p = zk.extract (n - p.b + p.a) (n - p.b + p.a + k) := by
    unfold joinZc
    rw [hzz, hnn, hk]
  rw [hjz, e3 i (lt_of_lt_of_le hi' (hpw ▸ hle)), hV i hi', hrp]
  congr 1
  refine sum_congr rfl fun r hr => ?_
  rw [e2 r (mem_range.1 hr), h0]

/-- What the runs of call q read is the extension of the call's key vector at the call's point. -/
theorem kf_ext (tl : HTailF2) (g : Heard) (q : ℕ) (μ : Ent3 → K)
    (hn : (g.zk.getD q #[]).size = (tl.zOf q).call.n) (h63 : (tl.zOf q).call.n ≤ 63)
    (hP : ∀ p ∈ piecesL tl q, PieceOK tl q (tl.zOf q).call.n p)
    (hD : (piecesL tl q).Pairwise fun p p' =>
      p.off + 2 ^ p.b ≤ p'.off ∨ p'.off + 2 ^ p'.b ≤ p.off)
    (hV : ∀ p ∈ piecesL tl q, ∀ i < p.Cp, W.entry p.tree p.row (p.c0 + i) = ∑ r ∈ range p.Rp,
      (eqTabK (exL (rdL ρ (g.zk.getD q #[])) ((tl.zOf q).call.n - p.b)
        ((tl.zOf q).call.n - p.b + p.a))).getD r 0 * μ (tl.ix.ZZ, p.r0 + r, p.c0 + i)) :
    kfRun ρ W tl g q = Blocks.ext (tl.zOf q).call.n (Kp tl μ q)
      (Blocks.ofList (rdL ρ (g.zk.getD q #[]))) := by
  rw [kp_pwVec, ext_pwVec _ _ _ _ _ _ _ (fun p hp => ⟨(hP p hp).bn, (hP p hp).dvd, (hP p hp).fit⟩)
    hD, zero_mul, add_zero]
  unfold kfRun
  congr 1
  exact List.map_congr_left fun p hp => kf_piece ρ W tl g q μ p hn h63 (hP p hp) (hV p hp)

end
end Fo
