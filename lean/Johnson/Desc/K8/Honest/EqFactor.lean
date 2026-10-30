-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/EqFactor.lean: THE PLAIN PRODUCT eqPlainF (OnBytes/Model/FormF.lean), READ,
IS THE LIBRARY's eq (Blocks.eqN, Blocks/Basic.lean) AT THE POINT's COORDINATES; AND AT A KEY OF A
PIECE IT IS THE PRODUCT OF ONE SINGLE EQUALITY WEIGHT AND TWO ENTRIES OF TABLES OF EQUALITY WEIGHTS.
Lemmas; none of the library's goals. On field words, arrays and numbers: no ledger, no block, no
prover; nothing on completeness, soundness or hiding. BY VALUES.

  `eqFactor_val`, `eqPre_val`, **`eqPlainF_val`**   the factors and products of
      Johnson/Desc/K8/Honest/EqRunPlain.lean, read; the point is read by readV
      (OnBytes/Slice/ProgField.lean)
  `eqOne_pt`, `eqTab_pt`   a single equality weight and an entry of the table, read in the same form
  `stretch_size`, `readV_stretch`, `eqN_stretch`   a stretch of a point. extract_getD
      (OnBytes/Tie/Pv/Att/ScdTop.lean), in a file that this one does not import, is the like of the
      second: its proof's lines are taken over
  **`eq_factor`**   a point of n0 + a + k coordinates; an index whose top part is hi, whose next a
      bits are r and whose last k bits are cc
  **`piece_factor`**, `piece_factor_ok`   in a piece's letters: at the key off + r * CP + cc; under
      named conditions on numbers; under Fo.PieceOK (OnBytes/Tie/Pv/Lookup/Ends/FoTailKf.lean)
By: Fo.eqOne_blocks (FoTailKf.lean) · Fo.tabK_blocks (OnBytes/Tie/Pv/Lookup/Ends/FoPieceExt.lean) ·
Fo.rdL_getD, Fo.eqTab_val, Fo.rdL_length (OnBytes/Tie/Pv/Lookup/Port/FoTwins.lean) · Fo.ofList_rdL
(OnBytes/Tie/Pv/Lookup/Ends/FoAttKeysAt.lean) · Blocks.eqN_append' (Blocks/EqN.lean).
Limits. Nothing on any weight of a ledger. The conditions on a piece's numbers are premises.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K8.Honest.EqRunPlain
import OnBytes.Tie.Pv.Lookup.Ends.FoTailKf
import OnBytes.Tie.Pv.Lookup.Ends.FoAttKeysAt
import Blocks.EqN

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model
open OnBytes.Slice (readV)

theorem eqFactor_val (z : Array E) (idx v : Nat) : Reading.gl.val (eqFactor z idx v) =
    if idx.testBit (z.size - 1 - v) then readV z v else 1 - readV z v := by
  unfold eqFactor
  split
  · rfl
  · rw [Reading.gl.sub, Reading.gl.one]
    rfl

theorem eqPre_val (z : Array E) (idx : Nat) : ∀ v : Nat, Reading.gl.val (eqPre z idx v) =
    ∏ t ∈ Finset.range v, (if idx.testBit (z.size - 1 - t) then readV z t else 1 - readV z t)
  | 0 => by
    rw [Finset.prod_range_zero]
    exact Reading.gl.one
  | v + 1 => by
    rw [Finset.prod_range_succ, ← eqPre_val z idx v, ← eqFactor_val]
    exact Reading.gl.mul _ _

/-- **The plain product, read**: the library's eq at the point's coordinates. -/
theorem eqPlainF_val (z : Array E) (idx : Nat) :
    Reading.gl.val (eqPlainF z idx) = Blocks.eqN z.size 0 (readV z) idx := by
  rw [eqPlainF_pre, eqPre_val]
  unfold Blocks.eqN
  exact Finset.prod_congr rfl fun t _ => by rw [Nat.zero_add]

/-- A single equality weight, read, where the index is in range. -/
theorem eqOne_pt (z : Array E) (c : Nat) (hok : eqIndexOK z c = true) :
    Reading.gl.val (eqOne z c) = Blocks.eqN z.size 0 (readV z) c := by
  rw [Fo.eqOne_blocks Reading.gl z c hok, Fo.ofList_rdL]

/-- An entry of the table of equality weights, read. -/
theorem eqTab_pt (z : Array E) (i : Nat) (hi : i < 2 ^ z.size) :
    Reading.gl.val ((eqTab z).getD i zeroE) = Blocks.eqN z.size 0 (readV z) i := by
  rw [Fo.rdL_getD Reading.gl, Fo.eqTab_val Reading.gl,
    Fo.tabK_blocks _ i (by rw [Fo.rdL_length]; exact hi), Fo.rdL_length, Fo.ofList_rdL]

/-- A stretch of a point. -/
theorem stretch_size (z : Array E) (s m : Nat) (h : s + m ≤ z.size) :
    (z.extract s (s + m)).size = m := by
  rw [Array.size_extract]
  omega

theorem readV_stretch (z : Array E) (s m t : Nat) (ht : t < m) :
    readV (z.extract s (s + m)) t = readV z (s + t) := by
  unfold readV
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_extract]
  split
  · rfl
  · rename_i hn
    have k : z.size ≤ s + t := by omega
    rw [Array.getElem?_eq_none k]

/-- The library's eq at a stretch is its eq from the stretch's first coordinate on. -/
theorem eqN_stretch (z : Array E) (s m : Nat) (h : s + m ≤ z.size) (c : Nat) :
    Blocks.eqN (z.extract s (s + m)).size 0 (readV (z.extract s (s + m))) c =
      Blocks.eqN m s (readV z) c := by
  rw [stretch_size z s m h]
  unfold Blocks.eqN
  exact Finset.prod_congr rfl fun t ht => by
    rw [Nat.zero_add, readV_stretch z s m t (Finset.mem_range.1 ht)]

/-- **THE FACTORING, BY VALUES**: a point of n0 + a + k coordinates; an index whose top part is hi,
whose next a bits are r and whose last k bits are cc. -/
theorem eq_factor (z : Array E) (n0 a k hi r cc : Nat) (hn : z.size = n0 + a + k) (h63 : n0 ≤ 63)
    (hhi : hi < 2 ^ n0) (hr : r < 2 ^ a) (hc : cc < 2 ^ k) :
    Reading.gl.val (eqPlainF z ((hi * 2 ^ a + r) * 2 ^ k + cc)) =
      Reading.gl.val (eqOne (z.extract 0 n0) hi) *
        Reading.gl.val ((eqTab (z.extract n0 (n0 + a))).getD r zeroE) *
        Reading.gl.val ((eqTab (z.extract (n0 + a) (n0 + a + k))).getD cc zeroE) := by
  have s0 : (z.extract 0 n0).size = n0 := by
    have e := stretch_size z 0 n0 (by omega)
    rwa [Nat.zero_add] at e
  have s1 := stretch_size z n0 a (by omega)
  have s2 := stretch_size z (n0 + a) k (by omega)
  have e0 : Blocks.eqN (z.extract 0 n0).size 0 (readV (z.extract 0 n0)) hi =
      Blocks.eqN n0 0 (readV z) hi := by
    have e := eqN_stretch z 0 n0 (by omega) hi
    rwa [Nat.zero_add] at e
  have ok0 : eqIndexOK (z.extract 0 n0) hi = true := by
    unfold eqIndexOK
    rw [s0, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
    exact ⟨h63, hhi⟩
  rw [eqPlainF_val, hn, Blocks.eqN_append' (n0 + a) k 0 (readV z) _ hc,
    Blocks.eqN_append' n0 a 0 (readV z) hi hr, eqOne_pt _ _ ok0, e0,
    eqTab_pt _ r (by rw [s1]; exact hr), eqN_stretch z n0 a (by omega) r,
    eqTab_pt _ cc (by rw [s2]; exact hc), eqN_stretch z (n0 + a) k (by omega) cc,
    Nat.zero_add, Nat.zero_add]

/-- **THE FACTORING IN A PIECE's LETTERS**: n: the call's number of coordinates; the piece's first
key off is a multiple of 2^b, b = a + kc, its padded number of columns CP is 2^kc. -/
theorem piece_factor (z : Array E) (n a b kc CP off r cc : Nat) (hz : z.size = n) (hbn : b ≤ n)
    (hb : b = a + kc) (hCP : CP = 2 ^ kc) (hoff : 2 ^ b ∣ off) (h63 : n - b ≤ 63)
    (hhi : off / 2 ^ b < 2 ^ (n - b)) (hr : r < 2 ^ a) (hc : cc < CP) :
    Reading.gl.val (eqPlainF z (off + r * CP + cc)) =
      Reading.gl.val (eqOne (z.extract 0 (n - b)) (off / 2 ^ b)) *
        Reading.gl.val ((eqTab (z.extract (n - b) (n - b + a))).getD r zeroE) *
        Reading.gl.val ((eqTab (z.extract (n - b + a) (n - b + a + kc))).getD cc zeroE) := by
  have e : off + r * CP + cc = (off / 2 ^ b * 2 ^ a + r) * 2 ^ kc + cc := by
    have h1 : off = off / 2 ^ b * 2 ^ b := (Nat.div_mul_cancel hoff).symm
    have h2 : (2 : Nat) ^ b = 2 ^ a * 2 ^ kc := by rw [hb, pow_add]
    rw [hCP, Nat.add_mul, Nat.mul_assoc, ← h2, ← h1]
  rw [e]
  exact eq_factor z (n - b) a kc _ r cc (by omega) h63 hhi hr (hCP ▸ hc)

/-- **THE SAME UNDER THE LIBRARY's OWN CONDITION ON A PIECE's PUBLIC NUMBERS** (Fo.PieceOK,
OnBytes/Tie/Pv/Lookup/Ends/FoTailKf.lean). -/
theorem piece_factor_ok {tl : HTailF2} {q n : Nat} {p : OnBytes.Model.Piece}
    (h : Fo.PieceOK tl q n p) (z : Array E) (hz : z.size = n) (h63 : n - p.b ≤ 63) (r cc : Nat)
    (hr : r < p.Rp) (hc : cc < p.CP) :
    Reading.gl.val (eqPlainF z (p.off + r * p.CP + cc)) =
      Reading.gl.val (eqOne (z.extract 0 (n - p.b)) (p.off / 2 ^ p.b)) *
        Reading.gl.val ((eqTab (z.extract (n - p.b) (n - p.b + p.a))).getD r zeroE) *
        Reading.gl.val ((eqTab (z.extract (n - p.b + p.a)
          (n - p.b + p.a + clog2 p.CP))).getD cc zeroE) := by
  have hp2 : 0 < 2 ^ p.b := Nat.two_pow_pos _
  have hlt : p.off / 2 ^ p.b < 2 ^ (n - p.b) := by
    rw [Nat.div_lt_iff_lt_mul hp2, ← pow_add, Nat.sub_add_cancel h.bn]
    have k := h.fit
    omega
  exact piece_factor z n p.a p.b (clog2 p.CP) p.CP p.off r cc hz h.bn h.b h.pw h.dvd h63 hlt
    (h.rp ▸ hr) hc

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.eqFactor_val
#print axioms VerifiableInference.Desc.First.K8.Honest.eqPre_val
#print axioms VerifiableInference.Desc.First.K8.Honest.eqPlainF_val
#print axioms VerifiableInference.Desc.First.K8.Honest.eqOne_pt
#print axioms VerifiableInference.Desc.First.K8.Honest.eqTab_pt
#print axioms VerifiableInference.Desc.First.K8.Honest.stretch_size
#print axioms VerifiableInference.Desc.First.K8.Honest.readV_stretch
#print axioms VerifiableInference.Desc.First.K8.Honest.eqN_stretch
#print axioms VerifiableInference.Desc.First.K8.Honest.eq_factor
#print axioms VerifiableInference.Desc.First.K8.Honest.piece_factor
#print axioms VerifiableInference.Desc.First.K8.Honest.piece_factor_ok
