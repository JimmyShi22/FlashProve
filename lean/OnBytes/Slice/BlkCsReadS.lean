-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkCsReadS.lean: what the program reads of a later stage's tree before a code switch.

A later stage's tree holds two oracle messages: the stage's own, with 2^(h + g) main rows over the
extension field and 2^h mask rows, and the fresh mask, with 2^h mask rows. The stage's group has the
first of them as its one member. OnBytes/Slice/BlkCsRead.lean shows that the symbols which the
program reads after the fold are those of the three folded words, if the program's tables have the
entries of the format's column. This file shows that they have, for such a tree, and puts the two
together.

Main theorems.
 `stage_skips`   where the symbols of the two oracle messages begin in a leaf's column.
 `stage_cols`    the program's main table, mask table and fresh column at a listed position have
                 the entries of the column that the format cuts from the same words.
 `stage_symS`    the symbols read by a run of the reading are the long symbols of the three folded
                 words.

Not claimed. That the format can cut the written columns: that is a hypothesis, on the words that
the view shows under the tree's number.
-/
import OnBytes.Slice.BlkCsRead
import OnBytes.Slice.BlkColumns

set_option autoImplicit false

namespace OnBytes.Slice

/-- Where the symbols begin in a leaf's column of a tree with two parts, of which the first has main
rows over the extension field and the second has no main rows. -/
theorem stage_skips (tree : Tree) (sh sh' : OracleShape)
    (w1 : tree.shape.mainSymbols = ([sh, sh'].map fun s => s.mainRows * s.mainDeg).toArray)
    (w2 : tree.shape.maskSymbols = ([sh, sh'].map fun s => s.maskRows * 3).toArray)
    (m2 : sh.mainDeg = 3) (f1 : sh'.mainRows = 0) :
    mainSkip tree 0 = 0 ∧ maskSkip tree 0 = 3 * sh.mainRows ∧
      maskSkip tree 1 = 3 * (sh.mainRows + sh.maskRows) := by
  have a1 : tree.shape.mainSymbols = #[sh.mainRows * 3, 0] := by
    rw [w1]
    simp only [List.map_cons, List.map_nil, m2, f1, Nat.zero_mul]
  have a2 : tree.shape.maskSymbols = #[sh.maskRows * 3, sh'.maskRows * 3] := by
    rw [w2]
    rfl
  unfold mainSkip maskSkip TreeShape.mainWidth
  rw [a1, a2]
  refine ⟨rfl, ?_, ?_⟩
  · simp
    omega
  · simp
    omega

/-- A table that one member fills from row 0 on has the member's symbols in its first rows. -/
theorem putAt_zero (c : Array E) (b : ℕ) (hb : b < c.size) :
    putAt (some 0) c (fun _ => zeroE) b = c.getD b zeroE := by
  show (if 0 ≤ b ∧ b < 0 + c.size then c.getD (b - 0) zeroE else zeroE) = c.getD b zeroE
  rw [if_pos ⟨Nat.zero_le b, by rw [Nat.zero_add]; exact hb⟩, Nat.sub_zero]

/-- The program's main table, mask table and fresh column at a listed position have the entries of
the column that the format cuts from the same words. f: the written columns of the tree number n, as
the view shows them. col: what the format cuts from them. -/
theorem stage_cols (V : Fmt.View) (s : Sg) (old : SingleRows) (pos : Positions) (a a' : Ctx)
    (opened : Array (Array Column)) (n o : ℕ) (sh sh' : OracleShape)
    (f : ℕ → Option (List UInt64)) (col : ℕ → Fmt.M1.Col) (hv : OnView V a)
    (hrd : (Blk.readOpened (singleRowsOracles old) pos).Yields a opened a')
    (hm : old.masks = 2) (hmem : old.layout.members = #[o])
    (hmf : old.layout.mainFirst.getD 0 none = some 0)
    (hzf : old.layout.maskFirst.getD 0 none = some 0)
    (seat : Seat a [o, old.fresh] n pos.logN [sh, sh'])
    (m1 : sh.mainRows = 2 ^ (s.h + s.g)) (m2 : sh.mainDeg = 3) (m3 : sh.maskRows = 2 ^ s.h)
    (f1 : sh'.mainRows = 0) (f3 : sh'.maskRows = 2 ^ s.h) (hshow : Shows V n f)
    (hcut : ∀ x w, f x = some w → Fmt.M1.stageCol s.st 0 (2 ^ (s.h + s.g)) w = some (col x)) :
    (∀ i, i < pos.all.size → ∀ b, b < 2 ^ (s.h + s.g) →
      readE (mainAt old.layout opened i b) = vec (col (pos.all.getD i 0)).main b) ∧
    (∀ i, i < pos.all.size → ∀ b, b < 2 ^ s.h →
      readE (maskAt old.layout opened i b) = vec (col (pos.all.getD i 0)).mask b) ∧
    ∀ i, i < pos.all.size → ∀ b, b < 2 ^ s.h →
      readV (colB opened old.layout.members.size i).mask b =
        vec (col (pos.all.getD i 0)).fresh b := by
  have hids : singleRowsOracles old = [o, old.fresh].toArray := by
    unfold singleRowsOracles
    rw [hm, hmem]
    rfl
  rw [hids] at hrd
  obtain ⟨tree, cs, w1, w2, _, hwords, hparts⟩ :=
    readSeat V _ pos a a' opened n _ hv hrd (Nat.zero_lt_succ 1) seat
  obtain ⟨k0, z0, z1⟩ := stage_skips tree sh sh' w1 w2 m2 f1
  obtain ⟨x0, e0, c0⟩ := hparts 0 (Nat.zero_lt_succ 1)
  obtain ⟨x1, e1, c1⟩ := hparts 1 (Nat.lt_succ_self 1)
  have e0' : x0.shape = sh := e0
  have e1' : x1.shape = sh' := e1
  have hsz : old.layout.members.size = 1 := by
    rw [hmem]
    rfl
  have hmainAt : ∀ i b, mainAt old.layout opened i b =
      putAt (some 0) (colB opened 0 i).main (fun _ => zeroE) b := fun i b => by
    unfold mainAt
    rw [hsz, ← hmf]
    rfl
  have hmaskAt : ∀ i b, maskAt old.layout opened i b =
      putAt (some 0) (colB opened 0 i).mask (fun _ => zeroE) b := fun i b => by
    unfold maskAt
    rw [hsz, ← hzf]
    rfl
  refine ⟨fun i hi b hb => ?_, fun i hi b hb => ?_, fun i hi b hb => ?_⟩
  · have hw := hcut _ _ (hwords f hshow i hi)
    have hb0 : b < x0.shape.mainRows := by rw [e0', m1]; exact hb
    have h := stage_main x0 (mainSkip tree 0) (maskSkip tree 0) (cs.getD i #[]) s.st _ _ hw 0 b hb0
      (by rw [e0']; exact m2) (by rw [k0]) (by rw [Nat.zero_add]; exact hb)
      (by rw [Nat.zero_add]; exact hb)
    rw [Nat.zero_add] at h
    rw [hmainAt, c0 i hi, putAt_zero _ _ (by rw [(columnOf_size _ _ _ _).1]; exact hb0)]
    exact h
  · have hw := hcut _ _ (hwords f hshow i hi)
    have hb0 : b < x0.shape.maskRows := by rw [e0', m3]; exact hb
    have h := stage_mask x0 (mainSkip tree 0) (maskSkip tree 0) (cs.getD i #[]) s.st _ _ hw 0 b hb0
      (by rw [z0, m1, Nat.add_zero]) (by rw [Nat.zero_add]; exact hb)
    rw [Nat.zero_add] at h
    rw [hmaskAt, c0 i hi, putAt_zero _ _ (by rw [(columnOf_size _ _ _ _).2]; exact hb0)]
    exact h
  · have hw := hcut _ _ (hwords f hshow i hi)
    have hb1 : b < x1.shape.maskRows := by rw [e1', f3]; exact hb
    have h := stage_fresh x1 (mainSkip tree 1) (maskSkip tree 1) (cs.getD i #[]) s.st _ _ hw 0 b hb1
      (by
        rw [z1, m1, m3, Nat.add_zero]
        rfl) (by rw [Nat.zero_add]; exact hb)
    rw [Nat.zero_add] at h
    rw [hsz, c1 i hi]
    exact h

/-- The symbols read by a run of the reading, at a later stage, are at each listed position the long
symbols of the three folded words at the point that the fold's challenges give. f, col and the
hypotheses on them are those of `stage_cols`. -/
theorem stage_symS (V : Fmt.View) (s : Sg) (old : SingleRows) (pos : Positions) (a a' : Ctx)
    (y : Array E) (n o : ℕ) (sh sh' : OracleShape) (f : ℕ → Option (List UInt64))
    (col : ℕ → Fmt.M1.Col) (hv : OnView V a) (hread : (singleRowsRead old pos).Yields a y a')
    (hm : old.masks = 2) (hmem : old.layout.members = #[o])
    (hkept : old.layout.kept.getD 0 false = false)
    (hmf : old.layout.mainFirst.getD 0 none = some 0)
    (hzf : old.layout.maskFirst.getD 0 none = some 0)
    (hk : old.layout.k = s.h + s.g) (hh : old.layout.h = s.h)
    (seat : Seat a [o, old.fresh] n pos.logN [sh, sh'])
    (m1 : sh.mainRows = 2 ^ (s.h + s.g)) (m2 : sh.mainDeg = 3) (m3 : sh.maskRows = 2 ^ s.h)
    (f1 : sh'.mainRows = 0) (f3 : sh'.maskRows = 2 ^ s.h) (hshow : Shows V n f)
    (hcut : ∀ x w, f x = some w → Fmt.M1.stageCol s.st 0 (2 ^ (s.h + s.g)) w = some (col x))
    (x : s.Ps) (hx : x.val ∈ pos.all) (α : s.cMid.Aa) :
    s.cMid.T (wordMid s col (readP _ old.gamma)) x α = symS s old pos y x.val α := by
  obtain ⟨opened, hrd, hsym⟩ := singleRowsRead_inv old pos y a a' hread
  obtain ⟨h1, h2, h3⟩ := stage_cols V s old pos a a' opened n o sh sh' f col hv hrd hm hmem hmf hzf
    seat m1 m2 m3 f1 f3 hshow hcut
  refine symS_of_cols s old pos opened y col hsym hm (fun w hw => ?_) hk hh h1 h2 h3 x hx α
  have hw0 : w = 0 := by
    rw [hmem] at hw
    exact Nat.lt_one_iff.1 hw
  rw [hw0]
  exact hkept

end OnBytes.Slice

#print axioms OnBytes.Slice.stage_skips
#print axioms OnBytes.Slice.putAt_zero
#print axioms OnBytes.Slice.stage_cols
#print axioms OnBytes.Slice.stage_symS
