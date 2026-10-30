-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkCsReadG.lean: the tables that the program reads of the link's group.

The link (OnBytes/Iop/Link.lean) compares two stored tables: the prover sends a fold of each, and
one proximity test is run on the group of these two folded rows. Before the first code switch of
that test the program opens the tree that holds the two folded rows and the fresh mask, puts the
opened symbols into a main table and a mask table, and folds the tables (OnBytes/Iop/Fold.lean).
OnBytes/Slice/BlkCsRead.lean shows that the symbols so read are those of the library's three folded
words, if the program's tables have the entries of the format's column. This file shows that they
have, for the link's group: two members of R main rows each over the extension field, without mask
rows, the first from row 0 on and the second from a row f1 on, and one fresh mask row.

Main theorems.
 `group_mainTable`  the program's main table is the format's column at every row, also where no
                    member has a row.
 `group_maskTable`, `group_freshCol`  the mask table, which holds zeros; the fresh mask's symbol.
 `link_skips`       the words at which the three parts begin in a leaf's column.
 `link_symS`        together: the symbols read are the long symbols of the three folded words.
 `group_symS`       the same for a run of the program's reading on a view.

Not claimed. That the format can cut the opened columns, and how the tree is found: these enter as
hypotheses.
-/
import OnBytes.Slice.BlkCsRead
import OnBytes.Slice.BlkColumns

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb _root_.Run

/-! ## The program's tables -/

/-- A table with symbols put in from a named row on. -/
theorem putAt_some (f : ℕ) (col : Array E) (base : ℕ → E) (j : ℕ) :
    putAt (some f) col base j = if f ≤ j ∧ j < f + col.size then col.getD (j - f) zeroE
      else base j := rfl

/-- A table into which nothing is put. -/
theorem putAt_none (col : Array E) (base : ℕ → E) (j : ℕ) : putAt none col base j = base j := rfl

section
variable (mem : Fmt.M2.Mem) (hE : mem.overE = true) (hm0 : mem.masks = 0) (f1 : ℕ)
  (hst : (Fmt.M2.starts [mem, mem]).1 = [some 0, some f1]) (hf : mem.rows ≤ f1)
  (hk : f1 + mem.rows ≤ 2 ^ Fmt.M2.kOf [mem, mem]) (L : GroupLayout) (hL : L.members.size = 2)
  (hF0 : L.mainFirst.getD 0 none = some 0) (hF1 : L.mainFirst.getD 1 none = some f1)
  (hZ0 : L.maskFirst.getD 0 none = none) (hZ1 : L.maskFirst.getD 1 none = none)
  (opened : Array (Array Column)) (i : ℕ) (w : Array F) (x0 x1 x2 : Oracle)
  (z0 z1 m2 : ℕ)
  (hc0 : colB opened 0 i = Blk.columnOf x0 0 z0 w)
  (hc1 : colB opened 1 i = Blk.columnOf x1 (3 * mem.rows) z1 w)
  (hc2 : colB opened 2 i = Blk.columnOf x2 m2 (3 * (mem.rows + mem.rows)) w)
  (hr0 : x0.shape.mainRows = mem.rows) (h30 : x0.shape.mainDeg = 3)
  (hr1 : x1.shape.mainRows = mem.rows) (h31 : x1.shape.mainDeg = 3)
  (hk2 : 0 < x2.shape.maskRows) (kc : Fmt.M2.KCol)
  (h : Fmt.M2.groupCol [mem, mem] 1 w.toList = some kc)

include hE hm0 hst hf hk hL hF0 hF1 hc0 hc1 hr0 h30 hr1 h31 h in
/-- The program's main table of the link's group is the format's column, at every row, also
where no member has a row. -/
theorem group_mainTable (b : ℕ) : readE (mainAt L opened i b) = vec kc.col.main b := by
  unfold mainAt
  rw [hL]
  show readE (putAt (L.mainFirst.getD 1 none) (colB opened 1 i).main
    (putAt (L.mainFirst.getD 0 none) (colB opened 0 i).main fun _ => zeroE) b) = _
  rw [hF0, hF1, hc0, hc1, putAt_some, putAt_some, (columnOf_size x1 _ _ w).1,
    (columnOf_size x0 _ _ w).1, hr0, hr1]
  by_cases hA : f1 ≤ b ∧ b < f1 + mem.rows
  · rw [if_pos hA]
    have e := group_main1 x1 (3 * mem.rows) z1 w mem hE hm0 f1 hst hf hk kc h (b - f1)
      (by rw [hr1]; omega) h31 rfl (by omega)
    rw [Nat.add_sub_cancel' hA.1] at e
    exact e
  · rw [if_neg hA]
    by_cases hB : 0 ≤ b ∧ b < 0 + mem.rows
    · rw [if_pos hB]
      exact group_main0 x0 0 z0 w mem hE hm0 f1 hst hf hk kc h b (by rw [hr0]; omega) h30 rfl
        (by omega)
    · rw [if_neg hB, readE_zero]
      exact (groupCol_zero mem hE hm0 f1 hst _ kc h b (by omega) (by omega)).symm

include hE hm0 hst hf hk hL hZ0 hZ1 h in
/-- The program's mask table of the link's group holds zeros, as the format's column does. -/
theorem group_maskTable (b : ℕ) : readE (maskAt L opened i b) = vec kc.col.mask b := by
  unfold maskAt
  rw [hL]
  show readE (putAt (L.maskFirst.getD 1 none) (colB opened 1 i).mask
    (putAt (L.maskFirst.getD 0 none) (colB opened 0 i).mask fun _ => zeroE) b) = _
  rw [hZ0, hZ1, putAt_none, putAt_none, readE_zero]
  exact ((groupCol_inv mem hE hm0 f1 hst hf hk _ kc h).2.2.1 b).symm

include hE hm0 hst hf hk hc2 hk2 h in
/-- The fresh mask's symbol is the format's fresh entry. -/
theorem group_freshCol : readV (colB opened 2 i).mask 0 = vec kc.col.fresh 0 := by
  rw [hc2]
  exact group_fresh x2 m2 _ w mem hE hm0 f1 hst hf hk kc h hk2 rfl

end

/-! ## Where the three parts begin in a leaf's column -/

/-- The words at which the parts of the link's tree begin: two oracle messages of R main rows over
the extension field without mask rows, and the fresh mask, which has no main row. -/
theorem link_skips (tree : Tree) (sh fr : OracleShape) (R : ℕ) (hR : sh.mainRows = R)
    (h3 : sh.mainDeg = 3) (hz : sh.maskRows = 0) (hf : fr.mainRows = 0)
    (hm : tree.shape.mainSymbols = ([sh, sh, fr].map fun s => s.mainRows * s.mainDeg).toArray)
    (hk : tree.shape.maskSymbols = ([sh, sh, fr].map fun s => s.maskRows * 3).toArray) :
    mainSkip tree 0 = 0 ∧ mainSkip tree 1 = 3 * R ∧ maskSkip tree 2 = 3 * (R + R) := by
  unfold mainSkip maskSkip TreeShape.mainWidth
  rw [hm, hk]
  simp [hR, h3, hz, hf]
  omega

/-! ## The symbols read before the first code switch -/

/-- The symbols that the program reads of the link's group before the first code switch are the
long symbols of the three folded words. s: a stage without a carried mask variable. mem: a member
of the format's group. sh, fr: the shapes of a folded row's oracle message and of the fresh mask.
tree, cs: the tree that holds the three, and its columns at the listed positions. col: the format's
columns, cut from the same words. -/
theorem link_symS (s : Sg) (hs0 : s.h = 0) (old : SingleRows) (pos : Positions)
    (opened : Array (Array Column)) (y : Array E) (col : ℕ → Fmt.M1.Col)
    (hsym : singleRowsSymbols old opened pos.all.size = some y) (hm : old.masks = 2)
    (hkept : ∀ w, w < old.layout.members.size → old.layout.kept.getD w false = false)
    (hk : old.layout.k = s.h + s.g) (hh : old.layout.h = s.h)
    (hL : old.layout.members.size = 2) (mem : Fmt.M2.Mem) (hE : mem.overE = true)
    (hm0 : mem.masks = 0) (f1 : ℕ) (hst : (Fmt.M2.starts [mem, mem]).1 = [some 0, some f1])
    (hf : mem.rows ≤ f1) (hk1 : f1 + mem.rows ≤ 2 ^ Fmt.M2.kOf [mem, mem])
    (hF0 : old.layout.mainFirst.getD 0 none = some 0)
    (hF1 : old.layout.mainFirst.getD 1 none = some f1)
    (hZ0 : old.layout.maskFirst.getD 0 none = none)
    (hZ1 : old.layout.maskFirst.getD 1 none = none)
    (sh fr : OracleShape) (hR : sh.mainRows = mem.rows) (h3 : sh.mainDeg = 3)
    (hz : sh.maskRows = 0) (hfm : fr.mainRows = 0) (hfz : 0 < fr.maskRows) (tree : Tree)
    (cs : Array (Array F))
    (hmS : tree.shape.mainSymbols = ([sh, sh, fr].map fun s => s.mainRows * s.mainDeg).toArray)
    (hkS : tree.shape.maskSymbols = ([sh, sh, fr].map fun s => s.maskRows * 3).toArray)
    (hcol : ∀ p, p < 3 → ∃ x : Oracle, x.shape = [sh, sh, fr].getD p default ∧
      ∀ i, i < pos.all.size →
        colB opened p i = Blk.columnOf x (mainSkip tree p) (maskSkip tree p) (cs.getD i #[]))
    (hcut : ∀ i, i < pos.all.size → ∃ kc, Fmt.M2.groupCol [mem, mem] 1 (cs.getD i #[]).toList =
      some kc ∧ col (pos.all.getD i 0) = kc.col)
    (x : s.Ps) (hx : x.val ∈ pos.all) (α : s.cMid.Aa) :
    s.cMid.T (wordMid s col (readP _ old.gamma)) x α = symS s old pos y x.val α := by
  obtain ⟨k0, k1, k2⟩ := link_skips tree sh fr mem.rows hR h3 hz hfm hmS hkS
  obtain ⟨x0, e0, c0⟩ := hcol 0 (by decide)
  obtain ⟨x1, e1, c1⟩ := hcol 1 (by decide)
  obtain ⟨x2, e2, c2⟩ := hcol 2 (by decide)
  have e0' : x0.shape = sh := e0
  have e1' : x1.shape = sh := e1
  have e2' : x2.shape = fr := e2
  rw [k0] at c0
  rw [k1] at c1
  rw [k2] at c2
  have hone : ∀ b, b < 2 ^ s.h → b = 0 := fun b hb => by
    rw [hs0, pow_zero] at hb
    omega
  refine symS_of_cols s old pos opened y col hsym hm hkept hk hh (fun i hi b _ => ?_)
    (fun i hi b _ => ?_) (fun i hi b hb => ?_) x hx α
  · obtain ⟨kc, g1, g2⟩ := hcut i hi
    rw [g2]
    exact group_mainTable mem hE hm0 f1 hst hf hk1 old.layout hL hF0 hF1 opened i _ x0 x1 _ _
      (c0 i hi) (c1 i hi) (by rw [e0', hR]) (by rw [e0', h3]) (by rw [e1', hR]) (by rw [e1', h3])
      kc g1 b
  · obtain ⟨kc, g1, g2⟩ := hcut i hi
    rw [g2]
    exact group_maskTable mem hE hm0 f1 hst hf hk1 old.layout hL hZ0 hZ1 opened i _ kc g1 b
  · obtain ⟨kc, g1, g2⟩ := hcut i hi
    rw [g2, hL, hone b hb]
    exact group_freshCol mem hE hm0 f1 hst hf hk1 opened i _ x2 _ (c2 i hi) (by rw [e2']; exact hfz)
      kc g1

/-- The symbols read by a run of the reading before the first code switch are the long symbols
of the three folded words. V: the view. n: the number of the tree that holds the two folded rows'
oracle messages o0, o1 and the fresh mask. f: the written columns of that tree, as the view shows
them. col: what the format cuts from them. -/
theorem group_symS (V : Fmt.View) (s : Sg) (hs0 : s.h = 0) (old : SingleRows) (pos : Positions)
    (a a' : Ctx) (y : Array E) (n o0 o1 : ℕ) (sh fr : OracleShape)
    (f : ℕ → Option (List UInt64)) (col : ℕ → Fmt.M1.Col) (hv : OnView V a)
    (hread : (singleRowsRead old pos).Yields a y a') (hm : old.masks = 2)
    (hmem : old.layout.members = #[o0, o1])
    (hkept : ∀ w, w < 2 → old.layout.kept.getD w false = false)
    (hk : old.layout.k = s.h + s.g) (hh : old.layout.h = s.h)
    (mem : Fmt.M2.Mem) (hE : mem.overE = true) (hm0 : mem.masks = 0) (f1 : ℕ)
    (hst : (Fmt.M2.starts [mem, mem]).1 = [some 0, some f1]) (hf : mem.rows ≤ f1)
    (hk1 : f1 + mem.rows ≤ 2 ^ Fmt.M2.kOf [mem, mem])
    (hF0 : old.layout.mainFirst.getD 0 none = some 0)
    (hF1 : old.layout.mainFirst.getD 1 none = some f1)
    (hZ0 : old.layout.maskFirst.getD 0 none = none)
    (hZ1 : old.layout.maskFirst.getD 1 none = none)
    (seat : Seat a [o0, o1, old.fresh] n pos.logN [sh, sh, fr]) (hR : sh.mainRows = mem.rows)
    (h3 : sh.mainDeg = 3) (hz : sh.maskRows = 0) (hfm : fr.mainRows = 0) (hfz : 0 < fr.maskRows)
    (hshow : Shows V n f)
    (hcut : ∀ x w, f x = some w → ∃ kc, Fmt.M2.groupCol [mem, mem] 1 w = some kc ∧ col x = kc.col)
    (x : s.Ps) (hx : x.val ∈ pos.all) (α : s.cMid.Aa) :
    s.cMid.T (wordMid s col (readP _ old.gamma)) x α = symS s old pos y x.val α := by
  obtain ⟨opened, hrd, hsym⟩ := singleRowsRead_inv old pos y a a' hread
  have hids : singleRowsOracles old = [o0, o1, old.fresh].toArray := by
    unfold singleRowsOracles
    rw [hm, hmem]
    rfl
  have hL : old.layout.members.size = 2 := by
    rw [hmem]
    rfl
  rw [hids] at hrd
  obtain ⟨tree, cs, w1, w2, _, hwords, hparts⟩ :=
    readSeat V _ pos a a' opened n _ hv hrd (Nat.zero_lt_succ 2) seat
  exact link_symS s hs0 old pos opened y col hsym hm (fun w hw => hkept w (hL ▸ hw)) hk hh hL mem
    hE hm0 f1 hst hf hk1 hF0 hF1 hZ0 hZ1 sh fr hR h3 hz hfm hfz tree cs w1 w2 hparts
    (fun i hi => hcut _ _ (hwords f hshow i hi)) x hx α

end OnBytes.Slice

#print axioms OnBytes.Slice.group_mainTable
#print axioms OnBytes.Slice.group_maskTable
#print axioms OnBytes.Slice.group_freshCol
#print axioms OnBytes.Slice.link_skips
#print axioms OnBytes.Slice.link_symS
#print axioms OnBytes.Slice.group_symS
#print axioms OnBytes.Slice.putAt_some
#print axioms OnBytes.Slice.putAt_none
