-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/CubeAt.lean: THE ARRANGED GROUP's MESSAGE, READ BACK OFF THE CUBE AT A
MEMBER's BLOCK, IS THAT MEMBER's OWN ROWS: so the premise `LaidOn` of EndSays.lean (beside this
file) follows from public ties between the typed group and a statement's layout, and one sentence on
the words. Definitions, statements and proofs. General in the typed group.

  `rowM R u r x`, `rowZ R u r x`: a member's main row and mask row AS THE GROUP's MESSAGE u HOLDS
    THEM BEHIND THE GROUP's VIEW: `(R.Sh.flat.up u).1` at (row r, place x).
  `up_main_some`, `up_main_none`, `up_kept`, `up_mask_some`, `up_mask_none`: what the arrangement
    `R.Sh.rho.up u` holds at a corner: the row without a slot whose corner has that number, or 0; in
    a slot, at every corner, the kept row; the like for masks.
  `tabK_main`, `tabK_mask`: the tables of a vector (`tabK`, EndSays.lean) at (row n, place x).
  `CubeFits R T L no`: PUBLIC TIES: the layout's h is the stage's, and the two codes' message
    lengths are 2 to the layout's exponents; every member of the layout is a member of the typed
    group (no: its number in the statement); a folded member's block begins at the typed corner,
    none of its rows has a slot, the block lies on the cube, its rows beyond the typed rows are
    free; the like for masks. `NamesFit R N T L no`: the slots' names: the member's number; (row,
    place) as an index of that member's own table; no row in two slots; every row of a kept member
    has a slot.
  `cube_main_at`, `cube_mask_at`, `cube_kept_at`: at a member's block (at a kept member: in the kept
    part) the tables of the arranged message hold `rowM` | `rowZ` of that member, and 0 on the rows
    beyond.
  `WordsAre R T no u m`: the words at the members are these rows, 0 beyond: asked below the tables'
    sizes alone. `laidOn_of_cube`: `R.Good`, hLk (the layout's k is the stage's number of row
    variables: handed in beside, not a field of `CubeFits`: at K10's closing it is drawn from the
    block's own yes), `LayFacts T G L` (Johnson/Desc/Means/Layout.lean: what every layout of a
    statement's has: it gives that a member's places are the layout's), `CubeFits`, `NamesFit`,
    `WordsAre` give `LaidOn T L m (tabK N (R.Sh.rho.up u).1)`.
Limits. (1) `WordsAre` SPEAKS OF `rowM` AND `rowZ`: ROWS BEHIND THE GROUP's VIEW (gather after
`R.view`), NOT OF A MEMBER's OWN MESSAGE's ENTRIES: the step from `rowM R (R.G.msg μ, r) ⟨a, j⟩ x`
to μ's entry at member a is `R.view a`'s text at the typed group in hand: not here. The pins need
that step too. (2) `CubeFits` and `NamesFit` are shown of no typed group, no statement and no layout
here. "The block's rows beyond the typed rows are free" holds where the typed corners leave each
member a whole block of 2 to its row bits, as the program's layout does: at the written groups the
corners are the program's own layout's of the WRITTEN shapes (LayoutDrawn.lean, CornersKept.lean):
that a record's statement has these shapes is a table's promise. (3) `WordsAre` is shown of no
words: it is what an extractor that lays the decoded messages is to give. TWO THINGS RIDE IN IT: "0
beyond the typed rows" is a demand on the READER of the witness (what it returns on a table's rows
beyond the real ones); and u holds the randomness r beside the message: if a row behind the view
hangs on r, `WordsAre` at one r pins the words to that r: WHICH r IS LAID IS THE EXTRACTOR's CHOICE.
(4) Nothing else is said on the randomness (the second component of `up`). Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.EndSays

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Slice OnBytes.Means Cb Johnson.Top.H
open H2K.ClaimSays (tabBack tabBack_at)

variable {S : Sig GE} (R : RowsK S) (N : SlotNames R)

/-- A member's main row, as the group's message holds it: row r, place x. -/
noncomputable def rowM (u : (R.G.C.J → GE) × (R.G.C.Q → GE)) (r : Σ a : R.G.A, Fin (R.nM a))
    (x : R.s.cM.J) : GE := (R.Sh.flat.up u).1 (.inl (r, x))

/-- A member's mask row. -/
noncomputable def rowZ (u : (R.G.C.J → GE) × (R.G.C.Q → GE)) (r : Σ a : R.G.A, Fin (R.nZ a))
    (x : R.s.cZ.J) : GE := (R.Sh.flat.up u).1 (.inr (r, x))

/-- **The arranged message on the cube's part without a slot**: at the corner b stands the row
without a slot whose corner has b's number. -/
theorem up_main_some (u : (R.G.C.J → GE) × (R.G.C.Q → GE)) (b : Fin (R.s.h + R.s.g) → Bool)
    (x : R.s.cM.J) (r : Σ a : R.G.A, Fin (R.nM a)) (h : R.rowAt (Sz.rowNo b) = some r) :
    (R.Sh.rho.up u).1 (.inl (b, (none, x))) = rowM R u r x := by
  have hs : R.Sh.am.src (b, none) = some r := h
  show R.Sh.am.spread _ ((b, none), x) = _
  simp only [Arr.spread, hs]
  rfl

/-- 0 where there is none. -/
theorem up_main_none (u : (R.G.C.J → GE) × (R.G.C.Q → GE)) (b : Fin (R.s.h + R.s.g) → Bool)
    (x : R.s.cM.J) (h : R.rowAt (Sz.rowNo b) = none) :
    (R.Sh.rho.up u).1 (.inl (b, (none, x))) = 0 := by
  have hs : R.Sh.am.src (b, none) = none := h
  show R.Sh.am.spread _ ((b, none), x) = _
  simp only [Arr.spread, hs]

/-- **In a slot**: at every corner a copy of the kept row. -/
theorem up_kept (u : (R.G.C.J → GE) × (R.G.C.Q → GE)) (b : Fin (R.s.h + R.s.g) → Bool) (q : R.Kp)
    (x : R.s.cM.J) : (R.Sh.rho.up u).1 (.inl (b, (some q, x))) = rowM R u (R.kept q) x := rfl

/-- **On the mask's cube.** -/
theorem up_mask_some (u : (R.G.C.J → GE) × (R.G.C.Q → GE)) (b : Fin R.s.h → Bool) (x : R.s.cZ.J)
    (r : Σ a : R.G.A, Fin (R.nZ a)) (h : R.Sh.ordZ b = some r) :
    (R.Sh.rho.up u).1 (.inr (b, x)) = rowZ R u r x := by
  have hs : R.Sh.az.src b = some r := h
  show R.Sh.az.spread _ (b, x) = _
  simp only [Arr.spread, hs]
  rfl

theorem up_mask_none (u : (R.G.C.J → GE) × (R.G.C.Q → GE)) (b : Fin R.s.h → Bool) (x : R.s.cZ.J)
    (h : R.Sh.ordZ b = none) : (R.Sh.rho.up u).1 (.inr (b, x)) = 0 := by
  have hs : R.Sh.az.src b = none := h
  show R.Sh.az.spread _ (b, x) = _
  simp only [Arr.spread, hs]

/-- The main table of a vector's tables at (row n, place x). -/
theorem tabK_main (v : R.Sh.Cin.J → GE) (n x : ℕ) (hn : n < 2 ^ (R.s.h + R.s.g))
    (hx : x < R.s.C.l) :
    (tabK N v).main (n + x * 2 ^ (R.s.h + R.s.g)) =
      v (.inl (vtx (R.s.h + R.s.g) n, (none, ⟨x, hx⟩))) := by
  have e := tabBack_at (R.s.h + R.s.g) R.s.C.l (fun y => v (.inl (y.1, (none, y.2))))
    (vtx (R.s.h + R.s.g) n, ⟨x, hx⟩)
  have e2 : Sz.rowNo (vtx (R.s.h + R.s.g) n) = n :=
    (rowNo_testBit _ _).trans (Nat.mod_eq_of_lt hn)
  rw [e2, Nat.mul_comm] at e
  exact e

/-- The mask table likewise. -/
theorem tabK_mask (v : R.Sh.Cin.J → GE) (n x : ℕ) (hn : n < 2 ^ R.s.h) (hx : x < R.s.Z.l) :
    (tabK N v).mask (n + x * 2 ^ R.s.h) = v (.inr (vtx R.s.h n, ⟨x, hx⟩)) := by
  have e := tabBack_at R.s.h R.s.Z.l (fun y => v (.inr y)) (vtx R.s.h n, ⟨x, hx⟩)
  have e2 : Sz.rowNo (vtx R.s.h n) = n := (rowNo_testBit _ _).trans (Nat.mod_eq_of_lt hn)
  rw [e2, Nat.mul_comm] at e
  exact e

/-- **The typed group's cube fits a statement's layout**: public ties alone. no: the number, in the
statement, of a member of the typed group. -/
structure CubeFits (T : Statement) (L : GroupLayout) (no : R.G.A → ℕ) : Prop where
  h : L.h = R.s.h
  /-- the two codes' message lengths are 2 to the layout's exponents -/
  el : 2 ^ L.logEll = R.s.C.l
  ez : 2 ^ L.logEllZk = R.s.Z.l
  /-- every member of the layout is a member of the typed group -/
  onto : ∀ o i, L.find o = some i → ∃ a, no a = o
  /-- a member whose main rows are folded: its block begins at the typed corner; none of its rows
  has a slot; the block lies on the cube; the block's rows beyond the typed rows are free -/
  main : ∀ a i first, L.find (no a) = some i → L.kept.getD i false = false →
    L.mainFirst.getD i none = some first →
      R.oM a = first ∧ (∀ j, R.slot ⟨a, j⟩ = none) ∧
      first + 2 ^ T.rowBits (no a) .main ≤ 2 ^ (R.s.h + R.s.g) ∧
      (∀ j, R.nM a ≤ j → j < 2 ^ T.rowBits (no a) .main → R.rowAt (first + j) = none)
  /-- the like for the mask rows -/
  mask : ∀ a i first, L.find (no a) = some i → L.maskFirst.getD i none = some first →
      R.oZ a = first ∧ first + 2 ^ T.rowBits (no a) .mask ≤ 2 ^ R.s.h ∧
      (∀ j, R.nZ a ≤ j → j < 2 ^ T.rowBits (no a) .mask →
        R.Sh.ordZ (vtx R.s.h (first + j)) = none)

/-- An index below a table's size: its row and its place. -/
theorem idx_split {T : Statement} {o : ℕ} {part : Part} {idx l : ℕ}
    (h : idx < tableSize T o part) (hl : 2 ^ T.placeBits o part = l) :
    idx % 2 ^ T.rowBits o part < 2 ^ T.rowBits o part ∧ idx / 2 ^ T.rowBits o part < l := by
  refine ⟨Nat.mod_lt _ (Nat.two_pow_pos _), ?_⟩
  unfold tableSize at h
  split at h
  · unfold Statement.tableBits at h
    rw [pow_add] at h
    rw [← hl]
    exact Nat.div_lt_of_lt_mul h
  · exact absurd h (Nat.not_lt_zero _)

/-- An index below a table's size: the table is there. -/
theorem has_of_idx {T : Statement} {o : ℕ} {part : Part} {idx : ℕ}
    (h : idx < tableSize T o part) : T.has o part = true := by
  unfold tableSize at h
  split at h
  · assumption
  · exact absurd h (Nat.not_lt_zero _)

/-- **The main table of the arranged message's tables, at a folded member's block, holds that
member's own rows**, and 0 on the block's rows beyond them. -/
theorem cube_main_at (hg : R.Good) {T : Statement} {L : GroupLayout} {no : R.G.A → ℕ}
    (hLk : L.k = R.s.h + R.s.g) (C : CubeFits R T L no) (u : (R.G.C.J → GE) × (R.G.C.Q → GE))
    (a : R.G.A) (i first : ℕ)
    (hf : L.find (no a) = some i) (hk : L.kept.getD i false = false)
    (hm : L.mainFirst.getD i none = some first) (idx : ℕ)
    (hx : idx / 2 ^ T.rowBits (no a) .main < R.s.C.l) :
    (tabK N (R.Sh.rho.up u).1).main (groupIndex idx (T.rowBits (no a) .main) first L.k) =
      if hj : idx % 2 ^ T.rowBits (no a) .main < R.nM a then
        rowM R u ⟨a, ⟨idx % 2 ^ T.rowBits (no a) .main, hj⟩⟩ ⟨idx / 2 ^ T.rowBits (no a) .main, hx⟩
      else 0 := by
  obtain ⟨e1, e2, e3, e4⟩ := C.main a i first hf hk hm
  have hj' : idx % 2 ^ T.rowBits (no a) .main < 2 ^ T.rowBits (no a) .main :=
    Nat.mod_lt _ (Nat.two_pow_pos _)
  have hn : first + idx % 2 ^ T.rowBits (no a) .main < 2 ^ (R.s.h + R.s.g) := by omega
  unfold groupIndex
  rw [hLk, tabK_main R N _ _ _ hn hx]
  have e6 : Sz.rowNo (vtx (R.s.h + R.s.g) (first + idx % 2 ^ T.rowBits (no a) .main)) =
      first + idx % 2 ^ T.rowBits (no a) .main :=
    (rowNo_testBit _ _).trans (Nat.mod_eq_of_lt hn)
  by_cases hj : idx % 2 ^ T.rowBits (no a) .main < R.nM a
  · rw [dif_pos hj]
    refine up_main_some R u _ _ _ ?_
    rw [e6]
    have e7 : first + idx % 2 ^ T.rowBits (no a) .main =
        R.atM ⟨a, ⟨idx % 2 ^ T.rowBits (no a) .main, hj⟩⟩ := by
      show _ = R.oM a + _
      rw [e1]
    rw [e7]
    exact R.rowAt_atM hg _ (e2 _)
  · rw [dif_neg hj]
    refine up_main_none R u _ _ ?_
    rw [e6]
    exact e4 _ (Nat.le_of_not_lt hj) hj'

open Classical in
/-- The mask row at the corner with the number of a mask row is that row. -/
theorem ordZ_atZ (hg : R.Good) (r : Σ a : R.G.A, Fin (R.nZ a)) :
    R.Sh.ordZ (vtx R.s.h (R.atZ r)) = some r := by
  have e : Sz.rowNo (vtx R.s.h (R.atZ r)) = R.atZ r :=
    (rowNo_testBit _ _).trans (Nat.mod_eq_of_lt (hg.fitZ r))
  have hex : ∃ r', R.atZ r' = Sz.rowNo (vtx R.s.h (R.atZ r)) := ⟨r, e.symm⟩
  show (if h : ∃ r', R.atZ r' = Sz.rowNo (vtx R.s.h (R.atZ r)) then some h.choose else none) = _
  rw [dif_pos hex]
  exact congrArg some (hg.injZ (hex.choose_spec.trans e))

/-- **The mask table likewise.** -/
theorem cube_mask_at (hg : R.Good) {T : Statement} {L : GroupLayout} {no : R.G.A → ℕ}
    (C : CubeFits R T L no) (u : (R.G.C.J → GE) × (R.G.C.Q → GE)) (a : R.G.A) (i first : ℕ)
    (hf : L.find (no a) = some i) (hm : L.maskFirst.getD i none = some first) (idx : ℕ)
    (hx : idx / 2 ^ T.rowBits (no a) .mask < R.s.Z.l) :
    (tabK N (R.Sh.rho.up u).1).mask (groupIndex idx (T.rowBits (no a) .mask) first L.h) =
      if hj : idx % 2 ^ T.rowBits (no a) .mask < R.nZ a then
        rowZ R u ⟨a, ⟨idx % 2 ^ T.rowBits (no a) .mask, hj⟩⟩ ⟨idx / 2 ^ T.rowBits (no a) .mask, hx⟩
      else 0 := by
  obtain ⟨e1, e3, e4⟩ := C.mask a i first hf hm
  have hj' : idx % 2 ^ T.rowBits (no a) .mask < 2 ^ T.rowBits (no a) .mask :=
    Nat.mod_lt _ (Nat.two_pow_pos _)
  have hn : first + idx % 2 ^ T.rowBits (no a) .mask < 2 ^ R.s.h := by omega
  unfold groupIndex
  rw [C.h, tabK_mask R N _ _ _ hn hx]
  by_cases hj : idx % 2 ^ T.rowBits (no a) .mask < R.nZ a
  · rw [dif_pos hj]
    refine up_mask_some R u _ _ _ ?_
    have e7 : first + idx % 2 ^ T.rowBits (no a) .mask =
        R.atZ ⟨a, ⟨idx % 2 ^ T.rowBits (no a) .mask, hj⟩⟩ := by
      show _ = R.oZ a + _
      rw [e1]
    rw [e7]
    exact ordZ_atZ R hg _
  · rw [dif_neg hj]
    exact up_mask_none R u _ _ (e4 _ (Nat.le_of_not_lt hj) hj')

/-- **The slots' names fit a statement**: the slot q bears the number of the member whose row it
keeps; the place x of that row bears the index (row, place) of that member's own main table; no row
is kept in two slots; and every real row of a kept member has a slot. -/
structure NamesFit (T : Statement) (L : GroupLayout) (no : R.G.A → ℕ) : Prop where
  inj : Function.Injective no
  orc : ∀ q, N.orc q = no (R.kept q).1
  idx : ∀ q x, N.idx q x = (R.kept q).2.val + x.val * 2 ^ T.rowBits (N.orc q) .main
  one : Function.Injective R.kept
  all : ∀ a i, L.find (no a) = some i → L.kept.getD i false = true →
    (∀ j : Fin (R.nM a), ∃ q, R.kept q = ⟨a, j⟩) ∧ R.nM a ≤ 2 ^ T.rowBits (no a) .main

/-- **The kept part of the arranged message's tables, at a kept member, holds that member's own
rows**, and 0 on the rows beyond them. -/
theorem cube_kept_at {T : Statement} {L : GroupLayout} {no : R.G.A → ℕ}
    (F : NamesFit R N T L no) (u : (R.G.C.J → GE) × (R.G.C.Q → GE)) (a : R.G.A) (i : ℕ)
    (hf : L.find (no a) = some i) (hk : L.kept.getD i false = true) (idx : ℕ)
    (hx : idx / 2 ^ T.rowBits (no a) .main < R.s.C.l) :
    (tabK N (R.Sh.rho.up u).1).kept (no a) idx =
      if hj : idx % 2 ^ T.rowBits (no a) .main < R.nM a then
        rowM R u ⟨a, ⟨idx % 2 ^ T.rowBits (no a) .main, hj⟩⟩ ⟨idx / 2 ^ T.rowBits (no a) .main, hx⟩
      else 0 := by
  obtain ⟨hall, hle⟩ := F.all a i hf hk
  -- what a name says of (q, x)
  have key : ∀ q (x : R.s.cM.J), (N.orc q = no a ∧ N.idx q x = idx) ↔
      ((R.kept q).1 = a ∧ (R.kept q).2.val = idx % 2 ^ T.rowBits (no a) .main ∧
        x.val = idx / 2 ^ T.rowBits (no a) .main) := by
    intro q x
    constructor
    · rintro ⟨h1, h2⟩
      have ha : (R.kept q).1 = a := F.inj ((F.orc q).symm.trans h1)
      have hlt : (R.kept q).2.val < 2 ^ T.rowBits (no a) .main := by
        have h0 := (R.kept q).2.isLt
        have h3 : R.nM (R.kept q).1 = R.nM a := congrArg R.nM ha
        omega
      rw [F.idx q x, h1] at h2
      refine ⟨ha, ?_, ?_⟩
      · rw [← h2, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt]
      · rw [← h2, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hlt,
          Nat.zero_add]
    · rintro ⟨ha, h1, h2⟩
      have ho : N.orc q = no a := by rw [F.orc q, ha]
      refine ⟨ho, ?_⟩
      rw [F.idx q x, ho, h1, h2, Nat.mul_comm]
      exact Nat.mod_add_div _ _
  show (∑ q : R.Kp, ∑ x : R.s.cM.J, if N.orc q = no a ∧ N.idx q x = idx then
    (R.Sh.rho.up u).1 (.inl (fun _ => false, (some q, x))) else 0) = _
  by_cases hj : idx % 2 ^ T.rowBits (no a) .main < R.nM a
  · rw [dif_pos hj]
    obtain ⟨q0, hq0⟩ := hall ⟨_, hj⟩
    rw [Finset.sum_eq_single q0, Finset.sum_eq_single ⟨idx / 2 ^ T.rowBits (no a) .main, hx⟩]
    · rw [if_pos ((key q0 _).2 ⟨by rw [hq0], by rw [hq0], rfl⟩), up_kept, hq0]
    · intro x _ hne
      rw [if_neg fun c => hne (Fin.ext ((key q0 x).1 c).2.2)]
    · intro h
      exact absurd (Finset.mem_univ _) h
    · intro q _ hne
      refine Finset.sum_eq_zero fun x _ => ?_
      rw [if_neg fun c => hne (F.one ?_)]
      obtain ⟨c1, c2, -⟩ := (key q x).1 c
      rw [hq0]
      exact Sigma.ext c1 (by subst c1; exact heq_of_eq (Fin.ext c2))
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [dif_neg hj]
    refine Finset.sum_eq_zero fun q _ => Finset.sum_eq_zero fun x _ => ?_
    rw [if_neg fun c => hj ?_]
    obtain ⟨c1, c2, -⟩ := (key q x).1 c
    rw [← c2]
    have h0 := (R.kept q).2.isLt
    have h3 : R.nM (R.kept q).1 = R.nM a := congrArg R.nM c1
    omega

/-- **The words at the typed group's members are these members' own rows**, as the group's message u
holds them, and 0 on the rows beyond: row := index % 2^(row bits), place := index / 2^(row bits).
Asked below the tables' sizes alone: of a table that is not there nothing is asked. -/
structure WordsAre (T : Statement) (no : R.G.A → ℕ) (u : (R.G.C.J → GE) × (R.G.C.Q → GE))
    (m : Words GE) : Prop where
  main : ∀ a idx, idx < tableSize T (no a) .main →
    ∀ hx : idx / 2 ^ T.rowBits (no a) .main < R.s.C.l, m (no a) .main idx =
      if hj : idx % 2 ^ T.rowBits (no a) .main < R.nM a then
        rowM R u ⟨a, ⟨idx % 2 ^ T.rowBits (no a) .main, hj⟩⟩ ⟨idx / 2 ^ T.rowBits (no a) .main, hx⟩
      else 0
  mask : ∀ a idx, idx < tableSize T (no a) .mask →
    ∀ hx : idx / 2 ^ T.rowBits (no a) .mask < R.s.Z.l, m (no a) .mask idx =
      if hj : idx % 2 ^ T.rowBits (no a) .mask < R.nZ a then
        rowZ R u ⟨a, ⟨idx % 2 ^ T.rowBits (no a) .mask, hj⟩⟩ ⟨idx / 2 ^ T.rowBits (no a) .mask, hx⟩
      else 0

/-- **THE ARRANGED MESSAGE's TABLES HOLD THE WORDS ON THE MEMBERS' BLOCKS**: under the public ties
(`CubeFits`, `NamesFit`; Y: the facts that every layout of a statement's has), for words that are
the members' own rows (`WordsAre`). -/
theorem laidOn_of_cube (hg : R.Good) {T : Statement} {G : Group} {L : GroupLayout}
    {no : R.G.A → ℕ} (Y : LayFacts T G L) (hLk : L.k = R.s.h + R.s.g) (C : CubeFits R T L no)
    (F : NamesFit R N T L no)
    (u : (R.G.C.J → GE) × (R.G.C.Q → GE)) (m : Words GE) (hW : WordsAre R T no u m) :
    LaidOn T L m (tabK N (R.Sh.rho.up u).1) where
  main_at := by
    intro o i first hf hk hm idx hidx
    obtain ⟨a, rfl⟩ := C.onto o i hf
    have hp : 2 ^ T.placeBits (no a) .main = R.s.C.l := by
      rw [Y.main_places _ (Y.mem_of_find _ _ hf) (has_of_idx hidx), C.el]
    have hx := (idx_split hidx hp).2
    rw [cube_main_at R N hg hLk C u a i first hf hk hm idx hx, hW.main a idx hidx hx]
  mask_at := by
    intro o i first hf hm idx hidx
    obtain ⟨a, rfl⟩ := C.onto o i hf
    have hp : 2 ^ T.placeBits (no a) .mask = R.s.Z.l := by
      rw [Y.mask_places _ (Y.mem_of_find _ _ hf) (has_of_idx hidx), C.ez]
    have hx := (idx_split hidx hp).2
    rw [cube_mask_at R N hg C u a i first hf hm idx hx, hW.mask a idx hidx hx]
  kept_at := by
    intro o i hf hk idx hidx
    obtain ⟨a, rfl⟩ := C.onto o i hf
    have hp : 2 ^ T.placeBits (no a) .main = R.s.C.l := by
      rw [Y.main_places _ (Y.mem_of_find _ _ hf) (has_of_idx hidx), C.el]
    have hx := (idx_split hidx hp).2
    rw [cube_kept_at R N F u a i hf hk idx hx, hW.main a idx hidx hx]

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.laidOn_of_cube
#print axioms VerifiableInference.Desc.First.Close.cube_mask_at
#print axioms VerifiableInference.Desc.First.Close.cube_kept_at
#print axioms VerifiableInference.Desc.First.Close.cube_main_at
