-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/CubeOfShapes.lean: THE TYPED GROUP's CUBE FITS THE LAYOUT THAT A
STATEMENT GIVES A GROUP WHICH HOLDS A WRITTEN LIST's MEMBERS: `CubeFits` (CubeAt.lean, beside this
file) FROM `ShapesAre` (LayoutOfShapes.lean). Definitions, statements and proofs.

Why. That the arranged group's message, read back off the cube at a member's block, is that member's
own rows (`laidOn_of_cube`, CubeAt.lean) asks public ties between the typed group and the layout:
`CubeFits`. It was shown of no typed group and no statement. Here it follows, at the typed group
whose corners are the program's own `layBlocks`' for the written shapes, from one sentence on the
statement and the group, with no new evaluation: the laws of `layBlocks` (`Laid`,
LayBlocks.lean: a block ends inside the rows taken; two blocks lie apart) give "the block lies on
the cube" and "the block's rows beyond the typed rows are free".
  `rising_pos`, `members_rising`, `members_nodup`, `mem_members`, `pos_get`, `pos_lt`: a member
    stands among the members at the place `posOf` (Drawn/Def.lean).
  `idxOf_lt`, `find_lt`, `find_pos`, `find_onto`, `flag_pos`: the place that a layout finds for a
    member's number is that place, WHERE THE NUMBERING PARTS THE MEMBERS (hinj); every member of the
    layout is a member of the list; the flag there is the member's.
  `groupLayK cs lo s e kb hM hZ`: the typed group of a list's members at `layBlocks`' corners for
    the flags kb, the members with the flag kept: general in the codes and the stage. `block_bits`,
    `rows_le_bits`.
  `cubeFits_of_shapes`: T.groups[g]? = some G; T.layout g = some L; `ShapesAre T G lo kb no`;
    `AgreesWith lo kb L`; hinj; L.k = s.h + s.g; s.h = 0; the two codes' message lengths are 2 to
    the layout's two exponents: THEN `CubeFits (groupLayK ..) T L fun a => no a.1`.
  `shapesAre_stOf`: `ShapesAre` HAS A MEMBER: the statement made of the list (`stOf lo kb`), its one
    group, each message under its own number.
  `front_h`: every group in front, at both sizes, has h = 0: by evaluation. `cubeFits_full`,
    `cubeFits_small`: at the real groups `groupFullLayK`, `groupSmallLayK` (CornersKept.lean),
    whichever members are kept, under gs.k = `kLay lo kb`: there is the layout L, in front of the
    beginning of the group's test and behind it, with L.k the stage's number of row variables; and
    `CubeFits`, IF the two codes' message lengths are 2 to L's two exponents.
Limits. `ShapesAre` and hinj are shown of no verifier's state (of the made statement alone). THE TWO
EQUATIONS ON THE CODES' LENGTHS STAY PREMISES: they read the statement's table of codes and the
group's two code numbers. gs.k = `kLay lo kb` stays a premise. `NamesFit` and `WordsAre`, the two
other premises of `laidOn_of_cube`, are not touched. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.LayoutOfShapes
import Johnson.Desc.First.Close.Law.CubeAt
import Johnson.Desc.First.Close.Law.CornersKept

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Slice OnBytes.Params Johnson.Pack Johnson.Top.H Johnson.G
open OnBytes.LayLaw (laySizes layout_eq Laid layBlocks_laid laySizes_some find_getD getD_some
  layout_blocksOk)

/-! ### Where a member stands among the members -/

/-- In a list in rising order a member stands behind just the members below it. -/
theorem rising_pos {n : ℕ} : ∀ (l : List (Fin n)), l.Pairwise (· < ·) → ∀ x ∈ l,
    l[(l.filter fun j => decide (j < x)).length]? = some x
  | [], _, _, h => absurd h List.not_mem_nil
  | a :: l, hp, x, hx => by
    obtain ⟨h1, h2⟩ := List.pairwise_cons.1 hp
    rcases List.mem_cons.1 hx with rfl | hx'
    · have e : ((x :: l).filter fun j => decide (j < x)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro y hy
        rcases List.mem_cons.1 hy with rfl | hy'
        · simp
        · simpa using le_of_lt (h1 y hy')
      rw [e]
      rfl
    · have ha : decide (a < x) = true := decide_eq_true (h1 x hx')
      have e : ((a :: l).filter fun j => decide (j < x)) = a :: l.filter fun j => decide (j < x) :=
        List.filter_cons_of_pos (p := fun j => decide (j < x)) ha
      rw [e, List.length_cons, List.getElem?_cons_succ]
      exact rising_pos l h2 x hx'

theorem members_rising (lo : List (OracleShape × ℕ)) : (membersOf lo).Pairwise (· < ·) :=
  (List.pairwise_lt_finRange lo.length).filter _

theorem members_nodup (lo : List (OracleShape × ℕ)) : (membersOf lo).Nodup :=
  (members_rising lo).imp fun h => ne_of_lt h

theorem mem_members {lo : List (OracleShape × ℕ)} {i : Fin lo.length} :
    i ∈ membersOf lo ↔ (lo.get i).1.mainRows ≠ 0 := by
  unfold membersOf
  simp

theorem pos_get (lo : List (OracleShape × ℕ)) (i : Fin lo.length) (hi : i ∈ membersOf lo) :
    (membersOf lo)[posOf lo i]? = some i := rising_pos _ (members_rising lo) i hi

theorem pos_lt (lo : List (OracleShape × ℕ)) (i : Fin lo.length) (hi : i ∈ membersOf lo) :
    posOf lo i < (membersOf lo).length := (List.getElem?_eq_some_iff.1 (pos_get lo i hi)).1

/-- A place that is found lies among the members. -/
theorem idxOf_lt (a : Array ℕ) (o i : ℕ) (h : a.idxOf? o = some i) : i < a.size := by
  obtain ⟨l⟩ := a
  rw [List.idxOf?_toArray] at h
  exact (List.idxOf?_eq_some_iff.1 h).1

theorem find_lt (L : GroupLayout) (o i : ℕ) (h : L.find o = some i) : i < L.members.size :=
  idxOf_lt L.members o i h

section
variable {T : Statement} {G : Group} {lo : List (OracleShape × ℕ)} {kb : Fin lo.length → Bool}
  {no : Fin lo.length → ℕ}

/-- **The place that a layout finds for a member's number is the member's place among the
members**, where the numbering parts the members. -/
theorem find_pos (H : ShapesAre T G lo kb no)
    (hinj : ∀ i ∈ membersOf lo, ∀ j ∈ membersOf lo, no i = no j → i = j) {L : GroupLayout}
    (hm : L.members = G.members) {a : Fin lo.length} (ha : a ∈ membersOf lo) {i : ℕ}
    (hf : L.find (no a) = some i) : i = posOf lo a := by
  have hi : i < (membersOf lo).length := by
    have := find_lt L _ _ hf
    rw [hm, H.size] at this
    exact this
  have e1 : G.members.getD i noId = no a := hm ▸ find_getD L _ _ hf
  rw [H.member hi] at e1
  have e2 : (membersOf lo)[i] = a := hinj _ (List.getElem_mem hi) _ ha e1
  have e3 : (membersOf lo)[posOf lo a]'(pos_lt lo a ha) = a :=
    (List.getElem?_eq_some_iff.1 (pos_get lo a ha)).2
  exact (List.Nodup.getElem_inj_iff (members_nodup lo)).1 (e2.trans e3.symm)

/-- Every member of the layout is a member of the list. -/
theorem find_onto (H : ShapesAre T G lo kb no) {L : GroupLayout} (hm : L.members = G.members)
    {o i : ℕ} (hf : L.find o = some i) : ∃ a ∈ membersOf lo, no a = o := by
  have hi : i < (membersOf lo).length := by
    have := find_lt L _ _ hf
    rw [hm, H.size] at this
    exact this
  have e1 : G.members.getD i noId = o := hm ▸ find_getD L _ _ hf
  rw [H.member hi] at e1
  exact ⟨_, List.getElem_mem hi, e1⟩

/-- The flag at a member's place is the member's. -/
theorem flag_pos (H : ShapesAre T G lo kb no) {a : Fin lo.length} (ha : a ∈ membersOf lo) :
    G.kept.getD (posOf lo a) false = kb a := by
  rw [H.flag, Array.getD_eq_getD_getElem?]
  simp [pos_get lo a ha]

end

/-! ### The typed group at the program's own layout of a written list -/

section
variable (cs : Codes) (lo : List (OracleShape × ℕ)) (s : Sg) (e : ℕ) (kb : Fin lo.length → Bool)
  (hM : ∀ i, memMain lo i → (lo.get i).1.mainRows ≠ 0 → cMain cs (lo.get i).1 = s.C)
  (hZ : ∀ i, memMain lo i → (lo.get i).1.maskRows ≠ 0 → cMask cs (lo.get i).1 = s.Z)

/-- The typed group of a list's members, at the corners that the program's layBlocks gives for the
flags kb, the members with the flag kept: general in the codes and the stage. -/
noncomputable abbrev groupLayK : RowsK (sigOf cs lo) :=
  (rowsPort cs lo (memMain lo) s e (fun i => layAt (sizesM lo kb) i.val)
    (fun i => layAt (sizesZ lo) i.val) hM hZ).keep fun a => kb a.1 = true

variable {cs lo s e kb hM hZ}
variable {T : Statement} {G : Group} {no : Fin lo.length → ℕ} {g : ℕ} {L : GroupLayout}

/-- The size that stands at a laid block's place is the member's bits of rows. -/
theorem block_bits (H : ShapesAre T G lo kb no) (part : Part) {a : Fin lo.length}
    (ha : a ∈ membersOf lo) {f : ℕ}
    (hf : (layBlocks (laySizes T G part)).1[posOf lo a]? = some (some f)) :
    (laySizes T G part)[posOf lo a]? = some (some (T.rowBits (no a) part)) ∧
      f + 2 ^ T.rowBits (no a) part ≤ (layBlocks (laySizes T G part)).2 := by
  obtain ⟨z, a1, -, a3⟩ := (layBlocks_laid (laySizes T G part)).block _ f hf
  have hz := laySizes_some T G part _ z a1
  rw [H.member (pos_lt lo a ha),
    (List.getElem?_eq_some_iff.1 (pos_get lo a ha)).2] at hz
  subst hz
  exact ⟨a1, a3⟩

/-- A member's rows are at most 2 to its bits of rows. -/
theorem rows_le_bits (H : ShapesAre T G lo kb no) (part : Part) {a : Fin lo.length}
    (ha : a ∈ membersOf lo) : (lo.get a).1.rows part ≤ 2 ^ T.rowBits (no a) part := by
  rw [(has_of_shape (H.shape a ha) part).2]
  exact Slice.le_two_pow_ceilLog2 _

/-- **THE TYPED GROUP's CUBE FITS THE LAYOUT OF A GROUP THAT HOLDS THE WRITTEN LIST's MEMBERS.** -/
theorem cubeFits_of_shapes (hG : T.groups[g]? = some G) (hL : T.layout g = some L)
    (H : ShapesAre T G lo kb no) (hA : AgreesWith lo kb L)
    (hinj : ∀ i ∈ membersOf lo, ∀ j ∈ membersOf lo, no i = no j → i = j)
    (hk : L.k = s.h + s.g) (hh : s.h = 0) (hel : 2 ^ L.logEll = s.C.l)
    (hez : 2 ^ L.logEllZk = s.Z.l) :
    CubeFits (groupLayK cs lo s e kb hM hZ) T L fun a => no a.1 := by
  have hLe := hL
  rw [layout_eq T g G hG] at hLe
  have hLm : L.members = G.members := by rw [← Option.some.inj hLe]
  have hLk : L.kept = G.kept := by rw [← Option.some.inj hLe]
  have hF1 : L.mainFirst = (layBlocks (laySizes T G .main)).1 := by rw [← Option.some.inj hLe]
  have hF2 : L.maskFirst = (layBlocks (laySizes T G .mask)).1 := by rw [← Option.some.inj hLe]
  obtain ⟨-, hA2, hA3, hA4⟩ := hA
  have hmem : ∀ a : {i // memMain lo i}, a.1 ∈ membersOf lo := fun a => mem_members.2 a.2
  refine ⟨hA2.trans hh.symm, hel, hez, ?_, ?_, ?_⟩
  · intro o i hf
    obtain ⟨a, ha, e1⟩ := find_onto H hLm hf
    exact ⟨⟨a, mem_members.1 ha⟩, e1⟩
  · intro a i first hf hkp hm
    obtain rfl := find_pos H hinj hLm (hmem a) hf
    have hkb : kb a.1 = false := by
      rw [hLk, flag_pos H (hmem a)] at hkp
      exact hkp
    have hfirst : layAt (sizesM lo kb) a.1.val = first := by
      have := hA3 a.1 a.2 hkb
      rw [hm] at this
      exact (Option.some.inj this).symm
    have hb := (layout_blocksOk T g L hL).1 (no a.1) _ first hf hm
    refine ⟨hfirst, fun j => ?_, hk ▸ hb.2, fun j hj1 hj2 => ?_⟩
    · exact (Rows.keep_slot_none _ _ _).2 (by simp [hkb])
    · -- no row without a slot stands at first + j
      unfold RowsK.rowAt
      rw [dif_neg]
      rintro ⟨⟨a', j'⟩, hs, hat⟩
      have hkb' : kb a'.1 = false := by
        have := (Rows.keep_slot_none _ _ _).1 hs
        simpa using this
      have hat' : layAt (sizesM lo kb) a'.1.val + j'.val = first + j := hat
      have hj' : j'.val < (lo.get a'.1).1.mainRows := j'.2
      by_cases hne : a' = a
      · subst hne
        have hj1' : (lo.get a'.1).1.mainRows ≤ j := hj1
        omega
      · have hp : posOf lo a'.1 ≠ posOf lo a.1 := by
          intro ep
          have e1 := pos_get lo a'.1 (hmem a')
          rw [ep, pos_get lo a.1 (hmem a)] at e1
          exact hne (Subtype.ext (Option.some.inj e1).symm)
        have hm' := hA3 a'.1 a'.2 hkb'
        rw [hF1] at hm hm'
        have g1 := (getD_some _ _ _).1 hm
        have g2 := (getD_some _ _ _).1 hm'
        have b1 := (block_bits H .main (hmem a) g1).1
        have b2 := (block_bits H .main (hmem a') g2).1
        have r2 := rows_le_bits H .main (hmem a')
        have r2' : (lo.get a'.1).1.mainRows ≤ 2 ^ T.rowBits (no a'.1) .main := r2
        rcases (layBlocks_laid (laySizes T G .main)).apart _ _ _ _ _ _ hp g2 g1 b2 b1 with q | q
        · omega
        · omega
  · intro a i first hf hm
    obtain rfl := find_pos H hinj hLm (hmem a) hf
    have hb := (layout_blocksOk T g L hL).2 (no a.1) _ first hf hm
    rw [hA2] at hb
    have hm2 := hm
    rw [hF2] at hm2
    have b1 := (block_bits H .mask (hmem a) ((getD_some _ _ _).1 hm2)).1
    -- a block is laid for a member that has the table
    have hz : (lo.get a.1).1.maskRows ≠ 0 := by
      intro h0
      unfold laySizes at b1
      rw [Array.getElem?_map] at b1
      have hr : (Array.range G.members.size)[posOf lo a.1]? = some (posOf lo a.1) := by
        rw [Array.getElem?_range, if_pos (H.size ▸ pos_lt lo a.1 (hmem a))]
      rw [hr] at b1
      have b1' := Option.some.inj b1
      dsimp only at b1'
      rw [H.member (pos_lt lo a.1 (hmem a)),
        (List.getElem?_eq_some_iff.1 (pos_get lo a.1 (hmem a))).2,
        (has_of_shape (H.shape a.1 (hmem a)) .mask).1] at b1'
      simp [OracleShape.rows] at b1'
      exact b1' h0
    have hfirst : layAt (sizesZ lo) a.1.val = first := by
      have := hA4 a.1 a.2 hz
      rw [hm] at this
      exact (Option.some.inj this).symm
    have hb' : first + 2 ^ T.rowBits (no a.1) .mask ≤ 2 ^ s.h := by rw [hh]; exact hb.2
    refine ⟨hfirst, hb', fun j hj1 hj2 => ?_⟩
    have hp1 : 1 ≤ 2 ^ T.rowBits (no a.1) .mask := Nat.one_le_two_pow
    have hb2 : first + 2 ^ T.rowBits (no a.1) .mask ≤ 2 ^ 0 := hb.2
    have hj1' : (lo.get a.1).1.maskRows ≤ j := hj1
    rw [pow_zero] at hb2
    omega

end

/-! ### It can be met; and at the two written sizes -/

/-- **ShapesAre has a member**: the statement made of the list, its one group, each message under
its own number. -/
theorem shapesAre_stOf (lo : List (OracleShape × ℕ)) (kb : Fin lo.length → Bool) :
    ShapesAre (stOf lo kb) (groupOf lo kb) lo kb fun i => i.val where
  members := by simp
  kept := by simp
  shape := fun i _ => stOf_shape lo kb i

/-- Every group in front, at both sizes, has no variable for the mask rows. -/
theorem front_h : (∀ gs ∈ frontFull, gs.h = 0) ∧ ∀ gs ∈ frontSmall, gs.h = 0 := by decide

section
variable {T : Statement} {G : Group} {lo : List (OracleShape × ℕ)} {kb : Fin lo.length → Bool}
  {no : Fin lo.length → ℕ} {g : ℕ}

/-- **At the real group of the full size**, whichever members are kept. -/
theorem cubeFits_full (hlo : lo ∈ linksFullLit) (gs : GroupSize) (hgs : gs ∈ frontFull)
    (hG : T.groups[g]? = some G) (H : ShapesAre T G lo kb no)
    (hinj : ∀ i ∈ membersOf lo, ∀ j ∈ membersOf lo, no i = no j → i = j)
    (hk : gs.k = kLay lo kb) :
    ∃ L, T.layout g = some L ∧ (begun T g G).layout g = some L ∧
      L.k = (groupFullLayK lo hlo gs hgs kb).s.h + (groupFullLayK lo hlo gs hgs kb).s.g ∧
      (2 ^ L.logEll = gs.main.ell → 2 ^ L.logEllZk = gs.mask.ell →
        CubeFits (groupFullLayK lo hlo gs hgs kb) T L fun a => no a.1) := by
  have hh : gs.h = 0 := front_h.1 gs hgs
  obtain ⟨L, h1, h2, -, -⟩ := layout_of_shapes hG H (linksFull_layout lo hlo kb)
  have hLk : L.k = gs.h + (gs.k - gs.h) := by rw [h2.1, hh, hk]; omega
  exact ⟨L, h1, (OnBytes.LayLaw.begun_layout T g G hG).trans h1, hLk, fun e1 e2 =>
    cubeFits_of_shapes hG h1 H h2 hinj hLk hh e1 e2⟩

/-- The like at the small size. -/
theorem cubeFits_small (hlo : lo ∈ linksSmallLit) (gs : GroupSize) (hgs : gs ∈ frontSmall)
    (hG : T.groups[g]? = some G) (H : ShapesAre T G lo kb no)
    (hinj : ∀ i ∈ membersOf lo, ∀ j ∈ membersOf lo, no i = no j → i = j)
    (hk : gs.k = kLay lo kb) :
    ∃ L, T.layout g = some L ∧ (begun T g G).layout g = some L ∧
      L.k = (groupSmallLayK lo hlo gs hgs kb).s.h + (groupSmallLayK lo hlo gs hgs kb).s.g ∧
      (2 ^ L.logEll = gs.main.ell → 2 ^ L.logEllZk = gs.mask.ell →
        CubeFits (groupSmallLayK lo hlo gs hgs kb) T L fun a => no a.1) := by
  have hh : gs.h = 0 := front_h.2 gs hgs
  obtain ⟨L, h1, h2, -, -⟩ := layout_of_shapes hG H (linksSmall_layout lo hlo kb)
  have hLk : L.k = gs.h + (gs.k - gs.h) := by rw [h2.1, hh, hk]; omega
  exact ⟨L, h1, (OnBytes.LayLaw.begun_layout T g G hG).trans h1, hLk, fun e1 e2 =>
    cubeFits_of_shapes hG h1 H h2 hinj hLk hh e1 e2⟩

end

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.cubeFits_of_shapes
#print axioms VerifiableInference.Desc.First.Close.shapesAre_stOf
#print axioms VerifiableInference.Desc.First.Close.cubeFits_full
#print axioms VerifiableInference.Desc.First.Close.cubeFits_small
#print axioms VerifiableInference.Desc.First.Close.front_h
#print axioms VerifiableInference.Desc.First.Close.find_pos
#print axioms VerifiableInference.Desc.First.Close.find_onto
#print axioms VerifiableInference.Desc.First.Close.flag_pos
