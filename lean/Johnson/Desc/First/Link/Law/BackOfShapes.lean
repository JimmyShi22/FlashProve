-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/BackOfShapes.lean: THE LAYOUT AGAINST THE ARRANGEMENT, ON INDICES
(`BackAt`, MiddleAtK10.lean
beside this file), AT A GROUP THAT HOLDS A WRITTEN LIST's MEMBERS: FROM `ShapesAre`. Theorems.

Why. `SampleFits` (Close/Law/SampleTie.lean) has two debts. `BlockAt` is paid at these groups by
`blockAt_of_shapes` (Close/Law/BlockOfShapes.lean). `Middle` is paid for kind K1's sample row by
`middle_of`
(MiddleAtK10.lean) under one named premise on indices, `BackAt`, which was shown of nothing. This
file pays it, on the
road of BlockOfShapes.lean's `main_one`.

What is said.
  `backAt_of_shapes`: T.groups[g]? = some G; T.layout g = some L; `GroupOk T G`; `ShapesAre T G lo
  kb no`;
    `AgreesWith lo kb L`; the numbering parts the members (hinj); L.k = s.h + s.g; s.h = 0: THEN, at
    every member a
    of `groupLayK cs lo s e kb hM hZ`, under the names `namesOf ..`: `BackAt .. T L (no a.1) a`:
    **at a vertex that
    holds a's row r, the entry of a's own table that belongs to (vertex, place x) is r + 2 ^ (a's
    row bits) * x**:
    main, kept, mask.
How. The vertex's number is the block's first row + r (`rowAt_some`; `AgreesWith`), so the index is
`groupIndex` of
r + 2 ^ bits * x (`groupIndex_closed`), and `unshift` undoes `groupIndex` at a block that is aligned
and inside
(`unshift_groupIndex`, OnBytes/Iop/RowLaws.lean). The row bits are the written shape's
(`has_of_shape`).

Limits. `ShapesAre` and hinj are shown of no verifier's state here. L.k = s.h + s.g and s.h = 0 stay
premises (both are
drawn at the two written sizes in Close/Law/CubeOfShapes.lean: `cubeFits_full`, `front_h`). Nothing
on soundness.

-/
import Johnson.Desc.First.Link.Law.MiddleAtK10
import Johnson.Desc.First.Close.Law.BlockOfShapes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin

open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Means Johnson.Pack Johnson.Top.H Johnson.G Cb
open OnBytes.LayLaw (layout_blocksOk)
open VerifiableInference.Desc.First.Close

variable {cs : Codes} {lo : List (OracleShape × ℕ)} {s : Sg} {e : ℕ} {kb : Fin lo.length → Bool}
  {hM : ∀ i, memMain lo i → (lo.get i).1.mainRows ≠ 0 → cMain cs (lo.get i).1 = s.C}
  {hZ : ∀ i, memMain lo i → (lo.get i).1.maskRows ≠ 0 → cMask cs (lo.get i).1 = s.Z}
  {no : Fin lo.length → ℕ} {T : Statement} {G : Group} {g : ℕ} {L : GroupLayout}

open Classical in
/-- Where the arrangement's mask row b holds the row r, r's number is b's. -/
theorem srcZ_at {S : Sig GE} {R : RowsK S} {b : Fin R.s.h → Bool}
    {r : Σ a : R.G.A, Fin (R.nZ a)} (h : R.Sh.az.src b = some r) : R.atZ r = Sz.rowNo b := by
  have h' : (if h : ∃ r, R.atZ r = Sz.rowNo b then some h.choose else none) = some r := h
  split at h'
  · rename_i hex
    obtain rfl := Option.some.inj h'
    exact hex.choose_spec
  · cases h'

/-- **THE LAYOUT AGAINST THE ARRANGEMENT, ON INDICES, AT A GROUP THAT HOLDS THE WRITTEN LIST's
MEMBERS.** -/
theorem backAt_of_shapes (hG : T.groups[g]? = some G) (hL : T.layout g = some L)
    (hOk : GroupOk T G) (H : ShapesAre T G lo kb no) (hA : AgreesWith lo kb L)
    (hinj : ∀ i ∈ membersOf lo, ∀ j ∈ membersOf lo, no i = no j → i = j)
    (hk : L.k = s.h + s.g) (hh : s.h = 0) (a : {i // memMain lo i}) :
    BackAt cs lo (memMain lo) s e (fun i => layAt (sizesM lo kb) i.val)
      (fun i => layAt (sizesZ lo) i.val) hM hZ (fun a => kb a.1 = true)
      (namesOf cs lo s e kb hM hZ no) T L (no a.1) a := by
  have hLe := hL
  rw [OnBytes.LayLaw.layout_eq T g G hG] at hLe
  have hLm : L.members = G.members := by rw [← Option.some.inj hLe]
  have Y := layFacts hG hL hOk
  have hm : a.1 ∈ membersOf lo := mem_members.2 a.2
  have hf := find_member Y H hinj hLm hm
  refine ⟨fun b r x h => ?_, fun q r x hq => ?_, fun b r y h => ?_⟩
  · obtain ⟨h1, h2⟩ := rowAt_some (groupLayK cs lo s e kb hM hZ) (i := Sz.rowNo b) h
    have hkb : kb a.1 = false := by
      have := (Rows.keep_slot_none _ _ _).1 h1
      simpa using this
    have hat : layAt (sizesM lo kb) a.1.val + r.val = Sz.rowNo b := h2
    have hfi := hA.2.2.1 a.1 a.2 hkb
    have hb := (layout_blocksOk T g L hL).1 _ _ _ hf hfi
    have hr : r.val < 2 ^ T.rowBits (no a.1) .main :=
      lt_of_lt_of_le r.2 (rows_le_bits H .main hm)
    have e1 : Sz.rowNo b + 2 ^ (s.h + s.g) * x.val =
        groupIndex (r.val + 2 ^ T.rowBits (no a.1) .main * x.val) (T.rowBits (no a.1) .main)
          (layAt (sizesM lo kb) a.1.val) L.k := by
      rw [groupIndex_closed _ _ _ _ _ hr, hk, hat]
    unfold mainBack
    rw [e1, unshift_groupIndex _ _ _ _ hb, (has_of_shape (H.shape _ hm) .main).2]
    rfl
  · have ea : q.1.1 = a := congrArg Sigma.fst hq
    subst ea
    have er : q.2 = r := eq_of_heq (Sigma.mk.inj_iff.1 hq).2
    subst er
    show q.2.val + x.val * 2 ^ ceilLog2 (lo.get q.1.1.1).1.mainRows =
      q.2.val + 2 ^ ceilLog2 (lo.get q.1.1.1).1.mainRows * x.val
    rw [Nat.mul_comm]
  · have hz : (lo.get a.1).1.maskRows ≠ 0 := fun h0 => absurd r.2 (by omega)
    have hat : layAt (sizesZ lo) a.1.val + r.val = Sz.rowNo b :=
      srcZ_at (R := groupLayK cs lo s e kb hM hZ) h
    have hfi := hA.2.2.2 a.1 a.2 hz
    have hb := (layout_blocksOk T g L hL).2 _ _ _ hf hfi
    have hr : r.val < 2 ^ T.rowBits (no a.1) .mask :=
      lt_of_lt_of_le r.2 (rows_le_bits H .mask hm)
    have hLh : L.h = s.h := hA.2.1.trans hh.symm
    have e1 : Sz.rowNo b + 2 ^ s.h * y.val =
        groupIndex (r.val + 2 ^ T.rowBits (no a.1) .mask * y.val) (T.rowBits (no a.1) .mask)
          (layAt (sizesZ lo) a.1.val) L.h := by
      rw [groupIndex_closed _ _ _ _ _ hr, hLh, hat]
    unfold maskBack
    rw [e1, unshift_groupIndex _ _ _ _ hb, (has_of_shape (H.shape _ hm) .mask).2]
    rfl

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.srcZ_at
#print axioms VerifiableInference.Desc.LinkJoin.backAt_of_shapes
