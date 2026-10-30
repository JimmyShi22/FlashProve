-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/BlockOfShapes.lean: THE LAYOUT AGAINST THE ARRANGEMENT, AT A GROUP THAT
HOLDS A WRITTEN LIST's MEMBERS: `BlockAt` (SampleTie.lean, beside this file) FROM `ShapesAre`
(LayoutOfShapes.lean). Statements and proofs.

Why. K10's promise asks of each member's sample row that the typed form, arranged, is the program's
row laid alone (`SampleFits`, SampleTie.lean). That file parts the debt in two: `BlockAt` (once for
a member of a group: the layout's block of the member's message is where the arrangement puts the
member's rows) and `Middle` (once for a sample row: other files'). `BlockAt` was shown of
nothing.
  `rowAt_some`: what "the row without a slot at the number i" says: it has no slot, and its corner's
    number is i.
  `find_member`: the layout finds each member at its place among the members.
  `main_one`: where the typed group `groupLayK` (CubeOfShapes.lean) has the main row r of the member
    m at the corner b: m's message has the weight 1 at the index (b's number + 2 ^ (s.h + s.g) * x):
    by `mainWeight_rows` (OnBytes/Iop/RowLaws.lean).
  `mask_one`: a member with a mask row has the weight 1 at EVERY index of the mask table: the layout
    has no variable for the mask rows (`AgreesWith`'s second clause), so its one row is that
    member's: by `maskWeight_rows`.
  `blockAt_of_shapes`: T.groups[g]? = some G; T.layout g = some L; `GroupOk T G`; `ShapesAre T G lo
    kb no`; `AgreesWith lo kb L`; the numbering parts the members (hinj); L.k = s.h + s.g: THEN, at
    every member a: `BlockAt (namesOf ..) T L (no a.1) a`. On another member's rows the weight is 0
    by `mainWeight_apart`, `maskWeight_apart` (LayTables.lean: at no index do two
    messages have a weight).
Limits. `ShapesAre` and hinj are shown of no verifier's state. L.k = s.h + s.g stays a premise.
`Middle`, the other half of `SampleFits`, is other files' and is not touched; `sampleFits_of` is
not called here. At both sizes the clauses on mask rows bite at one row at most. Nothing on
soundness.

-/
import Johnson.Desc.First.Close.Law.NamesOfShapes
import Johnson.Desc.First.Close.Law.SampleTie
import Johnson.Desc.First.Close.Law.LayTables

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Means Johnson.Pack Johnson.Top.H Johnson.G Cb
open OnBytes.LayLaw (layout_blocksOk mainWeight_apart maskWeight_apart)

/-- What "the row without a slot at the number i" says. -/
theorem rowAt_some {S : Sig GE} (R : RowsK S) {i : ℕ} {r : Σ a : R.G.A, Fin (R.nM a)}
    (h : R.rowAt i = some r) : R.slot r = none ∧ R.atM r = i := by
  unfold RowsK.rowAt at h
  split at h
  · rename_i hex
    obtain rfl := Option.some.inj h
    exact hex.choose_spec
  · cases h

section
variable {cs : Codes} {lo : List (OracleShape × ℕ)} {s : Sg} {e : ℕ} {kb : Fin lo.length → Bool}
  {hM : ∀ i, memMain lo i → (lo.get i).1.mainRows ≠ 0 → cMain cs (lo.get i).1 = s.C}
  {hZ : ∀ i, memMain lo i → (lo.get i).1.maskRows ≠ 0 → cMask cs (lo.get i).1 = s.Z}
  {no : Fin lo.length → ℕ} {T : Statement} {G : Group} {g : ℕ} {L : GroupLayout}

/-- The layout finds each member at its place among the members. -/
theorem find_member (Y : LayFacts T G L) (H : ShapesAre T G lo kb no)
    (hinj : ∀ i ∈ membersOf lo, ∀ j ∈ membersOf lo, no i = no j → i = j)
    (hLm : L.members = G.members) {a : Fin lo.length} (ha : a ∈ membersOf lo) :
    L.find (no a) = some (posOf lo a) := by
  have hin : no a ∈ G.members.toList := by
    rw [H.members]
    exact List.mem_map_of_mem ha
  obtain ⟨i, hi⟩ := Y.find_of_mem _ hin
  rw [hi, find_pos H hinj hLm ha hi]

/-- **On a member's own main rows its weight is 1.** -/
theorem main_one (hL : T.layout g = some L) (Y : LayFacts T G L) (H : ShapesAre T G lo kb no)
    (hA : AgreesWith lo kb L)
    (hinj : ∀ i ∈ membersOf lo, ∀ j ∈ membersOf lo, no i = no j → i = j)
    (hLm : L.members = G.members) (hLk : L.kept = G.kept) (hk : L.k = s.h + s.g)
    (m : {i // memMain lo i}) (b : Fin (s.h + s.g) → Bool) (r : Fin (lo.get m.1).1.mainRows)
    (x : ℕ) (h : (groupLayK cs lo s e kb hM hZ).rowAt (Sz.rowNo b) = some ⟨m, r⟩) :
    mainWeight (K := GE) T L (no m.1) (Sz.rowNo b + 2 ^ (s.h + s.g) * x) = 1 := by
  have hm : m.1 ∈ membersOf lo := mem_members.2 m.2
  obtain ⟨h1, h2⟩ := rowAt_some _ h
  have hkb : kb m.1 = false := by
    have := (Rows.keep_slot_none _ _ _).1 h1
    simpa using this
  have hat : layAt (sizesM lo kb) m.1.val + r.val = Sz.rowNo b := h2
  have hf := find_member Y H hinj hLm hm
  have hkp : L.kept.getD (posOf lo m.1) false = false := by rw [hLk, flag_pos H hm, hkb]
  have hfi := hA.2.2.1 m.1 m.2 hkb
  have hb := (layout_blocksOk T g L hL).1 _ _ _ hf hfi
  rw [mainWeight_rows T L _ _ _ _ hf hkp hfi hb, hk, Nat.add_mul_mod_self_left]
  have hr : r.val < 2 ^ T.rowBits (no m.1) .main :=
    lt_of_lt_of_le r.2 (rows_le_bits H .main hm)
  have hb2 := hb.2
  rw [hk] at hb2
  rw [Nat.mod_eq_of_lt (by omega), if_pos ⟨by omega, by omega⟩]

/-- **A member with a mask row has the weight 1 at every index of the mask table**: the layout has
no variable for the mask rows, so its one row is that member's. -/
theorem mask_one (hL : T.layout g = some L) (Y : LayFacts T G L) (H : ShapesAre T G lo kb no)
    (hA : AgreesWith lo kb L)
    (hinj : ∀ i ∈ membersOf lo, ∀ j ∈ membersOf lo, no i = no j → i = j)
    (hLm : L.members = G.members) (m : {i // memMain lo i}) (r : Fin (lo.get m.1).1.maskRows)
    (J : ℕ) : maskWeight (K := GE) T L (no m.1) J = 1 := by
  have hm : m.1 ∈ membersOf lo := mem_members.2 m.2
  have hz : (lo.get m.1).1.maskRows ≠ 0 := fun h0 => absurd r.2 (by omega)
  have hf := find_member Y H hinj hLm hm
  have hfi := hA.2.2.2 m.1 m.2 hz
  have hb := (layout_blocksOk T g L hL).2 _ _ _ hf hfi
  rw [maskWeight_rows T L _ _ _ _ hf hfi hb, hA.2.1, pow_zero, Nat.mod_one]
  have hb2 := hb.2
  rw [hA.2.1, pow_zero] at hb2
  have hp : 1 ≤ 2 ^ T.rowBits (no m.1) .mask := Nat.one_le_two_pow
  rw [if_pos ⟨by omega, by omega⟩]

/-- **THE LAYOUT AGAINST THE ARRANGEMENT, AT A GROUP THAT HOLDS THE WRITTEN LIST's MEMBERS.** -/
theorem blockAt_of_shapes (hG : T.groups[g]? = some G) (hL : T.layout g = some L)
    (hOk : GroupOk T G) (H : ShapesAre T G lo kb no) (hA : AgreesWith lo kb L)
    (hinj : ∀ i ∈ membersOf lo, ∀ j ∈ membersOf lo, no i = no j → i = j)
    (hk : L.k = s.h + s.g) (a : {i // memMain lo i}) :
    BlockAt (R := groupLayK cs lo s e kb hM hZ) (namesOf cs lo s e kb hM hZ no) T L (no a.1) a := by
  have hLe := hL
  rw [OnBytes.LayLaw.layout_eq T g G hG] at hLe
  have hLm : L.members = G.members := by rw [← Option.some.inj hLe]
  have hLk : L.kept = G.kept := by rw [← Option.some.inj hLe]
  have Y := layFacts hG hL hOk
  have hmem : ∀ m : {i // memMain lo i}, m.1 ∈ membersOf lo := fun m => mem_members.2 m.2
  have hne : ∀ m : {i // memMain lo i}, m ≠ a → no m.1 ≠ no a.1 := fun m hm e =>
    hm (Subtype.ext (hinj _ (hmem m) _ (hmem a) e))
  refine ⟨fun b r x h => main_one hL Y H hA hinj hLm hLk hk a b r x.val h, fun b m r x h hm => ?_,
    fun q r h => ?_, fun q m r h hm => ?_,
    fun _ r _ _ => mask_one hL Y H hA hinj hLm a r _, fun b m r y h hm => ?_⟩
  · refine mainWeight_apart T g L hL (no m.1) (no a.1) _ (hne m hm) ?_
    exact fun h0 => one_ne_zero ((main_one hL Y H hA hinj hLm hLk hk m b r x.val h).symm.trans h0)
  · have ea : q.1.1 = a := congrArg Sigma.fst h
    subst ea
    refine ⟨rfl, ?_⟩
    unfold keptWeight
    rw [find_member Y H hinj hLm (hmem q.1.1)]
    have hkp : L.kept.getD (posOf lo q.1.1.1) false = true := by
      rw [hLk, flag_pos H (hmem q.1.1)]
      exact q.1.2
    simp [hkp]
  · have em : q.1.1 = m := congrArg Sigma.fst h
    subst em
    exact hne q.1.1 hm
  · refine maskWeight_apart T g L hL (no m.1) (no a.1) _ (hne m hm) ?_
    exact fun h0 => one_ne_zero ((mask_one hL Y H hA hinj hLm m r _).symm.trans h0)

end

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.main_one
#print axioms VerifiableInference.Desc.First.Close.mask_one
#print axioms VerifiableInference.Desc.First.Close.blockAt_of_shapes
