-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/NamesOfShapes.lean: THE KEPT SLOTS' NAMES AS A TERM OFF THE WRITTEN
LIST; THEY FIT A STATEMENT WHOSE GROUP HOLDS THE LIST's MEMBERS; SO THE ARRANGED MESSAGE's TABLES
HOLD THE WORDS ON THE MEMBERS' BLOCKS. A definition, statements and proofs.

Why. K10's law is general in a letter N (`SlotNames`, Border.lean, beside this file): for each kept
slot the number of an oracle message and, for each place, an index of that message's main table.
EndSays.lean asks that these names lie within the statement's tables; CubeAt.lean asks `NamesFit`.
Neither was shown of any N.
  `namesOf cs lo s e kb hM hZ no`: N AS A TERM, at the typed group `groupLayK` (CubeOfShapes.lean):
    the slot of row j of a kept member a bears the number no a; its place x bears the index j + x *
    2 ^ (the bits of rows of a's WRITTEN shape).
  `namesFit_of_shapes`: T.groups[g]? = some G; T.layout g = some L; `ShapesAre T G lo kb no`
    (LayoutOfShapes.lean); the numbering parts the members (hinj): `NamesFit (groupLayK ..) (namesOf
    ..) T L fun a => no a.1`.
  `names_in`: with `LayFacts T G L` (Johnson/Desc/Means/Layout.lean) and 2 ^ L.logEll = s.C.l: each
    name's number is below the number of the statement's messages, and each index below that
    message's main table's size: the premise hN of EndSays.lean's three theorems.
  `laidOn_of_shapes`: `laidOn_of_cube` (CubeAt.lean) with its public ties paid
    (`cubeFits_of_shapes`, `namesFit_of_shapes`, `layFacts`): the group's data in order
    (`Good`); the group in order in the statement (`GroupOk`); `ShapesAre`; `AgreesWith lo kb L`;
    hinj; L.k = s.h + s.g; s.h = 0; the two codes' lengths; and `WordsAre`: THEN `LaidOn T L m (tabK
    (namesOf ..) (..Sh.rho.up u).1)`.
Limits. `WordsAre` (the words at the members are the members' own rows as the group's message holds
them, 0 beyond) STAYS A PREMISE: it is what an extractor that lays the decoded messages is to give.
`ShapesAre` and hinj are shown of no verifier's state. The two equations on the codes' lengths and
L.k = s.h + s.g stay premises. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.CubeOfShapes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Means Johnson.Pack Johnson.Top.H Johnson.G

section
variable (cs : Codes) (lo : List (OracleShape × ℕ)) (s : Sg) (e : ℕ) (kb : Fin lo.length → Bool)
  (hM : ∀ i, memMain lo i → (lo.get i).1.mainRows ≠ 0 → cMain cs (lo.get i).1 = s.C)
  (hZ : ∀ i, memMain lo i → (lo.get i).1.maskRows ≠ 0 → cMask cs (lo.get i).1 = s.Z)
  (no : Fin lo.length → ℕ)

/-- **The kept slots' names, off the written list and the numbering**: the member's number; (row,
place) as an index of that member's own main table, at the written shape's bits of rows. -/
def namesOf : SlotNames (groupLayK cs lo s e kb hM hZ) where
  orc := fun q => no q.1.1.1
  idx := fun q x => q.2.val + x.val * 2 ^ ceilLog2 (lo.get q.1.1.1).1.mainRows

variable {cs lo s e kb hM hZ no}
variable {T : Statement} {G : Group} {g : ℕ} {L : GroupLayout}

/-- **These names fit a statement whose group holds the written list's members.** -/
theorem namesFit_of_shapes (hG : T.groups[g]? = some G) (hL : T.layout g = some L)
    (H : ShapesAre T G lo kb no)
    (hinj : ∀ i ∈ membersOf lo, ∀ j ∈ membersOf lo, no i = no j → i = j) :
    NamesFit (groupLayK cs lo s e kb hM hZ) (namesOf cs lo s e kb hM hZ no) T L
      fun a => no a.1 := by
  have hLe := hL
  rw [OnBytes.LayLaw.layout_eq T g G hG] at hLe
  have hLm : L.members = G.members := by rw [← Option.some.inj hLe]
  have hLk : L.kept = G.kept := by rw [← Option.some.inj hLe]
  have hmem : ∀ a : {i // memMain lo i}, a.1 ∈ membersOf lo := fun a => mem_members.2 a.2
  refine ⟨fun a b h => Subtype.ext (hinj _ (hmem a) _ (hmem b) h), fun _ => rfl, fun q x => ?_,
    ?_, fun a i hf hk => ?_⟩
  · show q.2.val + x.val * 2 ^ ceilLog2 (lo.get q.1.1.1).1.mainRows =
      q.2.val + x.val * 2 ^ T.rowBits (no q.1.1.1) .main
    rw [(has_of_shape (H.shape _ (hmem q.1.1)) .main).2]
    rfl
  · rintro ⟨⟨a, ha⟩, j⟩ ⟨⟨a', ha'⟩, j'⟩ h
    have h' : (⟨a, j⟩ : Σ a : {i // memMain lo i}, Fin (lo.get a.1).1.mainRows) = ⟨a', j'⟩ := h
    cases h'
    rfl
  · obtain rfl := find_pos H hinj hLm (hmem a) hf
    have hkb : kb a.1 = true := by
      rw [hLk, flag_pos H (hmem a)] at hk
      exact hk
    exact ⟨fun j => ⟨⟨⟨a, hkb⟩, j⟩, rfl⟩, rows_le_bits H .main (hmem a)⟩

/-- **The names lie within the statement's tables.** -/
theorem names_in (Y : LayFacts T G L) (H : ShapesAre T G lo kb no)
    (hel : 2 ^ L.logEll = s.C.l) (q : (groupLayK cs lo s e kb hM hZ).Kp)
    (x : (groupLayK cs lo s e kb hM hZ).s.cM.J) :
    (namesOf cs lo s e kb hM hZ no).orc q < T.oracles.size ∧
      (namesOf cs lo s e kb hM hZ no).idx q x <
        tableSize T ((namesOf cs lo s e kb hM hZ no).orc q) .main := by
  have hm : q.1.1.1 ∈ membersOf lo := mem_members.2 q.1.1.2
  have hsh := H.shape _ hm
  have hlt : no q.1.1.1 < T.oracles.size := by
    obtain ⟨y, hy, -⟩ := Option.map_eq_some_iff.1 hsh
    exact (Array.getElem?_eq_some_iff.1 hy).1
  have hhas : T.has (no q.1.1.1) .main = true := by
    rw [(has_of_shape hsh .main).1]
    exact decide_eq_true (Nat.pos_of_ne_zero q.1.1.2)
  have hin : no q.1.1.1 ∈ G.members.toList := by
    rw [H.members]
    exact List.mem_map_of_mem hm
  have hpb := Y.main_places _ hin hhas
  have hrb := (has_of_shape hsh .main).2
  refine ⟨hlt, ?_⟩
  show q.2.val + x.val * 2 ^ ceilLog2 (lo.get q.1.1.1).1.mainRows < tableSize T (no q.1.1.1) .main
  unfold tableSize
  rw [if_pos hhas]
  unfold Statement.tableBits
  rw [hpb, hrb, pow_add, hel]
  have h1 : q.2.val < 2 ^ ceilLog2 (lo.get q.1.1.1).1.mainRows :=
    lt_of_lt_of_le q.2.2 (Slice.le_two_pow_ceilLog2 _)
  have h2 : x.val + 1 ≤ s.C.l := x.2
  calc q.2.val + x.val * 2 ^ ceilLog2 (lo.get q.1.1.1).1.mainRows
      < 2 ^ ceilLog2 (lo.get q.1.1.1).1.mainRows +
        x.val * 2 ^ ceilLog2 (lo.get q.1.1.1).1.mainRows := Nat.add_lt_add_right h1 _
    _ = 2 ^ ceilLog2 (lo.get q.1.1.1).1.mainRows * (x.val + 1) := by ring
    _ ≤ 2 ^ ceilLog2 (lo.get q.1.1.1).1.mainRows * s.C.l := Nat.mul_le_mul_left _ h2

/-- **THE ARRANGED MESSAGE's TABLES HOLD THE WORDS ON THE MEMBERS' BLOCKS**, at a statement whose
group holds the written list's members: the public ties of laidOn_of_cube are paid. -/
theorem laidOn_of_shapes (hg : (groupLayK cs lo s e kb hM hZ).Good) (hG : T.groups[g]? = some G)
    (hL : T.layout g = some L) (hOk : GroupOk T G) (H : ShapesAre T G lo kb no)
    (hA : AgreesWith lo kb L)
    (hinj : ∀ i ∈ membersOf lo, ∀ j ∈ membersOf lo, no i = no j → i = j)
    (hk : L.k = s.h + s.g) (hh : s.h = 0) (hel : 2 ^ L.logEll = s.C.l)
    (hez : 2 ^ L.logEllZk = s.Z.l)
    (u : ((groupLayK cs lo s e kb hM hZ).G.C.J → GE) × ((groupLayK cs lo s e kb hM hZ).G.C.Q → GE))
    (m : Words GE) (hW : WordsAre (groupLayK cs lo s e kb hM hZ) T (fun a => no a.1) u m) :
    LaidOn T L m (tabK (namesOf cs lo s e kb hM hZ no)
      ((groupLayK cs lo s e kb hM hZ).Sh.rho.up u).1) :=
  laidOn_of_cube _ _ hg (layFacts hG hL hOk) hk
    (cubeFits_of_shapes hG hL H hA hinj hk hh hel hez) (namesFit_of_shapes hG hL H hinj) u m hW

end

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.namesFit_of_shapes
#print axioms VerifiableInference.Desc.First.Close.names_in
#print axioms VerifiableInference.Desc.First.Close.laidOn_of_shapes
