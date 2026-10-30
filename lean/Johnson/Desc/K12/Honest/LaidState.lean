-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Honest/LaidState.lean: if a prover's state by index holds the members' rows at the
layout's blocks and 0 elsewhere (`StateAt`, Johnson/Desc/K12/Honest/FirstState.lean), then, under
the hypotheses listed below, its two tables hold on the members' blocks the words that the plain
rows make (`LaidOn`, Johnson/Desc/Means/Bridge.lean, at `wordsAt`). `bat_claimTrue`
(Johnson/Desc/K12/Honest/BatValues.lean) has `LaidOn` of its state's two tables as a hypothesis;
`first_V` (Johnson/Desc/K12/Honest/FirstValues.lean) has `StateAt` of its state as a hypothesis.
Here the first follows from the second; `bat_claimTrue_state`
(Johnson/Desc/K12/Honest/BatState.lean) calls `laidOn_state` for that. General in every parameter:
S, G, L, a, Dp, P and R. Two definitions and three theorems. It does not depend on the frame for an
honest side (Johnson/Desc/ProofFile/Honest/Frame.lean).

In the list: S (`Statement`, OnBytes/Iop/Ground.lean) is the library's statement. It names an oracle
message by a number o; a message has two tables (`Part`, Ground.lean): `.main`, of its main rows,
and `.mask`, of its mask rows. A table that is there (`S.has o part`) has 2 ^ `S.rowBits o part`
rows, of which the first `realRows S o part` (Johnson/Desc/Means/Says.lean) are the message's real
rows. The index idx of a table is entry (row idx % 2 ^ `S.rowBits o part`, place
idx / 2 ^ `S.rowBits o part`). Words (`Words`, Says.lean) are a value for each oracle message, table
and index. G (`Group`, Ground.lean) is a group of oracle messages, its members; it enters through
`LayFacts` only. L (`GroupLayout`, Ground.lean) is a group's layout: `L.find o` is the number of o
among the members, `L.mainFirst` and `L.maskFirst` state the first row of each member's block in the
group's main table and mask table, and `L.kept` marks the members that are kept (a kept member's
main rows have no block in the group's main table). Dp (`Plain`,
Johnson/Desc/K12/Law/FirstOk.lean) are the group's plain data, with a layout `Dp.L` and members
`Dp.mems`, each with its number `id` and its shape `sh`. R (`PlainRows`,
Johnson/Desc/K12/Honest/FirstRows.lean) are rows as functions of numbers: `R.M j i e` and
`R.Z j i e` are the entry at place e of row i of member j's main rows and mask rows. P (`PS`,
Johnson/Prover/Link/BodyState.lean) is the state by index; `tabsOf P` (BatValues.lean) is its two
tables `tabM` and `tabZ` as the library's tables of a group (`Tables`, Says.lean), with 0 as the
kept part. a (`Fmt.M1.Stage`) is a stage; `kk a` (FirstOk.lean) is `a.h + (a.k - a.h)`.

  `laidOn_state`: under the hypotheses below, `LaidOn S L (wordsAt S L R) (tabsOf P)`: for every
    member for which the layout states a block, and every index idx below the size of the member's
    table, the state's table has at the group's index of idx (`groupIndex`, Ground.lean) the value
    of `wordsAt` at idx; so for the main table and for the mask table
  `wordsAt S L R`: a definition: the words. At member number j of the layout, entry (row, place) of
    its main table is `R.M j` at that row and place, and of its mask table `R.Z j`. The value is 0
    on the rows from `realRows` on, and at every oracle message that is no member of the layout. No
    clause bounds the place: at an index from the table's size on whose row is a real row, the value
    is what R has at that row and place; it is not set to 0
  `MemsAre S L Dp`: a definition: the members of the plain data are the layout's, number by number,
    with the statement's shapes. Five fields. `lay`: `Dp.L` is L. `found`: an oracle message that L
    finds at number i is the `id` of entry i of `Dp.mems`, which is there. `finds`: L finds the `id`
    of entry i at number i. `shape`: S has an oracle message at that `id`, and its shape is the
    entry's `sh`. `kept`: L marks no entry's number as kept
  `MemsAre.rows`: under `MemsAre`, at each member and table, `realRows`, `S.rowBits` and `S.has` are
    the number of rows that `sh` states, its `ceilLog2`, and whether it is above 0
  `cut_index`: if idx < 2 ^ (a + pb), then idx % 2 ^ a < 2 ^ a and idx / 2 ^ a < 2 ^ pb; here a
    and pb are numbers

By what. On a real row: the fields `main` and `mask` of `StateAt`. On a row of a member's block
from `realRows` on: the fields `freeM` and `freeZ` of `StateAt`, which give 0 on a row that is among
no member's real rows. That the row is among none: for the member itself by the case; for another
member by the fields `main_block_of`, `mask_block_of`, `main_apart` and `mask_apart` of `LayFacts`
(Johnson/Desc/Means/Layout.lean) and by `le_two_pow_ceilLog2` (OnBytes/Slice/ProgCodes.lean). That
row and place are within the stage's tables: `cut_index`, the fields `mem_of_find`, `main_block`,
`mask_block`, `main_places` and `mask_places` of `LayFacts`, and the four equations on numbers.

Hypotheses. Those of `laidOn_state`. F: `LayFacts S G L`, the library's facts on the layout: it
finds just the members of G; a block that is stated is of a table that is there, is aligned and is
within the group's table; a table that is there has a block (a main table: if the member is not
kept); two members' blocks do not overlap; the members' tables have the layout's numbers of place
bits. `layFacts` (Layout.lean) proves them of the layout that a statement gives a group that meets
`GroupOk` (Says.lean). hS: `StateAt a Dp P R`. M: `MemsAre S L Dp`. The layout's four numbers are
the stage's: hk: `L.k = kk a`; hh: `L.h = a.h`; hl: `2 ^ L.logEll = a.C.l`; hz:
`2 ^ L.logEllZk = a.Z.l`.

Limits. `MemsAre` is asked: a public clause. This file proves it of no plain data; `memsAre_of`
(BatState.lean) proves it under hypotheses of its own. No member is kept: the field `kept` of
`MemsAre` says so of the layout, the clause `kept_at` of `LaidOn` then holds vacuously, and the
theorem is vacuous at a layout that has a kept member. Beyond a table's end `wordsAt` is not set to
0 (see the list); `laidOn_state` speaks only of the indices below the size of a member's table.
Nothing says that a row says its claim of these words (`Says`, `AllSay`, Says.lean); `bat_claimTrue`
has that as a further hypothesis. Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.K12.Honest.BatValues
import OnBytes.Slice.ProgCodes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Means Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.First
open Johnson.Prover.Link (PS)

/-- The words that the plain rows make: at a member of the layout the rows' entries, and 0 on the
rows from `realRows` on; 0 at every other oracle message. The place is not bounded: beyond a table's
end, on a real row, the value is what R has there. -/
def wordsAt (S : Statement) (L : GroupLayout) (R : PlainRows) : Words GE := fun o part idx =>
  match L.find o with
  | some j =>
    if idx % 2 ^ S.rowBits o part < realRows S o part then
      (match part with
        | .main => R.M j (idx % 2 ^ S.rowBits o part) (idx / 2 ^ S.rowBits o part)
        | .mask => R.Z j (idx % 2 ^ S.rowBits o part) (idx / 2 ^ S.rowBits o part))
    else 0
  | none => 0

/-- The plain data's members are the layout's, number by number, with the statement's shapes, and
the layout marks none of them as kept. -/
structure MemsAre (S : Statement) (L : GroupLayout) (Dp : Plain) : Prop where
  lay : Dp.L = L
  found : ∀ o i, L.find o = some i → ∃ hi : i < Dp.mems.length, (Dp.mems.get ⟨i, hi⟩).id = o
  finds : ∀ i : Fin Dp.mems.length, L.find (Dp.mems.get i).id = some i.val
  shape : ∀ i : Fin Dp.mems.length,
    ∃ x, S.oracles[(Dp.mems.get i).id]? = some x ∧ x.shape = (Dp.mems.get i).sh
  kept : ∀ i : Fin Dp.mems.length, L.kept.getD i.val false = false

section
variable {S : Statement} {L : GroupLayout} {Dp : Plain}

theorem MemsAre.rows (M : MemsAre S L Dp) (i : Fin Dp.mems.length) (part : Part) :
    realRows S (Dp.mems.get i).id part = (Dp.mems.get i).sh.rows part ∧
      S.rowBits (Dp.mems.get i).id part = ceilLog2 ((Dp.mems.get i).sh.rows part) ∧
      S.has (Dp.mems.get i).id part = decide (0 < (Dp.mems.get i).sh.rows part) := by
  obtain ⟨x, hx, ex⟩ := M.shape i
  unfold realRows Statement.rowBits Statement.has
  rw [hx]
  dsimp only
  rw [ex]
  exact ⟨rfl, rfl, rfl⟩

/-- An index of a table, cut into its row and its place. -/
theorem cut_index (idx a pb : ℕ) (h : idx < 2 ^ (a + pb)) :
    idx % 2 ^ a < 2 ^ a ∧ idx / 2 ^ a < 2 ^ pb :=
  ⟨Nat.mod_lt _ (Nat.two_pow_pos _), Nat.div_lt_of_lt_mul (by rw [← pow_add]; exact h)⟩

end

/-- **The state's tables hold the words on the members' blocks.** -/
theorem laidOn_state {S : Statement} {G : Group} {L : GroupLayout} (F : LayFacts S G L)
    (a : Fmt.M1.Stage) (Dp : Plain) (P : PS) (R : PlainRows) (hS : StateAt a Dp P R)
    (M : MemsAre S L Dp) (hk : L.k = kk a) (hh : L.h = a.h) (hl : 2 ^ L.logEll = a.C.l)
    (hz : 2 ^ L.logEllZk = a.Z.l) : LaidOn S L (wordsAt S L R) (tabsOf P) := by
  obtain rfl := M.lay
  refine ⟨fun o i first hf _ hm idx hi => ?_, fun o i first hf hm idx hi => ?_,
    fun o i hf hkept => ?_⟩
  · -- the main table
    obtain ⟨hi', rfl⟩ := M.found o i hf
    obtain ⟨r1, r2, r3⟩ := M.rows ⟨i, hi'⟩ .main
    obtain ⟨hhas, -, hB⟩ := F.main_block _ i first hf hm
    have hpl := F.main_places _ (F.mem_of_find _ i hf) hhas
    unfold tableSize at hi
    rw [if_pos hhas] at hi
    unfold Statement.tableBits at hi
    rw [hpl] at hi
    obtain ⟨c1, c2⟩ := cut_index idx _ _ hi
    rw [hl] at c2
    have hoM : oM Dp.L i = first := by
      unfold oM
      rw [hm]
      rfl
    show P.tabM (groupIndex idx _ first Dp.L.k) = wordsAt S Dp.L R _ .main idx
    unfold wordsAt groupIndex
    rw [hf, hk, Nat.mul_comm]
    dsimp only
    by_cases hr : idx % 2 ^ S.rowBits (Dp.mems.get ⟨i, hi'⟩).id .main <
        realRows S (Dp.mems.get ⟨i, hi'⟩).id .main
    · rw [if_pos hr, ← hoM]
      exact hS.main ⟨i, hi'⟩ _ _ (by rw [r1] at hr; exact hr) c2
    · rw [if_neg hr]
      refine (hS.freeM _ (by rw [← hk]; exact lt_of_lt_of_le (Nat.add_lt_add_left c1 _) hB.inside)
        fun j hj => ?_).1 _ c2
      by_cases e : j.val = i
      · obtain rfl : j = ⟨i, hi'⟩ := Fin.ext e
        rw [hoM] at hj
        rw [r1] at hr
        exact hr (Nat.lt_of_add_lt_add_left hj.2)
      · obtain ⟨s1, s2, s3⟩ := M.rows j .main
        have hpos : 0 < (Dp.mems.get j).sh.mainRows := by
          have := hj.1
          have := hj.2
          omega
        have hhas' : S.has (Dp.mems.get j).id .main = true := by
          rw [s3]
          exact decide_eq_true hpos
        obtain ⟨first', hm'⟩ := F.main_block_of _ j.val (M.finds j) hhas' (M.kept j)
        have hoM' : oM Dp.L j.val = first' := by
          unfold oM
          rw [hm']
          rfl
        have hne : (Dp.mems.get ⟨i, hi'⟩).id ≠ (Dp.mems.get j).id := fun h => by
          have k := M.finds j
          rw [← h, hf] at k
          exact e (Option.some.inj k).symm
        have hle : (Dp.mems.get j).sh.mainRows ≤ 2 ^ S.rowBits (Dp.mems.get j).id .main := by
          rw [s2]
          exact le_two_pow_ceilLog2 _
        rw [hoM'] at hj
        have h1 := hj.1
        have h2 := hj.2
        rcases F.main_apart _ _ i j.val first first' hne hf (M.finds j) hm hm' with h | h <;> omega
  · -- the mask table
    obtain ⟨hi', rfl⟩ := M.found o i hf
    obtain ⟨r1, r2, r3⟩ := M.rows ⟨i, hi'⟩ .mask
    obtain ⟨hhas, hB⟩ := F.mask_block _ i first hf hm
    have hpl := F.mask_places _ (F.mem_of_find _ i hf) hhas
    unfold tableSize at hi
    rw [if_pos hhas] at hi
    unfold Statement.tableBits at hi
    rw [hpl] at hi
    obtain ⟨c1, c2⟩ := cut_index idx _ _ hi
    rw [hz] at c2
    have hoZ : oZ Dp.L i = first := by
      unfold oZ
      rw [hm]
      rfl
    show P.tabZ (groupIndex idx _ first Dp.L.h) = wordsAt S Dp.L R _ .mask idx
    unfold wordsAt groupIndex
    rw [hf, hh, Nat.mul_comm]
    dsimp only
    by_cases hr : idx % 2 ^ S.rowBits (Dp.mems.get ⟨i, hi'⟩).id .mask <
        realRows S (Dp.mems.get ⟨i, hi'⟩).id .mask
    · rw [if_pos hr, ← hoZ]
      exact hS.mask ⟨i, hi'⟩ _ _ (by rw [r1] at hr; exact hr) c2
    · rw [if_neg hr]
      refine (hS.freeZ _ (by rw [← hh]; exact lt_of_lt_of_le (Nat.add_lt_add_left c1 _) hB.inside)
        fun j hj => ?_).1 _ c2
      by_cases e : j.val = i
      · obtain rfl : j = ⟨i, hi'⟩ := Fin.ext e
        rw [hoZ] at hj
        rw [r1] at hr
        exact hr (Nat.lt_of_add_lt_add_left hj.2)
      · obtain ⟨s1, s2, s3⟩ := M.rows j .mask
        have hpos : 0 < (Dp.mems.get j).sh.maskRows := by
          have := hj.1
          have := hj.2
          omega
        have hhas' : S.has (Dp.mems.get j).id .mask = true := by
          rw [s3]
          exact decide_eq_true hpos
        obtain ⟨first', hm'⟩ := F.mask_block_of _ j.val (M.finds j) hhas'
        have hoZ' : oZ Dp.L j.val = first' := by
          unfold oZ
          rw [hm']
          rfl
        have hne : (Dp.mems.get ⟨i, hi'⟩).id ≠ (Dp.mems.get j).id := fun h => by
          have k := M.finds j
          rw [← h, hf] at k
          exact e (Option.some.inj k).symm
        have hle : (Dp.mems.get j).sh.maskRows ≤ 2 ^ S.rowBits (Dp.mems.get j).id .mask := by
          rw [s2]
          exact le_two_pow_ceilLog2 _
        rw [hoZ'] at hj
        have h1 := hj.1
        have h2 := hj.2
        rcases F.mask_apart _ _ i j.val first first' hne hf (M.finds j) hm hm' with h | h <;> omega
  · -- no member is kept
    obtain ⟨hi', -⟩ := M.found o i hf
    rw [M.kept ⟨i, hi'⟩] at hkept
    cases hkept

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.MemsAre.rows
#print axioms ProofFile.Honest.K12.cut_index
#print axioms ProofFile.Honest.K12.laidOn_state
#print axioms ProofFile.Honest.K12.wordsAt
#print axioms ProofFile.Honest.K12.MemsAre
