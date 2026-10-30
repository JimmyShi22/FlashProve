-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkCsLay.lean: the layout of a group with one member, and the batching on it.

After a code switch the program's proximity test goes on with a new group, whose one member is the
new oracle message. A group puts its members' tables into two tables of its own
(OnBytes/Iop/Ground.lean: `Statement.layout`, `groupIndex`), and the batching carries each row's
coefficients there (OnBytes/Iop/Bat.lean: `Bat.combine`; its laws: OnBytes/Iop/RowLaws.lean).

What this file shows.
 The layout (`layBlocks_one`, `layout_one`, `CsRan.lay_eq`). A member with 2^a main rows and 2^b
   mask rows begins at the row 0 in both tables. The group's mask table has 2^b rows. Its main
   table has 2^k rows with k = max (max a b) 1: at least two rows, also where the member has one.
 The batching on such a group (`combine_one_main`, `combine_one_mask`, `combine_one_target`). At the
   place to which an entry of a table of the member goes, the batched row has the sum of the rows'
   coefficients on that entry under the powers of the drawn element; the same holds for the target.
 The rows of a switch (`CsRan.fits`). If the group had no member and no row, every row that a run of
   the code switch batches meets the condition `RowFits` of these laws: the claims because the call
   that adds a row has tested them, the sample row by its construction.
 Together (`CsRan.bat_main`, `CsRan.bat_mask`, `CsRan.bat_target`): what a run of the code switch
   returns, on both tables and in the target.

Main theorems: those named above; `find_one`, `one_blocksOk`, `one_weight`, `one_weight_other`;
`CsTaken.stJ_shape`, `CsTaken.stR_shape`, `CsRan.group_stR`, `rowBits_of_shape`,
`CsTaken.rowBits_begun`, `rowBits_le_partBits`.
Not claimed. That the structured vectors on the mask table reach over all places of the group: the
law on the mask table takes it as a hypothesis. Nothing on soundness.
-/
import OnBytes.Slice.BlkCsRun
import OnBytes.Slice.ProgCodes
import OnBytes.Slice.BlkRead
import OnBytes.Iop.RowLaws
import OnBytes.Iop.MaskLaws
import OnBytes.Slice.BlkSend

set_option autoImplicit false

namespace OnBytes.Slice

/-- A loop none of whose steps changes the value leaves it as it was. -/
theorem foldl_same {α β : Type} (f : β → α → β) (b : β) :
    ∀ l : List α, (∀ a ∈ l, f b a = b) → l.foldl f b = b
  | [], _ => rfl
  | a :: l, h => by
    rw [List.foldl_cons, h a (List.mem_cons_self ..)]
    exact foldl_same f b l fun x hx => h x (List.mem_cons_of_mem _ hx)

/-- One block of 2^a rows begins at the row 0 and takes 2^a rows. -/
theorem layBlocks_one (a : ℕ) : layBlocks #[some a] = (#[some 0], 2 ^ a) := by
  unfold layBlocks
  have htop : (#[some a] : Array (Option ℕ)).foldl (fun m s => max m (s.getD 0)) 0 = a := by
    simp
  simp only [htop]
  rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
    List.foldl_cons]
  have hfirst : (List.range (#[some a] : Array (Option ℕ)).size).foldl
      (fun (acc : Array (Option ℕ) × ℕ) i =>
        if (#[some a] : Array (Option ℕ)).getD i none == some a then
          (acc.1.setIfInBounds i (some acc.2), acc.2 + 2 ^ a)
        else acc) (Array.replicate (#[some a] : Array (Option ℕ)).size none, 0)
      = (#[some 0], 2 ^ a) := by
    simp [List.range_succ]
  rw [hfirst]
  refine foldl_same _ _ _ fun e he => ?_
  have hlt : e < a := List.mem_range.1 (List.mem_reverse.1 he)
  have hne : ¬ (a = e) := by omega
  simp [List.range_succ, hne]

/-- The layout of a group with one member, which has 2^a main rows and 2^b mask rows and is not
kept. The group's main table has at least two rows. -/
theorem layout_one (S : Statement) (g o a b : ℕ) (G : Group) (x : Oracle)
    (hG : S.groups[g]? = some G) (hm : G.members = #[o]) (hk : G.kept = #[false])
    (hx : S.oracles[o]? = some x) (hmain : x.shape.mainRows = 2 ^ a)
    (hmask : x.shape.maskRows = 2 ^ b) :
    S.layout g = some
      { k := max (max a b) 1, h := b
        logEll := (S.codes.base.getD G.code default).logEll
        logEllZk := (S.codes.mask.getD G.maskCode default).logEll
        members := #[o], kept := #[false], mainFirst := #[some 0], maskFirst := #[some 0] } := by
  have pa : 0 < 2 ^ a := Nat.two_pow_pos a
  have pb : 0 < 2 ^ b := Nat.two_pow_pos b
  have hsz : G.members.size = 1 := by rw [hm]; rfl
  have hr1 : Array.range 1 = #[0] := rfl
  unfold Statement.layout
  rw [hG]
  simp only [Option.map_some, hsz, hr1]
  simp [hm, hk, Statement.has, Statement.rowBits, hx, OracleShape.rows, hmain, hmask, pa, pb,
    layBlocks_one, ceilLog2_two_pow]

/-! ## The batching on a group with one member, the main table and the target -/

section
variable (S : Statement) (L : GroupLayout) (o a : ℕ)

/-- The place of an oracle message among the members, if there is one member. -/
theorem find_one (hmem : L.members = #[o]) (o' : ℕ) :
    L.find o' = if o' = o then some 0 else none := by
  unfold GroupLayout.find
  rw [hmem]
  by_cases h : o' = o
  · subst h
    simp
  · have h' : ¬ (o = o') := fun e => h e.symm
    simp [h, h']

/-- The one member's block of main rows is aligned and lies in the group's table. -/
theorem one_block (ha : a ≤ L.k) : BlockOk a 0 L.k :=
  ⟨Nat.zero_mod _, by rw [Nat.zero_add]; exact Nat.pow_le_pow_right (by omega) ha⟩

/-- The same, as the laws on the batching ask it. -/
theorem one_blocksOk (hmem : L.members = #[o]) (hfirst : L.mainFirst = #[some 0])
    (hrb : S.rowBits o .main = a) (ha : a ≤ L.k) : MainBlocksOk S L := by
  intro o' i first hf hm
  rw [find_one L o hmem] at hf
  by_cases h : o' = o
  · rw [if_pos h] at hf
    obtain rfl := Option.some.inj hf
    rw [hfirst] at hm
    obtain rfl : 0 = first := Option.some.inj hm
    rw [h, hrb]
    exact one_block L a ha
  · rw [if_neg h] at hf
    cases hf

/-- The place to which an entry of the member goes lies in the member's block. -/
theorem one_weight (hmem : L.members = #[o]) (hkept : L.kept = #[false])
    (hfirst : L.mainFirst = #[some 0]) (hrb : S.rowBits o .main = a) (ha : a ≤ L.k) (idx : ℕ) :
    mainWeight (K := GE) S L o (groupIndex idx a 0 L.k) = 1 := by
  have hb : BlockOk (S.rowBits o .main) 0 L.k := by rw [hrb]; exact one_block L a ha
  rw [mainWeight_rows S L o 0 0 _ (by rw [find_one L o hmem, if_pos rfl]) (by rw [hkept]; rfl)
    (by rw [hfirst]; rfl) hb, hrb, groupIndex_row idx a 0 L.k (one_block L a ha)]
  have hlt : idx % 2 ^ a < 2 ^ a := Nat.mod_lt _ (Nat.two_pow_pos a)
  rw [if_pos ⟨Nat.zero_le _, by omega⟩]

/-- No other oracle message has a block. -/
theorem one_weight_other (hmem : L.members = #[o]) (o' : ℕ) (h : o' ≠ o) (J : ℕ) :
    mainWeight (K := GE) S L o' J = 0 := by
  unfold mainWeight
  rw [find_one L o hmem, if_neg h]

/-- The batching on a group with one member, on the main table: at the place to which entry idx
of the member's main table goes, the batched row has the sum of the rows' coefficients on that entry
under the powers of x. Each row must meet `RowFits`. -/
theorem combine_one_main (g : ℕ) (input : RunInput) (x : E) (out : GroupRow)
    (h : Bat.combine S g input x = some out) (hr : ∀ r ∈ input.rows.toList, RowFits S r)
    (hmem : input.layout.members = #[o]) (hkept : input.layout.kept = #[false])
    (hfirst : input.layout.mainFirst = #[some 0]) (hrb : S.rowBits o .main = a)
    (ha : a ≤ input.layout.k) (idx : ℕ) :
    formAt out.c (groupIndex idx a 0 input.layout.k) =
      hornerSum (readE x) (input.rows.toList.map fun r => coefAt r o .main idx) := by
  have h1 := combine_main_member rdE S g input x out h
    (one_blocksOk S input.layout o a hmem hfirst hrb ha) hr o (groupIndex idx a 0 input.layout.k)
    (one_weight S input.layout o a hmem hkept hfirst hrb ha idx)
    (fun o' ho' => one_weight_other S input.layout o hmem o' ho' _)
  have hback : mainBack S input.layout o (groupIndex idx a 0 input.layout.k) = idx := by
    unfold mainBack
    rw [hrb]
    exact unshift_groupIndex idx a 0 input.layout.k (one_block input.layout a ha)
  rw [hback] at h1
  simp only [rdE_val] at h1
  exact h1

/-- The same for the target. -/
theorem combine_one_target (g : ℕ) (input : RunInput) (x : E) (out : GroupRow)
    (h : Bat.combine S g input x = some out) (hr : ∀ r ∈ input.rows.toList, RowFits S r) :
    readE out.target = hornerSum (readE x) (input.rows.toList.map fun r => readE r.target) := by
  have h1 := combine_target rdE S g input x out h hr
  simp only [rdE_val] at h1
  exact h1

/-! ### The mask table -/

/-- The one member's block of mask rows is aligned and lies in the group's table. -/
theorem one_maskBlock (hb : a ≤ L.h) : BlockOk a 0 L.h :=
  ⟨Nat.zero_mod _, by rw [Nat.zero_add]; exact Nat.pow_le_pow_right (by omega) hb⟩

/-- The same, as the laws on the batching ask it. -/
theorem one_maskBlocksOk (hmem : L.members = #[o]) (hfirst : L.maskFirst = #[some 0])
    (hrb : S.rowBits o .mask = a) (hb : a ≤ L.h) : MaskBlocksOk S L := by
  intro o' i first hf hm
  rw [find_one L o hmem] at hf
  by_cases h : o' = o
  · rw [if_pos h] at hf
    obtain rfl := Option.some.inj hf
    rw [hfirst] at hm
    obtain rfl : 0 = first := Option.some.inj hm
    rw [h, hrb]
    exact one_maskBlock L a hb
  · rw [if_neg h] at hf
    cases hf

/-- The place to which an entry of the member's mask table goes lies in the member's block. -/
theorem one_maskWeight (hmem : L.members = #[o]) (hfirst : L.maskFirst = #[some 0])
    (hrb : S.rowBits o .mask = a) (hb : a ≤ L.h) (idx : ℕ) :
    maskWeight (K := GE) S L o (groupIndex idx a 0 L.h) = 1 := by
  have hbl : BlockOk (S.rowBits o .mask) 0 L.h := by rw [hrb]; exact one_maskBlock L a hb
  rw [maskWeight_rows S L o 0 0 _ (by rw [find_one L o hmem, if_pos rfl]) (by rw [hfirst]; rfl)
    hbl, hrb, groupIndex_row idx a 0 L.h (one_maskBlock L a hb)]
  have hlt : idx % 2 ^ a < 2 ^ a := Nat.mod_lt _ (Nat.two_pow_pos a)
  rw [if_pos ⟨Nat.zero_le _, by omega⟩]

/-- No other oracle message has a block of mask rows. -/
theorem one_maskWeight_other (hmem : L.members = #[o]) (o' : ℕ) (h : o' ≠ o) (J : ℕ) :
    maskWeight (K := GE) S L o' J = 0 := by
  unfold maskWeight
  rw [find_one L o hmem, if_neg h]

/-- The batching on a group with one member, on the mask table: at the place to which entry idx
of the member's mask table goes, the batched row has the sum of the rows' coefficients on that entry
under the powers of x. Each row must meet `RowFits` and `MaskFits`, and the place must be within the
index bits of the group's mask table. -/
theorem combine_one_mask (g : ℕ) (input : RunInput) (x : E) (out : GroupRow)
    (h : Bat.combine S g input x = some out)
    (hr : ∀ r ∈ input.rows.toList, RowFits S r ∧ MaskFits S input.layout r)
    (hmem : input.layout.members = #[o]) (hfirst : input.layout.maskFirst = #[some 0])
    (hrb : S.rowBits o .mask = a) (hb : a ≤ input.layout.h) (idx : ℕ)
    (hJ : groupIndex idx a 0 input.layout.h < 2 ^ (input.layout.h + input.layout.logEllZk)) :
    readV out.d (groupIndex idx a 0 input.layout.h) =
      hornerSum (readE x) (input.rows.toList.map fun r => coefAt r o .mask idx) := by
  have h1 := combine_mask_member rdE S g input x out h
    (one_maskBlocksOk S input.layout o a hmem hfirst hrb hb) hr o
    (groupIndex idx a 0 input.layout.h) hJ
    (one_maskWeight S input.layout o a hmem hfirst hrb hb idx)
    (fun o' ho' => one_maskWeight_other S input.layout o hmem o' ho' _)
  have hback : maskBack S input.layout o (groupIndex idx a 0 input.layout.h) = idx := by
    unfold maskBack
    rw [hrb]
    exact unshift_groupIndex idx a 0 input.layout.h (one_maskBlock input.layout a hb)
  rw [hback] at h1
  simp only [rdE_val] at h1
  exact h1

end

/-! ## The group after a run of the code switch -/

section
variable {old : SingleRows} {T : SwitchTarget} {gp : ℕ} {others : Array OracleNotice} {c c' : Ctx}
  {out : Switched} {row : GroupRow} {lay : GroupLayout} {theta : E} {D : CsTaken}

/-- Closing a ledger leaves the codes and the shapes as they were. -/
theorem ledgerShut_shape (S : Statement) (T : SwitchTarget) (g o : ℕ) :
    (ledgerShut S T g).codes = S.codes ∧
      ((ledgerShut S T g).oracles[o]?).map (·.shape) = (S.oracles[o]?).map (·.shape) := by
  unfold ledgerShut
  split
  · refine ⟨rfl, ?_⟩
    unfold closeLedgers
    simp only [List.foldl_cons, List.foldl_nil, Array.getElem?_modify]
    split
    · rw [Option.map_map]
      rfl
    · rfl
  · exact ⟨rfl, rfl⟩

/-- The codes, and the shape of the new oracle message, in the statement in which it has joined its
group. -/
theorem CsTaken.stJ_shape (D : CsTaken) (T : SwitchTarget) (gp : ℕ) (others : Array OracleNotice)
    (c : Ctx) :
    (D.stJ T gp others c).codes = c.st.codes ∧
      ((D.stJ T gp others c).oracles[c.st.oracles.size]?).map (·.shape) = some T.shape := by
  have h1 := ledgerShut_shape (D.stA T others c) T c.st.oracles.size c.st.oracles.size
  constructor
  · exact h1.1
  · have h2 : ((D.stJ T gp others c).oracles[c.st.oracles.size]?).map (·.shape) =
        ((ledgerShut (D.stA T others c) T c.st.oracles.size).oracles[c.st.oracles.size]?).map
          (·.shape) := by
      unfold CsTaken.stJ withMessageInGroup
      simp only [Array.getElem?_modify, if_true, Option.map_map]
      rfl
    rw [h2, h1.2]
    unfold CsTaken.stA admitted sentOf
    simp only [Array.getElem?_modify, if_true, Option.map_map, sent_first]
    rfl

/-- The same in the statement with the claims. -/
theorem CsTaken.stR_shape (D : CsTaken) (T : SwitchTarget) (gp : ℕ) (others : Array OracleNotice)
    (c : Ctx) :
    (D.stR T gp others c).codes = c.st.codes ∧
      ((D.stR T gp others c).oracles[c.st.oracles.size]?).map (·.shape) = some T.shape := by
  obtain ⟨h1, h2⟩ := D.stJ_shape T gp others c
  obtain ⟨w1, w2⟩ := withRows_oracles gp D.rows (D.stJ T gp others c)
  unfold CsTaken.stR
  rw [w1, w2]
  exact ⟨h1, h2⟩

/-- The group, in the statement with the claims. -/
theorem CsRan.group_stR (h : CsRan old T gp others c c' out row lay theta D) :
    (D.stR T gp others c).groups[gp]? = some (D.grown c) := by
  unfold CsTaken.stR CsTaken.stJ
  rw [withRows_group gp D.rows _ _ (joined_group _ gp c.st.oracles.size false D.G h.group)]
  rfl

/-- The layout that a switch into a stage returns, for a group that had no member: the new
oracle message's 2^a main rows and 2^b mask rows begin at the row 0 of the group's tables. The
group's main table has at least two rows. -/
theorem CsRan.lay_eq {nc nz a b : ℕ}
    (h : CsRan old (switchTargetStage nc nz a b 1) gp others c c' out row lay theta D)
    (hm : D.G.members = #[]) (hk : D.G.kept = #[]) :
    lay = { k := max (max a b) 1, h := b
            logEll := (c.st.codes.base.getD D.G.code default).logEll
            logEllZk := (c.st.codes.mask.getD D.G.maskCode default).logEll
            members := #[c.st.oracles.size], kept := #[false]
            mainFirst := #[some 0], maskFirst := #[some 0] } := by
  obtain ⟨hcodes, hshape⟩ := D.stR_shape (switchTargetStage nc nz a b 1) gp others c
  obtain ⟨x, hx1, hx2⟩ : ∃ x, (D.stR (switchTargetStage nc nz a b 1) gp others c).oracles[
      c.st.oracles.size]? = some x ∧ x.shape = (switchTargetStage nc nz a b 1).shape := by
    cases hx : (D.stR (switchTargetStage nc nz a b 1) gp others c).oracles[c.st.oracles.size]? with
    | none => rw [hx] at hshape; cases hshape
    | some x => rw [hx] at hshape; exact ⟨x, rfl, Option.some.inj hshape⟩
  have hmem : (D.grown c).members = #[c.st.oracles.size] := by
    unfold CsTaken.grown
    simp [hm, Array.insertIdxIfInBounds]
  have hkept : (D.grown c).kept = #[false] := by
    unfold CsTaken.grown
    simp [hm, hk, Array.insertIdxIfInBounds]
  have hl := layout_one _ gp c.st.oracles.size a b (D.grown c) x h.group_stR hmem hkept hx1
    (by rw [hx2]; rfl) (by rw [hx2]; rfl)
  rw [h.layout, hcodes] at hl
  exact Option.some.inj hl

/-! ## The rows that the switch batches meet the conditions of the laws on batching -/

/-- The row bits of a table, from the oracle message's shape. -/
theorem rowBits_of_shape (S : Statement) (o : ℕ) (sh : OracleShape) (part : Part)
    (h : (S.oracles[o]?).map (·.shape) = some sh) : S.rowBits o part = ceilLog2 (sh.rows part) := by
  unfold Statement.rowBits
  cases hx : S.oracles[o]? with
  | none => rw [hx] at h; cases h
  | some x =>
    rw [hx] at h
    show ceilLog2 (x.shape.rows part) = _
    rw [show x.shape = sh from Option.some.inj h]

/-- The row bits in the statement in which the batching is done are those in the statement in which
the new oracle message has joined its group. -/
theorem CsTaken.rowBits_begun (D : CsTaken) (T : SwitchTarget) (gp : ℕ)
    (others : Array OracleNotice) (c : Ctx) (o : ℕ) (part : Part) :
    (begun (D.stR T gp others c) gp (D.grown c)).rowBits o part
      = (D.stJ T gp others c).rowBits o part := by
  rw [begun_rowBits]
  unfold Statement.rowBits CsTaken.stR
  rw [(withRows_oracles gp D.rows _).1]

/-- A table of an oracle message has at least its row bits among the index bits on the cube. -/
theorem rowBits_le_partBits (codes : Codes) (sh : OracleShape) (part : Part)
    (h : hasPart (Send.cube codes sh) part = true) :
    ceilLog2 (sh.rows part) ≤ partBits (Send.cube codes sh) part := by
  cases part
  · have h' : (Send.cube codes sh).hasMain = true := h
    show ceilLog2 sh.mainRows ≤ (Send.cube codes sh).mainBits
    rw [cube_mainBits_eq, cube_mainRowBits_eq, h']
    exact Nat.le_add_right _ _
  · have h' : (Send.cube codes sh).hasMask = true := h
    show ceilLog2 sh.maskRows ≤ (Send.cube codes sh).maskBits
    rw [cube_maskBits_eq, cube_maskRowBits_eq, h']
    exact Nat.le_add_right _ _

/-- Every row that the switch batches meets the conditions of the laws on batching, if the group
had no member and no row. -/
theorem CsRan.fits (h : CsRan old T gp others c c' out row lay theta D)
    (hm : D.G.members = #[]) (hr : D.G.rows = #[]) :
    ∀ r ∈ (runRows (D.stR T gp others c) (D.grown c)).toList,
      RowFits (begun (D.stR T gp others c) gp (D.grown c)) r := by
  have hclaim : ∀ r ∈ D.rows, RowFits (begun (D.stR T gp others c) gp (D.grown c)) r :=
    fun r hr' => rowFits_congr (D.rowBits_begun T gp others c)
      (rowFits_of_checked (h.kinds r hr').2)
  have hsample : RowFits (begun (D.stR T gp others c) gp (D.grown c)) D.sample := by
    refine rowFits_target _ _ (rowFits_form c.st.codes T.shape c.st.oracles.size ⟨D.z T c, D.beta⟩ 0
      D.smp h.form _ ?_ fun part hp => ?_) D.alpha
    · have h1 := congrArg List.length h.seed
      rw [List.length_drop] at h1
      show _ ≤ (D.z T c).length
      unfold CsTaken.z
      rw [List.length_take]
      simp only [List.length_cons, List.length_nil] at h1
      omega
    · rw [D.rowBits_begun T gp others c,
        rowBits_of_shape _ _ T.shape part (D.stJ_shape T gp others c).2]
      exact rowBits_le_partBits c.st.codes T.shape part hp
  intro r hr'
  rw [D.runRows_fresh T gp others c hm hr] at hr'
  simp only [Array.toList_append, Array.toList_filter, List.mem_append, List.mem_filter,
    List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with (⟨h1, _⟩ | rfl) | ⟨h1, _⟩
  · exact hclaim r h1
  · exact hsample
  · exact hclaim r h1

/-- What the switch returns, on the main table: at the place to which entry idx of the new
oracle message's main table goes, the returned row has the sum of the batched rows' coefficients on
that entry under the powers of theta. -/
theorem CsRan.bat_main {nc nz a b : ℕ}
    (h : CsRan old (switchTargetStage nc nz a b 1) gp others c c' out row lay theta D)
    (hm : D.G.members = #[]) (hk : D.G.kept = #[]) (hr : D.G.rows = #[]) (idx : ℕ) :
    formAt row.c (groupIndex idx a 0 (max (max a b) 1)) = hornerSum (readE theta)
      ((runRows (D.stR (switchTargetStage nc nz a b 1) gp others c) (D.grown c)).toList.map
        fun r => coefAt r c.st.oracles.size .main idx) := by
  have hl := h.lay_eq hm hk
  have hrb : (begun (D.stR (switchTargetStage nc nz a b 1) gp others c) gp (D.grown c)).rowBits
      c.st.oracles.size .main = a := by
    rw [D.rowBits_begun, rowBits_of_shape _ _ _ .main (D.stJ_shape _ gp others c).2]
    exact ceilLog2_two_pow a
  have h1 := combine_one_main _ c.st.oracles.size a gp _ theta row h.row (h.fits hm hr)
    (by rw [hl]) (by rw [hl]) (by rw [hl]) hrb (by rw [hl]; show a ≤ max (max a b) 1; omega) idx
  rw [hl] at h1
  exact h1

/-- The same on the mask table, for the entries idx below 2^(b + logEll), with the logEll of the
group's mask code. hmf: every structured vector on a mask table, in the rows that are batched,
reaches over the whole of the group's places. -/
theorem CsRan.bat_mask {nc nz a b : ℕ}
    (h : CsRan old (switchTargetStage nc nz a b 1) gp others c c' out row lay theta D)
    (hm : D.G.members = #[]) (hk : D.G.kept = #[]) (hr : D.G.rows = #[])
    (hmf : ∀ r ∈ (runRows (D.stR (switchTargetStage nc nz a b 1) gp others c) (D.grown c)).toList,
      MaskFits (begun (D.stR (switchTargetStage nc nz a b 1) gp others c) gp (D.grown c)) lay r)
    (idx : ℕ) (hi : idx < 2 ^ (b + (c.st.codes.mask.getD D.G.maskCode default).logEll)) :
    readV row.d (groupIndex idx b 0 b) = hornerSum (readE theta)
      ((runRows (D.stR (switchTargetStage nc nz a b 1) gp others c) (D.grown c)).toList.map
        fun r => coefAt r c.st.oracles.size .mask idx) := by
  have hl := h.lay_eq hm hk
  have hrb : (begun (D.stR (switchTargetStage nc nz a b 1) gp others c) gp (D.grown c)).rowBits
      c.st.oracles.size .mask = b := by
    rw [D.rowBits_begun, rowBits_of_shape _ _ _ .mask (D.stJ_shape _ gp others c).2]
    exact ceilLog2_two_pow b
  have hsame : groupIndex idx b 0 b = idx := by
    unfold groupIndex
    rw [Nat.zero_add, Nat.mul_comm]
    exact Nat.mod_add_div idx (2 ^ b)
  have h1 := combine_one_mask _ c.st.oracles.size b gp _ theta row h.row
    (fun r hr' => ⟨h.fits hm hr r hr', hmf r hr'⟩) (by rw [hl]) (by rw [hl]) hrb
    (by rw [hl]) idx (by rw [hl]; show groupIndex idx b 0 b < _; rw [hsame]; exact hi)
  rw [hl] at h1
  exact h1

/-- The same for the target. -/
theorem CsRan.bat_target (h : CsRan old T gp others c c' out row lay theta D)
    (hm : D.G.members = #[]) (hr : D.G.rows = #[]) :
    readE row.target = hornerSum (readE theta)
      ((runRows (D.stR T gp others c) (D.grown c)).toList.map fun r => readE r.target) :=
  combine_one_target _ gp _ theta row h.row (h.fits hm hr)

end

end OnBytes.Slice

#print axioms OnBytes.Slice.layout_one
#print axioms OnBytes.Slice.combine_one_main
#print axioms OnBytes.Slice.CsRan.lay_eq
#print axioms OnBytes.Slice.CsRan.fits
#print axioms OnBytes.Slice.CsRan.bat_main
#print axioms OnBytes.Slice.CsRan.bat_mask
#print axioms OnBytes.Slice.CsRan.bat_target
#print axioms OnBytes.Slice.foldl_same
#print axioms OnBytes.Slice.layBlocks_one
#print axioms OnBytes.Slice.find_one
#print axioms OnBytes.Slice.one_block
#print axioms OnBytes.Slice.one_blocksOk
#print axioms OnBytes.Slice.one_weight
#print axioms OnBytes.Slice.one_weight_other
#print axioms OnBytes.Slice.combine_one_target
#print axioms OnBytes.Slice.one_maskBlock
#print axioms OnBytes.Slice.one_maskBlocksOk
#print axioms OnBytes.Slice.one_maskWeight
#print axioms OnBytes.Slice.one_maskWeight_other
#print axioms OnBytes.Slice.combine_one_mask
#print axioms OnBytes.Slice.ledgerShut_shape
#print axioms OnBytes.Slice.CsTaken.stJ_shape
#print axioms OnBytes.Slice.CsTaken.stR_shape
#print axioms OnBytes.Slice.CsRan.group_stR
#print axioms OnBytes.Slice.rowBits_of_shape
#print axioms OnBytes.Slice.CsTaken.rowBits_begun
#print axioms OnBytes.Slice.rowBits_le_partBits
