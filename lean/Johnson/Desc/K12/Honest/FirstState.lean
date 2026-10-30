-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Honest/FirstState.lean: if a prover's state by index, at the first stage of a
proximity test, holds the members' rows at the layout's blocks and 0 elsewhere (`StateAt`), then its
message and tails are the members' messages and tails, placed on the stage's tables (`layJ`, `layQ`,
Johnson/Desc/K12/Honest/Group.lean). Here the two equations `μOf s P = layJ G m` and
`ρOf s P = layQ G r`, and two more on `φOf` and `ψOf`, are derived from one proposition on plain
data, at the library's group over the plain data (`GroupAt`,
Johnson/Desc/K12/Honest/FirstReads.lean) and at plain rows (`PlainRows`,
Johnson/Desc/K12/Honest/FirstRows.lean). `first_V` (Johnson/Desc/K12/Honest/FirstValues.lean) calls
all four. General in every parameter: p, a, row, Dp, P and R. Definitions and theorems. It does not
depend on the frame for an honest side (Johnson/Desc/ProofFile/Honest/Frame.lean).

In the list: a (`Fmt.M1.Stage`) is the stage, a free parameter; `first_V` takes a test's first
stage. It has the code `a.C` of a main row, the code `a.Z` of a mask row and the numbers `a.k` and
`a.h`. A code (`Fmt.M1.Code`) takes a message of `l` entries and a tail of `r` entries. `sg a`
(Johnson/Desc/K12/Law/FirstOkLaw.lean) is a in the library's form (`Sg`, OnBytes/Slice/Stage.lean).
The stage's main table has 2 ^ `kk a` rows, where `kk a` is `a.h + (a.k - a.h)`, and its mask table
2 ^ `a.h` rows. The library names a row by a vertex, a function from `Fin n` to `Bool`; `Sz.rowNo`
(OnBytes/Slice/LinkAt.lean) is a vertex's number and `vtx` (OnBytes/Slice/KeyPlaces.lean) a number's
vertex. P (`PS`, Johnson/Prover/Link/BodyState.lean) is the state by index, a structure of functions
of numbers. Of its fields this file reads the two tables `tabM` and `tabZ`, their rows' tails `tM`
and `tZ`, and the rows `fM` and tails `fT` of the fresh table, which has 2 ^ `a.h` rows under `a.Z`
(`Sg.cFr`, Stage.lean). `μOf`, `ρOf`, `φOf` and `ψOf` (BodyState.lean) read off P the message on the
two tables, its tails, the fresh table's message and its tails, as functions on the index types of
`sg a`. Dp (`Plain`, Johnson/Desc/K12/Law/FirstOk.lean) are the group's plain data. Of these this
file reads the members `Dp.mems`, each with its numbers of rows `sh.mainRows` and `sh.maskRows`, and
the layout `Dp.L` (`GroupLayout`, OnBytes/Iop/Ground.lean). `oM Dp.L j` and `oZ Dp.L j`
(FirstOk.lean) are the first rows that the layout states for member j's main rows and mask rows, and
0 where it states none. Member j's block of main rows has `sh.mainRows` rows from `oM Dp.L j` on;
its block of mask rows has `sh.maskRows` rows from `oZ Dp.L j` on. R (`PlainRows`) are rows as
functions of numbers; `msgsOf`, `tailsOf`, `freshOf` and `freshTlOf` (FirstRows.lean) are R on the
index types of the group and of `sg a`. hok says that Dp passes the library's test `gpL`
(FirstOk.lean). p (`P12`, Johnson/Desc/K12/Frame.lean: the numbers of the test's place) and `row`
(`GroupRow`, Ground.lean: a claim on a whole group) enter through that test only. `GroupAt hok` is a
group (`Gp`, OnBytes/Slice/KeyGroup.lean) with the members of Dp: row i of a block has its place at
the vertex of the number (the block's first row) + i. In `layJ` and `layQ`, an entry of the stage's
row b is the sum of that entry over the members' rows whose place is b.

  `muOf_state`: `μOf (sg a) P = layJ (GroupAt hok) (msgsOf R hok)`: the state's message is the
    members' messages, each row at its place
  `rhoOf_state`: `ρOf (sg a) P = layQ (GroupAt hok) (tailsOf R hok)`: the same for the tails
  `phiOf_state`, `psiOf_state`: `φOf (sg a) P = freshOf R (sg a)` and
    `ψOf (sg a) P = freshTlOf R (sg a)`. Their only hypothesis is `StateAt`
  `StateAt a Dp P R`: a definition, a structure of propositions. Member j's main row i stands at row
    (the layout's first main row of j) + i of the state's main table, with its tail; the like for
    mask rows; a row in no member's block is 0, with its tail; the fresh table and its tails are the
    plain rows'. The fields: `main` and `mainT` compare `P.tabM` and `P.tM` with `R.M` and `R.T`;
    `mask` and `maskT` compare `P.tabZ` and `P.tZ` with `R.Z` and `R.ZT`; `freeM` and `freeZ` are
    the two clauses on 0; `fresh` and `freshT` compare `P.fM` and `P.fT` with `R.F` and `R.FT`
  `InBlock o n b`: a definition: the row number b lies in the block of n rows from row o on: o ≤ b
    and b < o + n
  `main_cases`, `mask_cases`: a vertex b of the main table is `vtx` of `oM Dp.L j` + i for some
    member j and some i below its `sh.mainRows`, or the number of b lies in no member's block of
    main rows (`InBlock`). The same for the mask table, with `oZ` and `sh.maskRows`
  `apart_at`: no two rows of `GroupAt hok` have the same place (`Gp.Apart`, KeyGroup.lean)
  `vtx_rowNo`, `rowNo_vtx`: a vertex and its number: `vtx k (Sz.rowNo b) = b`; and
    `Sz.rowNo (vtx k n) = n` where n < 2 ^ k

By what. `muOf_state` and `rhoOf_state` go entry by entry and split by `main_cases` or `mask_cases`.
At a member's row they use `layJ_ent` or `layQ_ent` (Group.lean) under `apart_at`, `rowNo_vtx`, and
the field of `StateAt` for that kind of row. At a row in no block they use `freeM` or `freeZ`, and
`layJ_freeM` or `layJ_freeZ` (Group.lean); for the tails, the text of `layQ`. `apart_at` is
`Gp.Numbered.apart` (KeyPlaces.lean) at four inequalities of `good_of_ok` (FirstOkLaw.lean): each
block has room in its table, and two members' blocks do not overlap. The two on room also bound the
rows' numbers for `rowNo_vtx`. `phiOf_state` and `psiOf_state` are the fields `fresh` and `freshT`.
On vertices and numbers: `testBit_rowNo`, `rowNo_testBit` and `rowNo_lt` (OnBytes/Slice/Cells.lean).

Hypotheses of `muOf_state` and `rhoOf_state`.
  hS: `StateAt a Dp P R`
  hok: `ok (gpL p a row Dp) = true`: every clause of the library's test on the plain data passes

Limits. `StateAt` is a hypothesis: this file proves it of no state. It speaks only of entries below
the codes' lengths and of rows below the tables' heights: of message entries below `l`, tail entries
below `r`, and rows below 2 ^ `kk a` or 2 ^ `a.h`. It does not ask that the members' blocks are
apart, which is part of hok: where two blocks share a row and R gives that row two different entries
below `l`, no state meets it. `main_cases`, `mask_cases` and `apart_at` have `StateAt` as a
hypothesis, through the line `include hS`, and their proofs do not use it. Nothing on completeness,
on soundness or on what is hidden.
-/
import Johnson.Desc.K12.Honest.FirstRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun Cb _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Sw H2K.JointK H2K.First
open Johnson.Prover.Link

/-- The row number b lies in the block of n rows from row o on. -/
def InBlock (o n b : ℕ) : Prop := o ≤ b ∧ b < o + n

/-- The state holds the members' rows at the layout's blocks, and 0 elsewhere. Entry e of row b of
the main table is `P.tabM (b + 2 ^ kk a * e)`, of the mask table `P.tabZ (b + 2 ^ a.h * e)`; entry q
of that row's tail is `P.tM b q`, `P.tZ b q`. -/
structure StateAt (a : Fmt.M1.Stage) (Dp : Plain) (P : PS) (R : PlainRows) : Prop where
  main : ∀ (j : Fin Dp.mems.length) (i e : ℕ), i < (Dp.mems.get j).sh.mainRows → e < a.C.l →
    P.tabM (oM Dp.L j.val + i + 2 ^ kk a * e) = R.M j.val i e
  mainT : ∀ (j : Fin Dp.mems.length) (i q : ℕ), i < (Dp.mems.get j).sh.mainRows → q < a.C.r →
    P.tM (oM Dp.L j.val + i) q = R.T j.val i q
  mask : ∀ (j : Fin Dp.mems.length) (i e : ℕ), i < (Dp.mems.get j).sh.maskRows → e < a.Z.l →
    P.tabZ (oZ Dp.L j.val + i + 2 ^ a.h * e) = R.Z j.val i e
  maskT : ∀ (j : Fin Dp.mems.length) (i q : ℕ), i < (Dp.mems.get j).sh.maskRows → q < a.Z.r →
    P.tZ (oZ Dp.L j.val + i) q = R.ZT j.val i q
  freeM : ∀ b, b < 2 ^ kk a →
    (∀ j : Fin Dp.mems.length, ¬ InBlock (oM Dp.L j.val) (Dp.mems.get j).sh.mainRows b) →
    (∀ e, e < a.C.l → P.tabM (b + 2 ^ kk a * e) = 0) ∧ ∀ q, q < a.C.r → P.tM b q = 0
  freeZ : ∀ b, b < 2 ^ a.h →
    (∀ j : Fin Dp.mems.length, ¬ InBlock (oZ Dp.L j.val) (Dp.mems.get j).sh.maskRows b) →
    (∀ e, e < a.Z.l → P.tabZ (b + 2 ^ a.h * e) = 0) ∧ ∀ q, q < a.Z.r → P.tZ b q = 0
  fresh : ∀ b e, b < 2 ^ a.h → e < a.Z.l → P.fM b e = R.F b e
  freshT : ∀ b q, b < 2 ^ a.h → q < a.Z.r → P.fT b q = R.FT b q

theorem vtx_rowNo {k : ℕ} (b : Fin k → Bool) : vtx k (Sz.rowNo b) = b :=
  funext fun u => testBit_rowNo b u

theorem rowNo_vtx {k n : ℕ} (h : n < 2 ^ k) : Sz.rowNo (vtx k n) = n :=
  (rowNo_testBit k n).trans (Nat.mod_eq_of_lt h)

section
variable {p : P12} {a : Fmt.M1.Stage} {row : GroupRow} {Dp : Plain} {P : PS} {R : PlainRows}
  (hS : StateAt a Dp P R) (hok : ok (gpL p a row Dp) = true)
include hS

/-- A main row of the stage: a member's, or no member's. -/
theorem main_cases (b : Fin ((sg a).h + (sg a).g) → Bool) :
    (∃ (j : Fin Dp.mems.length) (i : Fin (Dp.mems.get j).sh.mainRows),
      b = vtx _ (oM Dp.L j.val + i.val)) ∨
    ∀ j : Fin Dp.mems.length,
      ¬ InBlock (oM Dp.L j.val) (Dp.mems.get j).sh.mainRows (Sz.rowNo b) := by
  by_cases h : ∃ j : Fin Dp.mems.length,
      InBlock (oM Dp.L j.val) (Dp.mems.get j).sh.mainRows (Sz.rowNo b)
  · obtain ⟨j, h1, h2⟩ := h
    refine .inl ⟨j, ⟨Sz.rowNo b - oM Dp.L j.val, by omega⟩, ?_⟩
    show b = vtx _ (oM Dp.L j.val + (Sz.rowNo b - oM Dp.L j.val))
    rw [Nat.add_sub_cancel' h1, vtx_rowNo]
  · exact .inr fun j hj => h ⟨j, hj⟩

/-- A mask row of the stage: a member's, or no member's. -/
theorem mask_cases (b : Fin (sg a).h → Bool) :
    (∃ (j : Fin Dp.mems.length) (i : Fin (Dp.mems.get j).sh.maskRows),
      b = vtx _ (oZ Dp.L j.val + i.val)) ∨
    ∀ j : Fin Dp.mems.length,
      ¬ InBlock (oZ Dp.L j.val) (Dp.mems.get j).sh.maskRows (Sz.rowNo b) := by
  by_cases h : ∃ j : Fin Dp.mems.length,
      InBlock (oZ Dp.L j.val) (Dp.mems.get j).sh.maskRows (Sz.rowNo b)
  · obtain ⟨j, h1, h2⟩ := h
    refine .inl ⟨j, ⟨Sz.rowNo b - oZ Dp.L j.val, by omega⟩, ?_⟩
    show b = vtx _ (oZ Dp.L j.val + (Sz.rowNo b - oZ Dp.L j.val))
    rw [Nat.add_sub_cancel' h1, vtx_rowNo]
  · exact .inr fun j hj => h ⟨j, hj⟩

theorem apart_at : (GroupAt hok).Apart :=
  Gp.Numbered.apart (oM := fun i => oM Dp.L i.val) (oZ := fun i => oZ Dp.L i.val)
    { pM := fun _ _ => rfl
      pZ := fun _ _ => rfl
      roomM := fun i => (good_of_ok p a row Dp hok).roomM i
      roomZ := fun i => (good_of_ok p a row Dp hok).roomZ i
      apartM := fun i j hij => (good_of_ok p a row Dp hok).apartM i j hij
      apartZ := fun i j hij => (good_of_ok p a row Dp hok).apartZ i j hij }

/-- **The state's message is the members' messages, each row at its place.** -/
theorem muOf_state : μOf (sg a) P = layJ (GroupAt hok) (msgsOf R hok) := by
  have hg := good_of_ok p a row Dp hok
  funext x
  rcases x with ⟨b, e⟩ | ⟨b, e⟩
  · rcases main_cases hS b with ⟨j, i, rfl⟩ | hfree
    · have hlt : oM Dp.L j.val + i.val < 2 ^ kk a :=
        lt_of_lt_of_le (Nat.add_lt_add_left i.isLt _) (hg.roomM j)
      refine Eq.trans ?_ (layJ_ent (GroupAt hok) (apart_at hS hok) (msgsOf R hok)
        ⟨j, .inl (i, e)⟩).symm
      show P.tabM (Sz.rowNo (vtx _ (oM Dp.L j.val + i.val)) + 2 ^ kk a * e.val) =
        R.M j.val i.val e.val
      rw [show Sz.rowNo (vtx ((sg a).h + (sg a).g) (oM Dp.L j.val + i.val)) =
        oM Dp.L j.val + i.val from rowNo_vtx hlt]
      exact hS.main j i.val e.val i.isLt e.isLt
    · refine Eq.trans ?_ (layJ_freeM (GroupAt hok) (msgsOf R hok) b (fun n hn => ?_) e).symm
      · exact (hS.freeM _ (rowNo_lt b) hfree).1 e.val e.isLt
      · have hlt : oM Dp.L n.1.val + n.2.val < 2 ^ kk a :=
          lt_of_lt_of_le (Nat.add_lt_add_left n.2.isLt _) (hg.roomM n.1)
        have hb : Sz.rowNo b = oM Dp.L n.1.val + n.2.val := by
          rw [← hn]
          exact rowNo_vtx hlt
        exact hfree n.1 ⟨by rw [hb]; exact Nat.le_add_right _ _,
          by rw [hb]; exact Nat.add_lt_add_left n.2.isLt _⟩
  · rcases mask_cases hS b with ⟨j, i, rfl⟩ | hfree
    · have hlt : oZ Dp.L j.val + i.val < 2 ^ a.h :=
        lt_of_lt_of_le (Nat.add_lt_add_left i.isLt _) (hg.roomZ j)
      refine Eq.trans ?_ (layJ_ent (GroupAt hok) (apart_at hS hok) (msgsOf R hok)
        ⟨j, .inr (i, e)⟩).symm
      show P.tabZ (Sz.rowNo (vtx _ (oZ Dp.L j.val + i.val)) + 2 ^ a.h * e.val) =
        R.Z j.val i.val e.val
      rw [show Sz.rowNo (vtx (sg a).h (oZ Dp.L j.val + i.val)) = oZ Dp.L j.val + i.val from
        rowNo_vtx hlt]
      exact hS.mask j i.val e.val i.isLt e.isLt
    · refine Eq.trans ?_ (layJ_freeZ (GroupAt hok) (msgsOf R hok) b (fun n hn => ?_) e).symm
      · exact (hS.freeZ _ (rowNo_lt b) hfree).1 e.val e.isLt
      · have hlt : oZ Dp.L n.1.val + n.2.val < 2 ^ a.h :=
          lt_of_lt_of_le (Nat.add_lt_add_left n.2.isLt _) (hg.roomZ n.1)
        have hb : Sz.rowNo b = oZ Dp.L n.1.val + n.2.val := by
          rw [← hn]
          exact rowNo_vtx hlt
        exact hfree n.1 ⟨by rw [hb]; exact Nat.le_add_right _ _,
          by rw [hb]; exact Nat.add_lt_add_left n.2.isLt _⟩

/-- **The state's tails are the members' tails, each row's tail at the row's place.** -/
theorem rhoOf_state : ρOf (sg a) P = layQ (GroupAt hok) (tailsOf R hok) := by
  have hg := good_of_ok p a row Dp hok
  funext x
  rcases x with ⟨b, q⟩ | ⟨b, q⟩
  · rcases main_cases hS b with ⟨j, i, rfl⟩ | hfree
    · have hlt : oM Dp.L j.val + i.val < 2 ^ kk a :=
        lt_of_lt_of_le (Nat.add_lt_add_left i.isLt _) (hg.roomM j)
      refine Eq.trans ?_ (layQ_ent (GroupAt hok) (apart_at hS hok) (tailsOf R hok) j
        (.inl (i, q))).symm
      show P.tM (Sz.rowNo (vtx _ (oM Dp.L j.val + i.val))) q.val = R.T j.val i.val q.val
      rw [show Sz.rowNo (vtx ((sg a).h + (sg a).g) (oM Dp.L j.val + i.val)) =
        oM Dp.L j.val + i.val from rowNo_vtx hlt]
      exact hS.mainT j i.val q.val i.isLt q.isLt
    · refine Eq.trans ((hS.freeM _ (rowNo_lt b) hfree).2 q.val q.isLt)
        (Finset.sum_eq_zero fun n _ => if_neg fun hn => ?_).symm
      have hlt : oM Dp.L n.1.val + n.2.val < 2 ^ kk a :=
        lt_of_lt_of_le (Nat.add_lt_add_left n.2.isLt _) (hg.roomM n.1)
      have hb : Sz.rowNo b = oM Dp.L n.1.val + n.2.val := by
        have hn' : _ = b := hn
        rw [← hn']
        exact rowNo_vtx hlt
      exact hfree n.1 ⟨by rw [hb]; exact Nat.le_add_right _ _,
        by rw [hb]; exact Nat.add_lt_add_left n.2.isLt _⟩
  · rcases mask_cases hS b with ⟨j, i, rfl⟩ | hfree
    · have hlt : oZ Dp.L j.val + i.val < 2 ^ a.h :=
        lt_of_lt_of_le (Nat.add_lt_add_left i.isLt _) (hg.roomZ j)
      refine Eq.trans ?_ (layQ_ent (GroupAt hok) (apart_at hS hok) (tailsOf R hok) j
        (.inr (i, q))).symm
      show P.tZ (Sz.rowNo (vtx _ (oZ Dp.L j.val + i.val))) q.val = R.ZT j.val i.val q.val
      rw [show Sz.rowNo (vtx (sg a).h (oZ Dp.L j.val + i.val)) = oZ Dp.L j.val + i.val from
        rowNo_vtx hlt]
      exact hS.maskT j i.val q.val i.isLt q.isLt
    · refine Eq.trans ((hS.freeZ _ (rowNo_lt b) hfree).2 q.val q.isLt)
        (Finset.sum_eq_zero fun n _ => if_neg fun hn => ?_).symm
      have hlt : oZ Dp.L n.1.val + n.2.val < 2 ^ a.h :=
        lt_of_lt_of_le (Nat.add_lt_add_left n.2.isLt _) (hg.roomZ n.1)
      have hb : Sz.rowNo b = oZ Dp.L n.1.val + n.2.val := by
        have hn' : _ = b := hn
        rw [← hn']
        exact rowNo_vtx hlt
      exact hfree n.1 ⟨by rw [hb]; exact Nat.le_add_right _ _,
        by rw [hb]; exact Nat.add_lt_add_left n.2.isLt _⟩

theorem phiOf_state : φOf (sg a) P = freshOf R (sg a) :=
  funext fun x => hS.fresh _ _ (rowNo_lt x.1) x.2.isLt

theorem psiOf_state : ψOf (sg a) P = freshTlOf R (sg a) :=
  funext fun x => hS.freshT _ _ (rowNo_lt x.1) x.2.isLt

end

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.vtx_rowNo
#print axioms ProofFile.Honest.K12.rowNo_vtx
#print axioms ProofFile.Honest.K12.main_cases
#print axioms ProofFile.Honest.K12.mask_cases
#print axioms ProofFile.Honest.K12.apart_at
#print axioms ProofFile.Honest.K12.muOf_state
#print axioms ProofFile.Honest.K12.rhoOf_state
#print axioms ProofFile.Honest.K12.phiOf_state
#print axioms ProofFile.Honest.K12.psiOf_state
#print axioms ProofFile.Honest.K12.InBlock
#print axioms ProofFile.Honest.K12.StateAt
