-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/ManyFitsLaw.lean

What it proves. At the job of a proximity test on a group of several oracle messages (ManyJob,
RunMany.lean, taken as a TestJob by toRun.toTest), at any number of members, with a fresh table that
stands in a member's tree or in its own, and at any number of trees: where the one test on public
things manyFitsB (ManyFits.lean) is true at the shape of the verifier's plain data Dp, the first
three clauses of DataFront (ShapeAll.lean) hold at the job's own rows (plainMany) and columns
(colsMany): StateAt, ColsAt, and "the job's trees are the group's". At every input, whatever
precedes the test, and all random values.

Names.
  Covers, layRows_at, layRows_free, lst_zeros   a row that one block alone covers is that block's; a
      row that no block covers is zeros.
  all_zipIdx, all_zip, ManyFits, manyFits_of_B, apart_of_B, memFits_of_B   what the test says, as
      propositions.
  blocksOf, blocksOf_get, memRows_of, laid_at, laid_free   the members' lists at their blocks.
  idx_mod, idx_div, tabM_many, tM_many, tabZ_many, tZ_many, seat_mem, kk_many, state_many   StateAt.
  getD_mid, read3_mid, wordsAt_three, wordsAt_cat, NoBase, selsOf_main, selsOf_mask, sels_three,
  len_piece, len_pieces, split_of_before, read3_piece   a column's words: row number i of a piece,
      read at the number of words in front of the piece plus 3 i.
  symOf_main, symOf_mask, symOf_fresh   a chosen row's symbol, decoded, is the field's symbol.
  tree_many, col_many, noBase_many, seat_of_B, cols_many, trees_many   ColsAt; the trees.
  dataThree_many   the theorem.

By what. symG_congr, wordsOf, length_wordsOf (Johnson/Prover/Link/Base.lean, SwitchCols.lean);
read3_wordsOf (FreshCols.lean); lst_range, getD_range, sg_k (RunByTab.lean); toE_ofE, toE_zeroE
(OnBytes/Slice/Field.lean); logAtS_eq, widthAtS_eq (Johnson/Desc/K12/Honest/Shape/TestDoor.lean).

Limits.
- RunJob.rowsFit is not asked: plainMany reads the members' lists by the same reader (lst) by which
  the job's state reads the laid lists, so a short or missing row or tail reads 0 on both sides. So
  the three clauses do not tell a member whose lists are short.
- DataFront's fourth clause (what the rows say of the words) is not touched.
- The clauses are on the job's own columns: nothing compares them with what the senders sent.
- Main rows over the extension field alone.
- That manyFitsB is true is shown at no parameters here (ManyFitsAt.lean).
- Nothing on completeness, on soundness or on what a view shows.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.ManyFits
import Johnson.Desc.ProofFile.Honest.K12.TreeIsColumn
import Johnson.Desc.ProofFile.Honest.K12.ShapeAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes.Slice (GE lst toE ofE)
open Fmt.M1 (Stage)
open Fmt.M1.Own (PSt words)
open VerifiableInference.Desc.K12 (P12 T12)
open Johnson.Prover.Link (PS symG symG_congr)
open H2K.First (Plain Seat1 oM oZ skM skZ kk logAt widthAt)
open ProofFile.Honest.K12 (PlainRows TestCoins StateAt ColsAt MemAt InBlock groupTrees read3 read1)
open ProofFile.Honest.Sh (PlainS plainSh logAtS widthAtS logAtS_eq widthAtS_eq)

variable {W X : Type}

/-! ## 1 Rows laid at blocks -/

/-- A block covers a row. -/
def Covers (B : RowBlock) (b : ℕ) : Prop := B.first ≤ b ∧ b < B.first + B.count

instance (B : RowBlock) (b : ℕ) : Decidable (Covers B b) := by
  unfold Covers
  infer_instance

/-- Where block number j covers row b and no other block does, row b is that block's. -/
theorem layRows_at (n len b : ℕ) (hb : b < n) : ∀ (bs : List RowBlock) (j : ℕ) (B : RowBlock),
    bs[j]? = some B → Covers B b → (∀ j' B', bs[j']? = some B' → j' ≠ j → ¬ Covers B' b) →
    (layRows n len bs).getD b [] = B.rows.getD (b - B.first) [] := by
  intro bs j B hj hc hn
  unfold layRows
  rw [getD_range n _ _ b hb]
  have key : ∀ (l : List RowBlock) (i : ℕ), l[i]? = some B →
      (∀ j' B', l[j']? = some B' → j' ≠ i → ¬ Covers B' b) →
      (l.findSome? fun B =>
        if B.first ≤ b ∧ b < B.first + B.count then some (B.rows.getD (b - B.first) [])
        else none) = some (B.rows.getD (b - B.first) []) := by
    intro l
    induction l with
    | nil => intro i h; cases h
    | cons B0 l ih =>
      intro i h hno
      cases i with
      | zero =>
        obtain rfl : B0 = B := Option.some.inj h
        have hc' : B0.first ≤ b ∧ b < B0.first + B0.count := hc
        rw [List.findSome?_cons, if_pos hc']
      | succ i =>
        have h0 : ¬ (B0.first ≤ b ∧ b < B0.first + B0.count) := hno 0 B0 rfl (by omega)
        rw [List.findSome?_cons, if_neg h0]
        exact ih i h fun j' B' hj' hne => hno (j' + 1) B' hj' (by omega)
  rw [key bs j hj hn]
  rfl

/-- A row that no block covers is zeros. -/
theorem layRows_free (n len b : ℕ) (hb : b < n) (bs : List RowBlock)
    (hn : ∀ B ∈ bs, ¬ Covers B b) :
    (layRows n len bs).getD b [] = List.replicate len Fmt.Fld.zeroE := by
  unfold layRows
  rw [getD_range n _ _ b hb]
  have key : (bs.findSome? fun B =>
      if B.first ≤ b ∧ b < B.first + B.count then some (B.rows.getD (b - B.first) [])
      else none) = none := by
    rw [List.findSome?_eq_none_iff]
    intro B hB
    have h0 : ¬ (B.first ≤ b ∧ b < B.first + B.count) := hn B hB
    rw [if_neg h0]
  rw [key]
  rfl

theorem lst_zeros (len e : ℕ) : lst (List.replicate len Fmt.Fld.zeroE) e = 0 := by
  unfold lst
  have h : (List.replicate len Fmt.Fld.zeroE).getD e Fmt.Fld.zeroE = Fmt.Fld.zeroE := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split <;> rfl
  rw [h]
  exact OnBytes.Slice.toE_zeroE

/-! ## 2 What the test says -/

theorem all_zipIdx {α : Type} (l : List α) (f : α × ℕ → Bool) :
    l.zipIdx.all f = true ↔ ∀ (i : ℕ) a, l[i]? = some a → f (a, i) = true := by
  rw [List.all_eq_true]
  constructor
  · intro h i a hi
    exact h (a, i) (List.mem_zipIdx_iff_getElem?.2 hi)
  · intro h x hx
    exact h x.2 x.1 (List.mem_zipIdx_iff_getElem?.1 hx)

theorem all_zip {α β : Type} (l : List α) (l' : List β) (f : α × β → Bool) :
    (l.zip l').all f = true ↔
      ∀ (i : ℕ) a b, l[i]? = some a → l'[i]? = some b → f (a, b) = true := by
  rw [List.all_eq_true]
  constructor
  · intro h i a b ha hb
    refine h (a, b) (List.mem_iff_getElem?.2 ⟨i, ?_⟩)
    rw [List.getElem?_zip_eq_some]
    exact ⟨ha, hb⟩
  · intro h x hx
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hx
    rw [List.getElem?_zip_eq_some] at hi
    exact h i x.1 x.2 hi.1 hi.2

/-- **What the test says**, clause by clause. -/
structure ManyFits (s : Stage) (ms : List MemShape) (trees : List (ℕ × List Piece)) (D : PlainS) :
    Prop where
  hk : s.h ≤ s.k
  len : D.mems.length = ms.length
  mem : ∀ (j : ℕ) m x, ms[j]? = some m → D.mems[j]? = some x → memFitsB s D.L j m x = true
  apartM : apartB₂ (ms.map fun m => (m.mainFirst, m.mainRows)) = true
  apartZ : apartB₂ (ms.map fun m => (m.maskFirst, m.maskRows)) = true
  nodup : D.ts.Nodup
  tlen : D.ts.length = trees.length
  tree : ∀ (i : ℕ) T u, trees[i]? = some T → D.ts[i]? = some u → treeFitsB s ms D T u = true
  seatM : ∀ (j : ℕ) m x, ms[j]? = some m → D.mems[j]? = some x → m.mainRows ≠ 0 →
    seatFitsB s ms trees D.ts x.t (.main j) (skM x.tsh x.part) = true
  seatZ : ∀ (j : ℕ) m x, ms[j]? = some m → D.mems[j]? = some x → m.maskRows ≠ 0 →
    seatFitsB s ms trees D.ts x.t (.mask j) (skZ x.tsh x.part) = true
  fresh : seatFitsB s ms trees D.ts D.fresh.t .fresh (skZ D.fresh.tsh D.fresh.part) = true

theorem manyFits_of_B {s : Stage} {ms : List MemShape} {trees : List (ℕ × List Piece)}
    {D : PlainS} (h : manyFitsB s ms trees D = true) : ManyFits s ms trees D := by
  unfold manyFitsB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  rw [all_zipIdx] at h3 h9
  rw [all_zip] at h8
  refine ⟨h1, h2, fun j m x hm hx => h3 j (m, x) ?_, h4, h5, h6, h7,
    fun i T u hT hu => h8 i T u hT hu, fun j m x hm hx hn => ?_, fun j m x hm hx hn => ?_, h10⟩
  · rw [List.getElem?_zip_eq_some]
    exact ⟨hm, hx⟩
  · have k := h9 j (m, x) (by rw [List.getElem?_zip_eq_some]; exact ⟨hm, hx⟩)
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at k
    exact k.1.resolve_left hn
  · have k := h9 j (m, x) (by rw [List.getElem?_zip_eq_some]; exact ⟨hm, hx⟩)
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at k
    exact k.2.resolve_left hn

/-- Two blocks of a list that passes apartB₂, both with rows, do not share a row. -/
theorem apart_of_B {bs : List (ℕ × ℕ)} (h : apartB₂ bs = true) (i j : ℕ) (a b : ℕ × ℕ)
    (hi : bs[i]? = some a) (hj : bs[j]? = some b) (hne : i ≠ j) (r : ℕ)
    (ha : a.1 ≤ r ∧ r < a.1 + a.2) : ¬ (b.1 ≤ r ∧ r < b.1 + b.2) := by
  unfold apartB₂ at h
  rw [all_zipIdx] at h
  have k := h i a hi
  rw [all_zipIdx] at k
  have k' := k j b hj
  simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at k'
  intro hb
  rcases k' with (((k' | k') | k') | k') | k' <;> omega

theorem memFits_of_B {s : Stage} {L : OnBytes.GroupLayout} {j : ℕ} {m : MemShape} {x : Seat1}
    (h : memFitsB s L j m x = true) :
    x.sh.mainRows = m.mainRows ∧ x.sh.maskRows = m.maskRows ∧
      (m.mainRows ≠ 0 → m.base = false ∧ x.sh.mainDeg ≠ 1 ∧ oM L j = m.mainFirst) ∧
      (m.maskRows ≠ 0 → oZ L j = m.maskFirst) ∧ m.mainFirst + m.mainRows ≤ 2 ^ s.k ∧
      m.maskFirst + m.maskRows ≤ 2 ^ s.h := by
  unfold memFitsB at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne,
    Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, fun hn => ⟨(h3.resolve_left hn).1.1, (h3.resolve_left hn).1.2,
    (h3.resolve_left hn).2⟩, fun hn => h4.resolve_left hn, h5, h6⟩

/-! ## 3 The members' lists at their blocks -/

section Laid
variable (A : ManyJob W X) (w : W) (fr : Front X) (C : TestCoins)
  (sel : MemShape → ℕ × ℕ) (tab : PSt → List (List Fmt.M1.E))

/-- The blocks of one of the stage's four lists. -/
def blocksOf : List RowBlock :=
  (A.mems.zipIdx.map fun m => (m.1.shape, m.1.rows w fr (C.mem m.2))).map fun x =>
    ⟨(sel x.1).1, (sel x.1).2, tab x.2⟩

theorem blocksOf_get (j : ℕ) :
    (blocksOf A w fr C sel tab)[j]? = (A.mems[j]?).map fun m =>
      ⟨(sel m.shape).1, (sel m.shape).2, tab (m.rows w fr (C.mem j))⟩ := by
  unfold blocksOf
  rw [List.getElem?_map, List.getElem?_map, List.getElem?_zipIdx]
  cases A.mems[j]? with
  | none => rfl
  | some m =>
    simp only [Option.map_some, Nat.zero_add]

theorem memRows_of {j : ℕ} {m : Mem W X} (hm : A.mems[j]? = some m) :
    memRows A w fr C j = m.rows w fr (C.mem j) := by
  unfold memRows
  rw [hm]

/-- **A row within member j's block is that member's own.** -/
theorem laid_at (hap : apartB₂ ((A.mems.map (·.shape)).map sel) = true) (n len j : ℕ)
    (m : Mem W X) (hm : A.mems[j]? = some m) (i : ℕ) (hi : i < (sel m.shape).2)
    (hb : (sel m.shape).1 + i < n) :
    (layRows n len (blocksOf A w fr C sel tab)).getD ((sel m.shape).1 + i) [] =
      (tab (memRows A w fr C j)).getD i [] := by
  rw [layRows_at n len _ hb (blocksOf A w fr C sel tab) j
    ⟨(sel m.shape).1, (sel m.shape).2, tab (m.rows w fr (C.mem j))⟩
    (by rw [blocksOf_get, hm]; rfl)
    ⟨Nat.le_add_right _ _, by show (sel m.shape).1 + i < (sel m.shape).1 + (sel m.shape).2; omega⟩
    ?_]
  · show (tab (m.rows w fr (C.mem j))).getD ((sel m.shape).1 + i - (sel m.shape).1) [] = _
    rw [Nat.add_sub_cancel_left, memRows_of A w fr C hm]
  · intro j' B' hj' hne
    rw [blocksOf_get] at hj'
    obtain ⟨m', hm', rfl⟩ := Option.map_eq_some_iff.1 hj'
    exact apart_of_B hap j j' (sel m.shape) (sel m'.shape)
      (by rw [List.getElem?_map, List.getElem?_map, hm]; rfl)
      (by rw [List.getElem?_map, List.getElem?_map, hm']; rfl) (Ne.symm hne) _
      ⟨Nat.le_add_right _ _, by omega⟩

/-- **A row within no member's block is zeros.** -/
theorem laid_free (n len b : ℕ) (hb : b < n)
    (hn : ∀ (j : ℕ) (m : Mem W X), A.mems[j]? = some m →
      ¬ ((sel m.shape).1 ≤ b ∧ b < (sel m.shape).1 + (sel m.shape).2)) :
    (layRows n len (blocksOf A w fr C sel tab)).getD b [] =
      List.replicate len Fmt.Fld.zeroE := by
  refine layRows_free n len b hb _ fun B hB => ?_
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hB
  rw [blocksOf_get] at hj
  obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.1 hj
  exact hn j m hm

end Laid

/-! ## 4 The state -/

section State
variable (A : ManyJob W X) (w : W) (fr : Front X) (C : TestCoins)

theorem idx_mod (n b e : ℕ) (hb : b < n) : (b + n * e) % n = b := by
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]

theorem idx_div (n b e : ℕ) (hb : b < n) : (b + n * e) / n = e := by
  rw [Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hb, Nat.zero_add]

theorem tabM_many (i : ℕ) : (A.toRun.toTest.first w fr C).tabM i =
    lst ((layRows (2 ^ A.s₀.k) A.s₀.C.l (blocksOf A w fr C (fun m => (m.mainFirst, m.mainRows))
      (·.M))).getD (i % 2 ^ A.s₀.k) []) (i / 2 ^ A.s₀.k) := rfl

theorem tM_many (b q : ℕ) : (A.toRun.toTest.first w fr C).tM b q =
    lst ((layRows (2 ^ A.s₀.k) A.s₀.C.r (blocksOf A w fr C (fun m => (m.mainFirst, m.mainRows))
      (·.Rh))).getD b []) q := rfl

theorem tabZ_many (i : ℕ) : (A.toRun.toTest.first w fr C).tabZ i =
    lst ((layRows (2 ^ A.s₀.h) A.s₀.Z.l (blocksOf A w fr C (fun m => (m.maskFirst, m.maskRows))
      (·.W))).getD (i % 2 ^ A.s₀.h) []) (i / 2 ^ A.s₀.h) := rfl

theorem tZ_many (b q : ℕ) : (A.toRun.toTest.first w fr C).tZ b q =
    lst ((layRows (2 ^ A.s₀.h) A.s₀.Z.r (blocksOf A w fr C (fun m => (m.maskFirst, m.maskRows))
      (·.Sg))).getD b []) q := rfl

variable {A} {Dp : Plain} (F : ManyFits A.s₀ (A.mems.map (·.shape)) A.trees (plainSh Dp))
include F

/-- Seat number j, the member number j, and what the test says of the two. -/
theorem seat_mem (j : Fin Dp.mems.length) : ∃ m : Mem W X, A.mems[j.val]? = some m ∧
    memFitsB A.s₀ Dp.L j.val m.shape (Dp.mems.get j) = true := by
  have hl : j.val < A.mems.length := by
    have := F.len
    rw [List.length_map] at this
    exact this ▸ j.isLt
  refine ⟨A.mems[j.val], List.getElem?_eq_getElem hl, ?_⟩
  exact F.mem j.val _ _ (by rw [List.getElem?_map, List.getElem?_eq_getElem hl]; rfl)
    (List.getElem?_eq_getElem j.isLt)

theorem kk_many : kk A.s₀ = A.s₀.k := by
  have := F.hk
  unfold kk
  omega

/-- **The state holds the members' own rows at the layout's blocks, and 0 elsewhere.** -/
theorem state_many : StateAt A.s₀ Dp (A.toRun.toTest.first w fr C) (plainMany A w fr C) where
  main := fun j i e hi _ => by
    obtain ⟨m, hm, hf⟩ := seat_mem F j
    obtain ⟨e1, -, e3, -, e5, -⟩ := memFits_of_B hf
    rw [e1] at hi
    obtain ⟨-, -, e3⟩ := e3 (by omega)
    have hb : m.shape.mainFirst + i < 2 ^ A.s₀.k := by omega
    rw [kk_many F, e3, tabM_many, idx_mod _ _ _ hb, idx_div _ _ _ hb]
    exact congrArg (lst · e) (laid_at A w fr C (fun m => (m.mainFirst, m.mainRows)) (·.M) F.apartM
      _ _ j.val m hm i hi hb)
  mainT := fun j i q hi _ => by
    obtain ⟨m, hm, hf⟩ := seat_mem F j
    obtain ⟨e1, -, e3, -, e5, -⟩ := memFits_of_B hf
    rw [e1] at hi
    obtain ⟨-, -, e3⟩ := e3 (by omega)
    have hb : m.shape.mainFirst + i < 2 ^ A.s₀.k := by omega
    rw [e3, tM_many]
    exact congrArg (lst · q) (laid_at A w fr C (fun m => (m.mainFirst, m.mainRows)) (·.Rh)
      F.apartM _ _ j.val m hm i hi hb)
  mask := fun j i e hi _ => by
    obtain ⟨m, hm, hf⟩ := seat_mem F j
    obtain ⟨-, e2, -, e4, -, e6⟩ := memFits_of_B hf
    rw [e2] at hi
    have e4 := e4 (by omega)
    have hb : m.shape.maskFirst + i < 2 ^ A.s₀.h := by omega
    rw [e4, tabZ_many, idx_mod _ _ _ hb, idx_div _ _ _ hb]
    exact congrArg (lst · e) (laid_at A w fr C (fun m => (m.maskFirst, m.maskRows)) (·.W) F.apartZ
      _ _ j.val m hm i hi hb)
  maskT := fun j i q hi _ => by
    obtain ⟨m, hm, hf⟩ := seat_mem F j
    obtain ⟨-, e2, -, e4, -, e6⟩ := memFits_of_B hf
    rw [e2] at hi
    have e4 := e4 (by omega)
    have hb : m.shape.maskFirst + i < 2 ^ A.s₀.h := by omega
    rw [e4, tZ_many]
    exact congrArg (lst · q) (laid_at A w fr C (fun m => (m.maskFirst, m.maskRows)) (·.Sg)
      F.apartZ _ _ j.val m hm i hi hb)
  freeM := fun b hb hn => by
    rw [kk_many F] at hb ⊢
    have hfree : ∀ (j : ℕ) (m : Mem W X), A.mems[j]? = some m →
        ¬ (m.shape.mainFirst ≤ b ∧ b < m.shape.mainFirst + m.shape.mainRows) := by
      intro j m hm hc
      have hl : j < Dp.mems.length := by
        have hh : Dp.mems.length = (A.mems.map (·.shape)).length := F.len
        rw [List.length_map] at hh
        rw [hh]
        exact (List.getElem?_eq_some_iff.1 hm).1
      obtain ⟨m', hm', hf⟩ := seat_mem F ⟨j, hl⟩
      obtain rfl : m' = m := Option.some.inj (hm'.symm.trans hm)
      obtain ⟨e1, -, e3, -⟩ := memFits_of_B hf
      obtain ⟨-, -, e3⟩ := e3 (by omega)
      exact hn ⟨j, hl⟩ ⟨by rw [e3]; exact hc.1, by rw [e3, e1]; exact hc.2⟩
    refine ⟨fun e _ => ?_, fun q _ => ?_⟩
    · rw [tabM_many, idx_mod _ _ _ hb, idx_div _ _ _ hb,
        laid_free A w fr C (fun m => (m.mainFirst, m.mainRows)) (·.M) _ _ b hb hfree]
      exact lst_zeros _ _
    · rw [tM_many, laid_free A w fr C (fun m => (m.mainFirst, m.mainRows)) (·.Rh) _ _ b hb hfree]
      exact lst_zeros _ _
  freeZ := fun b hb hn => by
    have hfree : ∀ (j : ℕ) (m : Mem W X), A.mems[j]? = some m →
        ¬ (m.shape.maskFirst ≤ b ∧ b < m.shape.maskFirst + m.shape.maskRows) := by
      intro j m hm hc
      have hl : j < Dp.mems.length := by
        have hh : Dp.mems.length = (A.mems.map (·.shape)).length := F.len
        rw [List.length_map] at hh
        rw [hh]
        exact (List.getElem?_eq_some_iff.1 hm).1
      obtain ⟨m', hm', hf⟩ := seat_mem F ⟨j, hl⟩
      obtain rfl : m' = m := Option.some.inj (hm'.symm.trans hm)
      obtain ⟨-, e2, -, e4, -⟩ := memFits_of_B hf
      have e4 := e4 (by omega)
      exact hn ⟨j, hl⟩ ⟨by rw [e4]; exact hc.1, by rw [e4, e2]; exact hc.2⟩
    refine ⟨fun e _ => ?_, fun q _ => ?_⟩
    · rw [tabZ_many, idx_mod _ _ _ hb, idx_div _ _ _ hb,
        laid_free A w fr C (fun m => (m.maskFirst, m.maskRows)) (·.W) _ _ b hb hfree]
      exact lst_zeros _ _
    · rw [tZ_many, laid_free A w fr C (fun m => (m.maskFirst, m.maskRows)) (·.Sg) _ _ b hb hfree]
      exact lst_zeros _ _
  fresh := fun _ _ _ _ => rfl
  freshT := fun _ _ _ _ => rfl

end State

/-! ## 5 A column's words -/

theorem getD_mid {α : Type} (a b c : List α) (d : α) (k : ℕ) (hk : k < b.length) :
    (a ++ (b ++ c)).getD (a.length + k) d = b.getD k d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
    List.getElem?_append_left hk]

theorem read3_mid (a b c : List UInt64) (k : ℕ) (hk : k + 2 < b.length) :
    read3 (a ++ (b ++ c)) (a.length + k) = read3 b k := by
  unfold read3
  rw [getD_mid a b c 0 k (by omega), Nat.add_assoc, getD_mid a b c 0 (k + 1) (by omega),
    Nat.add_assoc, getD_mid a b c 0 (k + 2) hk]

/-- Rows none of which is written as one word: three words each. -/
theorem wordsAt_three (sym : Sel → Fmt.M1.E) : ∀ l : List Sel, (∀ r ∈ l, r.base = false) →
    wordsAt sym l = Johnson.Prover.Link.wordsOf (l.map sym)
  | [], _ => rfl
  | r :: l, h => by
    have e : wordsAt sym (r :: l) = (if r.base then [(sym r).1] else words (sym r)) ++
        wordsAt sym l := rfl
    rw [e, h r List.mem_cons_self,
      wordsAt_three sym l fun r' hr' => h r' (List.mem_cons_of_mem _ hr')]
    rfl

theorem wordsAt_cat (sym : Sel → Fmt.M1.E) (l l' : List Sel) :
    wordsAt sym (l ++ l') = wordsAt sym l ++ wordsAt sym l' := by
  unfold wordsAt
  rw [List.flatMap_append]

/-- No member with main rows is over the base field. -/
def NoBase (ms : List MemShape) : Prop :=
  ∀ (t : ℕ) (m : MemShape), ms[t]? = some m → m.mainRows ≠ 0 → m.base = false

theorem selsOf_main (s : Stage) {ms : List MemShape} {t : ℕ} {m : MemShape}
    (hm : ms[t]? = some m) : selsOf s ms (.main t) =
      (List.range m.mainRows).map fun r => ⟨.main, m.mainFirst + r, m.base⟩ := by
  simp only [selsOf, hm]

theorem selsOf_mask (s : Stage) {ms : List MemShape} {t : ℕ} {m : MemShape}
    (hm : ms[t]? = some m) : selsOf s ms (.mask t) =
      (List.range m.maskRows).map fun r => ⟨.mask, m.maskFirst + r, false⟩ := by
  simp only [selsOf, hm]

theorem sels_three (s : Stage) {ms : List MemShape} (hB : NoBase ms) (q : Piece) :
    ∀ r ∈ selsOf s ms q, r.base = false := by
  intro r hr
  cases q with
  | main t =>
    cases hm : ms[t]? with
    | none =>
      simp only [selsOf, hm] at hr
      cases hr
    | some m =>
      rw [selsOf_main s hm] at hr
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hr
      exact hB t m hm (by have := List.mem_range.1 hi; omega)
  | mask t =>
    cases hm : ms[t]? with
    | none =>
      simp only [selsOf, hm] at hr
      cases hr
    | some m =>
      rw [selsOf_mask s hm] at hr
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hr
      rfl
  | fresh =>
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hr
    rfl

theorem len_piece (s : Stage) {ms : List MemShape} (hB : NoBase ms) (sym : Sel → Fmt.M1.E)
    (q : Piece) : (wordsAt sym (selsOf s ms q)).length = pieceLen s ms q := by
  rw [wordsAt_three sym _ (sels_three s hB q), Johnson.Prover.Link.length_wordsOf, List.length_map]
  rfl

theorem len_pieces (s : Stage) {ms : List MemShape} (hB : NoBase ms) (sym : Sel → Fmt.M1.E) :
    ∀ l : List Piece, (wordsAt sym (l.flatMap (selsOf s ms))).length = (l.map (pieceLen s ms)).sum
  | [] => rfl
  | q :: l => by
    rw [List.flatMap_cons, wordsAt_cat, List.length_append, len_piece s hB,
      len_pieces s hB sym l, List.map_cons, List.sum_cons]

/-- Where wordsBefore returns n, the list splits at the piece, with n words in front. -/
theorem split_of_before (s : Stage) (ms : List MemShape) (q : Piece) : ∀ (l : List Piece) (n : ℕ),
    wordsBefore s ms q l = some n →
    ∃ pre post, l = pre ++ q :: post ∧ (pre.map (pieceLen s ms)).sum = n
  | [], _, h => by cases h
  | r :: l, n, h => by
    unfold wordsBefore at h
    split at h
    · rename_i e
      obtain rfl := Option.some.inj h
      exact ⟨[], l, by rw [e]; rfl, rfl⟩
    · obtain ⟨n', hn', rfl⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨pre, post, rfl, hs⟩ := split_of_before s ms q l n' hn'
      exact ⟨r :: pre, post, rfl, by rw [List.map_cons, List.sum_cons, hs]⟩

/-- **Row number i of a piece, read off the column.** -/
theorem read3_piece (s : Stage) {ms : List MemShape} (hB : NoBase ms) (sym : Sel → Fmt.M1.E)
    (q : Piece) (l : List Piece) (n : ℕ) (h : wordsBefore s ms q l = some n) (i : ℕ)
    (hi : i < (selsOf s ms q).length) :
    read3 (wordsAt sym (l.flatMap (selsOf s ms))) (n + 3 * i) =
      lst ((selsOf s ms q).map sym) i := by
  obtain ⟨pre, post, rfl, hs⟩ := split_of_before s ms q l n h
  rw [List.flatMap_append, List.flatMap_cons, wordsAt_cat, wordsAt_cat, ← hs,
    ← len_pieces s hB sym pre, read3_mid _ _ _ _ (by rw [len_piece s hB]; unfold pieceLen; omega),
    wordsAt_three sym _ (sels_three s hB q)]
  exact ProofFile.Honest.K12.read3_wordsOf _ _ (by rw [List.length_map]; exact hi)

/-! ## 6 The columns, the trees, the theorem -/

theorem symOf_main (s : Stage) (hk : s.h ≤ s.k) (P : PS) (x r : ℕ) (hr : r < 2 ^ s.k) :
    toE (symOf s P x ⟨.main, r, false⟩) =
      symG s.C x (fun j => P.tabM (r + 2 ^ s.k * j)) (P.tM r) := by
  show toE (if r < 2 ^ s.k then ofE (Johnson.Prover.Link.mainSym (H2K.Pub.sgOf s) P.tabM P.tM x r)
    else Fmt.Fld.zeroE) = _
  rw [if_pos hr, OnBytes.Slice.toE_ofE]
  show symG s.C x (fun j => P.tabM (r + 2 ^ ((H2K.Pub.sgOf s).h + (H2K.Pub.sgOf s).g) * j))
    (P.tM r) = _
  rw [sg_k hk]

theorem symOf_mask (s : Stage) (P : PS) (x r : ℕ) (hr : r < 2 ^ s.h) :
    toE (symOf s P x ⟨.mask, r, false⟩) =
      symG s.Z (x % 2 ^ s.Z.a) (fun j => P.tabZ (r + 2 ^ s.h * j)) (P.tZ r) := by
  show toE (if r < 2 ^ s.h then ofE (Johnson.Prover.Link.maskSym (H2K.Pub.sgOf s) P.tabZ P.tZ x r)
    else Fmt.Fld.zeroE) = _
  rw [if_pos hr, OnBytes.Slice.toE_ofE]
  rfl

theorem symOf_fresh (s : Stage) (P : PS) (x r : ℕ) (hr : r < 2 ^ s.h) :
    toE (symOf s P x ⟨.fresh, r, false⟩) = symG s.Z (x % 2 ^ s.Z.a) (P.fM r) (P.fT r) := by
  show toE (if r < 2 ^ s.h then ofE (Johnson.Prover.Link.freshSym (H2K.Pub.sgOf s) P.fM P.fT x r)
    else Fmt.Fld.zeroE) = _
  rw [if_pos hr, OnBytes.Slice.toE_ofE]
  rfl

section Cols
variable (A : ManyJob W X) (w : W) (fr : Front X) (C : TestCoins)

/-- The job's tree number i. -/
theorem tree_many (i : ℕ) :
    (A.toRun.toTest.trees₀ w fr C.mem (A.toRun.toTest.first w fr C))[i]? =
      (A.trees[i]?).map fun T => (T.1, fun x =>
        wordsAt (symOf A.s₀ (A.toRun.toTest.first w fr C) x)
          (T.2.flatMap (selsOf A.s₀ (A.mems.map (·.shape))))) := by
  show ((treesOf A.s₀ (A.mems.map (·.shape)) A.trees).map fun T =>
    treeOf A.s₀ T (A.toRun.toTest.first w fr C))[i]? = _
  unfold treesOf
  rw [List.getElem?_map, List.getElem?_map]
  cases A.trees[i]? <;> rfl

/-- The column at a number of the book, where the job has a tree at that number's place. -/
theorem col_many (ts : List ℕ) (u : ℕ) (T : ℕ × List Piece) (hT : A.trees[ts.idxOf u]? = some T)
    (x : ℕ) : colsMany A ts w fr C u x =
      wordsAt (symOf A.s₀ (A.toRun.toTest.first w fr C) x)
        (T.2.flatMap (selsOf A.s₀ (A.mems.map (·.shape)))) := by
  unfold colsMany
  rw [tree_many, hT]
  rfl

variable {A} {Dp : Plain} (F : ManyFits A.s₀ (A.mems.map (·.shape)) A.trees (plainSh Dp))
include F

theorem noBase_many : NoBase (A.mems.map (·.shape)) := by
  intro t m hm hn
  have hl : t < Dp.mems.length := by
    have hh : Dp.mems.length = (A.mems.map (·.shape)).length := F.len
    rw [hh]
    exact (List.getElem?_eq_some_iff.1 hm).1
  exact ((memFits_of_B (F.mem t m _ hm (List.getElem?_eq_getElem hl))).2.2.1 hn).1

omit F in
theorem seat_of_B {t : ℕ} {q : Piece} {n : ℕ}
    (h : seatFitsB A.s₀ (A.mems.map (·.shape)) A.trees Dp.ts t q n = true) :
    ∃ T, A.trees[Dp.ts.idxOf t]? = some T ∧
      wordsBefore A.s₀ (A.mems.map (·.shape)) q T.2 = some n := by
  unfold seatFitsB at h
  split at h
  · rename_i T hT
    exact ⟨T, hT, by simpa using h⟩
  · cases h

/-- **The job's own columns hold the job's own rows' symbols, where the seats say.** -/
theorem cols_many : ColsAt A.s₀ Dp (colsMany A Dp.ts w fr C) (plainMany A w fr C) where
  width := fun u hu x _ => by
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hu
    have hlt : i < Dp.ts.length := (List.getElem?_eq_some_iff.1 hi).1
    have hlt' : i < A.trees.length := by
      have hh : Dp.ts.length = A.trees.length := F.tlen
      omega
    have hidx : Dp.ts.idxOf u = i := by
      have e : Dp.ts[i] = u := (List.getElem?_eq_some_iff.1 hi).2
      rw [← e]
      exact List.Nodup.idxOf_getElem F.nodup i hlt
    have k := F.tree i _ u (List.getElem?_eq_getElem hlt') hi
    unfold treeFitsB at k
    simp only [Bool.and_eq_true, beq_iff_eq] at k
    rw [col_many A w fr C Dp.ts u A.trees[i] (by rw [hidx]; exact List.getElem?_eq_getElem hlt'),
      len_pieces _ (noBase_many F), k.2]
    exact widthAtS_eq _ _
  mem := fun j x _ => by
    obtain ⟨m, hm, hf⟩ := seat_mem F j
    obtain ⟨e1, e2, e3, e4, e5, e6⟩ := memFits_of_B hf
    have hms : (A.mems.map (·.shape))[j.val]? = some m.shape := by
      rw [List.getElem?_map, hm]
      rfl
    have S := state_many w fr C F
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · have hi' : i < m.shape.mainRows := e1 ▸ hi
      obtain ⟨b1, b2, b3⟩ := e3 (by omega)
      obtain ⟨T, hT, hw⟩ := seat_of_B (F.seatM j.val m.shape _ hms
        (List.getElem?_eq_getElem j.isLt) (by omega))
      have hT : A.trees[Dp.ts.idxOf (Dp.mems.get j).t]? = some T := hT
      have hw : wordsBefore A.s₀ (A.mems.map (·.shape)) (.main j.val) T.2 =
          some (skM (Dp.mems.get j).tsh (Dp.mems.get j).part) := hw
      have hd : ((Dp.mems.get j).sh.mainDeg == 1) = false := by simpa using b2
      rw [hd]
      show read3 _ _ = _
      rw [col_many A w fr C Dp.ts _ T hT, read3_piece _ (noBase_many F) _ _ _ _ hw i
        (by rw [selsOf_main _ hms, List.length_map, List.length_range]; exact hi'),
        selsOf_main _ hms, List.map_map, lst_range _ _ _ hi']
      show toE (symOf A.s₀ _ x ⟨.main, m.shape.mainFirst + i, m.shape.base⟩) = _
      rw [b1, symOf_main _ F.hk _ _ _ (by omega)]
      refine symG_congr _ _ _ _ _ _ (fun e he => ?_) fun q hq => ?_
      · have k := S.main j i e hi he
        rw [kk_many F, b3] at k
        exact k
      · have k := S.mainT j i q hi hq
        rw [b3] at k
        exact k
    · have hi' : i < m.shape.maskRows := e2 ▸ hi
      have b3 := e4 (by omega)
      obtain ⟨T, hT, hw⟩ := seat_of_B (F.seatZ j.val m.shape _ hms
        (List.getElem?_eq_getElem j.isLt) (by omega))
      have hT : A.trees[Dp.ts.idxOf (Dp.mems.get j).t]? = some T := hT
      have hw : wordsBefore A.s₀ (A.mems.map (·.shape)) (.mask j.val) T.2 =
          some (skZ (Dp.mems.get j).tsh (Dp.mems.get j).part) := hw
      rw [col_many A w fr C Dp.ts _ T hT, read3_piece _ (noBase_many F) _ _ _ _ hw i
        (by rw [selsOf_mask _ hms, List.length_map, List.length_range]; exact hi'),
        selsOf_mask _ hms, List.map_map, lst_range _ _ _ hi']
      show toE (symOf A.s₀ _ x ⟨.mask, m.shape.maskFirst + i, false⟩) = _
      rw [symOf_mask _ _ _ _ (by omega)]
      refine symG_congr _ _ _ _ _ _ (fun e he => ?_) fun q hq => ?_
      · have k := S.mask j i e hi he
        rw [b3] at k
        exact k
      · have k := S.maskT j i q hi hq
        rw [b3] at k
        exact k
  fresh := fun x _ b hb => by
    obtain ⟨T, hT, hw⟩ := seat_of_B F.fresh
    have hT : A.trees[Dp.ts.idxOf Dp.fresh.t]? = some T := hT
    have hw : wordsBefore A.s₀ (A.mems.map (·.shape)) .fresh T.2 =
        some (skZ Dp.fresh.tsh Dp.fresh.part) := hw
    have hl : (selsOf A.s₀ (A.mems.map (·.shape)) .fresh).length = 2 ^ A.s₀.h := by
      show ((List.range (2 ^ A.s₀.h)).map _).length = _
      rw [List.length_map, List.length_range]
    rw [col_many A w fr C Dp.ts _ T hT, read3_piece _ (noBase_many F) _ _ _ _ hw b (hl ▸ hb)]
    show lst (((List.range (2 ^ A.s₀.h)).map fun r => (⟨.fresh, r, false⟩ : Sel)).map _) b = _
    rw [List.map_map, lst_range _ _ _ hb]
    exact symOf_fresh _ _ _ _ hb

/-- **The job's trees are the group's**, in the book's order, at the book's depths. -/
theorem trees_many :
    A.toRun.toTest.trees₀ w fr C.mem (A.toRun.toTest.first w fr C) =
      groupTrees Dp.ts (logAt Dp.book) (colsMany A Dp.ts w fr C) := by
  have hh : Dp.ts.length = A.trees.length := F.tlen
  refine List.ext_getElem? fun i => ?_
  unfold groupTrees
  rw [tree_many, List.getElem?_map]
  cases hT : A.trees[i]? with
  | none =>
    have : Dp.ts[i]? = none := by
      rw [List.getElem?_eq_none_iff] at hT ⊢
      omega
    rw [this]
    rfl
  | some T =>
    have hlt : i < Dp.ts.length := by
      have := (List.getElem?_eq_some_iff.1 hT).1
      omega
    rw [List.getElem?_eq_getElem hlt]
    have hidx : Dp.ts.idxOf Dp.ts[i] = i := List.Nodup.idxOf_getElem F.nodup i hlt
    have k := F.tree i T _ hT (List.getElem?_eq_getElem hlt)
    unfold treeFitsB at k
    simp only [Bool.and_eq_true, beq_iff_eq] at k
    show some (T.1, _) = some (logAt Dp.book Dp.ts[i], colsMany A Dp.ts w fr C Dp.ts[i])
    have e1 : T.1 = logAt Dp.book Dp.ts[i] := k.1.trans (logAtS_eq _ _)
    have e2 : colsMany A Dp.ts w fr C Dp.ts[i] = fun x =>
        wordsAt (symOf A.s₀ (A.toRun.toTest.first w fr C) x)
          (T.2.flatMap (selsOf A.s₀ (A.mems.map (·.shape)))) :=
      funext fun x => col_many A w fr C Dp.ts _ T (by rw [hidx]; exact hT) x
    rw [e1, e2]

end Cols

/-- **The first three clauses of DataFront at a ManyJob's job**, at the job's own rows and columns:
from the one test on public things; at every input, whatever precedes the test, and all random
values. -/
theorem dataThree_many (A : ManyJob W X) (Dp : Plain)
    (h : manyFitsB A.s₀ (A.mems.map (·.shape)) A.trees (plainSh Dp) = true) (w : W) (fr : Front X)
    (C : TestCoins) :
    ColsAt A.s₀ Dp (colsMany A Dp.ts w fr C) (plainMany A w fr C) ∧
      StateAt A.s₀ Dp (A.toRun.toTest.first w fr C) (plainMany A w fr C) ∧
      A.toRun.toTest.trees₀ w fr C.mem (A.toRun.toTest.first w fr C) =
        groupTrees Dp.ts (logAt Dp.book) (colsMany A Dp.ts w fr C) :=
  ⟨cols_many w fr C (manyFits_of_B h), state_many w fr C (manyFits_of_B h),
    trees_many w fr C (manyFits_of_B h)⟩

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.Covers
#print axioms ProofFile.Honest.K12.Light.layRows_at
#print axioms ProofFile.Honest.K12.Light.layRows_free
#print axioms ProofFile.Honest.K12.Light.lst_zeros
#print axioms ProofFile.Honest.K12.Light.all_zipIdx
#print axioms ProofFile.Honest.K12.Light.all_zip
#print axioms ProofFile.Honest.K12.Light.ManyFits
#print axioms ProofFile.Honest.K12.Light.manyFits_of_B
#print axioms ProofFile.Honest.K12.Light.apart_of_B
#print axioms ProofFile.Honest.K12.Light.memFits_of_B
#print axioms ProofFile.Honest.K12.Light.blocksOf
#print axioms ProofFile.Honest.K12.Light.blocksOf_get
#print axioms ProofFile.Honest.K12.Light.memRows_of
#print axioms ProofFile.Honest.K12.Light.laid_at
#print axioms ProofFile.Honest.K12.Light.laid_free
#print axioms ProofFile.Honest.K12.Light.idx_mod
#print axioms ProofFile.Honest.K12.Light.idx_div
#print axioms ProofFile.Honest.K12.Light.tabM_many
#print axioms ProofFile.Honest.K12.Light.tM_many
#print axioms ProofFile.Honest.K12.Light.tabZ_many
#print axioms ProofFile.Honest.K12.Light.tZ_many
#print axioms ProofFile.Honest.K12.Light.seat_mem
#print axioms ProofFile.Honest.K12.Light.kk_many
#print axioms ProofFile.Honest.K12.Light.state_many
#print axioms ProofFile.Honest.K12.Light.getD_mid
#print axioms ProofFile.Honest.K12.Light.read3_mid
#print axioms ProofFile.Honest.K12.Light.wordsAt_three
#print axioms ProofFile.Honest.K12.Light.wordsAt_cat
#print axioms ProofFile.Honest.K12.Light.NoBase
#print axioms ProofFile.Honest.K12.Light.selsOf_main
#print axioms ProofFile.Honest.K12.Light.selsOf_mask
#print axioms ProofFile.Honest.K12.Light.sels_three
#print axioms ProofFile.Honest.K12.Light.len_piece
#print axioms ProofFile.Honest.K12.Light.len_pieces
#print axioms ProofFile.Honest.K12.Light.split_of_before
#print axioms ProofFile.Honest.K12.Light.read3_piece
#print axioms ProofFile.Honest.K12.Light.symOf_main
#print axioms ProofFile.Honest.K12.Light.symOf_mask
#print axioms ProofFile.Honest.K12.Light.symOf_fresh
#print axioms ProofFile.Honest.K12.Light.tree_many
#print axioms ProofFile.Honest.K12.Light.col_many
#print axioms ProofFile.Honest.K12.Light.noBase_many
#print axioms ProofFile.Honest.K12.Light.seat_of_B
#print axioms ProofFile.Honest.K12.Light.cols_many
#print axioms ProofFile.Honest.K12.Light.trees_many
#print axioms ProofFile.Honest.K12.Light.dataThree_many
