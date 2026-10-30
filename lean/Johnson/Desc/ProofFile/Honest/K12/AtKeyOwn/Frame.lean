-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtKeyOwn/Frame.lean: FOR A PROXIMITY TEST ON A GROUP OF ANY NUMBER OF MEMBERS (ManyJob, RunMany.lean): the words that
the job lays for a piece of a tree's column (main rows or mask rows of member number t) are the field's code symbols of THAT MEMBER's OWN LISTS, decoded;
and OldAt (ColsTerm.lean) from tables that show the trees' columns. TreeIsColumn.lean has the first at two members; here the list is free.

  layRows_at       of a list of blocks: at a row that block number t covers and no earlier block covers: that block's row
  mask_piece_at, main_piece_at   a piece of member number t, from the member's own lists
  same_col         where two tables show the same, their columns below the length are equal, and so are their lengths
  oldAt_of_tables  OldAt from: no source is an own tree; at each tree the table at hand shows what a table T shows, T has the tree's depth
                   and, below it, the tree's columns

Limits. Equations of texts and an implication. Main rows over the extension field alone (base is false). Which rows a member's lists hold, whether a
table at hand shows anything, and every tie on coins are premises or are not spoken of. Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.TreeIsColumn
import Johnson.Desc.ProofFile.Honest.K12.ColsTerm
import Johnson.Desc.ProofFile.Honest.Thread.Thr

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtKeyOwn
open OnBytes.Slice (GE ofE toE lst)
open Johnson.Prover.Link (PS symG symG_congr)
open Fmt.M1 (Stage)
open Fmt.M1.Own (PSt words)
open ProofFile.Honest.K12.Light

/-- **Of a list of blocks, the rows of the first that covers.** -/
theorem findSome_at (b : ℕ) : ∀ (bs : List RowBlock) (t : ℕ) (B : RowBlock), bs[t]? = some B →
    (B.first ≤ b ∧ b < B.first + B.count) →
    (∀ i, i < t → ∀ B', bs[i]? = some B' → ¬ (B'.first ≤ b ∧ b < B'.first + B'.count)) →
    (bs.findSome? fun B =>
      if B.first ≤ b ∧ b < B.first + B.count then some (B.rows.getD (b - B.first) []) else none) =
      some (B.rows.getD (b - B.first) [])
  | [], _, _, h, _, _ => by cases h
  | B0 :: bs, 0, B, h, hin, _ => by
    obtain rfl : B0 = B := Option.some.inj h
    rw [List.findSome?_cons, if_pos hin]
  | B0 :: bs, t + 1, B, h, hin, hap => by
    have h0 := hap 0 (Nat.succ_pos t) B0 rfl
    rw [List.findSome?_cons, if_neg h0]
    exact findSome_at b bs t B h hin fun i hi B' hB' => hap (i + 1) (Nat.succ_lt_succ hi) B' hB'

theorem layRows_at (n len b : ℕ) (bs : List RowBlock) (t : ℕ) (B : RowBlock) (hB : bs[t]? = some B)
    (hb : b < n) (hin : B.first ≤ b ∧ b < B.first + B.count)
    (hap : ∀ i, i < t → ∀ B', bs[i]? = some B' → ¬ (B'.first ≤ b ∧ b < B'.first + B'.count)) :
    (layRows n len bs).getD b [] = B.rows.getD (b - B.first) [] := by
  unfold layRows
  rw [getD_range n _ _ b hb, findSome_at b bs t B hB hin hap]
  rfl

/-- b + 2 ^ h * j, cut by 2 ^ h. -/
theorem cut_idx (N b j : ℕ) (hb : b < N) : (b + N * j) % N = b ∧ (b + N * j) / N = j := by
  constructor
  · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]
  · rw [Nat.add_mul_div_left _ _ (Nat.lt_of_le_of_lt (Nat.zero_le b) hb), Nat.div_eq_of_lt hb,
      Nat.zero_add]

/-- **Member number t's mask rows.** hap: no earlier member's block of mask rows meets this one. -/
theorem mask_piece_at (s : Stage) (ms : List (MemShape × PSt)) (t : ℕ) (m : MemShape) (q : PSt)
    (hm : ms[t]? = some (m, q)) (P : PS) (hP : P.tabZ = (readPS s (layFirst s ms)).tabZ)
    (hT : P.tZ = (readPS s (layFirst s ms)).tZ) (hin : m.maskFirst + m.maskRows ≤ 2 ^ s.h)
    (hap : ∀ i, i < t → ∀ m' q', ms[i]? = some (m', q') →
      m'.maskFirst + m'.maskRows ≤ m.maskFirst ∨ m.maskFirst + m.maskRows ≤ m'.maskFirst) (x : ℕ) :
    wordsAt (symOf s P x) (selsOf s (ms.map (·.1)) (.mask t)) =
      (List.range m.maskRows).flatMap fun r =>
        words (ofE (symG s.Z (x % 2 ^ s.Z.a) (fun j => lst (q.W.getD r []) j)
          fun i => lst (q.Sg.getD r []) i)) := by
  have e0 : selsOf s (ms.map (·.1)) (.mask t) =
      (List.range m.maskRows).map fun r => ⟨.mask, m.maskFirst + r, false⟩ := by
    show (match (ms.map (·.1))[t]? with
      | some m => (List.range m.maskRows).map fun r => (⟨.mask, m.maskFirst + r, false⟩ : Sel)
      | none => []) = _
    rw [List.getElem?_map, hm]
    rfl
  rw [e0, ProofFile.Honest.K12.Light.maskWords s P x m.maskFirst m.maskRows hin]
  refine congrArg List.flatten (List.map_congr_left fun r hr => ?_)
  have hr' : r < m.maskRows := List.mem_range.1 hr
  have hb : m.maskFirst + r < 2 ^ s.h := by omega
  have row : ∀ (len : ℕ) (f : MemShape × PSt → List (List Fmt.M1.E)),
      (layRows (2 ^ s.h) len (ms.map fun y => ⟨y.1.maskFirst, y.1.maskRows, f y⟩)).getD
        (m.maskFirst + r) [] = (f (m, q)).getD r [] := by
    intro len f
    have := layRows_at (2 ^ s.h) len (m.maskFirst + r)
      (ms.map fun y => ⟨y.1.maskFirst, y.1.maskRows, f y⟩) t ⟨m.maskFirst, m.maskRows, f (m, q)⟩
      (by rw [List.getElem?_map, hm]; rfl) hb ⟨Nat.le_add_right _ _, by show _ < m.maskFirst + m.maskRows; omega⟩
      (fun i hi B' hB' => by
        rw [List.getElem?_map] at hB'
        cases hy : ms[i]? with
        | none => rw [hy] at hB'; cases hB'
        | some y =>
          rw [hy] at hB'
          obtain rfl := Option.some.inj hB'
          have := hap i hi y.1 y.2 hy
          show ¬ (y.1.maskFirst ≤ m.maskFirst + r ∧ m.maskFirst + r < y.1.maskFirst + y.1.maskRows)
          omega)
    rw [this]
    show (f (m, q)).getD (m.maskFirst + r - m.maskFirst) [] = _
    rw [Nat.add_sub_cancel_left]
  refine congrArg (fun y => words (ofE y)) (symG_congr _ _ _ _ _ _ (fun j _ => ?_) fun i _ => ?_)
  · rw [hP]
    show lst ((layFirst s ms).W.getD ((m.maskFirst + r + 2 ^ s.h * j) % 2 ^ s.h) [])
      ((m.maskFirst + r + 2 ^ s.h * j) / 2 ^ s.h) = _
    rw [(cut_idx _ _ j hb).1, (cut_idx _ _ j hb).2]
    exact congrArg (fun l => lst l j) (row s.Z.l fun y => y.2.W)
  · rw [hT]
    show lst ((layFirst s ms).Sg.getD (m.maskFirst + r) []) i = _
    exact congrArg (fun l => lst l i) (row s.Z.r fun y => y.2.Sg)

/-- **Member number t's main rows**, over the extension field. -/
theorem main_piece_at (s : Stage) (hk : s.h ≤ s.k) (ms : List (MemShape × PSt)) (t : ℕ)
    (m : MemShape) (q : PSt) (hm : ms[t]? = some (m, q)) (hbase : m.base = false) (P : PS)
    (hP : P.tabM = (readPS s (layFirst s ms)).tabM) (hT : P.tM = (readPS s (layFirst s ms)).tM)
    (hin : m.mainFirst + m.mainRows ≤ 2 ^ s.k)
    (hap : ∀ i, i < t → ∀ m' q', ms[i]? = some (m', q') →
      m'.mainFirst + m'.mainRows ≤ m.mainFirst ∨ m.mainFirst + m.mainRows ≤ m'.mainFirst) (x : ℕ) :
    wordsAt (symOf s P x) (selsOf s (ms.map (·.1)) (.main t)) =
      (List.range m.mainRows).flatMap fun r =>
        words (ofE (symG s.C x (fun j => lst (q.M.getD r []) j) fun i => lst (q.Rh.getD r []) i)) := by
  have e0 : selsOf s (ms.map (·.1)) (.main t) =
      (List.range m.mainRows).map fun r => ⟨.main, m.mainFirst + r, false⟩ := by
    show (match (ms.map (·.1))[t]? with
      | some m => (List.range m.mainRows).map fun r => (⟨.main, m.mainFirst + r, m.base⟩ : Sel)
      | none => []) = _
    rw [List.getElem?_map, hm]
    show ((List.range m.mainRows).map fun r => (⟨.main, m.mainFirst + r, m.base⟩ : Sel)) = _
    rw [hbase]
  rw [e0, mainWords s hk P x m.mainFirst m.mainRows hin]
  refine congrArg List.flatten (List.map_congr_left fun r hr => ?_)
  have hr' : r < m.mainRows := List.mem_range.1 hr
  have hb : m.mainFirst + r < 2 ^ s.k := by omega
  have row : ∀ (len : ℕ) (f : MemShape × PSt → List (List Fmt.M1.E)),
      (layRows (2 ^ s.k) len (ms.map fun y => ⟨y.1.mainFirst, y.1.mainRows, f y⟩)).getD
        (m.mainFirst + r) [] = (f (m, q)).getD r [] := by
    intro len f
    have := layRows_at (2 ^ s.k) len (m.mainFirst + r)
      (ms.map fun y => ⟨y.1.mainFirst, y.1.mainRows, f y⟩) t ⟨m.mainFirst, m.mainRows, f (m, q)⟩
      (by rw [List.getElem?_map, hm]; rfl) hb ⟨Nat.le_add_right _ _, by show _ < m.mainFirst + m.mainRows; omega⟩
      (fun i hi B' hB' => by
        rw [List.getElem?_map] at hB'
        cases hy : ms[i]? with
        | none => rw [hy] at hB'; cases hB'
        | some y =>
          rw [hy] at hB'
          obtain rfl := Option.some.inj hB'
          have := hap i hi y.1 y.2 hy
          show ¬ (y.1.mainFirst ≤ m.mainFirst + r ∧ m.mainFirst + r < y.1.mainFirst + y.1.mainRows)
          omega)
    rw [this]
    show (f (m, q)).getD (m.mainFirst + r - m.mainFirst) [] = _
    rw [Nat.add_sub_cancel_left]
  refine congrArg (fun y => words (ofE y)) (symG_congr _ _ _ _ _ _ (fun j _ => ?_) fun i _ => ?_)
  · rw [hP]
    show lst ((layFirst s ms).M.getD ((m.mainFirst + r + 2 ^ s.k * j) % 2 ^ s.k) [])
      ((m.mainFirst + r + 2 ^ s.k * j) / 2 ^ s.k) = _
    rw [(cut_idx _ _ j hb).1, (cut_idx _ _ j hb).2]
    exact congrArg (fun l => lst l j) (row s.C.l fun y => y.2.M)
  · rw [hT]
    show lst ((layFirst s ms).Rh.getD (m.mainFirst + r) []) i = _
    exact congrArg (fun l => lst l i) (row s.C.r fun y => y.2.Rh)

/-- Where two tables show the same: one length, and one column at every position below it. -/
theorem same_col {t u : Table} (h : t.same u = true) :
    t.logLength = u.logLength ∧ ∀ x, x < 2 ^ t.logLength → t.col x = u.col x := by
  unfold Table.same at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  exact ⟨h.1.1, h.2⟩

/-- **OldAt FROM TABLES THAT SHOW THE TREES' COLUMNS.** -/
theorem oldAt_of_tables (E : Env) (T₀ : List Tree) (srcs : List Fmt.TreeSource)
    (hl : T₀.length ≤ srcs.length) (hown : ∀ σ ∈ srcs, ∀ n, σ ≠ .own n)
    (h : ∀ k, k < T₀.length → ∃ (u : VerifiableInference.Desc.Place × Table) (T : Table),
      E.tree (srcs.getD k (.own 0)) = some u ∧ u.2.same T = true ∧
      T.logLength = (T₀.getD k (0, fun _ => [])).1 ∧
      ∀ x, x < 2 ^ T.logLength → T.col x = (T₀.getD k (0, fun _ => [])).2 x) :
    OldAt E T₀ (fun k => srcs.getD k (.own 0)) := by
  refine ⟨fun k hk n hn => ?_, fun k hk x hx => ?_⟩
  · have hk' : k < srcs.length := Nat.lt_of_lt_of_le hk hl
    have hmem : srcs.getD k (.own 0) ∈ srcs := by
      rw [List.getD_eq_getElem _ _ hk']
      exact List.getElem_mem hk'
    exact absurd hn (hown _ hmem n)
  · obtain ⟨u, T, hE, hs, hd, hc⟩ := h k hk
    obtain ⟨e1, e2⟩ := same_col hs
    unfold colAt
    rw [hE]
    show u.2.col x = _
    rw [e2 x (by rw [e1, hd]; exact hx), hc x (by rw [hd]; exact hx)]

end ProofFile.Honest.K12.AtKeyOwn

#print axioms ProofFile.Honest.K12.AtKeyOwn.layRows_at
#print axioms ProofFile.Honest.K12.AtKeyOwn.mask_piece_at
#print axioms ProofFile.Honest.K12.AtKeyOwn.main_piece_at
#print axioms ProofFile.Honest.K12.AtKeyOwn.oldAt_of_tables
