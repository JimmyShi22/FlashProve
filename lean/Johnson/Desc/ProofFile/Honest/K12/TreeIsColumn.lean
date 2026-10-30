-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/TreeIsColumn.lean: two texts that compute a stretch of a tree's
column give the same words, at every position: `symbolsOf`, by which a sending builds the column of
its table (`columnOf`, Johnson/Desc/ProofFile/Honest/K14/Sendings.lean), and `wordsAt` over `symOf`
(RunRows.lean, RunJob.lean), by which a job on words builds the column of a tree that its test
opens. General in the stage, the message and the rows. It imports Mathlib.

  `symbolsOf_field`   the sender's stretch: for each row the symbol over the field (`symG`,
                 Johnson/Prover/Link/Base.lean) of the row's decoded entries and tail, encoded
  `layRows_fst`, `layRows_snd`   of two blocks, the rows of the one that covers a row
  `mainWords`, `maskWords`, `freshWords`   the job's stretch for a piece of main rows, of mask rows,
                 of the fresh table: the same form
  `main_piece`   member 0's main rows, where the other member has no main row in front of them:
                 the job's stretch is the sender's, if the decoded entries agree
  `mask_piece`   member 1's mask rows, where member 0 has no mask row: alike
  `fresh_piece`  the fresh table's rows: alike
  `coin_below`, `read_congr`   an entry of `laid` at a tabulated place, decoded, reads the random
                 values below the message's count alone, decoded

By what. `col_symE` (RunByCols.lean): a symbol computed on words, at any two lists, is the field's
symbol of the decoded lists, encoded; so nothing is asked of the words. The library's `symG_congr`.
`spot_reads` (KeptLaw3.lean) for `read_congr`.

Limits. Equations of two texts. Which rows lie in which tree, and whether two families of random
values agree, are premises here. Main rows over the extension field alone (`base` is false). Nothing
on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.RunJobLaw
import Johnson.Desc.ProofFile.Honest.K12.RunByCols
import Johnson.Desc.ProofFile.Honest.K12.KeptLaw3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes (Codes OracleShape)
open OnBytes.Slice (GE ofE toE lst readE)
open Johnson.Prover.Link (PS symG symG_congr mainSym maskSym freshSym)
open Fmt.M1 (Stage)
open Fmt.M1.Own (PSt words)
open H2K.Pub (sgOf)
open ProofFile.Honest.K14 (Laid laid dueOf symbolsOf)

/-! ## 1 The sender's stretch -/

theorem symbolsOf_field (c : OnBytes.Code) (x n : ℕ) (row tail : ℕ → ℕ → OnBytes.E) :
    symbolsOf c x n row tail = (List.range n).flatMap fun r =>
      words (ofE (symG ⟨c.logN, c.ell, c.r⟩ x (fun j => readE (row r j))
        fun t => readE (tail r t))) := by
  unfold symbolsOf
  refine congrArg List.flatten (List.map_congr_left fun r _ => ?_)
  show words (Fmt.M1.symE ⟨c.logN, c.ell, c.r⟩ x _ _) = _
  rw [col_symE]
  refine congrArg (fun y => words (ofE y)) (symG_congr _ x _ _ _ _ (fun j hj => ?_) fun t ht => ?_)
  · exact lst_range c.ell _ j hj
  · exact lst_range c.r _ t ht

/-! ## 2 Two blocks -/

theorem layRows_fst (n len b : ℕ) (B0 B1 : RowBlock) (hb : b < n)
    (h : B0.first ≤ b ∧ b < B0.first + B0.count) :
    (layRows n len [B0, B1]).getD b [] = B0.rows.getD (b - B0.first) [] := by
  unfold layRows
  rw [getD_range n _ _ b hb]
  simp only [List.findSome?_cons, if_pos h, Option.getD_some]

theorem layRows_snd (n len b : ℕ) (B0 B1 : RowBlock) (hb : b < n) (h0 : B0.count = 0)
    (h : B1.first ≤ b ∧ b < B1.first + B1.count) :
    (layRows n len [B0, B1]).getD b [] = B1.rows.getD (b - B1.first) [] := by
  have hn : ¬ (B0.first ≤ b ∧ b < B0.first + B0.count) := by
    rw [h0]
    omega
  unfold layRows
  rw [getD_range n _ _ b hb]
  simp only [List.findSome?_cons, if_neg hn, if_pos h, Option.getD_some]

theorem tabE_row (r n : ℕ) (f : ℕ → ℕ → OnBytes.E) (i : ℕ) (h : i < r) :
    (tabE r n f).getD i [] = (List.range n).map fun j => (f i j).triple := by
  unfold tabE
  rw [getD_range r _ _ i h]

theorem lst_tabE (r n : ℕ) (f : ℕ → ℕ → OnBytes.E) (i j : ℕ) (hi : i < r) (hj : j < n) :
    lst ((tabE r n f).getD i []) j = readE (f i j) := by
  rw [tabE_row r n f i hi, lst_range n _ j hj]
  rfl

/-! ## 3 The job's stretch -/

theorem wordsAt_map (sym : Sel → Fmt.M1.E) (n : ℕ) (f : ℕ → Sel) (hf : ∀ r, (f r).base = false) :
    wordsAt sym ((List.range n).map f) = (List.range n).flatMap fun r => words (sym (f r)) := by
  unfold wordsAt
  rw [List.flatMap_map]
  refine congrArg List.flatten (List.map_congr_left fun r _ => ?_)
  rw [hf r]
  rfl

theorem mainWords (s : Stage) (hk : s.h ≤ s.k) (P : PS) (x first n : ℕ) (hn : first + n ≤ 2 ^ s.k) :
    wordsAt (symOf s P x) ((List.range n).map fun r => ⟨.main, first + r, false⟩) =
      (List.range n).flatMap fun r =>
        words (ofE (symG s.C x (fun j => P.tabM (first + r + 2 ^ s.k * j))
          (P.tM (first + r)))) := by
  rw [wordsAt_map _ _ _ fun _ => rfl]
  refine congrArg List.flatten (List.map_congr_left fun r hr => ?_)
  have hr' : first + r < 2 ^ s.k := by
    have := List.mem_range.1 hr
    omega
  show words (if first + r < 2 ^ s.k then ofE (mainSym (sgOf s) P.tabM P.tM x (first + r))
    else Fmt.Fld.zeroE) = _
  rw [if_pos hr']
  show words (ofE (symG s.C x (fun j => P.tabM (first + r + 2 ^ ((sgOf s).h + (sgOf s).g) * j))
    (P.tM (first + r)))) = _
  rw [sg_k hk]

theorem maskWords (s : Stage) (P : PS) (x first n : ℕ) (hn : first + n ≤ 2 ^ s.h) :
    wordsAt (symOf s P x) ((List.range n).map fun r => ⟨.mask, first + r, false⟩) =
      (List.range n).flatMap fun r =>
        words (ofE (symG s.Z (x % 2 ^ s.Z.a) (fun j => P.tabZ (first + r + 2 ^ s.h * j))
          (P.tZ (first + r)))) := by
  rw [wordsAt_map _ _ _ fun _ => rfl]
  refine congrArg List.flatten (List.map_congr_left fun r hr => ?_)
  have hr' : first + r < 2 ^ s.h := by
    have := List.mem_range.1 hr
    omega
  show words (if first + r < 2 ^ s.h then ofE (maskSym (sgOf s) P.tabZ P.tZ x (first + r))
    else Fmt.Fld.zeroE) = _
  rw [if_pos hr']
  rfl

theorem freshWords (s : Stage) (P : PS) (x : ℕ) :
    wordsAt (symOf s P x) ((List.range (2 ^ s.h)).map fun r => ⟨.fresh, r, false⟩) =
      (List.range (2 ^ s.h)).flatMap fun r =>
        words (ofE (symG s.Z (x % 2 ^ s.Z.a) (P.fM r) (P.fT r))) := by
  rw [wordsAt_map _ _ _ fun _ => rfl]
  refine congrArg List.flatten (List.map_congr_left fun r hr => ?_)
  show words (if r < 2 ^ s.h then ofE (freshSym (sgOf s) P.fM P.fT x r) else Fmt.Fld.zeroE) = _
  rw [if_pos (List.mem_range.1 hr)]
  rfl

/-! ## 4 A piece against the sender's stretch -/

/-- The three numbers of a code of OnBytes/ that passes `sameCode` are the stage's code. -/
theorem code_of_same {c : OnBytes.Code} {d : Fmt.M1.Code} (h : sameCode c d = true) :
    (⟨c.logN, c.ell, c.r⟩ : Fmt.M1.Code) = d := by
  unfold sameCode at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  rw [h1, h2, h3]

/-- **Member 0's main rows.** P: a state whose main table and tails are read off the stage's lists.
L: what the member's rows are tabulated from. L': the sender's. -/
theorem main_piece (s : Stage) (hk : s.h ≤ s.k) (c : OnBytes.Code) (hc : sameCode c s.C = true)
    (m0 m1 : MemShape) (q0 q1 : PSt) (L L' : Laid) (n : ℕ) (P : PS) (x : ℕ)
    (hM : q0.M = tabE n c.ell L.main) (hR : q0.Rh = tabE n c.r L.mainTail)
    (hn : m0.mainRows = n) (hb : m0.base = false) (hin : m0.mainFirst + n ≤ 2 ^ s.k)
    (hP : P.tabM = (readPS s (layFirst s [(m0, q0), (m1, q1)])).tabM)
    (hT : P.tM = (readPS s (layFirst s [(m0, q0), (m1, q1)])).tM)
    (em : ∀ r < n, ∀ j < c.ell, readE (L.main r j) = readE (L'.main r j))
    (et : ∀ r < n, ∀ t < c.r, readE (L.mainTail r t) = readE (L'.mainTail r t)) :
    wordsAt (symOf s P x) (selsOf s [m0, m1] (.main 0)) = symbolsOf c x n L'.main L'.mainTail := by
  have e0 : selsOf s [m0, m1] (.main 0) =
      (List.range n).map fun r => ⟨.main, m0.mainFirst + r, false⟩ := by
    show (List.range m0.mainRows).map (fun r => (⟨.main, m0.mainFirst + r, m0.base⟩ : Sel)) = _
    rw [hn, hb]
  rw [e0, mainWords s hk P x _ n hin, symbolsOf_field, code_of_same hc]
  have hl : c.ell = s.C.l := congrArg Fmt.M1.Code.l (code_of_same hc)
  have hr0 : c.r = s.C.r := congrArg Fmt.M1.Code.r (code_of_same hc)
  refine congrArg List.flatten (List.map_congr_left fun r hr => ?_)
  have hr' : r < n := List.mem_range.1 hr
  have hlt : m0.mainFirst + r < 2 ^ s.k := by omega
  have hcov : m0.mainFirst ≤ m0.mainFirst + r ∧ m0.mainFirst + r < m0.mainFirst + m0.mainRows := by
    rw [hn]
    omega
  refine congrArg (fun y => words (ofE y)) (symG_congr _ x _ _ _ _ (fun j hj => ?_) fun t ht => ?_)
  · rw [hP]
    show lst ((layRows (2 ^ s.k) s.C.l [⟨m0.mainFirst, m0.mainRows, q0.M⟩,
      ⟨m1.mainFirst, m1.mainRows, q1.M⟩]).getD ((m0.mainFirst + r + 2 ^ s.k * j) % 2 ^ s.k) [])
      ((m0.mainFirst + r + 2 ^ s.k * j) / 2 ^ s.k) = _
    rw [(split_idx s.k _ j hlt).1, (split_idx s.k _ j hlt).2, layRows_fst _ _ _ _ _ hlt hcov]
    show lst (q0.M.getD (m0.mainFirst + r - m0.mainFirst) []) j = _
    rw [Nat.add_sub_cancel_left, hM, lst_tabE n c.ell _ r j hr' (by rw [hl]; exact hj)]
    exact em r hr' j (by rw [hl]; exact hj)
  · rw [hT]
    show lst ((layRows (2 ^ s.k) s.C.r [⟨m0.mainFirst, m0.mainRows, q0.Rh⟩,
      ⟨m1.mainFirst, m1.mainRows, q1.Rh⟩]).getD (m0.mainFirst + r) []) t = _
    rw [layRows_fst _ _ _ _ _ hlt hcov]
    show lst (q0.Rh.getD (m0.mainFirst + r - m0.mainFirst) []) t = _
    rw [Nat.add_sub_cancel_left, hR, lst_tabE n c.r _ r t hr' (by rw [hr0]; exact ht)]
    exact et r hr' t (by rw [hr0]; exact ht)

/-- **Member 1's mask rows**, where member 0 has none. -/
theorem mask_piece (s : Stage) (z : OnBytes.Code) (hz : sameCode z s.Z = true)
    (m0 m1 : MemShape) (q0 q1 : PSt) (L L' : Laid) (n : ℕ) (P : PS) (x : ℕ)
    (hW : q1.W = tabE n z.ell L.mask) (hS : q1.Sg = tabE n z.r L.maskTail)
    (h0 : m0.maskRows = 0) (hn : m1.maskRows = n) (hin : m1.maskFirst + n ≤ 2 ^ s.h)
    (hP : P.tabZ = (readPS s (layFirst s [(m0, q0), (m1, q1)])).tabZ)
    (hT : P.tZ = (readPS s (layFirst s [(m0, q0), (m1, q1)])).tZ)
    (em : ∀ r < n, ∀ j < z.ell, readE (L.mask r j) = readE (L'.mask r j))
    (et : ∀ r < n, ∀ t < z.r, readE (L.maskTail r t) = readE (L'.maskTail r t)) :
    wordsAt (symOf s P x) (selsOf s [m0, m1] (.mask 1)) =
      symbolsOf z (x % 2 ^ z.logN) n L'.mask L'.maskTail := by
  have e0 : selsOf s [m0, m1] (.mask 1) =
      (List.range n).map fun r => ⟨.mask, m1.maskFirst + r, false⟩ := by
    show (List.range m1.maskRows).map (fun r => (⟨.mask, m1.maskFirst + r, false⟩ : Sel)) = _
    rw [hn]
  have ha : z.logN = s.Z.a := congrArg Fmt.M1.Code.a (code_of_same hz)
  have hl : z.ell = s.Z.l := congrArg Fmt.M1.Code.l (code_of_same hz)
  have hr0 : z.r = s.Z.r := congrArg Fmt.M1.Code.r (code_of_same hz)
  rw [e0, maskWords s P x _ n hin, symbolsOf_field, code_of_same hz, ha]
  refine congrArg List.flatten (List.map_congr_left fun r hr => ?_)
  have hr' : r < n := List.mem_range.1 hr
  have hlt : m1.maskFirst + r < 2 ^ s.h := by omega
  have hcov : m1.maskFirst ≤ m1.maskFirst + r ∧ m1.maskFirst + r < m1.maskFirst + m1.maskRows := by
    rw [hn]
    omega
  refine congrArg (fun y => words (ofE y)) (symG_congr _ _ _ _ _ _ (fun j hj => ?_) fun t ht => ?_)
  · rw [hP]
    show lst ((layRows (2 ^ s.h) s.Z.l [⟨m0.maskFirst, m0.maskRows, q0.W⟩,
      ⟨m1.maskFirst, m1.maskRows, q1.W⟩]).getD ((m1.maskFirst + r + 2 ^ s.h * j) % 2 ^ s.h) [])
      ((m1.maskFirst + r + 2 ^ s.h * j) / 2 ^ s.h) = _
    rw [(split_idx s.h _ j hlt).1, (split_idx s.h _ j hlt).2, layRows_snd _ _ _ _ _ hlt h0 hcov]
    show lst (q1.W.getD (m1.maskFirst + r - m1.maskFirst) []) j = _
    rw [Nat.add_sub_cancel_left, hW, lst_tabE n z.ell _ r j hr' (by rw [hl]; exact hj)]
    exact em r hr' j (by rw [hl]; exact hj)
  · rw [hT]
    show lst ((layRows (2 ^ s.h) s.Z.r [⟨m0.maskFirst, m0.maskRows, q0.Sg⟩,
      ⟨m1.maskFirst, m1.maskRows, q1.Sg⟩]).getD (m1.maskFirst + r) []) t = _
    rw [layRows_snd _ _ _ _ _ hlt h0 hcov]
    show lst (q1.Sg.getD (m1.maskFirst + r - m1.maskFirst) []) t = _
    rw [Nat.add_sub_cancel_left, hS, lst_tabE n z.r _ r t hr' (by rw [hr0]; exact ht)]
    exact et r hr' t (by rw [hr0]; exact ht)

/-- **The fresh table's rows.** L': the sender's. -/
theorem fresh_piece (s : Stage) (z : OnBytes.Code) (hz : sameCode z s.Z = true)
    (ms : List MemShape) (L' : Laid) (P : PS) (x : ℕ)
    (em : ∀ b < 2 ^ s.h, ∀ j < s.Z.l, readE (L'.mask b j) = P.fM b j)
    (et : ∀ b < 2 ^ s.h, ∀ q < s.Z.r, readE (L'.maskTail b q) = P.fT b q) :
    wordsAt (symOf s P x) (selsOf s ms .fresh) =
      symbolsOf z (x % 2 ^ z.logN) (2 ^ s.h) L'.mask L'.maskTail := by
  have ha : z.logN = s.Z.a := congrArg Fmt.M1.Code.a (code_of_same hz)
  show wordsAt (symOf s P x) ((List.range (2 ^ s.h)).map fun r => ⟨.fresh, r, false⟩) = _
  rw [freshWords, symbolsOf_field, code_of_same hz, ha]
  refine congrArg List.flatten (List.map_congr_left fun r hr => ?_)
  have hr' : r < 2 ^ s.h := List.mem_range.1 hr
  exact congrArg (fun y => words (ofE y)) (symG_congr _ _ _ _ _ _
    (fun j hj => (em r hr' j hj).symm) fun t ht => (et r hr' t ht).symm)

/-! ## 5 What an entry reads of the random values -/

theorem coin_below {codes : Codes} {s : OracleShape} {high : Bool}
    (hp : ((spotsOf codes s).filterMap (coinOf codes s)).Perm
      (List.range (dueOf codes s (.plain high)))) {x : Spot} (hx : x ∈ spotsOf codes s) {i : ℕ}
    (hc : coinOf codes s x = some i) : i < dueOf codes s (.plain high) :=
  List.mem_range.1 (hp.mem_iff.1 (List.mem_filterMap.2 ⟨x, hx, hc⟩))

/-- An entry at a tabulated place, decoded, reads the values below the count alone, decoded. -/
theorem read_congr (codes : Codes) (s : OracleShape) (v cs cs' : ℕ → OnBytes.E) (high : Bool)
    (hp : ((spotsOf codes s).filterMap (coinOf codes s)).Perm
      (List.range (dueOf codes s (.plain high))))
    (H : ∀ i < dueOf codes s (.plain high), readE (cs i) = readE (cs' i)) (x : Spot)
    (hx : x ∈ spotsOf codes s) :
    readE ((laid codes s v cs (.plain high)).read x) =
      readE ((laid codes s v cs' (.plain high)).read x) := by
  rw [spot_reads codes s v cs high x, spot_reads codes s v cs' high x]
  cases hc : coinOf codes s x with
  | none => rfl
  | some i => exact H i (coin_below hp hx hc)

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.symbolsOf_field
#print axioms ProofFile.Honest.K12.Light.layRows_fst
#print axioms ProofFile.Honest.K12.Light.layRows_snd
#print axioms ProofFile.Honest.K12.Light.tabE_row
#print axioms ProofFile.Honest.K12.Light.lst_tabE
#print axioms ProofFile.Honest.K12.Light.wordsAt_map
#print axioms ProofFile.Honest.K12.Light.mainWords
#print axioms ProofFile.Honest.K12.Light.maskWords
#print axioms ProofFile.Honest.K12.Light.freshWords
#print axioms ProofFile.Honest.K12.Light.code_of_same
#print axioms ProofFile.Honest.K12.Light.main_piece
#print axioms ProofFile.Honest.K12.Light.mask_piece
#print axioms ProofFile.Honest.K12.Light.fresh_piece
#print axioms ProofFile.Honest.K12.Light.coin_below
#print axioms ProofFile.Honest.K12.Light.read_congr
