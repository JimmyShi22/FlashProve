--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/Part4/OwnTakenPieces.lean: A JOB ON THREE MEMBERS WHOSE FIRST TWO ARE
MESSAGES OF SENDINGS OF THE KIND K1: a stretch of a tree's column, as the job computes it, is the
stretch of the sending's written column. General in the stage, the members and the rows.

WHAT IT IS NOT. Equations of two texts. Which rows lie in which tree, that the blocks do not overlap
and that the rows are the sender's are premises here. Main rows over the extension field alone. No
run, no coin, no book. Nothing on completeness, on soundness or on what is hidden.

  `shape_ofSending`, `shape_ofK1`   a member's public numbers, the first rows a letter
  `shapeAt_alike`, `trees_alike`, `startR_alike`, `dueR_alike`   what reads of a sending's parameters
                         its codes and messages alone
  `tabG_row`, `lst_tabG`   an entry of rows tabulated as words (`tabG`, K12/AtProof/JobW.lean), decoded
  `layRows_first`, `layRows_second`   of three blocks, the rows of the first that covers a row
  `first_three_mask`     the first state's mask tables are read off the stage's lists: the like of
                         `first_three` (K12/AtFile/WJointTree.lean) for the mask rows
  `mask_piece_first`, `mask_piece_second`, `main_piece_second`, `fresh_stretch`   the job's stretch
                         for a piece, in the form of `maskSyms` and `mainSyms`
                         (Johnson/Prover/Send/Core.lean)
  `col_of_mine`          the written column over the list of the tree's messages
  `treeTbl_at`           K1's text of a tree's table, where the part's coins are cut and the plan
                         passes its test: the table's depth, width and columns

CALLED: `maskWords`, `mainWords`, `freshWords` (K12/TreeIsColumn.lean) · `rows_three`
(WJointTree.lean) · `col_treeTable` (K12/TreesSentBeforeTestFromSentTable.lean) · `treeTbl_some` (K1/ScriptLots.lean). The
proofs of the pieces follow `mask_piece`, `main_piece_third` line by line.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WJointTree
import Johnson.Desc.ProofFile.Honest.K12.AtProof.JobW
import Johnson.Desc.ProofFile.Honest.K12.TreesSentBeforeTestFromSentTable
import Johnson.Desc.ProofFile.Honest.K1.ScriptLots

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Part4
open OnBytes.Slice (GE ofE toE lst)
open Johnson.Prover.Link (PS symG symG_congr words3)
open Johnson.Prover.Send (Rows col mainSyms maskSyms)
open Fmt.M1 (Stage)
open Fmt.M1.Own (PSt words)
open ProofFile.Honest.K12.Light
open ProofFile.Honest.K12.AtProof (tabG)

/-- A member made of a message of a sending of the shared chain: its public numbers. fs is a letter
here, so that no caller has to unfold what it lays there. -/
theorem shape_ofSending {W X : Type} (J : K14.SendJob) (a : Addr) (k : ℕ) (fs : Option ℕ × Option ℕ)
    (ask : W → K14.Ask) (v? : Option (W → Front X → ℕ → OnBytes.E)) :
    (memOfSending J a k fs ask v?).shape =
      ⟨fs.1.getD 0, (Light.shapeAt J k).mainRows, fs.2.getD 0, (Light.shapeAt J k).maskRows,
        (Light.shapeAt J k).mainDeg == 1⟩ := rfl

/-- The like for a message of a sending of the kind K1. -/
theorem shape_ofK1 {W Wd X : Type} (J : K1.SendJob Wd X) (lift : W → Wd) (a : Addr) (k : ℕ)
    (fs : Option ℕ × Option ℕ) :
    (AtProof.memK1 J lift a k fs).shape =
      ⟨fs.1.getD 0, (Johnson.Prover.Send.shapeAt J.P k).mainRows, fs.2.getD 0,
        (Johnson.Prover.Send.shapeAt J.P k).maskRows,
        (Johnson.Prover.Send.shapeAt J.P k).mainDeg == 1⟩ := rfl

/-! ### What reads of a sending's parameters its codes and messages alone -/

section Alike
variable {P' P : VerifiableInference.Desc.K1.Par}

theorem shapeAt_alike (hs : P'.sent = P.sent) (k : ℕ) :
    Johnson.Prover.Send.shapeAt P' k = Johnson.Prover.Send.shapeAt P k := by
  unfold Johnson.Prover.Send.shapeAt
  rw [hs]

theorem trees_alike (hc : P'.codes = P.codes) (hs : P'.sent = P.sent) : P'.trees = P.trees := by
  unfold VerifiableInference.Desc.K1.Par.trees
  rw [hc, hs]

theorem startR_alike (hc : P'.codes = P.codes) (hs : P'.sent = P.sent) (ride : ℕ → Option K1.Ride)
    (k : ℕ) : K1.startR P' ride k = K1.startR P ride k := by
  unfold K1.startR
  simp only [hc, shapeAt_alike hs]

theorem dueR_alike (hc : P'.codes = P.codes) (hs : P'.sent = P.sent) (ride : ℕ → Option K1.Ride) :
    K1.dueR P' ride = K1.dueR P ride := by
  unfold K1.dueR
  rw [startR_alike hc hs, hs]

end Alike

/-- A row of rows tabulated as words. -/
theorem tabG_row (r n : ℕ) (f : ℕ → ℕ → GE) (i : ℕ) (h : i < r) :
    (tabG r n f).getD i [] = (List.range n).map fun j => ofE (f i j) := by
  unfold tabG
  rw [getD_range r _ _ i h]

/-- An entry of it, decoded. -/
theorem lst_tabG (r n : ℕ) (f : ℕ → ℕ → GE) (i j : ℕ) (hi : i < r) (hj : j < n) :
    lst ((tabG r n f).getD i []) j = f i j := by
  rw [tabG_row r n f i hi, lst_range n _ j hj]
  exact OnBytes.Slice.toE_ofE _

/-- Of three blocks, the first's rows at a row that it covers. -/
theorem layRows_first (n len b : ℕ) (B0 B1 B2 : RowBlock) (hb : b < n)
    (h : B0.first ≤ b ∧ b < B0.first + B0.count) :
    (layRows n len [B0, B1, B2]).getD b [] = B0.rows.getD (b - B0.first) [] := by
  unfold layRows
  rw [getD_range n _ _ b hb]
  simp only [List.findSome?_cons, if_pos h, Option.getD_some]

/-- Of three blocks, the second's rows at a row that the first does not cover. -/
theorem layRows_second (n len b : ℕ) (B0 B1 B2 : RowBlock) (hb : b < n)
    (h0 : ¬ (B0.first ≤ b ∧ b < B0.first + B0.count))
    (h : B1.first ≤ b ∧ b < B1.first + B1.count) :
    (layRows n len [B0, B1, B2]).getD b [] = B1.rows.getD (b - B1.first) [] := by
  unfold layRows
  rw [getD_range n _ _ b hb]
  simp only [List.findSome?_cons, if_neg h0, if_pos h, Option.getD_some]

/-- The first state's mask tables are read off the stage's lists. -/
theorem first_three_mask {W X : Type} (B : ManyJob W X) (mA mB mC : Mem W X)
    (hm : B.mems = [mA, mB, mC]) (w : W) (fr : Front X) (C : TestCoins) :
    (B.toRun.toTest.first w fr C).tabZ = (readPS B.s₀ (layFirst B.s₀
        [(mA.shape, mA.rows w fr (C.mem 0)), (mB.shape, mB.rows w fr (C.mem 1)),
          (mC.shape, mC.rows w fr (C.mem 2))])).tabZ ∧
      (B.toRun.toTest.first w fr C).tZ = (readPS B.s₀ (layFirst B.s₀
        [(mA.shape, mA.rows w fr (C.mem 0)), (mB.shape, mB.rows w fr (C.mem 1)),
          (mC.shape, mC.rows w fr (C.mem 2))])).tZ := by
  rw [← rows_three B mA mB mC hm w fr C.mem]
  exact ⟨rfl, rfl⟩

/-- **The first member's mask rows.** -/
theorem mask_piece_first (s : Stage) (m0 m1 m2 : MemShape) (q0 q1 q2 : PSt)
    (mask tail : ℕ → ℕ → GE) (n : ℕ) (P : PS) (x : ℕ)
    (hW : q0.W = tabG n s.Z.l mask) (hS : q0.Sg = tabG n s.Z.r tail) (hn : m0.maskRows = n)
    (hin : m0.maskFirst + n ≤ 2 ^ s.h)
    (hP : P.tabZ = (readPS s (layFirst s [(m0, q0), (m1, q1), (m2, q2)])).tabZ)
    (hT : P.tZ = (readPS s (layFirst s [(m0, q0), (m1, q1), (m2, q2)])).tZ) :
    Light.wordsAt (symOf s P x) (selsOf s [m0, m1, m2] (.mask 0)) =
      (List.range n).flatMap fun r =>
        words3 (ofE (symG s.Z (x % 2 ^ s.Z.a) (mask r) (tail r))) := by
  have e0 : selsOf s [m0, m1, m2] (.mask 0) =
      (List.range n).map fun r => ⟨.mask, m0.maskFirst + r, false⟩ := by
    show (List.range m0.maskRows).map (fun r => (⟨.mask, m0.maskFirst + r, false⟩ : Sel)) = _
    rw [hn]
  rw [e0, Light.maskWords s P x _ n hin]
  refine congrArg List.flatten (List.map_congr_left fun r hr => ?_)
  have hr' : r < n := List.mem_range.1 hr
  have hlt : m0.maskFirst + r < 2 ^ s.h := by omega
  have hcov : m0.maskFirst ≤ m0.maskFirst + r ∧ m0.maskFirst + r < m0.maskFirst + m0.maskRows := by
    rw [hn]
    omega
  refine congrArg (fun y => words (ofE y)) (symG_congr _ _ _ _ _ _ (fun j hj => ?_) fun t ht => ?_)
  · rw [hP]
    show lst ((layRows (2 ^ s.h) s.Z.l [⟨m0.maskFirst, m0.maskRows, q0.W⟩,
      ⟨m1.maskFirst, m1.maskRows, q1.W⟩, ⟨m2.maskFirst, m2.maskRows, q2.W⟩]).getD
        ((m0.maskFirst + r + 2 ^ s.h * j) % 2 ^ s.h) [])
      ((m0.maskFirst + r + 2 ^ s.h * j) / 2 ^ s.h) = _
    rw [(split_idx s.h _ j hlt).1, (split_idx s.h _ j hlt).2, layRows_first _ _ _ _ _ _ hlt hcov]
    show lst (q0.W.getD (m0.maskFirst + r - m0.maskFirst) []) j = _
    rw [Nat.add_sub_cancel_left, hW, lst_tabG n s.Z.l _ r j hr' hj]
  · rw [hT]
    show lst ((layRows (2 ^ s.h) s.Z.r [⟨m0.maskFirst, m0.maskRows, q0.Sg⟩,
      ⟨m1.maskFirst, m1.maskRows, q1.Sg⟩, ⟨m2.maskFirst, m2.maskRows, q2.Sg⟩]).getD
        (m0.maskFirst + r) []) t = _
    rw [layRows_first _ _ _ _ _ _ hlt hcov]
    show lst (q0.Sg.getD (m0.maskFirst + r - m0.maskFirst) []) t = _
    rw [Nat.add_sub_cancel_left, hS, lst_tabG n s.Z.r _ r t hr' ht]

/-- **The second member's mask rows**, where the first member's block does not cover them. -/
theorem mask_piece_second (s : Stage) (m0 m1 m2 : MemShape) (q0 q1 q2 : PSt)
    (mask tail : ℕ → ℕ → GE) (n : ℕ) (P : PS) (x : ℕ)
    (hW : q1.W = tabG n s.Z.l mask) (hS : q1.Sg = tabG n s.Z.r tail) (hn : m1.maskRows = n)
    (hin : m1.maskFirst + n ≤ 2 ^ s.h)
    (d0 : ∀ r < n, ¬ (m0.maskFirst ≤ m1.maskFirst + r ∧
      m1.maskFirst + r < m0.maskFirst + m0.maskRows))
    (hP : P.tabZ = (readPS s (layFirst s [(m0, q0), (m1, q1), (m2, q2)])).tabZ)
    (hT : P.tZ = (readPS s (layFirst s [(m0, q0), (m1, q1), (m2, q2)])).tZ) :
    Light.wordsAt (symOf s P x) (selsOf s [m0, m1, m2] (.mask 1)) =
      (List.range n).flatMap fun r =>
        words3 (ofE (symG s.Z (x % 2 ^ s.Z.a) (mask r) (tail r))) := by
  have e0 : selsOf s [m0, m1, m2] (.mask 1) =
      (List.range n).map fun r => ⟨.mask, m1.maskFirst + r, false⟩ := by
    show (List.range m1.maskRows).map (fun r => (⟨.mask, m1.maskFirst + r, false⟩ : Sel)) = _
    rw [hn]
  rw [e0, Light.maskWords s P x _ n hin]
  refine congrArg List.flatten (List.map_congr_left fun r hr => ?_)
  have hr' : r < n := List.mem_range.1 hr
  have hlt : m1.maskFirst + r < 2 ^ s.h := by omega
  have hcov : m1.maskFirst ≤ m1.maskFirst + r ∧ m1.maskFirst + r < m1.maskFirst + m1.maskRows := by
    rw [hn]
    omega
  refine congrArg (fun y => words (ofE y)) (symG_congr _ _ _ _ _ _ (fun j hj => ?_) fun t ht => ?_)
  · rw [hP]
    show lst ((layRows (2 ^ s.h) s.Z.l [⟨m0.maskFirst, m0.maskRows, q0.W⟩,
      ⟨m1.maskFirst, m1.maskRows, q1.W⟩, ⟨m2.maskFirst, m2.maskRows, q2.W⟩]).getD
        ((m1.maskFirst + r + 2 ^ s.h * j) % 2 ^ s.h) [])
      ((m1.maskFirst + r + 2 ^ s.h * j) / 2 ^ s.h) = _
    rw [(split_idx s.h _ j hlt).1, (split_idx s.h _ j hlt).2,
      layRows_second _ _ _ _ _ _ hlt (d0 r hr') hcov]
    show lst (q1.W.getD (m1.maskFirst + r - m1.maskFirst) []) j = _
    rw [Nat.add_sub_cancel_left, hW, lst_tabG n s.Z.l _ r j hr' hj]
  · rw [hT]
    show lst ((layRows (2 ^ s.h) s.Z.r [⟨m0.maskFirst, m0.maskRows, q0.Sg⟩,
      ⟨m1.maskFirst, m1.maskRows, q1.Sg⟩, ⟨m2.maskFirst, m2.maskRows, q2.Sg⟩]).getD
        (m1.maskFirst + r) []) t = _
    rw [layRows_second _ _ _ _ _ _ hlt (d0 r hr') hcov]
    show lst (q1.Sg.getD (m1.maskFirst + r - m1.maskFirst) []) t = _
    rw [Nat.add_sub_cancel_left, hS, lst_tabG n s.Z.r _ r t hr' ht]

/-- **The second member's main rows**, over the extension field, where the first member's block does
not cover them. -/
theorem main_piece_second (s : Stage) (hk : s.h ≤ s.k) (m0 m1 m2 : MemShape) (q0 q1 q2 : PSt)
    (main tail : ℕ → ℕ → GE) (n : ℕ) (P : PS) (x : ℕ)
    (hM : q1.M = tabG n s.C.l main) (hR : q1.Rh = tabG n s.C.r tail) (hn : m1.mainRows = n)
    (hb : m1.base = false) (hin : m1.mainFirst + n ≤ 2 ^ s.k)
    (d0 : ∀ r < n, ¬ (m0.mainFirst ≤ m1.mainFirst + r ∧
      m1.mainFirst + r < m0.mainFirst + m0.mainRows))
    (hP : P.tabM = (readPS s (layFirst s [(m0, q0), (m1, q1), (m2, q2)])).tabM)
    (hT : P.tM = (readPS s (layFirst s [(m0, q0), (m1, q1), (m2, q2)])).tM) :
    Light.wordsAt (symOf s P x) (selsOf s [m0, m1, m2] (.main 1)) =
      (List.range n).flatMap fun r => words3 (ofE (symG s.C x (main r) (tail r))) := by
  have e0 : selsOf s [m0, m1, m2] (.main 1) =
      (List.range n).map fun r => ⟨.main, m1.mainFirst + r, false⟩ := by
    show (List.range m1.mainRows).map (fun r => (⟨.main, m1.mainFirst + r, m1.base⟩ : Sel)) = _
    rw [hn, hb]
  rw [e0, Light.mainWords s hk P x _ n hin]
  refine congrArg List.flatten (List.map_congr_left fun r hr => ?_)
  have hr' : r < n := List.mem_range.1 hr
  have hlt : m1.mainFirst + r < 2 ^ s.k := by omega
  have hcov : m1.mainFirst ≤ m1.mainFirst + r ∧ m1.mainFirst + r < m1.mainFirst + m1.mainRows := by
    rw [hn]
    omega
  refine congrArg (fun y => words (ofE y)) (symG_congr _ x _ _ _ _ (fun j hj => ?_) fun t ht => ?_)
  · rw [hP]
    show lst ((layRows (2 ^ s.k) s.C.l [⟨m0.mainFirst, m0.mainRows, q0.M⟩,
      ⟨m1.mainFirst, m1.mainRows, q1.M⟩, ⟨m2.mainFirst, m2.mainRows, q2.M⟩]).getD
        ((m1.mainFirst + r + 2 ^ s.k * j) % 2 ^ s.k) [])
      ((m1.mainFirst + r + 2 ^ s.k * j) / 2 ^ s.k) = _
    rw [(split_idx s.k _ j hlt).1, (split_idx s.k _ j hlt).2,
      layRows_second _ _ _ _ _ _ hlt (d0 r hr') hcov]
    show lst (q1.M.getD (m1.mainFirst + r - m1.mainFirst) []) j = _
    rw [Nat.add_sub_cancel_left, hM, lst_tabG n s.C.l _ r j hr' hj]
  · rw [hT]
    show lst ((layRows (2 ^ s.k) s.C.r [⟨m0.mainFirst, m0.mainRows, q0.Rh⟩,
      ⟨m1.mainFirst, m1.mainRows, q1.Rh⟩, ⟨m2.mainFirst, m2.mainRows, q2.Rh⟩]).getD
        (m1.mainFirst + r) []) t = _
    rw [layRows_second _ _ _ _ _ _ hlt (d0 r hr') hcov]
    show lst (q1.Rh.getD (m1.mainFirst + r - m1.mainFirst) []) t = _
    rw [Nat.add_sub_cancel_left, hR, lst_tabG n s.C.r _ r t hr' ht]

/-- **The fresh table's rows**, where the state's fresh table is these rows inside the code. -/
theorem fresh_stretch (s : Stage) (ms : List MemShape) (mask tail : ℕ → ℕ → GE) (P : PS) (x : ℕ)
    (em : ∀ b < 2 ^ s.h, ∀ j < s.Z.l, P.fM b j = mask b j)
    (et : ∀ b < 2 ^ s.h, ∀ q < s.Z.r, P.fT b q = tail b q) :
    Light.wordsAt (symOf s P x) (selsOf s ms .fresh) =
      (List.range (2 ^ s.h)).flatMap fun r =>
        words3 (ofE (symG s.Z (x % 2 ^ s.Z.a) (mask r) (tail r))) := by
  show Light.wordsAt (symOf s P x) ((List.range (2 ^ s.h)).map fun r => ⟨.fresh, r, false⟩) = _
  rw [Light.freshWords]
  refine congrArg List.flatten (List.map_congr_left fun r hr => ?_)
  have hr' : r < 2 ^ s.h := List.mem_range.1 hr
  exact congrArg (fun y => words (ofE y)) (symG_congr _ _ _ _ _ _ (fun j hj => em r hr' j hj)
    fun t ht => et r hr' t ht)

/-- The written column over the list of the tree's messages. -/
theorem col_of_mine (P : VerifiableInference.Desc.K1.Par) (V : ℕ → Rows) (τ x : ℕ) (mine : List ℕ)
    (h : ((List.range P.sent.size).filter fun k =>
      ((VerifiableInference.Desc.Own.treesMade P.codes P.sent).getD {}).tree[k]? == some τ) =
        mine) :
    col P V τ x = (mine.flatMap fun k => mainSyms P V k x) ++ mine.flatMap fun k => maskSyms P V k x := by
  unfold col
  simp only [h]

/-- **K1's text of a tree's table**, where the part's coins are cut, the plan passes its own test and
the tree is one of the plan's. -/
theorem treeTbl_at {Bk : ProverCoinCounts} {W Wl X : Type} (ch : ℕ) (wit : Wl → W) (J : K1.SendJob W X)
    (own₀ : X) (τ : ℕ) (k : Coins Bk) (c : Cs (K1.dueR J.P J.ride))
    (hc : K1.lentCut k ch ⟨J.P.place, 0⟩ (K1.dueR J.P J.ride) = some c)
    (hP : VerifiableInference.Desc.K1.planOkOwn J.P = true) (hτ : τ < J.P.trees.length) (w : Wl)
    (h : List Fmt.Drawn) :
    (K1.treeTbl ch wit J own₀ τ k w h).2.logLength = (J.P.trees.getD τ {}).logN ∧
      (K1.treeTbl ch wit J own₀ τ k w h).2.words =
        (J.P.trees.getD τ {}).mainWidth + (J.P.trees.getD τ {}).maskWidth ∧
      ∀ x, (K1.treeTbl ch wit J own₀ τ k w h).2.col x =
        col J.P (K1.rowsLaid J own₀ c (wit w) h) τ x := by
  have hlen : (K1.treeTables J.P (K1.rowsLaid J own₀ c (wit w) h)).length = J.P.trees.length := by
    simp [K1.treeTables]
  have hT : (K1.treeTables J.P (K1.rowsLaid J own₀ c (wit w) h))[τ]? =
      some ((K1.treeTables J.P (K1.rowsLaid J own₀ c (wit w) h))[τ]'(by rw [hlen]; exact hτ)) :=
    List.getElem?_eq_getElem _
  have e : (K1.treeTbl ch wit J own₀ τ k w h).2 =
      (K1.treeTables J.P (K1.rowsLaid J own₀ c (wit w) h))[τ]'(by rw [hlen]; exact hτ) := by
    rw [K1.treeTbl_some ch wit J own₀ τ k c hc w h]
    unfold K1.scriptTable
    rw [hT]
    rfl
  rw [e]
  refine ⟨?_, ?_, fun x => col_treeTable J.P _ hP τ x _ hT⟩
  · rw [List.getD_eq_getElem _ _ hτ]
    simp [K1.treeTables]
  · rw [List.getD_eq_getElem _ _ hτ]
    simp [K1.treeTables]

end ProofFile.Honest.K12.Part4

#print axioms ProofFile.Honest.K12.Part4.shape_ofSending
#print axioms ProofFile.Honest.K12.Part4.shape_ofK1
#print axioms ProofFile.Honest.K12.Part4.shapeAt_alike
#print axioms ProofFile.Honest.K12.Part4.trees_alike
#print axioms ProofFile.Honest.K12.Part4.startR_alike
#print axioms ProofFile.Honest.K12.Part4.dueR_alike
#print axioms ProofFile.Honest.K12.Part4.lst_tabG
#print axioms ProofFile.Honest.K12.Part4.layRows_first
#print axioms ProofFile.Honest.K12.Part4.layRows_second
#print axioms ProofFile.Honest.K12.Part4.first_three_mask
#print axioms ProofFile.Honest.K12.Part4.mask_piece_first
#print axioms ProofFile.Honest.K12.Part4.mask_piece_second
#print axioms ProofFile.Honest.K12.Part4.main_piece_second
#print axioms ProofFile.Honest.K12.Part4.fresh_stretch
#print axioms ProofFile.Honest.K12.Part4.col_of_mine
#print axioms ProofFile.Honest.K12.Part4.treeTbl_at
