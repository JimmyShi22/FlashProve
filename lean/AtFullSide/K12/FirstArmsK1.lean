-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K12/FirstArmsK1.lean: K1's side of the trees that the last chain's proximity test
takes over from the first chain (FirstArms, K12/AtFile/WJointArms.lean): the first chain's table of a
sending's tree, as the sender's written column.

  treeTbl_col, treeTbl_depth   a table of a K1 job's tree: its column, its depth
  cols_written                 the kernel: which messages lie in trees 1 of the first sending and 0 of W
  col_first, col_W             the two written columns, message by message
  member_rows                  a K1 member's rows at a stretch that holds the sender's coins

Limits. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.TreesSentBeforeTestFromSentTable
import Johnson.Desc.ProofFile.Honest.K12.AtProof.JobW
import Johnson.Desc.ProofFile.Honest.K1.ScriptLots
import Johnson.Desc.K1.Law.TiesWritten
import Johnson.Desc.ProofFile.Honest.K1.LotData
import Johnson.Desc.ProofFile.Honest.K1.PlaceFirst
import Johnson.Desc.ProofFile.Honest.K1.PlaceW

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K12
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.AtProof
open ProofFile.Honest.K1 (SendJob rowsLaid treeTbl lentCut scriptTable wordlessTable)
open VerifiableInference.Desc.K1 (parGF parWF)
open Johnson.Prover.Send (shapeAt col mainSyms maskSyms Rows)

variable {W' Wl X : Type} {Bk : ProverCoinCounts}

/-- **The column of a table of a K1 job's tree is the sender's written column.** -/
theorem treeTbl_col (ch : ℕ) (wit : Wl → W') (J : SendJob W' X) (own₀ : X) (τ : ℕ) (k : Coins Bk)
    (w : Wl) (h : List Fmt.Drawn) {c : Cs (K1.dueR J.P J.ride)}
    (hc : lentCut k ch ⟨J.P.place, 0⟩ (K1.dueR J.P J.ride) = some c)
    (hP : VerifiableInference.Desc.K1.planOkOwn J.P = true) (hτ : τ < J.P.trees.length) (x : ℕ) :
    (treeTbl ch wit J own₀ τ k w h).2.col x = col J.P (rowsLaid J own₀ c (wit w) h) τ x := by
  have hT : ∃ T, (K1.treeTables J.P (rowsLaid J own₀ c (wit w) h))[τ]? = some T := by
    have hl : τ < (K1.treeTables J.P (rowsLaid J own₀ c (wit w) h)).length := by
      unfold K1.treeTables
      rw [List.length_map, List.length_zipIdx]
      exact hτ
    exact ⟨_, List.getElem?_eq_getElem hl⟩
  obtain ⟨T, hT⟩ := hT
  have e : (treeTbl ch wit J own₀ τ k w h).2 = T := by
    unfold treeTbl
    rw [hc]
    show ((K1.treeTables J.P (rowsLaid J own₀ c (wit w) h))[τ]?).getD wordlessTable = T
    rw [hT]
    rfl
  rw [e]
  exact col_treeTable J.P _ hP τ x T hT

/-- Its depth. -/
theorem treeTbl_depth (ch : ℕ) (wit : Wl → W') (J : SendJob W' X) (own₀ : X) (τ : ℕ) (k : Coins Bk)
    (w : Wl) (h : List Fmt.Drawn) {c : Cs (K1.dueR J.P J.ride)}
    (hc : lentCut k ch ⟨J.P.place, 0⟩ (K1.dueR J.P J.ride) = some c)
    (hτ : τ < J.P.trees.length) :
    (treeTbl ch wit J own₀ τ k w h).2.logLength = (J.P.trees.getD τ {}).logN := by
  unfold treeTbl
  rw [hc]
  show (((K1.treeTables J.P (rowsLaid J own₀ c (wit w) h))[τ]?).getD wordlessTable).logLength = _
  unfold K1.treeTables
  rw [List.getElem?_map, List.getElem?_zipIdx, List.getElem?_eq_getElem hτ]
  show (J.P.trees[τ]).logN = _
  rw [List.getD_eq_getElem _ _ hτ]

set_option maxRecDepth 1000000 in
/-- **The kernel, on the written plans.** -/
theorem cols_written :
    (List.range parGF.sent.size).filter (fun k =>
        ((VerifiableInference.Desc.Own.treesMade parGF.codes parGF.sent).getD {}).tree[k]? == some 1) =
      [parGF.sent.size - 1] ∧
    (shapeAt parGF (parGF.sent.size - 1)).mainRows = 0 ∧
    (List.range parWF.sent.size).filter (fun k =>
        ((VerifiableInference.Desc.Own.treesMade parWF.codes parWF.sent).getD {}).tree[k]? == some 0) = [0, 1] ∧
    (shapeAt parWF 1).mainRows = 0 ∧ 1 < parGF.trees.length ∧ 0 < parWF.trees.length ∧
    (parGF.trees.getD 1 {}).logN = 13 ∧ (parWF.trees.getD 0 {}).logN = 22 := by
  decide +kernel

/-- Tree 1 of the first sending: the last message's mask rows. -/
theorem col_first (V : ℕ → Rows) (x : ℕ) :
    col parGF V 1 x = maskSyms parGF V (parGF.sent.size - 1) x := by
  obtain ⟨e1, e2, -⟩ := cols_written
  unfold col
  simp only [e1, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  have : mainSyms parGF V (parGF.sent.size - 1) x = [] := by
    unfold mainSyms
    simp only [e2, List.range_zero, List.flatMap_nil]
  rw [this, List.nil_append]

/-- Tree 0 of W's sending: W's rows, then the mask rows of both messages. -/
theorem col_W (V : ℕ → Rows) (x : ℕ) :
    col parWF V 0 x = mainSyms parWF V 0 x ++ (maskSyms parWF V 0 x ++ maskSyms parWF V 1 x) := by
  obtain ⟨-, -, e1, e2, -⟩ := cols_written
  unfold col
  simp only [e1, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  have : mainSyms parWF V 1 x = [] := by
    unfold mainSyms
    simp only [e2, List.range_zero, List.flatMap_nil]
  rw [this, List.append_nil]

/-- **A K1 member's rows, at a stretch that holds the sender's coins.** -/
theorem member_rows {Wd W : Type} (J : SendJob Wd X) (lift : W → Wd) (at_ : Addr) (n : ℕ)
    (fs : Option ℕ × Option ℕ) (w : W) (fr : Front X) (S : Stretch)
    (c : Cs (K1.dueR J.P J.ride)) (hn : n < J.P.sent.size)
    (hf : ∀ i, i < (K1.dueMsg J.P.codes (shapeAt J.P n) (J.ride n)).f →
      K1.cf c ((K1.startR J.P J.ride n).f + i) = S.f i)
    (he : ∀ i, i < (K1.dueMsg J.P.codes (shapeAt J.P n) (J.ride n)).e →
      K1.ce c ((K1.startR J.P J.ride n).e + i) = S.e i) :
    (memK1 J lift at_ n fs).rows w fr S =
      psOfRows J.P n (K1.rowsR J.P J.ride (J.data (lift w) fr) c n) := by
  show psOfRows J.P n (K1.rowsR J.P J.ride (J.data (lift w) fr) (csAt _ (K1.startR J.P J.ride n) S) n) = _
  rw [rowsR_csAt J.P J.ride _ n hn S c hf he]

/-- A filling's total call reads the challenges heard up to its own count alone. -/
theorem at_take (D : RowData) (R : Readers) (heard : List Fmt.Drawn) (a : MsgAddr) (r j n : ℕ)
    (hn : D.heardAt a ≤ n) : D.at_ R (heard.take n) a r j = D.at_ R heard a r j := by
  unfold RowData.at_
  rw [List.take_take, Nat.min_eq_left hn]

/-- **(K-c) at W's sending**: W's data at the front is W's data at the challenges that fix the table. -/
theorem w_data_behind {Xi : Type} (q : OnBytes.Params.First) (gp : _root_.Desc.Plain.GPar)
    (msg : Array OnBytes.OracleNotice) (n₁ n₂ : ℕ) (D : RowDataOf Xi) (w : K1.PlaceIn Xi)
    (fr fr' : Front X) (n : ℕ)
    (hh : fr'.heard = fr.heard.take n)
    (hn : ∀ k, (D w.x).heardAt ⟨⟨(VerifiableInference.Desc.K1.parW q gp 4 msg).place, 0⟩, k⟩ ≤ n) (k r j : ℕ) :
    (K1.wJobAt (X := X) q gp 4 msg n₁ D).data w fr k r j =
      (K1.wJobAt (X := X) q gp 4 msg n₂ D).data w fr' k r j := by
  show (D w.x).forSend w.R _ fr.heard k r j = (D w.x).forSend w.R _ fr'.heard k r j
  unfold RowData.forSend
  rw [hh, at_take _ _ _ _ _ _ _ (hn k)]

/-- **(K-c) at the first sending**: the opening's data at the front is the lot's at any challenges. -/
theorem first_data_behind (S : OnBytes.HonestTrace.Sz) (Z : ProofFile.Pub) (G : ProofFile.Ground)
    (x : ProofFile.Inst) (R : Readers) (n₀ : ℕ) (fr : Front X) (fr' : Front X) (k r j : ℕ) :
    (K1.firstJob (X := X) S Z G).data R fr k r j =
      (K1.placeJob (X := X) (VerifiableInference.Desc.K1.firstPar G.first
        (VerifiableInference.Desc.K1.gpOf Z)) n₀ (K1.firstFold G.first) (K1.lotData S Z G)).data
          ⟨x, R⟩ fr' k r j := by
  show (K1.firstFill S G.first).forSend R K1.firstAddr fr.heard k r j =
    (K1.lotData S Z G x).forSend R K1.firstAddr fr'.heard k r j
  rw [K1.data_first]
  unfold RowData.forSend
  rw [← at_take (K1.firstFill S G.first) R fr.heard _ r j 0 (Nat.le_refl _),
    ← at_take (K1.firstFill S G.first) R fr'.heard _ r j 0 (Nat.le_refl _)]
  simp only [List.take_zero]

end AtFullSide.K12

#print axioms AtFullSide.K12.treeTbl_col
#print axioms AtFullSide.K12.treeTbl_depth
#print axioms AtFullSide.K12.cols_written
#print axioms AtFullSide.K12.col_first
#print axioms AtFullSide.K12.col_W
#print axioms AtFullSide.K12.member_rows
#print axioms AtFullSide.K12.at_take
#print axioms AtFullSide.K12.w_data_behind
#print axioms AtFullSide.K12.first_data_behind
