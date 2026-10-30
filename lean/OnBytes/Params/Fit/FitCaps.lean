-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/Fit/FitCaps.lean: the caps LinCap and ReqCap of FitPlans.lean (in this folder) hold
at the sizes that the planner derives, where the parameter file's lines are within their ranges.

FitPlans.lean shows that every entry of the plans of a key file's and of a proof file's chains is
Small, under caps on the sizes from which the plans are made. This file pays the caps on the test on
the table (LinCap, for a proof and for a key) and on a proof's chains (ReqCap), from what sized
returns, the ranges of the lines (LinesCap, LinesCap.lean) and one premise on the classes of leaves
of the links' oracle messages (TreeClassCap, TreesSized.lean). It gathers what the other files of
this folder show: the table (TableCap.lean), the codes (CodesCap.lean, CodesSized.lean), the rows
(LinRows.lean), the stages (StageCaps.lean, SizedParts.lean), the trees (TreesSites.lean,
TreesSized.lean), the frame (FitCubes.lean), and the tests that sized runs itself (sized_tests).

Main names:
  codesShort_of_cap: CodesCap gives CodesShort.
  le_of_ceilLog2: n is at most 2 to its rounded-up logarithm.
  linLines_caps, linNums_of_lines: the lines of the test on the table are within their ranges.
  linCap_of: LinCap of what linSized returns, if its shape passes its own test (LinShape.ok), its
    table is in order (TableOk) and the lines' numbers are within their ranges (LinNums, GroupCap);
    at any list of codes with short messages.
  reqCap_of_sized: ReqCap of the proof's sizes that sized returns.
Limits. LinesCap and TreeClassCap are premises here. Nothing where sized refuses; that sized returns
at any lines is not said here. linSized does not run LinShape.ok: sized runs it afterwards, inside
linOk. KeyCap is not treated here but for its field lin, which linCap_of serves. The program does
not import this file.


-/
import OnBytes.Params.Fit.FitCubes
import OnBytes.Params.Fit.SetCapOf
import OnBytes.Params.Fit.TableCap
import OnBytes.Params.Fit.LinShapeCaps
import OnBytes.Params.Fit.CodesSized
import OnBytes.Params.Fit.SizedParts
import OnBytes.Params.Fit.TreesSized

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Params

open OnBytes

/-! ## Small laws -/

/-- Beyond a list's end stands the default code, whose message is empty. -/
theorem getD_logEll {A : Array Code} (h : ∀ c ∈ A.toList, c.logEll ≤ 64) (i : Nat) :
    (A.getD i default).logEll ≤ 64 := by
  by_cases hi : i < A.size
  · exact h _ (getD_mem default hi)
  · have e : A.getD i default = default := by simp [Array.getD, hi]
    rw [e]
    decide

theorem codesShort_of_cap {codes : Codes} (h : CodesCap codes) : CodesShort codes :=
  fun i => ⟨getD_logEll h.1 i, getD_logEll h.2 i⟩

theorem le_of_ceilLog2 {n a : Nat} (h : ceilLog2 n ≤ a) : n ≤ 2 ^ a :=
  (le_pow_clog2 n).trans (Nat.pow_le_pow_right (by omega) h)

/-! ## The lines of the test on the table -/

/-- The three groups' lines are within their ranges. -/
theorem linLines_caps {l : Lines} (H : LinesCap l) (m rows : Nat) (one : Bool) :
    GroupCap (linLines l m rows one).folded ∧ GroupCap (linLines l m rows one).omega ∧
      GroupCap (linLines l m rows one).own := by
  cases one
  · exact ⟨H.folded, H.omega, H.own⟩
  · exact ⟨H.onceFolded, H.onceOmega, H.onceOwn⟩

/-- The numbers from which the rows of the test's oracle messages are formed. -/
theorem linNums_of_lines {l : Lines} {T : TableSize} (H : LinesCap l)
    (hT : deriveTable (settingOf l) l = some T) {m rows : Nat} (hr : rows ≤ 4096)
    (hM : m ≤ 2 ^ 64) (one : Bool) : LinNums (settingOf l) (linLines l m rows one) T := by
  obtain ⟨e1, _, _⟩ := deriveTable_fields hT
  obtain ⟨cF, cO, _⟩ := linLines_caps H m rows one
  have hp : 2 ^ l.tableLogN ≤ 2 ^ 32 := Nat.pow_le_pow_right (by omega) H.tLogN
  have hf := H.tFit
  have hb := H.block
  refine ⟨(setCap_of_lines H).samples, ?_, hM, ?_, ?_, hr, ?_, ?_⟩
  · show l.blockLog - l.tableRowsLog ≤ 40
    omega
  · rw [e1]
    show l.tableData ≤ 2 ^ 32
    omega
  · rw [e1]
    show l.tableRandom ≤ 2 ^ 32
    omega
  · have a := cF.logL
    have b := cF.logN
    omega
  · have a := cO.logL
    have b := cO.logN
    omega

/-! ## The test on the table -/

/-- The shape holds the lines' number of rows of the matrix. -/
theorem linSized_matrixRows {s : Setting} {L : LinLines} {T : TableSize} {codes c : Codes}
    {x : LinSized} (h : linSized s L T codes = some (x, c)) :
    x.shape.matrixRows = L.matrixRows := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, e, _⟩ :=
    linSized_parts h
  exact e

/-- LinCap of what linSized returns, if its shape passes its own test (LinShape.ok), its table is in
order (TableOk) and the lines' numbers are within their ranges (LinNums, GroupCap). codes: the whole
list of the file's chains, which may be longer than the list that linSized returns; its messages are
short (CodesShort). -/
theorem linCap_of {s : Setting} {L : LinLines} {T : TableSize} {codes0 c : Codes} {x : LinSized}
    (codes : Codes) (h : linSized s L T codes0 = some (x, c)) (N : LinNums s L T)
    (CF : GroupCap L.folded) (CO : GroupCap L.omega) (CW : GroupCap L.own)
    (hT : TableOk x.table) (hok : x.shape.ok = true) (hc : CodesShort codes) :
    LinCap codes x := by
  obtain ⟨rU, rO, rW, rS, _⟩ := lin_rows h N
  obtain ⟨sW, sF, sO⟩ := lin_stages h N CF CO CW
  obtain ⟨k1, k2, _⟩ := linShape_caps hok
  exact
    { table := hT
      w := cubeBits_le hc rW.1 rW.2
      u := cubeBits_le hc rU.1 rU.2
      omega := cubeBits_le hc rO.1 rO.2
      split := cubeBits_le hc rS.1 rS.2
      kLo := k1.trans (by omega)
      kRow := k2.trans (by omega)
      treesW := fun _ _ ha hk => trees_linW codes hok ha hk
      treesU := fun _ _ ha hk => trees_linU codes x.shape ha hk
      treesOmega := fun _ hk => trees_linOmega codes hok hk
      own := sW
      folded := sF
      omegaT := sO }

/-! ## A proof's chains -/

/-- **ReqCap of the proof's sizes that sized returns.** -/
theorem reqCap_of_sized {l : Lines} {x : Shapes} {z : Sized} (h : sized l x = .ok z)
    (H : LinesCap l) (hc : TreeClassCap x.sub.links) : ReqCap z.proof := by
  obtain ⟨_, t2, _⟩ := sized_tests h
  obtain ⟨cL, cG, cR, ok1, _⟩ := sized_caps h hc
  have hp := sized_proof h
  obtain ⟨_, _, _, T, codes1, _, _, _, _, _, _, hT, hl⟩ := proofSized_parts hp
  have hs := codesShort_of_cap (proofSized_codes hp H)
  obtain ⟨g1, g2⟩ := proof_stages hp H.link (reqOk_shape t2)
  obtain ⟨cF, cO, cW⟩ := linLines_caps H x.sub.matrixRows
    (Send.maskRowsFor
      (x.sub.pendingRows + (if 1 < x.sub.pendingRows then Batt.masksOf l.blockLog else 0))
      (2 ^ l.own.maskLogL) l.answers) false
  have hM : x.sub.matrixRows ≤ 2 ^ 64 := by
    have e : z.proof.batch.shape.matrixRows = x.sub.matrixRows := linSized_matrixRows hl
    have k := (linShape_caps ok1).2.1
    have q : z.proof.batch.shape.matrixRows ≤ 2 ^ 30 := le_of_ceilLog2 k
    rw [e] at q
    exact q.trans (by omega)
  have tb : TableOk z.proof.batch.table := by
    rw [linSized_table hl]
    exact tableOk_of_lines H hT
  exact
    { lin := linCap_of z.proof.codes hl
        (linNums_of_lines H hT (maskRowsFor_le _ _ _) hM false) cF cO cW tb ok1 hs
      link := g1
      last := g2
      frame := frameCap_of (reqOk_shape t2) hs cG cL cR }

end OnBytes.Params
