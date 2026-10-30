-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/LiveTablesOfMark.lean: THE SMALLNESS TEST AT AN ATTENTION SEGMENT: WHERE THE MARK AT
THE SEGMENT's OWN ROUNDS (`mkReads`, Johnson/Desc/ProofFile/Honest/K5/Law/MarkReads.lean) IS SILENT,
THE STATE IN FRONT OF THE BATCHING HOLDS, ON TWO OF THE SEGMENT's MATRICES, A TABLE THAT IS LIVE IN
THE SENSE OF `LiveTable` (Johnson/Desc/K8/Honest/ReadsLiveOf.lean). Lemmas; NONE OF THE LIBRARY's
GOALS. Nothing on completeness, soundness or hiding.

  `liveTable_of_V`   a table that is live at values over a list of matrices (`LiveV`,
      Johnson/Desc/K5/Honest/Law/LiveValAt.lean) is a `LiveTable` of data that hold that list
  **`mats_at_att`**   in the goals' scope, at g < 12, at every (z, s) reached at 14 (2 g + 1) + 9: s
      holds data whose list of matrices is the plan's
  **`liveTables_of_mark`**   under the head of `mkReads_liveV`
      (Johnson/Desc/ProofFile/Honest/K5/Law/MarkReadsVal.lean) and its premises (the plan; five
      members' yes, chained; the challenges; the mark silent), and where the last state is reached:
      a `LiveTable` at the matrix NAs and one at NAs + 3
By: mkReads_liveV · `planned_at_batch` (Johnson/Desc/First/Link/Law/PlannedAtDraw.lean) ·
IM.ground_named, IM.ground_tails (Johnson/IMR/PureJoin.lean, K8Seat.lean) · `planned_sizes`
(Johnson/P1K8R/TiesAtBatch.lean) · ProofFile.Law.blankBy_W.
Limits. Two of the segment's NAs + 4 matrices. That the five yes, the mark's silence and "reached"
hold together at any run is not shown. Nothing on any measure.
-/
import Johnson.P1K8R.TiesAtBatch
import Johnson.Desc.K8.Honest.ReadsLiveOf
import Johnson.Desc.ProofFile.Honest.K5.Law.MarkReadsVal

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 OnBytes.Maker
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8 VerifiableInference.Desc.First.K8.Ready
open VerifiableInference.Desc.First.K8.Honest
open Johnson.Desc.First.Walk.Tied (Reach)
open H2K5.Honest (readRounds Reads LiveV Live2V)
open ProofFile.Honest.K5 (mkReads mkReads_liveV)
open P5J (AtMgA TS)

/-- A table that is live at values is a `LiveTable` of data that hold the list of matrices. -/
theorem liveTable_of_V {tl : HTailF2} {mats : Array TMat} (hm : tl.mats = mats) {mu n : ℕ}
    {Fn : HFun} (hF : Fn ∈ tl.funs.toList) (h : LiveV mats mu n Fn) : LiveTable tl mu Fn := by
  obtain ⟨h1, -, h3, h4, h5, h6⟩ := h
  exact ⟨hF, h1, Or.inr h3, h4, by rw [hm]; exact h5, h6⟩

/-- **At a state reached in front of an attention segment's batching the matrices are the
plan's.** -/
theorem mats_at_att {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)}
    {c : Chain S Claim} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12)
    {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * (2 * g + 1) + 9) (z, s)) :
    ∃ q tl, Bs.G₀.W.A[g]? = some q ∧ s.tl? = some tl ∧ tl.mats = q.seam.tl.mats := by
  obtain ⟨hN, -⟩ := IM.ground_named hS hR O.pub O.blank
  obtain ⟨-, X, -, -, -, -, e3, -⟩ := hN g hg
  obtain ⟨hT, -⟩ := IM.ground_tails hS hR O.pub O.blank
  obtain ⟨-, q, -, X', -, eq, -, -, -, -, -, -, e3', htl, -⟩ := hT g hg
  obtain rfl : X = X' := Option.some.inj (e3.symm.trans e3')
  have hv := LinkJoin.planned_at_batch planned_sizes hS hR O (x := (2 * g + 1, 4, 2))
    (List.mem_map.2 ⟨2 * g + 1, List.mem_range.2 (by omega), by
      rw [if_neg (by omega : ¬ 2 * g + 1 = 24), if_neg (by omega : ¬ 2 * g + 1 = 24)]⟩)
    e3 (z, s) h
  rw [htl] at hv
  unfold readTl at hv
  cases hts : s.tl? with
  | none =>
    rw [hts] at hv
    exact absurd hv (by simp)
  | some tl =>
    rw [hts] at hv
    have e := Option.some.inj hv
    simp only [sizesView, Prod.mk.injEq] at e
    exact ⟨q, tl, eq, rfl, e.2.2.1⟩

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : Look.Place} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
include h

/-- **From the mark's silence to two live tables at the state in front of the batching.** -/
theorem liveTables_of_mark {g : ℕ} (hg : g < 12) {a : Attention.Plan}
    (ea : (P5J.At.X Zp).A[g]? = some a) {b4 b5 b6 b7 b8 : Block S ProofFile.Cl}
    (f4 : cF.blocksInOrder[14 * (2 * g + 1) + 4]? = some b4)
    (f5 : cF.blocksInOrder[14 * (2 * g + 1) + 5]? = some b5)
    (f6 : cF.blocksInOrder[14 * (2 * g + 1) + 6]? = some b6)
    (f7 : cF.blocksInOrder[14 * (2 * g + 1) + 7]? = some b7)
    (f8 : cF.blocksInOrder[14 * (2 * g + 1) + 8]? = some b8) {s4 s5 s6 s7 s8 s9 : S}
    {rs4 rs5 rs6 rs7 rs8 : List Fmt.RoundView} {gs4 gs5 gs6 gs7 gs8 : List (List (ℕ × List UInt64))}
    (d4 : b4.decide s4 rs4 gs4 = .ok s5) (d5 : b5.decide s5 rs5 gs5 = .ok s6)
    (d6 : b6.decide s6 rs6 gs6 = .ok s7) (d7 : b7.decide s7 rs7 gs7 = .ok s8)
    (d8 : b8.decide s8 rs8 gs8 = .ok s9) (zk : Array (Array E)) {fr own : List Fmt.Drawn}
    (hc : Reads ⟨zk, own⟩ rs4)
    (hlen : ∀ n ∈ readRounds a.own (Att.P.parCOf a).geo, n < own.length)
    (hs : (mkReads (2 * g + 1) a.own (Att.P.parCOf a).geo).test fr own = none)
    {z : ProofFile.InstPub}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * (2 * g + 1) + 9) (z, s9)) :
    ∃ tl, s9.tl? = some tl ∧ (∃ Fn, LiveTable tl (Att.P.parCOf a).geo.NAs Fn) ∧
      ∃ Fn, LiveTable tl ((Att.P.parCOf a).geo.NAs + 3) Fn := by
  obtain ⟨tl, hts, ⟨F1, m1, l1⟩, F2, m2, l2⟩ :=
    mkReads_liveV h hg ea f4 f5 f6 f7 f8 d4 d5 d6 d7 d8 zk hc hlen hs
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨q, tl', eq, hts', hm⟩ := mats_at_att h.scope h.reads O hg hr
  obtain rfl : tl = tl' := Option.some.inj (hts.symm.trans hts')
  have eW : Bs.G₀.W = Zp.p.X := ProofFile.Law.blankBy_W O.blank
  rw [eW] at eq
  obtain rfl : a = q := Option.some.inj (ea.symm.trans eq)
  exact ⟨tl, hts, ⟨F1, liveTable_of_V hm m1 l1⟩, F2, liveTable_of_V hm m2 l2⟩

end

end P1K8

#print axioms P1K8.liveTable_of_V
#print axioms P1K8.mats_at_att
#print axioms P1K8.liveTables_of_mark
