-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K12/LettersReadyW.lean: under the library's head: the data of W's sending are ready at a
list of challenges: the test RowData.readyAt of K13.wDataAt at the filler K13.pileAnyK3, which
openHonest lays, at a base's ground. So where this test accepts, the value that the sender's job
reads through RowData.at_ is W's entry at the pile's true rows.

  fits_of_rows      the batching's test on the rows, from each row's fields
  w_ready_of_rows   the test accepts where enough has been heard, the batching's own challenges
                    have one element each, and the filler yields a row
  w_rows_at_fold    the filler yields a row where the verifier's fold over the 355 sub-protocols in
                    front returns without a mark, at the reply asked
  w_ready_at_fold   the two joined

By what. pileOfAnySize_at (K13/PileOfAnySizeAt.lean) and hfill_at_head (K13/FillFitsAtHead.lean):
where the filler yields a row, it yields the plan's number of rows, each of the plan's form.
k13_pileIs_at_head (K13/PileIsAtHead.lean): the filler's rows are the fold's pile's.
reach_of_fold, pile_length_reach (K13/PileLengthReach.lean): that pile has thirteen rows.
k13_wPublic_at_head, k13_wRow_at_head (AtFullSide/K13/WFillAtHead.lean): the public tests.

Limits.
- Three premises stay, all on a run: hn, that enough has been heard; hone, that the last 2 + kCol
  challenges have one element each; and that the fold returns, without a mark, at the reply asked.
- At a base's ground: ground_at_head holds A.G to it.
- The full size and the format's second hash function alone.
- Nothing on what a part plays. Nothing on completeness, soundness or hiding.
-/
import AtFullSide.K13.WFillAtHead
import Johnson.Desc.ProofFile.Honest.K13.PileOfAnySizeAt
import Johnson.Desc.ProofFile.Honest.K13.FillFitsAtHead
import Johnson.Desc.ProofFile.Honest.K13.GuardsAtM3
import Johnson.Desc.ProofFile.Honest.K13.PileIsAtHead
import Johnson.Desc.ProofFile.Honest.K13.PileLengthReach
import Johnson.Desc.ProofFile.Honest.K13.PileOneAt356

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K12
open OnBytes OnBytes.Params
open ProofFile.Honest ProofFile.Honest.K13
open VerifiableInference.Desc (Chain foldBlocks)
open VerifiableInference.Desc.K13.Honest (rowReads)
open P5J (AtMgA TS)

/-- **The batching's test on the rows, from each row's fields.** -/
theorem fits_of_rows {k kR : Nat} {rows : List TensorRow} (hne : rows ≠ []) (hk : 1 ≤ k)
    (hall : ∀ q ∈ rows, q.psi.length = k ∧ q.g ≠ [] ∧ ∀ t ∈ q.g, t.vars = kR) :
    Batt.fits k rows = true := by
  cases rows with
  | nil => exact absurd rfl hne
  | cons r tl =>
    obtain ⟨-, hg, hv⟩ := hall r (List.mem_cons_self ..)
    cases hr : r.g with
    | nil => exact absurd hr hg
    | cons t₀ ts =>
      have h₀ : t₀.vars = kR := hv t₀ (by rw [hr]; exact List.mem_cons_self ..)
      show (decide (1 ≤ k) && (r :: tl).all fun s =>
        s.psi.length == k && !s.g.isEmpty &&
          s.g.all fun t => some t.vars == r.g.head?.map Tensor.vars) = true
      rw [hr, Bool.and_eq_true]
      refine ⟨decide_eq_true hk, List.all_eq_true.2 fun s hs => ?_⟩
      obtain ⟨h1, h2, h3⟩ := hall s hs
      show (s.psi.length == k && !s.g.isEmpty &&
        s.g.all fun t => some t.vars == (t₀ :: ts).head?.map Tensor.vars) = true
      rw [Bool.and_eq_true, Bool.and_eq_true]
      refine ⟨⟨beq_iff_eq.2 h1, ?_⟩, List.all_eq_true.2 fun t ht => ?_⟩
      · cases hs' : s.g with
        | nil => exact absurd hs' h2
        | cons _ _ => rfl
      · simp [h3 t ht, h₀]

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **W's data are ready**, where enough has been heard, the batching's own challenges have one
element each, and the filler yields a row. -/
theorem w_ready_of_rows (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) (Bs : ProofFile.PureBase)
    (x : ProofFile.Inst) (heard : List Fmt.Drawn) (hn : wHeard Zp ≤ heard.length)
    (hone : ((heard.take (wHeard Zp)).drop (wHeard Zp - (2 + Zp.first.lin.kCol))).all
      (fun d => d.elems.length == 1) = true)
    (hrow : pileAnyK3 Zp Bs.G₀ x
      (wFront Zp.first.lin (wHeard Zp) (heard.take (wHeard Zp))) ≠ []) :
    (wDataAt pileAnyK3 Zp Bs.G₀ x).readyAt heard wAddr = true := by
  obtain ⟨cl, e⟩ : ∃ cl, pileAnyK3 Zp Bs.G₀ = fillerAt cF Zp cl :=
    ⟨_, pileOfAnySize_at h q0Idle Bs⟩
  have hl : (heard.take (wHeard Zp)).length = wHeard Zp := by
    rw [List.length_take]
    omega
  have hf := hfill_at_head h cl x (wFront Zp.first.lin (wHeard Zp) (heard.take (wHeard Zp)))
    (by rw [← e]; exact hrow)
  rw [← e] at hf
  unfold pileFits at hf
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hf
  obtain ⟨⟨⟨l1, -⟩, -⟩, l4⟩ := hf
  have hk : h.𝔇.P13.lin.kCol = Zp.first.lin.kCol :=
    (m3_kCol h).trans (AtFullSide.K13.k13_wRow_at_head h).2.2.2.symm
  have hR : h.𝔇.P13.lin.kRow = Zp.first.lin.kRow := rfl
  have hk1 : 1 ≤ Zp.first.lin.kCol := by
    rw [(AtFullSide.K13.k13_wRow_at_head h).2.2.2]
    decide
  have hu : (pileAnyK3 Zp Bs.G₀ x
      (wFront Zp.first.lin (wHeard Zp) (heard.take (wHeard Zp)))).length =
      Zp.first.pendingRows := by
    have a := beq_iff_eq.1 l1
    rw [List.length_map] at a
    exact a.trans ((m3_rows h).trans (m3_written h).2.2.2.1.symm)
  have hall : ∀ q ∈ pileAnyK3 Zp Bs.G₀ x
      (wFront Zp.first.lin (wHeard Zp) (heard.take (wHeard Zp))),
      q.psi.length = Zp.first.lin.kCol ∧ q.g ≠ [] ∧ ∀ t ∈ q.g, t.vars = Zp.first.lin.kRow := by
    intro q hq
    have a := List.all_eq_true.1 l4 (rowReads q) (List.mem_map.2 ⟨q, hq, rfl⟩)
    have a' : (q.psi.length == h.𝔇.P13.lin.kCol && !q.g.isEmpty &&
        q.g.all (·.vars == h.𝔇.P13.lin.kRow)) = true := a
    rw [Bool.and_eq_true, Bool.and_eq_true] at a'
    obtain ⟨⟨b1, b2⟩, b3⟩ := a'
    refine ⟨(beq_iff_eq.1 b1).trans hk, fun e0 => ?_, fun t ht => ?_⟩
    · rw [e0] at b2
      simp at b2
    · exact (beq_iff_eq.1 (List.all_eq_true.1 b3 t ht)).trans hR
  show (decide (wHeard Zp ≤ heard.length) &&
    (wPublic Zp.first.codes Zp.first.lin (wHeard Zp) Zp.first.pendingRows &&
      (heard.take (wHeard Zp)).length == wHeard Zp &&
      (((heard.take (wHeard Zp)).drop (wHeard Zp - (2 + Zp.first.lin.kCol))).all
        fun d => d.elems.length == 1) &&
      (pileAnyK3 Zp Bs.G₀ x
        (wFront Zp.first.lin (wHeard Zp) (heard.take (wHeard Zp)))).length ==
        Zp.first.pendingRows &&
      Batt.fits Zp.first.lin.kCol (pileAnyK3 Zp Bs.G₀ x
        (wFront Zp.first.lin (wHeard Zp) (heard.take (wHeard Zp)))) &&
      (pileAnyK3 Zp Bs.G₀ x (wFront Zp.first.lin (wHeard Zp) (heard.take (wHeard Zp)))).all
        fun q => q.g.all fun t => t.vars == Zp.first.lin.kRow)) = true
  simp only [Bool.and_eq_true]
  exact ⟨decide_eq_true hn, ⟨⟨⟨⟨AtFullSide.K13.k13_wPublic_at_head h, beq_iff_eq.2 hl⟩, hone⟩,
    beq_iff_eq.2 hu⟩, fits_of_rows hrow hk1 hall⟩,
    List.all_eq_true.2 fun q hq => List.all_eq_true.2 fun t ht =>
      beq_iff_eq.2 ((hall q hq).2.2 t ht)⟩

/-- **The filler yields a row where the verifier's fold in front returns without a mark, at the
reply asked.** -/
theorem w_rows_at_fold (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) (Bs : ProofFile.PureBase)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) (x : ProofFile.Inst)
    {rs : List Fmt.RoundView} {cols : List VerifiableInference.Desc.OpenedColumn}
    {s : VerifiableInference.Desc.First.S} {r' : List Fmt.RoundView}
    {c' : List VerifiableInference.Desc.OpenedColumn}
    (hf : foldBlocks 0 (cF.blocksInOrder.take 355) (ProofFile.startS Zp x.pub) rs cols = .ok (s, r', c'))
    (hs : s.failed = none) (hq : s.out.reply = some x.asked) (tl : List Fmt.Drawn) :
    pileAnyK3 Zp Bs.G₀ x
      ((rs.take (VerifiableInference.Desc.K13.Honest.roundsAhead cF.blocksInOrder 355)).map (·.drawn) ++
        tl) ≠ [] := by
  obtain ⟨Bs', base, O⟩ := h.laid.opened
  have hr : Johnson.Desc.First.Walk.Tied.Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 355 (x.pub, s) :=
    Johnson.Desc.First.Walk.Tied.reach_of_fold (start := ProofFile.startS Zp) (z := x.pub) 355
      (Nat.le_of_succ_le (k13_len356 h)) s rs r' cols c' hf
  have hc := (pile_length_reach h.scope h.reads O h.laid.planOk hr (Nat.le_refl 355)).2.trans
    takenAt_355
  have e := pileOfAnySize_at h q0Idle Bs
  have m := k13_pileIs_at_head h Bs hB (fun g => q0Idle Zp (2 * g)) x rs cols s r' c' hf hs hq tl
  intro e0
  have e1 : pileOfAnySize headArmOfSeg q0Idle Zp Bs.G₀ x
      ((rs.take (VerifiableInference.Desc.K13.Honest.roundsAhead cF.blocksInOrder 355)).map (·.drawn) ++
        tl) = [] := e0
  rw [e] at e1
  rw [e1] at m
  have hn : s.out.pending = [] := by simpa using m.symm
  rw [hn] at hc
  simp at hc

/-- **W's data are ready at the list that a returned fold hands.** hfr: the front of that list
holds the rounds in front of the batching's sub-protocol. -/
theorem w_ready_at_fold (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) (Bs : ProofFile.PureBase)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) (x : ProofFile.Inst)
    (heard : List Fmt.Drawn) (hn : wHeard Zp ≤ heard.length)
    (hone : ((heard.take (wHeard Zp)).drop (wHeard Zp - (2 + Zp.first.lin.kCol))).all
      (fun d => d.elems.length == 1) = true)
    {rs : List Fmt.RoundView} {cols : List VerifiableInference.Desc.OpenedColumn}
    {s : VerifiableInference.Desc.First.S} {r' : List Fmt.RoundView}
    {c' : List VerifiableInference.Desc.OpenedColumn}
    (hf : foldBlocks 0 (cF.blocksInOrder.take 355) (ProofFile.startS Zp x.pub) rs cols = .ok (s, r', c'))
    (hs : s.failed = none) (hq : s.out.reply = some x.asked) (tl : List Fmt.Drawn)
    (hfr : wFront Zp.first.lin (wHeard Zp) (heard.take (wHeard Zp)) =
      (rs.take (VerifiableInference.Desc.K13.Honest.roundsAhead cF.blocksInOrder 355)).map (·.drawn) ++ tl) :
    (wDataAt pileAnyK3 Zp Bs.G₀ x).readyAt heard wAddr = true :=
  w_ready_of_rows h Bs x heard hn hone (by
    rw [hfr]
    exact w_rows_at_fold h Bs hB x hf hs hq tl)

end AtFullSide.K12

#print axioms AtFullSide.K12.fits_of_rows
#print axioms AtFullSide.K12.w_ready_of_rows
#print axioms AtFullSide.K12.w_rows_at_fold
#print axioms AtFullSide.K12.w_ready_at_fold
