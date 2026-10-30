-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the public premises of onAtRun_paid at the first chain's last test.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/PublicAtRun.lean: under the head, public numbers alone. No run, no coin.

  placeL_only, finishWritten_at_K2   by Lean's kernel: at the written cut the test's place stands at number 354 alone; the written finish is at ⟨1, none, 1, .K2⟩
  front_public   hfront's public half: the block at the test has 354 in front, the last of them stands at the finish's place, and 76 trees stand in front of that one
  early_public, form_public, first_public   hE; hst with FP; hos₁

hfront's other three clauses, on the prover's list and on the book, are not here. That the finish is the written one is finish_at_head (TreesLAt.lean). No property of the
protocol is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim2.TreesLAt
import Johnson.Desc.ProofFile.Honest.K12.Sim2.PublicL
import Johnson.Desc.ProofFile.Honest.K12.AtProof.CutAtL
import AtFullSide.K12.FirstAnyAtHeadL
import Johnson.Road.K4.K4HeadWritten
import Johnson.Desc.First.CutAtNumbers

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Sim2
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.PlanWritten (cutFirstFull)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.AtProof
open H2K.Member (piLFull)

set_option maxRecDepth 1000000 in
/-- The test's place stands at number 354 of the written cut, and nowhere else. -/
theorem placeL_only : ((List.range (cutFirstFull.map (·.2.1)).length).all fun i =>
    ((cutFirstFull.map (·.2.1))[i]? != some placeL) || i == 354) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem finishWritten_at_K2 : finishWritten.map (·.place) = some ⟨1, none, 1, .K2⟩ := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}

/-- **hfront's public half**, at the written finish. -/
theorem front_public {Bs : ProofFile.PureBase}
    {base : List (Block S ProofFile.Cl)} (h : P5J.AtMg OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (_root_.Desc.K14.Law.seatZ Zp Np) (_root_.Desc.K14.Law.secondAt Zp Np))
    {pl : K2.SwitchPlace} (hf : finishWritten = some pl) {blk : Block S ProofFile.Cl}
    {pre' t' : List (Block S ProofFile.Cl)} (hc : cF.blocksInOrder = pre' ++ blk :: t') (hb : blk.place = placeL) :
    pre'.length = 354 ∧ ∃ (pre : List (Block S ProofFile.Cl)) (b : Block S ProofFile.Cl),
      pre' = pre ++ [b] ∧ b.place = pl.place ∧ treesTo cF.blocksInOrder pre.length = 76 := by
  have e : cF.blocksInOrder.map (·.place) = cutFirstFull.map (·.2.1) :=
    (VerifiableInference.Desc.First.told_at_cut (OnBytes.Road.K4.cut_of_head h)).1
  have e1 : (cutFirstFull.map (·.2.1))[pre'.length]? = some placeL := by
    rw [← e, hc]
    simp [hb]
  obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.1 e1
  have h354 : pre'.length = 354 := by
    have h1 := List.all_eq_true.1 placeL_only _ (List.mem_range.2 hlt)
    rw [e1] at h1
    simpa using h1
  have hne : pre' ≠ [] := fun hn => by
    rw [hn] at h354
    cases h354
  obtain ⟨pre, b, rfl⟩ : ∃ pre b, pre' = pre ++ [b] :=
    ⟨_, _, (List.dropLast_append_getLast hne).symm⟩
  have hlen : pre.length = 353 := by
    rw [List.length_append, List.length_singleton] at h354
    omega
  refine ⟨h354, pre, b, rfl, ?_, ?_⟩
  · have e2 : (cutFirstFull.map (·.2.1))[353]? = some b.place := by
      rw [← e, hc, ← hlen]
      simp
    have e3 := written_places.1
    rw [e2] at e3
    have e4 := finishWritten_at_K2
    rw [hf] at e4
    exact (Option.some.inj e3).trans (Option.some.inj e4).symm
  · rw [hlen]
    exact trees_to_at_head h O

/-- **hE.** -/
theorem early_public (h : P5J.AtMg OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF) :
    (H2U.p12OfMade Zp.made).early = true := by
  rw [numbersL_at_head h]
  exact (alike_head_L h).early.trans (by decide +kernel)

/-- **hst and FP.** -/
theorem form_public (h : P5J.AtMg OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF) :
    ∃ (a next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage),
      (H2U.p12OfMade Zp.made).nums.stages = a :: next :: rest ∧
      FormPub (H2U.p12OfMade Zp.made) a next rest := by
  rw [numbersL_at_head h]
  have hF := (ProofFile.Honest.K12.Light.facts_head_L h).form
  cases hs : (fourOf Np).L.nums.stages with
  | nil =>
    unfold formPubB at hF
    rw [hs] at hF
    cases hF
  | cons a l =>
    cases l with
    | nil =>
      unfold formPubB at hF
      rw [hs] at hF
      cases hF
    | cons next rest => exact ⟨a, next, rest, rfl, formPub_of_B _ a next rest hs hF⟩

/-- **hos₁.** -/
theorem first_public (h : P5J.AtMg OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF) :
    (H2U.p12OfMade Zp.made).nums.first.length = 1 := by
  rw [(seated_written h).1]
  exact osL_length

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.placeL_only
#print axioms ProofFile.Honest.K12.Sim2.finishWritten_at_K2
#print axioms ProofFile.Honest.K12.Sim2.front_public
#print axioms ProofFile.Honest.K12.Sim2.early_public
#print axioms ProofFile.Honest.K12.Sim2.form_public
#print axioms ProofFile.Honest.K12.Sim2.first_public
