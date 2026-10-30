-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/WFrontPlan.lean: what the plan says of W's message and of the
first sending, under the head, by the written parameters.

  lin_at_head      the first chain's shape of the test on the table is the written one
  split_at_head    it does not split the row
  ahead_at_head    it sends masks ahead
  wNotice_at_head  W's notice counts an answer
  indexNotice_at_head  the first sending's last notice counts an answer
  maskNamed_at_end the record at the end of the first chain's fold names a mask

Limits.
- Closed facts at the written parameters: nothing on any other plan.
- Nothing on completeness, soundness or what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WFrontOwn
import Johnson.AtFull.Shape.K1NumbersAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtFile
open OnBytes OnBytes.Slice
open VerifiableInference.Desc (Block Chain OpenedColumn foldBlocks)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K13 (whereOf)
open VerifiableInference.Desc.K13.Law (linAt)
open VerifiableInference.PlanWritten (proofSizedFull)
open OnBytes.Maker (WholeD)
open P5J (AtMgA)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

theorem lin_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    Zp.first.lin = proofSizedFull.batch.shape :=
  congrArg (·.lin) (Johnson.AtFull.Shape.where13_at_head h.toAtMg)

theorem split_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    (whereOf Zp).lin.ownSplitNeeded = false := by
  show Zp.first.lin.ownSplitNeeded = false
  rw [lin_at_head h]
  decide +kernel

theorem ahead_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    (whereOf Zp).lin.masksAhead = true := by
  show Zp.first.lin.masksAhead = true
  rw [lin_at_head h]
  decide +kernel

theorem wNotice_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∀ msg, linMessageW Zp.first.lin = some msg → ∃ n, msg[0]? = some n ∧ n.shape.answers ≠ 0 := by
  rw [lin_at_head h]
  have hk : ((linMessageW proofSizedFull.batch.shape).any fun m =>
      (m[0]?).any fun n => n.shape.answers != 0) = true := by decide +kernel
  intro msg hm
  rw [hm] at hk
  simp only [Option.any_some] at hk
  cases hn : msg[0]? with
  | none =>
    rw [hn] at hk
    cases hk
  | some n =>
    rw [hn] at hk
    exact ⟨n, rfl, by simpa using hk⟩

theorem indexNotice_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∃ hk : (VerifiableInference.Desc.K1.firstPar Zp.first
        (VerifiableInference.Desc.K1.gpOf Zp)).sent.size - 1 <
        (VerifiableInference.Desc.K1.shapesOf (VerifiableInference.Desc.K1.firstPar Zp.first
          (VerifiableInference.Desc.K1.gpOf Zp))).length,
      (VerifiableInference.Desc.K1.shapesOf (VerifiableInference.Desc.K1.firstPar Zp.first
        (VerifiableInference.Desc.K1.gpOf Zp)))[(VerifiableInference.Desc.K1.firstPar Zp.first
        (VerifiableInference.Desc.K1.gpOf Zp)).sent.size - 1].answers ≠ 0 := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have e := Johnson.AtFull.Shape.firstPar_at_head h.toAtMg O
  rw [O.first] at e
  rw [e]
  have hk : (VerifiableInference.Desc.K1.firstPar VerifiableInference.Desc.K1.qFull
      Johnson.AtFull.Shape.gpW).sent.size - 1 <
      (VerifiableInference.Desc.K1.shapesOf (VerifiableInference.Desc.K1.firstPar
        VerifiableInference.Desc.K1.qFull Johnson.AtFull.Shape.gpW)).length := by decide +kernel
  refine ⟨hk, ?_⟩
  have key : (((VerifiableInference.Desc.K1.shapesOf (VerifiableInference.Desc.K1.firstPar
      VerifiableInference.Desc.K1.qFull Johnson.AtFull.Shape.gpW))[(VerifiableInference.Desc.K1.firstPar
      VerifiableInference.Desc.K1.qFull Johnson.AtFull.Shape.gpW).sent.size - 1]?).any
      fun s => s.answers != 0) = true := by decide +kernel
  rw [List.getElem?_eq_getElem hk] at key
  simpa using key

/-- **The record at the end of the first chain's fold names a mask.** -/
theorem maskNamed_at_end (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {pI : ProofFile.InstPub} {e₁ : S}
    {rs r₀ : List Fmt.RoundView} {cols c₀ : List OpenedColumn}
    (hf : foldBlocks 0 cF.blocksInOrder (ProofFile.startS Zp pI) rs cols = .ok (e₁, r₀, c₀)) {l : LinFirst}
    (hl : linAt e₁ = some l) : ∃ id, l.mask = some id := by
  obtain ⟨t, mid, msg, R₁, R₂, G₁, G₂, hmsg, h1, h2⟩ := atW_of_fold h hf
  have hr : ∃ a b, R₁ = [a, b] := by
    obtain ⟨ids, d', h3, -, -⟩ := VerifiableInference.Desc.K1.sendAtS_ok _ _ _ _ _ h1
    match R₁, h3 with
    | [a, b], _ => exact ⟨a, b, rfl⟩
  obtain ⟨a, b, rfl⟩ := hr
  obtain ⟨m, hm₁, hsz, hI⟩ := VerifiableInference.Desc.K13.Law.sendAtS_idsLast _ t mid a b G₁ h1
  obtain ⟨m₀, l₀, hm₀, hl₀, hmask⟩ := VerifiableInference.Desc.K13.Law.rowsB_mask h2
  rw [hm₁] at hm₀
  obtain rfl : m = m₀ := by
    injection hm₀
  obtain rfl : l₀ = l := Option.some.inj (hl₀.symm.trans hl)
  exact ⟨_, (hmask hI).2.1 (ahead_at_head h)⟩

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.lin_at_head
#print axioms ProofFile.Honest.K12.AtFile.split_at_head
#print axioms ProofFile.Honest.K12.AtFile.ahead_at_head
#print axioms ProofFile.Honest.K12.AtFile.wNotice_at_head
#print axioms ProofFile.Honest.K12.AtFile.indexNotice_at_head
#print axioms ProofFile.Honest.K12.AtFile.maskNamed_at_end
