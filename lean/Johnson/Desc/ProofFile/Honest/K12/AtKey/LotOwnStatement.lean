-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtKey/LotOwnStatement.lean: CAN THE PREMISE ON THE STATE BE MET: `StatementAtOwnTest`
(LotOwnWords.lean) at every state of the last chain whose shape is the closed term in front of the own test (the `A₂`
of `stand_shape`, OwnShape.lean), at the numbers 0, 9, 11 and at parts under `OwnSenders`.

  `statementLinesB`     the lines that the tie reads off the shape: the own group's members are [0, 9, 11]; the three
                        messages' shapes are the written sendings'; the codes are the written plan's; the sendings'
                        counts of messages are 1 and 2
  `statement_closed`    they hold at the shape behind the chain's first two blocks. By the kernel
  `statement_bent`      control: not at the next group
  `statement_at_shape`  so `StatementAtOwnTest` at a state of that shape

Limits.
- That a stand's state has that shape is `stand_shape` (OwnShape.lean), in scope, where the verifier's fold over the
  chain's first two blocks returns it and the start has its shape: premises there.
- At the written sizes. FORM ALONE: nothing on what a message holds.
- Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtKey.LotOwnLines

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12.AtKey
open OnBytes (Group)
open VerifiableInference.Desc.Ground.Sh (stSh grpSh orcSh grp_get orc_get)
open VerifiableInference.Desc.Third (S₃)
open AtPublicFiles.KeyFile (KeyParts)
open AtPublicFiles.KeyLay (parIK parWK)
open AtPublicFiles.AtFiles (Sh₃ sh₃ SF ZW)
open AtPublicFiles.AtFiles.Full (QK X0)

/-- **The lines that the tie reads off the shape in front of the test.** -/
def statementLinesB (b : Sh₃) : Bool :=
  ((b.1.st.groups[b.2.own]?).any fun G => G.members == [0, 9, 11]) &&
    decide ((b.1.st.oracles[0]?).map (·.shape) = some (Johnson.Prover.Send.shapeAt parIK 0)) &&
    decide ((b.1.st.oracles[9]?).map (·.shape) = some (Johnson.Prover.Send.shapeAt parWK 0)) &&
    decide ((b.1.st.oracles[11]?).map (·.shape) =
      some (Light.shapeAt (K14.jobOmega ⟨QK, 0⟩) 0)) &&
    decide (b.1.st.codes = QK.codes) && parIK.sent.size == 1 && parWK.sent.size == 2

/-- The run from the chain's first shape over the first two blocks, and the lines behind it. -/
def statementClosedB (bend : Sh₃ → Sh₃) : Bool :=
  match X0 with
  | some a =>
    match ZW.run 2 a with
    | .ok b => statementLinesB (bend b)
    | .error _ => false
  | none => false

/-- **The lines hold.** By the kernel. -/
theorem statement_closed : statementClosedB id = true := by decide +kernel

/-- Control: at the next group they do not. -/
theorem statement_bent :
    statementClosedB (fun b => (b.1, { b.2 with own := b.2.own + 1 })) = false := by
  decide +kernel

variable {W₀ Rc X₀ X Wk : Type} {K : KeyParts W₀ Rc X₀ X Wk}

/-- **`StatementAtOwnTest` at a state of the closed shape.** -/
theorem statement_at_shape (h : OwnSenders K) {A₀ A₂ : Sh₃} (h₀ : X0 = some A₀)
    (h₂ : ZW.run 2 A₀ = .ok A₂) {st : S₃} (hsh : sh₃ SF st = A₂)
    (challengesBeforeVectorW challengesOfFirstChain : ℕ) :
    StatementAtOwnTest st.st st.loc.own K
      (numbersAtFullSize challengesBeforeVectorW challengesOfFirstChain) := by
  have c := statement_closed
  unfold statementClosedB at c
  rw [h₀] at c
  have c₁ : (match ZW.run 2 A₀ with
    | .ok b => statementLinesB (id b)
    | .error _ => false) = true := c
  rw [h₂] at c₁
  have c₂ : statementLinesB A₂ = true := c₁
  unfold statementLinesB at c₂
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at c₂
  obtain ⟨⟨⟨⟨⟨⟨gm, s0⟩, s9⟩, s11⟩, cd⟩, n1⟩, n2⟩ := c₂
  subst hsh
  have orc : ∀ i : ℕ, (st.st.oracles[i]?).map (fun x : OnBytes.Oracle => x.shape) =
      (((sh₃ SF st).1.st.oracles[i]?).map
        fun x : VerifiableInference.Desc.Ground.Sh.OrcSh => x.shape) := fun i => by
    show _ = (((stSh st.st).oracles[i]?).map
      fun x : VerifiableInference.Desc.Ground.Sh.OrcSh => x.shape)
    rw [orc_get, Option.map_map]
    rfl
  have z1 : K.idx.P.sent.size = 1 := by rw [h.idxSent]; exact n1
  have z2 : K.w.P.sent.size = 2 := by rw [h.wSent]; exact n2
  refine ⟨fun G hG => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have e : (sh₃ SF st).1.st.groups[(sh₃ SF st).2.own]? = some (grpSh G) := by
      show (stSh st.st).groups[st.loc.own]? = _
      rw [grp_get, hG]
      rfl
    rw [e] at gm
    have g' : ((grpSh G).members == [0, 9, 11]) = true := gm
    have g'' : G.members.toList = [0, 9, 11] := beq_iff_eq.1 g'
    rw [z1]
    exact Array.toList_inj.1 g''
  · rw [z1, z2]
    show 0 + 1 ≤ 9 ∧ 9 + 2 ≤ 11
    exact ⟨by decide, by decide⟩
  · rw [z1]
    decide
  · rw [z2]
    decide
  · rw [z1, (counts_of_alike h.idxSent h.idxCodes fun _ => none).2.2]
    exact (orc _).trans s0
  · rw [(counts_of_alike h.wSent h.wCodes fun _ => none).2.2]
    exact (orc _).trans s9
  · rw [h.sendPar]
    exact (orc _).trans s11
  · rw [h.sendPar]
    exact cd

end ProofFile.Honest.K12.AtKey

#print axioms ProofFile.Honest.K12.AtKey.statementLinesB
#print axioms ProofFile.Honest.K12.AtKey.statementClosedB
#print axioms ProofFile.Honest.K12.AtKey.statement_closed
#print axioms ProofFile.Honest.K12.AtKey.statement_bent
#print axioms ProofFile.Honest.K12.AtKey.statement_at_shape
