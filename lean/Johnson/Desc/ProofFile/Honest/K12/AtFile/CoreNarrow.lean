-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/CoreNarrow.lean: the two tests of `linesB` beyond `frontFiveB` at the
closed narrow shape `narrowW` (WNarrowAtW.lean), and `linesB` at a record that agrees with it.

  `many_narrowW`, `ts_narrowW`   by the kernel (CoreNarrowGuards.lean evaluates them first)
  `lines_of_narrow`   `linesB` at the record on entry, at a job at the seated place with the printed members'
                   numbers, where the record's core agrees with `narrowW`

Limits. `frontFive_narrowW` is WNarrowAtW.lean's closed line, not this file's. Nothing on a run here.
Nothing on completeness,
on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.CoreNarrowGuards
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WAtHead
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WFrontAtOwn

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12.AtFile
open VerifiableInference.Desc.Ground.Sh (CoreSh coreSh)
open VerifiableInference.Desc.K12 (T12)
open H2K.Member (piWFull codesFull)
open ProofFile.Honest.Sh (testSh)
open ProofFile.Honest.K12.AtProof (fourOf treesW)
open ProofFile.Honest.K12.Light (ManyJob manyFitsS tsLenOf alike_head_W manyFitsS_alike tsLenOf_alike
  frontFiveB_alike)

theorem many_narrowW :
    manyFitsS piWFull memsW (treesW piWFull) ⟨narrowW, 0, .nothing, some 198⟩ = true := by
  decide +kernel

theorem many_narrowW_bent :
    manyFitsS piWFull memsW.reverse (treesW piWFull) ⟨narrowW, 0, .nothing, some 198⟩ = false := by
  decide +kernel

theorem ts_narrowW : tsLenOf piWFull ⟨narrowW, 0, .nothing, some 198⟩ = 3 := by decide +kernel

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl} {W X : Type}

/-- **`linesB` at the record on entry**, where its core agrees with `narrowW`. -/
theorem lines_of_narrow (h : P5J.AtMg o Z D r Zp Np cF) (A : ManyJob W X)
    (hp : A.p = (fourOf Np).W) (hm : A.mems.map (·.shape) = memsW)
    (ht : A.trees = treesW piWFull) {t : T12}
    (hc : SameCore [4, 197, 198, 199] t.g 0 (coreSh ⟨t.st, t.book, t.roots⟩) narrowW)
    (hmask : t.mask = some 198) (hpass : t.pass = .nothing) :
    linesB A codesFull 3 (testSh t) = true := by
  have al := alike_head_W h
  have e : testSh t = ⟨coreSh ⟨t.st, t.book, t.roots⟩, t.g, .nothing, some 198⟩ := by
    unfold testSh
    rw [hpass, hmask]
    rfl
  have hid : (198 : ℕ) ∈ [4, 197, 198, 199] := by simp
  rw [e]
  unfold linesB
  rw [hp, hm, ht, frontFiveB_alike al, manyFitsS_alike al, tsLenOf_alike al]
  have e₁ := (frontFive_same hc piWFull codesFull early_written hid).symm.trans frontFive_narrowW
  have e₂ := (manyFits_same hc piWFull early_written memsW (treesW piWFull) hid).symm.trans
    many_narrowW
  have e₃ := (tsLen_same hc piWFull early_written hid).symm.trans ts_narrowW
  have e₂' : manyFitsS piWFull memsW (treesW piWFull)
      (ProofFile.Honest.Sh.thinOf ⟨coreSh ⟨t.st, t.book, t.roots⟩, t.g, .nothing, some 198⟩) = true := e₂
  have e₃' : tsLenOf piWFull
      (ProofFile.Honest.Sh.thinOf ⟨coreSh ⟨t.st, t.book, t.roots⟩, t.g, .nothing, some 198⟩) = 3 := e₃
  rw [e₁, e₂', e₃']
  rfl

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.many_narrowW
#print axioms ProofFile.Honest.K12.AtFile.many_narrowW_bent
#print axioms ProofFile.Honest.K12.AtFile.ts_narrowW
#print axioms ProofFile.Honest.K12.AtFile.lines_of_narrow
