-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
One file of the set on the key file's table of joints (Johnson/Desc/Key/KeyBorders.lean).
Johnson/RunOne/KeyReadsL.lean: THE ONE PREMISE ON THE READING THAT THE TEN Keeps OF THE FIRST CHAIN's ROUNDLESS BLOCKS ASK (KeyCaller.ReadsL: of the chain's state the reading reads the oracle messages without their ledgers, the book and the codes) IS MET AT THE READING BaseSt.h₁
(Johnson/RunOne/KeyOneReading.lean: the sample of tenant t of tree j := the sample, by the letter sm, of the statement's message whose number the plan gives to the witness's message arr j t), WHERE THE LETTER sm DOES NOT READ A MESSAGE's LEDGER (BaseSt.SmReads).
  readsL_h₁   **PROVED**: T.SmReads → ReadsL T.h₁
So ReadsL has a member that reads the stored sample off the state; sm itself is a letter.
(Where this and lean/THEOREM.md differ, the page holds.) Nothing on soundness.
-/
import Johnson.RunOne.KeyOneReading
import Johnson.RunOne.KeyCaller

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows1
open OnBytes
open VerifiableInference.Desc VerifiableInference.Desc.Key
open Johnson.RunOne.KeyRows23 (BaseSt)

theorem readsL_h₁ {Cells M Smp Rec : Type} (T : BaseSt Cells M Smp Rec) (h : T.SmReads) : ReadsL T.h₁ := by
  intro p s s' ho hb hc
  refine ⟨fun j t => ?_, rfl⟩
  show (T.orc₁ (T.arr j t)).bind (T.smAt s.d.st) = (T.orc₁ (T.arr j t)).bind (T.smAt s'.d.st)
  congr 1
  funext o
  show (s.d.st.oracles[o]?).bind (T.sm s.d.st.codes o) = (s'.d.st.oracles[o]?).bind (T.sm s'.d.st.codes o)
  rw [hc]
  have q := ho o
  cases h1 : s.d.st.oracles[o]? with
  | none =>
    rw [h1] at q
    cases h2 : s'.d.st.oracles[o]? with
    | none => rfl
    | some x' => rw [h2] at q; cases q
  | some x =>
    rw [h1] at q
    cases h2 : s'.d.st.oracles[o]? with
    | none => rw [h2] at q; cases q
    | some x' =>
      rw [h2] at q
      have e : unl x' = unl x := Option.some.inj q
      show T.sm s.d.st.codes o x = T.sm s.d.st.codes o x'
      rw [← h s.d.st.codes o x none, ← h s.d.st.codes o x' none]
      exact congrArg (T.sm s.d.st.codes o) e.symm

end Johnson.RunOne.KeyRows1

#print axioms Johnson.RunOne.KeyRows1.readsL_h₁
