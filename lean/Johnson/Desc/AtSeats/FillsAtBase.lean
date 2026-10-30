-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
import Johnson.Desc.K13.Law.FillsK13C
import Johnson.Desc.Sound.MgBase
import Johnson.Desc.K13.Law.AtRecord
/-
THREE OF K13's PREMISES ON THE MEANING, PAID AT THE COMPOSED MEANING OVER ITS CLOSED BASE: mgAll 𝔇 mgBase, AT EVERY 𝔇.
  quietC_said          at each of the eleven items at which FillsK13C asks that pubP say nothing, the table First.saysNone (AllSaid.lean) has «no sentence is meant»: decide.
  **fillsK13C_base**   FillsK13C 𝔇.P13 𝔇.N (mgAll 𝔇 mgBase) 𝔇.cs 𝔇.arr 𝔇.mat13 𝔇.G 𝔇.smp 𝔇.ms 𝔇.decT: thirteen fields by rfl (each field or public test of the meaning IS K13's
                       files' own term); the fourteenth by mgAll_pubP_said.
  **inOrder_rides_base**   «in order» at mgAll 𝔇 mgBase rides over the joined sub-protocol's step: it reads the public part alone (mgAll_inOrder_base), which the step keeps.
  base_more            mgBase's door is empty: rfl.
It says which terms the fields ARE. Nothing on any sub-protocol. NO SOUNDNESS.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open VerifiableInference.Desc.Sound (MgData mgAll mgBase CellsQ MsgT mgAll_pubP_said mgAll_inOrder_base)

theorem quietC_said : ∀ q ∈ quietC, (First.saysNone q).isSome = true := by decide

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X)

theorem fillsK13C_base :
    FillsK13C 𝔇.P13 𝔇.N (mgAll 𝔇 mgBase) 𝔇.cs 𝔇.arr 𝔇.mat13 𝔇.G 𝔇.smp 𝔇.ms 𝔇.decT where
  pile := fun _ _ _ => Iff.rfl
  pileOne := fun _ _ _ => Iff.rfl
  frontOk := fun _ => rfl
  evalLaid := fun _ => rfl
  wSits := fun _ => rfl
  indexIs := fun _ => rfl
  indexThere := fun _ => rfl
  held := fun _ => rfl
  shown := fun _ => Iff.rfl
  noColl := fun _ _ => Iff.rfl
  pin := fun _ _ _ => Iff.rfl
  pinW := fun _ _ _ => Iff.rfl
  decodes := fun _ _ => Iff.rfl
  quiet := fun q hq x => mgAll_pubP_said 𝔇 q x (quietC_said q hq)

theorem inOrder_rides_base (Cl : Type) (W : Where) (x x' : P × First.S) (h : StepM3 Cl W x x')
    (hx : (mgAll 𝔇 mgBase).inOrder x = true) : (mgAll 𝔇 mgBase).inOrder x' = true := by
  rw [mgAll_inOrder_base] at hx ⊢
  rw [h.1]
  exact hx

end

theorem base_more {P W : Type} : (mgBase : First.Meaning P W).more = {} := rfl

end VerifiableInference.Desc.K13.Law
