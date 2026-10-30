-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/RestAt9.lean: "IN ORDER" OF THE COMPOSED FILLING OVER ITS
BASE (`mgAll 𝔇 mgBase`, Johnson/Desc/Sound/MgBase.lean) READS THE PUBLIC PART
ALONE (`mgAll_inOrder_base`): so it rides over whatever leaves the public part. Statements with
their proofs. `inOrder9_same`: at two statements with one public part it answers alike.
  `rest9_M3`, `rest9_M4`, `rest9_G`: so it rides over an accepting step of kind K13's batching, of
  W's commitment and of the first segment's opening: the premise hrest of the laws' calls, at that
    filling.
  `hin9`: and it holds at every state beside a public part at which it holds at one: the premise
  hin of
    K13's and K1's files' terms of `IM.Hands`, AT THAT FILLING, is one test on the public part.
What is not claimed. That the test on the public part accepts. Nothing on the wider fillings' "in
order", which reads the state. Nothing on soundness.
-/
import Johnson.Desc.Sound.MgBase
import Johnson.Desc.K13.Law.AtTableFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace HashBuild
open OnBytes OnBytes.Params OnBytes.Model
open Desc.Plain
open Johnson.Desc.First.Walk (LayPar)
open VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MgData mgAll mgBase mgAll_inOrder_base)
open VerifiableInference.Desc.K13 (Where)
open VerifiableInference.Desc.K13.Law (StepM3 StepM4 StepG)

section
variable {Xi P Tok Cl : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X)

/-- It reads the public part alone. -/
theorem inOrder9_same {x x' : P × S} (h : x'.1 = x.1) :
    (mgAll 𝔇 mgBase).inOrder x' = (mgAll 𝔇 mgBase).inOrder x := by
  rw [mgAll_inOrder_base, mgAll_inOrder_base, h]

theorem rest9_M3 {Pw : Where} (x x' : P × S) (h : StepM3 Cl Pw x x')
    (h0 : (mgAll 𝔇 mgBase).inOrder x = true) : (mgAll 𝔇 mgBase).inOrder x' = true := by
  rw [inOrder9_same 𝔇 h.1]
  exact h0

theorem rest9_M4 {Pw : Where} {P' : K1.Par} (x x' : P × S) (h : StepM4 Cl Pw P' x x')
    (h0 : (mgAll 𝔇 mgBase).inOrder x = true) : (mgAll 𝔇 mgBase).inOrder x' = true := by
  rw [inOrder9_same 𝔇 h.1]
  exact h0

theorem rest9_G {q : Params.First} {gp : GPar} {nm : String} {Y : LayPar} {fvs : List Bool}
    {kCol : ℕ} (x x' : P × S) (h : StepG Cl q gp nm Y fvs kCol x x')
    (h0 : (mgAll 𝔇 mgBase).inOrder x = true) : (mgAll 𝔇 mgBase).inOrder x' = true := by
  rw [inOrder9_same 𝔇 h.1]
  exact h0

/-- One test on the public part. -/
theorem hin9 (z : P) (h : (_root_.Meaning.backReq (𝔇.reqB z)).isSome = true) (s : S) :
    (mgAll 𝔇 mgBase).inOrder (z, s) = true := by
  rw [mgAll_inOrder_base]
  exact h

end

end HashBuild
