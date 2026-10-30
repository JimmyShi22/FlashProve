-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K04OfHead.lean: THE KIND K4's LAW IN THE COUNTED FORM, WITH NO CONDITION OF K4's
OWN LEFT BESIDE THE HEAD. Two statements with their proofs. No new argument: calls.

FIRST. A MEMBER OF THE HEAD IS PROVED AT `storedPublicFiles` AND `zGap` ALONE (AT secondHashFunction; SIDE LIBRARY
AtFullSide/Top/). ALL THE WEIGHT LIES IN `k4Row_of_head` (Johnson/Road/K4/K4RowOfHead.lean): under
the head, K4's one test with code on the public parameters accepts. This file adds nothing to it.

WHAT IT IS FOR. `K4Last hA` (Johnson/Road/K4/K04Last.lean) has one field: row: `k4RowB Zp = true`.
The fourteen entry tests do not ask that test (the fourteenth row is on another matter): so the
field is paid by a theorem from the head, or not at all.

  `k4Last_of_head`: `K4Last hA`, at every head hA.
  `k04_of_head`: for every 𝔏 with the three lists' heads: `AtMgA.Kind hA 𝔏 KindName.K4`: THE FORM IN
    WHICH A KIND's LAW IS COUNTED, WITH NO CONDITION OF K4's OWN LEFT BESIDE THE HEAD.

Limits. The full size alone. The second hash function alone. The head in this tree stands over
fourteen entry tests (Johnson/Desc/Laid/ProofAsks.lean). Nothing on soundness.
-/
import Johnson.Road.K4.K04Last
import Johnson.Road.K4.K4RowOfHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (KindName)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **THE LAST LIST, FROM THE HEAD.** -/
theorem k4Last_of_head (hA : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) : K4Last hA :=
  ⟨k4Row_of_head hA⟩

/-- **K4's LAW IN THE FORM IN WHICH A KIND's LAW IS COUNTED: its binders are the head hA, the
filling 𝔏 and the three equations q₁ q₂ q₃ on the description's flat lists, as in every kind's
counted form: no condition of K4's own.** UNDER THE HEAD hA: A MEMBER OF THE HEAD IS PROVED AT
`storedPublicFiles` AND `zGap` ALONE (AT secondHashFunction; SIDE LIBRARY AtFullSide/Top/).
-/
theorem k04_of_head (hA : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (𝔏 : P5J.Free OnBytes.Flat.numsFull D (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃) :
    P5J.AtMgA.Kind hA 𝔏 KindName.K4 :=
  k04_counted_of_last hA (k4Last_of_head hA) 𝔏 q₁ q₂ q₃

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.k4Last_of_head
#print axioms OnBytes.Road.K4.k04_of_head
