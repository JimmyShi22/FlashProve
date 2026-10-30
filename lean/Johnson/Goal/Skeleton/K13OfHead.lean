-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Skeleton/K13OfHead.lean: kind K13's row in the counted form, from the head of the
closed constant and the three equations on the free letters alone. One theorem with its proof: one
call. It stands over the proof file's entry tests' list (`LPFD.lawsAsk`)
of fourteen rows.

Why. `K13.Law.k13_kindD` (Johnson/Desc/AtSeats/K13KindTight.lean) gives the row
under two premises beside the head: the first comparison of the plan with written values accepts,
and the first chain's cut is the written one. Both follow from the head's own fields `scope` and
`laid`: `P5J.pins_of_laid` (Johnson/Goal/Skeleton/PinsOfLaid.lean). So kind K13 needs no condition
of its own beside the head.

Main names. hA: the head (`P5J.AtMgA` at the second hash function). 𝔏: a filling of the free
letters. q₁ q₂ q₃: its three lists are the three chains' own.
  `k13_kind_of_head`: `hA.Kind 𝔏 KindName.K13`.

Limits. It pays no premise of the head: whether a head exists at any public files is not shown here.
It has content only at an 𝔏 under q₁ q₂ q₃. The second hash function alone. The full size alone.
What `hA.Kind 𝔏 .K13` says is left to K13's files. Nothing on soundness by itself.

-/
import Johnson.Desc.AtSeats.K13KindTight
import Johnson.Goal.Skeleton.PinsOfLaid

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K13.Law

open OnBytes.Maker (WholeD)
open OnBytes.Flat (numsFull)
open VerifiableInference.Desc (Chain KindName)
open VerifiableInference.Desc.First (S)
open ProofFile (Cl)

/-- **Kind K13's row, counted form, from the head alone.** -/
theorem k13_kind_of_head {Zl : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain S Cl} {x₀ : First.Look.Place}
    (hA : P5J.AtMgA OnBytes.secondHashFunction Zl D r₀ Zp Np cF x₀)
    (𝔏 : P5J.Free numsFull D (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃) :
    hA.Kind 𝔏 KindName.K13 :=
  k13_kindD hA 𝔏 q₁ q₂ q₃ (P5J.pins_of_laid hA.scope hA.laid).1
    (P5J.pins_of_laid hA.scope hA.laid).2

end VerifiableInference.Desc.K13.Law

#print axioms VerifiableInference.Desc.K13.Law.k13_kind_of_head
