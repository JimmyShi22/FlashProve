-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/LookAt342.lean: "THE TWO READERS OF THE LOOKUP's HEARING AGREE" AT EVERY STATE
THAT IS REACHED IN FRONT OF SUB-PROTOCOL 342 (the output head's reads), AT THE CLOSED CONSTANT
(P5J.mgAtAll, Johnson/P5J/MgAtAll.lean): the clause hlk (x.2.look? = x.2.lookHeard?) of the output
head's planes' premises. By calls.
  reach_back    the last step of "reached", inverted: a state reached at border k + 1 stands behind
                an accepting step of sub-protocol k from a state reached at border k
  **look_at_342**   a.1.2.look? = a.1.2.lookHeard? from the head and "reached" alone
HOW. In scope sub-protocol 341 of the flat list is the output head's own sub-protocol as seated
(k6_of, k6_at_341: Johnson/IMR/K6Seat.lean, FlatScope.lean): it only adds
refusals to seatedClaims' block (alone_underR; step_under, Johnson/Desc/Sound/SeatGuardChain.lean);
behind an accepting step of that block the two readers agree (seated_yes,
Johnson/Desc/Kinds/Law/SeatedYes.lean, over its look_behind).
PREMISES: the shared head hA · "reached" (the wider RchAt). Neither the promise nor "no mark" is
spent.
What is not claimed. That hA can be met: NO MEMBER. Nothing at another border. Nothing on soundness.

-/
import Johnson.P5J.MgAtAll
import Johnson.IMR.K6Seat
import Johnson.IMR.FlatScope
import Johnson.Desc.Kinds.Law.SeatedYes
import Johnson.Desc.Sound.SeatGuardChain
import Johnson.Top.H0.Walk.ReachAt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Maker
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound
open Johnson.Desc.First.Walk.Tied (Reach StepYes RchAt rchAt_raw)
open ProofFile (Cl)

/-- The last step of "reached", inverted. -/
theorem reach_back {T C P : Type} {ft : ℕ} {bs : List (Block T C)} {start : P → T} {k : ℕ}
    {x : P × T} (h : Reach ft bs start (k + 1) x) :
    ∃ s b, Reach ft bs start k (x.1, s) ∧ bs[k]? = some b ∧ StepYes ft b s x.2 := by
  cases h with
  | succ h1 h2 h3 => exact ⟨_, _, h1, h2, h3⟩

/-- **The two readers of the lookup's hearing agree in front of sub-protocol 342.** -/
theorem look_at_342 {Zl : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain S Cl} {x₀ : First.Look.Place}
    (hA : P5J.AtMgA OnBytes.secondHashFunction Zl D r₀ Zp Np cF x₀) {Str : Type}
    (a : (ProofFile.InstPub × S) × Str) (hr : RchAt (P5J.F0T OnBytes.secondHashFunction Zp Np cF) 342 a) :
    a.1.2.look? = a.1.2.lookHeard? := by
  obtain ⟨Bs, base, O⟩ := hA.laid.opened
  obtain ⟨Lk, b, b', ms, h1, h2, -, hb', hla, -⟩ := IM.k6_of hA.scope hA.reads O
  have h341 := (IM.k6_at_341 hA.scope hA.reads O h1 h2).1
  have hraw : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (341 + 1) a.1 := rchAt_raw hr
  obtain ⟨s, bb, -, hbb, R, c, -, hstep⟩ := reach_back hraw
  obtain rfl : bb = b := Option.some.inj (hbb.symm.trans h341)
  exact (Kinds.Head.Law.seated_yes hb' (step_under (IM.alone_underR hla) hstep)).2.2.2.1

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.reach_back
#print axioms VerifiableInference.Desc.K1.look_at_342
