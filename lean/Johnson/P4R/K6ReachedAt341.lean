-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P4R/K6ReachedAt341.lean: THE JOIN OF TWO HALVES: AT THE IOP AS WRITTEN IN LEAN, IN THE GOALS' SCOPE, A STATE
THAT IS REACHED AT BORDER 341 OF THE FIRST CHAIN MEETS K6Reached (Johnson/Desc/Kinds/Law/K6Reached.lean): the tables of the
reads are not laid, and the merge has not laid its end value. One theorem: three calls.
  P4.back_341 (P4R/Back341N.lean): "reached at 341" is the outcome of three accepts, at 338, 339 and 340, each in its
      own term.
  AtFold.made_H1, kept_H2, kept_H3: the first accept makes K6Reached, the two others keep it.
WHAT IS LEFT: hpl: the sub-protocol at number 340 of the flat list passes its own test on the list of rounds (planOk).
Every letter under "there is": none in the conclusion. THE WITNESSES INSIDE "REACHED" (the rounds and columns of the three
accepts) ARE NOT THE RUN'S OWN: nothing is concluded of them: two fields of the state s0 alone.
What it does not say. Nothing of a state that bears a mark is excluded or asked: the sentence holds of every reached state.
Nothing on soundness.
-/
import Johnson.P4R.Back341N
import Johnson.Desc.Kinds.Law.K6Reached

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P4

open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Kinds.Head.Law.AtFold (K6Reached made_H1 kept_H2 kept_H3)
open Johnson.Desc.First.Walk.Tied (Reach)
open ProofFile (Cl)
open Inst.Model (ScalesAndPolicy)

/-- **A state reached at border 341 meets K6Reached.** -/
theorem k6Reached_341 {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hpl : ∀ b3, c.blocksInOrder[340]? = some b3 → b3.planOk = true) {XP : Type} {start : XP → S}
    {z : XP} {s0 : S} (h : Reach 0 c.blocksInOrder start 341 (z, s0)) : K6Reached s0 := by
  obtain ⟨s338, s339, s340, _, ⟨rs1, gs1, h1⟩, ⟨p, n, HP, rs2, gs2, h2⟩, b3, Q, sent, laid, rs3,
    gs3, hb3, h3, hp3⟩ := back_341 hS hR O h
  exact kept_H3 K3Lot.ofForm 3 laid sent Q [] s340 s0 rs3 gs3 (hp3 (hpl b3 hb3)) h3
    (kept_H2 h2 (made_H1 Bs.G₀.W 24 "H:1" (k7Front Bs.G₀.W) Bs.G₀.W.H.tl (k7_front Bs.G₀.W)
      s338 rs1 gs1 s339 h1))

end P4

#print axioms P4.k6Reached_341
