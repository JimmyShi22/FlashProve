-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K09Shut.lean: AT THE CLOSED CONSTANT: THE SHUTTING's SIDE OF WHAT IS LEFT OF THE
BATCHING KIND's CONDITION (the last conjunct of `AtMgA.K9Rest`, K09Rest.lean) IS PAID WHOLE, FROM
THE HEAD (WHICH STANDS WITH FOURTEEN ENTRY TESTS): what is left at a link's shutting's piece
(`ShutRest`, Johnson/Desc/First/Link/Law/ShutRest.lean: four fields) at Zc := Zp, layF := Z.lay, Dw
:= D; «Zp is made by the road's own maker of the public data»; «the switch that spends carry 24 does
not stand at the head». The first theorem's term goes through Lean here.
Two theorems.

What is said.
  `shutRest_at`: **at every number k and piece qs of the seated row, and every sub-protocol b: there
    are o pol lay KL with `ProofFile.pureRoad.pub o pol lay KL = .ok Zp`, and `ShutRest h.𝔇 (atRec qs b)
    Zp Z.lay D`**, under the tower's own three equations on the flat lists' heads. mh: `meantEx_at`,
    `headIs_at` (Johnson/LPFE1R/K9RestLight.lean); hcr: `carry_at`, and the maker: `pub_at`
    (Johnson/LPFE1R/ShutRestAt.lean); hW and hbase: `P1L20.whole_atAll`
    (Johnson/P1L20R/FrameFourAll.lean). `k9_shut_at`: **the conjunct itself, to the letter**, with
    `P1L20.stands24_atAll` (Johnson/P1L20R/Stands24AtAll.lean).

Limits. A JOIN OF THEOREMS THAT LAY. No premise is left but the head (`AtMgA`, which stands with
fourteen entry tests) and the three equations. IT SAYS NOTHING OF THE LINK's THREE OTHER PIECES,
where the debt lies. AT THE SECOND HASH FUNCTION ALONE. Nothing on soundness.

-/
import Johnson.P5J.K09Rest
import Johnson.LPFE1R.K9RestLight
import Johnson.LPFE1R.ShutRestAt
import Johnson.P1L20R.FrameFourAll
import Johnson.P1L20R.Stands24AtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Road OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.RunA
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block FileDescription Place Strs Wit Link)
open VerifiableInference.Desc.First (S ModelPart Numbers)
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open _root_.Run _root_.Run.PQ
open VerifiableInference.Desc (Chain KindName)
open VerifiableInference.Desc.LinkJoin (atRec ShutRest)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

local notation "FD" => F0T OnBytes.secondHashFunction Zp Np cF

/-- **THE SHUTTING's REST, WHOLE.** -/
theorem shutRest_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D FD At.Tok) (q₁ : (FD).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (FD).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂) (q₃ : (FD).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃) (k : ℕ)
    (qs : _) (hq : (h.toAtMg.row 𝔏)[k]? = some qs) (b : _) :
    (∃ o pol lay KL, ProofFile.pureRoad.pub o pol lay KL = .ok Zp) ∧
      ShutRest h.𝔇 (atRec qs b) Zp Z.lay D :=
  ⟨pub_at h, ⟨meantEx_at h, headIs_at h⟩, carry_at h, (P1L20.whole_atAll h 𝔏 q₁ q₂ q₃).1,
    (P1L20.whole_atAll h 𝔏 q₁ q₂ q₃).2 k qs hq⟩

/-- **THE SHUTTING's SIDE OF WHAT IS LEFT OF THE CONDITION, WHOLE**: the last conjunct of
AtMgA.K9Rest at a link, to the letter (k: the shutting's number; b₅: any sub-protocol). -/
theorem k9_shut_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D FD At.Tok) (q₁ : (FD).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (FD).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂) (q₃ : (FD).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃) (k : ℕ)
    (b₅ : Block S ProofFile.Cl) :
    ∀ qs, (h.toAtMg.row 𝔏)[k]? = some qs → ∃ Zc layF Dw,
      (∃ o pol lay KL, ProofFile.pureRoad.pub o pol lay KL = .ok Zc) ∧
      (ProofFile.pAtK2 Zc 24).stands ≠ .head ∧
      ShutRest h.𝔇 (atRec qs (below b₅)) Zc layF Dw :=
  fun qs hq => ⟨Zp, Z.lay, D, (shutRest_at h 𝔏 q₁ q₂ q₃ k qs hq (below b₅)).1,
    P1L20.stands24_atAll h, (shutRest_at h 𝔏 q₁ q₂ q₃ k qs hq (below b₅)).2⟩

end P5J

#print axioms P5J.shutRest_at
#print axioms P5J.k9_shut_at
