-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/RadiiAtAllPaid.lean: THE PREMISE hRad OF RadiiAtAll.lean AND RadiiAtTwo.lean
(this folder) BY A CALL OF `radii_in_scope` (Johnson/HB/LLHARD/RadiiInScope.lean): so
RadAt at the fifty later places of the sub-protocol K1, the premise hPlanR, and PlanRest at the two
other places stand at the closed constant under hA, O, hP1, hP2 alone. Calls alone;
nothing is evaluated.

  `hRad_atAll`   wherever the maker of the sendings' rows returns at the public files, the first
                 proof chain's rows have the written radii
  `radAt_paid` `hPlanR_paid` `W_rest_paid` `G_rest_paid`   the statements of the two files with hRad
                 laid in. (W_HP, G_HP: `W_HP_atAll`, `G_HP_atAll` at `hRad_atAll hA hP1`, still from
                 their two leftovers each.)

That the maker of the rows returns is had here off the head's own field `plan.radii`
(`rows_atAll`, RadiiAtAll.lean), which in the assembly is itself paid from that very condition: an
implication for the call at the head, no payment of it: it stays owed by name.
What is not claimed. That hP1 or hP2 accept at any files. No member of the head hA. Nothing on
soundness.

-/
import Johnson.Desc.K1.Law.RadiiAtTwo
import Johnson.HB.LLHARD.RadiiInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1

open OnBytes OnBytes.Params Johnson.G
open OnBytes.Maker (WholeD)
open OnBytes.Slice (frS)
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.Sound (nTrees)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K13.Law (openAt wMsgFull)
open VerifiableInference.PlanWritten (madePinnedAt cutIs)
open _root_.Desc.K14.Law (seatZ secondAt)
open ProofFile (Cl)
open IM (Open)

section
variable {Zl : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x₀ : First.Look.Place} {Bs : ProofFile.PureBase} {base₀ : List (Block S Cl)}

theorem hRad_atAll (hA : P5J.AtMgA OnBytes.secondHashFunction Zl D r₀ Zp Np cF x₀)
    (hP1 : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true) :
    ∀ R, sendRowsOf Zl.pol Zl.lay Zl.KL = .ok R →
      (P5T.firstRows R).map (·.sampled) = radsFull :=
  fun _ hr => LinkJoin.radii_in_scope hA.scope hA.laid.pub hP1 hr

variable (hA : P5J.AtMgA OnBytes.secondHashFunction Zl D r₀ Zp Np cF x₀)
  (O : Open OnBytes.secondHashFunction Zl.pol Zl.lay Zl.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
    (seatZ Zp Np) (secondAt Zp Np))
  (hP1 : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true)
  (hP2 : cutIs (P5J.F0T OnBytes.secondHashFunction Zp Np cF) = true)
include hA O hP1 hP2

theorem radAt_paid (l : ℕ) (hl : l < 25) (d : Bool) :
    RadAt Zp.made.proof.1.sends.length (P5J.At.rad Zp Zl.lay) (P5T.planSeats Zp Zp.D.1)
      (parL Zp Bs.G₀ l d) (radRec (recL l d) (parL Zp Bs.G₀ l d))
      (baseD (D.at frS.P.T.a) cF l d) :=
  radAt_atAll hA O hP1 hP2 (hRad_atAll hA hP1) l hl d

/-- **hPlanR.** -/
theorem hPlanR_paid : ∀ l, l < 25 → ∀ d : Bool,
    PlanRest hA.𝔇.pubD.cs hA.𝔇.G hA.𝔇.ms (parL Zp Bs.G₀ l d)
      (radRec (recL l d) (parL Zp Bs.G₀ l d)) (baseD (D.at frS.P.T.a) cF l d)
      (hA.𝔇.N.sent l (momL d)) :=
  hPlanR_atAll hA O hP1 hP2 (hRad_atAll hA hP1)

theorem W_rest_paid : PlanRest hA.𝔇.pubD.cs hA.𝔇.G hA.𝔇.ms (parWZ Zp wMsgFull)
    (radRec 81 (parWZ Zp wMsgFull)) (nTrees ((D.at frS.P.T.a).ds₁.take (inFront cF 356)))
    [hA.𝔇.N.w] :=
  W_rest_atAll hA O hP1 hP2 (hRad_atAll hA hP1)

theorem G_rest_paid : PlanRest hA.𝔇.pubD.cs hA.𝔇.G hA.𝔇.ms (firstPar Bs.G₀.first (gpOf Zp))
    (radRec 0 (firstPar Bs.G₀.first (gpOf Zp)))
    (nTrees ((D.at frS.P.T.a).ds₁.take (inFront cF 2)))
    (First.sampledIn hA.𝔇.N (openAt Sound.linksFull psF (2 + 1))) :=
  G_rest_atAll hA O hP1 hP2 (hRad_atAll hA hP1)

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.hRad_atAll
#print axioms VerifiableInference.Desc.K1.radAt_paid
#print axioms VerifiableInference.Desc.K1.hPlanR_paid
#print axioms VerifiableInference.Desc.K1.W_rest_paid
#print axioms VerifiableInference.Desc.K1.G_rest_paid
