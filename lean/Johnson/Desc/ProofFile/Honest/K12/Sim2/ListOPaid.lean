-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the list of the test on G_omega at a run, at the maker's return, no premise on values.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/ListOPaid.lean: CONDITIONAL.

Can the hypotheses be met together at a real run? NOT KNOWN: see Sim2/ListOAtReturn.lean's head, with the
two things not shown there and «not the online prover»: all hold here. Lacking: a K : KindRows whose
shared rows hold rowAtOmega's; a value of `ThreadsP`; ready's and runC's return; that the part is called.

What is here. `onAtRun_O_paid`: `OnAtRun₂` at the list of the test on G_omega at the maker's return, with NO
CLAUSE ON VALUES LEFT: `onAtRun_O_thin` (Sim2/ListOThin.lean) at `saysAt_O_paid` (Sim2/SaysAtOPaid.lean). The end is
the rule's own.

THE PREMISES, SORTED. PUBLIC: h · hO · hb. THE MAKER: hAr. THE RUN: T · hρ · hR · hrun. WHICH OBJECTS: hP · hL.

Limits. All of the files named. No property of the protocol is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim2.ListOThin
import Johnson.Desc.ProofFile.Honest.K12.Sim2.SaysAtOPaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12.Sim2
open OnBytes (TableKey)
open VerifiableInference.Desc (Block Chain K1.qAt)
open VerifiableInference.Desc.K12 (P12)
open Desc.K14 (St blocks)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.Light ProofFile.Honest.K12.AtProof

/-- CONDITIONAL. **THE CLAUSE OF THE RULE AT THE LIST OF THE TEST ON G_omega, NO PREMISE ON VALUES.** -/
theorem onAtRun_O_paid {W₀ : Type} {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD}
    {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}
    {x₀ : VerifiableInference.Desc.First.Look.Place} {pO : P12}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF x₀) (hO : (fourOf Np).O = some pO)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (K1.qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (I : WiderIn W₀) (S' : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    {Ar : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hAr : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S' O) = .ok Ar)
    {H : Prover W₀ IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit}
    {G : Sides (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Ar.B W₀ IndexCommitterCoins TableKey Cells Unit Unit}
    (hP : G.prover H = Ar.H) {w₀ : W₀} {rc : IndexCommitterCoins} {x : ProofFile.Inst} {k : Coins Ar.B} {ρ : Draws}
    {R : Ready W₀ IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit}
    {r : RunC (P5J.F0T OnBytes.secondHashFunction Zp Np cF)}
    (T : ThreadsP (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Ar.B (G.prover H) w₀ rc x k R)
    (hρ : ρ.due (P5J.F0T OnBytes.secondHashFunction Zp Np cF) = true)
    (hR : ready (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Ar.B (G.prover H) w₀ rc x k = .ok R)
    (hrun : runC (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Ar.B (G.prover H) w₀ rc x k ρ = .ok r)
    (L : Lettered Ar.B St ProofFile.Cl Empty (Common W₀ IndexCommitterCoins TableKey) Unit TableKey)
    (hL : IsListAtO L (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] (I.weights Zp) pO)
      (simulatorJobAtOmega Zp.p.chains (K1.qAt Zp Np) (fourOf Np).U pO
        [b1, b2, b3, b4, b5, b6, b7, b8])) :
    OnAtRun₂ T ρ r L := by
  have hR' := hR
  rw [hP] at hR'
  have hrun' := hrun
  rw [hP] at hrun'
  obtain ⟨hB, hK, hf, hgO⟩ := four_at_return h hO b1 b2 b3 b4 b5 b6 b7 b8 hb I S' O hAr hR'
  refine onAtRun_O_thin h.toAtMg hO b1 b2 b3 b4 b5 b6 b7 b8 hb hB (fun x => ?_) T hρ hR hrun
    (I.weights Zp) L hL ?_ ?_ ?_
  · rw [hP]
    exact hK x
  · rw [hP]
    exact hf
  · rw [hP]
    exact hgO
  · intro m ca σ pre' t' hσ hcut hin hs hc hca hmid hfr
    have hc' : r.called ⟨pO.place, 1⟩ = true := by
      have e : L.place = pO.place := hL.place
      rw [← e]
      exact hc
    obtain ⟨m₁, hm₁, hall⟩ := saysAt_O_paid h hO b1 b2 b3 b4 b5 b6 b7 b8 hb I S' O hAr hρ hR' hrun' hc'
    have hmid' : midSharedAtW (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Ar.B Ar.H w₀ rc x k ρ ⟨pO.place, 1⟩ =
        .ok (some m) := by
      have e : L.place = pO.place := hL.place
      rw [← hP, ← e]
      exact hmid
    obtain rfl : m₁ = m := Option.some.inj (Except.ok.inj (hm₁.symm.trans hmid'))
    have hca' : carriedAt Ar.B k 1 ⟨pO.place, 1⟩
        (restPart (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] (I.weights Zp) pO) : Part Empty (Common W₀ IndexCommitterCoins TableKey) Unit).needsField = .ok ca := by
      have e : L.place = pO.place := hL.place
      rw [← e]
      exact hca
    exact hall ca hca'

/-- CONDITIONAL. **THE SAME AT A LIST THAT TAKES ITS PLACE, PARTS, On AND bud FROM A ROW OF `lotAtOmega`**: the four
equations that `Unlettered.lay` meets by its text. -/
theorem onAtRun_O_paid_at_lot {W₀ : Type} {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD}
    {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}
    {x₀ : VerifiableInference.Desc.First.Look.Place} {pO : P12}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF x₀) (hO : (fourOf Np).O = some pO)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (K1.qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (I : WiderIn W₀) (S' : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    {Ar : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hAr : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S' O) = .ok Ar)
    {H : Prover W₀ IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit}
    {G : Sides (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Ar.B W₀ IndexCommitterCoins TableKey Cells Unit Unit}
    (hP : G.prover H = Ar.H) {w₀ : W₀} {rc : IndexCommitterCoins} {x : ProofFile.Inst} {k : Coins Ar.B} {ρ : Draws}
    {R : Ready W₀ IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit}
    {r : RunC (P5J.F0T OnBytes.secondHashFunction Zp Np cF)}
    (T : ThreadsP (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Ar.B (G.prover H) w₀ rc x k R)
    (hρ : ρ.due (P5J.F0T OnBytes.secondHashFunction Zp Np cF) = true)
    (hR : ready (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Ar.B (G.prover H) w₀ rc x k = .ok R)
    (hrun : runC (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Ar.B (G.prover H) w₀ rc x k ρ = .ok r)
    (Gr : ProofFile.Ground) (row : Unlettered Empty (Common W₀ IndexCommitterCoins TableKey) Unit TableKey)
    (hrow : row ∈ (lotAtOmega I.weights).rows Zp Gr)
    (L : Lettered Ar.B St ProofFile.Cl Empty (Common W₀ IndexCommitterCoins TableKey) Unit TableKey)
    (hpl : L.place = row.place) (hr : L.row = row.row) (hOn : L.On = row.On)
    (hbud : L.bud = row.bud) :
    OnAtRun₂ T ρ r L := by
  have e := rowsAtOmega_at_head h.toAtMg hO b1 b2 b3 b4 b5 b6 b7 b8 hb (I.weights Zp)
  have hrow' : row ∈ rowsAtOmega (I.weights Zp) Zp := hrow
  rw [e] at hrow'
  obtain rfl := List.mem_singleton.1 hrow'
  exact onAtRun_O_paid h hO b1 b2 b3 b4 b5 b6 b7 b8 hb I S' O hAr hP T hρ hR hrun L
    ⟨hpl, hr, hOn, hbud⟩

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.onAtRun_O_paid_at_lot
#print axioms ProofFile.Honest.K12.Sim2.onAtRun_O_paid
