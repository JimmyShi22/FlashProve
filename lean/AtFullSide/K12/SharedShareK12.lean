-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: K12's share of the shared chain, in the field's own text.
/-
AtFullSide/K12/SharedShareK12.lean: CONDITIONAL: A CONDITIONAL WITH NO KNOWN MEMBER.

Can the hypotheses be met together at a real run? NOT KNOWN: a value of `ThreadsP`, ready's and runC's return and
that a part is called have no term known to us. hrows: index privacy's kOurs seats both rows in its shared list,
by its letter (a trial; not called here).

What is here. K12's share of the rule's field on₂ (`KindOnAtRun`, Honest/Law/UseByKind.lean) and of bud₂'s
(`KindBud`, Johnson/M1/BudGather.lean) at the shared chain, at the maker's return at the matrices and at an
instance written of a sample, under the crossing's one equation hrc, from ONE PREMISE ON G, hrows: every list of the
kind K12 in G.shared takes its place, parts, On and bud from a row of the lot at G_u or at G_omega. `Unlettered.lay`
meets the four equations by its text, so `Letters.ofThreads` does.

  `K12RowAt`   what hrows asks of one list.
  `k12_on₂_at_base`   on₂.
  `k12_bud₂_at_base`   bud₂'s shared clause.

Limits. All of the files beneath: AtFullSide/K12/OnAtRunUAtLot.lean's, Sim2/ListOPaid.lean's and
Sim2/ListOAtReturn.lean's: at the base term, not the online prover. No property is claimed.
-/
import AtFullSide.K12.OnAtRunUAtLot
import Johnson.Desc.ProofFile.Honest.K12.Sim2.ListOPaid
import Johnson.Desc.ProofFile.Honest.K12.Sim2.BudAtOGuarded

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtFullSide.K12
open OnBytes (E TableKey)
open OnBytes.Slice (frS)
open VerifiableInference.Desc (Block Chain KindName)
open VerifiableInference.Desc (K1.qAt)
open VerifiableInference.Desc.First (S)
open Desc.K14 (St blocks)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.Light ProofFile.Honest.K12.AtProof ProofFile.Honest.K12.Sim2
open ProofFile.Honest.Term (matrixInput)
open AtPublicFiles.AtFiles (FullSizeMatrix protocolAtFiles)
open LPFD.Full (XF instanceAsPlainRecord)

/-- **One list of the kind K12 at the shared chain takes its four fields from a row of the lot at G_u or at G_omega.** -/
def K12RowAt {Bk : ProverCoinCounts} {St' Cl' : Type} (Zp : ProofFile.Pub) (Gd : ProofFile.Ground)
    (L : Lettered Bk St' Cl' Empty (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit TableKey) : Prop :=
  ∃ row : Unlettered Empty (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit TableKey,
    (row ∈ (lotU Face.shared matrixInput.weights
        (fun Zq w => Bind.ForProver.encW Zq (matrixInput.weights Zq w))).rows Zp Gd ∨
      row ∈ (lotAtOmega matrixInput.weights).rows Zp Gd) ∧
    L.place = row.place ∧ L.row = row.row ∧ L.On = row.On ∧ L.bud = row.bud

/-- CONDITIONAL: see the head. **K12's SHARE OF on₂.** -/
theorem k12_on₂_at_base {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD}
    {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain S ProofFile.Cl}
    {x₀ : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF x₀)
    (S' : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    {Ar : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
    (hAr : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL
      (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction S' O) = .ok Ar)
    {H : Prover FullSizeMatrix IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit}
    {G : Sides (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Ar.B FullSizeMatrix IndexCommitterCoins TableKey Cells Unit Unit}
    (hP : G.prover H = Ar.H) {M : FullSizeMatrix} {rc : IndexCommitterCoins}
    (online : (protocolAtFiles Z).EncodingRandomness) (seed : (protocolAtFiles Z).OutOfDomainSeed) (request : XF)
    (hrc : rc = ProofFile.Honest.randOf (S := frS) (cut := 402653181) online)
    {k : Coins Ar.B} {ρ : Draws}
    {R : Ready FullSizeMatrix IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit}
    {r : RunC (P5J.F0T OnBytes.secondHashFunction Zp Np cF)}
    (T : ThreadsP (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Ar.B (G.prover H) M rc
      (instanceAsPlainRecord (request, (protocolAtFiles Z).recOf M online seed)) k R)
    (hρ : ρ.due (P5J.F0T OnBytes.secondHashFunction Zp Np cF) = true)
    (hR : ready (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Ar.B (G.prover H) M rc
      (instanceAsPlainRecord (request, (protocolAtFiles Z).recOf M online seed)) k = .ok R)
    (hrun : runC (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Ar.B (G.prover H) M rc
      (instanceAsPlainRecord (request, (protocolAtFiles Z).recOf M online seed)) k ρ = .ok r)
    (Gd : ProofFile.Ground)
    (hrows : ∀ L ∈ G.shared, L.place.kind = KindName.K12 → K12RowAt Zp Gd L) :
    ∀ L ∈ G.shared, L.place.kind = KindName.K12 → OnAtRun₂ (G := G) (H := H) T ρ r L := by
  intro L hL hk
  obtain ⟨row, hrow, hpl, hr, hOn, hbud⟩ := hrows L hL hk
  rcases hrow with hrow | hrow
  · exact onAtRun_U_at_lot_at_the_written_instance h S' O hAr hP online seed request hrc T hρ hR hrun Gd
      row hrow L hpl hr hOn hbud
  · obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, hb⟩ := eight_head h.toAtMg
    obtain ⟨pO, hO⟩ := ProofFile.Honest.K12.AtProof.someO_at_head h.toAtMg
    exact onAtRun_O_paid_at_lot h hO b1 b2 b3 b4 b5 b6 b7 b8 hb matrixInput S' O hAr hP T hρ hR hrun Gd
      row hrow L hpl hr hOn hbud

/-- CONDITIONAL: see the head. **K12's SHARE OF bud₂.** -/
theorem k12_bud₂_at_base {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD}
    {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain S ProofFile.Cl}
    (h : P5J.AtMg OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF) {Bk : ProverCoinCounts}
    {G : Sides (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk FullSizeMatrix IndexCommitterCoins TableKey Cells Unit Unit}
    (Gd : ProofFile.Ground)
    (hrows : ∀ L ∈ G.shared, L.place.kind = KindName.K12 → K12RowAt Zp Gd L) :
    ∀ L ∈ G.shared, L.place.kind = KindName.K12 → Johnson.M1.BudOwed₂ (P5J.F0T OnBytes.secondHashFunction Zp Np cF) L := by
  intro L hL hk
  obtain ⟨row, hrow, hpl, hr, hOn, hbud⟩ := hrows L hL hk
  rcases hrow with hrow | hrow
  · exact rowU_owes h _ _ _ Gd row hrow L hpl hr hbud
  · obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, hb⟩ := eight_head h
    obtain ⟨pO, hO⟩ := ProofFile.Honest.K12.AtProof.someO_at_head h
    exact budOwed₂_at_lot h hO b1 b2 b3 b4 b5 b6 b7 b8 hb matrixInput.weights Gd row hrow L hpl hr hOn hbud

end AtFullSide.K12

#print axioms AtFullSide.K12.k12_on₂_at_base
#print axioms AtFullSide.K12.k12_bud₂_at_base
