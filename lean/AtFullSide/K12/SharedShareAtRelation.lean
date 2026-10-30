-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: K12's share of the shared chain at the relation of T3's row.
/-
AtFullSide/K12/SharedShareAtRelation.lean: CONDITIONAL: A CONDITIONAL WITH NO KNOWN MEMBER.

What is here. `k12_on₂_at_base` (AtFullSide/K12/SharedShareK12.lean) in the prefix of part 4's `KindOnAtEveryRun`, at the
relation that Johnson/T3/TheOneTheorem.lean's debts take, written out: imageRel id (tableCoins Z) (relAt …), at any Ry
in relAt's second place, at any description equal to the head's. T is a letter: the end holds at every value.

  `rec_gen`   the object's sample is the seed with `ansAt`'s answers.
  `k12_on₂_at_relation`   the statement.
  `k12_onAt₂_at_relation`   the same at the prover A.H, at `OnAtRunAt₂`: the socket's form. Under the ring.

Limits. All of AtFullSide/K12/SharedShareK12.lean's. The crossing to the online prover is T3's law, not here
(Johnson/T3/OnlineThru.lean, owed_of_base). No property is claimed.
-/
import AtFullSide.K12.SharedShareK12
import AtFullSide.Honest.InstanceTie
import Johnson.T3.ThreadsAtRing

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtFullSide.K12
open OnBytes (TableKey)
open VerifiableInference.Desc (Block Chain KindName FileDescription)
open VerifiableInference.Desc.First (S)
open Desc.K14 (St)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.Light ProofFile.Honest.K12.AtProof ProofFile.Honest.K12.Sim2
open ProofFile.Honest.Term (matrixInput tableCoins)
open AtPublicFiles.AtFiles AtPublicFiles.Committed AtPublicFiles.Bridge AtPublicFiles.Along
open VerifierAndGoals VerifierAndGoals.Fit FlashProve FlashProve
open LPFD.Full (XF instanceAsPlainRecord)

attribute [local irreducible] theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF LPFD.Full.mOneAt PV.EncId.encF
  PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8 FlashProve.thePlan FlashProve.theItem riDigits fieldRows

local instance (priority := high) padAtRelation : Nonempty PadZ :=
  pads_nonempty OnBytes.Slice.frS 402653181

/-- **The object's sample is the seed with the answers**, at any configuration: by unfolding. -/
theorem rec_gen {C : _} (F : OnBytes.Flat.Files C) (P : F.Provers) (i : C.I) (r : C.Pad × C.Rnd) (s : C.Seed) :
    (F.withProvers P).recOf i r s = (s, ansC C i r s) := rfl

set_option maxHeartbeats 4000000 in
/-- CONDITIONAL: see the head. **K12's SHARE OF on₂ IN THE PREFIX OF `KindOnAtEveryRun`.** -/
theorem k12_on₂_at_relation {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD}
    {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain S ProofFile.Cl}
    {x₀ : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF x₀)
    (S' : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    {Ar : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
    (hAr : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL
      (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction S' O) = .ok Ar)
    (F : FileDescription ProofFile.Inst) (eF : F = P5J.F0T OnBytes.secondHashFunction Zp Np cF)
    {G : Sides F Ar.B FullSizeMatrix IndexCommitterCoins TableKey Cells Unit Unit} (hP : G.prover Ar.H = Ar.H)
    (Gd : ProofFile.Ground)
    (hrows : ∀ L ∈ G.shared, L.place.kind = KindName.K12 → K12RowAt Zp Gd L)
    (Ry : FullSizeMatrix → XF → Prop) :
    ∀ w₀ rc x, (∃ w rc', ProofFile.Honest.relAt (ansAt (AZ Z) PadZ (holdZ Z)) Ry instanceAsPlainRecord w rc' x ∧
        id w = w₀ ∧ tableCoins Z rc' = rc) →
      ∀ k R (_ : ready F Ar.B (G.prover Ar.H) w₀ rc x k = .ok R)
        (T : ThreadsP F Ar.B (G.prover Ar.H) w₀ rc x k R) (ρ : Draws) (r : RunC F),
        ρ.due F = true → runC F Ar.B (G.prover Ar.H) w₀ rc x k ρ = .ok r →
        ∀ L ∈ G.shared, L.place.kind = KindName.K12 → OnAtRun₂ (G := G) (H := Ar.H) T ρ r L := by
  subst eF
  rintro w₀ rc x ⟨w, rc', ⟨s, x', hx, -⟩, rfl, rfl⟩ k R hR T ρ r hρ hrun
  have hx' : x = instanceAsPlainRecord (x', (protocolAtFiles Z).recOf w rc' s) := by
    have e1 : (protocolAtFiles Z).recOf w rc' s = (s, ansC (Cz Z) w rc' s) :=
      rec_gen (filesAt Z) (dataAtFiles flashProveData Z).P w rc' s
    have e2 : ansAt (AZ Z) PadZ (holdZ Z) = ansC (Cz Z) := ansAt_eq (AZ Z) PadZ (holdZ Z)
    rw [e1, ← e2]
    exact hx
  subst hx'
  exact k12_on₂_at_base h S' O hAr hP rc' s x' rfl T hρ hR hrun Gd hrows

set_option maxHeartbeats 4000000 in
/-- CONDITIONAL: see the head. **THE SAME IN THE SOCKET's OWN FORM** (`threads_of_named`'s field named, Johnson/T3/ThreadsAtRing.lean):
at the prover A.H, at a value T of `ThreadsP` there, `OnAtRunAt₂` at T's invariants. T is a letter. -/
theorem k12_onAt₂_at_relation {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD}
    {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain S ProofFile.Cl}
    {x₀ : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF x₀)
    (S' : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    {Ar : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
    (hAr : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL
      (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction S' O) = .ok Ar)
    (F : FileDescription ProofFile.Inst) (eF : F = P5J.F0T OnBytes.secondHashFunction Zp Np cF)
    {G : Sides F Ar.B FullSizeMatrix IndexCommitterCoins TableKey Cells Unit Unit} (hP : G.prover Ar.H = Ar.H)
    (Gd : ProofFile.Ground)
    (hrows : ∀ L ∈ G.shared, L.place.kind = KindName.K12 → K12RowAt Zp Gd L)
    (Ry : FullSizeMatrix → XF → Prop) :
    ∀ w₀ rc x, (∃ w rc', ProofFile.Honest.relAt (ansAt (AZ Z) PadZ (holdZ Z)) Ry instanceAsPlainRecord w rc' x ∧
        id w = w₀ ∧ tableCoins Z rc' = rc) →
      ∀ k R (_ : ready F Ar.B Ar.H w₀ rc x k = .ok R)
        (T : ThreadsP F Ar.B Ar.H w₀ rc x k R) (ρ : Draws) (r : RunC F),
        ρ.due F = true → runC F Ar.B Ar.H w₀ rc x k ρ = .ok r →
        ∀ L ∈ G.shared, L.place.kind = KindName.K12 →
          OnAtRunAt₂ G Ar.H w₀ rc x k T.I₂ ρ r L := by
  intro w₀ rc x hrel k R hR T ρ r hρ hrun L hL hk
  have hR' : ready F Ar.B (G.prover Ar.H) w₀ rc x k = .ok R := by
    rw [hP]
    exact hR
  have hrun' : runC F Ar.B (G.prover Ar.H) w₀ rc x k ρ = .ok r := by
    rw [hP]
    exact hrun
  have a : OnAtRunAt₂ G Ar.H w₀ rc x k (ThreadsP.ofEq hP.symm T).I₂ ρ r L :=
    k12_on₂_at_relation h S' O hAr F eF hP Gd hrows Ry w₀ rc x hrel k R hR'
      (ThreadsP.ofEq hP.symm T) ρ r hρ hrun' L hL hk
  rw [ThreadsP.ofEq_I₂] at a
  exact a

end AtFullSide.K12

#print axioms AtFullSide.K12.k12_onAt₂_at_relation
#print axioms AtFullSide.K12.rec_gen
#print axioms AtFullSide.K12.k12_on₂_at_relation
