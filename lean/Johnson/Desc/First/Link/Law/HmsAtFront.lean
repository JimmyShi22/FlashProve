-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/HmsAtFront.lean: "THE SYMBOLS' ARRAYS HAVE THE ROWS THAT THEIR SIZES
ASK" (the field hmS of `EqTake`, ExpsAt.lean, and of `NumbersOk`) AT WHAT IS FIXED AT
EVERY STATE REACHED IN FRONT OF EVERY ONE OF THE 25 BATCHINGS, FROM TWO CLOSED SENTENCES ON THE
BUILT SEGMENT. In the goals' scope. One definition, statements and proofs: a carrying.

  `MsPlan tl`: THE CLOSED SENTENCE: each matrix's shape has a third of the MATRIX's rows of cells,
    rounded up, as its rows of symbols: the letters of `addTreesF_mS`
    (Johnson/Road/K4/Plan/ShapeRows.lean: where the routine that lays the arrays returns; not
    imported here).
  `hmS_of`: `MsPlan tlP`; `Fits tlP` (the shapes' rows of cells are the matrices'); a structure with
    tlP's four planned readings (`rowsRead`) ⊢ the field's body: (shp.getD mu {}).mS = Alg.symRows
    (shp.getD mu {}).m at mu < NM.
  `hmS_at`: **reached at the batching's front of a written stretch; Xl the built segment; MsPlan
    Xl.tl; Fits Xl.tl ⊢ the field at fixed9 (phiAll u ψ) s'.**
Limits. `MsPlan Xl.tl` AND `Fits Xl.tl` ARE PREMISES: that the built segment's structure is a return
of that routine is said for no sort here. No soundness statement.
-/
import Johnson.Desc.First.Link.Law.RowsNumberAtBatch
import Johnson.Desc.First.Link.Law.OkAtBatch
import Johnson.Desc.First.Link.Law.PhiAll
import Johnson.Desc.First.Link.Law.PayLayers

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open OnBytes.Tie.Pv.Tail.Port (Fits)
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.TailClaims.Law (blank)
open VerifiableInference.Desc.PhiAll
open Johnson.Desc.First.Walk.Tied (Reach)

/-- **THE CLOSED SENTENCE.** -/
def MsPlan (tl : HTailF2) : Prop :=
  ∀ mu, mu < tl.NM → (tl.shp.getD mu {}).mS = ((tl.mats.getD mu {}).m + 2) / 3

/-- The field's body. -/
theorem hmS_of {tlP tlb : HTailF2} (M : MsPlan tlP) (Ft : Fits tlP)
    (h : rowsRead tlb = rowsRead tlP) :
    ∀ mu, mu < tlb.NM → (tlb.shp.getD mu {}).mS = Alg.symRows (tlb.shp.getD mu {}).m := by
  have h1 : tlb.NM = tlP.NM := congrArg (·.1) h
  have h4 : tlb.shp = tlP.shp := congrArg (·.2.2.2) h
  intro mu hmu
  rw [h1] at hmu
  rw [h4, M mu hmu, (Ft mu hmu).1]
  rfl

variable {β : Type} {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray}
  {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
  {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **THE FIELD, AT ALL 25.** -/
theorem hmS_at (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B)
    {x : ℕ × ℕ × ℕ} (hx : x ∈ P1K8S.stretches) {Xl : LinkH}
    (e3 : Bs.G₀.built[x.1]? = some Xl) {z : ProofFile.InstPub} {s' : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * x.1 + x.2.1 + 3 + x.2.2) (z, s'))
    (M : MsPlan Xl.tl) (Ft : Fits Xl.tl) (u : HTailF2) (ψ : S → β) :
    ∀ tlb, (pi8 (fixed9 (phiAll u ψ) s').1).1 = some tlb → ∀ mu, mu < tlb.NM →
      (tlb.shp.getD mu {}).mS = Alg.symRows (tlb.shp.getD mu {}).m := by
  have hr := of_readTl (planned_at_batch planned_rows hS hR O hx e3 (z, s') h)
  intro tlb e1
  obtain ⟨tl, htl, rfl⟩ := Option.map_eq_some_iff.1
    (show s'.tl?.map (blank u) = some tlb from e1)
  exact hmS_of M Ft (show rowsRead (blank u tl) = rowsRead Xl.tl from hr tl htl)

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.hmS_of
#print axioms VerifiableInference.Desc.LinkJoin.hmS_at
