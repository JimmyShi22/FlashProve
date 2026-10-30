-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Tables/TablesLen.lean: THE FIELDS len₁ AND len₂ OF `TablesFitR`
(Johnson/P5J/TopTablesR.lean), PAID AT THE SEATED DESCRIPTION's OWN TERM. ONE TEXT:
that three rows of pieces are as long as a description's three flat lists, and the field len₃, are
other files' (`ToldDesc.len₁_of_ofDesc`, `len₂_of_ofDesc`, `third_length`,
Johnson/ToldDescR/LengthsAtTable.lean): called here, not typed here. Each field says: one more
than a row's rest of pieces is the number of places of that chain's table. They are shown at EVERY
three rows of pieces T that hold the description's own sub-protocols (`OfDesc (F0T o Zp Np cF) T`):
the tower's T := piecesAt … is one, by `AtMg.ofDesc`. Three theorems: calls; no
evaluation.

  `first_flat_length`: the first chain has `At.ps.length` sub-protocols: in the goals' scope, from
    `LaidAt` at `OnBytes.secondHashFunction`: by `LPFK9.blockPlaces_full`.
  `len₁_of` : 1 + T.l₁.length = At.ps.length · in scope, the files read, `LaidAt` at secondHashFunction.
  `len₂_of` : 1 + T.l₂.length = (sharedPlaces true).length · in scope, `LaidAt` at any o.

Limits. Nothing on soundness. len₂ IS PAID AT split := true ALONE: at split := false the field is
false in scope (11 places against 12 sub-protocols): whoever fills the tower's free letters lays
split := true. len₁ at `OnBytes.secondHashFunction` alone. That `LaidAt` can be met is shown by no theorem.

-/
import Johnson.Road.Tables.FlatLengths
import Johnson.LPFK9R.SubsFull
import Johnson.ToldDescR.LengthsAtTable

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.Tables
open VerifiableInference.Desc (FileDescription)
open VerifiableInference.Desc.Sound (OfDesc ThreeAt)
open VerifiableInference.Desc.Shared (sharedPlaces)
open OnBytes.Maker (WholeD)
open P5J (F0T LaidAt TS)

variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain TS ProofFile.Cl}

/-- **The first chain has as many sub-protocols as its table has places.** -/
theorem first_flat_length (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) :
    (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.length = P5J.At.ps.length := by
  obtain ⟨Bs, base, O⟩ := L.opened
  exact first_flat_of_places (LPFK9.blockPlaces_full hZ hR O)

variable {C : _root_.Run.PQ.CK} {D' : WholeD} {all : List OnBytes.Maker.LeftT} {X₁ X₂ W : Type}

/-- **len₁.** -/
theorem len₁_of (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    {T : ThreeAt C D' all (F0T OnBytes.secondHashFunction Zp Np cF) X₁ X₂ W}
    (h : OfDesc (F0T OnBytes.secondHashFunction Zp Np cF) T) : 1 + T.l₁.length = P5J.At.ps.length :=
  (ToldDesc.len₁_of_ofDesc h).trans (first_flat_length hZ hR L)

/-- **len₂, at split := true.** -/
theorem len₂_of {o : ProofFile.SecondHashFunctionArgument} (hZ : VerifierAndGoals.InScope Z = true)
    (L : LaidAt o Z.pol Z.lay Z.KL D r Zp Np cF) {T : ThreeAt C D' all (F0T o Zp Np cF) X₁ X₂ W}
    (h : OfDesc (F0T o Zp Np cF) T) : 1 + T.l₂.length = (sharedPlaces true).length :=
  (ToldDesc.len₂_of_ofDesc h).trans (shared_flat_length hZ L)

end OnBytes.Road.Tables

#print axioms OnBytes.Road.Tables.first_flat_length
#print axioms OnBytes.Road.Tables.len₁_of
#print axioms OnBytes.Road.Tables.len₂_of
