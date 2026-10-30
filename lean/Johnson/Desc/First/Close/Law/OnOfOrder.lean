-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/OnOfOrder.lean: TWO CLAUSES OF K10's PROMISE FOLLOW FROM "THE STATEMENT
IS IN ORDER". A definition, statements and proofs.

K10's promise (`K10On`, OnK10.lean; `K10OnS`, AtBlockSelf.lean, beside this file) asks of every row
that the closing's test takes in: it fits (`RowFits`), and its structured vectors on mask tables
reach over all places of the group (`MaskFits`): both at the begun statement. The library's
`OnBytes.Means.InOrder` (Johnson/Desc/Means/Order.lean: every group is in order; every open row has
passed the tests of the adding at its group; every sample row is on its own message) gives both.
  `rowFits_of_inOrder`: by `InOrder.runRows`, `RowIn.extends` over `extends_begun`, `RowIn.fits`.
  `begunGroup`, `begun_at`: the group as the beginning of its test leaves it. `maskFits_of_inOrder`:
    by the same, `InOrder.begun`, `layFacts`, `RowIn.maskFits`.
  `k10OnS_of_order`: so K10's promise follows from: the two equations of numbers on the record;
    front; tied; code; the stage's mask length is at most the layout's number of mask places (zl);
    and `InOrder` of the record's statement.
Limits. That a record's statement is in order is a premise: who fills the table's "in order" owes it
at every border. zl, the first half of the clause masks, is left: a comparison of two public
numbers. Nothing is said of front, tied, code. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.AtBlockSelf
import Johnson.Desc.Means.Holds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Slice OnBytes.Means

/-- **Every row that the test takes in fits, at the begun statement**, at a statement in order. -/
theorem rowFits_of_inOrder {T : Statement} (hI : InOrder T) (g : ℕ) (G : Group)
    (hG : T.groups[g]? = some G) :
    ∀ w ∈ (runRows T G).toList, RowFits (begun T g G) w := fun w hw =>
  ((hI.runRows g G hG w hw).extends (extends_begun T g G) (G' := G) fun _ h => h).fits

/-- The group as the beginning of its test leaves it: its open rows are taken, it is marked. -/
def begunGroup (G : Group) : Group :=
  { code := G.code, maskCode := G.maskCode, members := G.members, kept := G.kept, inRun := true }

theorem begun_at {T : Statement} (g : ℕ) (G : Group) (hG : T.groups[g]? = some G) :
    (begun T g G).groups[g]? = some (begunGroup G) := by
  rw [begun_groups, Array.getElem?_modify, if_pos rfl, hG]
  rfl

/-- **Its structured vectors on mask tables reach over all places of the group**, at the begun
statement's layout. -/
theorem maskFits_of_inOrder {T : Statement} (hI : InOrder T) (g : ℕ) (G : Group)
    (hG : T.groups[g]? = some G) (lay : GroupLayout) (hL : (begun T g G).layout g = some lay) :
    ∀ w ∈ (runRows T G).toList, MaskFits (begun T g G) lay w := by
  intro w hw
  have hG' := begun_at g G hG
  have hOk := (hI.begun g G hG).groups g _ hG'
  exact (RowIn.extends (G := G) (G' := begunGroup G) (extends_begun T g G) (fun _ h => h)
    (hI.runRows g G hG w hw)).maskFits (layFacts hG' hL hOk)

section
open scoped ENNReal
open OnBytes.Tie.Pv.Fold OnBytes.Flat OnBytes.Maker Iop IOR Prob Run KObj
open VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.BatFoldAt Cb Cb.Pv Johnson.Top.H
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K9 (recOf putRec)

variable {S : Sig GE} (R : RowsK S) (N : SlotNames R) (keep : S.O → Prop) [DecidablePred keep]
  {B : Type} [Fintype B] (pull : (R.Sh.Cin.J → GE) → R.G.C.J → GE) (n : ℕ)
  (num : R.G.Row B ≃ Fin n)
  (fx : Fin ((R.Sh.fold (SbV R B) (slV R pull) (ZV R n num)).n + 1) × GE) {Kc St₀ Wp : Type}
  {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ ((S.sub (R.sizeB keep (SbV R B) (slV R pull) (ZV R n num)).kp).Msg × Wp))
  (bC bZ : ℕ) (w₀ : S.Wit × Wp)
  (w₁ : LdBrW R.G (R.sizeB keep (SbV R B) (slV R pull) (ZV R n num)).kp Wp)

/-- **K10's promise from "the statement is in order"**: `k10OnS_of` with `K10On`'s clause rows and
    the
second half of its clause masks paid by `Means.InOrder` of the record's statement. -/
theorem k10OnS_of_order (L : List (BatFoldCaller GE))
    (pS : ∀ as : (Σ a : R.G.A, (S.om a.1).Z.S), (S.om as.1.1).Z.D → R.Sh.Cin.J → GE)
    (Pr : Par) {F : Frame}
    (fa : VerifiableInference.Desc.First.S × F.E.Str → ((kBatFoldRide L).src (R.foldCaller keep (SbV
      R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).X × ((kBatFoldRide L).src (R.foldCaller
      keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).E.Str)
    (a : VerifiableInference.Desc.First.S × F.E.Str)
    (hk : (planOf (entries Pr) (rdK a.1)).k = R.s.h + R.s.g)
    (hh : (planOf (entries Pr) (rdK a.1)).h = R.s.h)
    (front : ((Cb.Pv.Bat.inJ (R.sizeB keep (SbV R B) (slV R pull) (ZV R n num)) A₀).keepE
      R.Sh.par.Cw.nat).on (fa a))
    (tied : ∀ G lay, (rdK a.1).2.2.groups[(rdK a.1).2.1.group]? = some G → (begun (rdK a.1).2.2 (rdK
      a.1).2.1.group G).layout (rdK a.1).2.1.group = some lay → RowsTied R n num N pS (fa a).1.1.1
      (fa a).1.2 (begun (rdK a.1).2.2 (rdK a.1).2.1.group G) lay (runRows (rdK a.1).2.2 G).toList)
    (zl : ∀ G lay, (rdK a.1).2.2.groups[(rdK a.1).2.1.group]? = some G → (begun (rdK a.1).2.2 (rdK
      a.1).2.1.group G).layout (rdK a.1).2.1.group = some lay → R.s.Z.l ≤ 2 ^ lay.logEllZk)
    (hI : InOrder (rdK a.1).2.2)
    (code : ((rdK a.1).2.2.codes.mask.getD (planOf (entries Pr) (rdK a.1)).maskCode default).ell =
      R.s.Z.l) :
    K10OnS R N keep pull n num fx A₀ bC bZ w₀ w₁ L pS Pr fa a :=
  k10OnS_of R N keep pull n num fx A₀ bC bZ w₀ w₁ L pS Pr fa a hk hh front tied
    (fun G lay hG hL => ⟨zl G lay hG hL, maskFits_of_inOrder hI _ G hG lay hL⟩)
    (fun G hG => rowFits_of_inOrder hI _ G hG) code

end

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.rowFits_of_inOrder
#print axioms VerifiableInference.Desc.First.Close.maskFits_of_inOrder
#print axioms VerifiableInference.Desc.First.Close.k10OnS_of_order
