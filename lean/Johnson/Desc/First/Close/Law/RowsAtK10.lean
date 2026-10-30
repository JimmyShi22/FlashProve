-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/RowsAtK10.lean: FROM K10's LAW's END TO EVERY OPEN ITEM "row" OF THE
SEGMENT, IN ONE TERM: `k10_end_allSay` (EndRows.lean) and `rowSays_of_taken` (FillRow.lean), both
beside this file, called together. A statement and its proof.

  `k10_rows_at_table`: at a record a.1 beside a public part z: the premises of `k10_end_allSay` at
    the words that the layer's reader gives at ((z, a.1), y, w); the frame's group is the table's
    number for the segment m (hg); the promise's own `rowsHeld` and `membersHeld` at the open set O;
    `PlacesApart`; hP (a moment's samples are open only with that moment's pin): every item "row m
    c" that is open in O says what the layer `fillRow` lays: `rowSays Nu words m c (z, a.1) y w`.
Limits. It is a join: all premises of the two stand: hLaid (the tie between the typed message and
the words), hCar, hH, hPr, hl, hz, hN; hg is new: that the request's frame names the group that the
table's numbers name is shown nowhere. words is a letter (FillRowFirst.lean lays the ruled reader
in). Nothing on the pins. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.EndRows
import Johnson.Desc.First.Close.Law.FillRow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open scoped ENNReal
open OnBytes OnBytes.Slice OnBytes.Tie.Pv.Fold OnBytes.Flat OnBytes.Maker Iop IOR Prob Run KObj
open VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.BatFoldAt Cb Cb.Pv Johnson.Top.H
open VerifiableInference.Desc.Sound
open Johnson.Top.H.ArrAdd (FreeAt)
open OnBytes.PscRun (drawnOf)
open VerifiableInference.Desc.K9 (recOf putRec)
open OnBytes.Means (Words AllSay InOrder LaidOn tableSize)
open VerifiableInference.Desc (Strs)
open VerifiableInference.Desc.First (Numbers RowClass Item rowsHeld membersHeld PlacesApart rowSays
  rowSays_of_taken)

variable {S : Sig GE} (R : RowsK S) (N : SlotNames R) (keep : S.O → Prop) [DecidablePred keep]
  {B : Type} [Fintype B] (pull : (R.Sh.Cin.J → GE) → R.G.C.J → GE) (n : ℕ)
  (num : R.G.Row B ≃ Fin n)
  (fx : Fin ((R.Sh.fold (SbV R B) (slV R pull) (ZV R n num)).n + 1) × GE) {Kc St₀ Wp : Type}
  {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ ((S.sub (R.sizeB keep (SbV R B) (slV R pull) (ZV R n num)).kp).Msg × Wp))
  (bC bZ : ℕ) (w₀ : S.Wit × Wp)
  (w₁ : LdBrW R.G (R.sizeB keep (SbV R B) (slV R pull) (ZV R n num)).kp Wp)

theorem k10_rows_at_table {Pz Wt : Type}
    (L : List (BatFoldCaller GE))
    (dB dE dR : RDT)
    {Cl W : Type}
    {F : Frame}
    (Pr : Par)
    (b : Block VerifiableInference.Desc.First.S Cl)
    (base : ℕ)
    (ext : VerifiableInference.Desc.First.S × F.E.Str → Iop.Tr (uLT (ckP .two) (dB :: dE ::
      List.replicate (Yc (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀
      w₁)).k dR)) → W → W)
    (err : Err (uLT (ckP .two) (dB :: dE :: List.replicate (Yc (R.foldCaller keep (SbV R B) (slV R
      pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).k dR)))
    (fa : VerifiableInference.Desc.First.S × F.E.Str → ((kBatFoldRide L).src (R.foldCaller keep (SbV
      R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).X × ((kBatFoldRide L).src (R.foldCaller
      keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).E.Str)
    (a a' : VerifiableInference.Desc.First.S × F.E.Str)
    (hE : K10EndS R N keep pull n num fx A₀ bC bZ w₀ w₁ L dB dE dR Pr b base ext err fa a a')
    (hPr : Pr.k = R.s.h + R.s.g)
    (hH : ∀ lay, (rdK a.1).2.2.layout (rdK a.1).2.1.group = some lay → lay.h = R.s.h)
    (hI : InOrder (rdK a.1).2.2)
    (hl : ∀ lay, (rdK a.1).2.2.layout (rdK a.1).2.1.group = some lay → 2 ^ lay.logEll = R.s.C.l)
    (hz : ∀ lay, (rdK a.1).2.2.layout (rdK a.1).2.1.group = some lay → 2 ^ lay.logEllZk = R.s.Z.l)
    (hN : ∀ G, (rdK a.1).2.2.groups[(rdK a.1).2.1.group]? = some G → ∀ q x, N.orc q < (begun (rdK
      a.1).2.2 (rdK a.1).2.1.group G).oracles.size ∧ N.idx q x < tableSize (begun (rdK a.1).2.2 (rdK
      a.1).2.1.group G) (N.orc q) .main)
    (hCar : CarriedAt R N keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁ L (fa a) (rdBK
      a'.1).1.rows)
    (r : R.G.C.Q → GE) (Nu : Numbers)
    (words : Pz × VerifiableInference.Desc.First.S → Strs → Wt → Words GE) (z : Pz) (y : Strs)
    (w : Wt)
    (hLaid : ∀ μ : S.Msg, (∀ i, S.decs (fa a).1.2 (fa a).2.1.2 i = some (μ i)) → ∀ G lay, (rdK
      a.1).2.2.groups[(rdK a.1).2.1.group]? = some G → (begun (rdK a.1).2.2 (rdK a.1).2.1.group
      G).layout (rdK a.1).2.1.group = some lay → LaidOn (begun (rdK a.1).2.2 (rdK a.1).2.1.group G)
      lay (words (z, a.1) y w) (tabK N (R.Sh.rho.up (R.G.msg μ, r)).1))
    (m : ℕ) (hg : (rdK a.1).2.1.group = Nu.groupAt m) (O : List Item) (hR : rowsHeld Nu O a.1 =
        true)
    (hM : membersHeld Nu O a.1 = true) (hA : PlacesApart a.1)
    (hP : ∀ t, Item.row m (.sample t) ∈ O → t < 3 ∧ Item.pin m t ∈ O) :
    ∀ c, Item.row m c ∈ O → rowSays Nu words m c (z, a.1) y w := by
  obtain ⟨G, hG, hall⟩ :=
    k10_end_allSay R N keep pull n num fx A₀ bC bZ w₀ w₁ L dB dE dR Pr b base ext err fa a a' hE hPr
      hH hI hl hz hN hCar r (words (z, a.1) y w) hLaid
  rw [hg] at hG
  exact rowSays_of_taken Nu words O (z, a.1) y w hR hM hA m G hG hP hall

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.k10_rows_at_table
