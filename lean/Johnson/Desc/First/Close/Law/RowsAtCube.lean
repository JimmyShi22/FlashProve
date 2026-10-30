-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/RowsAtCube.lean: FROM K10's LAW's END TO EVERY OPEN ITEM "row" OF THE
SEGMENT, WITH THE TIE BETWEEN THE TYPED MESSAGE AND THE WORDS IN ITS PARTS: RowsAtK10.lean's join
with `laidOn_of_cube` (CubeAt.lean) in hLaid's place. All beside this file. A statement and its
proof.

  `k10_rows_at_cube`: from the law's end `K10EndS` between a and a'; `CarriedAt` behind; "the
    statement in front is in order"; `R.Good`; hPr (the place's k is the stage's: on letters); a
    numbering no of the typed group's members with `CubeFits` and `NamesFit` at the begun statement
    and the layout (hC: public ties); `WordsAre` at the decoded messages and the words that the
    layer's reader gives at ((z, a.1), y, w) (hW); the slots' names within the tables (hN); the
    frame's group is the table's number (hgr); the promise's `rowsHeld`, `membersHeld`;
    `PlacesApart`; hP: every item "row m c" that is open in O says what the layer `fillRow` lays.
    What turns against `k10_rows_at_table`: NO PREMISE IS DISCHARGED; THEY ARE MOVED AND PARTED:
    hLaid is parted into hC, hW and `R.Good`; hH, hl, hz (three of the layout's four numbers) now
    stand as fields of `CubeFits` inside hC. hPr STAYS AS IT WAS: a premise on LETTERS: the layout's
    k is drawn from the yes that the law's end holds (`closeFrame_k`, `closeFrame_kh`), as in
    EndRows.lean. Also drawn here: that the group and its layout are there (the same yes); the facts
    that every layout has: from "in order" (`layFacts`).
Limits. A join: hC, hW, hN, hCar, hgr, `PlacesApart`, hP are premises, shown of nothing here.
`WordsAre` speaks of rows behind the group's view (CubeAt.lean's Limit (1)). words is a letter.
Nothing on the pins. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.RowsAtK10
import Johnson.Desc.First.Close.Law.CubeAt
import Johnson.Desc.First.Close.Law.OnOfOrder

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
open OnBytes.Means (Words AllSay InOrder LaidOn tableSize layFacts)
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

theorem k10_rows_at_cube {Pz Wt : Type}
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
    (hPr : Pr.k = R.s.h + R.s.g) (hI : InOrder (rdK a.1).2.2) (hg : R.Good)
    (no : R.G.A → ℕ)
    (hC : ∀ G lay, (rdK a.1).2.2.groups[(rdK a.1).2.1.group]? = some G → (begun (rdK a.1).2.2 (rdK
      a.1).2.1.group G).layout (rdK a.1).2.1.group = some lay → CubeFits R (begun (rdK a.1).2.2 (rdK
      a.1).2.1.group G) lay no ∧ NamesFit R N (begun (rdK a.1).2.2 (rdK a.1).2.1.group G) lay no)
    (hN : ∀ G, (rdK a.1).2.2.groups[(rdK a.1).2.1.group]? = some G → ∀ q x, N.orc q < (begun (rdK
      a.1).2.2 (rdK a.1).2.1.group G).oracles.size ∧ N.idx q x < tableSize (begun (rdK a.1).2.2 (rdK
      a.1).2.1.group G) (N.orc q) .main)
    (hCar : CarriedAt R N keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁ L (fa a) (rdBK
      a'.1).1.rows)
    (r : R.G.C.Q → GE) (Nu : Numbers)
    (words : Pz × VerifiableInference.Desc.First.S → Strs → Wt → Words GE) (z : Pz) (y : Strs)
    (w : Wt)
    (hW : ∀ μ : S.Msg, (∀ i, S.decs (fa a).1.2 (fa a).2.1.2 i = some (μ i)) → ∀ G, (rdK
      a.1).2.2.groups[(rdK a.1).2.1.group]? = some G → WordsAre R (begun (rdK a.1).2.2 (rdK
      a.1).2.1.group G) no (R.G.msg μ, r) (words (z, a.1) y w))
    (m : ℕ) (hgr : (rdK a.1).2.1.group = Nu.groupAt m) (O : List Item) (hR : rowsHeld Nu O a.1 =
        true)
    (hM : membersHeld Nu O a.1 = true) (hA : PlacesApart a.1)
    (hP : ∀ t, Item.row m (.sample t) ∈ O → t < 3 ∧ Item.pin m t ∈ O) :
    ∀ c, Item.row m c ∈ O → rowSays Nu words m c (z, a.1) y w := by
  obtain ⟨⟨τ, -, -, hcf⟩, -, -, -, hlast⟩ := hE
  obtain ⟨Gf, G, lay, hGf, hG, -, hLb, ek, -⟩ := closeFrame_kh hcf
  obtain ⟨Gf', hGf', ek'⟩ := closeFrame_k hcf
  obtain rfl : Gf = Gf' := Option.some.inj (hGf.symm.trans hGf')
  have hLk : lay.k = R.s.h + R.s.g := ek.trans (ek'.trans hPr)
  obtain ⟨⟨μ, hμ⟩, hall⟩ := hlast hCar
  obtain ⟨C, Fn⟩ := hC G lay hG hLb
  have hG' := begun_at _ G hG
  have Y := layFacts hG' hLb ((hI.begun _ G hG).groups _ _ hG')
  have hsay := allSay_of_rowVec N _ hI _ G hG lay hLb hLk C.h C.el C.ez (hN G hG) _
    (words (z, a.1) y w) (laidOn_of_cube R N hg Y hLk C Fn _ _ (hW μ hμ G hG))
    fun i hi => hall μ hμ G lay hG hLb r i hi
  rw [hgr] at hG
  exact rowSays_of_taken Nu words O (z, a.1) y w hR hM hA m G hG hP hsay

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.k10_rows_at_cube
