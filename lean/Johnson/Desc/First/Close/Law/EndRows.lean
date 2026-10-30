-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/EndRows.lean: K10's LAW's END GIVES WHAT THE TABLE's ITEM "row" ASKS OF
A CLOSER: THE JOIN of `K10EndS` (GoodOf.lean), `allSay_of_rowVec` (EndSays.lean) and `closeFrame_k`,
`closeFrame_kh` (KOfYes.lean), all beside this file. A statement and its proof.

  `k10_end_allSay`: from the law's end between a and a'; the sentence `CarriedAt` on the statement
    behind; "the statement in front is in order"; and words m that the decoded group's message,
    arranged on the cube, holds at each member's block (hLaid): there is the frame's group G in the
    statement in front, and ALL ROWS THAT ITS TEST TAKES IN SAY THEIR CLAIMS OF m: `AllSay rdE st
    (runRows st G).toList m`: the premise of FillRow.lean's `rowSays_of_taken`.
What is paid here against EndSays.lean's premises: that the group and the layout are there, and the
layout's k and h: they are drawn from the yes that the law's end holds (the closing's own tests
"K10.stretch" and "K10.kh") with hPr (the place's k is the stage's: on letters) and hH (the
statement's layout has the stage's h: `K10OnU`'s first clause). The sums on the cube: the end's last
conjunct, at the decoded messages, which the end says there are.
Limits. (1) hLaid IS THE WHOLE TIE BETWEEN THE TYPED MESSAGE AND THE WORDS (EndSays.lean's Limit
(1)): asked at every family of decoded messages (there is just one: a function of the statement), at
one r. Shown of no words. (2) hCar: that the relation behind gives `CarriedAt` is the opener's side
of the item "carry": not here. (3) hl, hz (the two codes' message lengths are 2 to the layout's
exponents), hN (the slots' names lie within the tables): premises. (4) Nothing on the pins. Nothing
on soundness.

-/
import Johnson.Desc.First.Close.Law.GoodOf
import Johnson.Desc.First.Close.Law.EndSays
import Johnson.Desc.First.Close.Law.KOfYes

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

variable {S : Sig GE} (R : RowsK S) (N : SlotNames R) (keep : S.O → Prop) [DecidablePred keep]
  {B : Type} [Fintype B] (pull : (R.Sh.Cin.J → GE) → R.G.C.J → GE) (n : ℕ)
  (num : R.G.Row B ≃ Fin n)
  (fx : Fin ((R.Sh.fold (SbV R B) (slV R pull) (ZV R n num)).n + 1) × GE) {Kc St₀ Wp : Type}
  {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ ((S.sub (R.sizeB keep (SbV R B) (slV R pull) (ZV R n num)).kp).Msg × Wp))
  (bC bZ : ℕ) (w₀ : S.Wit × Wp)
  (w₁ : LdBrW R.G (R.sizeB keep (SbV R B) (slV R pull) (ZV R n num)).kp Wp)

theorem k10_end_allSay
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
    (r : R.G.C.Q → GE) (m : Words GE)
    (hLaid : ∀ μ : S.Msg, (∀ i, S.decs (fa a).1.2 (fa a).2.1.2 i = some (μ i)) → ∀ G lay, (rdK
      a.1).2.2.groups[(rdK a.1).2.1.group]? = some G → (begun (rdK a.1).2.2 (rdK a.1).2.1.group
      G).layout (rdK a.1).2.1.group = some lay → LaidOn (begun (rdK a.1).2.2 (rdK a.1).2.1.group G)
      lay m (tabK N (R.Sh.rho.up (R.G.msg μ, r)).1)) :
    ∃ G, (rdK a.1).2.2.groups[(rdK a.1).2.1.group]? = some G ∧ AllSay rdE (rdK a.1).2.2 (runRows
      (rdK a.1).2.2 G).toList m := by
  obtain ⟨⟨τ, -, -, hcf⟩, -, -, -, hlast⟩ := hE
  obtain ⟨Gf, G, lay, hGf, hG, hL, hLb, ek, -⟩ := closeFrame_kh hcf
  obtain ⟨Gf', hGf', ek'⟩ := closeFrame_k hcf
  obtain rfl : Gf = Gf' := Option.some.inj (hGf.symm.trans hGf')
  obtain ⟨⟨μ, hμ⟩, hall⟩ := hlast hCar
  exact ⟨G, hG, allSay_of_rowVec N _ hI _ G hG lay hLb (ek.trans (ek'.trans hPr)) (hH lay hL)
    (hl lay hL) (hz lay hL) (hN G hG) _ m (hLaid μ hμ G lay hG hLb)
    fun i hi => hall μ hμ G lay hG hLb r i hi⟩

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.k10_end_allSay
