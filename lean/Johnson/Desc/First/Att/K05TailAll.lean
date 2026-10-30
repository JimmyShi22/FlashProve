-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05TailAll.lean: at the closed parameters: K05_law's premise TailPrem, whole,
at the rows
that leftP returns.

Main names:
  `closed_below_prem`: the value product below the diagonal: RowPrem, no place left.
  `closed_tailPrem`: from leftP's own return (LeftIs (geoOf S) zk h G l), Said, Sized G, BetasNz,
    the library's
    numberings, TailOfP, P0.D = L5.dimOf S, Sizes S, kap = 4, two equations of numbers, and LookPts
      at the
    weights and the inner point that leftP itself took.

Sources: what Att/K05Weights4.lean, K05Key.lean and K05ClosedSeam.lean name.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05Weights4
import Johnson.Desc.First.Att.K05Key

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb TWhole OnBytes OnBytes.Model OnBytes.Model.Road Johnson.L5.Layers Cb.Pv.Att Inst.Model
open OnBytes.Tie.Pv.Att (PscH SumH TailH recOf sc3Num scdNum)
open VerifiableInference.Desc.Part

variable {K : Type} [Field K] [Fintype K] {ρ : Reading K} {M0 X : Type}

/-- **The value product below the diagonal at the closed parameters: no place left.** -/
theorem closed_below_prem (P0 : OwnPar K M0 X) {Mg : Type} (Λ : Lin P0 Mg) {h : Heard} {G : Fork}
    (Mn : Means K (closedOf P0 Λ G.ns (numsOf h)).D (closedOf P0 Λ G.ns (numsOf h)).C
      (closedOf P0 Λ G.ns (numsOf h)).kap)
    (rows : ℕ) {L : Lists} (hs : Said (recOf (closedOf P0 Λ G.ns (numsOf h)) rows) h G L)
    (hz : Sized G) (nz : BetasNz ρ L) (nm : TailNums ((closedOf P0 Λ G.ns (numsOf h)).tail Mn).toTail)
    (hn : ∀ a : Fin P0.D.nb × Bool, nm.nM a = sc3Num a) (x0 : Seen K X) (S : Attention.Shape)
    (hDS : P0.D = OnBytes.Road.L5.dimOf S) (Z : OnBytes.Road.Rows.Sizes S) (hlt : S.cf.lt = P0.D.lT)
    (ho : TailOfP (tailData ((closedOf P0 Λ G.ns (numsOf h)).tail Mn).toTail L h nz nm x0)
      (recOf (closedOf P0 Λ G.ns (numsOf h)) rows) h L) {pw zW : Array E}
    (lp : LookPts ρ P0.D P0.C (P0.zOf x0.1) pw zW)
    (entry : ℕ → ℕ → ℕ → K) (m : Mg) {f : Aff} (hf : left G h.below (wBelow (geoOf S) pw zW h) = some f) :
    RowPrem ((closedOf P0 Λ G.ns (numsOf h)).tail Mn).toTail.sVM
      (tailData ((closedOf P0 Λ G.ns (numsOf h)).tail Mn).toTail L h nz nm x0).dVM (.slot h.values) h.below f
      (G.worldOf ρ (Λ.maskOf m) entry) m :=
  below_prem (closedOf P0 Λ G.ns (numsOf h)) Mn rows hs nz nm hn x0 (Λ.maskOf m) entry m hf
    (by unfold wBelow; rw [Array.size_map]; exact lp.nPw)
    (by simpa using closed_kV P0 Λ G.ns (numsOf h) m 0 (le_of_lt (put_lt hz (by simpa using hs.pC 0 (by rw [hs.lC]; omega)))))
    (below_hW P0.D S hDS Z hlt P0.C (closedOf P0 Λ G.ns (numsOf h)).rd _ ((closedOf P0 Λ G.ns (numsOf h)).wAt .s11)
      ((closedOf P0 Λ G.ns (numsOf h)).cAt .s11) _ _ (closedOf P0 Λ G.ns (numsOf h)).msg _
      (tailData ((closedOf P0 Λ G.ns (numsOf h)).tail Mn).toTail L h nz nm x0).dVM h ho.zM ho.oM hs.sM lp)
    (D1_at ((closedOf P0 Λ G.ns (numsOf h)).tail Mn).toTail.sVM _ ho.zM hs.sM (Λ.maskOf m) entry m fun i =>
      closed_w P0 Λ G.ns (numsOf h) m .s11 i
        (le_of_lt (put_lt hz (coef_put ((closedOf P0 Λ G.ns (numsOf h)).tail Mn).toTail.sVM ho.zM hs.sM i))))

/-- **TailPrem at the closed parameters, at the rows that leftP returns.** -/
theorem closed_tailPrem (P0 : OwnPar K M0 X) {Mg : Type} (Λ : Lin P0 Mg) {h : Heard} {G : Fork}
    (Mn : Means K (closedOf P0 Λ G.ns (numsOf h)).D (closedOf P0 Λ G.ns (numsOf h)).C
      (closedOf P0 Λ G.ns (numsOf h)).kap)
    (hk4 : P0.kap = 4) (rows : ℕ) {L : Lists} (hs : Said (recOf (closedOf P0 Λ G.ns (numsOf h)) rows) h G L)
    (hz : Sized G) (nz : BetasNz ρ L) (nm : TailNums ((closedOf P0 Λ G.ns (numsOf h)).tail Mn).toTail)
    (hnE : ∀ a : Fin P0.D.nb × Bool, nm.nE a = sc3Num a) (hnM : ∀ a : Fin P0.D.nb × Bool, nm.nM a = sc3Num a)
    (hnVD : ∀ a : Fin P0.D.nb × Bool, nm.nVD a = sc3Num a)
    (hnD : ∀ a : (size18 P0.D).A, nm.nD a = scdNum (size18 P0.D) a)
    (hnH : ∀ a : Fin P0.D.nb × Bool, nm.nH a = sc3Num a) (x0 : Seen K X) (S : Attention.Shape)
    (hDS : P0.D = OnBytes.Road.L5.dimOf S) (Z : OnBytes.Road.Rows.Sizes S) (hlt : S.cf.lt = P0.D.lT)
    (hNP : (geoOf S).NP = (size18 P0.D).pairs)
    (ho : TailOfP (tailData ((closedOf P0 Λ G.ns (numsOf h)).tail Mn).toTail L h nz nm x0)
      (recOf (closedOf P0 Λ G.ns (numsOf h)) rows) h L) {zk : Array (Array E)} {l : Left}
    (li : LeftIs (geoOf S) zk h G l)
    (lp : ∀ wl, (geoOf S).single .wl = some wl → LookPts ρ P0.D P0.C (P0.zOf x0.1)
      (weights wl (zk.getD wl.call #[])) (inner wl (zk.getD wl.call #[])))
    (entry : ℕ → ℕ → ℕ → K) (m : Mg) :
    TailPrem (tailData ((closedOf P0 Λ G.ns (numsOf h)).tail Mn).toTail L h nz nm x0)
      (recOf (closedOf P0 Λ G.ns (numsOf h)) rows) h l (G.worldOf ρ (Λ.maskOf m) entry) m := by
  obtain ⟨wl, w1, _, _, lE, lM, lVD, _, lD, lH⟩ := li.rest
  have hl := Z.lnT
  have g1 : (geoOf S).lt = P0.D.lT := hlt
  have g2 : (geoOf S).lgk = P0.D.lg := by rw [hDS]; rfl
  have g3 : (geoOf S).lnT = P0.D.lP + 1 := by
    rw [hDS]
    show S.lnT = S.lnT - 1 + 1
    omega
  exact ⟨closed_division_prem P0 Λ Mn rows hs hz nz nm hnE x0 (geoOf S) g1 g2 ho (lp wl w1) entry m lE,
    closed_below_prem P0 Λ Mn rows hs hz nz nm hnM x0 S hDS Z hlt ho (lp wl w1) entry m lM,
    closed_on_prem P0 Λ Mn rows hs hz nz nm hnVD x0 (geoOf S) g1 g2 g3 ho (lp wl w1) entry m lVD,
    closed_key_prem P0 Λ Mn rows hs hz nz nm hnD x0 (geoOf S) g1 g2 (by rw [hDS]; rfl) (by rw [hDS]; rfl) hNP ho entry m
      lD,
    closed_cells_prem P0 Λ Mn hk4 rows hs hz nz nm hnH x0 (geoOf S) g1 g2 ho entry m lH⟩

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.closed_tailPrem
#print axioms VerifiableInference.Desc.First.Att.P.closed_below_prem
