-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05ClosedSeam.lean: at the closed parameters (Att/K05Closed.lean) and the
world of the
message's own mask: more premises that were "a place" are lemmas.

Main names:
  `end_put`: under the slot of end value number i lies what was heard, with the factor beta.
  `closed_division_prem`, `closed_on_prem`: RowPrem of the denominator times the output and of the
    value
    product on the diagonal, at leftP's rows: no place left; LookPts stays.
  `closed_ends`: the places of the end values' mask entries, at the library's numbering sc3Num, for
    the
    denominator times the output, the two value products, the score at the index and the bits.

Sources: what Att/K05ClosedAt.lean names; OnBytes/Tie/Pv/Att (sc3Num_lt, scdNum_lt).
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05ClosedAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb TWhole OnBytes OnBytes.Model OnBytes.Model.Road Johnson.L5.Layers Cb.Pv.Att Inst.Model
open OnBytes.Tie.Pv.Att (PscH SumH TailH recOf sc3Num sc3Num_lt scdNum scdNum_lt)
open VerifiableInference.Desc.Part

variable {K : Type} [Field K] [Fintype K] {ρ : Reading K} {M0 X : Type}

theorem end_put {C : Aff} {vs : List MaskedSum.Var} {e : MaskedSum.Ends} {pre : List E} {H : PscH}
    {hh : MaskedSum.Heard} {G : Fork} (h : SumAt C (.sum vs e) pre H hh G) {i : ℕ} (hi : i < e.n) :
    Put G (hh.sEnd + i) (H.v.getD i zeroE) H.beta := by
  obtain ⟨vs', e', F, G0, used, e1, sd, hst⟩ := h
  injection e1 with _ e3
  subst e3
  exact hst _ _ _ (sd.ends i hi)

/-- **The denominator times the output at the closed parameters: no place left.** -/
theorem closed_division_prem (P0 : OwnPar K M0 X) {Mg : Type} (Λ : Lin P0 Mg) {h : Heard} {G : Fork}
    (Mn : Means K (closedOf P0 Λ G.ns (numsOf h)).D (closedOf P0 Λ G.ns (numsOf h)).C (closedOf P0 Λ G.ns (numsOf h)).kap)
    (rows : ℕ) {L : Lists} (hs : Said (recOf (closedOf P0 Λ G.ns (numsOf h)) rows) h G L)
    (hz : Sized G) (nz : BetasNz ρ L) (nm : TailNums ((closedOf P0 Λ G.ns (numsOf h)).tail Mn).toTail)
    (hn : ∀ a : Fin P0.D.nb × Bool, nm.nE a = sc3Num a) (x0 : Seen K X) (g : Geo) (g1 : g.lt = P0.D.lT)
    (g2 : g.lgk = P0.D.lg)
    (ho : TailOfP (tailData ((closedOf P0 Λ G.ns (numsOf h)).tail Mn).toTail L h nz nm x0)
      (recOf (closedOf P0 Λ G.ns (numsOf h)) rows) h L) {pw zW : Array E}
    (lp : LookPts ρ P0.D P0.C (P0.zOf x0.1) pw zW)
    (entry : ℕ → ℕ → ℕ → K) (m : Mg) {f : Aff} (hf : left G h.division (wDivision g pw zW h) = some f) :
    RowPrem ((closedOf P0 Λ G.ns (numsOf h)).tail Mn).toTail.sE
      (tailData ((closedOf P0 Λ G.ns (numsOf h)).tail Mn).toTail L h nz nm x0).dE (.slot (h.five + 1)) h.division f
      (G.worldOf ρ (Λ.maskOf m) entry) m :=
  value_division_prem (closedOf P0 Λ G.ns (numsOf h)) Mn rows hs nz nm hn x0 g g1 g2 ho lp (Λ.maskOf m) entry m hf
    (closed_kE P0 Λ G.ns (numsOf h) m (le_of_lt (put_lt hz (hs.p5 1 (by rw [hs.l5]; omega)))))
    (D1_at ((closedOf P0 Λ G.ns (numsOf h)).tail Mn).toTail.sE _ ho.zE hs.sE (Λ.maskOf m) entry m fun i =>
      closed_w P0 Λ G.ns (numsOf h) m .s8 i
        (le_of_lt (put_lt hz (coef_put ((closedOf P0 Λ G.ns (numsOf h)).tail Mn).toTail.sE ho.zE hs.sE i))))

/-- **The value product on the diagonal at the closed parameters: no place left.** -/
theorem closed_on_prem (P0 : OwnPar K M0 X) {Mg : Type} (Λ : Lin P0 Mg) {h : Heard} {G : Fork}
    (Mn : Means K (closedOf P0 Λ G.ns (numsOf h)).D (closedOf P0 Λ G.ns (numsOf h)).C (closedOf P0 Λ G.ns (numsOf h)).kap)
    (rows : ℕ) {L : Lists} (hs : Said (recOf (closedOf P0 Λ G.ns (numsOf h)) rows) h G L)
    (hz : Sized G) (nz : BetasNz ρ L) (nm : TailNums ((closedOf P0 Λ G.ns (numsOf h)).tail Mn).toTail)
    (hn : ∀ a : Fin P0.D.nb × Bool, nm.nVD a = sc3Num a) (x0 : Seen K X) (g : Geo) (g1 : g.lt = P0.D.lT)
    (g2 : g.lgk = P0.D.lg) (g3 : g.lnT = P0.D.lP + 1)
    (ho : TailOfP (tailData ((closedOf P0 Λ G.ns (numsOf h)).tail Mn).toTail L h nz nm x0)
      (recOf (closedOf P0 Λ G.ns (numsOf h)) rows) h L) {pw zW : Array E}
    (lp : LookPts ρ P0.D P0.C (P0.zOf x0.1) pw zW)
    (entry : ℕ → ℕ → ℕ → K) (m : Mg) {f : Aff} (hf : left G h.on (wOn g pw zW h) = some f) :
    RowPrem ((closedOf P0 Λ G.ns (numsOf h)).tail Mn).toTail.sVD
      (tailData ((closedOf P0 Λ G.ns (numsOf h)).tail Mn).toTail L h nz nm x0).dVD (.slot (h.values + 1)) h.on f
      (G.worldOf ρ (Λ.maskOf m) entry) m :=
  value_on_prem (closedOf P0 Λ G.ns (numsOf h)) Mn rows hs nz nm hn x0 g g1 g2 g3 ho lp (Λ.maskOf m) entry m hf
    (closed_kV P0 Λ G.ns (numsOf h) m 1 (le_of_lt (put_lt hz (hs.pC 1 (by rw [hs.lC]; omega)))))
    (D1_at ((closedOf P0 Λ G.ns (numsOf h)).tail Mn).toTail.sVD _ ho.zVD hs.sVD (Λ.maskOf m) entry m fun i =>
      closed_w P0 Λ G.ns (numsOf h) m .s12 i
        (le_of_lt (put_lt hz (coef_put ((closedOf P0 Λ G.ns (numsOf h)).tail Mn).toTail.sVD ho.zVD hs.sVD i))))

/-- **The places of the end values' mask entries, at the closed parameters**: the five sumchecks of
the tail that owe their
output claims, and the score at the index. -/
theorem closed_ends (P0 : OwnPar K M0 X) {Mg : Type} (Λ : Lin P0 Mg) {h : Heard} {G : Fork} (rows : ℕ) {L : Lists}
    (hs : Said (recOf (closedOf P0 Λ G.ns (numsOf h)) rows) h G L) (hz : Sized G) (m : Mg) :
    (∀ y : Fin P0.D.nb × Bool, (closedOf P0 Λ G.ns (numsOf h)).msg m ((closedOf P0 Λ G.ns (numsOf h)).cAt .s8 y) =
      (Λ.maskOf m) (h.division.sEnd + sc3Num y)) ∧
    (∀ y : Fin P0.D.nb × Bool, (closedOf P0 Λ G.ns (numsOf h)).msg m ((closedOf P0 Λ G.ns (numsOf h)).cAt .s11 y) =
      (Λ.maskOf m) (h.below.sEnd + sc3Num y)) ∧
    (∀ y : Fin P0.D.nb × Bool, (closedOf P0 Λ G.ns (numsOf h)).msg m ((closedOf P0 Λ G.ns (numsOf h)).cAt .s12 y) =
      (Λ.maskOf m) (h.on.sEnd + sc3Num y)) ∧
    (∀ y : Fin P0.D.nb × Bool, (closedOf P0 Λ G.ns (numsOf h)).msg m ((closedOf P0 Λ G.ns (numsOf h)).cAt .s16 y) =
      (Λ.maskOf m) (h.atIndex.sEnd + sc3Num y)) ∧
    (∀ y : Fin P0.D.nb × Bool, (closedOf P0 Λ G.ns (numsOf h)).msg m ((closedOf P0 Λ G.ns (numsOf h)).cH y) =
      (Λ.maskOf m) (h.cells.sEnd + sc3Num y)) :=
  ⟨fun y => closed_c P0 Λ G.ns (numsOf h) m .s8 y (le_of_lt (put_lt hz (end_put hs.sE (sc3Num_lt y)))),
   fun y => closed_c P0 Λ G.ns (numsOf h) m .s11 y (le_of_lt (put_lt hz (end_put hs.sM (sc3Num_lt y)))),
   fun y => closed_c P0 Λ G.ns (numsOf h) m .s12 y (le_of_lt (put_lt hz (end_put hs.sVD (sc3Num_lt y)))),
   fun y => closed_c P0 Λ G.ns (numsOf h) m .s16 y (le_of_lt (put_lt hz (end_put hs.sF (sc3Num_lt y)))),
   fun y => closed_cH P0 Λ G.ns (numsOf h) m y (le_of_lt (put_lt hz (end_put hs.sH (sc3Num_lt y))))⟩

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.closed_division_prem
#print axioms VerifiableInference.Desc.First.Att.P.closed_on_prem
#print axioms VerifiableInference.Desc.First.Att.P.closed_ends
