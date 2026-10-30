-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05Prem2.lean: K05_law at the library's letters: RowPrem of the denominator
times the
output and of the value product on the diagonal, at the rows that leftP makes (weights wDivision,
wOn).

Main names: `value_division_prem`, `value_on_prem`.
Premises: (D1) · one place each · LookPts at the typed first statement's lookup point · the place's
numbers.
Sources: what Att/K05Places.lean and Att/K05Weights2.lean name; Cb/Pv/Att/OwnSteps.lean (pub0, pubV,
zOf).
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05Places
import Johnson.Desc.First.Att.K05Weights2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb TWhole OnBytes OnBytes.Model OnBytes.Model.Road Johnson.L5.Layers Cb.Pv.Att Inst.Model
open OnBytes.Tie.Pv.Att (PscH SumH TailH recOf sc3Num)
open VerifiableInference.Desc.Part

variable {K : Type} [Field K] [Fintype K] {ρ : Reading K} {M X : Type}
variable (P : OwnPar K M X) (Mn : Means K P.D P.C P.kap)

/-- **The denominator times the output, at leftP's row.** -/
theorem value_division_prem (rows : ℕ) {h : Heard} {G : Fork} {L : Lists} (hs : Said (recOf P rows) h G L)
    (nz : BetasNz ρ L) (nm : TailNums (P.tail Mn).toTail) (hn : ∀ a : Fin P.D.nb × Bool, nm.nE a = sc3Num a)
    (x0 : Seen K X) (g : Geo) (g1 : g.lt = P.D.lT) (g2 : g.lgk = P.D.lg)
    (ho : TailOfP (tailData (P.tail Mn).toTail L h nz nm x0) (recOf P rows) h L) {pw zW : Array E}
    (lp : LookPts ρ P.D P.C (P.zOf x0.1) pw zW) (mask : ℕ → K) (entry : ℕ → ℕ → ℕ → K) (m : M) {f : Aff}
    (hf : left G h.division (wDivision g pw zW h) = some f) (hk : P.msg m (P.kE P.iZO) = mask (h.five + 1))
    (D1 : (P.st3 .s8 fun _ => inc1 (P.kE P.iZO)).plain.our.par.W
        (tailData (P.tail Mn).toTail L h nz nm x0).dE.st (P.msg m) =
      OnBytes.Road.Hd.place (G.worldOf ρ mask entry).slot ((P.st3 .s8 fun _ => inc1 (P.kE P.iZO)).plain.our.par.vars
        (tailData (P.tail Mn).toTail L h nz nm x0).dE.st) h.division.first) :
    RowPrem (P.tail Mn).toTail.sE (tailData (P.tail Mn).toTail L h nz nm x0).dE (.slot (h.five + 1)) h.division f
      (G.worldOf ρ mask entry) m :=
  division_prem P Mn rows hs nz nm hn x0 mask entry m hf
    (by unfold wDivision; rw [Array.size_map]; exact lp.nPw) hk
    (division_hW P.D P.C P.rd _ (P.wAt .s8) (P.cAt .s8) _ _ P.msg _ (tailData (P.tail Mn).toTail L h nz nm x0).dE g h
      ho.zE ho.oE hs.sE lp g1 g2) D1

/-- **The value product on the diagonal, at leftP's row.** -/
theorem value_on_prem (rows : ℕ) {h : Heard} {G : Fork} {L : Lists} (hs : Said (recOf P rows) h G L)
    (nz : BetasNz ρ L) (nm : TailNums (P.tail Mn).toTail) (hn : ∀ a : Fin P.D.nb × Bool, nm.nVD a = sc3Num a)
    (x0 : Seen K X) (g : Geo) (g1 : g.lt = P.D.lT) (g2 : g.lgk = P.D.lg) (g3 : g.lnT = P.D.lP + 1)
    (ho : TailOfP (tailData (P.tail Mn).toTail L h nz nm x0) (recOf P rows) h L) {pw zW : Array E}
    (lp : LookPts ρ P.D P.C (P.zOf x0.1) pw zW) (mask : ℕ → K) (entry : ℕ → ℕ → ℕ → K) (m : M) {f : Aff}
    (hf : left G h.on (wOn g pw zW h) = some f) (hk : P.msg m (P.kV 1) = mask (h.values + 1))
    (D1 : (P.st3 .s12 fun _ => inc1 (P.kV 1)).plain.our.par.W
        (tailData (P.tail Mn).toTail L h nz nm x0).dVD.st (P.msg m) =
      OnBytes.Road.Hd.place (G.worldOf ρ mask entry).slot ((P.st3 .s12 fun _ => inc1 (P.kV 1)).plain.our.par.vars
        (tailData (P.tail Mn).toTail L h nz nm x0).dVD.st) h.on.first) :
    RowPrem (P.tail Mn).toTail.sVD (tailData (P.tail Mn).toTail L h nz nm x0).dVD (.slot (h.values + 1)) h.on f
      (G.worldOf ρ mask entry) m :=
  on_prem P Mn rows hs nz nm hn x0 mask entry m hf
    (by unfold wOn; rw [Array.size_map]; exact lp.nPw) hk
    (on_hW P.D P.C P.rd _ (P.wAt .s12) (P.cAt .s12) _ _ P.msg _ (tailData (P.tail Mn).toTail L h nz nm x0).dVD g h
      ho.zVD ho.oVD hs.sVD lp g1 g2 g3) D1

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.value_division_prem
#print axioms VerifiableInference.Desc.First.Att.P.value_on_prem
