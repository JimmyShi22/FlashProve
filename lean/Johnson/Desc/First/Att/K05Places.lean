-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05Places.lean: K05_law at the library's letters: the rows' second equation
(D2) (the
typed incoming form is worth the target read less what the start form is worth in the world), proved
in the
ledger's world for the denominator times the output and the two value products, each from one place:
the
mask entry of the scalar from which the sumcheck starts is the ledger's mask at its slot.

Main names:
  `d2_slot`: a scalar heard lies under slot j with the factor 1, and the target reads as it: then
    the target
    read less the slot's worth is the mask at j.
  `division_D2`, `below_D2`, `on_D2`.
  `division_prem`, `below_prem`, `on_prem`: RowPrem under (D1), that one place, and hW.

Sources: what Att/K05Prem.lean names; Cb/Pv/Att/OwnSteps.lean (inc1, inc1_sum, kE, kV, iZO, sE, sVM,
sVD).
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05Prem

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb TWhole OnBytes OnBytes.Model OnBytes.Model.Road Johnson.L5.Layers Cb.Pv.Att Inst.Model
open OnBytes.Tie.Pv.Att (PscH SumH TailH recOf sc3Num sc3Vals)
open VerifiableInference.Desc.Part

variable {K : Type} [Field K] [Fintype K] {ρ : Reading K} {M X : Type}

omit [Fintype K] in
theorem d2_slot {G : Fork} {j : ℕ} {y t : E} (hp : Put G j y oneE) (ht : ρ.val t = ρ.val y) (mask : ℕ → K)
    (entry : ℕ → ℕ → ℕ → K) : ρ.val t - (Aff.slot j).value ρ (G.worldOf ρ mask entry) = mask j := by
  rw [Aff.value_slot, hp.world ρ mask entry, ht, ρ.one]
  ring

variable (P : OwnPar K M X)

theorem division_D2 (rows : ℕ) {h : Heard} {G : Fork} {L : Lists} (hs : Said (recOf P rows) h G L) (mask : ℕ → K)
    (entry : ℕ → ℕ → ℕ → K) (m : M) (hk : P.msg m (P.kE P.iZO) = mask (h.five + 1)) (st : AttSeg.Pub K) :
    (P.st3 .s8 fun _ => inc1 (P.kE P.iZO)).plain.our.par.inc st (P.msg m) =
      ρ.val h.division.target - (Aff.slot (h.five + 1)).value ρ (G.worldOf ρ mask entry) := by
  show ∑ j, inc1 (P.kE P.iZO) j * P.msg m j = _
  rw [inc1_sum, d2_slot (hs.p5 1 (by rw [hs.l5]; omega)) (hs.tE K ρ), hk]

theorem below_D2 (rows : ℕ) {h : Heard} {G : Fork} {L : Lists} (hs : Said (recOf P rows) h G L) (mask : ℕ → K)
    (entry : ℕ → ℕ → ℕ → K) (m : M) (hk : P.msg m (P.kV 0) = mask h.values) (st : AttSeg.Pub K) :
    (P.st3 .s11 fun _ => inc1 (P.kV 0)).plain.our.par.inc st (P.msg m) =
      ρ.val h.below.target - (Aff.slot h.values).value ρ (G.worldOf ρ mask entry) := by
  show ∑ j, inc1 (P.kV 0) j * P.msg m j = _
  rw [inc1_sum, d2_slot (j := h.values) (by simpa using hs.pC 0 (by rw [hs.lC]; omega)) (hs.tM K ρ), hk]

theorem on_D2 (rows : ℕ) {h : Heard} {G : Fork} {L : Lists} (hs : Said (recOf P rows) h G L) (mask : ℕ → K)
    (entry : ℕ → ℕ → ℕ → K) (m : M) (hk : P.msg m (P.kV 1) = mask (h.values + 1)) (st : AttSeg.Pub K) :
    (P.st3 .s12 fun _ => inc1 (P.kV 1)).plain.our.par.inc st (P.msg m) =
      ρ.val h.on.target - (Aff.slot (h.values + 1)).value ρ (G.worldOf ρ mask entry) := by
  show ∑ j, inc1 (P.kV 1) j * P.msg m j = _
  rw [inc1_sum, d2_slot (hs.pC 1 (by rw [hs.lC]; omega)) (hs.tVD K ρ), hk]

variable (Mn : Means K P.D P.C P.kap)

/-- The denominator times the output: RowPrem under (D1), one place and hW. -/
theorem division_prem (rows : ℕ) {h : Heard} {G : Fork} {L : Lists} (hs : Said (recOf P rows) h G L)
    (nz : BetasNz ρ L) (nm : TailNums (P.tail Mn).toTail) (hn : ∀ a : Fin P.D.nb × Bool, nm.nE a = sc3Num a)
    (x0 : Seen K X) (mask : ℕ → K) (entry : ℕ → ℕ → ℕ → K) (m : M) {Wt : Array E} {f : Aff}
    (hf : left G h.division Wt = some f) (hsz : Wt.size = P.D.nb)
    (hk : P.msg m (P.kE P.iZO) = mask (h.five + 1))
    (hW : ∀ b : Fin P.D.nb, (P.st3 .s8 fun _ => inc1 (P.kE P.iZO)).W
      (tailData (P.tail Mn).toTail L h nz nm x0).dE.st b (ldPartIni (AttSeg.Step.s8.g P.D) (fun _ => 3) (pDummy K 2)
        (tailData (P.tail Mn).toTail L h nz nm x0).dE.out.pt) = ρ.val (Wt.getD b.1 zeroE))
    (D1 : (P.st3 .s8 fun _ => inc1 (P.kE P.iZO)).plain.our.par.W
        (tailData (P.tail Mn).toTail L h nz nm x0).dE.st (P.msg m) =
      OnBytes.Road.Hd.place (G.worldOf ρ mask entry).slot ((P.st3 .s8 fun _ => inc1 (P.kE P.iZO)).plain.our.par.vars
        (tailData (P.tail Mn).toTail L h nz nm x0).dE.st) h.division.first) :
    RowPrem (P.tail Mn).toTail.sE (tailData (P.tail Mn).toTail L h nz nm x0).dE (.slot (h.five + 1)) h.division f
      (G.worldOf ρ mask entry) m :=
  left3_prem (P.st3 .s8 fun _ => inc1 (P.kE P.iZO)) _ _ P.msg _ (tailData (P.tail Mn).toTail L h nz nm x0).dE hs.sE _ m
    hf hsz (funext fun a => by
      show ρ.val (L.HE.v.getD (nm.nE a) zeroE) = _
      rw [hn]
      rfl) hW D1 (division_D2 P rows hs mask entry m hk _)

/-- The value product below the diagonal: RowPrem under (D1), one place and hW. -/
theorem below_prem (rows : ℕ) {h : Heard} {G : Fork} {L : Lists} (hs : Said (recOf P rows) h G L)
    (nz : BetasNz ρ L) (nm : TailNums (P.tail Mn).toTail) (hn : ∀ a : Fin P.D.nb × Bool, nm.nM a = sc3Num a)
    (x0 : Seen K X) (mask : ℕ → K) (entry : ℕ → ℕ → ℕ → K) (m : M) {Wt : Array E} {f : Aff}
    (hf : left G h.below Wt = some f) (hsz : Wt.size = P.D.nb) (hk : P.msg m (P.kV 0) = mask h.values)
    (hW : ∀ b : Fin P.D.nb, (P.st3 .s11 fun _ => inc1 (P.kV 0)).W
      (tailData (P.tail Mn).toTail L h nz nm x0).dVM.st b (ldPartIni (AttSeg.Step.s11.g P.D) (fun _ => 3) (pDummy K 2)
        (tailData (P.tail Mn).toTail L h nz nm x0).dVM.out.pt) = ρ.val (Wt.getD b.1 zeroE))
    (D1 : (P.st3 .s11 fun _ => inc1 (P.kV 0)).plain.our.par.W
        (tailData (P.tail Mn).toTail L h nz nm x0).dVM.st (P.msg m) =
      OnBytes.Road.Hd.place (G.worldOf ρ mask entry).slot ((P.st3 .s11 fun _ => inc1 (P.kV 0)).plain.our.par.vars
        (tailData (P.tail Mn).toTail L h nz nm x0).dVM.st) h.below.first) :
    RowPrem (P.tail Mn).toTail.sVM (tailData (P.tail Mn).toTail L h nz nm x0).dVM (.slot h.values) h.below f
      (G.worldOf ρ mask entry) m :=
  left3_prem (P.st3 .s11 fun _ => inc1 (P.kV 0)) _ _ P.msg _ (tailData (P.tail Mn).toTail L h nz nm x0).dVM hs.sM _ m
    hf hsz (funext fun a => by
      show ρ.val (L.HM.v.getD (nm.nM a) zeroE) = _
      rw [hn]
      rfl) hW D1 (below_D2 P rows hs mask entry m hk _)

/-- The value product on the diagonal: RowPrem under (D1), one place and hW. -/
theorem on_prem (rows : ℕ) {h : Heard} {G : Fork} {L : Lists} (hs : Said (recOf P rows) h G L)
    (nz : BetasNz ρ L) (nm : TailNums (P.tail Mn).toTail) (hn : ∀ a : Fin P.D.nb × Bool, nm.nVD a = sc3Num a)
    (x0 : Seen K X) (mask : ℕ → K) (entry : ℕ → ℕ → ℕ → K) (m : M) {Wt : Array E} {f : Aff}
    (hf : left G h.on Wt = some f) (hsz : Wt.size = P.D.nb) (hk : P.msg m (P.kV 1) = mask (h.values + 1))
    (hW : ∀ b : Fin P.D.nb, (P.st3 .s12 fun _ => inc1 (P.kV 1)).W
      (tailData (P.tail Mn).toTail L h nz nm x0).dVD.st b (ldPartIni (AttSeg.Step.s12.g P.D) (fun _ => 3) (pDummy K 2)
        (tailData (P.tail Mn).toTail L h nz nm x0).dVD.out.pt) = ρ.val (Wt.getD b.1 zeroE))
    (D1 : (P.st3 .s12 fun _ => inc1 (P.kV 1)).plain.our.par.W
        (tailData (P.tail Mn).toTail L h nz nm x0).dVD.st (P.msg m) =
      OnBytes.Road.Hd.place (G.worldOf ρ mask entry).slot ((P.st3 .s12 fun _ => inc1 (P.kV 1)).plain.our.par.vars
        (tailData (P.tail Mn).toTail L h nz nm x0).dVD.st) h.on.first) :
    RowPrem (P.tail Mn).toTail.sVD (tailData (P.tail Mn).toTail L h nz nm x0).dVD (.slot (h.values + 1)) h.on f
      (G.worldOf ρ mask entry) m :=
  left3_prem (P.st3 .s12 fun _ => inc1 (P.kV 1)) _ _ P.msg _ (tailData (P.tail Mn).toTail L h nz nm x0).dVD hs.sVD _ m
    hf hsz (funext fun a => by
      show ρ.val (L.HVD.v.getD (nm.nVD a) zeroE) = _
      rw [hn]
      rfl) hW D1 (on_D2 P rows hs mask entry m hk _)

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.division_prem
#print axioms VerifiableInference.Desc.First.Att.P.below_prem
#print axioms VerifiableInference.Desc.First.Att.P.on_prem
