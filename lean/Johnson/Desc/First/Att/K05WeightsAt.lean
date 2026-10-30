-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05WeightsAt.lean: K05_law at the library's letters (A := P.own Mn):
left3_uholds'
premise hW (the typed weights at the output's point are the readings of the kind's weights), paid
for the
bits' sumcheck and for the score at the index: the two whose weights are made of the kind's own
draws alone.

Main names:
  `nat_cut1`, `nat_cut2`: the two cuts of the point drawn, as the library writes points, are the
    readings
    of the list heard.
  `value_cells_hW`, `value_atIndex_hW`: at the data made of the lists (Att/K5Claims.lean: tailData)
    every
    premise of cells_hW and atIndex_hW on the state is a lemma: the factors are the powers of the
      element
    drawn; the points are the cuts of the point drawn.

Premises left: the place's two numbers are the description's; for the bits: kap = 4.
Sources: Cb/Pv/Att/OwnSteps.lean (pubH, pubD, pubF, pubZ, sH, g1, g2); Gaps.lean (cutPt);
Blocks/Basic.lean
(nat); and what Att/K05Weights.lean and Att/K05AtValue.lean name.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05Weights
import Johnson.Desc.First.Att.K05AtValue

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb TWhole OnBytes OnBytes.Model OnBytes.Model.Road Johnson.L5.Layers Cb.Pv.Att Inst.Model
open OnBytes.Tie.Pv.Att (PscH SumH TailH recOf)
open VerifiableInference.Desc.Part

variable {K : Type} [Field K] [Fintype K] {ρ : Reading K} {M X : Type}

omit [Fintype K] in
theorem nat_cut1 (a b : ℕ) (l : List E) (k : ℕ) (hk : k < a) :
    Blocks.nat (cutPt a b (rd ρ (a + b) l)).1 k = ρ.val (l.getD k zeroE) := by
  unfold Blocks.nat
  rw [dif_pos hk]
  rfl

omit [Fintype K] in
theorem nat_cut2 (a b : ℕ) (l : List E) (k : ℕ) (hk : k < b) :
    Blocks.nat (cutPt a b (rd ρ (a + b) l)).2 k = ρ.val (l.getD (a + k) zeroE) := by
  unfold Blocks.nat
  rw [dif_pos hk]
  rfl

variable (P : OwnPar K M X) (Mn : Means K P.D P.C P.kap)

/-- **The bits' sumcheck at the library's letters: hW is paid.** -/
theorem value_cells_hW (hk4 : P.kap = 4) (rows : ℕ) {h : Heard} {G : Fork} {L : Lists}
    (hs : Said (recOf P rows) h G L) (nz : BetasNz ρ L) (nm : TailNums (P.tail Mn).toTail) (x0 : Seen K X) (g : Geo)
    (g1 : g.lt = P.D.lT) (g2 : g.lgk = P.D.lg)
    (ho : TailOfP (tailData (P.tail Mn).toTail L h nz nm x0) (recOf P rows) h L) (b : Fin P.D.nb) :
    (bitsSc3 P.kap P.D P.rd (fun _ _ => 0) P.wH P.cH).W (tailData (P.tail Mn).toTail L h nz nm x0).dH.st b
      (ldPartIni (P.D.lT + P.D.lg + P.kap) (fun _ => 3) (pDummy K 2)
        (tailData (P.tail Mn).toTail L h nz nm x0).dH.out.pt) = ρ.val ((wCells g h).getD b.1 zeroE) := by
  have hpl : L.pt.length = 2 * P.D.lg + 2 * P.D.lT + 4 := hs.lPt
  have hpg : ∀ j, h.point.getD j zeroE = L.pt.getD j zeroE := fun j => by
    rw [hs.point]
    simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]
  refine cells_hW P.kap hk4 P.D P.rd (fun _ _ => 0) P.wH P.cH 0 _ P.msg _
    (tailData (P.tail Mn).toTail L h nz nm x0).dH g h ho.zH ho.oH hs.sH ?_ g1 g2 ?_ ?_ ?_ ?_ ?_ b
  · rw [hs.om'']
    simp [powersFrom_length]
    exact le_refl _
  · rw [hs.point]
    simp [hpl]
  · intro c hc
    rw [hs.om'', powers_getD ρ _ (recOf P rows).pairs _ hc]
    rfl
  · intro k hk
    rw [hpg]
    exact (nat_cut2 P.g1 P.g2 L.pt k (by show k < P.kap + P.D.lg + P.D.lT; omega)).symm
  · intro k hk
    rw [hpg]
    refine Eq.trans ?_ (nat_cut2 P.g1 P.g2 L.pt (P.kap + k) (by show P.kap + k < P.kap + P.D.lg + P.D.lT; omega)).symm
    congr 2
    show P.D.lg + P.D.lT + 4 + k = P.D.lg + P.D.lT + (P.kap + k)
    omega
  · intro k hk
    rw [hpg]
    refine Eq.trans ?_ (nat_cut2 P.g1 P.g2 L.pt (P.kap + P.D.lg + k)
      (by show P.kap + P.D.lg + k < P.kap + P.D.lg + P.D.lT; omega)).symm
    congr 2
    show 2 * P.D.lg + P.D.lT + 4 + k = P.D.lg + P.D.lT + (P.kap + P.D.lg + k)
    omega

/-- **The score at the index at the library's letters: hW is paid.** -/
theorem value_atIndex_hW (rows : ℕ) {h : Heard} {G : Fork} {L : Lists} (hs : Said (recOf P rows) h G L)
    (nz : BetasNz ρ L) (nm : TailNums (P.tail Mn).toTail) (x0 : Seen K X) (g : Geo) (g1 : g.lt = P.D.lT)
    (g2 : g.lgk = P.D.lg) (ho : TailOfP (tailData (P.tail Mn).toTail L h nz nm x0) (recOf P rows) h L)
    (b : Fin P.D.nb) :
    (P.st3 .s16 fun p => incAt P.kF fun b => p.o b).W (tailData (P.tail Mn).toTail L h nz nm x0).dF.st b
      (ldPartIni (AttSeg.Step.s16.g P.D) (fun _ => 3) (pDummy K 2)
        (tailData (P.tail Mn).toTail L h nz nm x0).dF.out.pt) = ρ.val ((wAtIndex g h).getD b.1 zeroE) := by
  have hpl : L.pt.length = 2 * P.D.lg + 2 * P.D.lT + 4 := hs.lPt
  have hpg : ∀ j, h.point.getD j zeroE = L.pt.getD j zeroE := fun j => by
    rw [hs.point]
    simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]
  refine atIndex_hW P.D P.C P.rd _ (P.wAt .s16) (P.cAt .s16) 0 _ P.msg _
    (tailData (P.tail Mn).toTail L h nz nm x0).dF g h ho.zF ho.oF hs.sF ?_ g1 g2 ?_ ?_ ?_ ?_ ?_ b
  · rw [hs.om]
    simp [powersFrom_length]
    exact le_refl _
  · rw [hs.point]
    simp [hpl]
    omega
  · show P.D.lT + P.D.lg ≤ P.D.lT + P.D.lg + P.D.ln
    omega
  · intro c hc
    rw [hs.om, powers_getD ρ _ (recOf P rows).pairs _ hc]
    rfl
  · intro k hk
    rw [hpg]
    exact (nat_cut1 P.g1 P.g2 L.pt k (by show k < P.D.lg + P.D.lT; omega)).symm
  · intro k hk
    rw [hpg]
    exact (nat_cut1 P.g1 P.g2 L.pt (P.D.lg + k) (by show P.D.lg + k < P.D.lg + P.D.lT; omega)).symm

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.value_atIndex_hW
#print axioms VerifiableInference.Desc.First.Att.P.value_cells_hW
