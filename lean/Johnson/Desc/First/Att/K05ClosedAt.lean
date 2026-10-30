-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05ClosedAt.lean: at the closed parameters (Att/K05Closed.lean: closedOf P0 Λ
G.ns
(numsOf h)) and the world of the message's own mask: RowPrem with no place left, for the bits'
sumcheck and
the score at the index.

Main names: `closed_cells_prem`, `closed_atIndex_prem`.
Premises left: kap = 4 (the bits) · Said · Sized G · BetasNz · the library's numbering sc3Num · the
place's two
numbers are the description's · TailOfP · left has returned at leftP's weights.
The theorems are stated at the ledger G of Said. Att/K05Numbers.lean's closed_is_plan: where G is
the ledger
behind the hearing, or a later one with as many slots, these parameters are made of the plan and of
two
numbers of the ledger in front.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05Closed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb TWhole OnBytes OnBytes.Model OnBytes.Model.Road Johnson.L5.Layers Cb.Pv.Att Inst.Model
open OnBytes.Tie.Pv.Att (PscH SumH TailH recOf sc3Num)
open VerifiableInference.Desc.Part

variable {K : Type} [Field K] [Fintype K] {ρ : Reading K} {M0 X : Type}

/-- **The bits' sumcheck at the closed parameters: RowPrem, no place left.** -/
theorem closed_cells_prem (P0 : OwnPar K M0 X) {Mg : Type} (Λ : Lin P0 Mg) {h : Heard} {G : Fork}
    (Mn : Means K (closedOf P0 Λ G.ns (numsOf h)).D (closedOf P0 Λ G.ns (numsOf h)).C (closedOf P0 Λ G.ns (numsOf h)).kap)
    (hk4 : P0.kap = 4) (rows : ℕ) {L : Lists} (hs : Said (recOf (closedOf P0 Λ G.ns (numsOf h)) rows) h G L)
    (hz : Sized G) (nz : BetasNz ρ L) (nm : TailNums ((closedOf P0 Λ G.ns (numsOf h)).tail Mn).toTail)
    (hnH : ∀ a : Fin P0.D.nb × Bool, nm.nH a = sc3Num a) (x0 : Seen K X) (g : Geo) (g1 : g.lt = P0.D.lT)
    (g2 : g.lgk = P0.D.lg)
    (ho : TailOfP (tailData ((closedOf P0 Λ G.ns (numsOf h)).tail Mn).toTail L h nz nm x0)
      (recOf (closedOf P0 Λ G.ns (numsOf h)) rows) h L)
    (entry : ℕ → ℕ → ℕ → K) (m : Mg) {f : Aff} (hf : left G h.cells (wCells g h) = some f) :
    RowPrem ((closedOf P0 Λ G.ns (numsOf h)).tail Mn).toTail.sH
      (tailData ((closedOf P0 Λ G.ns (numsOf h)).tail Mn).toTail L h nz nm x0).dH (.ofConst zeroE) h.cells f
      (G.worldOf ρ (Λ.maskOf m) entry) m :=
  value_cells_prem (closedOf P0 Λ G.ns (numsOf h)) Mn hk4 rows hs nz nm hnH x0 g g1 g2 ho _ m hf
    (D1_at ((closedOf P0 Λ G.ns (numsOf h)).tail Mn).toTail.sH _ ho.zH hs.sH (Λ.maskOf m) entry m fun i =>
      closed_wH P0 Λ G.ns (numsOf h) m i
        (le_of_lt (put_lt hz (coef_put ((closedOf P0 Λ G.ns (numsOf h)).tail Mn).toTail.sH ho.zH hs.sH i))))

/-- **The score at the index at the closed parameters: RowPrem, no place left.** -/
theorem closed_atIndex_prem (P0 : OwnPar K M0 X) {Mg : Type} (Λ : Lin P0 Mg) {h : Heard} {G : Fork}
    (Mn : Means K (closedOf P0 Λ G.ns (numsOf h)).D (closedOf P0 Λ G.ns (numsOf h)).C (closedOf P0 Λ G.ns (numsOf h)).kap)
    (rows : ℕ) {L : Lists} (hs : Said (recOf (closedOf P0 Λ G.ns (numsOf h)) rows) h G L)
    (hz : Sized G) (nz : BetasNz ρ L) (nm : TailNums ((closedOf P0 Λ G.ns (numsOf h)).tail Mn).toTail)
    (hnF : ∀ a : Fin P0.D.nb × Bool, nm.nF a = sc3Num a) (x0 : Seen K X) (g : Geo) (g1 : g.lt = P0.D.lT)
    (g2 : g.lgk = P0.D.lg)
    (ho : TailOfP (tailData ((closedOf P0 Λ G.ns (numsOf h)).tail Mn).toTail L h nz nm x0)
      (recOf (closedOf P0 Λ G.ns (numsOf h)) rows) h L)
    (entry : ℕ → ℕ → ℕ → K) (m : Mg) {f : Aff} (hf : left G h.atIndex (wAtIndex g h) = some f) :
    RowPrem ((closedOf P0 Λ G.ns (numsOf h)).tail Mn).toTail.sF
      (tailData ((closedOf P0 Λ G.ns (numsOf h)).tail Mn).toTail L h nz nm x0).dF
      (batched (recOf (closedOf P0 Λ G.ns (numsOf h)) rows).pairs h.om h.maxima 1 0) h.atIndex f
      (G.worldOf ρ (Λ.maskOf m) entry) m :=
  value_atIndex_prem (closedOf P0 Λ G.ns (numsOf h)) Mn rows hs nz nm hnF x0 g g1 g2 ho (Λ.maskOf m) entry m hf
    (fun i => closed_kF P0 Λ G.ns (numsOf h) m i (le_of_lt (put_lt hz (hs.pM i.1 (by rw [hs.lM]; exact i.2)))))
    (D1_at ((closedOf P0 Λ G.ns (numsOf h)).tail Mn).toTail.sF _ ho.zF hs.sF (Λ.maskOf m) entry m fun i =>
      closed_w P0 Λ G.ns (numsOf h) m .s16 i
        (le_of_lt (put_lt hz (coef_put ((closedOf P0 Λ G.ns (numsOf h)).tail Mn).toTail.sF ho.zF hs.sF i))))

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.closed_cells_prem
#print axioms VerifiableInference.Desc.First.Att.P.closed_atIndex_prem
