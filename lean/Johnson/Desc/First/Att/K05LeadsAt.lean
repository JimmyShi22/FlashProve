-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05LeadsAt.lean: the law of Att/K05LeadsRow.lean at the library's own carry:
over written rounds
uLT (ckP .two) ds, at the field GE and the reading Reading.gl, with the view "rvT (ckP .two) ds τ,
the digests struck" and
F := chCarry (Att/K05Read.lean). The debts (b) and (c) of Att/K05Leads.lean are paid.

Main names:
  `readsAs_carry`: ReadsAs at the carry, from carry_reads, where "yes" gives that the tests of work
    pass.
  `K05_leads_row_at`, `K05_keepsW_row_at`.

Premises left: CapAt; the ledger in front (two numbers, Sized, LookAll); the seam: out's yes is
decide's yes on the view,
with roundsFit, every drawn triple below the prime, the tests of work passed; the written rounds
meet the specs (MeetsT),
hold no "answer" item, and their counts bear the chain's errors (BearsT); the names' lists are
Listed; for KeepsW:
BillsRow, on' for certain, the pin.
No soundness of the protocol is claimed: the seam and the premises named are not shown.
Nothing is claimed on completeness or hiding.

-/
import Johnson.Desc.First.Att.K05LeadsRow
import Johnson.Desc.First.Att.K05ReadAs

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb TWhole IOR OnBytes OnBytes.Model OnBytes.Model.Road Cb.Pv.Att Inst.Model OnBytes.Slice OnBytes.Flat
open OnBytes.Maker Run Fo.Peel

variable {X Mg : Type}

/-- **(c) at the library's own carry.** -/
theorem readsAs_carry {Aa : Type} (P : OwnPar GE Mg X) (Ex : ExtSpec) (x : Params.AttentionRounds) (ds : List RDT)
    (qu : UShs (P.own (theMeans GE P.D P.C P.kap)).units) (qt : Shs (P.own (theMeans GE P.D P.C P.kap)).tail)
    (lu : UListed _ qu (landedUnits P _)) (lt : TListed qt (landedTail P _))
    (hl : ds.length = (chSp (P.own (theMeans GE P.D P.C P.kap)).ch (ownRd _ qu qt)).length)
    (hA : ∀ d ∈ ds, NoAns d.items) (x0 : Aa → X) (yes : Aa → Tr (uLT (ckP .two) ds) → Prop)
    (hy : ∀ a τ, yes a τ → passT (ckP .two) ds (rhoT (ckP .two) ds τ) = true) :
    ReadsAs P Ex Reading.gl x (fun _ τ => (rvT (ckP .two) ds τ).map noDigest) x0 yes
      (fun _ => chCarry Ex (P.own (theMeans GE P.D P.C P.kap)).ch (ownRd _ qu qt) ds hl) :=
  fun a τ _ _ _ nz du dt h0 hs hr t1 t2 t3 t4 =>
    carry_reads Ex _ qu qt _ _ lu lt ds hl hA τ (hy a τ h0) hs hr nz (x0 a) du dt t1 t2 t3 t4

/-- **K5's law in the plain form, at the library's own carry.** -/
theorem K05_leads_row_at {M0 St Aa Bb : Type} (P0 : OwnPar GE M0 X) (Λ : Lin P0 Mg) (seat : Seat St) (p : Par)
    (ns0 k0 : ℕ) {S : Attention.Shape} {rows : ℕ} {u1 u2 : UnitG} (cap : CapAt P0 S p rows u1 u2) (Ex : ExtSpec)
    (ds : List RDT) (out : Aa → Tr (uLT (ckP .two) ds) → Option Bb) (recA : Aa → St) (recB : Bb → St) (x0 : Aa → X)
    (yOf : Aa → Ex.Str) (mOf : Aa → Mg) (zk : Aa → Array (Array E)) (on : Aa → Prop)
    (hon : ∀ a, on a → ∃ F, seat.ledger (recA a) = some F ∧ F.ns = ns0 ∧ F.next = k0 ∧ Sized F ∧
      LookAll P0 S (zk a) u1 u2 Reading.gl (x0 a))
    (hyes : ∀ a τ b, on a → out a τ = some b →
      decide seat p (recA a) ((rvT (ckP .two) ds τ).map noDigest) = .ok (recB b) ∧
        roundsFit (rounds p) ((rvT (ckP .two) ds τ).map noDigest) = true ∧
        ∀ r ∈ (rvT (ckP .two) ds τ).map noDigest, ∀ x ∈ r.drawn.elems, Fmt.Fld.two.okE x = true)
    (hpass : ∀ a τ b, out a τ = some b → passT (ckP .two) ds (rhoT (ckP .two) ds τ) = true)
    (qu : UShs ((closedOf P0 Λ ns0 (numsPlan p.own k0)).own (theMeans GE _ _ _)).units) (qt : Shs ((closedOf P0 Λ ns0 (numsPlan p.own k0)).own (theMeans GE _ _ _)).tail)
    (lu : UListed _ qu (landedUnits (closedOf P0 Λ ns0 (numsPlan p.own k0)) _)) (lt : TListed qt (landedTail (closedOf P0 Λ ns0 (numsPlan p.own k0)) _))
    (hM : List.Forall₂ MeetsT ds (chSp ((closedOf P0 Λ ns0 (numsPlan p.own k0)).own (theMeans GE _ _ _)).ch (ownRd _ qu qt)))
    (hA : ∀ d ∈ ds, NoAns d.items) (ε' : Err (uLT (ckP .two) ds))
    (hB : BearsT ds _ (((closedOf P0 Λ ns0 (numsPlan p.own k0)).own (theMeans GE _ _ _)).ch.eps Ex) ε') :
    (⟨uLT (ckP .two) ds, out⟩ : Reduction Aa Bb).Leads on
      (LeadsSaysRow (closedOf P0 Λ ns0 (numsPlan p.own k0)) Λ.maskOf seat p.own S Reading.gl recA recB x0 mOf zk) ε' :=
  K05_leads_row P0 Λ seat p ns0 k0 cap Reading.gl readsNz_gl Ex ⟨uLT (ckP .two) ds, out⟩ recA recB
    (fun _ τ => (rvT (ckP .two) ds τ).map noDigest) x0 yOf mOf zk on hon hyes
    (fun _ => chCarry Ex _ (ownRd _ qu qt) ds hM.length_eq) ε'
    (fun _ => chCarry_fits Ex _ _ ds hM ε' hB)
    (readsAs_carry _ Ex p.own ds qu qt lu lt hM.length_eq hA x0 _ fun a τ ⟨b, hb⟩ => hpass a τ b hb)

/-- **The same in the form for the table of joints.** -/
theorem K05_keepsW_row_at {M0 St Aa Bb W : Type} (P0 : OwnPar GE M0 X) (Λ : Lin P0 Mg) (seat : Seat St) (p : Par)
    (ns0 k0 : ℕ) {S : Attention.Shape} {rows : ℕ} {u1 u2 : UnitG} (cap : CapAt P0 S p rows u1 u2) (Ex : ExtSpec)
    (ds : List RDT) (out : Aa → Tr (uLT (ckP .two) ds) → Option Bb) (recA : Aa → St) (recB : Bb → St) (x0 : Aa → X)
    (yOf : Aa → Ex.Str) (zk : Aa → Array (Array E)) (on : Aa → Prop)
    (hon : ∀ a, on a → ∃ F, seat.ledger (recA a) = some F ∧ F.ns = ns0 ∧ F.next = k0 ∧ Sized F ∧
      LookAll P0 S (zk a) u1 u2 Reading.gl (x0 a))
    (hyes : ∀ a τ b, on a → out a τ = some b →
      decide seat p (recA a) ((rvT (ckP .two) ds τ).map noDigest) = .ok (recB b) ∧
        roundsFit (rounds p) ((rvT (ckP .two) ds τ).map noDigest) = true ∧
        ∀ r ∈ (rvT (ckP .two) ds τ).map noDigest, ∀ x ∈ r.drawn.elems, Fmt.Fld.two.okE x = true)
    (hpass : ∀ a τ b, out a τ = some b → passT (ckP .two) ds (rhoT (ckP .two) ds τ) = true)
    (qu : UShs ((closedOf P0 Λ ns0 (numsPlan p.own k0)).own (theMeans GE _ _ _)).units) (qt : Shs ((closedOf P0 Λ ns0 (numsPlan p.own k0)).own (theMeans GE _ _ _)).tail)
    (lu : UListed _ qu (landedUnits (closedOf P0 Λ ns0 (numsPlan p.own k0)) _)) (lt : TListed qt (landedTail (closedOf P0 Λ ns0 (numsPlan p.own k0)) _))
    (hM : List.Forall₂ MeetsT ds (chSp ((closedOf P0 Λ ns0 (numsPlan p.own k0)).own (theMeans GE _ _ _)).ch (ownRd _ qu qt)))
    (hA : ∀ d ∈ ds, NoAns d.items) (ε' : Err (uLT (ckP .two) ds))
    (hB : BearsT ds _ (((closedOf P0 Λ ns0 (numsPlan p.own k0)).own (theMeans GE _ _ _)).ch.eps Ex) ε')
    (part : W → Mg) (mOf : Aa → Mg) (on' : Bb → Prop) (R' : Bb → W → Prop)
    (hon' : ∀ a τ b, on a → out a τ = some b → on' b)
    (hb : BillsRow (closedOf P0 Λ ns0 (numsPlan p.own k0)) Λ.maskOf seat p.own S Reading.gl recA recB x0 zk part R')
    (pin : ∀ a τ b w, on a → out a τ = some b → R' b w → part w = mOf a) :
    (⟨uLT (ckP .two) ds, out⟩ : Reduction Aa Bb).KeepsW on on'
      (fun a w => ((closedOf P0 Λ ns0 (numsPlan p.own k0)).own (theMeans GE _ _ _)).ch.Todo (x0 a) (part w)) R' ε' :=
  K05_keepsW_row P0 Λ seat p ns0 k0 cap Reading.gl readsNz_gl Ex ⟨uLT (ckP .two) ds, out⟩ recA recB
    (fun _ τ => (rvT (ckP .two) ds τ).map noDigest) x0 yOf zk on hon hyes
    (fun _ => chCarry Ex _ (ownRd _ qu qt) ds hM.length_eq) ε'
    (fun _ => chCarry_fits Ex _ _ ds hM ε' hB)
    (readsAs_carry _ Ex p.own ds qu qt lu lt hM.length_eq hA x0 _ fun a τ ⟨b, hb⟩ => hpass a τ b hb)
    part mOf on' R' hon' hb pin

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.K05_keepsW_row_at
#print axioms VerifiableInference.Desc.First.Att.P.K05_leads_row_at
