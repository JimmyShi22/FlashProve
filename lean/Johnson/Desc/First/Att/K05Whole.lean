-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05Whole.lean: the chain's knowledge soundness, carried to the kind's rounds
at the data heard; the bill stands on the left, in the
library's typed form. Over written rounds whose entries are the kind's ROUNDS and that send and draw
elements alone; at the field GE and the reading Reading.gl; the library's own carry inside.

Main names:
  `own_lists`: lists of the end values' names, Listed at the library's numberings, with the plan's
    lengths, exist.
  `noAns_of_plain`.
  `K05_whole`: (⟨uLT (ckP .two) ds, out⟩ : Reduction Aa Bb).Leads on LeadsSaysCl ε'.

The rows, the end values, the linear claims and the join are not paid here: they stand on the left
of Q's last clause ("all
pull-backs of ownCl at the run made of what was heard hold": by the library's att_bill_iff that is
the chain's bill; and a
pull-back sets the late entries at their meant values, so "every table is true" sits in it too).
Premises left: CapAt; the ledger in front (two numbers, Sized, LookAll); the seam (out's yes is
decide's yes on the view,
with roundsFit, every drawn triple below the prime; the tests of work passed); the written rounds
are Plain with the
kind's entries; BearsT; Fits Ly Q. LookAll only opens K05_cap_at's guard here: Att/K05WholeAny.lean
states the law without it.
yOf is spent inside alone. Q's lists and data are bound by "there are": whoever pays the left side
pays it at all lists and
data with the ties.
No soundness of the protocol is claimed: the seam and the premises named are not shown.
Nothing is claimed on completeness or hiding.

-/
import Johnson.Desc.First.Att.K05LeadsCl
import Johnson.Desc.First.Att.K05LeadsAt
import Johnson.Desc.First.Att.K05Listed
import Johnson.Desc.First.Att.K05Spec

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb TWhole IOR OnBytes OnBytes.Model OnBytes.Model.Road Cb.Pv.Att Inst.Model OnBytes.Slice OnBytes.Flat
open OnBytes.Maker Run Fo.Peel
open OnBytes.Tie.Pv.Att (recOf ownAt_fits)
open Cb.Pv.Att.End (EndLay JoinLay Fits)

variable {X Mg : Type}

/-- The lists of names exist. -/
theorem own_lists (P : OwnPar GE Mg X) (rows : ℕ) :
    ∃ (qu : UShs (P.own (theMeans GE P.D P.C P.kap)).units) (qt : Shs (P.own (theMeans GE P.D P.C P.kap)).tail),
      UListed _ qu (landedUnits P _) ∧ TListed qt (landedTail P _) ∧ ULen _ qu (recOf P rows).score ∧
        ShsLen qt (recOf P rows) := by
  obtain ⟨s3, l3, n3⟩ := sc3_listed P.D.nb
  obtain ⟨sd, ld, nd⟩ := scd_listed (size18 P.D)
  exact ⟨(⟨s3, l3.1⟩, (⟨s3, l3.1⟩, ())), ⟨s3, l3.1, s3, l3.1, s3, l3.1, s3, l3.1, sd, ld.1, s3, l3.1⟩,
    ⟨l3, l3, trivial⟩, ⟨l3, l3, l3, l3, ld, l3⟩, ⟨n3, n3, trivial⟩, ⟨n3, n3, n3, n3, nd, n3⟩⟩

theorem noAns_of_plain {ds : List RDT} (hd : ∀ d ∈ ds, Plain (toRD d)) : ∀ d ∈ ds, NoAns d.items :=
  fun d h it hi e => by
    have := (hd d h).allE it hi
    rw [e] at this
    cases this

/-- **The chain's knowledge soundness, carried to K5's written rounds at the data heard; the bill
stands on the left.** -/
theorem K05_whole {M0 St Aa Bb : Type} (P0 : OwnPar GE M0 X) (Λ : Lin P0 Mg) (seat : Seat St) (p : Par)
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
    (hd : ∀ d ∈ ds, Plain (toRD d)) (he : ds.map (·.entry) = (rounds p).map (·.entry))
    (ε' : Err (uLT (ckP .two) ds))
    (hB : BearsT ds _ (((closedOf P0 Λ ns0 (numsPlan p.own k0)).own (theMeans GE _ _ _)).ch.eps Ex) ε')
    {J₂ : Type} [Fintype J₂] [DecidableEq J₂] {Ly : EndLay (closedOf P0 Λ ns0 (numsPlan p.own k0)) J₂} {Q : JoinLay (closedOf P0 Λ ns0 (numsPlan p.own k0))} (hFit : Fits Ly Q) :
    (⟨uLT (ckP .two) ds, out⟩ : Reduction Aa Bb).Leads on
      (LeadsSaysCl (closedOf P0 Λ ns0 (numsPlan p.own k0)) Ly Q seat p.own Reading.gl recA recB x0 mOf) ε' := by
  obtain ⟨qu, qt, lu, lt, nu, nt⟩ := own_lists (closedOf P0 Λ ns0 (numsPlan p.own k0)) rows
  have hrec : p.own = recOf (closedOf P0 Λ ns0 (numsPlan p.own k0)) rows := cap.record
  have hne : p.own.score ≠ [] := by
    rw [hrec]
    simp [recOf]
  have hfit := ownAt_fits (closedOf P0 Λ ns0 (numsPlan p.own k0)) (theMeans GE _ _ _) cap.kap rows
  rw [← hrec] at hfit
  obtain ⟨fu, ft⟩ := fits_of_own ((closedOf P0 Λ ns0 (numsPlan p.own k0)).own (theMeans GE _ _ _)) p.own hfit hne
  rw [← hrec] at nu nt
  have hM := own_meets _ qu qt p fu ft nu nt hne ds hd he
  exact K05_leads_cl P0 Λ seat p ns0 k0 cap Reading.gl readsNz_gl Ex ⟨uLT (ckP .two) ds, out⟩ recA recB
    (fun _ τ => (rvT (ckP .two) ds τ).map noDigest) x0 yOf mOf zk on hon hyes
    (fun _ => chCarry Ex _ (ownRd _ qu qt) ds hM.length_eq) ε'
    (fun _ => chCarry_fits Ex _ _ ds hM ε' hB)
    (readsAs_carry _ Ex p.own ds qu qt lu lt hM.length_eq (noAns_of_plain hd) x0 _ fun a τ ⟨b, hb⟩ => hpass a τ b hb)
    hFit

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.K05_whole
#print axioms VerifiableInference.Desc.First.Att.P.own_lists
