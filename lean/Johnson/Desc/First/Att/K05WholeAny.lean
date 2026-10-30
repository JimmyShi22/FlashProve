-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05WholeAny.lean: the chain's knowledge soundness, carried to the kind's
rounds at the data heard; the bill stands on the left, in the
library's typed form: at every parameter record P over GE with kap = 4 whose plan's record is
recOf P rows; the library's own carry inside; the written counts written out (bearErr).

Main names:
  `K05_whole_any`: (⟨uLT (ckP .two) ds, out⟩ : Reduction Aa Bb).Leads on (LeadsSaysCl P Ly Q seat
    p.own Reading.gl recA recB x0
    mOf) (bearErr ds _ (A.ch.eps Ex)).

Premises, all: kap = 4; the plan's record; the seat's ledger in front is Sized; the seam (out's yes
is decide's yes on
"rvT (ckP .two) ds τ, digests struck", with roundsFit and every drawn triple below the prime; out's
yes gives that the tests
of work pass); the written rounds are Plain with the kind's entries; Fits Ly Q.
The rows, the end values, the linear claims and the join are not paid here: they stand on the left
of Q's last clause ("all
pull-backs of ownCl at the run made of what was heard hold": by the library's att_bill_iff that is
the chain's bill; and a
pull-back sets the late entries at their meant values, so "every table is true" sits in it too).
That the left side is met at a run made of a view that the verifier accepts is not shown.
That the written counts are small shares: Att/K05Bears.lean (bear_below), Att/K05Held.lean
(held_of_check).
No soundness of the protocol is claimed: the seam and the premises named are not shown.
Nothing is claimed on completeness or hiding.

-/
import Johnson.Desc.First.Att.K05Any
import Johnson.Desc.First.Att.K05Whole
import Johnson.Desc.First.Att.K05Bears

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb TWhole IOR OnBytes OnBytes.Model OnBytes.Model.Road Cb.Pv.Att Inst.Model OnBytes.Slice OnBytes.Flat
open OnBytes.Maker Run Fo.Peel
open OnBytes.Tie.Pv.Att (recOf ownAt_fits)
open Cb.Pv.Att.End (EndLay JoinLay Fits)

variable {X Mg : Type}

theorem K05_whole_any {St Aa Bb : Type} (P : OwnPar GE Mg X) (hk4 : P.kap = 4) (rows : ℕ) (seat : Seat St) (p : Par)
    (hrec : p.own = recOf P rows) (Ex : ExtSpec) (ds : List RDT) (out : Aa → Tr (uLT (ckP .two) ds) → Option Bb)
    (recA : Aa → St) (recB : Bb → St) (x0 : Aa → X) (yOf : Aa → Ex.Str) (mOf : Aa → Mg) (on : Aa → Prop)
    (hon : ∀ a, on a → ∀ F, seat.ledger (recA a) = some F → Sized F)
    (hyes : ∀ a τ b, on a → out a τ = some b →
      decide seat p (recA a) ((rvT (ckP .two) ds τ).map noDigest) = .ok (recB b) ∧
        roundsFit (rounds p) ((rvT (ckP .two) ds τ).map noDigest) = true ∧
        ∀ r ∈ (rvT (ckP .two) ds τ).map noDigest, ∀ x ∈ r.drawn.elems, Fmt.Fld.two.okE x = true)
    (hpass : ∀ a τ b, out a τ = some b → passT (ckP .two) ds (rhoT (ckP .two) ds τ) = true)
    (hd : ∀ d ∈ ds, Plain (toRD d)) (he : ds.map (·.entry) = (rounds p).map (·.entry))
    {J₂ : Type} [Fintype J₂] [DecidableEq J₂] {Ly : EndLay P J₂} {Q : JoinLay P} (hFit : Fits Ly Q) :
    (⟨uLT (ckP .two) ds, out⟩ : Reduction Aa Bb).Leads on
      (LeadsSaysCl P Ly Q seat p.own Reading.gl recA recB x0 mOf) (bearErr ds _ ((P.own (theMeans GE P.D P.C P.kap)).ch.eps Ex)) := by
  obtain ⟨qu, qt, lu, lt, nu, nt⟩ := own_lists P rows
  have hne : p.own.score ≠ [] := by
    rw [hrec]
    simp [recOf]
  have hfit := ownAt_fits P (theMeans GE _ _ _) hk4 rows
  rw [← hrec] at hfit nu nt
  obtain ⟨fu, ft⟩ := fits_of_own (P.own (theMeans GE P.D P.C P.kap)) p.own hfit hne
  have hM := own_meets _ qu qt p fu ft nu nt hne ds hd he
  exact K05_leads_any P hk4 rows seat p hrec Reading.gl readsNz_gl Ex ⟨uLT (ckP .two) ds, out⟩ recA recB
    (fun _ τ => (rvT (ckP .two) ds τ).map noDigest) x0 yOf mOf on hon hyes
    (fun _ => chCarry Ex _ (ownRd _ qu qt) ds hM.length_eq) _
    (fun _ => chCarry_fits Ex _ _ ds hM _ (bears_self ds _ _))
    (readsAs_carry _ Ex p.own ds qu qt lu lt hM.length_eq (noAns_of_plain hd) x0 _ fun a τ ⟨b, hb⟩ => hpass a τ b hb)
    hFit

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.K05_whole_any
