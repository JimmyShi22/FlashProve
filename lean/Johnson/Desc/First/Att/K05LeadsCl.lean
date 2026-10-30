-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05LeadsCl.lean: the chain's knowledge soundness, carried to the kind's
rounds at the data heard; the bill stands on the left, in the
library's typed form (Cb/Pv/Att/End/Cl.lean: ownCl L Q u: the claims that the verifier of an
attention
sub-proof keeps of the sub-proof's own rounds; ClRan.lean: att_bill: its pull-back pays the chain's
bill).

Main names:
  `LeadsSaysCl`: Q: the seat has laid (h, G); Said; the ledger behind is Sized, has the slots of the
    one in front, and the
    slots' numbers heard are the plan's; there are typed data with the four ties; and: the
      pull-backs of all
    claims of ownCl at the run made of what was heard, at mOf a, give Todo (x0 a) (mOf a).
  `K05_leads_cl`: Kr.Leads on LeadsSaysCl ε'.

The rows, the end values, the linear claims and the join are not paid here: they stand on the left
of Q's last clause ("all
pull-backs of ownCl at the run made of what was heard hold": by the library's att_bill_iff that is
the chain's bill; and a
pull-back sets the late entries at their meant values, so "every table is true" sits in it too).
K05_cap's law of the rows, K05_join and K05_row are not spent here; the law of the rows is spent in
Att/K05Rows.lean.
Premises: those of K05_leads, and Fits Ly Q.
No soundness of the protocol is claimed: the seam and the premises named are not shown.
Nothing is claimed on completeness or hiding.

-/
import Johnson.Desc.First.Att.K05RunHeard
import Johnson.Desc.First.Att.K05Leads

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb TWhole IOR OnBytes OnBytes.Model OnBytes.Model.Road Cb.Pv.Att Inst.Model
open OnBytes.Flat (CarryS leads_carryS)
open OnBytes.Tie.Pv.Att (UnitsH TailH seenAfter ownTrs)
open Cb.Pv.Att.End (EndLay JoinLay Fits ownCl attA att_bill)

variable {K : Type} [Field K] [Fintype K] {X Mg : Type}

/-- **Q, with the library's typed ledger behind.** -/
def LeadsSaysCl {Aa Bb St : Type} (P : OwnPar K Mg X) {J₂ : Type} [Fintype J₂] [DecidableEq J₂] (Ly : EndLay P J₂)
    (Q : JoinLay P) (seat : Seat St) (x : Params.AttentionRounds) (ρ : Reading K) (recA : Aa → St) (recB : Bb → St)
    (x0 : Aa → X) (mOf : Aa → Mg) (a : Aa) (b : Bb) : Prop :=
  ∃ (F G : Fork) (h : Heard) (L : Lists), seat.ledger (recA a) = some F ∧ seat.lay (recA a) h G = some (recB b) ∧
    Said x h G L ∧ (Sized G ∧ G.ns = F.ns ∧ numsOf h = numsPlan x F.next) ∧
    ∃ (nz : BetasNz ρ L) (du : UnitsH ρ (P.own (theMeans K P.D P.C P.kap)).units)
      (dt : TailH ρ (P.own (theMeans K P.D P.C P.kap)).tail),
      UnitsOfP (P.own (theMeans K P.D P.C P.kap)).units du x.score h.scores.toList L.planes.flatten L.units ∧
      TailOfP dt x h L ∧
      UnitsVals (P.own (theMeans K P.D P.C P.kap)).units du
        (unitsAdd (ρ := ρ) (P.own (theMeans K P.D P.C P.kap)).units (landedUnits P _) L.planes.flatten L.units
          (x0 a, [])) ∧
      TailVals dt (tailAdd (P.own (theMeans K P.D P.C P.kap)).tail L h nz (landedTail P _)
        (seenAfter (P.own (theMeans K P.D P.C P.kap)).units du (x0 a, []))) ∧
      ((∀ f ∈ ownCl Ly Q (runHeard P (x0 a) du dt),
          (Cb.Sub.pullF (attA Ly (runHeard P (x0 a) du dt)) f).Holds (P.msg (mOf a))) →
        (P.own (theMeans K P.D P.C P.kap)).ch.Todo (x0 a) (mOf a))

/-- **K5's law in the plain form, with the library's typed ledger behind.** -/
theorem K05_leads_cl {M0 St Aa Bb : Type} (P0 : OwnPar K M0 X) (Λ : Lin P0 Mg) (seat : Seat St) (p : Par) (ns0 k0 : ℕ)
    {S : Attention.Shape} {rows : ℕ} {u1 u2 : UnitG} (cap : CapAt P0 S p rows u1 u2) (ρ : Reading K)
    {Good : Tri → Prop} (hρ : ReadsNz Good ρ) (Ex : ExtSpec) (Kr : Reduction Aa Bb) (recA : Aa → St) (recB : Bb → St)
    (viewOf : Aa → Tr Kr.shape → List Fmt.RoundView) (x0 : Aa → X) (yOf : Aa → Ex.Str) (mOf : Aa → Mg)
    (zk : Aa → Array (Array E)) (on : Aa → Prop)
    (hon : ∀ a, on a → ∃ F, seat.ledger (recA a) = some F ∧ F.ns = ns0 ∧ F.next = k0 ∧ Sized F ∧
      LookAll P0 S (zk a) u1 u2 ρ (x0 a))
    (hyes : ∀ a τ b, on a → Kr.out a τ = some b →
      decide seat p (recA a) (viewOf a τ) = .ok (recB b) ∧ roundsFit (rounds p) (viewOf a τ) = true ∧
        ∀ r ∈ viewOf a τ, ∀ x ∈ r.drawn.elems, Good x)
    (F : Aa → CarryS Kr.shape (((closedOf P0 Λ ns0 (numsPlan p.own k0)).own (theMeans K _ _ _)).ch.R Ex).shape)
    (ε' : Err Kr.shape)
    (hF : ∀ a, (F a).Fits (((closedOf P0 Λ ns0 (numsPlan p.own k0)).own (theMeans K _ _ _)).ch.eps Ex) ε')
    (hread : ReadsAs (closedOf P0 Λ ns0 (numsPlan p.own k0)) Ex ρ p.own viewOf x0
      (fun a τ => ∃ b, Kr.out a τ = some b) F)
    {J₂ : Type} [Fintype J₂] [DecidableEq J₂] {Ly : EndLay (closedOf P0 Λ ns0 (numsPlan p.own k0)) J₂}
    {Q : JoinLay (closedOf P0 Λ ns0 (numsPlan p.own k0))} (hFit : Fits Ly Q) :
    Kr.Leads on (LeadsSaysCl (closedOf P0 Λ ns0 (numsPlan p.own k0)) Ly Q seat p.own ρ recA recB x0 mOf) ε' := by
  intro a ha
  have hk := (ownAt_knowAt (closedOf P0 Λ ns0 (numsPlan p.own k0)) Ex (idle Ex Mg) (fun _ => ())
    (fun _ _ => True)).know (mOf a)
  refine (leads_carryS Kr _ F _ ε' hF (fun a' => (x0 a', yOf a')) (fun a' => a' = a ∧ on a') _ _ _
    (fun _ _ => trivial) ?_ (leads_of_know_id hk)) a ⟨rfl, ha⟩
  rintro a' τ b ⟨rfl, _⟩ hb
  obtain ⟨F0, hl, hns, hnx, hz, hlook⟩ := hon a' ha
  obtain ⟨hd, hfit, hgood⟩ := hyes a' τ b ha hb
  obtain ⟨F1, G, h, a1, a3, a2, hcap⟩ := K05_cap_at P0 Λ seat p _ _ _ hd (fun F' hF' => by
    rw [hl] at hF'
    cases hF'
    exact hz) cap (zk a')
  have eF : F1 = F0 := by
    rw [hl] at a1
    exact (Option.some.inj a1).symm
  subst eF
  subst hns hnx
  obtain ⟨_, _, _, zG, _, _⟩ := hear_law_paid a2 hz
  obtain ⟨L, c1, c2, _, _, c5⟩ := hcap G (fun _ _ _ hp => hp) rfl zG
  have nz := betas_nz p a2 hz hfit hgood hρ c2
  obtain ⟨du, dt, ⟨t1, t2, t3, t4, _⟩, _, _, out, _⟩ := c5 ρ nz (x0 a') hlook
  refine ⟨_, _, hread a' τ h G L nz du dt ⟨b, hb⟩ c2 c1 t1 t2 t3 t4, out Ex (yOf a'), fun hQ => ?_⟩
  obtain ⟨n1, n2⟩ := numbers_of_plan a2 hz
  refine ⟨F1, G, h, L, a1, a3, c2, ⟨zG, n2, n1⟩, nz, du, dt, t1, t2, t3, t4, fun hcl => ?_⟩
  exact (hQ () ⟨trivial, last_of_cl _ hFit (x0 a') du dt (mOf a') hcl⟩).2.2

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.K05_leads_cl
