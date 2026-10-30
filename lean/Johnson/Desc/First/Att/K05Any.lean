-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05Any.lean: the chain's knowledge soundness, carried to the kind's rounds at
the data heard; the bill stands on the left, in the
library's typed form: at every parameter record P with kap = 4 whose plan's record is recOf P rows.
No
point of the lookup, no shape, no place and no number of the ledger is a premise.

Main names:
  `data_core`: from the hearing's return at a Sized ledger: the lists; Said; and for every reading
    with BetasNz and every
    first statement: typed data with the four ties, the letters' claims, and the reduction's output
      on the joined transcript.
  `K05_leads_any`: Kr.Leads on (LeadsSaysCl P Ly Q …) ε'.

The rows, the end values, the linear claims and the join are not paid here: they stand on the left
of Q's last clause ("all
pull-backs of ownCl at the run made of what was heard hold": by the library's att_bill_iff that is
the chain's bill; and a
pull-back sets the late entries at their meant values, so "every table is true" sits in it too).
The places come back where they are spent: Att/K05Rows.lean and Att/K05Port.lean.
The first half of cap_core's proof (Att/K05Cap.lean) goes the way of data_core's.
No soundness of the protocol is claimed: the seam and the premises named are not shown.
Nothing is claimed on completeness or hiding.

-/
import Johnson.Desc.First.Att.K05LeadsCl

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb TWhole IOR OnBytes OnBytes.Model OnBytes.Model.Road Johnson.L5.Layers Cb.Pv.Att Inst.Model
open OnBytes.Flat (CarryS leads_carryS)
open OnBytes.Tie.Pv.Att (PscH SumH TailH UnitsH UnitsClaims seenAfter recOf sc3Num scdNum ownTrs own_out ownAt_fits)
open Cb.Pv.Att.End (EndLay JoinLay Fits)

variable {K : Type} [Field K] [Fintype K] {X Mg : Type}

/-- **The data, from the hearing's return.** -/
theorem data_core (P : OwnPar K Mg X) (hk4 : P.kap = 4) (rows : ℕ) {F G : Fork} {rs : List Fmt.RoundView} {h : Heard}
    (hh : hear (recOf P rows) (F, rs, 0) = some (h, G, [], 0)) (hzF : Sized F) :
    ∃ L : Lists, RoundsAre L.rounds rs ∧ Said (recOf P rows) h G L ∧
      ∀ (ρ : Reading K) (nz : BetasNz ρ L) (x0 : X),
        ∃ (du : UnitsH ρ (P.own (theMeans K P.D P.C P.kap)).units) (dt : TailH ρ (P.own (theMeans K P.D P.C P.kap)).tail),
          (UnitsOfP (P.own (theMeans K P.D P.C P.kap)).units du (recOf P rows).score h.scores.toList L.planes.flatten L.units ∧
            TailOfP dt (recOf P rows) h L ∧
            UnitsVals (P.own (theMeans K P.D P.C P.kap)).units du
              (unitsAdd (ρ := ρ) (P.own (theMeans K P.D P.C P.kap)).units (landedUnits P _) L.planes.flatten L.units (x0, [])) ∧
            TailVals dt (tailAdd (P.own (theMeans K P.D P.C P.kap)).tail L h nz (landedTail P _) (seenAfter (P.own (theMeans K P.D P.C P.kap)).units du (x0, [])))) ∧
          (UnitsClaims (P.own (theMeans K P.D P.C P.kap)).units du (x0, []) ∧ dt.Claims (seenAfter (P.own (theMeans K P.D P.C P.kap)).units du (x0, []))) ∧
          ∀ (Ex : ExtSpec) (y : Ex.Str), ((P.own (theMeans K P.D P.C P.kap)).ch.R Ex).red.out (x0, y) ((P.own (theMeans K P.D P.C P.kap)).ch.join Ex (ownTrs (P.own (theMeans K P.D P.C P.kap)) du dt)) =
            some ((P.own (theMeans K P.D P.C P.kap)).ch.run x0 (ownTrs (P.own (theMeans K P.D P.C P.kap)) du dt), y) := by
  obtain ⟨L, b1, b2, _, _, _⟩ := hear_law_paid hh hzF
  refine ⟨L, b1, b2, fun ρ nz x0 => ?_⟩
  have hne : (recOf P rows).score ≠ [] := by simp [recOf]
  obtain ⟨fu, ft⟩ := fits_of_own (P.own (theMeans K P.D P.C P.kap)) _ (ownAt_fits P _ hk4 rows) hne
  rw [← b2.nPlanes, ← planes_length b2.planes] at fu
  obtain ⟨du, d1, d3⟩ := units_exist (P.own (theMeans K P.D P.C P.kap)).units _ _ _ _ b2.units fu nz.units
    (unitsAdd (ρ := ρ) (P.own (theMeans K P.D P.C P.kap)).units (landedUnits P _) L.planes.flatten L.units (x0, []))
  obtain ⟨e1, e2⟩ := tail_exists (P.own (theMeans K P.D P.C P.kap)).tail b2 hne nz ft
    (tailAdd (P.own (theMeans K P.D P.C P.kap)).tail L h nz (landedTail P _) (seenAfter (P.own (theMeans K P.D P.C P.kap)).units du (x0, [])))
  have cu : UnitsClaims (P.own (theMeans K P.D P.C P.kap)).units du (x0, []) :=
    (units_claims _ du _ _ _ _ (landedUnits P _) _ d1 d3).2
      (units_targets_of_last _ du _ _ _ _ _ (last_own _ _) b2.units d1)
  have ct := (tail_claims (P.own (theMeans K P.D P.C P.kap)).tail L h nz (landedTail P _) (seenAfter (P.own (theMeans K P.D P.C P.kap)).units du (x0, []))).2
    (value_tail_targets P _ rows b2 nz (landedTail P _) (fun i => by simp [landedTail, sc3Num]) _)
  exact ⟨du, _, ⟨d1, e1, d3, e2⟩, ⟨cu, ct⟩, fun Ex y => own_out _ du _ Ex x0 y⟩

/-- **The law at every P.** -/
theorem K05_leads_any {St Aa Bb : Type} (P : OwnPar K Mg X) (hk4 : P.kap = 4) (rows : ℕ) (seat : Seat St) (p : Par)
    (hrec : p.own = recOf P rows) (ρ : Reading K) {Good : Tri → Prop} (hρ : ReadsNz Good ρ) (Ex : ExtSpec)
    (Kr : Reduction Aa Bb) (recA : Aa → St) (recB : Bb → St) (viewOf : Aa → Tr Kr.shape → List Fmt.RoundView) (x0 : Aa → X)
    (yOf : Aa → Ex.Str) (mOf : Aa → Mg) (on : Aa → Prop)
    (hon : ∀ a, on a → ∀ F, seat.ledger (recA a) = some F → Sized F)
    (hyes : ∀ a τ b, on a → Kr.out a τ = some b →
      decide seat p (recA a) (viewOf a τ) = .ok (recB b) ∧ roundsFit (rounds p) (viewOf a τ) = true ∧
        ∀ r ∈ viewOf a τ, ∀ x ∈ r.drawn.elems, Good x)
    (F : Aa → CarryS Kr.shape ((P.own (theMeans K P.D P.C P.kap)).ch.R Ex).shape) (ε' : Err Kr.shape)
    (hF : ∀ a, (F a).Fits ((P.own (theMeans K P.D P.C P.kap)).ch.eps Ex) ε')
    (hread : ReadsAs P Ex ρ p.own viewOf x0 (fun a τ => ∃ b, Kr.out a τ = some b) F)
    {J₂ : Type} [Fintype J₂] [DecidableEq J₂] {Ly : EndLay P J₂} {Q : JoinLay P} (hFit : Fits Ly Q) :
    Kr.Leads on (LeadsSaysCl P Ly Q seat p.own ρ recA recB x0 mOf) ε' := by
  intro a ha
  have hk := (ownAt_knowAt P Ex (idle Ex Mg) (fun _ => ()) (fun _ _ => True)).know (mOf a)
  refine (leads_carryS Kr _ F _ ε' hF (fun a' => (x0 a', yOf a')) (fun a' => a' = a ∧ on a') _ _ _
    (fun _ _ => trivial) ?_ (leads_of_know_id hk)) a ⟨rfl, ha⟩
  rintro a' τ b ⟨rfl, _⟩ hb
  obtain ⟨hd, hfit, hgood⟩ := hyes a' τ b ha hb
  obtain ⟨_, F1, h, G, a1, a2, a3⟩ := (decide_lays seat p _ _ _).1 hd
  have hz := hon a' ha F1 a1
  have a2' := a2
  rw [hrec] at a2'
  obtain ⟨L, c1, c2, c5⟩ := data_core P hk4 rows a2' hz
  rw [← hrec] at c2
  have nz := betas_nz p a2 hz hfit hgood hρ c2
  obtain ⟨du, dt, ⟨t1, t2, t3, t4⟩, _, out⟩ := c5 ρ nz (x0 a')
  rw [← hrec] at t1 t2
  refine ⟨_, _, hread a' τ h G L nz du dt ⟨b, hb⟩ c2 c1 t1 t2 t3 t4, out Ex (yOf a'), fun hQ => ?_⟩
  obtain ⟨n1, n2⟩ := numbers_of_plan a2 hz
  obtain ⟨_, _, _, zG, _, _⟩ := hear_law_paid a2 hz
  refine ⟨F1, G, h, L, a1, a3, c2, ⟨zG, n2, n1⟩, nz, du, dt, t1, t2, t3, t4, fun hcl => ?_⟩
  exact (hQ () ⟨trivial, last_of_cl _ hFit (x0 a') du dt (mOf a') hcl⟩).2.2

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.data_core
#print axioms VerifiableInference.Desc.First.Att.P.K05_leads_any
