-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05LeadsRow.lean: K05_leads and K05_keepsW with K05_row in K05_cap's place:
what stands behind is no
longer the raw bill but what the claims and the later kinds say.

Main names:
  `Behind`: there are the claims' record i (its numbers the shape's; its points pointsOf's of h and
    l), the lookup's
    record and Kc with: SayAt in the world of m's mask; UnitsLin and UnitsMeans; TailLin and the
      five EndsMean.
  `LeadsSaysRow`: Q: as LeadsSays, with "Behind gives Todo" for every l that leftP returns on G.
  `K05_leads_row`: Kr.Leads on LeadsSaysRow ε', from K05_leads' premises.
  `BillsRow`: what stands behind, R' b w, gives, for the (h, G) laid into b and all typed data with
    the four ties: leftP
    returns some l on G, and Behind at l, part w and some entry.
  `K05_keepsW_row`: Kr.KeepsW on on' (fun a w => Todo (x0 a) (part w)) R' ε'.

Limits. Every premise of K05_leads and K05_keepsW stays a premise. leftP's return is asked of R'
(BillsRow). "Some
entry": SayAt's and the readers' forms read the world's entries (the array of tables); which entry
function is meant is
not said here; Todo follows at any. TailLin holds the letter owF (Att/K05Row.lean unfolds it).
No soundness of the protocol is claimed: the seam and the premises named are not shown.
Nothing is claimed on completeness or hiding.

-/
import Johnson.Desc.First.Att.K05Keeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb TWhole IOR OnBytes OnBytes.Model OnBytes.Model.Road Cb.Pv.Att Inst.Model
open OnBytes.Flat (CarryS leads_carryS)
open OnBytes.Tie.Pv.Att (UnitsH TailH seenAfter ownTrs)
open K5Law (SayAt PointsAre unitReader endsE endsV endsK endsH oldOf sum3Back)

variable {K : Type} [Field K] [Fintype K] {X Mg : Type}

/-- What the claims and the later kinds say behind K5's rounds. -/
def Behind (P : OwnPar K Mg X) (maskOf : Mg → ℕ → K) (S : Attention.Shape) (ρ : Reading K) (zk : Array (Array E))
    (x0 : X) (G : Fork) (h : Heard) (L : Lists) (nz : BetasNz ρ L) (du : UnitsH ρ (P.own (theMeans K P.D P.C P.kap)).units)
    (dt : TailH ρ (P.own (theMeans K P.D P.C P.kap)).tail) (l : Left) (m : Mg) (entry : ℕ → ℕ → ℕ → K) : Prop :=
  ∃ (gL : Forest.Heard) (i : Runs.In) (Kc : ℕ), i.g = geoOf S ∧ PointsAre i.g zk h l i.p ∧
    SayAt ρ (G.worldOf ρ (maskOf m) entry) S gL i Kc ∧
    (UnitsLin (P.own (theMeans K P.D P.C P.kap)).units du (x0, []) m ∧
      UnitsMeans (P.own (theMeans K P.D P.C P.kap)).units du
        (unitsAdd (ρ := ρ) (P.own (theMeans K P.D P.C P.kap)).units (landedUnits P _) L.planes.flatten L.units (x0, [])) 0 (unitReader S gL i Kc)
        (G.worldOf ρ (maskOf m) entry) m) ∧
    (TailLin dt (seenAfter (P.own (theMeans K P.D P.C P.kap)).units du (x0, [])) m ∧
      EndsMean (P.own (theMeans K P.D P.C P.kap)).tail.sE dt.dE
        (tailAdd (P.own (theMeans K P.D P.C P.kap)).tail L h nz (landedTail P _) (seenAfter (P.own (theMeans K P.D P.C P.kap)).units du (x0, []))).aE
        (endsE (oldOf S gL i) Kc) (G.worldOf ρ (maskOf m) entry) m ∧
      EndsMean (P.own (theMeans K P.D P.C P.kap)).tail.sVM dt.dVM
        (tailAdd (P.own (theMeans K P.D P.C P.kap)).tail L h nz (landedTail P _) (seenAfter (P.own (theMeans K P.D P.C P.kap)).units du (x0, []))).aM
        (endsV (oldOf S gL i) Kc (sum3Back i.p.d.vpm) i.t.tVM i.t.ptM false i.t.qVM) (G.worldOf ρ (maskOf m) entry) m ∧
      EndsMean (P.own (theMeans K P.D P.C P.kap)).tail.sVD dt.dVD
        (tailAdd (P.own (theMeans K P.D P.C P.kap)).tail L h nz (landedTail P _) (seenAfter (P.own (theMeans K P.D P.C P.kap)).units du (x0, []))).aVD
        (endsV (oldOf S gL i) Kc (sum3Back i.p.d.vpd) i.t.tVD i.t.ptD true i.t.qVD) (G.worldOf ρ (maskOf m) entry) m ∧
      EndsMean (P.own (theMeans K P.D P.C P.kap)).tail.sD dt.dD
        (tailAdd (P.own (theMeans K P.D P.C P.kap)).tail L h nz (landedTail P _) (seenAfter (P.own (theMeans K P.D P.C P.kap)).units du (x0, []))).aD
        (endsK (oldOf S gL i) Kc) (G.worldOf ρ (maskOf m) entry) m ∧
      EndsMean (P.own (theMeans K P.D P.C P.kap)).tail.sH dt.dH
        (tailAdd (P.own (theMeans K P.D P.C P.kap)).tail L h nz (landedTail P _) (seenAfter (P.own (theMeans K P.D P.C P.kap)).units du (x0, []))).aH
        (endsH (oldOf S gL i) Kc) (G.worldOf ρ (maskOf m) entry) m)

/-- **Q, in the row's form.** -/
def LeadsSaysRow {Aa Bb St : Type} (P : OwnPar K Mg X) (maskOf : Mg → ℕ → K) (seat : Seat St)
    (x : Params.AttentionRounds) (S : Attention.Shape) (ρ : Reading K) (recA : Aa → St) (recB : Bb → St) (x0 : Aa → X)
    (mOf : Aa → Mg) (zk : Aa → Array (Array E)) (a : Aa) (b : Bb) : Prop :=
  ∃ (F G : Fork) (h : Heard) (L : Lists), seat.ledger (recA a) = some F ∧ seat.lay (recA a) h G = some (recB b) ∧
    Said x h G L ∧
    ∃ (nz : BetasNz ρ L) (du : UnitsH ρ (P.own (theMeans K P.D P.C P.kap)).units) (dt : TailH ρ (P.own (theMeans K P.D P.C P.kap)).tail),
      UnitsOfP (P.own (theMeans K P.D P.C P.kap)).units du x.score h.scores.toList L.planes.flatten L.units ∧
      TailOfP dt x h L ∧
      UnitsVals (P.own (theMeans K P.D P.C P.kap)).units du
        (unitsAdd (ρ := ρ) (P.own (theMeans K P.D P.C P.kap)).units (landedUnits P _) L.planes.flatten L.units (x0 a, [])) ∧
      TailVals dt (tailAdd (P.own (theMeans K P.D P.C P.kap)).tail L h nz (landedTail P _) (seenAfter (P.own (theMeans K P.D P.C P.kap)).units du (x0 a, []))) ∧
      ∀ l, leftP (geoOf S) (zk a) h G = some l → ∀ entry : ℕ → ℕ → ℕ → K,
        Behind P maskOf S ρ (zk a) (x0 a) G h L nz du dt l (mOf a) entry → (P.own (theMeans K P.D P.C P.kap)).ch.Todo (x0 a) (mOf a)

/-- **K5's law in the plain form, the row's.** -/
theorem K05_leads_row {M0 St Aa Bb : Type} (P0 : OwnPar K M0 X) (Λ : Lin P0 Mg) (seat : Seat St) (p : Par) (ns0 k0 : ℕ)
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
      (fun a τ => ∃ b, Kr.out a τ = some b) F) :
    Kr.Leads on
      (LeadsSaysRow (closedOf P0 Λ ns0 (numsPlan p.own k0)) Λ.maskOf seat p.own S ρ recA recB x0 mOf zk) ε' := by
  intro a ha
  have hk := (ownAt_knowAt (closedOf P0 Λ ns0 (numsPlan p.own k0)) Ex (idle Ex Mg) (fun _ => ())
    (fun _ _ => True)).know (mOf a)
  refine (leads_carryS Kr _ F _ ε' hF (fun a' => (x0 a', yOf a')) (fun a' => a' = a ∧ on a') _ _ _
    (fun _ _ => trivial) ?_ (leads_of_know_id hk)) a ⟨rfl, ha⟩
  rintro a' τ b ⟨rfl, _⟩ hb
  obtain ⟨F0, hl, hns, hnx, hz, hlook⟩ := hon a' ha
  obtain ⟨hd, hfit, hgood⟩ := hyes a' τ b ha hb
  obtain ⟨F1, G, h, a1, a3, a2, hrow⟩ := K05_row_at P0 Λ seat p _ _ _ hd (fun F' hF' => by
    rw [hl] at hF'
    cases hF'
    exact hz) cap (zk a')
  have eF : F1 = F0 := by
    rw [hl] at a1
    exact (Option.some.inj a1).symm
  subst eF
  subst hns hnx
  obtain ⟨_, _, _, zG, _, _⟩ := hear_law_paid a2 hz
  obtain ⟨L, c1, c2, _, _, c5⟩ := hrow G (fun _ _ _ hp => hp) rfl zG
  have nz := betas_nz p a2 hz hfit hgood hρ c2
  obtain ⟨du, dt, ⟨t1, t2, t3, t4, _, _⟩, _, out, hiff⟩ := c5 ρ nz (x0 a') hlook
  refine ⟨_, _, hread a' τ h G L nz du dt ⟨b, hb⟩ c2 c1 t1 t2 t3 t4, out Ex (yOf a'), fun hQ => ?_⟩
  refine ⟨F1, G, h, L, a1, a3, c2, nz, du, dt, t1, t2, t3, t4, fun l hl' entry hB => ?_⟩
  obtain ⟨gL, i, Kc, g1, g2, g3, g4, g5⟩ := hB
  have hLast := ((hiff l hl' (fun _ _ => True) (mOf a') entry gL i Kc g1 g2 g3).1).2 ⟨trivial, g4, g5⟩
  exact (hQ () ⟨trivial, hLast⟩).2.2

/-- What stands behind gives Behind. -/
def BillsRow {Aa Bb St W : Type} (P : OwnPar K Mg X) (maskOf : Mg → ℕ → K) (seat : Seat St)
    (x : Params.AttentionRounds) (S : Attention.Shape) (ρ : Reading K) (recA : Aa → St) (recB : Bb → St) (x0 : Aa → X)
    (zk : Aa → Array (Array E)) (part : W → Mg) (R' : Bb → W → Prop) : Prop :=
  ∀ (a : Aa) (b : Bb) (w : W), R' b w → ∀ (G : Fork) (h : Heard) (L : Lists), seat.lay (recA a) h G = some (recB b) →
    Said x h G L → ∀ (nz : BetasNz ρ L) (du : UnitsH ρ (P.own (theMeans K P.D P.C P.kap)).units) (dt : TailH ρ (P.own (theMeans K P.D P.C P.kap)).tail),
      UnitsOfP (P.own (theMeans K P.D P.C P.kap)).units du x.score h.scores.toList L.planes.flatten L.units →
      TailOfP dt x h L →
      UnitsVals (P.own (theMeans K P.D P.C P.kap)).units du
        (unitsAdd (ρ := ρ) (P.own (theMeans K P.D P.C P.kap)).units (landedUnits P _) L.planes.flatten L.units (x0 a, [])) →
      TailVals dt (tailAdd (P.own (theMeans K P.D P.C P.kap)).tail L h nz (landedTail P _) (seenAfter (P.own (theMeans K P.D P.C P.kap)).units du (x0 a, []))) →
      ∃ (l : Left) (entry : ℕ → ℕ → ℕ → K), leftP (geoOf S) (zk a) h G = some l ∧
        Behind P maskOf S ρ (zk a) (x0 a) G h L nz du dt l (part w) entry

/-- **K5's law in the form for the table of joints, the row's.** -/
theorem K05_keepsW_row {M0 St Aa Bb W : Type} (P0 : OwnPar K M0 X) (Λ : Lin P0 Mg) (seat : Seat St) (p : Par)
    (ns0 k0 : ℕ) {S : Attention.Shape} {rows : ℕ} {u1 u2 : UnitG} (cap : CapAt P0 S p rows u1 u2) (ρ : Reading K)
    {Good : Tri → Prop} (hρ : ReadsNz Good ρ) (Ex : ExtSpec) (Kr : Reduction Aa Bb) (recA : Aa → St) (recB : Bb → St)
    (viewOf : Aa → Tr Kr.shape → List Fmt.RoundView) (x0 : Aa → X) (yOf : Aa → Ex.Str) (zk : Aa → Array (Array E))
    (on : Aa → Prop)
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
    (part : W → Mg) (mOf : Aa → Mg) (on' : Bb → Prop) (R' : Bb → W → Prop)
    (hon' : ∀ a τ b, on a → Kr.out a τ = some b → on' b)
    (hb : BillsRow (closedOf P0 Λ ns0 (numsPlan p.own k0)) Λ.maskOf seat p.own S ρ recA recB x0 zk part R')
    (pin : ∀ a τ b w, on a → Kr.out a τ = some b → R' b w → part w = mOf a) :
    Kr.KeepsW on on'
      (fun a w => ((closedOf P0 Λ ns0 (numsPlan p.own k0)).own (theMeans K _ _ _)).ch.Todo (x0 a) (part w)) R' ε' := by
  refine Reduction.keepsW_of_pinned part mOf (fun m => ?_) pin
  refine Reduction.Leads.conseq (K05_leads_row P0 Λ seat p ns0 k0 cap ρ hρ Ex Kr recA recB viewOf x0 yOf (fun _ => m) zk
    on hon hyes F ε' hF hread) (fun _ h => h) fun a τ b ha hout hq => ⟨hon' a τ b ha hout, fun w hw hR => ?_⟩
  obtain ⟨_, G, h, L, _, q2, q3, nz, du, dt, t1, t2, t3, t4, q4⟩ := hq
  obtain ⟨l, entry, l1, l2⟩ := hb a b w hR G h L q2 q3 nz du dt t1 t2 t3 t4
  subst hw
  exact q4 l l1 entry l2

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.K05_leads_row
#print axioms VerifiableInference.Desc.First.Att.P.K05_keepsW_row
