-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05Leads.lean: the law of kind K5 in the plain form
(Johnson/Desc/Plain/Leads.lean:
Kr.Leads on Q ε': on the statements with "on" the prover has lost, at the errors ε', towards
"whatever the verifier
puts out stands in Q to the statement in front"). The library's proved chain of attention's own
rounds is carried
(Plain/Carry.lean: leads_carryS), not proved anew. Stated over an abstract reduction Kr over written
rounds; what
ties Kr to the kind's block at its stretch stands in four named parameters and premises:
  (a) `viewOf`, `hyes`: Kr's yes at (a, τ) is decide's yes of the kind's block on the view viewOf a
    τ, which passes
      the general step's roundsFit, and whose drawn triples are all Good.
  (b) `F`, `hF`: a reading of Kr's written transcripts as the typed chain's, whose counts bear the
    chain's errors.
  (c) `ReadsAs`: where Kr says yes and Said holds, that reading's image of τ is the typed transcript
    made of the lists that the view holds, at data with
      all four ties (UnitsOfP, TailOfP, and the values' ties UnitsVals, TailVals at the library's
        numberings). The first
      two leave the end values free, and these stand in the typed transcript.
  (d) `mOf`: the world is a function of the statement in front (what its oracles hold). The
    library's KnowAt fixes the
      committed messages outside the game, since the bad challenges hang on them: so the chain's
        Know is spent, at
      each a, at mOf a.

Main names:
  (By Att/K05One.lean two data with the four ties are one and the rounds fix the lists: so ReadsAs
    asks one thing of F
    at each (a, τ).)
  `leads_of_know_id`: a Know whose extractor hands the witness through gives Leads towards "for all
    w: RB b w gives
    RA a w".
  `LeadsSays`: Q: the seat has laid (h, G); Said; there are typed data made of the lists heard (the
    four ties are said); and for every l that
    leftP returns on G: the kind's bill at l, in the world of mOf a's mask, gives the chain's first
      joint's Todo at
    (x0 a, mOf a). (By Att/K05Front.lean Todo gives own2, and own1 where a position has at most 2 ^
      kap bits.)
  `K05_leads`: Kr.Leads on LeadsSays ε'.

This is the kind's own block without the lookup: Dn is True and the base joint says nothing, so Q
ends at Todo alone;
for the identities that ride on the lookup's point the lookup must stand in front.
"on" must give: the seat's ledger in front is some F with F.ns = ns0, F.next = k0, Sized F; and
LookAll at x0 a.
Paid inside: K05_cap_at, betas_nz, ownAt_knowAt.
Limits. It is not a closed caller: (a) to (d), CapAt, ReadsNz and LookAll are premises; none is
shown in this file or
in what it imports, but ReadsNz at Reading.gl (Att/K05Nz.lean). The bill is judged here at the
ledger right behind the
hearing; the claims are gathered later (K05_cap speaks of every later ledger).
No soundness of the protocol is claimed: the seam and the premises named are not shown.
Nothing is claimed on completeness or hiding.

-/
import Johnson.Desc.Plain.Carry
import Johnson.Desc.First.Att.K05CapAt
import Johnson.Desc.First.Att.K05Nz
import Johnson.Desc.First.Att.K05One

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb TWhole IOR OnBytes OnBytes.Model OnBytes.Model.Road Cb.Pv.Att Inst.Model
open OnBytes.Flat (CarryS leads_carryS)
open OnBytes.Tie.Pv.Att (UnitsH TailH seenAfter ownTrs)

/-- A Know whose extractor hands the witness through: world by world. -/
theorem leads_of_know_id {A B W : Type} {Kr : Reduction A B} {on : A → Prop} {RA : A → W → Prop}
    {RB : B → W → Prop} {ε : Err Kr.shape} (h : Kr.Know on RA RB (fun _ _ w => w) ε) :
    Kr.Leads on (fun a b => ∀ w, RB b w → RA a w) ε :=
  fun a ha => Doomed.mono _ _ (fun _ hτ b hb w hw => hτ b w hb hw) (h a ha)

variable {K : Type} [Field K] [Fintype K] {X Mg : Type}

/-- The joint that says nothing. -/
def idle (Ex : ExtSpec) (Mg : Type) : Rels Unit Unit Ex (Mg × Unit) :=
  ⟨fun _ _ _ => True, fun _ _ => True, fun _ => True, fun _ => ()⟩

/-- **(c)**: the reading's image of a written transcript is the typed transcript made of the lists
that the view holds. -/
def ReadsAs {Aa : Type} {sh : Shape} (P : OwnPar K Mg X) (Ex : ExtSpec) (ρ : Reading K) (x : Params.AttentionRounds)
    (viewOf : Aa → Tr sh → List Fmt.RoundView) (x0 : Aa → X) (yes : Aa → Tr sh → Prop)
    (F : Aa → CarryS sh ((P.own (theMeans K P.D P.C P.kap)).ch.R Ex).shape) : Prop :=
  ∀ (a : Aa) (τ : Tr sh) (h : Heard) (G : Fork) (L : Lists) (nz : BetasNz ρ L)
    (du : UnitsH ρ (P.own (theMeans K P.D P.C P.kap)).units)
    (dt : TailH ρ (P.own (theMeans K P.D P.C P.kap)).tail), yes a τ → Said x h G L →
    RoundsAre L.rounds (viewOf a τ) →
    UnitsOfP (P.own (theMeans K P.D P.C P.kap)).units du x.score h.scores.toList L.planes.flatten L.units →
    TailOfP dt x h L →
    UnitsVals (P.own (theMeans K P.D P.C P.kap)).units du
      (unitsAdd (ρ := ρ) (P.own (theMeans K P.D P.C P.kap)).units (landedUnits P _) L.planes.flatten L.units
        (x0 a, [])) →
    TailVals dt (tailAdd (P.own (theMeans K P.D P.C P.kap)).tail L h nz (landedTail P _)
      (seenAfter (P.own (theMeans K P.D P.C P.kap)).units du (x0 a, []))) →
    (F a).tr τ = some ((P.own (theMeans K P.D P.C P.kap)).ch.join Ex (ownTrs (P.own (theMeans K P.D P.C P.kap)) du dt))

/-- **Q.** -/
def LeadsSays {Aa Bb St : Type} (P : OwnPar K Mg X) (maskOf : Mg → ℕ → K) (seat : Seat St) (x : Params.AttentionRounds)
    (S : Attention.Shape) (ρ : Reading K) (recA : Aa → St) (recB : Bb → St) (x0 : Aa → X) (mOf : Aa → Mg)
    (zk : Aa → Array (Array E)) (a : Aa) (b : Bb) : Prop :=
  ∃ (F G : Fork) (h : Heard) (L : Lists), seat.ledger (recA a) = some F ∧ seat.lay (recA a) h G = some (recB b) ∧
    Said x h G L ∧
    ∃ (nz : BetasNz ρ L) (du : UnitsH ρ (P.own (theMeans K P.D P.C P.kap)).units)
      (dt : TailH ρ (P.own (theMeans K P.D P.C P.kap)).tail),
      UnitsOfP (P.own (theMeans K P.D P.C P.kap)).units du x.score h.scores.toList L.planes.flatten L.units ∧
      TailOfP dt x h L ∧
      UnitsVals (P.own (theMeans K P.D P.C P.kap)).units du
        (unitsAdd (ρ := ρ) (P.own (theMeans K P.D P.C P.kap)).units (landedUnits P _) L.planes.flatten L.units
          (x0 a, [])) ∧
      TailVals dt (tailAdd (P.own (theMeans K P.D P.C P.kap)).tail L h nz (landedTail P _)
        (seenAfter (P.own (theMeans K P.D P.C P.kap)).units du (x0 a, []))) ∧
      ∀ l, leftP (geoOf S) (zk a) h G = some l → ∀ entry : ℕ → ℕ → ℕ → K,
        UnitsBill (P.own (theMeans K P.D P.C P.kap)).units du (x0 a, []) l.scores.toList
          (G.worldOf ρ (maskOf (mOf a)) entry) (mOf a) →
        TailBill dt (seenAfter (P.own (theMeans K P.D P.C P.kap)).units du (x0 a, [])) l
          (G.worldOf ρ (maskOf (mOf a)) entry) (mOf a) →
        (P.own (theMeans K P.D P.C P.kap)).ch.Todo (x0 a) (mOf a)

/-- **K5's law in the plain form.** -/
theorem K05_leads {M0 St Aa Bb : Type} (P0 : OwnPar K M0 X) (Λ : Lin P0 Mg) (seat : Seat St) (p : Par) (ns0 k0 : ℕ)
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
    Kr.Leads on (LeadsSays (closedOf P0 Λ ns0 (numsPlan p.own k0)) Λ.maskOf seat p.own S ρ recA recB x0 mOf zk) ε' := by
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
  obtain ⟨du, dt, ⟨t1, t2, t3, t4, _⟩, _, _, out, hiff⟩ := c5 ρ nz (x0 a') hlook
  refine ⟨_, _, hread a' τ h G L nz du dt ⟨b, hb⟩ c2 c1 t1 t2 t3 t4, out Ex (yOf a'), fun hQ => ?_⟩
  refine ⟨F1, G, h, L, a1, a3, c2, nz, du, dt, t1, t2, t3, t4, fun l hl' entry hu ht => ?_⟩
  have hLast := (hiff l hl' (fun _ _ => True) (mOf a') entry).2 ⟨trivial, hu, ht⟩
  exact (hQ () ⟨trivial, hLast⟩).2.2

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.K05_leads
