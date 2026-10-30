-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05Keeps.lean: the law of kind K5 in the form for a table of joints
(Johnson/Desc/Plain/World.lean: KeepsW on on' R R' ε: the promise behind is kept, and for every
world w, inside the
game, the open items behind at (b, w) give the open items in front at (a, w)), by the pin
(Plain/Pinned.lean:
keepsW_of_pinned).

Main names:
  `Bills`: the one new premise with content: what stands behind, R' b w, gives the kind's bill: for
    the record (h, G)
    that the seat has laid into b and all typed data with the four ties: leftP returns some l on G,
      and UnitsBill and
    TailBill hold at l, in the world of (part w)'s mask at some entry.
  `K05_keepsW`: Kr.KeepsW on on' (fun a w => Todo (x0 a) (part w)) R' ε', from K05_leads' premises,
    Bills, "on' b for
    certain" and the pin "R' b w gives part w = mOf a".
part w: the part of the world on which the kind's bad challenges hang: the committed symbols and the
mask. mOf a: what
the oracles that a already holds decode to.

Limits: K05_leads' (a), (b), (c), CapAt, ReadsNz, LookAll, Bills, the promise behind and the pin are
premises; none is
shown in this file or in what it imports, but ReadsNz at Reading.gl (Att/K05Nz.lean).
No soundness of the protocol is claimed: the seam and the premises named are not shown.
Nothing is claimed on completeness or hiding.

-/
import Johnson.Desc.Plain.Pinned
import Johnson.Desc.First.Att.K05Leads

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb TWhole IOR OnBytes OnBytes.Model OnBytes.Model.Road Cb.Pv.Att Inst.Model
open OnBytes.Flat (CarryS)
open OnBytes.Tie.Pv.Att (UnitsH TailH seenAfter ownTrs)

variable {K : Type} [Field K] [Fintype K] {X Mg : Type}

/-- What stands behind gives K5's bill. -/
def Bills {Aa Bb St W : Type} (P : OwnPar K Mg X) (maskOf : Mg → ℕ → K) (seat : Seat St) (x : Params.AttentionRounds)
    (S : Attention.Shape) (ρ : Reading K) (recA : Aa → St) (recB : Bb → St) (x0 : Aa → X) (zk : Aa → Array (Array E))
    (part : W → Mg) (R' : Bb → W → Prop) : Prop :=
  ∀ (a : Aa) (b : Bb) (w : W), R' b w → ∀ (G : Fork) (h : Heard) (L : Lists), seat.lay (recA a) h G = some (recB b) →
    Said x h G L → ∀ (nz : BetasNz ρ L) (du : UnitsH ρ (P.own (theMeans K P.D P.C P.kap)).units)
      (dt : TailH ρ (P.own (theMeans K P.D P.C P.kap)).tail),
      UnitsOfP (P.own (theMeans K P.D P.C P.kap)).units du x.score h.scores.toList L.planes.flatten L.units →
      TailOfP dt x h L →
      UnitsVals (P.own (theMeans K P.D P.C P.kap)).units du
        (unitsAdd (ρ := ρ) (P.own (theMeans K P.D P.C P.kap)).units (landedUnits P _) L.planes.flatten L.units
          (x0 a, [])) →
      TailVals dt (tailAdd (P.own (theMeans K P.D P.C P.kap)).tail L h nz (landedTail P _)
        (seenAfter (P.own (theMeans K P.D P.C P.kap)).units du (x0 a, []))) →
      ∃ (l : Left) (entry : ℕ → ℕ → ℕ → K), leftP (geoOf S) (zk a) h G = some l ∧
        UnitsBill (P.own (theMeans K P.D P.C P.kap)).units du (x0 a, []) l.scores.toList
          (G.worldOf ρ (maskOf (part w)) entry) (part w) ∧
        TailBill dt (seenAfter (P.own (theMeans K P.D P.C P.kap)).units du (x0 a, [])) l
          (G.worldOf ρ (maskOf (part w)) entry) (part w)

/-- **K5's law in the form for the table of joints.** -/
theorem K05_keepsW {M0 St Aa Bb W : Type} (P0 : OwnPar K M0 X) (Λ : Lin P0 Mg) (seat : Seat St) (p : Par) (ns0 k0 : ℕ)
    {S : Attention.Shape} {rows : ℕ} {u1 u2 : UnitG} (cap : CapAt P0 S p rows u1 u2) (ρ : Reading K)
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
    (hb : Bills (closedOf P0 Λ ns0 (numsPlan p.own k0)) Λ.maskOf seat p.own S ρ recA recB x0 zk part R')
    (pin : ∀ a τ b w, on a → Kr.out a τ = some b → R' b w → part w = mOf a) :
    Kr.KeepsW on on'
      (fun a w => ((closedOf P0 Λ ns0 (numsPlan p.own k0)).own (theMeans K _ _ _)).ch.Todo (x0 a) (part w)) R' ε' := by
  refine Reduction.keepsW_of_pinned part mOf (fun m => ?_) pin
  refine Reduction.Leads.conseq (K05_leads P0 Λ seat p ns0 k0 cap ρ hρ Ex Kr recA recB viewOf x0 yOf (fun _ => m) zk on hon
    hyes F ε' hF hread) (fun _ h => h) fun a τ b ha hout hq => ⟨hon' a τ b ha hout, fun w hw hR => ?_⟩
  obtain ⟨_, G, h, L, _, q2, q3, nz, du, dt, t1, t2, t3, t4, q4⟩ := hq
  obtain ⟨l, entry, l1, l2, l3⟩ := hb a b w hR G h L q2 q3 nz du dt t1 t2 t3 t4
  subst hw
  exact q4 l l1 entry l2 l3

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.K05_keepsW
