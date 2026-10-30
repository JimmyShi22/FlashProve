-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05Law.lean: kind K5: the claims made of what was heard are the proved
chain's
out-claim, at all views: the hearing's and the rows' share, under one name, every premise named.

`K05_law`. planOk; the block's decide says yes at (s, rs); the ledger that the seat hands has its
arrays'
lengths. Then there are the ledger F in front, the ledger G behind the hearing, the record h and
lists L
with:
  (a) the seat lays just (h, G); the rounds hold just L (every item of every round; every draw); the
      rounds are `rounds p`, entry for entry;
  (b) at every ledger G' in which what is filled has stayed: Said p.own h G' L;
  (c) for every reading under which no beta of L reads 0, all letters of the proved chain with the
    plan's
      numbers, and whatever the typed side adds: there are typed data made of L such that (c1) each
      sumcheck's typed output is the part's record, read, and each target reads as the scalars
        heard;
      (c2) the chain's verifier, on the transcript joined of these data, puts out the chain's run;
        (c3)
      under the letters' claims and the rows' three equations, the chain's last claim on that run
        holds
      exactly if the kind's bill is paid.
The chain's knowledge soundness (Cb/Pv/Att/Own.lean: attOwn_knowAt) ends at that last claim, with
the
errors of Att/K05Rounds.lean.

Premises: PartHearLaw, PartRowLaw · planOk · Sized of the ledger handed · Stays along the later
steps ·
BetasNz · facts of the letters at a value: OwnFits; the letters' claims; UnitsPrem and TailPrem.
Att/K05Cap.lean pays the last three kinds at the library's letters, under the lookup's points'
premises.
By reading: a decide that says yes to all and lays a fixed record fails (a) and (c1); one that says
no to
all fails Att/K5Returns.lean's hear_iff.
Sources: what Att/K5Law.lean, K5Data.lean, K5Later.lean and K05Rounds.lean name. No routine that
runs in a
context is reached.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05Rounds
import Johnson.Desc.First.Att.K5Later

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb TWhole OnBytes OnBytes.Model OnBytes.Model.Road Johnson.L5.Layers Cb.Pv.Att
open OnBytes.Tie.Pv.Att (PscH SumH TailH UnitsH UnitsClaims seenAfter ownTrs own_out OwnFits)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.Part.MaskedSum (Fits PartHearLaw PartRowLaw)

/-- **K05_law.** -/
theorem K05_law (hearLaw : PartHearLaw) (rowLaw : PartRowLaw) {S : Type} (seat : Seat S) (p : Par)
    (hp : planOk p = true) (s s' : S) (rs : List Fmt.RoundView) (hd : decide seat p s rs = .ok s')
    (hz : ∀ F, seat.ledger s = some F → Sized F) :
    ∃ (F G : Fork) (h : Heard) (L : Lists),
      (seat.ledger s = some F ∧ seat.lay s h G = some s' ∧ RoundsAre L.rounds rs ∧
        Fits ((rounds p).map (·.entry)) rs ∧ Sized G ∧ Stays F G) ∧
      (∀ G', Stays G G' → Said p.own h G' L) ∧
      ∀ (K : Type) [Field K] [Fintype K] (ρ : Reading K), BetasNz ρ L → ∀ (M X : Type) (A : AttOwn K M X),
        OwnFits A p.own → ∀ (au : UnitsAdd A.units) (at' : TailAdd A.tail),
        ∃ (du : UnitsH ρ A.units) (dt : TailH ρ A.tail),
          (UnitsOfP A.units du p.own.score h.scores.toList L.planes.flatten L.units ∧ TailOfP dt p.own h L ∧
            UnitsVals A.units du au ∧ TailVals dt at') ∧
          (UnitsAreP A.units du h.scores.toList ∧ TailIsP dt p.own h L) ∧
          (∀ (Ex : ExtSpec) (x0 : X) (y : Ex.Str),
            (A.ch.R Ex).red.out (x0, y) (A.ch.join Ex (ownTrs A du dt)) = some (A.ch.run x0 (ownTrs A du dt), y)) ∧
          ∀ (Dn : X → M → Prop) (x0 : X) (m : M), UnitsClaims A.units du (x0, []) →
            dt.Claims (seenAfter A.units du (x0, [])) → ∀ (l : Left) (W : World K),
            UnitsPrem A.units du h.scores.toList l.scores.toList W m → TailPrem dt p.own h l W m →
            (A.ch.Last Dn (A.ch.run x0 (ownTrs A du dt)) m ↔
              Dn x0 m ∧ UnitsBill A.units du (x0, []) l.scores.toList W m ∧
                TailBill dt (seenAfter A.units du (x0, [])) l W m) := by
  obtain ⟨_, F, h, G, a1, a2, a3⟩ := (decide_lays seat p s s' rs).1 hd
  obtain ⟨L, b1, b2, b3, b4, b5⟩ := hear_law hearLaw a2 (hz F a1)
  have hfit : Fits ((rounds p).map (·.entry)) rs := by
    obtain ⟨used, c1, c2⟩ := hear_rounds p a2
    rw [List.append_nil] at c1
    rw [c1]
    exact c2
  have hne : p.own.score ≠ [] := by
    have hp' := hp
    unfold planOk at hp'
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at hp'
    exact hp'.1.1
  refine ⟨F, G, h, L, ⟨a1, a3, b1, hfit, b3, b4⟩, fun G' hs => b2.mono hs, ?_⟩
  intro K _ _ ρ nz M X A hA au at'
  obtain ⟨fu, ft⟩ := fits_of_own A p.own hA hne
  obtain ⟨du, dt, d1, d2, d3, d4⟩ := data_exist A hp b2 nz fu ft au at'
  exact ⟨du, dt, ⟨d1, d2, d3, d4⟩, b5 K ρ M X A du dt d1 d2, fun Ex x0 y => own_out A du dt Ex x0 y,
    fun Dn x0 m cu ct l W pu pt => k5_last rowLaw A du dt b2 d1 d2 Dn x0 m cu ct pu pt⟩

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.K05_law
