-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/BlindAttO.lean: THE SEAT OF K5's CLAIMS THAT READS WHAT WAS HEARD
(Johnson/Desc/First/Att/SeatO.lean: seatCO) IS NOT TURNED BY AN ADDING: SO K3's "join" AND "planes"
AT THAT SEAT ARE BLIND TO THE REAL ADDING (Johnson/Desc/First/Batch/BlindAtt.lean's laws, which are
general in the seat). No Mathlib.
  `shown_of_quiet`: what was shown under a slot hangs on the number of slots and on two arrays,
      which no adding turns (Johnson/Desc/First/Batch/BlindPlanes.lean: `quiet`, `addAll_quiet`).
  `leftP_of_shown` · `ptsFrom_of_shown`: K5's road from what was heard to what its claims read looks
      at the ledger through "what was shown" alone.
  `seatCO_quiet`: the five readers. `joinAttO_blind` · `planesAttO_blind`.
Limits: laws on programs' commuting, at one seat. That K5's three runs at this seat are blind stands
in Johnson/Desc/First/Batch/BlindClaims.lean, not here. Nothing on soundness.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.First.Batch.BlindAtt
import Johnson.Desc.First.Att.SeatO

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9
open OnBytes OnBytes.Model OnBytes.K.Kc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Att.P (seatCO parCOf ParC)

theorem shown_of_quiet (F G : Fork) (h : quiet G = quiet F) : G.shown = F.shown := by
  funext j
  unfold quiet at h
  have h1 : G.ns = F.ns := congrArg (·.1) h
  have h2 : G.gotF = F.gotF := congrArg (·.2.1) h
  have h3 : G.vp = F.vp := congrArg (·.2.2.1) h
  unfold Fork.shown
  rw [h1, h2, h3]

theorem left_of_shown (F G : Fork) (hs : G.shown = F.shown) (h : Part.MaskedSum.Heard)
    (W : Array E) : First.Att.P.left G h W = First.Att.P.left F h W := by
  unfold First.Att.P.left
  rw [hs]

theorem leftKey_of_shown (F G : Fork) (hs : G.shown = F.shown) (g : First.Att.P.Geo)
    (h : Part.MaskedSum.Heard) (rho om' : Array E) :
    First.Att.P.leftKey g G h rho om' = First.Att.P.leftKey g F h rho om' := by
  unfold First.Att.P.leftKey
  rw [hs]

theorem leftP_of_shown (F G : Fork) (hs : G.shown = F.shown) (g : First.Att.P.Geo)
    (zk : Array (Array E)) (h : First.Att.P.Heard) :
    First.Att.P.leftP g zk h G = First.Att.P.leftP g zk h F := by
  unfold First.Att.P.leftP
  simp only [left_of_shown F G hs, leftKey_of_shown F G hs]

theorem ptsFrom_of_shown (F G : Fork) (hs : G.shown = F.shown) (g : First.Att.P.Geo)
    (zk : Array (Array E)) (h : First.Att.P.Heard) :
    First.Att.P.ptsFrom g zk h G = First.Att.P.ptsFrom g zk h F := by
  unfold First.Att.P.ptsFrom
  rw [leftP_of_shown F G hs]

/-- The three readers that do not look at the ledger. -/
theorem seatCO_three (c : ParC) (t : S) (q : Part) :
    (seatCO c).look (atS.set t q) = (seatCO c).look t ∧
    (seatCO c).pad (atS.set t q) = (seatCO c).pad t ∧
    (seatCO c).zk (atS.set t q) = (seatCO c).zk t := by
  cases hh : t.here with
  | between => simp [seatCO, atS, S.putLink, S.putFork, hh]
  | fin a => simp [seatCO, atS, S.putLink, S.putFork, hh]
  | mem a => simp [seatCO, atS, S.putLink, S.putFork, hh]
  | lay a => simp [seatCO, atS, S.putLink, S.putFork, hh]
  | att a => simp [seatCO, atS, S.putLink, S.putFork, hh]
  | head a =>
    cases ho : a.opened with
    | false => simp [seatCO, atS, S.putLink, S.putFork, hh, ho]
    | true => simp [seatCO, atS, S.putLink, S.putFork, hh, ho]

/-- The number of columns of one array of the ledger. -/
theorem seatCO_cols (c : ParC) : Unturned (seatCO c).cols := by
  intro t p cs G hp hG
  have hc := addAll_cols c.iU3 cs p.F G hG
  unfold colsAt at hc
  cases hh : t.here with
  | between => simp [atS, S.link?, hh] at hp
  | fin a => simp [atS, S.link?, hh] at hp
  | mem a => simp [atS, S.link?, hh] at hp
  | lay a => simp [seatCO, atS, S.putLink, S.putFork, hh]
  | att a =>
    simp [atS, S.link?, S.fork?, S.tl?, usedOf, hh] at hp
    subst hp
    simp at hc
    simp [seatCO, atS, S.putLink, S.putFork, hh, hc]
  | head a =>
    cases ho : a.opened with
    | false => simp [seatCO, atS, S.putLink, S.putFork, hh, ho]
    | true => simp [seatCO, atS, S.putLink, S.putFork, hh, ho]

/-- The points: they look at the ledger through what was shown. -/
theorem seatCO_pts (c : ParC) : Unturned (seatCO c).pts := by
  intro t p cs G hp hG
  have hpt : ∀ (zk : Array (Array E)) (h : First.Att.P.Heard),
      First.Att.P.ptsFrom c.geo zk h G = First.Att.P.ptsFrom c.geo zk h p.F :=
    ptsFrom_of_shown p.F G (shown_of_quiet p.F G (addAll_quiet cs p.F G hG)) c.geo
  cases hh : t.here with
  | between => simp [atS, S.link?, hh] at hp
  | fin a => simp [atS, S.link?, hh] at hp
  | mem a => simp [atS, S.link?, hh] at hp
  | lay a => simp [seatCO, atS, S.putLink, S.putFork, hh]
  | att a =>
    simp [atS, S.link?, S.fork?, S.tl?, usedOf, hh] at hp
    subst hp
    simp at hpt
    simp [seatCO, atS, S.putLink, S.putFork, S.heard5?, hh, hpt]
  | head a =>
    cases ho : a.opened with
    | false => simp [seatCO, atS, S.putLink, S.putFork, hh, ho]
    | true => simp [seatCO, atS, S.putLink, S.putFork, hh, ho]

/-- **The seat that reads what was heard is a quiet seat.** -/
theorem seatCO_quiet (c : ParC) : SeatQuiet (seatCO c) where
  pts := seatCO_pts c
  cols := seatCO_cols c
  look := fun t p _ G _ _ => (seatCO_three c t { p with F := G }).1
  pad := fun t p _ G _ _ => (seatCO_three c t { p with F := G }).2.1
  zk := fun t p _ G _ _ => (seatCO_three c t { p with F := G }).2.2

theorem joinAttO_blind (A : Attention.Plan) :
    Blind (addsOf atS atS_ok) (joinCalls (First.Att.P.keysOfO A)) :=
  joinAt_blind _ (seatCO_quiet _) _

theorem planesAttO_blind (lm : Nat) (A : Attention.Plan) :
    Blind (addsOf atS atS_ok) (planesCalls lm (First.Att.P.readersOfO A)) :=
  planesAt_blind lm _ (seatCO_quiet _) _

end VerifiableInference.Desc.K9
