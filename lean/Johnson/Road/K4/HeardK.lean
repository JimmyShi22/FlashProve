-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/HeardK.lean: SIX FACTS ON WHAT K4's HEARING RETURNS, in a group that is not the
first, gathered in one conjunction. One theorem at a hearing, and the same under `Plan4.Meets`
(Johnson/Road/K4/PlanMaps.lean). Nothing new is argued: each fact is a lemma of the file that is
named beside it, applied.

  `heard_K`: where `hear` returns o over the plain engine:
    (1) the reading of the negative of the program's inverse of the terms' coefficient, times the
        reading of that coefficient, is -1 (by `hinv_of`, `gl_inv`, `gl_numerals`;
        `gl_ne_of_word`, Johnson/Road/K4/OwnCoin.lean; the text refuses three words 0:
        `Led7.eps`);
    (2) the table of scales is the one that `sclOf` makes at o's own environment;
    (3) o's environment holds the public record's layout;
    (4) the number of the group's first layer;
    (5) `NormWords` (`normWords_of_hear`, Johnson/Road/K4/NormWordsOfHear.lean);
    (6) the slot of the second side's own end value follows the routed experts' slots
        (by `hearStack_public`).
  `Plan4L.heard_K`: at { par.P with tokv := tk } and the value's sizes and first layer.

PREMISES. The ledger in front has arrays of the right sizes. EVERY WORD THAT THE TAPE's ROUNDS DREW
IS BELOW THE PRIME (`SmallTape`): without it three words that are not 0 could read 0. The layout is
`layout`'s; the library's sizes agree with the shape. TWO CHOICES OF LETTERS, named: hscl: the
section's table of scales IS `sclOf hS P.sc g P.y.Lam`; hL0: the value's first layer IS g * Lam.

Limits. One direction: from a return. Equations alone: nothing on soundness.
-/
import Johnson.Road.K4.OwnLedgers
import Johnson.Road.K4.OwnCoin
import Johnson.Road.K4.NormWordsOfHear
import Johnson.Road.K4.PlanMaps
import Johnson.Road.K4.ValueSlots
import Johnson.Road.Rows.LayerEnds34Ref
import OnBytes.Desc.First.K4.StackPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.K.Kc OnBytes.Model
open OnBytes.Model.Layer (Pub HPlan2 Own layout)
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim)
open OnBytes.Desc.First.K4 (Par engFl hear hearStack_public)
open OnBytes.Desc.First.P1 (tapeEps tscIn_heard)

/-- **Six facts on what the hearing returns.** -/
theorem heard_K [scl : Scl] {P : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {F G : Fork}
    {t0 u : Tape} {o : Own} {hS : Layer.Shape} {pc : List (List String)} {D : Dim} {L0 : ℕ}
    (h : hear engFl P hp g fo F t0 = some (o, G, u)) (hF : PscRun.Sized F)
    (hg : (g == 0) = false) (hs : SmallTape t0) (hy : layout hS pc = .ok P.y) (Z : Sized hS D)
    (hscl : scl = sclOf hS P.sc g P.y.Lam) (hL0 : g * P.y.Lam = L0) :
    (∀ tT, o.H.tT = some tT →
      Reading.gl.val (negE (invE tT.p.eps)) * Reading.gl.val tT.p.eps = -1) ∧
    scl = sclOf hS o.v.sc o.v.g o.v.y.Lam ∧ o.v.y = P.y ∧ o.v.g * o.v.y.Lam = L0 ∧
    NormWords o.v D ∧ o.K.sB0 = o.K.sA0 + (1 + (1 + P.y.LamM)) := by
  subst hscl
  obtain ⟨vy, vsc, vg, _⟩ := env_of_hear h
  obtain ⟨H1, hd2, tT0, F4, F7, F8, G1, G1', G2, G3, G3', G4, Ld⟩ := own_led7 hF h hg
  have L := laySizes_of_layout hy
  refine ⟨?_, by rw [vsc, vg, vy], vy, by rw [vg, vy]; exact hL0, ?_, ?_⟩
  · intro tT e
    rw [Ld.kTT] at e
    obtain rfl := Option.some.inj e
    show Reading.gl.val (negE (invE tT0.p.eps)) * Reading.gl.val tT0.p.eps = -1
    have e1 : tT0.p.eps =
        tapeEps ((((ksOf P hp).tcP (t0.drop 1)).drop 1).drop (P.y.h.lt + 3)) :=
      (tscIn_heard Ld.c3).2.2.2.2.2.2.2.2.1
    have hsm : SmallTape ((((ksOf P hp).tcP (t0.drop 1)).drop 1).drop (P.y.h.lt + 3)) :=
      ((((((hs.drop 1).drop 1).drop 1).drop _).drop 1).drop 1).drop _
    have hk : okE tT0.p.eps = true := by
      rw [e1]
      exact small_eps hsm
    exact Rows.hinv_of gl_numerals (gl_ne_of_word hk Ld.eps) (Rows.gl_inv _)
  · have N := normWords_of_hear h D L.NN (L.Lam.trans (nl_tie Z).symm)
    rw [L.shape] at N
    exact N
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, a1, a2, _⟩ :=
      hearStack_public Ld.c4
    rw [a2, a1]
    omega

/-- **The same under `Meets`**, at the value with its slots and orders laid. -/
theorem Plan4L.heard_K [scl : Scl] {M X : Type} {QL : Plan4L Cb.Gl.E M X} {par : Par}
    {hS : Layer.Shape} {pcl : List (List String)} (A : QL.plan.Meets par hS pcl) {tk : Array Nat}
    {fo : Forest.Heard} {F G : Fork} {t0 u : Tape} {o : Own}
    (h : hear engFl { par.P with tokv := tk } par.hp par.g fo F t0 = some (o, G, u))
    (hF : PscRun.Sized F) (hs : SmallTape t0)
    (hscl : scl = sclOf hS par.P.sc par.g par.P.y.Lam) (hL0 : par.g * par.P.y.Lam = QL.L0) :
    (∀ tT, o.H.tT = some tT →
      Reading.gl.val (negE (invE tT.p.eps)) * Reading.gl.val tT.p.eps = -1) ∧
    scl = sclOf hS o.v.sc o.v.g o.v.y.Lam ∧ o.v.y = par.P.y ∧
    o.v.g * o.v.y.Lam = QL.plan.full.ip.L0 ∧ NormWords o.v QL.plan.full.D ∧
    o.K.sB0 = o.K.sA0 + (1 + (1 + par.P.y.LamM)) := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := OnBytes.Road.K4.heard_K (P := { par.P with tokv := tk })
    (hS := hS) (pc := pcl) (D := QL.plan.D) (L0 := QL.L0) h hF A.hg hs A.hy A.Z hscl hL0
  exact ⟨a1, a2, a3, a4, a5, a6⟩

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.heard_K
#print axioms OnBytes.Road.K4.Plan4L.heard_K
