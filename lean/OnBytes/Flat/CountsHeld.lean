-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Flat/CountsHeld.lean: error counts for a chain's written rounds that bear the counts of a
typed protocol along partial maps (`CarryS.Fits`, OnBytes/Flat/CarrySkip.lean) and are below
2^(-target).

A theorem that carries soundness from typed rounds to written rounds along a `CarryS` asks for
counts of the written rounds with two properties: they bear the typed counts, and they are small.
Here the counts are written down: at a round that is read as a typed round, the typed count times
a weight; at a skipped round 0. Definitions, statements and proofs. No protocol occurs here.

Main names, all in the namespace `OnBytes.Flat.Held`:
  `cnts s ws s' ε`: the counts of the written rounds s from the typed counts ε and a list ws:
    `some w` for a round that is read as the next typed round, at the weight w; `none` for a
    skipped round.
  `Follows F ws`: F steps and skips as ws says, whatever was sent, and at a step at most w written
    verifier messages go to one typed message.
  `fits_cnts`: `Follows F ws → F.Fits ε (cnts s ws s' ε)`.
  `wsOf ds marks`: the list for the written rounds of ds: at a mark `true` the weight of the
    format's sampler.
  `CountsL ds rs marks s' ε`: at each round that is read, the typed count is at most the planner's
    number for the round's error times the number of the round's typed values; the lists and the
    typed rounds are used up together.
  `cnts_below_held`: `Held s r d` for each pair, and `CountsL`, give `Err.Below (cnts … (wsOf ds
    marks) s' ε) (2⁻¹ ^ s.target)`, by `held_round` (OnBytes/Slice/HeldRound.lean) round by round.
  `cnts_below_finishHeld`: the same from the planner's own `finishHeld`, `Aligned` and `sideB`
    (OnBytes/Flat/HeldAll.lean), against the plan's rounds of the chain (`chainRounds`).

Limits: that a typed count is at most the planner's number is asked, round by round: it is what
OnBytes/Slice/HeldKinds.lean and the files behind it answer kind by kind; there an element other
than 0 has p ^ 3 - 1 typed values, not p ^ 3. That a map's fibres are within the sampler's weight
is asked in `Follows`: for the map `chalTo d g` it is `chalTo_fib` (OnBytes/Slice/Draws.lean).
Nothing says that a count bounds a prover's chance. What `held_round` does not claim is not
claimed here.
-/
import OnBytes.Flat.CarrySkip
import OnBytes.Flat.HeldAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Flat.Held
open Iop Prob _root_.Run _root_.Run.PQ OnBytes.Params OnBytes.Slice OnBytes.Flat
open scoped ENNReal

/-- The counts of the written rounds. -/
def cnts : (s : Shape) → List (Option ℕ) → (s' : Shape) → Err s' → Err s
  | [], _, _, _ => ()
  | _ :: s, some w :: ws, _ :: s', (e, ε) => (e * w, cnts s ws s' ε)
  | _ :: s, some _ :: ws, [], ε => (0, cnts s ws [] ε)
  | _ :: s, none :: ws, s', ε => (0, cnts s ws s' ε)
  | _ :: s, [], s', ε => (0, cnts s [] s' ε)

/-- F steps and skips as the list says; at a step the fibres are within the weight. -/
def Follows : {s s' : Shape} → CarryS s s' → List (Option ℕ) → Prop
  | _, _, .nil, _ => True
  | _, _, .step (r := r) (r' := r') _ fc k, some w :: ws =>
      (∀ (m : r.Msg) (c' : r'.Chal), cnt (fun c => fc m c = some c') ≤ w) ∧
        ∀ m c, Follows (k m c) ws
  | _, _, .step _ _ _, _ => False
  | _, _, .skip k, none :: ws => ∀ m c, Follows (k m c) ws
  | _, _, .skip _, _ => False

/-- The counts bear the typed counts. -/
theorem fits_cnts : ∀ {s s' : Shape} (F : CarryS s s') (ws : List (Option ℕ)) (ε : Err s'),
    Follows F ws → F.Fits ε (cnts s ws s' ε)
  | _, _, .nil, _, _, _ => trivial
  | _, _, .step _ _ k, some w :: ws, (_, ε), h =>
    ⟨⟨w, h.1, le_rfl⟩, fun m c => fits_cnts (k m c) ws ε (h.2 m c)⟩
  | _, _, .skip k, none :: ws, ε, h => fun m c => fits_cnts (k m c) ws ε (h m c)

/-- The list for written rounds: at a mark the weight of the format's sampler. -/
def wsOf : List RD → List Bool → List (Option ℕ)
  | d :: ds, true :: ms => some (bsRound .two d.entry d.kind).w :: wsOf ds ms
  | _ :: ds, false :: ms => none :: wsOf ds ms
  | _, _ => []

/-- Each typed count is at most the planner's number for its round. -/
def CountsL : List RD → List PlanRound → List Bool → (s' : Shape) → Err s' → Prop
  | [], [], [], [], _ => True
  | d :: ds, r :: rs, true :: ms, _ :: s', (e, ε) =>
      (e : ℚ) ≤ r.error.val * (nVals (Fmt.dsOf d.entry d.kind) : ℚ) ∧ CountsL ds rs ms s' ε
  | _ :: ds, _ :: rs, false :: ms, s', ε => CountsL ds rs ms s' ε
  | _, _, _, _, _ => False

theorem cnts_below_held (st : Setting) : ∀ (ds : List RD) (rs : List PlanRound) (ms : List Bool)
    (s' : Shape) (ε : Err s'), List.Forall₂ (fun d r => Held st r d) ds rs →
    CountsL ds rs ms s' ε →
    Err.Below (cnts (uL (ckP .two) ds) (wsOf ds ms) s' ε) ((2 : ℝ≥0∞)⁻¹ ^ st.target)
  | [], _, _, _, _, _, _ => trivial
  | d :: ds, r :: rs, true :: ms, _ :: s', (e, ε), .cons H Hs, hc =>
    ⟨held_round st H.p H.degree r d H.entry H.log H.nz H.work H.holds e hc.1,
      cnts_below_held st ds rs ms s' ε Hs hc.2⟩
  | _ :: ds, _ :: rs, false :: ms, s', ε, .cons _ Hs, hc =>
    ⟨by simp, cnts_below_held st ds rs ms s' ε Hs hc⟩

/-- From the planner's own `finishHeld`. The routine x and the setting are variables. -/
theorem cnts_below_finishHeld (st : Setting) (scope : Scope) (x : Planning Unit) (P : Planned)
    (h : finishHeld st scope x = .ok P) (ds : List RD) (ha : Aligned ds P)
    (hs : sideB P = true) (ms : List Bool) (s' : Shape) (ε : Err s')
    (hc : CountsL ds (chainRounds P) ms s' ε) :
    Err.Below (cnts (uL (ckP .two) ds) (wsOf ds ms) s' ε) ((2 : ℝ≥0∞)⁻¹ ^ st.target) :=
  cnts_below_held st ds (chainRounds P) ms s' ε (held_all st scope x P h ds ha hs) hc

end OnBytes.Flat.Held

#print axioms OnBytes.Flat.Held.fits_cnts
#print axioms OnBytes.Flat.Held.cnts_below_held
#print axioms OnBytes.Flat.Held.cnts_below_finishHeld
