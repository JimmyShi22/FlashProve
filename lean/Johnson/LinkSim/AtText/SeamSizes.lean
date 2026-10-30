-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/AtText/SeamSizes.lean: the public premises on sizes along the stages, at the
challenges of the protocol.
Terms: Johnson/LinkSim/Spec.lean; for the prover's algorithm, Johnson/LinkSim/AtText/Defs.lean.

What this file proves. Both statements hold for every rounds' description ds.
  Spec.possLen, possLen   at every verifier message, round n of the protocol has sampled exactly
               cntD ds n positions, the number that the description declares (by fitsDrawn_run,
               Johnson/Prover/Link/ChainRounds.lean).
  Spec.fitsOfOk, fitsOfOk   suppose round n has sampled cnt n positions, for every n. If the test
               fitsOk accepts cnt, then FitsBody holds.

Why. The statements that the prover's algorithm and the simulator's algorithm disclose the same up
to a shift of the coins (Spec.linkShift, SpecShift.lean; and the form that carries over to a finite
type of coins, Spec.linkShiftIn, SpecShiftIn.lean) have public premises on sizes (Sizes, FitsBody).
All but one kind of their conditions are numbers of the plan. The other kind says how many positions
a round has sampled. This file proves that this number is the declared one, at the challenges of the
protocol, taken as hash blocks over the field GF (ckP .two). It also reduces FitsBody to a Boolean
test.

How it fits. SeamAtFull3.lean evaluates the test at the full-size parameters and so proves Sizes
there (fr_sizes); ShortTailAtFull.lean uses possLen. possLen and fitsOfOk are used in the proof of
homeExact (Johnson/LinkSim/AtHome/Home.lean), through SeamAtFull3.lean,
Johnson/LinkSim/AtHome/HomeTies.lean and home_upTo (Johnson/LinkSim/AtHome/RoadCloses.lean).

The other names (namespace OnBytes.LinkSim.Seam).
  cntD ds n       the number of positions that round n of the rounds' description declares; 0
               where there is no such round.
  possLen_of      the induction behind possLen.
  fitsOk cnt rest cur o   FitsBody with the number of sampled positions of round n replaced by
               cnt n: a Boolean test. Whether two stages' sizes fit is evaluated by decCsFit
               (Johnson/Top/H/StageJ.lean).

Limits.
- Only at one choice of challenge types: challenges as hash blocks, over the field GF (ckP .two).

Notes. The test is evaluated in SeamAtFull3.lean, not here.
Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.AtText.SpecShift
import Johnson.Prover.Link.LinkView
import Johnson.Prover.Link.ChainRounds
import Johnson.Top.H.StageJ

set_option autoImplicit false

noncomputable section

namespace OnBytes.LinkSim.Seam
open OnBytes OnBytes.Slice
open OnBytes.LinkSim.AtText
open H2K.Pub (sgOf)
open Johnson.Prover.Link
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run (ckP)
open TypedOracleCompiler.Run.PQ (RD uL drawnSL)

/-- The number of positions that round n declares; 0 where there is no such round. -/
def cntD (ds : List RD) (n : ℕ) : ℕ := ((ds[n]?).map (·.entry.poss)).getD 0

/-- If each round's challenges have the declared number of positions, then so does the entry read
at any round n. -/
theorem possLen_of : ∀ (ds : List RD) (Ds : List Fmt.Drawn),
    List.Forall₂ (fun (w : RD) (D : Fmt.Drawn) => D.poss.length = w.entry.poss) ds Ds →
    ∀ n, (drawsOf Ds n).poss.length = cntD ds n
  | [], [], _, _ => rfl
  | _ :: _, _ :: _, .cons h _, 0 => h
  | _ :: ds, _ :: Ds, .cons _ t, n + 1 => possLen_of ds Ds t n

/-- Statement only; proved as possLen below. **At every verifier message, round n has sampled the
declared number of positions.** -/
def Spec.possLen : Prop :=
  ∀ (ds : List RD) (ρ : Rho (uL (ckP .two) ds)) (n : ℕ),
    (drawsOf (drawnSL (ckP .two) ds ρ) n).poss.length = cntD ds n

theorem possLen : Spec.possLen := fun ds ρ n =>
  possLen_of ds _ ((fitsDrawn_run ds ρ).imp fun _ _ h => h.poss) n

/-- FitsBody with the numbers of sampled positions as a variable: a Boolean test. -/
def fitsOk (cnt : ℕ → ℕ) : List Fmt.M1.Stage → Fmt.M1.Stage → ℕ → Bool
  | [], cur, o =>
    decide (cnt (o + 1) ≤ (sgOf cur).C.r) && decide (cnt (o + 1) ≤ (sgOf cur).Z.r) &&
      decide ((sgOf cur).h = 0) && decide ((sgOf cur).g = 0)
  | next :: rest, cur, o =>
    decide (cnt (o + 2 + ((sgOf cur).h + (sgOf cur).g)) ≤ (sgOf cur).C.r) &&
      decide (cnt (o + 2 + ((sgOf cur).h + (sgOf cur).g)) ≤ (sgOf cur).Z.r) &&
      decide ((sgOf cur).h + 2 * (sgOf cur).g + 1 ≤ (sgOf cur).Z.l) &&
      decide (CsFit (sgOf cur) (sgOf next)) &&
      fitsOk cnt rest next (o + ((sgOf cur).h + (sgOf cur).g) + 3)

/-- Statement only; proved as fitsOfOk below. If the test accepts, FitsBody holds. -/
def Spec.fitsOfOk : Prop :=
  ∀ (D : ℕ → Fmt.Drawn) (cnt : ℕ → ℕ), (∀ n, (D n).poss.length = cnt n) →
    ∀ (rest : List Fmt.M1.Stage) (cur : Fmt.M1.Stage) (o : ℕ),
      fitsOk cnt rest cur o = true → FitsBody D rest cur o

theorem fitsOfOk : Spec.fitsOfOk := by
  intro D cnt hD rest
  induction rest with
  | nil =>
    intro cur o h
    unfold fitsOk at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    unfold FitsBody
    rw [hD]
    exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩
  | cons next rest ih =>
    intro cur o h
    unfold fitsOk at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    unfold FitsBody
    rw [hD]
    exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, ih next _ h.2⟩

end OnBytes.LinkSim.Seam

#print axioms OnBytes.LinkSim.Seam.possLen
#print axioms OnBytes.LinkSim.Seam.fitsOfOk
