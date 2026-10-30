-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/RecCompile/PublicLift.lean: public digests that are answers of the one hash function
cost a bound nothing: the induction of `arm_pr_pub` (LinkAnsPublic.lean), said once, with the
makers' side abstract.

An experiment over one hash function has a makers' part, which puts out a value y (what the makers
have made, with their logs of strings), and then a verdict on y. Suppose the verdict and the event
hang on a value d, and that at every fixed d the event "yes, and bad at d" has probability at most B
against every lawful maker. Then the same bound holds where d is what a public algorithm without
coins `Pub` gets from the function itself, run behind the makers' part.

What is asked, of a set Pt of public strings:
  * the makers: a value can be wired in at a string (`wireM`): the wired maker runs under g as the
    maker under g with the value laid in there, but for its logs, from which the entries at the
    string are struck (`strikeY`); a lawful maker stays lawful;
  * the verdict: it does not see what is struck, and never asks a string of Pt;
  * the event: striking the entries at a string of Pt does not undo it;
  * `Pub`: no coins; strings of Pt alone; none twice.

  `expD`      the experiment at a fixed d
  `verdP`, `expP`   the public algorithm, then the verdict at its output; the experiment with it
  `pub_lift`  the bound
  `wire2`, `strike2`, `run2`, `run2_wire`   the makers' part in two stages, and its law

How: one public point at a time, as in the head of LinkAnsPublic.lean. The bound is an average over
the public digests of bounds against makers that may hang on them.

Limits: a lemma on experiments. It says nothing of an arm, a wire or a program.

Terms: lean/GLOSSARY.md.

-/
import Johnson.TypedOracleCompiler.RecCompile.LinkAnsPublic

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Compile.Batch.Cms
open _root_.Compile TypedOracleCompiler.Iop Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Iop.BatchH4 (ProverLaw VerLaw)
open scoped ENNReal
open OnBytes.Slice

variable {lam : ℕ}

/-- The experiment at a fixed d: the makers' part, then the verdict at d. -/
def expD {D Y : Type} (verd : D → Y → OComp (rom lam) Bool) (d : D) (c : OComp (rom lam) Y) :
    OComp (rom lam) (Y × D × Bool) :=
  c.bind fun y => (verd d y).bind fun b => OComp.pure (y, d, b)

/-- The verdict with the public algorithm in front. -/
def verdP {D Y : Type} (verd : D → Y → OComp (rom lam) Bool) (Pub : OComp (rom lam) D) (y : Y) :
    OComp (rom lam) (D × Bool) :=
  Pub.bind fun d => (verd d y).bind fun b => OComp.pure (d, b)

/-- The experiment with the public algorithm: the makers' part; the public algorithm; the verdict at
its output. -/
def expP {D Y : Type} (verd : D → Y → OComp (rom lam) Bool) (Pub : OComp (rom lam) D)
    (c : OComp (rom lam) Y) : OComp (rom lam) (Y × D × Bool) :=
  c.bind fun y => (verdP verd Pub y).bind fun v => OComp.pure (y, v)

/-- Public digests cost nothing. If at every fixed d the event "the verdict says yes and Bad d" has
probability at most B against every maker with ok (base), then it has probability at most B where d
is the output of a public algorithm run behind the makers' part. Premises: the law of the wired
maker (hrun); ok is kept by wiring (hok); the verdict is the same program on a struck outcome (hvs)
and at no d asks a string of Pt (hno); Bad d is kept when the entries at a string of Pt are struck
(hbs); the public algorithm has no coins, asks strings of Pt alone and none twice. -/
theorem pub_lift {D Y M : Type} (run : M → OComp (rom lam) Y)
    (wireM : List Bool → (Fin lam → Bool) → M → M) (strikeY : List Bool → Y → Y)
    (hrun : ∀ s r Mk g, (run (wireM s r Mk)).runEager g =
      ((run Mk).runEager (g.set () s r)).map (strikeY s))
    (ok : M → Prop) (hok : ∀ s r Mk, ok Mk → ok (wireM s r Mk))
    (verd : D → Y → OComp (rom lam) Bool) (hvs : ∀ d s y, verd d (strikeY s y) = verd d y)
    (Pt : List Bool → Prop) (hno : ∀ d y, (verd d y).AsksIn fun _ s => ¬ Pt s)
    (Bad : D → Y → Prop) (hbs : ∀ d s y, Pt s → Bad d y → Bad d (strikeY s y)) (B : ℝ≥0∞)
    (base : ∀ d Mk, ok Mk →
      Rom.Pr (expD verd d (run Mk)) (fun _ => {x | x.2.2 = true ∧ Bad x.2.1 x.1}) ≤ B) :
    ∀ (Pub : OComp (rom lam) D), Pub.NoCoin → (Pub.AsksIn fun _ s => Pt s) → NoRepeat Pub →
      ∀ Mk, ok Mk →
        Rom.Pr (expP verd Pub (run Mk)) (fun _ => {x | x.2.2 = true ∧ Bad x.2.1 x.1}) ≤ B := by
  intro Pub
  induction Pub with
  | pure d =>
    intro _ _ _ Mk hq
    have e : expP verd (OComp.pure d) (run Mk) = expD verd d (run Mk) := by
      simp only [expP, expD, verdP, OComp.bind_assoc, OComp.bind]
    rw [e]
    exact base d Mk hq
  | sample n k _ =>
    intro hc
    exact hc.elim
  | query o s k ih =>
    intro hc hp hr Mk hq
    cases o
    unfold Rom.Pr
    rw [lintegral_U_resample () s (measurable_PrCoins _ _)]
    refine (expect_mono _ fun r => ?_).trans (le_of_eq (expect_const _ _))
    refine le_trans (MeasureTheory.lintegral_mono fun g => ?_)
      (ih r (hc r) (hp.2 r) (hr r).2 (wireM s r Mk) (hok s r Mk hq))
    have hv : ∀ y, (verdP verd (OComp.query () s k) y).runEager (g.set () s r) =
        (verdP verd (k r) y).runEager g := by
      intro y
      have h1 : (verdP verd (OComp.query () s k) y).runEager (g.set () s r) =
          (verdP verd (k r) y).runEager (g.set () s r) := by
        simp only [verdP, OComp.bind, OComp.runEager, Fam.set_self]
      rw [h1]
      refine runEager_set s r g _ ?_
      have ha : ∀ d, ((verd d y).bind fun b =>
          (OComp.pure (d, b) : OComp (rom lam) (D × Bool))).AsksIn fun _ s' => s' ≠ s := by
        intro d
        refine OComp.AsksIn.bind ?_
          (OComp.AsksIn.mono (P := fun _ s' => ¬ Pt s') (Q := fun _ s' => s' ≠ s)
            (fun _ s' h e => h (by rw [e]; exact hp.1)) (hno d y))
        intro _
        trivial
      exact OComp.AsksIn.bind ha (hr r).1
    have hvs' : ∀ y, verdP verd (k r) (strikeY s y) = verdP verd (k r) y := by
      intro y
      simp only [verdP, hvs]
    unfold PrCoins expP
    rw [OComp.runEager_bind, OComp.runEager_bind, hrun, PMF.bind_map]
    refine pr_bind_le_bind _ _ _ _ _ fun y _ => ?_
    simp only [Function.comp, OComp.runEager_bind, hv, hvs']
    refine pr_bind_le_bind _ _ _ _ _ fun v _ => ?_
    refine pr_pure_le_pure ?_
    rintro ⟨hb, hbad⟩
    exact ⟨hb, hbs v.1 s y hp.1 hbad⟩

/-! ## The makers' part in two stages -/

/-- The makers' part in two stages: a first algorithm, with its log; a second, handed a part of what
the first has put out, with its log. -/
def run2 {α β St : Type} (st : α → St) (M : OComp (rom lam) α × (St → OComp (rom lam) β)) :
    OComp (rom lam) ((α × Trace (rom lam)) × (β × Trace (rom lam))) :=
  M.1.withTrace.bind fun a => (M.2 (st a.1)).withTrace.bind fun b => OComp.pure (a, b)

/-- a value wired into both stages -/
def wire2 {α β St : Type} (s : List Bool) (r : Fin lam → Bool)
    (M : OComp (rom lam) α × (St → OComp (rom lam) β)) :
    OComp (rom lam) α × (St → OComp (rom lam) β) :=
  (wire s r M.1, fun x => wire s r (M.2 x))

/-- the entries at a string struck from both logs -/
def strike2 {α β : Type} (s : List Bool)
    (y : (α × Trace (rom lam)) × (β × Trace (rom lam))) :
    (α × Trace (rom lam)) × (β × Trace (rom lam)) :=
  ((y.1.1, strike s y.1.2), (y.2.1, strike s y.2.2))

/-- The law of the wired makers in two stages. -/
theorem run2_wire {α β St : Type} (st : α → St) (s : List Bool) (r : Fin lam → Bool)
    (M : OComp (rom lam) α × (St → OComp (rom lam) β)) (g : Fam (rom lam)) :
    (run2 st (wire2 s r M)).runEager g =
      ((run2 st M).runEager (g.set () s r)).map (strike2 s) := by
  unfold run2 wire2
  simp only [OComp.runEager_bind, withTrace_wire, PMF.bind_map, PMF.map_bind, OComp.runEager,
    PMF.pure_map, Function.comp_def]
  rfl

end TypedOracleCompiler.Compile.Batch.Cms
