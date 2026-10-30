-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/Fire/ArmAsked.lean: the tie of the entry file to the entry's arm of the compiled
verifier, and the bound on that arm, both said of ONE TERM ON FILES: read the files by a reading
that asks the oracle, then run the arm, which asks the same oracle through its coding. The maker of
the bound is the files' author, then this reading.

Definitions, statements and proofs; general in the arm's input r (`ArmIn`, Johnson/Top/TieArm.lean)
and in the reading. What it is for: limit 3 of Johnson/Top/Fire/ArmPair.lean ends "by no theorem is
the maker of the bound the files' author, then this reading". Here that is a theorem. The reading at
a ground: Johnson/Top/Fire/ArmAskedAt.lean.

Main names (namespace `OnBytes.K.Fire`):
  `AskReader r tT`: a reading of the files into what the arm takes in, as an oracle computation
    without coins that asks at most tT strings.
  `chkArm Y d`: the one term. `chkArm_det`: under every oracle g its value is the value of the
    reading under g, then `verdict r g` (ArmPair.lean).
  `makerOf Y A z0`: the files' author A, then the reading. `makerOf_queries`: t + tT.
    `makerOf_law`: its output and log under g: the author's files read, and the author's log with
    the reading's (`askedLog`) behind it.
  `SoundSays Y εs`, `bound_files`: from `BoundSays r εs`: the same expression at t + tT bounds the
    probability, over the author's own run, that `chkArm` says yes on the author's files while
    what the arm promises fails of the value that the reading made.
  `Y.Agrees Z R`: at the oracle made from the hash, the reading makes of the files of a run what
    the tie's reading R makes of them.
  `ZeroSays Y Z`, `zero_files`: from `TieSays r Z R` and `Y.Agrees Z R`: `TieSays`' text with its
    last clause said of `chkArm` on the run's own files.

Limits.
  1. All seven limits of ArmPair.lean's head stand, but the last sentence of its limit 3. In short,
     of its limits 1, 2 and 6: THE ARM IS A SIBLING OF THE ENTRY ARM OF `innerCompiledVerifier`,
     NOT THAT ARM: made of the same definitions, run without the strict format, at an object whose
     link is written anew, at a wiring that serves this check alone. No theorem makes it a part of
     `innerCompiledVerifier` at one input.
  2. `ZeroSays` and `SoundSays` speak of one term and are composed nowhere. The first is at one
     fixed function, Lean's BLAKE2b; the second over a random function. No probability is said of
     the program's yes.
  3. The log. The words of which the arm's promise speaks are read off the author's log WITH THE
     READING'S QUESTIONS BEHIND IT: what only the reading asked counts as known to the author. That
     is the weaker way: the promise is the easier to keep. OnBytes/K/Oracle/ArmO.lean, on another
     checker, has the author's log alone.
  4. Nothing here ties a reading to a program: `SoundSays` holds of every reading with the two laws,
     of one that returns nothing too. What ties it is `Agrees`, at one oracle.
  5. That under a random function `chkArm` says yes on any files is not shown.
  For proofs only; no program imports this file.

-/
import Johnson.Top.Fire.ArmPair
import OnBytes.Slice.WrapBetween
import OnBytes.Slice.Guard
import OnBytes.K.Left.Arm

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal

namespace OnBytes.K.Fire

open Rom
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run (bytesToDig oBits)
open OnBytes.Slice (runEager_withTrace_det runEager_bind_pure det_withTrace_fst)
open OnBytes.Shell (Steps opsIO World Event wholeReads kindOf Asked)
open OnBytes.K.Left (filesOf)

/-- A reading of the files that asks the oracle, into what the arm takes in. tT: a bound on its
queries. -/
structure AskReader (r : ArmIn) (tT : ℕ) where
  /-- the reading -/
  rd : OnBytes.Slice.Shapes.Files → OComp (rom 256) (Option (OutLA 256 r.L r.aL))
  /-- it tosses no coin -/
  noCoin : ∀ d, (rd d).NoCoin
  /-- it asks at most tT strings -/
  queries : ∀ d, (rd d).QueryBound tT

variable {r : ArmIn} {tT : ℕ} (Y : AskReader r tT)

/-- One term: read the files, asking; then the arm, which asks the same oracle through its
coding. -/
def chkArm (d : OnBytes.Slice.Shapes.Files) : OComp (rom 256) Bool :=
  (Y.rd d).bind fun oz => match oz with
    | none => .pure false
    | some z => (armL r.W r.Sd r.cA z).overOne r.m

/-- Under every oracle: the reading's value under it, then the arm's verdict under it. -/
theorem chkArm_det (g : Fam (rom 256)) (d : OnBytes.Slice.Shapes.Files) :
    (chkArm Y d).det g = match (Y.rd d).det g with
      | none => false
      | some z => verdict r g z := by
  unfold chkArm
  rw [OComp.det_bind]
  cases (Y.rd d).det g with
  | none => rfl
  | some z => exact (verdict_overOne r g z).symm

/-- What the reading asks on the files d under g, with the answers. -/
def askedLog (g : Fam (rom 256)) (d : OnBytes.Slice.Shapes.Files) : Trace (rom 256) :=
  ((Y.rd d).withTrace.det g).2

/-- The files' author, then this reading. z0: what stands for a refusal. -/
def makerOf (A : OComp (rom 256) OnBytes.Slice.Shapes.Files) (z0 : OutLA 256 r.L r.aL) :
    OComp (rom 256) (OutLA 256 r.L r.aL) :=
  A.bind fun d => (Y.rd d).bind fun oz => .pure (oz.getD z0)

/-- It asks what the author asks and what the reading asks. -/
theorem makerOf_queries {A : OComp (rom 256) OnBytes.Slice.Shapes.Files} {t : ℕ}
    (hA : A.QueryBound t) (z0 : OutLA 256 r.L r.aL) : (makerOf Y A z0).QueryBound (t + tT) :=
  OComp.QueryBound.bind hA fun d => OComp.QueryBound.bind (t := 0) (Y.queries d) fun _ => trivial

/-- The law of its output and log: the author's files read, and the author's log with the reading's
behind it. -/
theorem makerOf_law (g : Fam (rom 256)) (A : OComp (rom 256) OnBytes.Slice.Shapes.Files)
    (z0 : OutLA 256 r.L r.aL) :
    (makerOf Y A z0).withTrace.runEager g =
      (A.withTrace.runEager g).map fun x =>
        (((Y.rd x.1).det g).getD z0, x.2 ++ askedLog Y g x.1) := by
  unfold makerOf
  rw [Rom.withTrace_bind, OComp.runEager_bind, ← PMF.bind_pure_comp]
  refine congrArg _ (funext fun x => ?_)
  show ((((Y.rd x.1).bind fun oz => (OComp.pure (oz.getD z0) :
    OComp (rom 256) (OutLA 256 r.L r.aL))).withTrace.bind fun out' =>
    OComp.pure (out'.1, x.2 ++ out'.2)).runEager g) = PMF.pure _
  rw [runEager_bind_pure, Rom.withTrace_bind, OComp.runEager_bind,
    runEager_withTrace_det g _ (Y.noCoin x.1), PMF.pure_bind]
  show (PMF.pure _).map _ = _
  rw [PMF.pure_map]
  show PMF.pure ((((Y.rd x.1).withTrace.det g).1.getD z0),
    x.2 ++ (((Y.rd x.1).withTrace.det g).2 ++ [])) = _
  rw [List.append_nil, det_withTrace_fst]
  rfl

/-- What the bound says of the one term. Over one uniformly random oracle, for every author of files
with at most t queries: with at most the arm's own bound at t + tT queries, the one term says yes on
the author's files while what the arm promises fails of the value that the reading made, on the
words that the author's log with the reading's behind it fixes. -/
def SoundSays (εs : ℝ≥0∞) : Prop :=
  ∀ (A : OComp (rom 256) OnBytes.Slice.Shapes.Files) (t : ℕ), A.QueryBound t →
    Rom.Pr A.withTrace
        (fun g => {x | (chkArm Y x.1).det g = true ∧ ∀ z, (Y.rd x.1).det g = some z →
          ¬ LinkHolds r.W (logOne r.W (armL r.W r.Sd r.cA) r.m (readBlocks r.m g)
            (z, x.2 ++ askedLog Y g x.1)) z.1 z.2.1 z.2.2.1 z.2.2.2.1}) ≤
      (((t + tT + tVL r.W) * (1 + 4) : ℕ) : ℝ≥0∞) * εs +
        2 * (((t + tT + tVL r.W) * (1 + 4) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 256

/-- From the bound against every maker of typed values to the bound at the files' author: the maker
is the author, then this reading. -/
theorem bound_files {εs : ℝ≥0∞} (h : BoundSays r εs) : SoundSays Y εs := by
  intro A t hA
  by_cases hne : Nonempty (OutLA 256 r.L r.aL)
  · obtain ⟨z0⟩ := hne
    refine le_trans ?_ (h (makerOf Y A z0) (t + tT) (makerOf_queries Y hA z0))
    unfold Rom.Pr Rom.PrCoins
    refine MeasureTheory.lintegral_mono fun g => ?_
    rw [makerOf_law, Prob.pr_map]
    refine Prob.pr_mono _ fun x hx => ?_
    obtain ⟨h1, h2⟩ := hx
    rw [chkArm_det] at h1
    cases e : (Y.rd x.1).det g with
    | none => rw [e] at h1; exact absurd h1 (by simp)
    | some z =>
      rw [e] at h1
      have ez : ((Y.rd x.1).det g).getD z0 = z := by rw [e]; rfl
      show verdict r g (((Y.rd x.1).det g).getD z0) = true ∧
        ¬ LinkHolds r.W (logOne r.W (armL r.W r.Sd r.cA) r.m (readBlocks r.m g)
          (((Y.rd x.1).det g).getD z0, x.2 ++ askedLog Y g x.1)) (((Y.rd x.1).det g).getD z0).1
          (((Y.rd x.1).det g).getD z0).2.1 (((Y.rd x.1).det g).getD z0).2.2.1
          (((Y.rd x.1).det g).getD z0).2.2.2.1
      rw [ez]
      exact ⟨h1, h2 z e⟩
  · have e : (fun g : Fam (rom 256) => {x : OnBytes.Slice.Shapes.Files × Trace (rom 256) |
        (chkArm Y x.1).det g = true ∧ ∀ z, (Y.rd x.1).det g = some z →
          ¬ LinkHolds r.W (logOne r.W (armL r.W r.Sd r.cA) r.m (readBlocks r.m g)
            (z, x.2 ++ askedLog Y g x.1)) z.1 z.2.1 z.2.2.1 z.2.2.2.1}) = fun _ => ∅ := by
      funext g
      refine Set.eq_empty_of_forall_notMem fun x hx => ?_
      have h1 := hx.1
      rw [chkArm_det] at h1
      cases e : (Y.rd x.1).det g with
      | none => rw [e] at h1; exact absurd h1 (by simp)
      | some z => exact hne ⟨z⟩
    rw [e]
    refine le_trans (le_of_eq ?_) (zero_le _)
    unfold Rom.Pr Rom.PrCoins
    simp [Prob.pr]

/-- The reading, at the oracle made from the hash, makes of a run's files what the tie's reading of
the files makes of them. -/
def AskReader.Agrees (Z : Pub) (R : Reading5 r.shape) : Prop :=
  ∀ (F : Files) (id : String) (table further : OnBytes.Params.TableName)
    (o : Model.Verify.Options) (c cj : r.L.Rec) (πL : OneProtocolProof 256 (batLC r.L r.aL)),
    PortYesAt F id table further → F.pol = Z.pol → F.lay = Z.lay → F.KL = Z.KL →
    r.recOf (stmOf F o) table = some c → r.recOf (stmOf F o) further = some cj →
    R.ent (stmOf F o) F.key F.ent = some (further, πL) →
    (Y.rd (filesOf F)).det oBits =
      some (bytesToDig table.root, bytesToDig further.root, c, cj, πL)

/-- What the tie says of the one term: `TieSays` (Johnson/Top/Fire/ArmPair.lean) with its last
clause said of `chkArm` on the run's own files. -/
def ZeroSays (Z : Pub) : Prop :=
  ∀ {args : List String} {s s' : World}, Shell.Run (_root_.main args) s 0 s' →
    ∃ (config ivk request y proof : String) (a : Asked) (F : Files) (t : List Event) (id : String)
      (pre post : List String),
      args = "verify" :: config :: ivk :: request :: y :: proof ::
        (pre ++ "-id" :: id :: post) ∧
      kindOf args = .whole config ivk request y proof a ∧
      Steps opsIO (wholeReads config ivk request y proof F.entry (.bytes F.pol) (.bytes F.KL)
        (.bytes F.lay) (.bytes F.key) (.bytes F.request) (.bytes F.y) (.bytes F.proof)
        (.bytes F.ent) ++ t) s s' ∧
      a.options.id = some id ∧ a.options.bits = 128 ∧
      ∃ (table further : OnBytes.Params.TableName), PortYesAt F id table further ∧
        (F.pol = Z.pol → F.lay = Z.lay → F.KL = Z.KL → a.options.policy = none →
          a.options.noProofOfWork = false → (chkArm Y (filesOf F)).det oBits = true)

/-- From the tie to the one term. -/
theorem zero_files {Z : Pub} {R : Reading5 r.shape} (h : TieSays r Z R) (hY : Y.Agrees Z R) :
    ZeroSays Y Z := by
  intro args s s' hr
  obtain ⟨config, ivk, request, y, proof, a, F, t, id, pre, post, h1, h2, h3, h4, h5, table,
    further, hp, hrest⟩ := h hr
  refine ⟨config, ivk, request, y, proof, a, F, t, id, pre, post, h1, h2, h3, h4, h5, table,
    further, hp, fun e1 e2 e3 e4 e5 => ?_⟩
  obtain ⟨c, cj, πL, hc, hcj, he, hv⟩ := hrest e1 e2 e3 e4 e5
  rw [chkArm_det, hY F id table further a.options c cj πL hp e1 e2 e3 hc hcj he]
  exact hv

end OnBytes.K.Fire
