-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/WrapLaw.lean: the claim of OnBytes/Slice/FineAtRecWrap.lean is shown, and with it the
goal for tables with a record is stated for every committer.

OF THE GOAL: THIS IS WHAT WOULD BE CLAIMED; NOTHING IS SHOWN. What is shown is that two
probabilities compare (`wrapClaim`), and an implication.

Under every oracle g the law of "the committer that asks, a prover, the verifier" is the law of "the
committer, the prover, the verifier", but that what is asked stands behind the committer's log, and
in the log of the two together, which nothing here reads. In every log of a run under g each entry
holds g's own answer, so there the seed is not missing, and `FineAtRec` is `FineO`
(`fineAtRec_moreAt`).

Main theorems.
(`support_withTrace_ans`: every entry of every log of a run under g, coins and all, holds g's own
answer: it stands in OnBytes/Slice/WrapBetween.lean.)
 `runEager_withTrace_twice`   the log of the algorithm that outputs its own log is that log.
 `runEager_wrap`        output and log of the committer that asks: C's output, and C's log with what
                        is asked put behind it (`askBehind`).
 `law_two`              the law of the three algorithms one after the other, written out.
 `wrapClaim`            `WrapClaim`, for every `AskRead`, committer, prover and verifier.
 `join_fine_rec_all`    THE GOAL FOR EVERY COMMITTER, with the three parts as variables.

What is not claimed. `join_fine_rec_all` IS AN IMPLICATION FROM HYPOTHESES THAT NOBODY HAS MET: no
part for a key, an entry or a proof at a setting with a record is written.
`wrapClaim` compares
two probabilities and bounds neither. No lemma in the shape of `hX'` is drawn from
`support_withTrace_ans`. Nothing on how the seeds are distributed. Nothing on any hash function.

-/
import OnBytes.Slice.FineAtRecWrap
import OnBytes.Slice.WrapBetween
import Compile.GlueBinding

set_option autoImplicit false

namespace OnBytes.Slice
open _root_.Iop Rom Prob Compile Compile.Batch _root_.Run _root_.Run.PQ MeasureTheory
open scoped ENNReal
open OnBytes.Tie (IdKey idCode firstId)

/-! ## Logs of runs with coins -/

section
variable {S : OSpec} {α γ : Type}

/-- The log of the algorithm that outputs its own log is that log: `runEager_withTrace_self`
(OnBytes/Slice/WrapBetween.lean), under the name by which this file calls it. -/
theorem runEager_withTrace_twice (g : Fam S) (c : OComp S α) :
    c.withTrace.withTrace.runEager g = (c.withTrace.runEager g).map fun x => (x, x.2) :=
  runEager_withTrace_self g c

end

/-! ## The law of the run with the committer that asks -/

section
variable {β δ Xi : Type} {D : DecR} (R : AskRead D) (dig : β → ZKCP.Digest 256)

/-- What is asked put behind a log. -/
def askBehind (g : Fam (rom 256)) (x : β × Trace (rom 256)) : β × Trace (rom 256) :=
  (x.1, x.2 ++ R.more g (dig x.1) x.2)

/-- **Output and log of the committer that asks are C's output and C's log with what is asked put
behind it**: as laws over the coins, under every g. -/
theorem runEager_wrap (g : Fam (rom 256)) (C : OComp (rom 256) β) :
    (wrap R dig C).withTrace.runEager g = (C.withTrace.runEager g).map (askBehind R dig g) := by
  unfold wrap
  rw [Rom.withTrace_bind, OComp.runEager_bind, runEager_withTrace_twice, PMF.bind_map,
    ← PMF.bind_pure_comp]
  refine congrArg _ (funext fun x => ?_)
  show (((match firstId (dig x.1) x.2 with
      | some k => (R.ask k).bind fun _ => OComp.pure x.1
      | none => OComp.pure x.1).withTrace.bind fun out' =>
        OComp.pure (out'.1, x.2 ++ out'.2)).runEager g) = PMF.pure (askBehind R dig g x)
  unfold askBehind AskRead.more
  cases firstId (dig x.1) x.2 with
  | none => rfl
  | some k =>
    have hn : (((R.ask k).bind fun _ => (OComp.pure x.1 : OComp (rom 256) β)).withTrace).NoCoin :=
      noCoin_withTrace _ (OComp.NoCoin.bind (R.ask_noCoin k) fun _ => trivial)
    show ((((R.ask k).bind fun _ => (OComp.pure x.1 : OComp (rom 256) β)).withTrace.bind
      fun out' => OComp.pure (out'.1, x.2 ++ out'.2)).runEager g) = _
    rw [hn.runEager_bind]
    show PMF.pure _ = PMF.pure _
    congr 1
    refine Prod.ext ?_ ?_
    · show (((R.ask k).bind fun _ => (OComp.pure x.1 : OComp (rom 256) β)).withTrace.det g).1 = x.1
      rw [det_withTrace_fst, OComp.det_bind]
      rfl
    · show x.2 ++ (((R.ask k).bind fun _ =>
        (OComp.pure x.1 : OComp (rom 256) β)).withTrace.det g).2 = _
      rw [det_withTrace_bind]
      show x.2 ++ (((R.ask k).withTrace.det g).2 ++ []) = _
      rw [List.append_nil]

/-- The law of "a committer, a prover, the verifier", without the log of the first two together. -/
theorem law_two (g : Fam (rom 256)) (C : OComp (rom 256) β) (P : β → OComp (rom 256) δ)
    (V : β × δ → OComp (rom 256) Bool) :
    ((twoExp (twoExp C P) fun x => V (x.1.1, x.2)).runEager g).map (fun z => (z.1.1, z.2)) =
      (C.withTrace.runEager g).bind fun x => ((P x.1).runEager g).bind fun y =>
        ((V (x.1, y)).runEager g).map fun b => ((x, y), b) := by
  have h1 : ((twoExp (twoExp C P) fun x => V (x.1.1, x.2)).runEager g).map
      (fun z => (z.1.1, z.2)) =
      ((twoExp C P).runEager g).bind fun a => ((V (a.1.1, a.2)).runEager g).map fun b => (a, b) :=
          by
    rw [← runEager_withTrace_fst g (twoExp C P), PMF.bind_map]
    unfold twoExp
    rw [OComp.runEager_bind, PMF.map_bind]
    refine congrArg _ (funext fun x => ?_)
    rw [OComp.runEager_bind, PMF.map_bind]
    show ((V (x.1.1.1, x.1.2)).runEager g).bind (fun a =>
        (PMF.pure (x, a)).map fun z => (z.1.1, z.2)) =
      ((V (x.1.1.1, x.1.2)).runEager g).map fun b => (x.1, b)
    rw [← PMF.bind_pure_comp]
    refine congrArg _ (funext fun y => ?_)
    rw [PMF.pure_map]
    rfl
  rw [h1]
  unfold twoExp
  rw [OComp.runEager_bind, PMF.bind_bind]
  refine congrArg _ (funext fun x => ?_)
  rw [OComp.runEager_bind, PMF.bind_bind]
  refine congrArg _ (funext fun y => ?_)
  show (PMF.pure _).bind _ = _
  rw [PMF.pure_bind]

variable (A : D.Claims Xi) (shape₀ : Params.IndexShape) (xReq : δ → Xi)

/-- **THE CLAIM OF OnBytes/Slice/FineAtRecWrap.lean HOLDS**: for every committer C, prover and
verifier, the probability of "yes, and not fine read with the oracle" is at most the probability of
"yes, and not `FineAtRec`" for the committer that asks. Under every g the two laws are one, but for
what is asked put behind the committer's log; there the seed is not missing. -/
theorem wrapClaim : WrapClaim A R shape₀ dig xReq := by
  intro C P V
  refine lintegral_mono fun g => ?_
  show Prob.pr _ _ ≤ Prob.pr _ _
  have e1 : Prob.pr ((twoExp (twoExp C P) fun x => V (x.1.1, x.2)).runEager g)
      {z | z.2 = true ∧ ¬ FineO A R shape₀ dig xReq g z.1} =
      Prob.pr (((twoExp (twoExp C P) fun x => V (x.1.1, x.2)).runEager g).map
        fun z => (z.1.1, z.2))
        {p | p.2 = true ∧ ¬ FineO A R shape₀ dig xReq g (p.1, [])} := by
    rw [Prob.pr_map]
    rfl
  have e2 : Prob.pr ((twoExp (twoExp (wrap R dig C) P) fun x => V (x.1.1, x.2)).runEager g)
      {z | z.2 = true ∧ ¬ FineAtRec A R.toLogRead shape₀ dig xReq z.1} =
      Prob.pr (((twoExp (twoExp (wrap R dig C) P) fun x => V (x.1.1, x.2)).runEager g).map
        fun z => (z.1.1, z.2))
        {p | p.2 = true ∧ ¬ FineAtRec A R.toLogRead shape₀ dig xReq (p.1, [])} := by
    rw [Prob.pr_map]
    rfl
  rw [e1, e2, law_two, law_two, runEager_wrap, PMF.bind_map]
  have e3 : ((C.withTrace.runEager g).bind ((fun x : β × Trace (rom 256) =>
        ((P x.1).runEager g).bind fun y => ((V (x.1, y)).runEager g).map fun b => ((x, y), b)) ∘
          askBehind R dig g)) =
      ((C.withTrace.runEager g).bind fun x => ((P x.1).runEager g).bind fun y =>
        ((V (x.1, y)).runEager g).map fun b => ((x, y), b)).map
          fun p => ((askBehind R dig g p.1.1, p.1.2), p.2) := by
    rw [PMF.map_bind]
    refine congrArg _ (funext fun x => ?_)
    show ((P x.1).runEager g).bind _ = _
    rw [PMF.map_bind]
    refine congrArg _ (funext fun y => ?_)
    rw [PMF.map_comp]
    rfl
  rw [e3, Prob.pr_map]
  refine Prob.pr_mono_support _ fun p hp hE => ?_
  obtain ⟨x, hx, hp2⟩ := (PMF.mem_support_bind_iff _ _ _).1 hp
  obtain ⟨y, -, hp3⟩ := (PMF.mem_support_bind_iff _ _ _).1 hp2
  obtain ⟨b, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hp3
  refine ⟨hE.1, fun hF => hE.2 ?_⟩
  exact (fineAtRec_moreAt A R shape₀ dig xReq g ((x, y), [])
    (support_withTrace_ans g C x hx)).1 hF

end

/-! ## For every committer -/

section
variable {β δ Xi : Type} {D : DecR}

/-- **THE GOAL FOR TABLES WITH A RECORD, FOR EVERY COMMITTER: THIS IS WHAT WOULD BE CLAIMED; NOTHING
IS SHOWN.** The three parts K, E, F, the verifier, the rare set X', the decoder's data and both
readings of a log are variables. `join_fine_rec_run` (OnBytes/Slice/FineAtRec.lean) at the committer
that asks, behind `wrapClaim`: the probability that the verifier says yes and it is not fine, read
with the oracle (`FineO`), is at most B. The hypotheses are those of `join_fine_rec_run`, with three
changes: R is an `AskRead`; the bound `hX'` speaks of `wrap R dig C`; in `hB` the committer's
questions are tC + R.qS. Of C it asks its number of questions; C also stands in `hX'`: X' must be
rare in the run of the committer that asks. That any three parts, any X' and any verifier meet the
hypotheses is not shown. -/
theorem join_fine_rec_all (w : DecR.Way D) (sc : List Bool) (S₀ : Finset (List Bool))
    (S₁ : Tab → Finset (List Bool))
    (h169₀ : ∀ s ∈ S₀, IsCall169 s) (h169₁ : ∀ T₀, ∀ s ∈ S₁ T₀, IsCall169 s)
    (C : OComp (rom 256) β) (dig : β → ZKCP.Digest 256) (P : β → OComp (rom 256) δ)
    (shape₀ : Params.IndexShape) (table : δ → Params.TableName) (tC tP : ℕ)
    (hC : C.QueryBound tC) (hP : ∀ b, (P b).QueryBound tP)
    (K E F : Tab → Tab → PartO 256 ((β × Trace (rom 256)) × δ) SgX)
    (hK : ∀ T₀ T₁, (K T₀ T₁).OK) (hE : ∀ T₀ T₁, (E T₀ T₁).OK) (hF : ∀ T₀ T₁, (F T₀ T₁).OK)
    (bS : ℕ → ℕ → ℝ≥0∞) (hS : ∀ T₀ T₁, (K T₀ T₁).Stable bS)
    (hKE : ∀ T₀ T₁, SameRaw (K T₀ T₁) (E T₀ T₁)) (hEF : ∀ T₀ T₁, SameRaw (E T₀ T₁) (F T₀ T₁))
    (A : D.Claims Xi) (R : AskRead D) (xReq : δ → Xi) (xOf : ∀ T₀ T₁, (F T₀ T₁).Out → Xi)
    (recK : ∀ T₀ T₁, (K T₀ T₁).Out → D.Rec) (recE₀ recE₁ : ∀ T₀ T₁, (E T₀ T₁).Out → D.Rec)
    (recF : ∀ T₀ T₁, (F T₀ T₁).Out → D.Rec)
    (hLK : ∀ T₀ T₁ oK Y, (K T₀ T₁).Lang oK [Y] → DecR.LangK A w (recK T₀ T₁ oK) Y)
    (hLE : ∀ T₀ T₁ oE Y₀ Y₁, (E T₀ T₁).Lang oE [Y₀, Y₁] →
      DecR.LangE w (recE₀ T₀ T₁ oE) (recE₁ T₀ T₁ oE) Y₀ Y₁)
    (hLF : ∀ T₀ T₁ oF Y, (F T₀ T₁).Lang oF [Y] →
      DecR.LangP A w (xOf T₀ T₁ oF) (recF T₀ T₁ oF) Y)
    (X' : Tab → Tab → Fam (rom 256) → Set (((β × Trace (rom 256)) × δ) × Trace (rom 256)))
    (bX' : ℝ≥0∞)
    (hX' : ∀ T₀ T₁, Rom.Pr (twoExp (pinOn (S₁ T₀) T₁ (pinOn S₀ T₀ (wrap R dig C)))
      fun b => pinOn (S₁ T₀) T₁ (pinOn S₀ T₀ (P b))).withTrace (X' T₀ T₁) ≤ bX')
    (hid : ∀ k s, idCode k = some s → s ∉ S₀ ∧ ∀ T₀, s ∉ S₁ T₀)
    (V : β × δ → OComp (rom 256) Bool) (hV : ∀ x, (V x).NoCoin)
    (hYes : ∀ T₀ T₁ g z,
      (V (z.1.1.1, z.1.2)).det (over S₀ T₀ (over (S₁ T₀) T₁ g)) = true → z ∉ X' T₀ T₁ g →
      (∃ s, idCode (keyAt shape₀ sc table T₀ z.1.2) = some s ∧
        over S₀ T₀ (over (S₁ T₀) T₁ g) () s = dig z.1.1.1) ∧ ∃ oK oE oF cm',
        ((K T₀ T₁).chk z.1).det g = some oK ∧ ((E T₀ T₁).chk z.1).det g = some oE ∧
        ((F T₀ T₁).chk z.1).det g = some oF ∧
        (K T₀ T₁).roots oK = [bytesToDig (table z.1.2).root] ∧
        (E T₀ T₁).roots oE = [bytesToDig (table z.1.2).root, cm'] ∧
        (F T₀ T₁).roots oF = [cm'] ∧
        recE₀ T₀ T₁ oE = recK T₀ T₁ oK ∧ recF T₀ T₁ oF = recE₁ T₀ T₁ oE ∧
        (∀ ρ, R.seed (keyAt shape₀ sc table T₀ z.1.2) z.1.1.2 = some ρ →
          R.recAt (keyAt shape₀ sc table T₀ z.1.2) z.1.1.2 = some (recK T₀ T₁ oK)) ∧
        (NoClash z.1.1.2 → (K T₀ T₁).raw z.1.1.2 (bytesToDig (table z.1.2).root) =
          R.raw (cOf sc T₀) z.1.1.2 (bytesToDig (table z.1.2).root)) ∧
        xOf T₀ T₁ oF = xReq z.1.2)
    (B : ℝ≥0∞)
    (hB : ∀ T₀ T₁, (K T₀ T₁).bound (tC + R.qS + tP) + ((E T₀ T₁).bound (tC + R.qS + tP) +
      ((F T₀ T₁).bound (tC + R.qS + tP) +
        (bS (tC + R.qS) tP + ((((tC + R.qS + tP + 2) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 + bX')))) ≤ B) :
    Rom.Pr (twoExp (twoExp C P) fun x => V (x.1.1, x.2))
      (fun g => {z | z.2 = true ∧ ¬ FineO A R shape₀ dig xReq g z.1}) ≤ B :=
  (wrapClaim R dig A shape₀ xReq C P V).trans
    (join_fine_rec_run w sc S₀ S₁ h169₀ h169₁ (wrap R dig C) dig P shape₀ table (tC + R.qS) tP
      (wrap_bound R dig C tC hC) hP K E F hK hE hF bS hS hKE hEF A R.toLogRead xReq xOf recK recE₀
      recE₁ recF hLK hLE hLF X' bX' hX' hid V hV hYes B hB)

end

end OnBytes.Slice
