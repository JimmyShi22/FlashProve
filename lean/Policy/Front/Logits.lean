-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Policy/Front/Logits.lean

The logits, gaps and costs of Policy/Front/MeetsPolicy.lean are those of the library's integer
program, under the hypotheses of each statement.

MeetsPolicy.lean reads the logits off `IntegerTransformer.trace` (IntegerModel/Model.lean), the
function on arrays that returns every named value of the model. The relation on a request (`RinfR`,
Inst/Model/ProgramR.lean) reads the logits `lgK` (Inst/Model/Program.lean) of one pass over a window
of 1,024 tokens. Main names: `trace_logits` (the two are the same numbers), `logits_of_window` (from
a list of tokens to a window that begins with it), `logitGap_eq_gapOf_of_entries`,
`tokenCost_of_window`. The chief hypothesis is that the arrays hold the library's numbers: `Same`
(IntegerModel/Readable/Defs.lean) in `trace_logits`; `Feeds` (IntegerModel/Readable/Tie.lean: `Same`
at the model's sizes and a committed model's numbers, and the model's own test passed) in the
statements on lists of tokens.

Sources: the files named here; the step to a window is `lgK_prefix`
(IntegerModel/ReplyOnWindow.lean). Terms: lean/GLOSSARY.md: index, table of scales, request.

Limits: an error common to `trace` and `lgK` is not detected by their equality. The statements are
on logits: `trace` and `lgK` test no range condition. That given weights meet `Feeds` is not said
here (`feeds_of_tie`, Policy/Front/TrueUnder.lean).
-/
import Policy.Front.MeetsPolicy
import IntegerModel.Readable.Tie

set_option autoImplicit false

/- No default table of scales is in sight in this file: the low-priority instance `Scl.ref`
(Inst/Model/Scl.lean) is switched off, so whatever takes an `Scl` has to say which. -/
attribute [-instance] Inst.Model.Scl.ref

namespace Policy

open VerifiableInference
open Inst.Model IntegerModel.Readable IntegerModel.Runnable

/-! ## 1. The trace's logits are the program's -/

/-- The field `logits` of the trace of a prompt holds the program's logits: entry v of row t is
`lgK .. t v`. For all sizes with `Good P` (IntegerModel/Runnable/Defs.lean), a prompt of `P.T`
tokens with `P.T ≤ Tmax`, and arguments that hold the library's numbers (`Same`,
IntegerModel/Readable/Defs.lean). It stands beside `trace_finalNorm` and `trace_choices`
(IntegerModel/Readable/Main.lean). -/
theorem trace_logits (P : Params) (hP : IntegerModel.Runnable.Good P) (Tmax : ℕ) (hTm : P.T ≤ Tmax)
    (κ : ℕ → LayerScale) (nf : NormPar) (tbs : ℕ → Tables) (w : Inst.Model.Weights)
    (s : IntegerTransformer.Settings) (tables : IntegerTransformer.Tables)
    (weights : IntegerTransformer.Weights) (h : Same P Tmax κ nf tbs w s tables weights)
    (prompt : Fin P.T → Fin P.V) :
    (IntegerTransformer.trace s tables weights (toks P prompt)).logits =
      tabl P.T fun t => tabl P.V fun v => lgK P κ nf tbs w prompt t v := by
  show ((IntegerTransformer.trace s tables weights (toks P prompt)).finalNorm.map
      fun n => IntegerTransformer.product n.out weights.head s.vocabulary) = _
  rw [trace_finalNorm P hP Tmax hTm κ nf tbs w s tables weights h prompt, tabl_map,
    h.sizes.vocabulary]
  refine tabl_congr fun t _ => ?_
  show IntegerTransformer.product
      (tabl P.d (NORM.out nf P.d (XK P κ tbs w prompt (2 * P.layers) t))) weights.head P.V = _
  exact product_same _ _ _ _ w.H h.head

/-- At the model's sizes, on a list of at most 1,024 tokens: entry v of row t of the trace's logits
is the logit of the program that runs on these tokens alone, for a position t of the list and a
token v of the vocabulary. `hF`: the arrays hold m's numbers (`Feeds`,
IntegerModel/Readable/Tie.lean). -/
theorem logits_of_feeds (m : IntegerModel.Committed) (s : IntegerTransformer.Settings)
    (tables : IntegerTransformer.Tables) (weights : IntegerTransformer.Weights)
    (hF : Feeds m s tables weights) (ctx : List IntegerModel.Token) (hn : ctx.length ≤ ppref.T)
    {t v : ℕ} (ht : t < ctx.length) (hv : v < ppref.V) :
    ((IntegerTransformer.trace s tables weights (nums ctx)).logits.entry t).entry v =
      lgK (IntegerModel.arch ctx.length) m.settings.kap m.settings.nf (fun _ => tbRef)
        m.weights.val (fun i => ctx.get i) t v := by
  have e : nums ctx = toks { ppref with T := ctx.length } (fun i => ctx.get i) := toks_eq ctx
  have h1 : (IntegerTransformer.trace s tables weights (nums ctx)).logits =
      tabl ctx.length fun t => tabl ppref.V fun v =>
        lgK (IntegerModel.arch ctx.length) m.settings.kap m.settings.nf (fun _ => tbRef)
          m.weights.val (fun i => ctx.get i) t v := by
    rw [e]
    exact trace_logits { ppref with T := ctx.length } (good_ref _) ppref.T hn m.settings.kap
      m.settings.nf (fun _ => tbRef) m.weights.val s tables weights (hF.same.withT _)
      (fun i => ctx.get i)
  rw [h1]
  exact (congrArg (fun row : IntegerTransformer.IntegerVector => row.entry v) (tabl_entry _ ht)).trans
    (tabl_entry _ hv)

/-- From a list of tokens to a window. If `ctx` is a nonempty prefix of the window, the trace's
logits at the last position of `ctx` are the logits, at that position, of the program's pass over
the window. What follows `ctx` in the window does not matter. The sister for the next token is
`IntegerModel.model_of_window` (IntegerModel/ReplyOnWindow.lean). -/
theorem logits_of_window (m : IntegerModel.Committed) (s : IntegerTransformer.Settings)
    (tables : IntegerTransformer.Tables) (weights : IntegerTransformer.Weights)
    (hF : Feeds m s tables weights) (window : Fin ppref.T → Fin ppref.V)
    (ctx : List IntegerModel.Token) (h0 : 0 < ctx.length) (hn : ctx.length ≤ ppref.T)
    (hget : ∀ t (ht : t < ctx.length), ctx.get ⟨t, ht⟩ = window ⟨t, lt_of_lt_of_le ht hn⟩)
    {v : ℕ} (hv : v < ppref.V) :
    ((IntegerTransformer.trace s tables weights (nums ctx)).logits.entry (ctx.length - 1)).entry v =
      lgK ppref m.settings.kap m.settings.nf (fun _ => tbRef) m.weights.val window
        (ctx.length - 1) v :=
  (logits_of_feeds m s tables weights hF ctx hn (Nat.sub_lt h0 Nat.one_pos) hv).trans
    (congrFun (IntegerModel.lgK_prefix ppref ctx.length hn m.settings.kap m.settings.nf
      (fun _ => tbRef) m.weights.val window (fun i => ctx.get i) hget
      (Nat.sub_lt h0 Nat.one_pos)) v)

/-! ## 2. The gap -/

/-- The gap of a token of the vocabulary reads the logits of the vocabulary's tokens alone. -/
theorem gapOf_congr {V : ℕ} {l l' : ℕ → ℤ} {w : ℕ} (hw : w < V) (h : ∀ v < V, l v = l' v) :
    gapOf V l w = gapOf V l' w := by
  unfold gapOf
  refine maxTo_congr' (V - 1) fun v hv => ?_
  show l v - l w + (if v < w then 1 else 0) = l' v - l' w + (if v < w then 1 else 0)
  rw [h v (by omega), h w hw]

/-- The gap on an array (`logitGap`, Policy/Front/MeetsPolicy.lean) is the relation's gap
(`Inst.Model.gapOf`, Inst/Model/ProgramR.lean) on every function that has the array's numbers at the
tokens of the vocabulary. -/
theorem logitGap_eq_gapOf_of_entries {V : ℕ} {logits : IntegerTransformer.IntegerVector} {l : ℕ → ℤ} {w : ℕ}
    (hw : w < V) (h : ∀ v < V, logits.entry v = l v) : logitGap V logits w = gapOf V l w :=
  (maxUpTo_eq (fun other => logits.entry other - logits.entry w + if other < w then 1 else 0)
    (V - 1)).trans (gapOf_congr (l := fun v => logits.entry v) hw h)

/-! ## 3. At weights whose arrays hold the numbers of a committed model -/

section
variable (m : IntegerModel.Committed) {settings : IntegerTransformer.Settings}
  (weights : ModelWeights settings) (hF : Feeds m settings lookupTables weights.val)
include hF

/-- On every list of tokens `modelNextToken` is the library's model function at m:
`model_eq_programNextToken` (IntegerModel/Readable/Tie.lean), said of `modelNextToken`. -/
theorem modelNextToken_of_feeds (tokens : List IntegerModel.Token) :
    modelNextToken settings weights (tokens.map Fin.val) =
      (IntegerModel.programNextToken m tokens).map Fin.val :=
  model_eq_programNextToken _ _ _ _ hF tokens

/-- The cost of a token after a list of tokens: the relation's gap of that token under the logits,
at the list's last position, of the program's pass over any window that begins with the list, plus
2^8. -/
theorem tokenCost_of_window (window : Fin ppref.T → Fin ppref.V) (ctx : List IntegerModel.Token)
    (h0 : 0 < ctx.length) (hn : ctx.length ≤ ppref.T)
    (hget : ∀ t (ht : t < ctx.length), ctx.get ⟨t, ht⟩ = window ⟨t, lt_of_lt_of_le ht hn⟩)
    (token : IntegerModel.Token) :
    tokenCost settings weights (ctx.map Fin.val) token.val =
      gapOf ppref.V (lgK ppref m.settings.kap m.settings.nf (fun _ => tbRef) m.weights.val window
        (ctx.length - 1)) token.val + 2 ^ 8 := by
  unfold tokenCost
  rw [hF.same.sizes.vocabulary]
  refine congrArg (fun gap : ℤ => gap + 2 ^ 8)
    (logitGap_eq_gapOf_of_entries token.isLt fun v hv => ?_)
  show ((IntegerTransformer.trace settings lookupTables weights.val
      (ctx.map Fin.val).toArray).logits.entry ((ctx.map Fin.val).length - 1)).entry v = _
  rw [List.length_map]
  exact logits_of_window m settings lookupTables weights.val hF window ctx h0 hn hget hv

end

end Policy

#print axioms Policy.trace_logits
#print axioms Policy.logits_of_feeds
#print axioms Policy.logits_of_window
#print axioms Policy.gapOf_congr
#print axioms Policy.logitGap_eq_gapOf_of_entries
#print axioms Policy.modelNextToken_of_feeds
#print axioms Policy.tokenCost_of_window
