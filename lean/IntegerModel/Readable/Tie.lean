-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
IntegerModel/Readable/Tie.lean: IntegerTransformer.model (IntegerModel/Model.lean) compared with
IntegerModel.programNextToken (the library's integer program as a function from a list of tokens to
the next token), IntegerModel.greedyOutput, IntegerModel.IsReply (IntegerModel/Reply.lean).
  Feeds m s tables weights   the arguments hold Maverick's sizes, m's scales and weights and the
                             library's five
                             tables, at every position inside the shapes, and pass the model's check
                             wellFormed
  model_eq_programNextToken   model s tables weights (nums ctx) = programNextToken m ctx, as numbers
  greedy_eq_greedyOutput, isReply_iff_greedy   token by token; "the reply is the model's" in this
                                               function's
                                         terms
In the types: a token is a number below 202,048; m's weights are well formed and its settings lawful
(IntegerModel.Committed; Lawful: Inst/Model/Scales.lean).
These theorems say: if Feeds m s tables weights holds, the function gives m's answers.
-/
import IntegerModel.Readable.Main
import IntegerModel.Runnable.AtModelSizes
import IntegerModel.ReplyOnWindow

set_option autoImplicit false

namespace IntegerModel.Readable

open Inst.Model IntegerModel.Runnable

/-- the number of positions P.T is no part of what ties the arguments: if Same holds at P, it holds
with any n as P.T. (s.positions = Tmax stays.) -/
theorem Same.withT {P : Params} {Tmax : ℕ} {κ : ℕ → LayerScale} {nf : NormPar} {tbs : ℕ → Tables}
    {w : Inst.Model.Weights} {s : IntegerTransformer.Settings} {tables : IntegerTransformer.Tables}
    {weights : IntegerTransformer.Weights} (h : Same P Tmax κ nf tbs w s tables weights) (n : ℕ) :
    Same { P with T := n } Tmax κ nf tbs w s tables weights where
  sizes := ⟨h.sizes.positions, h.sizes.layers, h.sizes.width, h.sizes.queryHeads,
    h.sizes.keyValueHeads, h.sizes.headDim, h.sizes.hidden, h.sizes.expertHidden,
    h.sizes.experts, h.sizes.vocabulary⟩
  scales := h.scales
  finalBits := h.finalBits
  finalShift := h.finalShift
  finalEps := h.finalEps
  tables L hL := ⟨(h.tables L hL).cos, (h.tables L hL).sin, (h.tables L hL).rows,
    (h.tables L hL).exp, (h.tables L hL).silu, (h.tables L hL).sigm⟩
  layer L hL := ⟨(h.layer L hL).Wq, (h.layer L hL).Wk, (h.layer L hL).Wv, (h.layer L hL).Wo,
    (h.layer L hL).Wg, (h.layer L hL).Wu, (h.layer L hL).Wd, (h.layer L hL).Wr, (h.layer L hL).Eg,
    (h.layer L hL).Eu, (h.layer L hL).Ed⟩
  emb := h.emb
  head := h.head

/-- a list of tokens as a list of numbers -/
def vals (l : List IntegerModel.Token) : List ℕ := l.map fun y => y.val
/-- a list of tokens as the function takes it -/
def nums (ctx : List IntegerModel.Token) : Array ℕ := (vals ctx).toArray

/-- the arguments hold the sizes of ppref, m's numbers and the library's five tables, inside the
shapes, and pass the model's own test -/
structure Feeds (m : IntegerModel.Committed) (s : IntegerTransformer.Settings)
    (tables : IntegerTransformer.Tables) (weights : IntegerTransformer.Weights) : Prop where
  same : Same ppref ppref.T m.settings.kap m.settings.nf (fun _ => tbRef)
    m.weights.val s tables weights
  wellFormed : IntegerTransformer.wellFormed s tables weights = true

/-- n answers of g, each after the context and the answers before it; none if g gives none on the
way -/
def greedy (g : Array ℕ → Option ℕ) : Array ℕ → ℕ → Option (List ℕ)
  | _, 0 => some []
  | ctx, n + 1 => match g ctx with
    | none => none
    | some y => (greedy g (ctx.push y) n).map (y :: ·)

theorem greedy_of (g : Array ℕ → Option ℕ) (f : List IntegerModel.Token → Option IntegerModel.Token)
    (hg : ∀ ctx, g (nums ctx) = (f ctx).map fun y => y.val) :
    ∀ (n : ℕ) (ctx : List IntegerModel.Token),
      greedy g (nums ctx) n = (IntegerModel.greedyOutput f ctx n).map vals
  | 0, _ => rfl
  | n + 1, ctx => by
      show (match g (nums ctx) with
        | none => none
        | some y => (greedy g ((nums ctx).push y) n).map (y :: ·))
        = (match f ctx with
          | none => none
          | some y => (IntegerModel.greedyOutput f (ctx ++ [y]) n).map (y :: ·)).map vals
      rw [hg ctx]
      cases f ctx with
      | none => rfl
      | some y =>
          have e : (nums ctx).push y.val = nums (ctx ++ [y]) := by simp [nums, vals]
          show (greedy g ((nums ctx).push y.val) n).map (y.val :: ·) =
            ((IntegerModel.greedyOutput f (ctx ++ [y]) n).map (y :: ·)).map vals
          rw [e, greedy_of g f hg n (ctx ++ [y])]
          cases IntegerModel.greedyOutput f (ctx ++ [y]) n <;> rfl

section Tie
variable (m : IntegerModel.Committed) (s : IntegerTransformer.Settings)
  (tables : IntegerTransformer.Tables)
  (weights : IntegerTransformer.Weights) (hF : Feeds m s tables weights)
include hF

/-- On every list of tokens the function, under hF : Feeds m s tables weights, gives the answer of
IntegerModel.programNextToken.
(Both run only on the tokens of ctx and require the range conditions at these positions: the
prefix, not a window of 1,024.) -/
theorem model_eq_programNextToken (ctx : List IntegerModel.Token) :
    IntegerTransformer.model s tables weights (nums ctx) =
      (IntegerModel.programNextToken m ctx).map fun y => y.val := by
  have h := model_is { ppref with T := ctx.length } (good_ref _) ppref.T
    m.settings.kap m.settings.nf (fun _ => tbRef) m.weights.val s tables weights
    (hF.same.withT _) (fun i => ctx.get i)
  have ht : nums ctx = toks { ppref with T := ctx.length } (fun i => ctx.get i) := toks_eq ctx
  rw [ht]
  unfold IntegerModel.programNextToken
  by_cases hc : 0 < ctx.length ∧
    ctx.length ≤ ppref.T ∧
    RunsK (IntegerModel.arch ctx.length) m.settings.kap m.settings.nf (fun _ => tbRef)
      m.weights.val (fun i => ctx.get i)
  · rw [if_pos hc, Option.map_some]
    dsimp only
    exact h.1 ⟨hF.wellFormed, hc⟩
  · rw [if_neg hc, Option.map_none]
    exact h.2 fun a => hc a.2

theorem greedy_eq_greedyOutput (n : ℕ) (ctx : List IntegerModel.Token) :
    greedy (IntegerTransformer.model s tables weights) (nums ctx) n =
      (IntegerModel.greedyOutput (IntegerModel.programNextToken m) ctx n).map vals :=
  greedy_of _ _ (model_eq_programNextToken m s tables weights hF) n ctx

/-- IsReply of IntegerModel/Reply.lean ("the reply is the model's") in terms of this function. -/
theorem isReply_iff_greedy (x : IntegerModel.Request) :
    IntegerModel.IsReply m x ↔
    x.r < x.e ∧
    greedy (IntegerTransformer.model s tables weights)
        (nums (IntegerModel.promptOf x)) (x.e - x.r) =
      some (vals (IntegerModel.replyOf x)) := by
  unfold IntegerModel.IsReply
  rw [greedy_eq_greedyOutput m s tables weights hF]
  refine and_congr Iff.rfl ⟨fun h => by rw [h]; rfl, fun h => ?_⟩
  cases hg : IntegerModel.greedyOutput
      (IntegerModel.programNextToken m) (IntegerModel.promptOf x) (x.e - x.r) with
  | none => rw [hg] at h; exact absurd h (by simp)
  | some l =>
      rw [hg, Option.map_some, Option.some.injEq] at h
      exact congrArg some (List.map_injective_iff.2 Fin.val_injective h)

end Tie

end IntegerModel.Readable
