-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
IntegerModel/Reply.lean: the library's integer program as a function from a list of tokens to the
next token, and what it means that the reply in a request is that function's. Definitions, with one
lemma that a definition needs.
- `Committed`: lawful quantization settings with integer weights.
- `programNextToken m ctx`: the next token after the tokens `ctx`; `greedyOutput`: n tokens, one
  after the other.
- `IsReply m x`: the reply tokens of the request x are what `programNextToken m` outputs after x's
  context. `Says m x`: the same, position by position. `IsModelOutput`: the same for two lists of
  tokens (true of an empty output).
- `HoldsOnWindow pp i x`: a sentence on one pass of the program over the 1,024 tokens of x.
- `requestWellFormed x`: the test on the two numbers r, e and the token y of x.
How they are related: IntegerModel/ReplyOnWindow.lean (`holdsOnWindow_iff`); the tie to the proof
system's relation: IntegerModel/TrueRequest.lean. A function on arrays, in a file without imports
(IntegerModel/Model.lean), gives the answers of `programNextToken m` at the arrays made from m's
numbers and from the five fixed tables: IntegerModel/Readable/AtCommitted.lean (`modelOf_eq`).
-/
import Inst.Model.Scales

set_option autoImplicit false

open Inst.Model

/- No default table of scales here: `Scl.ref` (Inst/Model/Scl.lean) is off; each `Scl` is named. -/
attribute [-instance] Inst.Model.Scl.ref

namespace IntegerModel

/-! ## 1. The model
It builds on Inst/Model/Program.lean, ProgramR.lean, ProgTests.lean, Scales.lean, FF/ScalesDef.lean,
Tables.lean, TablesRef.lean and TablesData.lean. -/

/-- The quantization constants. For each of 48 layers: ten shifts, two normalisations of
three numbers each and one further shift. Then the final normalisation and the three numbers of an
acceptance policy. No function in this file reads the policy; `Committed` asks only that it be
lawful. -/
abbrev Settings : Type := ScalesAndPolicy
/-- Integer tensors of Maverick's shapes, every entry in its range. "Maverick" is only a name for
the sizes in `ppref`; no statement in this file mentions it. -/
abbrev Weights : Type := Index ppref
abbrev Token : Type := Fin ppref.V
/-- A request: 1,024 tokens, an announced token y, and two numbers r, e ≤ 1,024. The covered
positions are r ≤ t < e. The token checked at position t is `w t`: token t + 1, or y at t = 1,023.
Tokens are counted from 0. -/
abbrev Request : Type := Instance ppref

/-- The arguments of the model function: lawful settings (`Lawful`, Inst/Model/Scales.lean) and the
integer weights. No statement ties them to any given model. "Lawful" excludes division by zero
(`sigK_pos`, Inst/Model/ScalesSanity.lean), not nonsense: Cm/Rel2Idle.lean has two lawful tables
(`Cm.lawful_idle`, `Cm.lawful_flat`: lawful as `Cm.Scales`, which by `Cm.lawful_iff`,
Cm/Rel2Proofs.lean, is `Lawful` with the policy of exact match) and tells, in part by hand, why the
statements say little of the weights there. -/
structure Committed where
  settings : Settings
  weights : Weights
  lawful : Lawful settings

local instance (a : ℤ) : Decidable (Fits16 a) := by unfold Fits16; infer_instance
local instance (np : NormPar) (d : ℕ) (x : Vec) : Decidable (NORM.OK np d x) := by
  unfold NORM.OK; infer_instance
local instance (d : ℕ) (z wg wu : Vec) (k k' : ℕ) : Decidable (UNIT.OK d z wg wu k k') := by
  unfold UNIT.OK; infer_instance
local instance (P : Params) (tb : Tables) (w : LayerW) (L : ℕ) (x : ℕ → Vec) :
    Decidable (Att.OK P tb w L x) := by unfold Att.OK; infer_instance
local instance (P : Params) (tb : Tables) (w : LayerW) (L : ℕ) (x : ℕ → Vec) :
    Decidable (FF.OK P tb w L x) := by unfold FF.OK; infer_instance
local instance (P : Params) (κ : ℕ → LayerScale) (nf : NormPar) (tbs : ℕ → Tables)
    (i : Inst.Model.Weights) (p : Fin P.T → Fin P.V) : Decidable (RunsK P κ nf tbs i p) := by
  unfold RunsK; infer_instance

/-- Maverick's sizes, for a context of n tokens. -/
def arch (n : ℕ) : Params := { ppref with T := n }

theorem argTo_lt (f : Vec) : argTo f (ppref.V - 1) < ppref.V :=
  Nat.lt_of_le_of_lt (argTo_spec f _).1 (by decide)

/-- The model: the integer program run on the tokens of `ctx` only, with the library's five fixed
tables `tbRef`. The answer is the least token with the largest logit at the last position. It is
`none` if `ctx` is empty or longer than 1,024, or if a range condition of the program (`RunsK`,
Inst/Model/Program.lean) fails at some position of `ctx`. `programNextToken` is computable in Lean's
sense, but this file never evaluates it; the full size (`ppref`) is its only size, but for the
number of tokens. -/
def programNextToken (m : Committed) (ctx : List Token) : Option Token :=
  if 0 < ctx.length ∧ ctx.length ≤ ppref.T ∧
      RunsK (arch ctx.length) m.settings.kap m.settings.nf (fun _ => tbRef) m.weights.val
        (fun i => ctx.get i) then
    some ⟨argTo (lgK (arch ctx.length) m.settings.kap m.settings.nf (fun _ => tbRef) m.weights.val
      (fun i => ctx.get i) (ctx.length - 1)) (ppref.V - 1), argTo_lt _⟩
  else none

/-- n tokens, each being f's answer on the context followed by the tokens before it; `none` if f
returns `none` on the way. -/
def greedyOutput (f : List Token → Option Token) : List Token → ℕ → Option (List Token)
  | _, 0 => some []
  | ctx, n + 1 => match f ctx with
    | none => none
    | some y => (greedyOutput f (ctx ++ [y]) n).map (y :: ·)

/-! ## 2. The reply in a request -/

/-- The request's first k tokens (token 1,024 is the announced y). -/
def firstToks (x : Request) (k : ℕ) : List Token :=
  (List.range k).map fun j => ⟨x.tok j, x.tok_lt j⟩
/-- The context: tokens 0 .. r, that is r + 1 tokens. r is the last position of the context, not its
length. -/
def promptOf (x : Request) : List Token := firstToks x (x.r + 1)
/-- The reply: the checked tokens r + 1 .. e (token 1,024 is y). -/
def replyOf (x : Request) : List Token :=
  (List.range (x.e - x.r)).map fun j => ⟨x.w (x.r + j), x.w_lt _⟩

/-- The reply is the model's: the request covers at least one position, and its reply tokens are
what `programNextToken` outputs, token by token, after its context. `HoldsOnWindow` (below) implies
it (IntegerModel/ReplyOnWindow.lean: `holdsOnWindow_iff`). `IsReply` omits two parts of
`HoldsOnWindow`: y = 0 where e < 1,024, and the range conditions at the positions from e on. -/
def IsReply (m : Committed) (x : Request) : Prop :=
  x.r < x.e ∧ greedyOutput (programNextToken m) (promptOf x) (x.e - x.r) = some (replyOf x)

/-- The same, position by position; equivalent to `IsReply` (IntegerModel/ReplyOnWindow.lean:
`isReply_iff`). -/
def Says (m : Committed) (x : Request) : Prop :=
  x.r < x.e ∧ ∀ t, x.r ≤ t → t < x.e → programNextToken m (firstToks x (t + 1)) = some
      ⟨x.w t, x.w_lt t⟩

/-- The output tokens are the model's: each of them is `programNextToken`'s result after the prompt
and the output tokens before it. Nothing is said on whether the model would continue. -/
def IsModelOutput (m : Committed) (prompt output : List Token) : Prop :=
  ∀ (position : ℕ) (h : position < output.length),
    programNextToken m (prompt ++ output.take position) = some output[position]

/-! ## 3. One pass over the window -/

/-- The sentence on one pass over the window: the request is well-formed; the program runs on its
1,024 tokens; at every covered position the checked token is the least token of largest logit. -/
def HoldsOnWindow (pp : ScalesAndPolicy) (i : Index ppref) (x : Instance ppref) : Prop :=
  (x.r < x.e ∧ x.e ≤ ppref.T ∧ (x.e < ppref.T → x.y.val = 0)) ∧
    RunsK ppref pp.kap pp.nf (fun _ => tbRef) i.val x.prompt ∧
      ∀ t, x.r ≤ t → t < x.e →
        (∀ v < ppref.V, lgK ppref pp.kap pp.nf (fun _ => tbRef) i.val x.prompt t v ≤
          lgK ppref pp.kap pp.nf (fun _ => tbRef) i.val x.prompt t (x.w t)) ∧
        ∀ v < x.w t, lgK ppref pp.kap pp.nf (fun _ => tbRef) i.val x.prompt t v <
          lgK ppref pp.kap pp.nf (fun _ => tbRef) i.val x.prompt t (x.w t)

/-- The request's form (Inst/Model/ProgramR.lean: `Head3`), as a test: r < e, e ≤ T, and y = 0 where
e < T. It is true exactly when these three clauses hold (IntegerModel/ReplyOnWindow.lean:
`form_of_requestWellFormed`, `requestWellFormed_of_form`). -/
def requestWellFormed (x : Instance ppref) : Bool :=
  decide (x.r < x.e) && decide (x.e ≤ ppref.T) && (!decide (x.e < ppref.T) || decide (x.y.val = 0))

end IntegerModel
