-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/- IntegerModel/Runnable/ArrayNext.lean: two additions to the array program of
IntegerModel/Runnable/ArrayModel.lean: the next token after a context; the check on the settings.
Core Lean only. -/
import IntegerModel.Runnable.ArrayModel

namespace ArrayProgram

/-- The next token: the model's first choice after the tokens of ctx. It runs the layers on the
tokens of ctx only, without filling up to S.T. It is none if ctx is empty, or longer than the
shape's window S.T, or holds a number that is not a token (S.V or more), or a range condition fails
at some position of ctx. -/
def next (S : Shape) (tb : Tables) (st : Settings) (W : Weights) (ctx : Array Nat) : Option Nat :=
  if 0 < ctx.size && ctx.size ≤ S.T && ctx.all (· < S.V) then do
    let n ← (← stream S tb st W ctx).mapM (rmsNorm st.final)
    return argmaxFirst (row S.V fun v => dot n[ctx.size - 1]! (W.head · v))
  else none

/-! ## Which settings are lawful at Maverick's sizes

The intervals are those of the library's Lawful (Inst/Model/Scales.lean; proved the same in
IntegerModel/Runnable/Lawful.lean). They depend on the sizes: these are the ones for `modelShape`.
Limit: settings with a scale outside them (for instance kd = 9) fail the test whatever sizes they
are made for, and the library's theorems for lawful settings say nothing of them.

As in the library, kr, kgR, kuR are tested in the dense layers too, where nothing reads them: anyone
who fills a Settings must put numbers inside the intervals there. The Lawful of
Inst/Model/Scales.lean also bounds three numbers of the acceptance policy; these are not part of the
model and are not here.
-/

def Norm.lawful (n : Norm) : Bool :=
  1 ≤ n.eps && n.eps < 2 ^ 48 && 24 ≤ n.M && n.M ≤ 47 && 17 ≤ n.K && n.K ≤ 32 &&
    n.M - 14 ≤ n.K && n.K ≤ n.M

def LayerScales.lawful (s : LayerScales) : Bool :=
  5 ≤ s.kq && s.kq ≤ 32 && 5 ≤ s.kk && s.kk ≤ 32 && (s.kq == s.kk || (16 ≤ s.kq && 16 ≤ s.kk)) &&
    1 ≤ s.kv && s.kv ≤ 24 && 1 ≤ s.ko && s.ko ≤ 19 && 1 ≤ s.kg && s.kg ≤ 24 && 1 ≤ s.kgR &&
    s.kgR ≤ 24 && 1 ≤ s.ku && s.ku ≤ 24 && 1 ≤ s.kuR && s.kuR ≤ 24 && 10 ≤ s.kd && s.kd ≤ 19 &&
    8 ≤ s.kr && s.kr ≤ 24 && s.norm1.lawful && s.norm2.lawful && 4 ≤ s.sh && s.sh ≤ 12

/-- Every layer's scales and the final norm are in their intervals, with kq = kk unless both are at
least 16, and with M - 14 ≤ K ≤ M in each norm, and the softmax's shift sh has one value in each
group of four layers. Of S it reads only the number of layers. -/
def lawful (S : Shape) (st : Settings) : Bool :=
  (List.range S.layers).all
      (fun L => (st.layer L).lawful && (st.layer L).sh == (st.layer (4 * (L / 4))).sh) &&
    st.final.lawful

end ArrayProgram
