-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Star.lean: the parameters of the compiled scheme (`Params`) and `erase`, which makes an
ordinary oracle algorithm of a token program (words of this library: lean/GLOSSARY.md). The scheme
itself is in Compile/Batch/Star.lean.
-/
import Compile.Bcs

noncomputable section

namespace Compile
open Iop Rom

/-- Forget the rules: tokens are strings, kept in a list; fresh = sample; marked = query; reveal =
read. -/
def erase {S : OSpec} {sp : Split S} {α : Type} : Step S sp α → List Bits → OComp S (α × List Bits)
  | .pure a, vs => .pure (a, vs)
  | .sample n k, vs => .sample n fun r => erase (k r) vs
  | .plain o q k, vs => .query o q fun r => erase (k r) vs
  | .fresh ℓ k, vs =>
    .sample (2 ^ ℓ - 1) fun r =>
      erase (k vs.length) (vs ++ [List.ofFn fun i : Fin ℓ => r.val.testBit i])
  | .marked o t us pt _ k, vs => .query o (pt (vs.getD t []) (us.map fun u => vs.getD u [])) fun r =>
      erase (k (sp.split o r).1 vs.length) (vs ++ [List.ofFn (sp.split o r).2])
  | .reveal ts k, vs => erase (k (ts.map fun u => vs.getD u [])) vs

structure Params where
  sMT : ℕ
  sFS : ℕ
  /-- the number of copies is M + 1 -/
  M : ℕ
  s1 : ℕ

end Compile
