-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/PartGuard.lean: a part of the sibling's compiler whose checker's reader may part
from the compiled verifier where two strings of the checker's own log have one answer.

OnBytes/Slice/Guard.lean pays, over the one oracle alone, for the oracles under which two strings of
a checker's own log have one answer. This file brings that to a part of the sibling's compiler
(OnBytes/TypedOracleCompiler/Slice/Part.lean): it is enough to show the clause `fit` under the oracles under which
the checker's own log has no such two strings.

Main definition: `Part.guard s`: s with the guarded checker; `Part.toO_guard`: its `toO` is
`PartO.guard` of s's, by definition.
Main theorems.
 `Part.guard_ok_of` the guarded part meets `Part.OK` if six of the seven clauses hold of s and `fit`
     holds where the checker's own log has no clash.
 `Part.toO_ok_of_fit` then s's `toO`, with (t + tR)^2 / 2^lam more in its bound, has `PartO.OK`.
 `Part.on_toO_ok_of_fit` the same for the part whose checker answers by a table (`Part.on`).

What is not claimed. No part is given. All limits in the heads of the two files hold here too. The
compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on
definitions of Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Slice.GuardOn
import OnBytes.TypedOracleCompiler.Slice.PartOn

set_option autoImplicit false

namespace TypedOracleCompiler.Slice
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop MeasureTheory
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open scoped ENNReal
open OnBytes.Slice (PartO NoClash offSet over det_pinOn noCoin_pinOn queryBound_pinOn
  det_withTrace_pinOn)
open TypedOracleCompiler.Run (OneBlock)

variable {lam : ℕ} {γ Sg : Type}

namespace Part
variable (s : Part lam γ Sg)

open Classical in
/-- The part whose checker refuses where two strings of its own log have one answer. All other
fields are the part's own. -/
noncomputable def guard : Part lam γ Sg :=
  { s with chk := fun x => (s.chk x).withTrace.bind fun o =>
      OComp.pure (if NoClash o.2 then o.1 else none) }

/-- Over the one oracle it is the guarded part of OnBytes/Slice/Guard.lean. -/
theorem toO_guard : s.guard.toO = s.toO.guard := rfl

/-- The guarded part meets `Part.OK`, if six of the seven clauses hold of s and `fit` holds
under every oracle under which no two strings of the checker's own log have one answer. -/
theorem guard_ok_of (hj : JudgeAt s.W s.J s.e) (h1 : OneBlock s.m) (hn : ∀ x, (s.chk x).NoCoin)
    (hq : ∀ x, (s.chk x).QueryBound s.tR) (hf : ∀ x, (s.rts x).length ≤ s.a)
    (hnm : ∀ (g : Fam (rom lam)) (x : γ) (o : s.Out), (s.chk x).det g = some o →
      ∀ r ∈ s.J.roots o, r ∈ s.rts x)
    (hfit : ∀ (g : Fam (rom lam)) (x : γ) (o : s.Out), NoClash (s.toO.ownLog g x) →
      (s.chk x).det g = some o → (s.J.run o).det (readBlocks s.m g) = true ∧ s.J.ok o) :
    s.guard.OK := by
  have key : ∀ (g : Fam (rom lam)) (x : γ) (o : s.Out), (s.guard.chk x).det g = some o →
      NoClash (s.toO.ownLog g x) ∧ (s.chk x).det g = some o := by
    intro g x o h
    have h' := (s.toO.guard_det g x).symm.trans h
    by_cases hc : NoClash (s.toO.ownLog g x)
    · rw [if_pos hc] at h'
      exact ⟨hc, h'⟩
    · rw [if_neg hc] at h'
      cases h'
  exact
    { judge := hj
      one := h1
      noCoin := fun x => s.toO.guard_noCoin hn x
      queries := fun x => s.toO.guard_queryBound s.tR hq x
      few := hf
      fit := fun g x o h => hfit g x o (key g x o h).1 (key g x o h).2
      named := fun g x o h => hnm g x o (key g x o h).2 }

/-- Then the part itself, over the one oracle, has `PartO.OK`, with (t + tR)^2 / 2^lam more in
its bound. -/
theorem toO_ok_of_fit (hj : JudgeAt s.W s.J s.e) (h1 : OneBlock s.m)
    (hn : ∀ x, (s.chk x).NoCoin) (hq : ∀ x, (s.chk x).QueryBound s.tR)
    (hf : ∀ x, (s.rts x).length ≤ s.a)
    (hnm : ∀ (g : Fam (rom lam)) (x : γ) (o : s.Out), (s.chk x).det g = some o →
      ∀ r ∈ s.J.roots o, r ∈ s.rts x)
    (hfit : ∀ (g : Fam (rom lam)) (x : γ) (o : s.Out), NoClash (s.toO.ownLog g x) →
      (s.chk x).det g = some o → (s.J.run o).det (readBlocks s.m g) = true ∧ s.J.ok o) :
    ({ s.toO with bound := fun t => s.toO.bound t + (((t + s.tR) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ lam } :
      PartO lam γ Sg).OK :=
  s.toO.ok_of_guard hn s.tR hq (s.guard.toO_ok (s.guard_ok_of hj h1 hn hq hf hnm hfit))

/-- The same for the part whose checker answers by a table (`Part.on`), as the join at tables of
the oracle's values takes its parts: `fit` is asked with the checker under the oracle with the table
put over it and the family read out of the oracle itself, and only where the checker's log under
that oracle, WITHOUT the entries at the strings of the table, has no two strings with one answer. A
clash between a value of the table and the answer at an asked string is not seen by this guard:
`hfit` must hold there too. -/
theorem on_toO_ok_of_fit (S : Finset (List Bool)) (T : List Bool → Dig lam)
    (hj : JudgeAt s.W s.J s.e) (h1 : OneBlock s.m) (hn : ∀ x, (s.chk x).NoCoin)
    (hq : ∀ x, (s.chk x).QueryBound s.tR) (hf : ∀ x, (s.rts x).length ≤ s.a)
    (hnm : ∀ (g : Fam (rom lam)) (x : γ) (o : s.Out), (s.chk x).det g = some o →
      ∀ r ∈ s.J.roots o, r ∈ s.rts x)
    (hfit : ∀ (g : Fam (rom lam)) (x : γ) (o : s.Out),
      NoClash (offSet S (s.toO.ownLog (over S T g) x)) → (s.chk x).det (over S T g) = some o →
      (s.J.run o).det (readBlocks s.m g) = true ∧ s.J.ok o) :
    ({ (s.on S T).toO with
        bound := fun t => (s.on S T).toO.bound t + (((t + s.tR) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ lam } :
      PartO lam γ Sg).OK :=
  (s.on S T).toO_ok_of_fit hj h1 (fun x => noCoin_pinOn S T _ (hn x))
    (fun x => queryBound_pinOn S T _ _ (hq x)) hf
    (fun g x o h => hnm (over S T g) x o ((det_pinOn S T g _).symm.trans h))
    (fun g x o hc h => hfit g x o ((det_withTrace_pinOn S T g (s.chk x)) ▸ hc)
      ((det_pinOn S T g _).symm.trans h))

end Part

end TypedOracleCompiler.Slice
