-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/PartAskGuard.lean: the doors through which a real part reaches what the join asks,
for a part whose analysis holds only of traces that ask first.

OnBytes/TypedOracleCompiler/Slice/PartOn.lean and PartGuard.lean have the lemmas through which a part goes whose
checker answers some strings by a table, or whose `fit` holds only where no two strings of the
checker's own log have one answer. They take `JudgeAt` and give `Part.OK`. This file says them again
with `JudgeAtAsk` and the three laws on `pre` (OnBytes/TypedOracleCompiler/Slice/OneWorldAsk.lean, PartAsk.lean):
they give `Part.OKAsk`, and `PartO.OK` of `Part.toOAsk`.

Main theorems: `Part.on_okAsk_of`; `Part.guard_okAsk_of`; `Part.toOAsk_guard` (by rfl);
`Part.toOAsk_ok_of_fit`; `Part.on_toOAsk_ok_of_fit`. The proofs are the sources' texts.

What is not claimed. No part, no `pre`. All limits in the heads of PartOn.lean, PartGuard.lean,
PartAsk.lean and OneWorldAsk.lean hold here too: above all, a clash between a value of the table and
the answer at an asked string is not seen by the guard.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.PartAsk
import OnBytes.TypedOracleCompiler.Slice.PartGuard

set_option autoImplicit false

namespace TypedOracleCompiler.Slice
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop MeasureTheory
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open scoped ENNReal
open OnBytes.Slice (PartO NoClash offSet over det_pinOn noCoin_pinOn queryBound_pinOn
  det_withTrace_pinOn lenB)
open TypedOracleCompiler.Run (OneBlock)

variable {lam : ℕ} {γ Sg : Type}

namespace Part
variable (s : Part lam γ Sg)

/-- The part whose checker answers by a table meets `OKAsk`: `Part.on_ok_of`
(OnBytes/TypedOracleCompiler/Slice/PartOn.lean) with `JudgeAtAsk` and the three laws on `pre` for `JudgeAt`. -/
theorem on_okAsk_of (S : Finset (List Bool)) (T : List Bool → Dig lam)
    (pre : (o : (typedOracleFamily lam s.W.K s.L).ι) → (typedOracleFamily lam s.W.K s.L).Dom o → TypedOracleComputation lam s.W.K s.L Unit)
    (n : ℕ)
    (hj : JudgeAtAsk s.W s.J s.e pre) (hpn : ∀ o q, (pre o q).NoCoin)
    (hpq : ∀ o q, (pre o q).QueryBound n)
    (hb : ∀ F tr cm, s.J.R.at s.W (lenB pre F tr) cm = s.J.R.at s.W tr cm)
    (h1 : OneBlock s.m) (hn : ∀ x, (s.chk x).NoCoin)
    (hq : ∀ x, (s.chk x).QueryBound s.tR) (hf : ∀ x, (s.rts x).length ≤ s.a)
    (hnm : ∀ (g : Fam (rom lam)) (x : γ) (o : s.Out), (s.chk x).det g = some o →
      ∀ r ∈ s.J.roots o, r ∈ s.rts x)
    (hfit : ∀ (g : Fam (rom lam)) (x : γ) (o : s.Out), (s.chk x).det (over S T g) = some o →
      (s.J.run o).det (readBlocks s.m g) = true ∧ s.J.ok o) : (s.on S T).OKAsk pre n where
  judge := hj
  preNoCoin := hpn
  preQueries := hpq
  blind := hb
  one := h1
  noCoin := fun x => noCoin_pinOn S T _ (hn x)
  queries := fun x => queryBound_pinOn S T _ _ (hq x)
  few := hf
  fit := fun g x o h => hfit g x o ((det_pinOn S T g _).symm.trans h)
  named := fun g x o h => hnm (over S T g) x o ((det_pinOn S T g _).symm.trans h)

/-- The guarded part meets `OKAsk`: `Part.guard_ok_of` (OnBytes/TypedOracleCompiler/Slice/PartGuard.lean) with
`JudgeAtAsk` and the three laws on `pre` for `JudgeAt`. -/
theorem guard_okAsk_of
    (pre : (o : (typedOracleFamily lam s.W.K s.L).ι) → (typedOracleFamily lam s.W.K s.L).Dom o → TypedOracleComputation lam s.W.K s.L Unit)
    (n : ℕ)
    (hj : JudgeAtAsk s.W s.J s.e pre) (hpn : ∀ o q, (pre o q).NoCoin)
    (hpq : ∀ o q, (pre o q).QueryBound n)
    (hb : ∀ F tr cm, s.J.R.at s.W (lenB pre F tr) cm = s.J.R.at s.W tr cm)
    (h1 : OneBlock s.m) (hn : ∀ x, (s.chk x).NoCoin)
    (hq : ∀ x, (s.chk x).QueryBound s.tR) (hf : ∀ x, (s.rts x).length ≤ s.a)
    (hnm : ∀ (g : Fam (rom lam)) (x : γ) (o : s.Out), (s.chk x).det g = some o →
      ∀ r ∈ s.J.roots o, r ∈ s.rts x)
    (hfit : ∀ (g : Fam (rom lam)) (x : γ) (o : s.Out), NoClash (s.toO.ownLog g x) →
      (s.chk x).det g = some o → (s.J.run o).det (readBlocks s.m g) = true ∧ s.J.ok o) :
    s.guard.OKAsk pre n := by
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
      preNoCoin := hpn
      preQueries := hpq
      blind := hb
      one := h1
      noCoin := fun x => s.toO.guard_noCoin hn x
      queries := fun x => s.toO.guard_queryBound s.tR hq x
      few := hf
      fit := fun g x o h => hfit g x o (key g x o h).1 (key g x o h).2
      named := fun g x o h => hnm g x o (key g x o h).2 }

/-- Over the one oracle the guarded part with the bound at the multiplied count is the guarded form
of `toOAsk`. -/
theorem toOAsk_guard (n : ℕ) : s.guard.toOAsk n = (s.toOAsk n).guard := rfl

/-- Then the part itself, over the one oracle, has `PartO.OK`, with (t + tR)^2 / 2^lam more in
its bound: `Part.toO_ok_of_fit` at `toOAsk`. -/
theorem toOAsk_ok_of_fit
    (pre : (o : (typedOracleFamily lam s.W.K s.L).ι) → (typedOracleFamily lam s.W.K s.L).Dom o → TypedOracleComputation lam s.W.K s.L Unit)
    (n : ℕ)
    (hj : JudgeAtAsk s.W s.J s.e pre) (hpn : ∀ o q, (pre o q).NoCoin)
    (hpq : ∀ o q, (pre o q).QueryBound n)
    (hb : ∀ F tr cm, s.J.R.at s.W (lenB pre F tr) cm = s.J.R.at s.W tr cm)
    (h1 : OneBlock s.m)
    (hn : ∀ x, (s.chk x).NoCoin) (hq : ∀ x, (s.chk x).QueryBound s.tR)
    (hf : ∀ x, (s.rts x).length ≤ s.a)
    (hnm : ∀ (g : Fam (rom lam)) (x : γ) (o : s.Out), (s.chk x).det g = some o →
      ∀ r ∈ s.J.roots o, r ∈ s.rts x)
    (hfit : ∀ (g : Fam (rom lam)) (x : γ) (o : s.Out), NoClash (s.toO.ownLog g x) →
      (s.chk x).det g = some o → (s.J.run o).det (readBlocks s.m g) = true ∧ s.J.ok o) :
    ({ s.toOAsk n with
        bound := fun t => (s.toOAsk n).bound t + (((t + s.tR) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ lam } :
      PartO lam γ Sg).OK :=
  (s.toOAsk n).ok_of_guard hn s.tR hq
    (toOAsk_ok (s.guard_okAsk_of pre n hj hpn hpq hb h1 hn hq hf hnm hfit))

/-- The same for the part whose checker answers by a table: `Part.on_toO_ok_of_fit` at
`toOAsk`. -/
theorem on_toOAsk_ok_of_fit (S : Finset (List Bool)) (T : List Bool → Dig lam)
    (pre : (o : (typedOracleFamily lam s.W.K s.L).ι) → (typedOracleFamily lam s.W.K s.L).Dom o → TypedOracleComputation lam s.W.K s.L Unit)
    (n : ℕ)
    (hj : JudgeAtAsk s.W s.J s.e pre) (hpn : ∀ o q, (pre o q).NoCoin)
    (hpq : ∀ o q, (pre o q).QueryBound n)
    (hb : ∀ F tr cm, s.J.R.at s.W (lenB pre F tr) cm = s.J.R.at s.W tr cm)
    (h1 : OneBlock s.m) (hn : ∀ x, (s.chk x).NoCoin)
    (hq : ∀ x, (s.chk x).QueryBound s.tR) (hf : ∀ x, (s.rts x).length ≤ s.a)
    (hnm : ∀ (g : Fam (rom lam)) (x : γ) (o : s.Out), (s.chk x).det g = some o →
      ∀ r ∈ s.J.roots o, r ∈ s.rts x)
    (hfit : ∀ (g : Fam (rom lam)) (x : γ) (o : s.Out),
      NoClash (offSet S (s.toO.ownLog (over S T g) x)) → (s.chk x).det (over S T g) = some o →
      (s.J.run o).det (readBlocks s.m g) = true ∧ s.J.ok o) :
    ({ (s.on S T).toOAsk n with
        bound := fun t => ((s.on S T).toOAsk n).bound t +
          (((t + s.tR) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ lam } : PartO lam γ Sg).OK :=
  (s.on S T).toOAsk_ok_of_fit pre n hj hpn hpq hb h1 (fun x => noCoin_pinOn S T _ (hn x))
    (fun x => queryBound_pinOn S T _ _ (hq x)) hf
    (fun g x o h => hnm (over S T g) x o ((det_pinOn S T g _).symm.trans h))
    (fun g x o hc h => hfit g x o ((det_withTrace_pinOn S T g (s.chk x)) ▸ hc)
      ((det_pinOn S T g _).symm.trans h))

end Part

end TypedOracleCompiler.Slice
