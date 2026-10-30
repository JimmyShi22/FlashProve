-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/PartAsk.lean: a part of the join whose compiled verifier's analysis holds only of
traces that ask first.

`Part.OK` (OnBytes/TypedOracleCompiler/Slice/Part.lean) asks `JudgeAt` of a part's compiled verifier. This file asks
`JudgeAtAsk` (OnBytes/TypedOracleCompiler/Slice/OneWorldAsk.lean) in its place and gives what the join asks of every
part, `PartO.OK`: a bound FOR EVERY MAKER. Nothing is asked of a maker, and no property of makers
stands in a statement: what is asked first is asked in the proof alone, among the part's typed
oracles.

Main definitions: `Part.OKAsk pre n`; `Part.boundAsk n` (`Part.bound` with the count multiplied by 1
+ n); `Part.toOAsk n` (`Part.toO` with that bound). Main theorems: `Part.pr_lose_ask`;
`Part.toOAsk_ok`; `Part.toOAsk_stable`; `Part.OK.ask` (`Part.OK` gives `OKAsk` at any lawful `pre`;
the bound grows by the factor all the same).

What does not turn: checker, roots, language and the raw string read off a log are `Part.toO`'s
(`toOAsk_raw` and the like by rfl). So the lemmas that speak of these alone serve as they lie
(`Part.raw_offSet`, `SameRaw`, `Stable`, `ok_of_guard`); `toO_byWalks` in one line. NOT the lemmas
that take `JudgeAt` and give `Part.OK` (`on_ok_of`, `on_ok`, `guard_ok_of`, `toO_ok_of_fit`,
`on_toO_ok_of_fit`), through which every real part goes: their forms at `OKAsk` stand in
OnBytes/TypedOracleCompiler/Slice/PartAskGuard.lean.

What is not claimed. No part; no `pre` HERE (one, with its three laws: `preSeed`,
OnBytes/TypedOracleCompiler/Slice/SeedFirstAsk.lean, JudgeOff.lean); `OKAsk` is shown here of nothing but what has
`OK`. THE FACTOR 1 + n STANDS ON THE WHOLE COUNT t + a + tR + tV, in the linear term and, squared,
in the second. All limits in the heads of Part.lean and OneWorldAsk.lean hold here too.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.Part
import OnBytes.TypedOracleCompiler.Slice.OneWorldAsk

set_option autoImplicit false

namespace TypedOracleCompiler.Slice
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop MeasureTheory
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open scoped ENNReal
open OnBytes.Slice (PartO Raw rawOf measurable_twoExp_det Pr_twoExp_det lenB)
open TypedOracleCompiler.Run (OneBlock)

variable {lam : ℕ} {γ Sg : Type}

namespace Part
variable (s : Part lam γ Sg)

/-- `Part.OK` with the analysis' conclusion asked only of traces that ask first. `pre`: what is
to be asked, among the part's typed oracles, before a typed query; n: a bound on its queries. The
other six clauses are `Part.OK`'s. -/
structure OKAsk (pre : (o : (typedOracleFamily lam s.W.K s.L).ι) → (typedOracleFamily lam s.W.K s.L).Dom o →
    TypedOracleComputation lam s.W.K s.L Unit) (n : ℕ) : Prop where
  /-- the analysis' conclusion on the compiled verifier, for traces that ask first -/
  judge : JudgeAtAsk s.W s.J s.e pre
  /-- what is asked first is asked without coins -/
  preNoCoin : ∀ o q, (pre o q).NoCoin
  /-- and with at most n queries -/
  preQueries : ∀ o q, (pre o q).QueryBound n
  /-- the judge's reading reads the same off a trace and off the lengthened trace -/
  blind : ∀ F tr cm, s.J.R.at s.W (lenB pre F tr) cm = s.J.R.at s.W tr cm
  /-- a leaf's and a vertex's answer is one block, taken as it is -/
  one : OneBlock s.m
  /-- the checker tosses no coin -/
  noCoin : ∀ x, (s.chk x).NoCoin
  /-- it asks at most tR strings -/
  queries : ∀ x, (s.chk x).QueryBound s.tR
  /-- at most a roots are read off the maker's output -/
  few : ∀ x, (s.rts x).length ≤ s.a
  /-- under every oracle the compiled verifier accepts what the checker returns, under the family
  that is read out of the oracle through m, and that output is `ok` -/
  fit : ∀ (g : Fam (rom lam)) (x : γ) (o : s.Out), (s.chk x).det g = some o →
    (s.J.run o).det (readBlocks s.m g) = true ∧ s.J.ok o
  /-- the roots of what the checker returns are among those read off the maker's output -/
  named : ∀ (g : Fam (rom lam)) (x : γ) (o : s.Out), (s.chk x).det g = some o →
    ∀ r ∈ s.J.roots o, r ∈ s.rts x

/-- `one_worldJ_ask`'s bound for a maker with at most t queries: `Part.bound` with the count
multiplied by 1 + n. -/
noncomputable def boundAsk (n t : ℕ) : ℝ≥0∞ :=
  (((t + s.a + s.tR + s.J.tV) * (1 + n) : ℕ) : ℝ≥0∞) * s.e +
    2 * (((t + s.a + s.tR + s.J.tV) * (1 + n) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam

variable {s}
variable {pre : (o : (typedOracleFamily lam s.W.K s.L).ι) → (typedOracleFamily lam s.W.K s.L).Dom o → TypedOracleComputation lam s.W.K s.L Unit}
  {n : ℕ}

/-- The part's event has probability at most that bound, FOR EVERY MAKER. -/
theorem pr_lose_ask (hs : s.OKAsk pre n) (A : OComp (rom lam) γ) (t : ℕ) (hA : A.QueryBound t) :
    Rom.Pr A.withTrace s.lose ≤ s.boundAsk n t := by
  have h := one_worldJ_ask s.W s.J s.e pre n hs.preNoCoin hs.preQueries hs.blind hs.judge s.m
    hs.one.leaf1 hs.one.node1 s.chk s.rts s.tR s.a hs.noCoin hs.queries hs.few hs.fit hs.named A t
    hA
  rw [Pr_twoExp_det A s.chk hs.noCoin] at h
  exact h

variable (s) in
/-- The part as it is seen over the one oracle, with that bound: `Part.toO` in every other field. -/
noncomputable def toOAsk (n : ℕ) : PartO lam γ Sg := { s.toO with bound := s.boundAsk n }

/-- What the join asks of every part, from `OKAsk`: a bound for EVERY maker: nothing is asked of
a maker, and no property of makers stands in the statement. -/
theorem toOAsk_ok (hs : s.OKAsk pre n) : (s.toOAsk n).OK where
  rare := fun A t hA => by
    have e : (s.toOAsk n).lose = s.lose := funext s.toO_lose
    rw [e]
    exact pr_lose_ask hs A t hA
  meas := fun A => by
    have e : (s.toOAsk n).lose = s.lose := funext s.toO_lose
    rw [e]
    exact measurable_twoExp_det A s.chk hs.noCoin (winJOne s.W s.m s.J fun _ y => y)

/-- The raw string that is read off a log is `Part.toO`'s. -/
theorem toOAsk_raw : (s.toOAsk n).raw = s.toO.raw := rfl

/-- What the join asks of the first part beside, as `Part.toO_stable`. -/
theorem toOAsk_stable (hs : s.OKAsk pre n) :
    (s.toOAsk n).Stable fun tC tP => 2 * ((tC + 1 + tP : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam := by
  intro β δ C rt P tC tP hC hP
  refine le_trans (Rom.Pr_mono _ fun _ w hw => ?_)
    (stableLeaf_maker s.m hs.one.leaf1 hs.one.node1 C rt P tC tP hC hP)
  obtain ⟨cm, hrt, hne⟩ := hw
  refine ⟨cm, hrt, s.W.depth, ?_⟩
  by_contra hall
  push Not at hall
  exact hne (congrArg (rawOf s.u) (s.J.R.at_congr hall))

/-- `Part.OK` gives `OKAsk`, whatever is asked first without coins, with at most n queries, and
unseen by the reading. -/
theorem OK.ask (hs : s.OK) (hn : ∀ o q, (pre o q).NoCoin) (hq : ∀ o q, (pre o q).QueryBound n)
    (hb : ∀ F tr cm, s.J.R.at s.W (lenB pre F tr) cm = s.J.R.at s.W tr cm) : s.OKAsk pre n :=
  ⟨hs.judge.ask pre, hn, hq, hb, hs.one, hs.noCoin, hs.queries, hs.few, hs.fit, hs.named⟩

end Part

end TypedOracleCompiler.Slice
