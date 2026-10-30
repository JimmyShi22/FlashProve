-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/PartOn.lean: a part of the sibling's compiler: its reading does not see entries of
a log that its look does not read; strings of the call 169 are such; and the part whose checker
answers by a table.

`Part.raw_offSet` and `look_call169` of OnBytes/Slice/WalkOff.lean, and `Part.on` of
OnBytes/Slice/PartChainOn.lean, said again over the sibling (OnBytes/TypedOracleCompiler/), with `Part.on_chk_det`,
`Part.on_ok_of`, `Part.on_ok`, here alone. `Part.raw_offSet`, `Part.on`: the same text. Left out:
`look_other` (its core without the look: `theImpl_other5` of OnBytes/TypedOracleCompiler/Run/PageXJoin.lean),
`look_digestStr`, `look_configStr`. `look_call169` stands on OnBytes/TypedOracleCompiler/Run/PageXJoin.lean's
`inv_call169`, for the sibling's encoding `theImpl C` at any data; `IsCall169` is that file's, the
same text as OnBytes/Slice/WalkOff.lean's.

They are what the join at tables of the oracle's values (OnBytes/Slice/JoinAtSet.lean) wants of a
part beside `PartO.OK` at one oracle: a checker that asks for digests of public bytes is answered by
a table, and `fit` is asked with the checker under the oracle with the table put over it and the
family read out of the oracle itself.

What is not claimed. No part is given. That `fit` in that form holds of any checker. What the heads
of the two files do not claim. The compiler under OnBytes/TypedOracleCompiler/ is the one that
`innerCompiledVerifier` is made with; it builds on definitions of Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Slice.WalksO
import OnBytes.TypedOracleCompiler.Slice.ByWalks

set_option autoImplicit false

namespace TypedOracleCompiler.Slice
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop MeasureTheory
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open scoped ENNReal
open OnBytes.Slice (PartO Raw rawOf Look offSet walk_offSet over pinOn det_pinOn noCoin_pinOn
    queryBound_pinOn)
open TypedOracleCompiler.Run (OneBlock theImpl IsCall169 inv_call169)

variable {lam : ℕ} {γ Sg : Type}

/-- The raw string that a part reads under a root does not see the entries at the strings of S,
if the part's implementation reads none of them as a vertex or as a leaf, and has one block for a
leaf's and a vertex's answer, taken as it is. No condition on the log. -/
theorem Part.raw_offSet (s : Part lam γ Sg) (hm : OneBlock s.m)
    (S : Finset (List Bool)) (hn : ∀ x ∈ S, (lookOf s.m).node x = none)
    (hl : ∀ x ∈ S, (lookOf s.m).leaf x = none) (σ : Trace (rom lam)) (cm : Dig lam) :
    s.raw (offSet S σ) cm = s.raw σ cm := by
  refine congrArg (rawOf s.u) (s.J.R.at_congr fun j => ?_)
  rw [extLeaf_eq_walk s.m hm, extLeaf_eq_walk s.m hm, walk_offSet _ S hn hl]

/-- A part with its checker's queries at the strings of S answered by the table T. All other fields
are the part's own. -/
noncomputable def Part.on (s : Part lam γ Sg) (S : Finset (List Bool)) (T : List Bool → Dig lam) :
    Part lam γ Sg :=
  { s with chk := fun x => pinOn S T (s.chk x) }

/-- Its checker has under g the value that the part's own checker has under g with the table put
over it. -/
theorem Part.on_chk_det (s : Part lam γ Sg) (S : Finset (List Bool)) (T : List Bool → Dig lam)
    (g : Fam (rom lam)) (x : γ) : ((s.on S T).chk x).det g = (s.chk x).det (over S T g) :=
  det_pinOn S T g _

/-- It meets `Part.OK`, if six of the seven clauses hold of s and `fit` holds with the checker
under the oracle with the table put over it and the family read out of the oracle itself. `fit` of s
itself, with checker and family at one oracle, is NOT asked: for a checker that asks at a string of
S, beside an implementation that holds the table's value, it need not hold. Coins and count go over
by `noCoin_pinOn` and `queryBound_pinOn`; the roots by `hnm` at the oracle with the table. -/
theorem Part.on_ok_of (s : Part lam γ Sg) (S : Finset (List Bool)) (T : List Bool → Dig lam)
    (hj : JudgeAt s.W s.J s.e) (h1 : OneBlock s.m) (hn : ∀ x, (s.chk x).NoCoin)
    (hq : ∀ x, (s.chk x).QueryBound s.tR) (hf : ∀ x, (s.rts x).length ≤ s.a)
    (hnm : ∀ (g : Fam (rom lam)) (x : γ) (o : s.Out), (s.chk x).det g = some o →
      ∀ r ∈ s.J.roots o, r ∈ s.rts x)
    (hfit : ∀ (g : Fam (rom lam)) (x : γ) (o : s.Out), (s.chk x).det (over S T g) = some o →
      (s.J.run o).det (readBlocks s.m g) = true ∧ s.J.ok o) : (s.on S T).OK where
  judge := hj
  one := h1
  noCoin := fun x => noCoin_pinOn S T _ (hn x)
  queries := fun x => queryBound_pinOn S T _ _ (hq x)
  few := hf
  fit := fun g x o h => hfit g x o ((det_pinOn S T g _).symm.trans h)
  named := fun g x o h => hnm (over S T g) x o ((det_pinOn S T g _).symm.trans h)

/-- The same where s meets `Part.OK` itself; of that, `fit` is not used. -/
theorem Part.on_ok (s : Part lam γ Sg) (S : Finset (List Bool)) (T : List Bool → Dig lam)
    (hs : s.OK)
    (hfit : ∀ (g : Fam (rom lam)) (x : γ) (o : s.Out), (s.chk x).det (over S T g) = some o →
      (s.J.run o).det (readBlocks s.m g) = true ∧ s.J.ok o) : (s.on S T).OK :=
  s.on_ok_of S T hs.judge hs.one hs.noCoin hs.queries hs.few hs.named hfit

section
variable {I X : Type} {L : BatchProtocolWithLeafBody I X} {K : ℕ} {tg : Tag} (C : TypedOracleCompiler.Run.PageC L K tg)

/-- The string of a call with the number 169 is read neither as a vertex nor as a leaf, through
the sibling's encoding at any data: it is a point of the spare oracle (`TypedOracleCompiler.Run.inv_call169`). -/
theorem look_call169 (s : List Bool) (hs : IsCall169 s) :
    (lookOf (theImpl C)).node s = none ∧ (lookOf (theImpl C)).leaf s = none := by
  have hi := inv_call169 C s hs
  constructor
  · show nodeOf ((theImpl C).inv s).1 ((theImpl C).inv s).2.1 = none
    rw [hi]
    rfl
  · show leafOf ((theImpl C).inv s).1 ((theImpl C).inv s).2.1 = none
    rw [hi]
    rfl

end

end TypedOracleCompiler.Slice
