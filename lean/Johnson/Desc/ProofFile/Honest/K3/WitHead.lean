-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/WitHead.lean: the honest side of the kind "lookup" (K3): at the
head's calls the shape and the layout are the public part's own: of the instance the filling takes
the covered positions and the checked tokens alone. Definitions with code, and small theorems by
rfl.

Terms. Honest/K3/GLOSSARY.md.

Why. In the fillings of Honest/K3/WitDigits.lean the head's public data are a letter pubH : Xi →
PubH, a whole structure: shape, layout, the stream's border, covered positions, checked tokens, the
weights' layout. Nothing tied its shape and layout to the public part's. Here four of the six fields
are taken from the public part, as `pubHAt` (Johnson/HonestTrace/FullPlanes.lean) takes them; what
is left of the letter is req : Xi → Head.Covered × Array ℕ.

What is defined and shown.
  `headPub`: the head's public data, as a function of the public part, covered positions and checked
    tokens.
  `headPub_h`, `headPub_L`, `headPub_fs`, `headPub_lay`: its shape, layout, lookup's shape and
    weights' layout are the public part's.
  `pubHAt_eq`: `pubHAt X x` of the trace's files is `headPub` at that request's positions and
    tokens.
  `tiedPlanSources`, `tiedSources`: the two fillings with the head tied to the public part.

Hypotheses that remain. None.

Users. `tiedOwnSources` (Honest/K3/WitOwner.lean) calls `headPub`. Tests in
Honest/K3/WitHeadPlayNF.lean [not in this library], Honest/K3/WitAttnPlayQa.lean
[not in this library], Honest/K3/WitReadsHead.lean [not in this library] and
Honest/K3/WitReadsOwn.lean [not in this library], among others, evaluate `tiedPlanSources`. No other
file names `tiedSources`.

Limits. req is a letter: public data of the instance.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.WitDigits

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3

/-- **The head's public data**: shape, layout, the stream's border and the weights' layout are the
public part's. -/
def headPub (X : OnBytes.Model.Verify.Public) (cov : OnBytes.Model.Head.Covered) (win : Array ℕ) :
    OnBytes.Ends.H.PubH :=
  ⟨X.hS, X.HLy, OnBytes.Model.Verify.borderOf X.y, cov, win, X.layers.wsLay⟩

section
variable (X : OnBytes.Model.Verify.Public) (cov : OnBytes.Model.Head.Covered) (win : Array ℕ)

theorem headPub_h : (headPub X cov win).h = X.hS := rfl

theorem headPub_L : (headPub X cov win).L = X.HLy := rfl

/-- The shape by which the head's keys and bits are numbered is the public part's. -/
theorem headPub_fs : (headPub X cov win).L.fs = X.HLy.fs := rfl

theorem headPub_lay : (headPub X cov win).lay = X.layers.wsLay := rfl

end

/-- The structure of the trace's files at a request is `headPub` at that request's covered positions
and its tokens at the 1,024 positions. -/
theorem pubHAt_eq (X : OnBytes.Model.Verify.Public) (x : Inst.Model.Instance Inst.Model.ppref) :
    OnBytes.HonestTrace.pubHAt X x =
      headPub X (OnBytes.Road.Hd.covReq x) ((Array.range 1024).map x.w) := rfl

/-- **The filling by the public part's own numbers, the head tied.** Here req gives, of
the instance, the covered positions and the token that is checked at each. -/
def tiedPlanSources {W₀ Xi Tr' : Type} (X : OnBytes.Model.Verify.Public) (cells : Tr' → Cells)
    (weights : W₀ → Weights) (req : Xi → OnBytes.Model.Head.Covered × Array ℕ) :
    Sources W₀ Xi Tr' :=
  thePlanSources X cells weights fun x => headPub X (req x).1 (req x).2

/-- **The filling at the full size, the head tied.** -/
def tiedSources {W₀ Xi Tr' : Type} (X : OnBytes.Model.Verify.Public) (cells : Tr' → Cells)
    (weights : W₀ → Weights) (req : Xi → OnBytes.Model.Head.Covered × Array ℕ) :
    Sources W₀ Xi Tr' :=
  theSources X cells weights fun x => headPub X (req x).1 (req x).2

end ProofFile.Honest.K3

#print axioms ProofFile.Honest.K3.headPub_h
#print axioms ProofFile.Honest.K3.headPub_L
#print axioms ProofFile.Honest.K3.headPub_fs
#print axioms ProofFile.Honest.K3.headPub_lay
#print axioms ProofFile.Honest.K3.pubHAt_eq
