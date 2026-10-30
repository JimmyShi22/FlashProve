-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/ShapesConv.lean: "type, then run" where the typing is a plain converter, and the
checker's value in one world.

`chkT` (OnBytes/TypedOracleCompiler/Slice/ShapesTyping.lean) is the checker "type, then run": a typing makes of the
five files what the part's typed verifier takes in; then that verifier is run over the one oracle
through the part's implementation.

Main definitions: `pureTyp c`: a plain function c of the files as a typing. It asks the oracle
nothing.
Main theorems.
 `chkT_det_eq` the checker's value, whatever the typing: the typing's value, if the typed verifier
     accepts it under the family read out of the oracle; else nothing.
 `pureTyp_noCoin`, `pureTyp_queries`, `pureTyp_det` no coin; no string; under every oracle the
     converter's value.
 `chkT_pure_det` pre-process, then run: the value.
 `FileSpec.merge_own`, `FileSpec.chk_own` in one world the pin is nothing: at the oracle's own
     tables the checker of the part as the bound sees it has, under that oracle, the value of the
     part's own checker.

What is not claimed. Nothing on any converter or any part. `det` is the run with every coin 0. No
probability.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.ShapesOne
import OnBytes.Slice.OverSelf

set_option autoImplicit false

namespace OnBytes.Slice.Shapes
open Iop Rom Prob
open scoped ENNReal

/-- The value of "type, then run", whatever the typing: the typing's value, if the part's typed
verifier accepts it under the family that is read out of the oracle through the part's
implementation; else nothing. -/
theorem chkT_det_eq (p : TypedOracleCompiler.Slice.Part 256 Files Run.PQ.SgX)
    (typ : Files → OComp (rom 256) (Option p.Out)) (x : Files) (g : Fam (rom 256)) :
    (chkT p typ x).det g = ((typ x).det g).bind fun o =>
      if (p.J.run o).det (readBlocks p.m g) = true then some o else none := by
  unfold chkT
  rw [OComp.det_bind]
  rcases (typ x).det g with _ | o
  · rfl
  · show (((p.J.run o).overOne p.m).bind fun b =>
      OComp.pure (if b then some o else none)).det g = _
    rw [OComp.det_bind, det_overOne p.m g _ (noCoin_of_detBound _ _ (p.J.bound o))]
    show (if (p.J.run o).det (readBlocks p.m g) then some o else none) = _
    rfl

/-- A PLAIN CONVERTER AS A TYPING: it asks the oracle nothing. -/
def pureTyp {Out : Type} (c : Files → Option Out) : Files → OComp (rom 256) (Option Out) :=
  fun d => OComp.pure (c d)

/-- It tosses no coin. -/
theorem pureTyp_noCoin {Out : Type} (c : Files → Option Out) (d : Files) :
    (pureTyp c d).NoCoin := trivial

/-- It asks no string. -/
theorem pureTyp_queries {Out : Type} (c : Files → Option Out) (d : Files) :
    (pureTyp c d).QueryBound 0 := trivial

/-- Its value, under every oracle, is the converter's. -/
theorem pureTyp_det {Out : Type} (c : Files → Option Out) (d : Files) (g : Fam (rom 256)) :
    (pureTyp c d).det g = c d := rfl

/-- PRE-PROCESS, THEN RUN THE TYPED VERIFIER: the value. -/
theorem chkT_pure_det (p : TypedOracleCompiler.Slice.Part 256 Files Run.PQ.SgX) (c : Files → Option p.Out)
    (x : Files) (g : Fam (rom 256)) :
    (chkT p (pureTyp c) x).det g = (c x).bind fun o =>
      if (p.J.run o).det (readBlocks p.m g) = true then some o else none :=
  chkT_det_eq p (pureTyp c) x g

namespace FileSpec
variable (φ : FileSpec) (S₀ : Finset (List Bool)) (S₁ : Tab → Finset (List Bool))

/-- The two tables that the oracle itself holds, merged, are the oracle's own values at the public
strings. -/
theorem merge_own (g : Fam (rom 256)) (x : List Bool) (hx : x ∈ S₀ ∪ S₁ (own₀ S₀ g)) :
    mergeT S₀ (own₀ S₀ g) (own₁ S₀ S₁ g) x = g () x := by
  unfold mergeT
  by_cases h0 : x ∈ S₀
  · rw [if_pos h0]
    unfold own₀ cutT
    rw [if_pos h0]
    rfl
  · rw [if_neg h0]
    have h1 : x ∈ S₁ (own₀ S₀ g) := (Finset.mem_union.1 hx).resolve_left h0
    unfold own₁ cutT
    rw [if_pos h1]
    rfl

/-- IN ONE WORLD THE PIN IS NOTHING: at the oracle's own tables the checker of the part as the
bound sees it has, under that oracle, the value of the part's own checker. -/
theorem chk_own (g : Fam (rom 256)) (x : Files) :
    ((φ.toO S₀ S₁ (own₀ S₀ g) (own₁ S₀ S₁ g)).chk x).det g =
      ((φ.part (own₀ S₀ g) (own₁ S₀ S₁ g)).chk x).det g :=
  det_pinOn_of_eq _ _ g (merge_own S₀ S₁ g) _

end FileSpec

end OnBytes.Slice.Shapes
