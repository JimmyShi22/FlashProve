-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/Serves.lean

A definition of where an honest prover has a trace of the model's run on a request, and where none.

The steps of an honest prover read the cells of the model's run on a request. There is not always
such a run to prove: a range condition of the integer program can fail, the request can lack its
form, the policy's clauses can fail. This file names the set of pairs (weights, request) at which
none of the three happens, "Serves", and makes of any function to cells a function to "Option" that
has a value exactly there, "traceOf". Sizes, scales, tables and policy are letters, and so is what a
cell is.

Main definitions and theorems:
* "Serves": no range condition fails ("RunsK"), the request has its form ("Head3"), and the policy's
  three clauses hold of the program's logits ("PolOK"). All three are predicates of Inst/Model/.
* "decServes": "Serves" is decided by evaluating its clauses.
* "traceOf": the cells where "Serves" holds, "none" elsewhere.
* "traceOf_isSome_iff", "traceOf_eq_none_iff", "traceOf_eq_some_iff": where "traceOf" has a value,
  and which.
* "serves_iff_rinfR": at the weights of an index "Serves" is the relation "RinfR" of
  Inst/Model/ProgramR.lean. It holds by definition.
* "not_serves_of_le": a request without a covered position (e ≤ r) is not served.

Limits. The definitions are general in the sizes. That "Serves" is exactly where cells exist that
meet a relation of the library is shown at the reference sizes alone, at the lookup tables "tbRef"
and the weights that an index holds (so well formed), for one relation modulo a prime p ≥ 2^61 - 1,
at a lawful table of scales and a policy within its bounds (Johnson/HonestTrace/ServesAtRef.lean:
"serves_tfae"). That "Serves" holds somewhere is shown there too, not here. "Serves" asks nothing of
the weights' form, of the scales, of the lookup tables or of the policy's numbers. So at weights
that are not well formed, at other lookup tables, at a table of scales that is not lawful or at a
policy outside its bounds "traceOf" can have a value of which the theorems of this file and of
Johnson/HonestTrace/ServesAtRef.lean say only which it is ("traceOf_eq_some_iff",
"traceRef_eq_some_iff") and, at an index's weights, that "ModelR" holds ("modelR_of_serves"): none
says that it meets a relation of the library; to reject such inputs is left to whoever calls it. At
scales without sense (a divisor 0) "Serves" is still a proposition, over Lean's x / 0 = 0, and says
nothing of a model. A request is an "Instance P" here: its tokens are below V and r, e are at most T
by type. To turn a request on bytes into one, which can fail too, is not done in this file. The
instances evaluate sums over all positions, layers and tokens with nothing kept between calls, and
this file evaluates them at no size.

Not claimed: that a verifier accepts a proof made of a trace; that the released provers serve every
pair in "Serves" (by their documentation they stop earlier at some range conditions); that "cells"
are an honest prover's cells: it is a letter here.

-/
import Inst.Model.ProgramRPol

set_option autoImplicit false

namespace OnBytes.HonestTrace

open Inst.Model

/-! ## Decidability -/

section Dec

local instance (a : ℤ) : Decidable (Fits16 a) := by unfold Fits16; infer_instance
local instance (np : NormPar) (d : ℕ) (x : Vec) : Decidable (NORM.OK np d x) := by
  unfold NORM.OK; infer_instance
local instance (d : ℕ) (z wg wu : Vec) (k k' : ℕ) : Decidable (UNIT.OK d z wg wu k k') := by
  unfold UNIT.OK; infer_instance
local instance (P : Params) (tb : Tables) (w : LayerW) (L : ℕ) (x : ℕ → Vec) :
    Decidable (Att.OK P tb w L x) := by unfold Att.OK; infer_instance
local instance (P : Params) (tb : Tables) (w : LayerW) (L : ℕ) (x : ℕ → Vec) :
    Decidable (FF.OK P tb w L x) := by unfold FF.OK; infer_instance

/-- Whether the integer program runs (no range condition fails) is decided by evaluating the
conditions: bounded quantifiers over comparisons of integers. -/
instance decRunsK (P : Params) (κ : ℕ → LayerScale) (nf : NormPar) (tbs : ℕ → Tables)
    (w : Weights) (p : Fin P.T → Fin P.V) : Decidable (RunsK P κ nf tbs w p) := by
  unfold RunsK; infer_instance

/-- The policy's three clauses are decided by evaluating them: a sum, a count, and one equation
under two tests. -/
instance decPolOK {P : Params} (lg : ℕ → ℕ → ℤ) (pol : AcceptancePolicy) (x : Instance P) :
    Decidable (PolOK lg pol x) :=
  decidable_of_iff
    ((∑ t ∈ x.cnt, min (costOf lg x t) pol.C ≤ pol.theta * x.NB) ∧
      ((x.cnt.filter fun t => (pol.C : ℤ) < costOf lg x t).card ≤ pol.cap) ∧
      (x.r < x.e → x.e = P.T → gapOf P.V (lg (P.T - 1)) x.y.val = 0))
    ⟨fun h => ⟨h.1, h.2.1, h.2.2⟩, fun h => ⟨h.a, h.b, h.c⟩⟩

end Dec

/-! ## Serves, and the trace as an option -/

section Any
variable (P : Params) (κ : ℕ → LayerScale) (nf : NormPar) (tbs : ℕ → Tables) (pol : AcceptancePolicy)

/-- **The weights w serve the request x**, at sizes P, scales κ and nf, tables tbs and the policy
pol. Three clauses:
* no range condition of the integer program fails on the request's T tokens, at any position,
  covered or not, in any layer or in the final normalisation ("RunsK", Inst/Model/Program.lean);
* the request has its form: r < e ≤ T, and y = 0 if e < T ("Head3", Inst/Model/ProgramR.lean);
* the policy's clauses (a), (b), (c) hold of the program's logits ("PolOK", the same file).

It is defined at any sizes, and asks nothing of the weights' form, the scales, the lookup tables or
the policy's numbers (the head of this file, "Limits"). -/
def Serves (w : Weights) (x : Instance P) : Prop :=
  RunsK P κ nf tbs w x.prompt ∧ Head3 x ∧ PolOK (lgK P κ nf tbs w x.prompt) pol x

/-- "Serves" is decided by evaluating its three clauses. -/
instance decServes (w : Weights) (x : Instance P) : Decidable (Serves P κ nf tbs pol w x) := by
  unfold Serves; infer_instance

/-- **The trace, where there is one.** W₀ is what all requests share, "weights" reads the model's
weights from it, and "cells" is any function to any type Tr. The value is "cells w₀ x" where the
weights serve the request, and "none" elsewhere. The weights, the scales, the lookup tables and the
policy are asked nothing: at weights that are not well formed, at other lookup tables than "tbRef",
at a table of scales that is not lawful or at a policy outside its bounds there can be a value, of
which the theorems of this file and of Johnson/HonestTrace/ServesAtRef.lean say only which it is
("traceOf_eq_some_iff", "traceRef_eq_some_iff") and, at an index's weights, that "ModelR" holds
("modelR_of_serves"): none says that it meets a relation of the library. The request is an "Instance
P" already. -/
def traceOf {W₀ Tr : Type} (weights : W₀ → Weights) (cells : W₀ → Instance P → Tr) (w₀ : W₀)
    (x : Instance P) : Option Tr :=
  if Serves P κ nf tbs pol (weights w₀) x then some (cells w₀ x) else none

variable {P κ nf tbs pol}

/-- "traceOf" has a value exactly where the weights serve the request. -/
theorem traceOf_isSome_iff {W₀ Tr : Type} (weights : W₀ → Weights)
    (cells : W₀ → Instance P → Tr) (w₀ : W₀) (x : Instance P) :
    (traceOf P κ nf tbs pol weights cells w₀ x).isSome = true ↔
      Serves P κ nf tbs pol (weights w₀) x := by
  unfold traceOf
  by_cases h : Serves P κ nf tbs pol (weights w₀) x
  · rw [if_pos h]
    exact ⟨fun _ => h, fun _ => rfl⟩
  · rw [if_neg h]
    exact ⟨fun e => absurd e (by simp), fun e => absurd e h⟩

/-- "traceOf" is "none" exactly where the weights do not serve the request. -/
theorem traceOf_eq_none_iff {W₀ Tr : Type} (weights : W₀ → Weights)
    (cells : W₀ → Instance P → Tr) (w₀ : W₀) (x : Instance P) :
    traceOf P κ nf tbs pol weights cells w₀ x = none ↔
      ¬ Serves P κ nf tbs pol (weights w₀) x := by
  unfold traceOf
  by_cases h : Serves P κ nf tbs pol (weights w₀) x
  · rw [if_pos h]
    exact ⟨fun e => absurd e (by simp), fun e => absurd h e⟩
  · rw [if_neg h]
    exact ⟨fun _ => h, fun _ => rfl⟩

/-- "traceOf" has the value t exactly if the weights serve the request and t is "cells w₀ x". -/
theorem traceOf_eq_some_iff {W₀ Tr : Type} (weights : W₀ → Weights)
    (cells : W₀ → Instance P → Tr) (w₀ : W₀) (x : Instance P) (t : Tr) :
    traceOf P κ nf tbs pol weights cells w₀ x = some t ↔
      Serves P κ nf tbs pol (weights w₀) x ∧ cells w₀ x = t := by
  unfold traceOf
  by_cases h : Serves P κ nf tbs pol (weights w₀) x
  · rw [if_pos h]
    exact ⟨fun e => ⟨h, Option.some.inj e⟩, fun e => by rw [e.2]⟩
  · rw [if_neg h]
    exact ⟨fun e => absurd e (by simp), fun e => absurd e.1 h⟩

/-- At the weights of an index, "Serves" is the library's relation of a request under a policy,
"RinfR" (Inst/Model/ProgramR.lean). It holds by definition. -/
theorem serves_iff_rinfR (i : Index P) (x : Instance P) :
    Serves P κ nf tbs pol i.val x ↔ RinfR P κ nf tbs pol i x :=
  Iff.rfl

/-- No weights serve a request without a covered position (e ≤ r), at any sizes, scales, tables and
policy: it lacks its form. -/
theorem not_serves_of_le (w : Weights) {x : Instance P} (h : x.e ≤ x.r) :
    ¬ Serves P κ nf tbs pol w x :=
  fun hs => absurd hs.2.1.1 (not_lt.2 h)

end Any

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.decRunsK
#print axioms OnBytes.HonestTrace.decPolOK
#print axioms OnBytes.HonestTrace.Serves
#print axioms OnBytes.HonestTrace.decServes
#print axioms OnBytes.HonestTrace.traceOf
#print axioms OnBytes.HonestTrace.traceOf_isSome_iff
#print axioms OnBytes.HonestTrace.traceOf_eq_none_iff
#print axioms OnBytes.HonestTrace.traceOf_eq_some_iff
#print axioms OnBytes.HonestTrace.serves_iff_rinfR
#print axioms OnBytes.HonestTrace.not_serves_of_le
