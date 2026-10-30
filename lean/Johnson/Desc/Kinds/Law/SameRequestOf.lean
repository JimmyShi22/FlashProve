-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/SameRequestOf.lean: THE SEAM BETWEEN THE OUTPUT HEAD's PUBLIC LETTERS AND THE LIBRARY's TYPED REQUEST: WHO PAYS
the premise SameRequest (Law/ProgramBridge.lean). Statements and proofs; no chance in it.
SameRequest P x has eight fields. FOUR ARE ON THE PLAN's NUMBERS: T, V, d are the library's; the least cost's exponent
sh is 8 (the kind's tests on the plan allow 7 too; the library's cost has 2^8): HeadScope P: A NAMED PREMISE ON PUBLIC
NUMBERS: its payer is the scope's reader (Law/HeadScopeAt.lean: at the public record of a parameter file in scope).
NO TEST OF A PROGRAM IS NARROWED. FOUR TIE THE REQUEST: token i, r, e, y. These need no premise:
  instOf       THE INSTANCE THAT THE LETTERS STATE: under the kind's own test on the request (Request.ok: r < e <= T;
               every token below V) and the next token's block's test (y < V), the letters ARE a typed request.
  sameRequest_instOf   SameRequest holds of it.
  sameRequest_unique   and of no other: the letters state one instance.
So "there is exactly one typed request that the head's letters state". WHAT IT DOES NOT SAY. That this instance is the one
that the user meant: how the user's files become the record's request words and the asked token is the matter of
the reading of these files (the row on the map from typed requests to the verifier's instances): not ours.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.ProgramBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open Norm (lt ls d lPd T S2)
open Inst.Model (Params Instance)

/-- **The scope's four numbers**: the plan's sizes are the library's, and the least cost is 2^8. -/
structure HeadScope [Sizes] (P : Params) : Prop where
  hT : T = P.T
  hV : V = P.V
  hd : d = P.d
  hsh : sh = 8

namespace Came

variable [Sizes] [Policy] [Request] [Token] {P : Params}

theorem req_spec (h : Request.ok = true) : r < e ∧ e ≤ T ∧ ∀ t, t < T → tok t < V := by
  unfold Request.ok at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- **The instance that the letters state.** -/
def instOf (Sc : HeadScope P) (hreq : Request.ok = true) (hy : y < V) : Instance P where
  prompt i := ⟨tok i.val, by
    rw [← Sc.hV]
    exact (req_spec hreq).2.2 i.val (by rw [Sc.hT]; exact i.isLt)⟩
  y := ⟨y, by rw [← Sc.hV]; exact hy⟩
  rF := ⟨r, by
    have h := req_spec hreq
    rw [← Sc.hT]
    omega⟩
  eF := ⟨e, by
    have h := req_spec hreq
    rw [← Sc.hT]
    omega⟩

theorem sameRequest_instOf (Sc : HeadScope P) (hreq : Request.ok = true) (hy : y < V) :
    SameRequest P (instOf Sc hreq hy) :=
  ⟨Sc.hT, Sc.hV, Sc.hd, Sc.hsh, fun _ _ => rfl, rfl, rfl, rfl⟩

theorem sameRequest_unique {x x' : Instance P} (R : SameRequest P x) (R' : SameRequest P x') :
    x = x' := by
  obtain ⟨p, yy, rF, eF⟩ := x
  obtain ⟨p', yy', rF', eF'⟩ := x'
  have h1 : p = p' := by
    funext i
    apply Fin.ext
    have a := R.htok i.val i.isLt
    have b := R'.htok i.val i.isLt
    exact a.symm.trans b
  have h2 : yy = yy' := Fin.ext (R.hy.symm.trans R'.hy)
  have h3 : rF = rF' := Fin.ext (R.hr.symm.trans R'.hr)
  have h4 : eF = eF' := Fin.ext (R.he.symm.trans R'.he)
  rw [h1, h2, h3, h4]

/-- SameRequest gives the scope's four numbers back. -/
theorem scope_of_same {x : Instance P} (R : SameRequest P x) : HeadScope P :=
  ⟨R.hT, R.hV, R.hd, R.hsh⟩

end Came

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.sameRequest_instOf
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.sameRequest_unique
