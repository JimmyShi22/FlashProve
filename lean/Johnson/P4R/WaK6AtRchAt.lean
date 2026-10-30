-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P4R/WaK6AtRchAt.lean: P4.waK6_at_346 (P4R/WaK6At346.lean) AT THE FAMILY THAT THE
PIECES' ACCEPTANCES HAND ON: RchAt (Johnson/Top/H0/Walk/ReachAt.lean), at the proof
file's own IOP as written in Lean (FD Z A B c: P4R/K6AtRchAt.lean), in the goals' scope.

What is proved.
  reachB_of_rchAt   RchAt (FD Z A B c) k a IS "reached by the wrapped sub-protocols' steps", in the
                    letters of the walk: by unfolding alone.
  **waK6_rchAt**    at every a with RchAt (FD Z A B c) 346 a: WaK6 Bs.G₀.W Bs.G₀.W.P.h.V a.1.2.
  waK6_rchAt_at     the same in a law's own letter Wp, where
                    publicOf P.pol P.KL (some lay) = .ok Wp.

Existential quantifiers. None in the statements.
Not proved here. THAT ANY a HAS RchAt ... 346. That the plan's test passes (hOk). "No mark"
(a.1.2.failed = none) stands in the binders because the laws that would call this have it there: IT
IS IDLE: the proof does not read it. At the second, non-standard hash alone (secondHashFunction). Only in the
goals' scope, at the full size. Nothing on soundness.

-/
import Johnson.P4R.WaK6At346
import Johnson.P4R.K6AtRchAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P4

open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Kinds.Head.Law.AtTable (WaK6)
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach RchAt)
open ProofFile (Cl)
open Inst.Model (ScalesAndPolicy)

variable {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat} {Str : Type}

/-- The family, wrapped, in the letters of the walk. -/
theorem reachB_of_rchAt {k : ℕ} {a : (ProofFile.InstPub × S) × Str} (h : RchAt (FD Z A B c) k a) :
    Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) k (a.1.1, a.1.2) := h

/-- **WaK6 AT THE FAMILY THAT COUNTS.** -/
theorem waK6_rchAt (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true) :
    ∀ a : (ProofFile.InstPub × S) × Str, RchAt (FD Z A B c) 346 a → a.1.2.failed = none →
      WaK6 Bs.G₀.W Bs.G₀.W.P.h.V a.1.2 :=
  fun _ h _ => waK6_at_346 hS hR O hOk (reachB_of_rchAt h)

/-- The same in a law's own letter for the public numbers. -/
theorem waK6_rchAt_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {Wp : OnBytes.Model.Verify.Public}
    (hX : OnBytes.Model.Verify.publicOf P.pol P.KL (some lay) = .ok Wp) :
    ∀ a : (ProofFile.InstPub × S) × Str, RchAt (FD Z A B c) 346 a → a.1.2.failed = none →
      WaK6 Wp Wp.P.h.V a.1.2 := by
  obtain rfl := (wp_is O hX).2
  exact waK6_rchAt hS hR O hOk

end P4

#print axioms P4.reachB_of_rchAt
#print axioms P4.waK6_rchAt
#print axioms P4.waK6_rchAt_at
