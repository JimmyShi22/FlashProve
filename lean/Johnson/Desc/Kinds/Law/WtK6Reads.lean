-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/WtK6Reads.lean: WHAT THE ITEM "weights" SAYS (Law/WtK6.lean: wtK6) READS THE
WITNESS THROUGH WHAT THE TABLE BOOKS FOR THE ITEM forms m j "weights" ALONE: the messages and pads
of segment m's group's tenants, and the cells. At two witnesses that are one on these components the
sentence is one. Other files' reading law of the forms wants it.

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable).
  compCut_reads: the components that K6's rule reads off the witness are one at two witnesses that
      are one on segment 24's group's tenants and have the same cells.
  wtK6_reads: THE STATEMENT. NO FENCE: at every m, every state, every list of segments' sorts.

How. wtK6 speaks at m = 24 alone, of w.cells and of compCut at w. compCut is made of the segment's
own integers (ownCut: off Sound.readAt at 24), the weights (whOf of the cells) and the mask row
(maskQ: off Sound.readAt at 24). By oneOn_of_reads and readAt_same
(Law/ReadsOkK6.lean).
What it does not say. That the sentence holds anywhere. Nothing on the item formsT. Nothing on
soundness.
-/
import Johnson.Desc.Kinds.Law.WtK6
import Johnson.Desc.Kinds.Law.ReadsOkK6

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable

open OnBytes
open OnBytes.Params (ReqLayout)
open VerifiableInference.OnPublicFiles.Flat (GE InRange)
open VerifiableInference.Desc.First (S Numbers ModelPart Item Comp)
open VerifiableInference.Desc.Sound (Mem MsgT sameQ)

variable {rows cols : Nat} {P Tok : Type} (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ) (msR : List Mem)
  (N : Numbers)

/-- **The components are one.** -/
theorem compCut_reads (s : Nat → Cb.Pv.Tail.Size)
    (seat : ∀ k, Fin (s k).NM → Nat → Nat → Nat × Nat × Nat) (Wp : OnBytes.Model.Verify.Public)
    (pl : Nat → Nat × Bool × Nat × Nat) (w w' : Wit (Fin rows → Fin cols → GE) Tok MsgT)
    (ho : Came.OneOn arr (N.group 24) w w') (hc : w.cells = w'.cells) :
    compCut cs arr msR N s seat Wp pl w = compCut cs arr msR N s seat Wp pl w' := by
  have er := Came.readAt_same cs arr msR N 24 w w' ho
  unfold compCut compOf ownCut maskQ
  rw [P5J.ownQ_at, P5J.ownQ_at, er, hc]

/-- **THE STATEMENT.** -/
theorem wtK6_reads (Wp : OnBytes.Model.Verify.Public) (lay6 : ReqLayout) (num : ℕ → ℕ → ℕ)
    (n rb : ℕ) (links : List ModelPart) (m j : ℕ) (a : P × S) (y : Strs)
    (w w' : Wit (Fin rows → Fin cols → GE) Tok MsgT)
    (h : ∀ c ∈ (Item.forms m j "weights").reads arr N links, sameQ c w w')
    (hw : wtK6 cs arr msR N Wp lay6 num n rb m a y w) :
    wtK6 cs arr msR N Wp lay6 num n rb m a y w' := by
  intro hm hR
  subst hm
  have ho : Came.OneOn arr (N.group 24) w w' :=
    Came.oneOn_of_reads arr N links (Item.forms 24 j "weights") w w' h
  have hc : w.cells = w'.cells :=
    h Comp.cells (by
      unfold Item.reads
      exact List.mem_append_right _ (List.mem_singleton.2 rfl))
  rw [← compCut_reads cs arr msR N _ _ Wp _ w w' ho hc]
  exact hw rfl (hc ▸ hR)

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.compCut_reads
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.wtK6_reads
