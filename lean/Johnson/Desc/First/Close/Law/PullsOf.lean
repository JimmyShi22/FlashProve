-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/PullsOf.lean: THE PREMISE `Pulls` OF OrderedOf.lean, PAID FROM TWO
CONDITIONS ON THE GROUP's DATA. A definition, statements and proofs.

`orderedV_of` (OrderedOf.lean, beside this file) asks a function pull with: pull V, arranged, is V
off the free rows, for every vector V on the fold's input code that is 0 at the kept slots off the
corner 0 .. 0. `RowsK.fm_onto` (Johnson/Top/H/GroupRowsOnto.lean) says that such a
vector is there, if every kept slot's row names that slot and every member's change of shape carries
forms onto.
  `pullOf R`: one such vector, by choice, where there is one; 0 else.
  `pulls_of`: `Pulls R (pullOf R)` under these two conditions.
  `pulls_keep`: at whole members kept (`Rows.keep`) the first condition holds by make
    (`Rows.keep_names`, same file): "every member's change of shape carries
    forms onto" is left as the one premise.
Limits. A choice: nothing says which vector. The premise that is left is shown of no data here
(Johnson/Top/H/MemberOnto.lean speaks of the members of the programs' shapes; it is not
called here). Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.First.Close.Law.OrderedOf
import Johnson.Top.H.GroupRowsOnto

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Slice Iop IOR KObj Cb Cb.Pv Johnson.Top.H
open Johnson.Top.H.ArrAdd (FreeAt)

variable {S : Sig GE} (R : RowsK S)

open Classical in
/-- A vector on the group's own entries that, arranged, is V off the free rows, if there is one. -/
noncomputable def pullOf (V : R.Sh.Cin.J → GE) : R.G.C.J → GE :=
  if h : ∃ a : R.G.C.J → GE, ∀ j, ¬ FreeAt R.Sh j → R.Sh.rho.fm a j = V j then h.choose else 0

theorem pulls_of (hS : ∀ q, R.slot (R.kept q) = some q)
    (hV : ∀ a, Function.Surjective (R.view a).fm) : Pulls R (pullOf R) := fun V hK j hj => by
  have h := R.fm_onto hS hV V hK
  unfold pullOf
  rw [dif_pos h]
  exact h.choose_spec j hj

theorem pulls_keep (R₀ : Rows S) (kp : {a // R₀.mem a} → Prop) [DecidablePred kp]
    (hV : ∀ a, Function.Surjective ((R₀.keep kp).view a).fm) :
    Pulls (R₀.keep kp) (pullOf (R₀.keep kp)) :=
  pulls_of (R₀.keep kp) (Rows.keep_names R₀ kp) hV

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.pulls_of
#print axioms VerifiableInference.Desc.First.Close.pulls_keep
