-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/Fit/AttKeeps.lean: the rounds of an attention sub-proof that the verifier's public
part plans keep every entry of the plan small.

"Verify.linkRounds X link moment" (OnBytes/Model/VerifySubproofs.lean) plans the rounds of a link's
sub-proof. Its arm for attention is "Attention.rounds a moment" at a member a of X.A.
OnBytes/Params/Fit/FitSubAtt.lean shows that these rounds keep a property of the entries under two
caps; OnBytes/Model/Fit/AttCaps.lean draws both caps from the yes of "Verify.publicOf";
OnBytes/Params/Fit/FitBase.lean pays the basic routines at the property "Small".

Main theorems.
 - **att_keeps**: Keeps s Small (Attention.rounds a moment), from publicOf's yes, SetCap s and
   X.A[g]? = some a.
 - link_att_keeps: the same of the whole arm of linkRounds, the case "no such plan" counted in.

Limits. Nothing on the other two arms of linkRounds. "Keeps" speaks only of a state of planning with
the setting s and no open root, and only where the routine returns; "Small" speaks of single entries
of a plan; what it is good for is said in OnBytes/Params/Fit/FitCalc.lean. The program does not
import this file.


-/
import OnBytes.Model.Fit.AttCaps
import OnBytes.Params.Fit.FitBase
import OnBytes.Params.Fit.FitSubAtt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Model.Fit

open OnBytes.Params (Keeps Small SetCap)

variable {pol KL : ByteArray} {lay : Option ByteArray} {X : Verify.Public}

/-- **An attention sub-proof's rounds keep the entries small.** -/
theorem att_keeps {s : Params.Setting} (hX : Verify.publicOf pol KL lay = .ok X) (S : SetCap s)
    (g : Nat) (a : Attention.Plan) (hg : X.A[g]? = some a) (moment : Nat) :
    Keeps s Small (Attention.rounds a moment) := by
  unfold Attention.rounds
  exact Params.keeps_attentionRounds (Params.subBase_small S) _ (att_zero_cap hX hg)
    (att_small_cap hX hg) moment

/-- The whole arm of linkRounds. -/
theorem link_att_keeps {s : Params.Setting} (hX : Verify.publicOf pol KL lay = .ok X)
    (S : SetCap s) (g moment : Nat) :
    Keeps s Small (match X.A[g]? with
      | some a => Attention.rounds a moment
      | none => Params.needs false) := by
  cases hg : X.A[g]? with
  | none => exact (Params.keeps_needs _ _).any
  | some a => exact att_keeps hX S g a hg moment

end OnBytes.Model.Fit

#print axioms OnBytes.Model.Fit.att_keeps
#print axioms OnBytes.Model.Fit.link_att_keeps
