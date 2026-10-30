-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Lane5SoundFourMet.lean

"ReadsModel" and the premise on the relation of "sound_four_of_ledger" (Lane5SoundFour.lean) can be
met together, at the library's own letters; a lawful table stays a premise.

Main definitions and theorems:
* "readsModelSelf scales": "ReadsModel" at I := "Cm.Idx", X := the model's requests, build :=
  "requestOfTokens", nextToken := "IntegerModel.nextToken" at the table and the index's tensors;
  both maps are the identity, both laws hold by definition.
* "sound_four_self": "sound_four_of_ledger" at these letters, at the relation
  "Policy.LedgerRel.Rno" itself, each witness taken as it is: its premise on the relation holds by
  definition. The conclusion is that of "sound_ledger_exact" (Lane5SoundLedger.lean).

It shows that "ReadsModel" and the premise on the relation are not empty, and no more: these are
the library's letters, not a protocol's. Not claimed: that some built request has a witness; that
any description of a protocol has "ReadsModel"; anything on the premises of
"sound_four_of_meanHoles". All that Lane5SoundFour.lean does not claim.

-/
import Johnson.Road.Lane5SoundFour

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open Inst.Model
open VerifiableInference

/-- **The library's own letters read the model.** -/
def readsModelSelf (scales : Cm.Scales) :
    ReadsModel (I := Cm.Idx) (X := Instance ppref) requestOfTokens
      (fun i l => IntegerModel.nextToken scales i.index l) scales :=
  ⟨id, id, fun _ _ _ h => h, fun _ _ => rfl⟩

/-- **"ReadsModel" and the premise on the relation are met together at these letters.** A lawful
table stays a premise. -/
theorem sound_four_self {scales : Cm.Scales} (lawful : scales.Lawful) :
    ∀ (i : Cm.Idx) (x' : List Token × List Token) (b : List Token) (x : Instance ppref),
      requestOfTokens x' b = some x →
        (∃ w, Policy.LedgerRel.Rno Cb.Gl.p (Policy.ppOf scales AcceptancePolicy.exact) i x w) →
          ∀ position (h : position < x'.2.length),
            IntegerModel.nextToken scales i.index (x'.1 ++ x'.2.take position) =
              some x'.2[position] :=
  sound_four_of_ledger (Rn := fun i x w =>
      Policy.LedgerRel.Rno Cb.Gl.p (Policy.ppOf scales AcceptancePolicy.exact) i x w)
    lawful (readsModelSelf scales) id (fun _ _ _ _ _ _ h => h)

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.readsModelSelf
#print axioms OnBytes.Road.L5.sound_four_self
