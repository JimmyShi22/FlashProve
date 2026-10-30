-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Total/PubOnly.lean: TWO PARTS OF THE LAW "behind K4's hearing its two runs of claims
return" (Johnson/Road/K4/Total/Returns.lean): FrontPub and RunPub, to the letter: of the public
record the listing "front" and the run of that name read the layout and the record of reads alone:
at two public records that share these two fields they are the same function. Statements and proofs.

Why it is wanted: K4's block hears at its public record with the state's tokens laid in, and runs at
the record as it is (Johnson/Desc/First/K4/Block.lean); a member of the law may stand at a third.

WHAT OF P EACH TEXT READS (OnBytes/Desc/First/K4/Claims.lean, Plain.lean): normsForms: P.y and
P.rd.lNI. gatedForms: P.y. front: these two listings, and P.y in rowBatchForm; the other five
listings take no P. formsFrontWith: P.y.NI, P.y in rowsSummand, and front.

  `normsForms_pub`, `gatedForms_pub`: the two listings that take P.
  `front_pub : FrontPub`, `run_pub : RunPub`: the parts.
  `formsFrontWith_tokv`: the case of other tokens laid in.
No new argument: each text unfolded, the two fields rewritten.
**Limits.** EQUATIONS OF FUNCTIONS under two premises, as the sentences have them: Pr.y = P.y and
Pr.rd = P.rd; both hold by rfl where the records differ in the tokens alone. Neither the listing nor
the run is said to return anywhere. Nothing on what a form is worth, nothing on soundness. K04_law,
the law of K4's block itself, IS NOT PROVED. Met through Lean at no member; by a run at one honest
proof of each of two sizes both runs of claims return at all 2 and 12 layers' places: that run is
the member of the law that these serve.


-/
import Johnson.Road.K4.Total.Returns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Total

open OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Model.Layer (Pub Own Heard Env)

theorem normsForms_pub {P Pr : Pub} (hy : Pr.y = P.y) (hrd : Pr.rd = P.rd) (v : Env) (H : Heard) :
    normsForms Pr v H = normsForms P v H := by
  unfold normsForms
  rw [hy, hrd]

theorem gatedForms_pub {P Pr : Pub} (hy : Pr.y = P.y) (v : Env) (hd : Level)
    (hd2 : Option Level) : gatedForms Pr v hd hd2 = gatedForms P v hd hd2 := by
  unfold gatedForms
  rw [hy]

/-- **The part FrontPub.** -/
theorem front_pub : FrontPub := by
  intro rows P Pr g o a b hy hrd
  unfold front
  rw [normsForms_pub hy hrd, gatedForms_pub hy, hy]

/-- **The part RunPub.** -/
theorem run_pub : RunPub := by
  intro rows P Pr g o F hy hrd
  have hf : ∀ a b, front rows Pr g o a b = front rows P g o a b :=
    fun a b => front_pub rows P Pr g o a b hy hrd
  unfold formsFrontWith
  rw [hy]
  simp only [hf]

/-- The run "front" is the same at a public record with other tokens laid in. -/
theorem formsFrontWith_tokv (rows : Bool) (P : Pub) (x : Array Nat) (g : ℕ) (o : Own) (F : Fork) :
    formsFrontWith rows { P with tokv := x } g o F = formsFrontWith rows P g o F :=
  run_pub rows P { P with tokv := x } g o F rfl rfl

end OnBytes.Desc.First.K4.Total

#print axioms OnBytes.Desc.First.K4.Total.normsForms_pub
#print axioms OnBytes.Desc.First.K4.Total.gatedForms_pub
#print axioms OnBytes.Desc.First.K4.Total.front_pub
#print axioms OnBytes.Desc.First.K4.Total.run_pub
#print axioms OnBytes.Desc.First.K4.Total.formsFrontWith_tokv
