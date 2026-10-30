-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Lane5LedgerLinks.lean

The first 24 links are the same for both heads.

"A link is in order" reads the family of segments at its own segment alone. The family with the cost
ledger's head ("Policy.segPol s pol") is the library's own family ("Cm.Seg.TS.segM s") but for the
last segment. So a link other than the head's that is shown in order for the one family is in order
for the other: the layers' and attention's links are shown once.

Main theorems:
* "linkOK_seg": two families with the same segment k have the same "in order" at k.
* "linkOK_pol": for k other than 24, from the library's family to the ledger's ("Policy.segPol_ne").

Not claimed: all that Lane5.lean does not claim. The shape h of the head is a letter in both: a link
must be shown at the shape at which it is used.
-/
import Policy.Seg.All
import Johnson.Road.Lane5

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open Inst.Model

variable {h : Cm.Seg.Hd} {Wz : Mat} {x : Instance ppref} {k : ℕ} {A : Mx}

/-- **Two families with the same segment k have the same "in order" at k.** -/
theorem linkOK_seg {seg seg' : Segs} (e : seg k = seg' k) (H : LinkOK h seg Wz x k A) :
    LinkOK h seg' Wz x k A :=
  ⟨H.small, by rw [← e]; exact H.idn, by rw [← e]; exact H.key⟩

/-- **A link other than the head's is in order for the ledger's family if it is for the library's.**
-/
theorem linkOK_pol {s : Cm.Scales} (pol : AcceptancePolicy) (hk : k ≠ 24)
    (H : LinkOK h (Cm.Seg.TS.segM s) Wz x k A) : LinkOK h (Policy.segPol s pol) Wz x k A :=
  linkOK_seg (Policy.segPol_ne s pol hk).symm H

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.linkOK_seg
#print axioms OnBytes.Road.L5.linkOK_pol
