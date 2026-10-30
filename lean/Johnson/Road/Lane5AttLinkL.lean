-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Lane5AttLinkL.lean

The end of Johnson/Road/Lane5AttLink.lean for the family of segments whose head carries the cost
ledger ("Policy.segPol s pol", Policy/Seg/All.lean): its segment 2 g + 1 is the library's
("Policy.segPol_ne"). Hypotheses and what is not claimed: as there.
-/
import Johnson.Road.Lane5AttLink
import Policy.Seg.All

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open Inst.Model (ppref Instance Mat AcceptancePolicy tbRef)

/-- **With the ledger: link 2 g + 1 is in order.** -/
theorem linkA_of_ordL {S : Attention.Shape} {g : ℕ} (hg : g < 12) (hS : AttSized S)
    {s : Cm.Scales} (hsh : (s.kap (4 * g)).sh = S.cf.sh.getD 0 0)
    (hE : ∀ ι : ℕ, ι < S.u0 → ((S.Tt.getD ι 0 : ℕ) : ℤ) = tbRef.Exp ι) {Z : Zs}
    (O : AttOrd S Z) (pol : AcceptancePolicy) (Wz : Mat) (x : Instance ppref) :
    LinkOK Cm.Seg.Hd.main (Policy.segPol s pol) Wz x (2 * g + 1) (attMx S g Z) :=
  linkA_gen hg hS hsh hE O _ _ (Policy.segPol_ne s pol (by omega)) Wz x

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.linkA_of_ordL
