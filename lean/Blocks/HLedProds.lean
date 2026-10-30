-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/HLedProds.lean: a list of product claims put on record at once, and the honest prover's copy.

Record and copy: Blocks/HLed.lean. A chain of products x_k = x_(k-1) · e_k is recorded as one claim
REL(f; a · b) for each step (`Ledger.addProd`, Blocks/ProductBlock.lean). Here: the same for a list
of triples (f, a, b), in order.
 * `Ledger.addProds`; `true_addProds`: if `wf` holds, the longer record says what the record says
   and that every product holds.
 * `HLed.addProds`, on the list of the pairs of values; `Good.addProds`.
-/
import Blocks.HLed

set_option autoImplicit false

namespace Blocks

namespace Ledger

variable {N E : Type}

/-- The record with the claims REL(p.1; p.2.1 · p.2.2), p in the list, each with its two opened
forms. -/
def addProds [One E] (x : Ledger N E) : List (Form N E × Form N E × Form N E) → Ledger N E
  | [] => x
  | p :: ps => (x.addProd p.1 p.2.1 p.2.2).addProds ps

theorem wf_addProds [One E] :
    ∀ (ps : List (Form N E × Form N E × Form N E)) {x : Ledger N E},
      x.wf = true → (x.addProds ps).wf = true
  | [], _, h => h
  | p :: ps, _, h => wf_addProds ps (wf_addProd h p.1 p.2.1 p.2.2)

theorem true_addProds [Fintype N] [CommRing E] (y : N → E) :
    ∀ (ps : List (Form N E × Form N E × Form N E)) {x : Ledger N E}, x.wf = true →
      ((x.addProds ps).True y ↔
        x.True y ∧ ∀ p ∈ ps, Form.val y p.1 = Form.val y p.2.1 * Form.val y p.2.2)
  | [], _, _ => ⟨fun h => ⟨h, fun _ hp => absurd hp List.not_mem_nil⟩, fun h => h.1⟩
  | p :: ps, x, h => by
      show ((x.addProd p.1 p.2.1 p.2.2).addProds ps).True y ↔ _
      rw [true_addProds y ps (wf_addProd h p.1 p.2.1 p.2.2), true_addProd h,
        List.forall_mem_cons, and_assoc]

end Ledger

namespace HLed

variable {N E : Type}

/-- The copy with the values of the opened forms of a list of product claims. -/
def addProds [One E] (h : HLed E) : List (E × E) → HLed E
  | [] => h
  | v :: vs => (h.addProd v.1 v.2).addProds vs

theorem len_addProds [One E] :
    ∀ (vs : List (E × E)) (h : HLed E),
      (h.addProds vs).len = (h.len.1, h.len.2.1 + 2 * vs.length, h.len.2.2 + vs.length)
  | [], _ => rfl
  | v :: vs, h => by
      show ((h.addProd v.1 v.2).addProds vs).len = _
      rw [len_addProds vs, len_addProd, List.length_cons]
      refine Prod.ext rfl (Prod.ext ?_ ?_)
      · show h.len.2.1 + 2 + 2 * vs.length = h.len.2.1 + 2 * (vs.length + 1)
        omega
      · show h.len.2.2 + 1 + vs.length = h.len.2.2 + (vs.length + 1)
        omega

variable [Fintype N] [CommRing E]

theorem Good.addProds {y : N → E} :
    ∀ (ps : List (Form N E × Form N E × Form N E)) {h : HLed E} {led : Ledger N E}, h.Good led y →
      (∀ p ∈ ps, Form.val y p.1 = Form.val y p.2.1 * Form.val y p.2.2) →
      (h.addProds (ps.map fun p => (Form.val y p.2.1, Form.val y p.2.2))).Good (led.addProds ps) y
  | [], _, _, H, _ => H
  | p :: ps, _, _, H, hp =>
    Good.addProds ps (H.addProd (hp p List.mem_cons_self)) fun q hq =>
      hp q (List.mem_cons_of_mem _ hq)

end HLed

end Blocks
