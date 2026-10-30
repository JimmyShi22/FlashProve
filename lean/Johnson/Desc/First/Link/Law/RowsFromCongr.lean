-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/RowsFromCongr.lean: THE SECOND READING's SECOND TEXT (`rowsFrom`,
RowsFrom.lean beside this file) READS THE TABLE OF ARMS AT THE NUMBERS OF THE REQUEST's GROUPS
ALONE; AND OF WHAT THE PLANNER CONFIGURED THE FOUR FIELDS THAT DO NOT HANG ON THE DIGEST. Theorems
by unfolding and induction. A law file; no running text imports it.
  `nMomentsA_congr`   A l = A' l ⊢ nMomentsA A z l … = nMomentsA A' z l ….
  `nFrameA_congr`     A j = A' j at l ≤ j < l + gs.length ⊢ nFrameA A z l gs … = nFrameA A' z l gs
                    ….
  `callsFrom_congr`, `packFrom_congr`, `rowsFrom_congr`   A j = A' j at every j below the number
                      of the request's groups ⊢ rowsFrom c o n A = rowsFrom c o n A'.
  `rowsFrom_four`     two values of the planner with one sized, key, proof and entry have one
                    rowsFrom.

Limits. Tools. Nothing on whether rowsFrom returns. Nothing on soundness or on hiding.

-/
import Johnson.Desc.First.Link.Law.RowsFrom

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Params
open Johnson.G hiding sendsFrom
open VerifiableInference.Number (sendsFrom)

theorem nMomentsA_congr {A A' : Nat → Arm} (z : ProofSized) (l : Nat) (msgs : List ReqMessage)
    (h : A l = A' l) : ∀ fuel moment,
    nMomentsA A z l msgs fuel moment = nMomentsA A' z l msgs fuel moment
  | 0, _ => rfl
  | fuel + 1, moment => by
    unfold nMomentsA
    simp only [h, nMomentsA_congr z l msgs h fuel]

theorem nFrameA_congr {A A' : Nat → Arm} (z : ProofSized) :
    ∀ (gs : List ReqGroup) (l : Nat) (links : List ReqLink) (open_ : List Nat)
      (before : GroupSize), (∀ j, l ≤ j → j < l + gs.length → A j = A' j) →
    nFrameA A z l gs links open_ before = nFrameA A' z l gs links open_ before
  | [], _, _, _, _, _ => by
    unfold nFrameA
    rfl
  | g :: gs, l, links, open_, before, h => by
    have h0 : A l = A' l := h l (Nat.le_refl _) (by rw [List.length_cons]; omega)
    have ih := fun links' open' before' => nFrameA_congr z gs (l + 1) links' open' before'
      (fun j h1 h2 => h j (by omega) (by rw [List.length_cons]; omega))
    unfold nFrameA
    simp only [h0, nMomentsA_congr z l _ h0, ih]

theorem callsFrom_congr {A A' : Nat → Arm} (c : Configured) (o : List Nat) (n : Nat)
    (h : ∀ j, j < (reqGroups c.sized.proof.request).toList.length → A j = A' j) :
    callsFrom c o n A = callsFrom c o n A' := by
  unfold callsFrom
  simp only [nFrameA_congr c.sized.proof (reqGroups c.sized.proof.request).toList 0
    c.sized.proof.request.link o c.sized.proof.link.group
    (fun j _ h2 => h j (by omega))]

theorem packFrom_congr {A A' : Nat → Arm} (c : Configured) (o : List Nat) (n : Nat)
    (h : ∀ j, j < (reqGroups c.sized.proof.request).toList.length → A j = A' j) :
    packFrom c o n A = packFrom c o n A' := by
  unfold packFrom
  rw [callsFrom_congr c o n h]

/-- **The table of arms is read at the numbers of the request's groups alone.** -/
theorem rowsFrom_congr {A A' : Nat → Arm} (c : Configured) (o : List Nat) (n : Nat)
    (h : ∀ j, j < (reqGroups c.sized.proof.request).toList.length → A j = A' j) :
    rowsFrom c o n A = rowsFrom c o n A' := by
  unfold rowsFrom
  rw [packFrom_congr c o n h]

/-- **Of what the planner configured four fields are read.** -/
theorem rowsFrom_four {c c' : Configured} (e1 : c.sized = c'.sized) (e2 : c.key = c'.key)
    (e3 : c.proof = c'.proof) (e4 : c.entry = c'.entry) (o : List Nat) (n : Nat)
    (A : Nat → Arm) : rowsFrom c o n A = rowsFrom c' o n A := by
  have es : sendsFrom c = sendsFrom c' := by
    unfold VerifiableInference.Number.sendsFrom
    rw [e1, e2, e3, e4]
  unfold rowsFrom packFrom callsFrom
  rw [es, e1, e2, e3, e4]

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.rowsFrom_congr
#print axioms VerifiableInference.Desc.LinkJoin.rowsFrom_four
