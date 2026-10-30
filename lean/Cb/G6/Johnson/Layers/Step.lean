-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/G6/Johnson/Layers/Step.lean: how one round is put before a doomed tail.

Statements with their proofs, and one definition. No protocol occurs here.

Main names:
  `Doomed.cons_of_bad`: the first step of the library's `doomed_of_clean` (Iop/Rbr.lean), with a
    doomed tail in the place of further bad sets. For every message there is a set of draws that is
    fixed before the draw, with at most e members; outside it the tail is doomed. Then the round
    with the tail is doomed, and the round's number is e. So a tail that comes from another theorem
    can be used.
  `Doomed.cons_pow`: a batch by powers as such a round. The draw is read in E by an injective map
    (all of E, or E without 0); the batched vector may depend on the round's own message; the caller
    owes the tail where the draw is outside `badPow`. The number is n - 1.
  `Doomed.cons_pt`, `Doomed.cons_ptFam`: a point under the equality kernel as such a round, for one
    vector and for a family with one bad set. The number is g |E|^(g-1).
  `Carry.refl`, `Carry.tr_refl`, `Carry.inj_refl`: the carrying that changes nothing. So the type
    `Carry s s` is inhabited.

Limits: nothing is assumed; nothing is said on a protocol.

-/
import Cb.G6.Johnson.Layers.Carry
import Cb.G6.Johnson.Layers.Rounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.L5.Layers
open Iop Prob

/-- One round before a doomed tail, from a bound on the bad draws of each message. -/
theorem Doomed.cons_of_bad {r : Round} {s : Shape} (e : ℕ) (ε : Err s) (bad : Tr (r :: s) → Prop)
    (B : r.Msg → Set r.Chal) (hB : ∀ m, cnt (fun c => c ∈ B m) ≤ e)
    (h : ∀ m c, c ∉ B m → Doomed s ε (fun τ => bad (m, c, τ))) :
    Doomed (r :: s) (e, ε) bad := fun m =>
  le_trans (cnt_mono fun c hc => by
    by_contra hcB
    exact hc (h m c hcB)) (hB m)

section
variable {E : Type} [Field E] [Fintype E]

/-- A batch by powers as one round before a doomed tail. -/
theorem Doomed.cons_pow {r : Round} {s : Shape} (ε : Err s) (bad : Tr (r :: s) → Prop) {n : ℕ}
    (v : r.Chal → E) (hv : Function.Injective v) (a : r.Msg → Fin n → E)
    (h : ∀ m c, v c ∉ badPow (a m) → Doomed s ε (fun τ => bad (m, c, τ))) :
    Doomed (r :: s) (n - 1, ε) bad :=
  Doomed.cons_of_bad (n - 1) ε bad (fun m => {c | v c ∈ badPow (a m)})
    (fun m => le_trans (cnt_le_of_inj v hv fun _ hc => hc) (cnt_badPow (a m))) h

/-- A point under the equality kernel as one round before a doomed tail. -/
theorem Doomed.cons_pt {r : Round} {s : Shape} (ε : Err s) (bad : Tr (r :: s) → Prop) {g : ℕ}
    (v : r.Chal → Fin g → E) (hv : Function.Injective v) (d : r.Msg → ℕ → E)
    (h : ∀ m c, v c ∉ badPt g (d m) → Doomed s ε (fun τ => bad (m, c, τ))) :
    Doomed (r :: s) (g * Fintype.card E ^ (g - 1), ε) bad :=
  Doomed.cons_of_bad _ ε bad (fun m => {c | v c ∈ badPt g (d m)})
    (fun m => le_trans (cnt_le_of_inj v hv fun _ hc => hc) (cnt_badPt g (d m))) h

/-- The same for a family of vectors with one bad set. -/
theorem Doomed.cons_ptFam {r : Round} {s : Shape} (ε : Err s) (bad : Tr (r :: s) → Prop) {g : ℕ}
    {J : Type} (v : r.Chal → Fin g → E) (hv : Function.Injective v) (d : r.Msg → J → ℕ → E)
    (h : ∀ m c, v c ∉ badPtFam g (d m) → Doomed s ε (fun τ => bad (m, c, τ))) :
    Doomed (r :: s) (g * Fintype.card E ^ (g - 1), ε) bad :=
  Doomed.cons_of_bad _ ε bad (fun m => {c | v c ∈ badPtFam g (d m)})
    (fun m => le_trans (cnt_le_of_inj v hv fun _ hc => hc) (cnt_badPtFam g (d m))) h

end

/-- The carrying that changes nothing. -/
def Carry.refl : (s : Shape) → Carry s s
  | [] => ()
  | _ :: s => (id, id, fun _ _ => Carry.refl s)

theorem Carry.tr_refl : ∀ (s : Shape) (τ : Tr s), (Carry.refl s).tr τ = τ
  | [], () => rfl
  | _ :: s, (m, c, τ) => by
    show (m, c, (Carry.refl s).tr τ) = (m, c, τ)
    rw [Carry.tr_refl s τ]

theorem Carry.inj_refl : ∀ s : Shape, (Carry.refl s).Inj
  | [] => trivial
  | _ :: s => ⟨Function.injective_id, fun _ _ => Carry.inj_refl s⟩

end Johnson.L5.Layers
