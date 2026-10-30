-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/Defer2Adv.lean: tools for the hypothesis of the lemma on deferred programming of the random
oracle (`Spec.defer2`, CompileK/SpecDefer2.lean): `Step.Alw` is monotone in its end and goes through
bind; `AdvAlw` follows from any property of (adversary, state) that meets the four conditions of
`advAlw_of_inv` (`hhalt`, `hsample`, `hquery`, `hcall`), one for each kind of move.

Theorems `alw_mono`, `alw_bind`, `advAlw_of_inv`. Framework only. Nothing assumed beyond the
hypotheses of the statements and whatever the arguments hold as proofs. `Step.Alw` and `AdvAlw` are
recursions along a program and along an adversary: conditions at every marked evaluation, a property
G of states on the way, and an end: the last argument Post of `Step.Alw`; for `AdvAlw`, Fn at a
halt.
-/
import CompileK.SpecDefer2

set_option autoImplicit false

namespace Rom
namespace DeferTail2
open DeferTail

variable {S : OSpec} {sp : Split S} {K : Type} {cl : PtCls S K} {J : K → Bool} {G : DSt S → Prop}

theorem alw_mono {α : Type} {Post Post' : α × DSt S → Prop}
    (h : ∀ y, Post y → Post' y) (c : Step S sp α) :
    ∀ d, c.Alw cl J G d Post → c.Alw cl J G d Post' := by
  induction c with
  | pure a => exact fun d hd => h _ hd
  | sample n k ih => exact fun d hd r => ih r d (hd r)
  | plain o q k ih => exact fun d hd y hy => ih y.1 _ (hd y hy)
  | fresh L k ih => exact fun d hd u => ih _ _ (hd u)
  | marked o t us pt inj k ih => exact fun d hd => ⟨hd.1, hd.2.1, fun r => ⟨(hd.2.2 r).1, ih _ _ _ (hd.2.2 r).2⟩⟩
  | reveal ts k ih => exact fun d hd => ⟨hd.1, ih _ _ hd.2⟩

theorem alw_bind {α β : Type} {Post : β × DSt S → Prop} (c : Step S sp α) (g : α → Step S sp β) :
    ∀ d, c.Alw cl J G d (fun y => (g y.1).Alw cl J G y.2 Post) → (c.bind g).Alw cl J G d Post := by
  induction c with
  | pure a => exact fun d hd => hd
  | sample n k ih => exact fun d hd r => ih r d (hd r)
  | plain o q k ih => exact fun d hd y hy => ih y.1 _ (hd y hy)
  | fresh L k ih => exact fun d hd u => ih _ _ (hd u)
  | marked o t us pt inj k ih => exact fun d hd => ⟨hd.1, hd.2.1, fun r => ⟨(hd.2.2 r).1, ih _ _ _ (hd.2.2 r).2⟩⟩
  | reveal ts k ih => exact fun d hd => ⟨hd.1, ih _ _ hd.2⟩

/-- From moves to runs. -/
theorem advAlw_of_inv {Out In α : Type} (C : Chall S sp Out In) (Fn : DSt S → Prop)
    (P : Adv S Out In α → C.τ × DSt S → Prop) (hhalt : ∀ a s, P (.halt a) s → Fn s.2)
    (hsample : ∀ n k s, P (.sample n k) s → ∀ r, P (k r) s)
    (hquery : ∀ o q k s, P (.query o q k) s → ∀ r T, P (k r) (s.1, withT s.2 T))
    (hcall : ∀ m k s,
      P (.call m k) s → (C.step s.1 m).Alw cl J G s.2 fun y => P (k y.1.1) (y.1.2, y.2))
    (A : Adv S Out In α) :
    ∀ s, P A s → AdvAlw C cl J G Fn A s := by
  induction A with
  | halt a => exact fun s h => hhalt a s h
  | sample n k ih => exact fun s h r => ih r s (hsample n k s h r)
  | query o q k ih => exact fun s h y _ => ih y.1 _ (hquery o q k s h y.1 y.2)
  | call m k ih => exact fun s h => alw_mono (fun y hy => ih y.1.1 _ hy) _ _ (hcall m k s h)

end DeferTail2
end Rom
