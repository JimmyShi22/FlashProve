-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/CostAt.lean: queries with weights that may depend on the query: rules for programs with
tokens, and the cost of making and deriving samples (words of this library: lean/GLOSSARY.md).

Why: the step to one hash function implements a family of oracles, whose answers are tuples of hash
blocks of lam bits, by one hash function f (Rom/Family.lean). In Rom/OverOneN.lean a function of the
oracle, the query and the number j of a hash block marks hash blocks, and f is queried for the
marked ones only; an unmarked one is the all-zero block (what is proved of that step and what is
not: its head). So in that step a typed query costs as many hash queries as hash blocks of its
answer are marked, and that number depends on the query: `OComp.CostBoundAt`. This file has the
rules for weights w o q, which may depend on the query q.

Part 1
  `SWA w c m P`    On every path, whatever the answers, the coins and the strings of the tokens, the
                   weights of the queries of the program c add up to at most m, and its result has
                   the property P. At a query a bound for its weight is counted; a marked query
                   depends on the strings of its tokens, so the bound holds for all of them. Rules:
                   `SWA.mono`, `SWA.bind`, `SWA.bind'`, `SWA.pure`.
  `SWA.erase`      The erased program, from any list of strings, has `OComp.CostBoundAt w m`.
Part 2
  `CostBoundAt.tossN`, `CostBoundAt.blocks`
                   Making samples from small ones (Rom/Blocks.lean) costs nothing.
  `CostBoundAt.derive`
                   Deriving the coins of an algorithm with exactly n uniform samples on every path
                   (Rom/SpecDerive.lean) costs at most n · u more, if a query to the auxiliary
                   oracle for the seed weighs at most u.

Limits: nothing on any scheme. All are upper bounds on weighted numbers of queries; nothing on time
or memory.
-/
import Rom.OverOneN
import Compile.SeedRootCost

set_option autoImplicit false

open Rom Iop

namespace Compile
namespace CostP

/-! ## Part 1. Programs with tokens -/

section SWA
variable {S : OSpec} {sp : Split S} {α β : Type} (w : (o : S.ι) → S.Dom o → ℕ)

/-- On every path the weights of the queries of the program add up to at most m, and its result has
the property P. -/
def SWA : Step S sp α → ℕ → (α → Prop) → Prop
  | .pure a, _, P => P a
  | .sample _ k, m, P => ∀ r, SWA (k r) m P
  | .plain o q k, m, P => ∃ c m', w o q ≤ c ∧ m = c + m' ∧ ∀ r, SWA (k r) m' P
  | .fresh _ k, m, P => ∀ t, SWA (k t) m P
  | .marked o _ _ pt _ k, m, P => ∃ c m', (∀ v vs, w o (pt v vs) ≤ c) ∧ m = c + m' ∧ ∀ v t, SWA (k v t) m' P
  | .reveal _ k, m, P => ∀ vs, SWA (k vs) m P

variable {w}

theorem SWA.pure {a : α} {P : α → Prop} (h : P a) (m : ℕ) : SWA w (Step.pure a : Step S sp α) m P :=
  h

theorem SWA.mono {c : Step S sp α} {P P' : α → Prop} (hP : ∀ a, P a → P' a) :
    ∀ {m m' : ℕ}, m ≤ m' → SWA w c m P → SWA w c m' P' := by
  induction c with
  | pure a => exact fun _ h => hP a h
  | sample n k ih => exact fun hm h r => ih r hm (h r)
  | plain o q k ih =>
    rintro m m' hm ⟨c, m0, hc, rfl, h⟩
    exact ⟨c, m' - c, hc, by omega, fun r => ih r (by omega) (h r)⟩
  | fresh l k ih => exact fun hm h t => ih t hm (h t)
  | marked o t us pt inj k ih =>
    rintro m m' hm ⟨c, m0, hc, rfl, h⟩
    exact ⟨c, m' - c, hc, by omega, fun v t => ih v t (by omega) (h v t)⟩
  | reveal ts k ih => exact fun hm h vs => ih vs hm (h vs)

theorem SWA.bind {c : Step S sp α} {g : α → Step S sp β} {P : α → Prop} {Q : β → Prop}
    {m' : ℕ} (hg : ∀ a, P a → SWA w (g a) m' Q) :
    ∀ {m : ℕ}, SWA w c m P → SWA w (c.bind g) (m + m') Q := by
  induction c with
  | pure a => exact fun h => (hg a h).mono (fun _ h => h) (by omega)
  | sample n k ih => exact fun h r => ih r (h r)
  | plain o q k ih =>
    rintro m ⟨c, m0, hc, rfl, h⟩
    exact ⟨c, m0 + m', hc, by omega, fun r => ih r (h r)⟩
  | fresh l k ih => exact fun h t => ih t (h t)
  | marked o t us pt inj k ih =>
    rintro m ⟨c, m0, hc, rfl, h⟩
    exact ⟨c, m0 + m', hc, by omega, fun v t => ih v t (h v t)⟩
  | reveal ts k ih => exact fun h vs => ih vs (h vs)

theorem SWA.bind' {c : Step S sp α} {g : α → Step S sp β} {P : α → Prop} {Q : β → Prop} {m m' n : ℕ}
    (hc : SWA w c m P) (hg : ∀ a, P a → SWA w (g a) m' Q) (hn : m + m' ≤ n) :
    SWA w (c.bind g) n Q :=
  (SWA.bind hg hc).mono (fun _ h => h) hn

/-- The erased program costs no more. -/
theorem SWA.erase {c : Step S sp α} {P : α → Prop} :
    ∀ {m : ℕ}, SWA w c m P → ∀ vs, (erase c vs).CostBoundAt w m := by
  induction c with
  | pure a => exact fun _ _ => trivial
  | sample n k ih => exact fun h vs r => ih r (h r) vs
  | plain o q k ih =>
    rintro m ⟨c, m0, hc, rfl, h⟩ vs
    exact ⟨c - w o q + m0, by omega, fun r => (ih r (h r) vs).mono (by omega)⟩
  | fresh l k ih => exact fun h vs r => ih _ (h _) _
  | marked o t us pt inj k ih =>
    rintro m ⟨c, m0, hc, rfl, h⟩ vs
    have hc' := hc (vs.getD t []) (us.map fun u => vs.getD u [])
    exact ⟨c - w o (pt (vs.getD t []) (us.map fun u => vs.getD u [])) + m0,
      by omega,
      fun r => (ih _ _ (h _ _) _).mono (by omega)⟩
  | reveal ts k ih => exact fun h vs => ih _ (h _) vs

end SWA

end CostP
end Compile

/-! ## Part 2. Samples -/

namespace Rom
namespace OComp

variable {S : OSpec} {α : Type} {w : (o : S.ι) → S.Dom o → ℕ}

theorem CostBoundAt.tossN (v : ℕ) {t : ℕ} :
    ∀ (m : ℕ) (f : (Fin m → Fin (v + 1)) → OComp S α),
      (∀ x, (f x).CostBoundAt w t) → (OComp.tossN v m f).CostBoundAt w t
  | 0, _, h => h _
  | m + 1, f, h => fun r => CostBoundAt.tossN v m (fun x => f (Fin.cons r x)) fun _ => h _

/-- Making samples from small ones costs nothing. -/
theorem CostBoundAt.blocks (bk : CoinPlan) :
    ∀ (c : OComp S α) (t : ℕ), c.CostBoundAt w t → (c.blocks bk).CostBoundAt w t
  | .pure _, _, _ => trivial
  | .query _ _ k, _, ⟨t', e, h⟩ => ⟨t', e, fun r => CostBoundAt.blocks bk (k r) t' (h r)⟩
  | .sample n k, t, h =>
    CostBoundAt.tossN bk.w (bk.m n) _ fun x => CostBoundAt.blocks bk (k (bk.φ n x)) t (h _)

/-- Deriving the coins of an algorithm with exactly n uniform samples on every path costs at most n
· u more, if a query to the auxiliary oracle for the seed weighs at most u. -/
theorem CostBoundAt.derive (σ : SeedOracle S) (s : Fin (σ.sd + 1)) {u : ℕ}
    (hu : ∀ j, w σ.o (σ.pt s j) ≤ u) {n : ℕ} {c : OComp S α} (hc : Compile.Seed.Tosses n c) :
    ∀ (t j : ℕ), c.CostBoundAt w t → (c.derive σ s j).CostBoundAt w (t + n * u) := by
  induction hc with
  | pure a => exact fun _ _ _ => trivial
  | query o q _ ih =>
    rintro t j ⟨t', rfl, h⟩
    exact ⟨t' + _, by omega, fun r => ih r t' j (h r)⟩
  | sample m _ ih =>
    intro t j h
    rename_i n k _
    have h1 := hu j
    exact ⟨u - w σ.o (σ.pt s j) + (t + n * u),
      by rw [Nat.succ_mul]; omega,
      fun d => (ih _ t (j + 1) (h _)).mono (by omega)⟩

end OComp
end Rom
