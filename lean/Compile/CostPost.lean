-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/CostPost.lean: a bound on the weight of the queries of an oracle algorithm together with a
property of its result (words of this library: lean/GLOSSARY.md).

A few rules, generic in the family of oracles and in the weight. Rom/OverOneN.lean has
`OComp.CostBoundAt w c t`: on every path the weights of the queries of c add up to at most t. To
bound (c.bind g) one often has to know something of what c returns (how long a list is, how many
slots hold a request). Compile/CostAt.lean has that for token programs (`SWA`). Here is the same for
ordinary oracle algorithms.

  `OComp.CA w c m P`       On every path the weights add up to at most m, and the result has the
                           property P.
  `CA.cost`, `CA.ofCost`   `CA` gives `CostBoundAt`; and `CostBoundAt` gives it with the property
                           that is always true.
  `SWA.ca`                 The erasure of a token program has the bound and the property of the
                           program.
  `CA.blocks`, `CA.derive`
                           Making samples from small ones costs nothing; deriving n samples from a
                           seed costs at most n · u more, if a query to the auxiliary oracle for the
                           seed weighs at most u.

Limits: nothing on probabilities. All bounds hold on every path.
Terms: lean/GLOSSARY.md.
-/
import Compile.CostAt

namespace Rom
namespace OComp

variable {S : OSpec} {α β : Type} (w : (o : S.ι) → S.Dom o → ℕ)

/-- On every path the weights of the queries add up to at most m, and the result has the property
P. -/
def CA : OComp S α → ℕ → (α → Prop) → Prop
  | .pure a, _, P => P a
  | .sample _ k, m, P => ∀ r, CA (k r) m P
  | .query o q k, m, P => ∃ m', w o q + m' ≤ m ∧ ∀ r, CA (k r) m' P

variable {w}

theorem CA.pure {a : α} {P : α → Prop} (h : P a) (m : ℕ) : CA w (OComp.pure a : OComp S α) m P := h

theorem CA.mono {c : OComp S α} {P P' : α → Prop} (hP : ∀ a, P a → P' a) :
    ∀ {m m' : ℕ}, m ≤ m' → CA w c m P → CA w c m' P' := by
  induction c with
  | pure a => exact fun _ h => hP a h
  | sample n k ih => exact fun hm h r => ih r hm (h r)
  | query o q k ih =>
    rintro m m' hm ⟨m0, h0, h⟩
    exact ⟨m0, by omega, fun r => ih r (Nat.le_refl _) (h r)⟩

theorem CA.bind {c : OComp S α} {g : α → OComp S β} {P : α → Prop} {Q : β → Prop}
    {m' : ℕ} (hg : ∀ a, P a → CA w (g a) m' Q) :
    ∀ {m : ℕ}, CA w c m P → CA w (c.bind g) (m + m') Q := by
  induction c with
  | pure a => exact fun h => (hg a h).mono (fun _ h => h) (by omega)
  | sample n k ih => exact fun h r => ih r (h r)
  | query o q k ih =>
    rintro m ⟨m0, h0, h⟩
    exact ⟨m0 + m', by omega, fun r => ih r (h r)⟩

theorem CA.bind' {c : OComp S α} {g : α → OComp S β} {P : α → Prop} {Q : β → Prop} {m m' n : ℕ}
    (hc : CA w c m P) (hg : ∀ a, P a → CA w (g a) m' Q) (hn : m + m' ≤ n) : CA w (c.bind g) n Q :=
  (CA.bind hg hc).mono (fun _ h => h) hn

theorem CA.map {c : OComp S α} {P : α → Prop} {Q : β → Prop} {m : ℕ} (hc : CA w c m P)
    (f : α → β) (hf : ∀ a, P a → Q (f a)) :
    CA w (c.bind fun a => .pure (f a)) m Q :=
  CA.bind' hc (m' := 0) (fun a h => hf a h) (Nat.le_refl _)

/-- `CA` gives the bound `CostBoundAt`. -/
theorem CA.cost {c : OComp S α} {P : α → Prop} : ∀ {m : ℕ}, CA w c m P → c.CostBoundAt w m := by
  induction c with
  | pure a => exact fun _ => trivial
  | sample n k ih => exact fun h r => ih r (h r)
  | query o q k ih =>
    rintro m ⟨m0, h0, h⟩
    exact ⟨m - w o q, by omega, fun r => (ih r (h r)).mono (by omega)⟩

theorem CA.ofCost {c : OComp S α} : ∀ {m : ℕ}, c.CostBoundAt w m → CA w c m fun _ => True := by
  induction c with
  | pure a => exact fun _ => trivial
  | sample n k ih => exact fun h r => ih r (h r)
  | query o q k ih =>
    rintro m ⟨m0, h0, h⟩
    exact ⟨m0, by omega, fun r => ih r (h r)⟩

theorem CA.tossN (v : ℕ) {t : ℕ} {P : α → Prop} :
    ∀ (m : ℕ) (f : (Fin m → Fin (v + 1)) → OComp S α),
      (∀ x, CA w (f x) t P) → CA w (OComp.tossN v m f) t P
  | 0, _, h => h _
  | m + 1, f, h => fun r => CA.tossN v m (fun x => f (Fin.cons r x)) fun _ => h _

/-- Making samples from small ones costs nothing. -/
theorem CA.blocks (bk : CoinPlan) {P : α → Prop} :
    ∀ (c : OComp S α) (t : ℕ), CA w c t P → CA w (c.blocks bk) t P
  | .pure _, _, h => h
  | .query _ _ k, _, ⟨t', e, h⟩ => ⟨t', e, fun r => CA.blocks bk (k r) t' (h r)⟩
  | .sample n k, t, h => CA.tossN bk.w (bk.m n) _ fun x => CA.blocks bk (k (bk.φ n x)) t (h _)

/-- Deriving the coins of an algorithm with exactly n uniform samples on every path costs at most n
· u more, under `hu`. -/
theorem CA.derive (σ : SeedOracle S) (s : Fin (σ.sd + 1)) {u : ℕ} (hu : ∀ j, w σ.o (σ.pt s j) ≤ u)
    {n : ℕ} {c : OComp S α} {P : α → Prop} (hc : Compile.Seed.Tosses n c) :
    ∀ (t j : ℕ), CA w c t P → CA w (c.derive σ s j) (t + n * u) P := by
  induction hc with
  | pure a => exact fun _ _ h => h
  | query o q _ ih =>
    rintro t j ⟨t', e, h⟩
    exact ⟨t' + _, by omega, fun r => ih r t' j (h r)⟩
  | sample m _ ih =>
    intro t j h
    rename_i n k _
    have h1 := hu j
    exact ⟨t + n * u, by rw [Nat.succ_mul]; omega, fun d => ih _ t (j + 1) (h _)⟩

end OComp
end Rom

namespace Compile
namespace CostP
open Rom

variable {S : OSpec} {sp : Split S} {α : Type} {w : (o : S.ι) → S.Dom o → ℕ}

/-- The erased program has the bound and the property of the program. -/
theorem SWA.ca {c : Step S sp α} {P : α → Prop} :
    ∀ {m : ℕ}, SWA w c m P → ∀ vs, OComp.CA w (Compile.erase c vs) m fun o => P o.1 := by
  induction c with
  | pure a => exact fun h _ => h
  | sample n k ih => exact fun h vs r => ih r (h r) vs
  | plain o q k ih =>
    rintro m ⟨c, m0, hc, rfl, h⟩ vs
    exact ⟨m0, by omega, fun r => ih r (h r) vs⟩
  | fresh l k ih => exact fun h vs r => ih _ (h _) _
  | marked o t us pt inj k ih =>
    rintro m ⟨c, m0, hc, rfl, h⟩ vs
    have hc' := hc (vs.getD t []) (us.map fun u => vs.getD u [])
    exact ⟨m0, by omega, fun r => ih _ _ (h _ _) _⟩
  | reveal ts k ih => exact fun h vs => ih _ (h _) vs

end CostP
end Compile
