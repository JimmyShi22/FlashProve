-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/CostPostV.lean: a bound on the weight of the queries of an oracle algorithm together with a
property of its result, where the weight of a query may depend on its answer (words of this library:
lean/GLOSSARY.md).

Generic in the family of oracles and in the weight. The counterpart of Compile/CostPost.lean (`CA`)
for `OComp.CostBoundV` (Rom/SpecOverOneA.lean), as Compile/CostV.lean (`SWV`) is the counterpart of
`SWA` for token programs. Why such weights (Rom/SpecOverOneA.lean, its head): "An algorithm that
makes the same kind of query again and again until the first hash block of the answer passes a check
(a search for a nonce: proof of work) reads only the first hash block of a failed attempt. Whether
an attempt fails is seen in its answer, not in its query."

  `OComp.CAV w c m P`        On every path the weights of the queries, each at its own answer, add
                             up to at most m, and the result has the property P.
  `CAV.cost`, `CAV.ofCost`   `CAV` gives `CostBoundV`; and `CostBoundV` gives it with the property
                             that is always true.
  `CAV.of_ca`                From a weight w₀ that does not depend on the answer and is nowhere
                             smaller: so every bound `CA` for such a weight transfers.
  `SWV.cav`                  The erasure of a token program has the bound and the property of the
                             program.
  `CAV.blocks`, `CAV.derive`
                             Making samples from small ones costs nothing; deriving n samples from a
                             seed costs at most n · u more, if a query to the auxiliary oracle for
                             the seed weighs at most u whatever its answer.

Notation: `SWV w c m P` : Prop, c : `Step S sp α` (Compile/CostV.lean): on every path the weights of
the queries, each at its own answer, add up to at most m, and the result has the property P.

Limits: nothing on probabilities. All bounds hold on every path.
-/
import Compile.CostPost
import Compile.CostV

namespace Rom
namespace OComp

variable {S : OSpec} {α β : Type} (w : (o : S.ι) → S.Dom o → S.Rng o → ℕ)

/-- On every path the weights of the queries, each at its own answer, add up to at most m, and the
result has the property P. -/
def CAV : OComp S α → ℕ → (α → Prop) → Prop
  | .pure a, _, P => P a
  | .sample _ k, m, P => ∀ r, CAV (k r) m P
  | .query o q k, m, P => ∀ r, ∃ m', w o q r + m' ≤ m ∧ CAV (k r) m' P

variable {w}

theorem CAV.pure {a : α} {P : α → Prop} (h : P a) (m : ℕ) : CAV w (OComp.pure a : OComp S α) m P :=
  h

theorem CAV.mono {c : OComp S α} {P P' : α → Prop} (hP : ∀ a, P a → P' a) :
    ∀ {m m' : ℕ}, m ≤ m' → CAV w c m P → CAV w c m' P' := by
  induction c with
  | pure a => exact fun _ h => hP a h
  | sample n k ih => exact fun hm h r => ih r hm (h r)
  | query o q k ih =>
    intro m m' hm h r
    obtain ⟨m0, h0, h1⟩ := h r
    exact ⟨m0, by omega, ih r (Nat.le_refl _) h1⟩

theorem CAV.bind {c : OComp S α} {g : α → OComp S β} {P : α → Prop} {Q : β → Prop}
    {m' : ℕ} (hg : ∀ a, P a → CAV w (g a) m' Q) :
    ∀ {m : ℕ}, CAV w c m P → CAV w (c.bind g) (m + m') Q := by
  induction c with
  | pure a => exact fun h => (hg a h).mono (fun _ h => h) (by omega)
  | sample n k ih => exact fun h r => ih r (h r)
  | query o q k ih =>
    intro m h r
    obtain ⟨m0, h0, h1⟩ := h r
    exact ⟨m0 + m', by omega, ih r h1⟩

theorem CAV.bind' {c : OComp S α} {g : α → OComp S β} {P : α → Prop} {Q : β → Prop} {m m' n : ℕ}
    (hc : CAV w c m P) (hg : ∀ a, P a → CAV w (g a) m' Q) (hn : m + m' ≤ n) :
    CAV w (c.bind g) n Q :=
  (CAV.bind hg hc).mono (fun _ h => h) hn

theorem CAV.map {c : OComp S α} {P : α → Prop} {Q : β → Prop} {m : ℕ} (hc : CAV w c m P)
    (f : α → β) (hf : ∀ a, P a → Q (f a)) :
    CAV w (c.bind fun a => .pure (f a)) m Q :=
  CAV.bind' hc (m' := 0) (fun a h => hf a h) (Nat.le_refl _)

/-- `CAV` gives the bound `CostBoundV`. -/
theorem CAV.cost {c : OComp S α} {P : α → Prop} : ∀ {m : ℕ}, CAV w c m P → c.CostBoundV w m := by
  induction c with
  | pure a => exact fun _ => trivial
  | sample n k ih => exact fun h r => ih r (h r)
  | query o q k ih =>
    intro m h r
    obtain ⟨m0, h0, h1⟩ := h r
    exact ⟨m0, h0, ih r h1⟩

theorem CAV.ofCost {c : OComp S α} : ∀ {m : ℕ}, c.CostBoundV w m → CAV w c m fun _ => True := by
  induction c with
  | pure a => exact fun _ => trivial
  | sample n k ih => exact fun h r => ih r (h r)
  | query o q k ih =>
    intro m h r
    obtain ⟨m0, h0, h1⟩ := h r
    exact ⟨m0, h0, ih r h1⟩

/-- From a weight that does not depend on the answer and is nowhere smaller. -/
theorem CAV.of_ca {w₀ : (o : S.ι) → S.Dom o → ℕ} (hw : ∀ o q r, w o q r ≤ w₀ o q)
    {c : OComp S α} {P : α → Prop} :
    ∀ {m : ℕ}, CA w₀ c m P → CAV w c m P := by
  induction c with
  | pure a => exact fun h => h
  | sample n k ih => exact fun h r => ih r (h r)
  | query o q k ih =>
    rintro m ⟨m0, h0, h⟩ r
    have := hw o q r
    exact ⟨m0, by omega, ih r (h r)⟩

theorem CAV.tossN (v : ℕ) {t : ℕ} {P : α → Prop} :
    ∀ (m : ℕ) (f : (Fin m → Fin (v + 1)) → OComp S α),
      (∀ x, CAV w (f x) t P) → CAV w (OComp.tossN v m f) t P
  | 0, _, h => h _
  | m + 1, f, h => fun r => CAV.tossN v m (fun x => f (Fin.cons r x)) fun _ => h _

/-- Making samples from small ones costs nothing. -/
theorem CAV.blocks (bk : CoinPlan) {P : α → Prop} :
    ∀ (c : OComp S α) (t : ℕ), CAV w c t P → CAV w (c.blocks bk) t P
  | .pure _, _, h => h
  | .query _ _ k, _, h => fun r => let ⟨t', e, h'⟩ := h r; ⟨t', e, CAV.blocks bk (k r) t' h'⟩
  | .sample n k, t, h => CAV.tossN bk.w (bk.m n) _ fun x => CAV.blocks bk (k (bk.φ n x)) t (h _)

/-- Deriving the coins of an algorithm with exactly n uniform samples on every path costs at most n
· u more, under `hu`. -/
theorem CAV.derive (σ : SeedOracle S) (s : Fin (σ.sd + 1)) {u : ℕ}
    (hu : ∀ j r, w σ.o (σ.pt s j) r ≤ u) {n : ℕ} {c : OComp S α}
    {P : α → Prop} (hc : Compile.Seed.Tosses n c) :
    ∀ (t j : ℕ), CAV w c t P → CAV w (c.derive σ s j) (t + n * u) P := by
  induction hc with
  | pure a => exact fun _ _ h => h
  | query o q _ ih =>
    intro t j h r
    obtain ⟨t', e, h'⟩ := h r
    exact ⟨t' + _, by omega, ih r t' j h'⟩
  | sample m _ ih =>
    intro t j h d
    rename_i n k _
    have h1 := hu j d
    exact ⟨t + n * u, by rw [Nat.succ_mul]; omega, ih _ t (j + 1) (h _)⟩

end OComp
end Rom

namespace Compile
namespace CostP
open Rom

variable {S : OSpec} {sp : Split S} {α : Type} {w : (o : S.ι) → S.Dom o → S.Rng o → ℕ}

/-- The erased program has the bound and the property of the program. -/
theorem SWV.cav {c : Step S sp α} {P : α → Prop} :
    ∀ {m : ℕ}, SWV w c m P → ∀ vs, OComp.CAV w (Compile.erase c vs) m fun o => P o.1 := by
  induction c with
  | pure a => exact fun h _ => h
  | sample n k ih => exact fun h vs r => ih r (h r) vs
  | plain o q k ih =>
    intro m h vs r
    obtain ⟨m0, h0, h1⟩ := h r
    exact ⟨m0, h0, ih r h1 vs⟩
  | fresh l k ih => exact fun h vs r => ih _ (h _) _
  | marked o t us pt inj k ih =>
    intro m h vs r
    obtain ⟨c, m0, hc, h0, h1⟩ := h (sp.split o r).1
    have hc' := hc (vs.getD t []) (us.map fun u => vs.getD u []) r rfl
    exact ⟨m0, by omega, ih _ _ (h1 _) _⟩
  | reveal ts k ih => exact fun h vs => ih _ (h _) vs

end CostP
end Compile
