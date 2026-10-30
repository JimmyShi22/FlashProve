-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/Cost.lean: weighted bounds on the queries of an oracle algorithm (`OComp.CostBound`). Over one
hash function f (`OComp.overOne`, Rom/Family.lean), a query to the oracle o of a family becomes
`blocks o` queries to f.

  `queryBound_overOne_of_cost`
                              `CostBound m.blocks c t` gives `(c.overOne m).QueryBound t`.

This is finer than `queryBound_overOne` of Rom/Prefix.lean, which counts every query as the largest
number of hash blocks.

Notation:
  `m`: `OracleCoding S lam` (Rom/Family.lean): the query encoding; `m.blocks o`: `ℕ`; `m.rng o`:
    `S.Rng o ≃ (Fin (m.blocks o) → Fin lam → Bool)`; `m.code o q j`: `List Bool`; hash block j of
    the answer of oracle o at query q is f (code o q j)
  `lam`: `ℕ`; `Fin lam → Bool`: a hash block (`Dg lam`, Rom/NeedA.lean)
  `c.QueryBound t` (Rom/OComp.lean): at most t queries in all, on every path; a repeated query
    counts again
-/
import Rom.Prefix

set_option autoImplicit false

namespace Rom

variable {S : OSpec} {lam : ℕ} {α β : Type}

/-- On every path, whatever the answers and the coins, the weights of the queries add up to at most
t. -/
def OComp.CostBound (w : S.ι → ℕ) : OComp S α → ℕ → Prop
  | .pure _, _ => True
  | .sample _ k, t => ∀ r, (k r).CostBound w t
  | .query o _ k, t => ∃ t', t = w o + t' ∧ ∀ r, (k r).CostBound w t'

namespace OComp.CostBound

variable {w : S.ι → ℕ}

theorem mono {c : OComp S α} : ∀ {s t : ℕ}, c.CostBound w s → s ≤ t → c.CostBound w t := by
  induction c with
  | pure a => exact fun _ _ => trivial
  | sample n k ih => exact fun h hst r => ih r (h r) hst
  | query o q k ih =>
    rintro s t ⟨s', rfl, h⟩ hst
    exact ⟨t - w o, by omega, fun r => ih r (h r) (by omega)⟩

theorem bind {c : OComp S α} {g : α → OComp S β} {t : ℕ} (hg : ∀ a, (g a).CostBound w t) :
    ∀ {s : ℕ}, c.CostBound w s → (c.bind g).CostBound w (s + t) := by
  induction c with
  | pure a => exact fun _ => (hg a).mono (by omega)
  | sample n k ih => exact fun h r => ih r (h r)
  | query o q k ih =>
    rintro s ⟨s', rfl, h⟩
    exact ⟨s' + t, by omega, fun r => ih r (h r)⟩

theorem pure (a : α) (t : ℕ) : (OComp.pure a : OComp S α).CostBound w t := trivial

theorem ask (o : S.ι) (q : S.Dom o) : (OComp.ask o q).CostBound w (w o) :=
  ⟨0, rfl, fun _ => trivial⟩

end OComp.CostBound

/-- If `c.CostBound m.blocks t`, then c over the hash function makes at most t queries. -/
theorem queryBound_overOne_of_cost (m : OracleCoding S lam) (c : OComp S α) :
    ∀ t, c.CostBound m.blocks t → (c.overOne m).QueryBound t := by
  induction c with
  | pure a => exact fun _ _ => trivial
  | sample n k ih => exact fun t h r => ih r t (h r)
  | query o q k ih =>
    rintro t ⟨t', rfl, h⟩
    exact (queryBound_askAll (lam := lam) (m.blocks o) (m.code o q)).bind
      (g := fun bs => (k ((m.rng o).symm bs)).overOne m) fun bs => ih _ t' (h _)

end Rom
