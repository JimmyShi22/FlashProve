-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/CostV.lean: the cost of a token program, if the weight of a query may depend on its answer
(words of this library: lean/GLOSSARY.md).

These are the rules `SWA` of Compile/CostAt.lean for such weights. Reason. `SWA` fixes, at a query,
what is left for the rest before the answer is seen. A proof-of-work search that goes on after a
cheap failed attempt and ends after an expensive final one needs the other order.

  `SWV w c m P`    On every path, whatever the answers, the coins and the strings of the tokens, the
                   weights w o q r of the queries of c, each at its own answer r, add up to at most
                   m, and its result has the property P. At a marked query the bound on the weight
                   and what is left may depend on the visible part v of the answer; the bound holds
                   for all strings of the tokens and all answers with that visible part. Rules:
                   `SWV.pure`, `mono`, `bind`, `bind'`.
  `SWV.erase`      The erased program, from any list of strings, has `OComp.CostBoundV w m`
                   (Rom/SpecOverOneA.lean).
  `SWV.of_swa`     From `SWA`: a program that is bounded for a weight w₀ that does not depend on the
                   answer is bounded for every w with w o q r ≤ w₀ o q. So a part without a search
                   keeps its bound from `SWA`.

Notation: token program: a `Step S sp α` (Rom/Defer.lean); token: a `Tok` (the same file); `.fresh`,
`.marked o t us pt inj k`, `.reveal`: constructors of `Step`: see that file's head, "Rules", and
`Step.run`; `pt x vs`, a query to o: the point of the marked evaluation, at the string x of the
charged token t and the strings vs of the further tokens us (`Step.run`, the same file); visible
part: `(sp.split o r).1` (`Split`, the same file).

Limits: nothing on any program.
-/
import Compile.CostAt
import Rom.CostV

set_option autoImplicit false

open Rom Iop

namespace Compile
namespace CostP

variable {S : OSpec} {sp : Split S} {α β : Type} (w : (o : S.ι) → S.Dom o → S.Rng o → ℕ)

/-- On every path the weights of the queries, each at its own answer, add up to at most m, and the
result has the property P. -/
def SWV : Step S sp α → ℕ → (α → Prop) → Prop
  | .pure a, _, P => P a
  | .sample _ k, m, P => ∀ r, SWV (k r) m P
  | .plain o q k, m, P => ∀ r, ∃ m', w o q r + m' ≤ m ∧ SWV (k r) m' P
  | .fresh _ k, m, P => ∀ t, SWV (k t) m P
  | .marked o _ _ pt _ k, m, P =>
    ∀ v, ∃ c m',
      (∀ x vs r, (sp.split o r).1 = v → w o (pt x vs) r ≤ c) ∧ c + m' ≤ m ∧ ∀ t, SWV (k v t) m' P
  | .reveal _ k, m, P => ∀ vs, SWV (k vs) m P

variable {w}

theorem SWV.pure {a : α} {P : α → Prop} (h : P a) (m : ℕ) : SWV w (Step.pure a : Step S sp α) m P :=
  h

theorem SWV.mono {c : Step S sp α} {P P' : α → Prop} (hP : ∀ a, P a → P' a) :
    ∀ {m m' : ℕ}, m ≤ m' → SWV w c m P → SWV w c m' P' := by
  induction c with
  | pure a => exact fun _ h => hP a h
  | sample n k ih => exact fun hm h r => ih r hm (h r)
  | plain o q k ih =>
    intro m m' hm h r
    obtain ⟨m0, h1, h2⟩ := h r
    exact ⟨m0, h1.trans hm, ih r le_rfl h2⟩
  | fresh l k ih => exact fun hm h t => ih t hm (h t)
  | marked o t us pt inj k ih =>
    intro m m' hm h v
    obtain ⟨c, m0, hc, h1, h2⟩ := h v
    exact ⟨c, m0, hc, h1.trans hm, fun t => ih v t le_rfl (h2 t)⟩
  | reveal ts k ih => exact fun hm h vs => ih vs hm (h vs)

theorem SWV.bind {c : Step S sp α} {g : α → Step S sp β} {P : α → Prop} {Q : β → Prop}
    {m' : ℕ} (hg : ∀ a, P a → SWV w (g a) m' Q) :
    ∀ {m : ℕ}, SWV w c m P → SWV w (c.bind g) (m + m') Q := by
  induction c with
  | pure a => exact fun h => (hg a h).mono (fun _ h => h) (by omega)
  | sample n k ih => exact fun h r => ih r (h r)
  | plain o q k ih =>
    intro m h r
    obtain ⟨m0, h1, h2⟩ := h r
    exact ⟨m0 + m', by omega, ih r h2⟩
  | fresh l k ih => exact fun h t => ih t (h t)
  | marked o t us pt inj k ih =>
    intro m h v
    obtain ⟨c, m0, hc, h1, h2⟩ := h v
    exact ⟨c, m0 + m', hc, by omega, fun t => ih v t (h2 t)⟩
  | reveal ts k ih => exact fun h vs => ih vs (h vs)

theorem SWV.bind' {c : Step S sp α} {g : α → Step S sp β} {P : α → Prop} {Q : β → Prop} {m m' n : ℕ}
    (hc : SWV w c m P) (hg : ∀ a, P a → SWV w (g a) m' Q) (hn : m + m' ≤ n) :
    SWV w (c.bind g) n Q :=
  (SWV.bind hg hc).mono (fun _ h => h) hn

/-- The erased program costs no more. -/
theorem SWV.erase {c : Step S sp α} {P : α → Prop} :
    ∀ {m : ℕ}, SWV w c m P → ∀ vs, (erase c vs).CostBoundV w m := by
  induction c with
  | pure a => exact fun _ _ => trivial
  | sample n k ih => exact fun h vs r => ih r (h r) vs
  | plain o q k ih =>
    intro m h vs r
    obtain ⟨m0, h1, h2⟩ := h r
    exact ⟨m0, h1, ih r h2 vs⟩
  | fresh l k ih => exact fun h vs r => ih _ (h _) _
  | marked o t us pt inj k ih =>
    intro m h vs r
    obtain ⟨c, m0, hc, h1, h2⟩ := h (sp.split o r).1
    exact ⟨m0, (Nat.add_le_add_right (hc _ _ r rfl) m0).trans h1, ih _ _ (h2 _) _⟩
  | reveal ts k ih => exact fun h vs => ih _ (h _) vs

/-- From a weight that does not depend on the answer and is nowhere smaller. -/
theorem SWV.of_swa {w₀ : (o : S.ι) → S.Dom o → ℕ} (hw : ∀ o q r, w o q r ≤ w₀ o q)
    {c : Step S sp α} {P : α → Prop} :
    ∀ {m : ℕ}, SWA w₀ c m P → SWV w c m P := by
  induction c with
  | pure a => exact fun h => h
  | sample n k ih => exact fun h r => ih r (h r)
  | plain o q k ih =>
    rintro m ⟨c, m0, hc, rfl, h⟩ r
    exact ⟨m0, Nat.add_le_add_right ((hw o q r).trans hc) m0, ih r (h r)⟩
  | fresh l k ih => exact fun h t => ih t (h t)
  | marked o t us pt inj k ih =>
    rintro m ⟨c, m0, hc, rfl, h⟩ v
    exact ⟨c, m0, fun x vs r _ => (hw o _ r).trans (hc x vs), le_rfl, fun t => ih v t (h v t)⟩
  | reveal ts k ih => exact fun h vs => ih vs (h vs)

end CostP
end Compile
