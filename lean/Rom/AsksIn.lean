-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/AsksIn.lean: "every query of the algorithm has the property P" (`OComp.AsksIn`,
Rom/SigmaExits.lean) under weakening of P (`AsksIn.mono`), bind (`AsksIn.bind`) and two changes of
oracles. Generic.

  `AsksIn.cut`         If c queries only oracles with P, then after the splitting of answers
                       (`OComp.cut`, Rom/SpecCut.lean: an oracle o becomes two, `.inl o` and
                       `.inr o` of `cutSpec`) it queries only the two oracles of such oracles.
  `AsksIn.stateFirstA` If every query of c has P, then after the expansion from a state under a rule
                       (`OComp.stateFirstA`, Rom/StateFirstLazy.lean) every query has P or goes to
                       the added oracle dr (`.inr ()` of `stSpec`).

No mathematics beyond inductions on programs.

Notation:
  in `AsksIn.cut`: `C o`: `OCut (S.Rng o)` (Rom/SpecCut.lean): how an oracle with answers in R is
    treated: `whole`, or `cut` with `e : R ≃ A × B`; `need`: `NeedCut C` (there): a rule: after the
    first part a of the answer at q, is the second part queried?
  in `AsksIn.stateFirstA`: `C o`: `Link lam (S.Rng o)` (Rom/StateFirst.lean): how an oracle with
    answers in R is treated: `plain`, or `chain K e` with
    `e : R ≃ (Fin K → Dg lam) × Dg lam × Dg lam`; `need`: `NeedA S lam` (Rom/NeedA.lean): a rule
    that says which hash blocks are queried
  `stSpec S lam C` (Rom/StateFirst.lean): the second family; `.inl o`: the oracle o, with answers in
    `(C o).Ans`; `.inr ()`: the oracle dr, on `(Dg lam × Dg lam) × ℕ`, with answers in `Dg lam`
  `lam`: `ℕ`; `Dg lam`: `Fin lam → Bool` (Rom/NeedA.lean): a hash block
  `askAd C σ nd K j acc` (Rom/StateFirstLazy.lean): the queries to dr at a state under a rule: K
    indices from j on; acc: the hash blocks so far
  `expandA C c nd a` (Rom/StateFirstLazy.lean): from the answer of the second family to the typed
    answer, under a rule
-/
import Rom.SigmaExits

set_option autoImplicit false

namespace Rom
variable {S : OSpec} {α β : Type}

theorem OComp.AsksIn.mono {P Q : (o : S.ι) → S.Dom o → Prop} (h : ∀ o q, P o q → Q o q) :
    ∀ {c : OComp S α}, c.AsksIn P → c.AsksIn Q
  | .pure _, _ => trivial
  | .sample _ _, hc => fun r => (hc r).mono h
  | .query _ _ _, hc => ⟨h _ _ hc.1, fun r => (hc.2 r).mono h⟩

theorem OComp.AsksIn.bind {P : (o : S.ι) → S.Dom o → Prop}
    {g : α → OComp S β} (hg : ∀ a, (g a).AsksIn P) :
    ∀ {c : OComp S α}, c.AsksIn P → (c.bind g).AsksIn P
  | .pure a, _ => hg a
  | .sample _ _, hc => fun r => (hc r).bind hg
  | .query _ _ _, hc => ⟨hc.1, fun r => (hc.2 r).bind hg⟩

/-- the property on the split family: that of the oracle o, at both its parts -/
def asksCut (C : ∀ o, OCut (S.Rng o)) (P : S.ι → Prop) :
    (x : (cutSpec S C).ι) → (cutSpec S C).Dom x → Prop
  | .inl o, _ => P o
  | .inr o, _ => P o

theorem OComp.AsksIn.cut (C : ∀ o, OCut (S.Rng o)) (need : NeedCut C) {P : S.ι → Prop} :
    ∀ {c : OComp S α}, c.AsksIn (fun o _ => P o) → (c.cut C need).AsksIn (asksCut C P)
  | .pure _, _ => trivial
  | .sample _ _, hc => fun r => (hc r).cut C need
  | .query o q k, hc => by
      refine ⟨hc.1, fun a => ?_⟩
      show (if (C o).isWhole || !need o q a then (k ((C o).alone a)).cut C need
          else .query (S := cutSpec S C) (.inr o) q fun b => (k ((C o).join a b)).cut C need).AsksIn
        (asksCut C P)
      split
      · exact (hc.2 _).cut C need
      · exact ⟨hc.1, fun b => (hc.2 _).cut C need⟩

variable {lam : ℕ}

/-- after the expansion: P at S's oracles; anything at dr -/
def asksSt (C : ∀ o, Link lam (S.Rng o)) (P : (o : S.ι) → S.Dom o → Prop) :
    (x : (stSpec S lam C).ι) → (stSpec S lam C).Dom x → Prop
  | .inl o, q => P o q
  | .inr _, _ => True

theorem asksIn_askAd (C : ∀ o, Link lam (S.Rng o)) (P : (o : S.ι) → S.Dom o → Prop)
    (σ : Dg lam × Dg lam) (nd : ℕ → (ℕ → Dg lam) → Bool) :
    ∀ (K j : ℕ) (acc : ℕ → Dg lam), (askAd C σ nd K j acc).AsksIn (asksSt C P)
  | 0, _, _ => trivial
  | K + 1, j, acc => by
      unfold askAd
      cases nd j acc with
      | true => exact ⟨trivial, fun r => asksIn_askAd C P σ nd K (j + 1) _⟩
      | false => exact asksIn_askAd C P σ nd K (j + 1) acc

theorem asksIn_expandA (C : ∀ o, Link lam (S.Rng o)) (P : (o : S.ι) → S.Dom o → Prop) {R : Type}
    (c : Link lam R) (nd : ℕ → (ℕ → Dg lam) → Bool) (a : c.Ans) :
    (expandA C c nd a).AsksIn (asksSt C P) := by
  cases c with
  | plain => trivial
  | chain K e =>
    exact OComp.AsksIn.bind (g := fun acc => OComp.pure (e.symm ((fun i : Fin K => acc i.val), a)))
      (fun _ => trivial) (asksIn_askAd C P a nd K 0 (acc0 lam))

theorem OComp.AsksIn.stateFirstA
    (C : ∀ o, Link lam (S.Rng o)) (need : NeedA S lam) {P : (o : S.ι) → S.Dom o → Prop} :
    ∀ {c : OComp S α}, c.AsksIn P → (c.stateFirstA C need).AsksIn (asksSt C P)
  | .pure _, _ => trivial
  | .sample _ _, hc => fun r => (hc r).stateFirstA C need
  | .query o q _, hc =>
    ⟨hc.1, fun a =>
        (asksIn_expandA C P (C o) (need o q) a).bind fun r => (hc.2 r).stateFirstA C need⟩

end Rom
