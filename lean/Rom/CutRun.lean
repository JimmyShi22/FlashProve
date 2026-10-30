-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/CutRun.lean: the splitting step for one algorithm. Proofs of `Spec.runCut`, `Spec.cutCost` and
`Spec.cutAll` of Rom/SpecCut.lean, whose doc comments say what the three statements state.

The splitting step replaces an oracle by two oracles on the same queries, one for the first part of
its answer and one for the second (`OCut`, `cutSpec`); the algorithm `c.cut` queries the second only
where a rule that sees the first part says so.

  `runCut`
          If c meets `ReadsCut` (after an answer, and after that answer with the unqueried second
          part replaced by a fixed value, c continues with the same program), then for every fixed
          family F, `c.cut` on `cutFam C F` returns what c returns on F.
  `cutCost`
          For a weight u on the queries over the split family, `wCut C need u` is what a typed query
          costs there. If on every path of c the weights `wCut C need u` add up to at most t, then
          on every path of `c.cut` the weights u do.
  `cutAll`
          Under the rule "always" every algorithm meets `ReadsCut`.

The lemmas `OCut.join_parts`, `front_alone`, `front_join`, `alone_whole` are on the parts of an
answer; `shownCut_of_ask` and `shownCut_of_skip` give the answer as the rule shows it, in the two
cases.

Notation:
  `C o`: `OCut (S.Rng o)` (Rom/SpecCut.lean): how an oracle with answers in R is treated: `whole`,
    or `cut` with `e : R ≃ A × B`
  `(C o).front r`, `(C o).rest r` (Rom/SpecCut.lean): the two parts of a typed answer;
    `(C o).join a b`: the typed answer from its parts; `(C o).alone a`: the typed answer from its
    first part only: the fixed element replaces the second part; `(C o).isWhole`: `true` at `.whole`
  `need`: `NeedCut C` (Rom/SpecCut.lean): a rule: after the first part a of the answer at q, is the
    second part queried?
  `shownCut C need o q r` (Rom/SpecCut.lean): the answer, with the second part replaced where the
    rule does not query it
  `c.runEager F` (Rom/OComp.lean): the oracles fixed: the law of the output over the coins only;
    `F`: `Fam S` (Rom/OSpec.lean): a whole family of functions
  `cutFam C F` (Rom/SpecCut.lean): the family of the parts of a family
  `wCut C need u o q r`: `ℕ` (Rom/SpecCut.lean): what a typed query costs over the second family
    (`cutSpec S C`), if a query there costs u
  `c.CostBoundV w t` (Rom/SpecOverOneA.lean): on every path the weights of the queries add up to at
    most t, where the weight of a query may depend on its answer
  `c.CostBoundAt w t` (Rom/OverOneN.lean): on every path, whatever the answers and the coins, the
    weights w o q of the queries add up to at most t
-/
import Rom.SpecCut

set_option autoImplicit false

noncomputable section

namespace Rom

namespace OCut
variable {R : Type}

theorem join_parts : ∀ (c : OCut R) (r : R), c.join (c.front r) (c.rest r) = r
  | .whole, _ => rfl
  | .cut _ _ _ _ _ e _, r => e.symm_apply_apply r

theorem front_alone : ∀ (c : OCut R) (a : c.Front), c.front (c.alone a) = a
  | .whole, _ => rfl
  | .cut _ _ _ _ _ e dB, a => congrArg Prod.fst (e.apply_symm_apply (a, dB))

theorem front_join : ∀ (c : OCut R) (a : c.Front) (b : c.Rest), c.front (c.join a b) = a
  | .whole, _, _ => rfl
  | .cut _ _ _ _ _ e _, a, b => congrArg Prod.fst (e.apply_symm_apply (a, b))

theorem alone_whole : ∀ (c : OCut R), c.isWhole = true → ∀ r : R, c.alone (c.front r) = r
  | .whole, _, _ => rfl

end OCut

variable {S : OSpec} (C : ∀ o, OCut (S.Rng o)) {α : Type}

theorem shownCut_of_skip {need : NeedCut C} {o : S.ι} {q : S.Dom o} {r : S.Rng o}
    (h : ((C o).isWhole || !need o q ((C o).front r)) = true) :
    shownCut C need o q r = (C o).alone ((C o).front r) := by
  unfold shownCut
  rw [if_pos h]

theorem shownCut_of_ask {need : NeedCut C} {o : S.ι} {q : S.Dom o} {r : S.Rng o}
    (h : ¬ ((C o).isWhole || !need o q ((C o).front r)) = true) : shownCut C need o q r = r := by
  unfold shownCut
  rw [if_neg h]

theorem runCut : Spec.runCut := by
  intro S C α need c
  induction c with
  | pure a => exact fun _ _ => rfl
  | sample n k ih => exact fun h F => congrArg _ (funext fun r => ih r (h r) F)
  | query o q k ih =>
    intro h F
    show (if ((C o).isWhole || !need o q ((C o).front (F o q))) = true then
            (k ((C o).alone ((C o).front (F o q)))).cut C need
          else
            OComp.query (S := cutSpec S C) (.inr o) q fun b =>
              (k ((C o).join ((C o).front (F o q)) b)).cut C need).runEager (cutFam C F) =
      (k (F o q)).runEager F
    by_cases hc : ((C o).isWhole || !need o q ((C o).front (F o q))) = true
    · rw [if_pos hc, ih _ (h.2 _) F, h.1 (F o q) _ rfl, shownCut_of_skip C hc]
    · rw [if_neg hc]
      show ((k ((C o).join ((C o).front (F o q)) ((C o).rest (F o q)))).cut C need).runEager
          (cutFam C F) = _
      rw [OCut.join_parts, ih _ (h.2 _) F]

theorem cutCost : Spec.cutCost := by
  intro S C α need u c
  induction c with
  | pure a => exact fun _ _ => trivial
  | sample n k ih => exact fun t h r => ih r t (h r)
  | query o q k ih =>
    intro t h
    obtain ⟨r0⟩ := S.neRng o
    have h0 : u (.inl o) q ≤ t := by
      obtain ⟨t', e, -⟩ := h r0
      unfold wCut at e
      omega
    refine ⟨t - u (.inl o) q, by omega, fun a => ?_⟩
    show (if ((C o).isWhole || !need o q a) = true then (k ((C o).alone a)).cut C need
        else
          OComp.query (S := cutSpec S C) (.inr o) q fun b =>
            (k ((C o).join a b)).cut C need).CostBoundAt
      u (t - u (.inl o) q)
    by_cases hc : ((C o).isWhole || !need o q a) = true
    · rw [if_pos hc]
      obtain ⟨t', e, h'⟩ := h ((C o).alone a)
      unfold wCut at e
      rw [OCut.front_alone, if_pos hc] at e
      exact (ih _ t' h').mono (by omega)
    · rw [if_neg hc]
      obtain ⟨b0⟩ := OCut.neRest (C o)
      have h1 : u (.inl o) q + u (.inr o) q ≤ t := by
        obtain ⟨t', e, -⟩ := h ((C o).join a b0)
        unfold wCut at e
        rw [OCut.front_join, if_neg hc] at e
        omega
      refine ⟨t - u (.inl o) q - u (.inr o) q, by omega, fun b => ?_⟩
      obtain ⟨t', e, h'⟩ := h ((C o).join a b)
      unfold wCut at e
      rw [OCut.front_join, if_neg hc] at e
      exact (ih _ t' h').mono (by omega)

theorem cutAll : Spec.cutAll := by
  intro S C α c
  induction c with
  | pure a => trivial
  | sample n k ih => exact fun r => ih r
  | query o q k ih =>
    refine ⟨fun r r' e => ?_, fun r => ih r⟩
    rw [e]
    by_cases hw : (C o).isWhole = true
    · rw [shownCut_of_skip C (by rw [hw]; rfl), OCut.alone_whole _ hw]
    · rw [shownCut_of_ask C (by simpa using hw)]

end Rom
