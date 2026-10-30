-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/OverOneNRel.lean: oracle algorithms that carry along more of an answer than they ever use.
Generic in the family of oracles; a companion to Section 5 of Rom/OverOneN.lean.

In Rom/OverOneN.lean, `OComp.FactorsBy ag c` says that at every query of the algorithm c, two
answers that are related by ag lead to the same continuation program. It is proved piece by piece
(`FactorsBy.bind`), and that requires each piece to return the same value after related answers. An
algorithm that keeps a whole answer in a value which it passes from one piece to the next, and later
reads only a part of it, has the property as a whole, but its pieces do not. Here the pieces are
compared up to a relation R on what they return: `OComp.FactorsByR ag R c`, "c is an algorithm up to
R": after two answers that are related by ag the algorithm goes on in the same way, up to R at its
leaves (`AlikeO R`); and every value a that it returns has R a a. `FactorsByR.bind` is for
sequential composition. For R equality `FactorsByR` is `FactorsBy` (`FactorsBy.toR`,
`FactorsByR.toFactorsBy`). (Compile/NeedRel.lean does the same for programs of the token language
(`Step`, Rom/Defer.lean); Compile/NeedRelErase.lean ties the two.)

Notation:
  `ag`: for each oracle o and query q, a relation on two answers, of type
      `∀ o, S.Dom o → S.Rng o → S.Rng o → Prop`

Limits: nothing on any scheme. For a relation R other than equality, `FactorsByR ag R c` does not
say that c returns the same after related answers: the algorithm that returns the whole answer has
it for R = (fun _ _ => True). Only R = equality leads on, by `FactorsByR.toFactorsBy`.
-/
import Rom.OverOneN

set_option autoImplicit false

namespace Rom

variable {S : OSpec} {α β : Type}

/-- The same algorithm but for the values at its leaves, which are related by R. For R equality the
algorithms are equal (`AlikeO.eq`). -/
inductive OComp.AlikeO (R : α → α → Prop) : OComp S α → OComp S α → Prop
  | pure {a a' : α} (h : R a a') : AlikeO R (.pure a) (.pure a')
  | sample (n : ℕ) {k k' : Fin (n + 1) → OComp S α} (h : ∀ r, AlikeO R (k r) (k' r)) :
      AlikeO R (.sample n k) (.sample n k')
  | query (o : S.ι) (q : S.Dom o) {k k' : S.Rng o → OComp S α} (h : ∀ r, AlikeO R (k r) (k' r)) :
      AlikeO R (.query o q k) (.query o q k')

namespace OComp.AlikeO
variable {R : α → α → Prop} {R' : β → β → Prop}

theorem bind {c c' : OComp S α} {g g' : α → OComp S β} (hc : AlikeO R c c')
    (hg : ∀ a a', R a a' → AlikeO R' (g a) (g' a')) :
    AlikeO R' (c.bind g) (c'.bind g') := by
  induction hc with
  | pure h => exact hg _ _ h
  | sample n _ ih => exact .sample n ih
  | query o q _ ih => exact .query o q ih

theorem eq {c c' : OComp S α} (h : AlikeO Eq c c') : c = c' := by
  induction h with
  | pure h => exact congrArg OComp.pure h
  | sample n _ ih => exact congrArg (OComp.sample n) (funext ih)
  | query o q _ ih => exact congrArg (OComp.query o q) (funext ih)

theorem refl (hR : ∀ a, R a a) (c : OComp S α) : AlikeO R c c := by
  induction c with
  | pure a => exact .pure (hR a)
  | sample n k ih => exact .sample n ih
  | query o q k ih => exact .query o q ih

theorem of_eq {c c' : OComp S α} (h : c = c') : AlikeO Eq c c' := h ▸ refl (fun _ => rfl) c

theorem mono {R₂ : α → α → Prop} (hR : ∀ a a', R a a' → R₂ a a')
    {c c' : OComp S α} (h : AlikeO R c c') : AlikeO R₂ c c' := by
  induction h with
  | pure h => exact .pure (hR _ _ h)
  | sample n _ ih => exact .sample n ih
  | query o q _ ih => exact .query o q ih

/-- The same piece c before two families of algorithms that are alike at every a: `c.bind g` and
`c.bind g'` are alike. -/
theorem bindSame (c : OComp S α) {g g' : α → OComp S β} (hg : ∀ a, AlikeO R' (g a) (g' a)) :
    AlikeO R' (c.bind g) (c.bind g') :=
  (refl (R := Eq) (fun _ => rfl) c).bind fun a _ h => h ▸ hg a

end OComp.AlikeO

/-- "c is an algorithm up to R": after two answers that are related by ag the algorithm goes on in
the same way, up to R at its leaves (`AlikeO R`); and every value a that it returns has R a a. (R
need not be reflexive: "R a a" serves as "a is a well-formed value".) -/
inductive OComp.FactorsByR (ag : ∀ o, S.Dom o → S.Rng o → S.Rng o → Prop) (R : α → α → Prop) :
    OComp S α → Prop
  | pure {a : α} (h : R a a) : FactorsByR ag R (.pure a)
  | sample (n : ℕ) {k : Fin (n + 1) → OComp S α} (h : ∀ r, FactorsByR ag R (k r)) :
      FactorsByR ag R (.sample n k)
  | query (o : S.ι) (q : S.Dom o) {k : S.Rng o → OComp S α}
      (he : ∀ r r', ag o q r r' → OComp.AlikeO R (k r) (k r')) (h : ∀ r, FactorsByR ag R (k r)) :
      FactorsByR ag R (.query o q k)

namespace OComp.FactorsByR
variable {ag : ∀ o, S.Dom o → S.Rng o → S.Rng o → Prop} {R : α → α → Prop} {R' : β → β → Prop}

theorem self {c : OComp S α} (h : FactorsByR ag R c) : AlikeO R c c := by
  induction h with
  | pure h => exact .pure h
  | sample n _ ih => exact .sample n ih
  | query o q _ _ ih => exact .query o q ih

/-- Sequential composition: if c is an algorithm up to R, g takes R-related values to algorithms in
`AlikeO R'` (hs), and g a is an algorithm up to R' at every a with R a a (hg), then `c.bind g` is an
algorithm up to R'. -/
theorem bind {c : OComp S α} {g : α → OComp S β} (hc : FactorsByR ag R c)
    (hs : ∀ a a', R a a' → AlikeO R' (g a) (g a')) (hg : ∀ a, R a a → FactorsByR ag R' (g a)) :
    FactorsByR ag R' (c.bind g) := by
  induction hc with
  | pure h => exact hg _ h
  | sample n _ ih => exact .sample n ih
  | query o q he _ ih => exact .query o q (fun r r' h => (he r r' h).bind hs) ih

theorem toFactorsBy {c : OComp S α} (h : FactorsByR ag Eq c) : c.FactorsBy ag := by
  induction h with
  | pure _ => trivial
  | sample n _ ih => exact ih
  | query o q he _ ih => exact ⟨fun r r' h => (he r r' h).eq, ih⟩

end OComp.FactorsByR

theorem OComp.FactorsBy.toR {ag : ∀ o, S.Dom o → S.Rng o → S.Rng o → Prop} {c : OComp S α} :
    c.FactorsBy ag → c.FactorsByR ag Eq := by
  induction c with
  | pure a => exact fun _ => .pure rfl
  | sample n k ih => exact fun h => .sample n fun r => ih r (h r)
  | query o q k ih =>
    exact fun h => .query o q (fun r r' e => OComp.AlikeO.of_eq (h.1 r r' e)) fun r => ih r (h.2 r)

/-- If c has `FactorsBy` and every g a is an algorithm up to R', so is `c.bind g`. -/
theorem OComp.FactorsByR.bindFac {ag : ∀ o, S.Dom o → S.Rng o → S.Rng o → Prop} {R' : β → β → Prop}
    {c : OComp S α} {g : α → OComp S β} (hc : c.FactorsBy ag) (hg : ∀ a, (g a).FactorsByR ag R') :
    (c.bind g).FactorsByR ag R' :=
  hc.toR.bind (fun a _ h => h ▸ (hg a).self) fun a _ => hg a

end Rom
