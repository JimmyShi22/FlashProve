-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/NeedRel.lean: token programs that carry along more of an answer than they ever use (words of
this library: lean/GLOSSARY.md).

Generic; it complements Part 1 of Compile/NeedBlocks.lean. Token programs (`Rom.Step`,
Rom/Defer.lean) are the form in which committer and prover are written before secret strings are put
in the place of their tokens.

Compile/NeedBlocks.lean, Part 1, has `SFac ag c`: at every query of the program c, two answers that
are related by ag lead to the same continuation program (and at a marked query have the same part
for the store). It is proved part by part (`SFac.bind`), and that asks each part to return the same
value after related answers. A program that stores a whole answer in its state, and later reads only
a part of what it stored, has the property as a whole, but its parts do not: they return different
states. Here the parts are compared up to a relation R on what they return.

  `Alike R c c'`     The programs c and c' are the same tree but for the values at their ends, which
                     are related by R. `Alike.eq`: for R equality the programs are equal.
  `SFacR ag R c`     At every query of c two answers related by ag lead to continuations in the
                     relation `Alike R` (at a marked query they must also have the same part for the
                     store); and every value a that c returns has R a a. (R need not be reflexive: R
                     a a serves as "a is a lawful state".)
  `SFacR.self`       If `SFacR ag R c`, then `Alike R c c`.
  `SFacR.bind`       If `SFacR ag R c`, and g (hs) takes R-related values to programs in `Alike R'`
                     and (hg) has `SFacR ag R' (g a)` at every value a with R a a, then
                     `SFacR ag R' (c.bind g)`.
  `SFac.toR`, `SFacR.toFac`
                     For R equality `SFacR` is `SFac`. Also `SFacR.bindFac`.

Limits: nothing on any scheme. And: for a relation R other than equality, `SFacR ag R c` does not
say that c returns the same after related answers: the program that returns the whole answer has
`SFacR ag (fun _ _ => True)`, for every ag. Only R = equality leads on to the condition of
Rom/OverOneN.lean, by `SFacR.toFac`.
-/
import Compile.NeedBlocks

open Rom Iop

namespace Compile
namespace Need

variable {S : OSpec} {sp : Split S} {α β : Type}

/-- The same program but for the values at its ends, which are related by R. -/
inductive Alike (R : α → α → Prop) : Step S sp α → Step S sp α → Prop
  | pure {a a' : α} (h : R a a') : Alike R (.pure a) (.pure a')
  | sample (m : ℕ) {k k' : Fin (m + 1) → Step S sp α} (h : ∀ r, Alike R (k r) (k' r)) :
      Alike R (.sample m k) (.sample m k')
  | plain (o : S.ι) (q : S.Dom o) {k k' : S.Rng o → Step S sp α} (h : ∀ r, Alike R (k r) (k' r)) :
      Alike R (.plain o q k) (.plain o q k')
  | fresh (ℓ : ℕ) {k k' : Tok → Step S sp α} (h : ∀ t, Alike R (k t) (k' t)) :
      Alike R (.fresh ℓ k) (.fresh ℓ k')
  | marked (o : S.ι) (t : Tok) (us : List Tok) (pt : Bits → List Bits → S.Dom o)
      (inj : ∀ vs, Function.Injective fun v => pt v vs) {k k' : sp.Vis o → Tok → Step S sp α}
      (h : ∀ v t', Alike R (k v t') (k' v t')) :
      Alike R (.marked o t us pt inj k) (.marked o t us pt inj k')
  | reveal (ts : List Tok) {k k' : List Bits → Step S sp α} (h : ∀ w, Alike R (k w) (k' w)) :
      Alike R (.reveal ts k) (.reveal ts k')

namespace Alike
variable {R : α → α → Prop} {R' : β → β → Prop}

theorem bind {c c' : Step S sp α} {g g' : α → Step S sp β} (hc : Alike R c c')
    (hg : ∀ a a', R a a' → Alike R' (g a) (g' a')) :
    Alike R' (c.bind g) (c'.bind g') := by
  induction hc with
  | pure h => exact hg _ _ h
  | sample m _ ih => exact .sample m ih
  | plain o q _ ih => exact .plain o q ih
  | fresh ℓ _ ih => exact .fresh ℓ ih
  | marked o t us pt inj _ ih => exact .marked o t us pt inj ih
  | reveal ts _ ih => exact .reveal ts ih

/-- for equality the two programs are one -/
theorem eq {c c' : Step S sp α} (h : Alike Eq c c') : c = c' := by
  induction h with
  | pure h => exact congrArg Step.pure h
  | sample m _ ih => exact congrArg (Step.sample m) (funext ih)
  | plain o q _ ih => exact congrArg (Step.plain o q) (funext ih)
  | fresh ℓ _ ih => exact congrArg (Step.fresh ℓ) (funext ih)
  | marked o t us pt inj _ ih => exact congrArg (Step.marked o t us pt inj) (funext fun v => funext fun t' => ih v t')
  | reveal ts _ ih => exact congrArg (Step.reveal ts) (funext ih)

theorem refl (hR : ∀ a, R a a) (c : Step S sp α) : Alike R c c := by
  induction c with
  | pure a => exact .pure (hR a)
  | sample m k ih => exact .sample m ih
  | plain o q k ih => exact .plain o q ih
  | fresh ℓ k ih => exact .fresh ℓ ih
  | marked o t us pt inj k ih => exact .marked o t us pt inj ih
  | reveal ts k ih => exact .reveal ts ih

theorem of_eq {c c' : Step S sp α} (h : c = c') : Alike Eq c c' := h ▸ refl (fun _ => rfl) c

theorem mono {R₂ : α → α → Prop} (hR : ∀ a a', R a a' → R₂ a a')
    {c c' : Step S sp α} (h : Alike R c c') : Alike R₂ c c' := by
  induction h with
  | pure h => exact .pure (hR _ _ h)
  | sample m _ ih => exact .sample m ih
  | plain o q _ ih => exact .plain o q ih
  | fresh ℓ _ ih => exact .fresh ℓ ih
  | marked o t us pt inj _ ih => exact .marked o t us pt inj ih
  | reveal ts _ ih => exact .reveal ts ih

end Alike

variable (ag : ∀ o, S.Dom o → S.Rng o → S.Rng o → Prop)

/-- After two answers that are related by ag the program goes on in the same way, up to R at its
ends; and what it returns is related to itself. -/
inductive SFacR (R : α → α → Prop) : Step S sp α → Prop
  | pure {a : α} (h : R a a) : SFacR R (.pure a)
  | sample (m : ℕ) {k : Fin (m + 1) → Step S sp α} (h : ∀ r, SFacR R (k r)) : SFacR R (.sample m k)
  | plain (o : S.ι) (q : S.Dom o) {k : S.Rng o → Step S sp α}
      (he : ∀ r r', ag o q r r' → Alike R (k r) (k r')) (h : ∀ r, SFacR R (k r)) :
      SFacR R (.plain o q k)
  | fresh (ℓ : ℕ) {k : Tok → Step S sp α} (h : ∀ t, SFacR R (k t)) : SFacR R (.fresh ℓ k)
  | marked (o : S.ι) (t : Tok) (us : List Tok) (pt : Bits → List Bits → S.Dom o)
      (inj : ∀ vs, Function.Injective fun v => pt v vs) {k : sp.Vis o → Tok → Step S sp α}
      (he : ∀ v ws r r', ag o (pt v ws) r r' →
        (sp.split o r).2 = (sp.split o r').2 ∧
        ∀ t', Alike R (k (sp.split o r).1 t') (k (sp.split o r').1 t'))
      (h : ∀ v t', SFacR R (k v t')) :
      SFacR R (.marked o t us pt inj k)
  | reveal (ts : List Tok) {k : List Bits → Step S sp α} (h : ∀ w, SFacR R (k w)) :
      SFacR R (.reveal ts k)

variable {ag}

namespace SFacR
variable {R : α → α → Prop} {R' : β → β → Prop}

theorem self {c : Step S sp α} (h : SFacR ag R c) : Alike R c c := by
  induction h with
  | pure h => exact .pure h
  | sample m _ ih => exact .sample m ih
  | plain o q _ _ ih => exact .plain o q ih
  | fresh ℓ _ ih => exact .fresh ℓ ih
  | marked o t us pt inj _ _ ih => exact .marked o t us pt inj ih
  | reveal ts _ ih => exact .reveal ts ih

/-- One part after the other, under `hc`, `hs` and `hg` (see the header). -/
theorem bind {c : Step S sp α} {g : α → Step S sp β} (hc : SFacR ag R c)
    (hs : ∀ a a', R a a' → Alike R' (g a) (g a')) (hg : ∀ a, R a a → SFacR ag R' (g a)) :
    SFacR ag R' (c.bind g) := by
  induction hc with
  | pure h => exact hg _ h
  | sample m _ ih => exact .sample m ih
  | plain o q he _ ih => exact .plain o q (fun r r' h => (he r r' h).bind hs) ih
  | fresh ℓ _ ih => exact .fresh ℓ ih
  | marked o t us pt inj he _ ih =>
    exact .marked o t us pt inj
      (fun v ws r r' h => ⟨(he v ws r r' h).1, fun t' => ((he v ws r r' h).2 t').bind hs⟩) ih
  | reveal ts _ ih => exact .reveal ts ih

theorem toFac {c : Step S sp α} (h : SFacR ag Eq c) : SFac ag c := by
  induction h with
  | pure _ => exact .pure _
  | sample m _ ih => exact .sample m ih
  | plain o q he _ ih => exact .plain o q (fun r r' h => (he r r' h).eq) ih
  | fresh ℓ _ ih => exact .fresh ℓ ih
  | marked o t us pt inj he _ ih =>
    exact .marked o t us pt inj
      (fun v ws r r' h => ⟨(he v ws r r' h).1, funext fun t' => ((he v ws r r' h).2 t').eq⟩) ih
  | reveal ts _ ih => exact .reveal ts ih

end SFacR

theorem SFac.toR {c : Step S sp α} (h : SFac ag c) : SFacR ag Eq c := by
  induction h with
  | pure a => exact .pure rfl
  | sample m _ ih => exact .sample m ih
  | plain o q he _ ih => exact .plain o q (fun r r' h => Alike.of_eq (he r r' h)) ih
  | fresh ℓ _ ih => exact .fresh ℓ ih
  | marked o t us pt inj he _ ih =>
    exact .marked o t us pt inj
      (fun v ws r r' h =>
        ⟨(he v ws r r' h).1, fun t' => Alike.of_eq (congrFun (he v ws r r' h).2 t')⟩) ih
  | reveal ts _ ih => exact .reveal ts ih

/-- a part that returns the same value after related answers, and what follows it -/
theorem SFacR.bindFac {R' : β → β → Prop} {c : Step S sp α} {g : α → Step S sp β}
    (hc : SFac ag c) (hg : ∀ a, SFacR ag R' (g a)) : SFacR ag R' (c.bind g) :=
  hc.toR.bind (fun a _ h => h ▸ (hg a).self) fun a _ => hg a

/-- the same part before two programs that are alike -/
theorem Alike.bindSame {R' : β → β → Prop} (c : Step S sp α)
    {g g' : α → Step S sp β} (hg : ∀ a, Alike R' (g a) (g' a)) :
    Alike R' (c.bind g) (c.bind g') :=
  (Alike.refl (R := Eq) (fun _ => rfl) c).bind fun a _ h => h ▸ hg a

end Need
end Compile
