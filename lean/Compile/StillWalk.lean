-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/StillWalk.lean: three small groups of helper definitions and lemmas for
Compile/LiveWalk.lean and Compile/SpecEraseDead.lean (words of this library: lean/GLOSSARY.md).

Generic in the family of oracles and in the relation ag on answers.

  `OComp.StillBy ag c`, `Still ag c`
                       The oracle algorithm c, or the token program c, makes only queries at which
                       ag relates no two answers (a marked query: to an oracle at which it relates
                       none). Such a c depends on its answers only up to ag (`OComp.FactorsBy`),
                       whatever it returns, its store too: `StillBy.fac`, and `Still.erase` (the
                       erasure of a `Still` program has `StillBy`).
  `OAlike.bind`        If two oracle algorithms are the same tree but for related values at their
                       ends (`OAlike`), and at related values they are followed by algorithms that
                       are so, then the two compositions are so.
  `LiveW.eraseSt`      The last step of a proof by the rules of `LiveW` (live tokens, store:
                       Compile/LiveWalk.lean), for a scheme that goes on with the store: the erasure
                       of a `LiveW`, started on a store that holds all its live tokens and followed
                       by a g that gets the store, depends on its answers only up to ag, if
                       (1) g is the same algorithm on two stores that differ at one index d which is
                       not 0, is in the store and is no live token of the value;
                       (2) g depends on its answers only up to ag, on every store that holds the
                       live tokens of the value.
                       (`LiveW.erase` is the case of a g that forgets the store.)
                       `LiveW.eraseStG`: the same where every value has G (`Ends`).

Notation: `ag`: of type `∀ o, S.Dom o → S.Rng o → S.Rng o → Prop`; erasure: `erase`
(Compile/Star.lean): "Forget the rules: tokens are strings, kept in a list; fresh = sample; marked =
query; reveal = read."; the store: that list (`vs`, `st`: a `List Bits`); token, marked query: the
head of Rom/Defer.lean; `LiveW ag T TP c` (Compile/LiveWalk.lean): "LiveWalk, with the live tokens
given as sets: T: those in the arguments of c; TP a: those in its value a."; `d`: a natural number;
`G`: of type `α → Prop`; `Ends G c` (Compile/LiveWalk.lean): "Every value that the program returns
has G, whatever the answers, the coins and the tokens."; `sp`: a `Split S` (Rom/Defer.lean).

Limits: nothing on any program.
-/
import Compile.LiveWalk
import Compile.SeedKit

set_option autoImplicit false

namespace Rom
namespace OComp

variable {S : OSpec} {α β : Type} {ag : ∀ o, S.Dom o → S.Rng o → S.Rng o → Prop}

/-- The algorithm makes only queries at which ag relates no two answers. -/
def StillBy (ag : ∀ o, S.Dom o → S.Rng o → S.Rng o → Prop) : OComp S α → Prop
  | .pure _ => True
  | .sample _ k => ∀ r, StillBy ag (k r)
  | .query o q k => (∀ r r', ¬ ag o q r r') ∧ ∀ r, StillBy ag (k r)

/-- An algorithm with `StillBy ag` has `FactorsBy ag`. -/
theorem StillBy.fac : ∀ {c : OComp S α}, c.StillBy ag → c.FactorsBy ag
  | .pure _, _ => trivial
  | .sample _ k, h => fun r => StillBy.fac (c := k r) (h r)
  | .query _ _ k, h => ⟨fun r r' e => (h.1 r r' e).elim, fun r => StillBy.fac (c := k r) (h.2 r)⟩

theorem StillBy.bind {g : α → OComp S β} :
    ∀ {c : OComp S α}, c.StillBy ag → (∀ a, (g a).StillBy ag) → (c.bind g).StillBy ag
  | .pure a, _, hg => hg a
  | .sample _ k, h, hg => fun r => StillBy.bind (c := k r) (h r) hg
  | .query _ _ k, h, hg => ⟨h.1, fun r => StillBy.bind (c := k r) (h.2 r) hg⟩

theorem StillBy.map {c : OComp S α} (h : c.StillBy ag) (f : α → β) :
    (c.bind fun a => .pure (f a)).StillBy ag :=
  h.bind fun _ => trivial

theorem StillBy.tossN (v : ℕ) :
    ∀ (m : ℕ) (f : (Fin m → Fin (v + 1)) → OComp S α),
      (∀ x, (f x).StillBy ag) → (OComp.tossN v m f).StillBy ag
  | 0, _, h => h _
  | m + 1, f, h => fun r => StillBy.tossN v m (fun x => f (Fin.cons r x)) fun _ => h _

theorem StillBy.blocks (bk : CoinPlan) : ∀ {c : OComp S α}, c.StillBy ag → (c.blocks bk).StillBy ag
  | .pure _, _ => trivial
  | .query _ _ k, h => ⟨h.1, fun r => StillBy.blocks bk (c := k r) (h.2 r)⟩
  | .sample n k, h =>
    StillBy.tossN bk.w (bk.m n) _ fun x => StillBy.blocks bk (c := k (bk.φ n x)) (h _)

theorem StillBy.derive (σ : SeedOracle S) (s : Fin (σ.sd + 1)) (hσ : ∀ q r r', ¬ ag σ.o q r r') :
    ∀ {c : OComp S α}, c.StillBy ag → ∀ j, (c.derive σ s j).StillBy ag
  | .pure _, _, _ => trivial
  | .query _ _ k, h, j => ⟨h.1, fun r => StillBy.derive σ s hσ (c := k r) (h.2 r) j⟩
  | .sample n k, h, j => ⟨hσ _, fun d => StillBy.derive σ s hσ (c := k (σ.ψ n d)) (h _) (j + 1)⟩

end OComp
end Rom

namespace Compile
open Rom

variable {S : OSpec} {sp : Split S} {α β γ : Type} {ag : ∀ o, S.Dom o → S.Rng o → S.Rng o → Prop}

/-- The token program makes only plain queries at which, and marked queries to oracles at which, ag
relates no two answers. -/
def Still (ag : ∀ o, S.Dom o → S.Rng o → S.Rng o → Prop) : Step S sp α → Prop
  | .pure _ => True
  | .sample _ k => ∀ r, Still ag (k r)
  | .plain o q k => (∀ r r', ¬ ag o q r r') ∧ ∀ r, Still ag (k r)
  | .fresh _ k => ∀ t, Still ag (k t)
  | .marked o _ _ _ _ k => (∀ q r r', ¬ ag o q r r') ∧ ∀ v t, Still ag (k v t)
  | .reveal _ k => ∀ w, Still ag (k w)

theorem Still.bind {g : α → Step S sp β} :
    ∀ {c : Step S sp α}, Still ag c → (∀ a, Still ag (g a)) → Still ag (c.bind g)
  | .pure a, _, hg => hg a
  | .sample _ k, h, hg => fun r => Still.bind (c := k r) (h r) hg
  | .plain _ _ k, h, hg => ⟨h.1, fun r => Still.bind (c := k r) (h.2 r) hg⟩
  | .fresh _ k, h, hg => fun t => Still.bind (c := k t) (h t) hg
  | .marked _ _ _ _ _ k, h, hg => ⟨h.1, fun v t => Still.bind (c := k v t) (h.2 v t) hg⟩
  | .reveal _ k, h, hg => fun w => Still.bind (c := k w) (h w) hg

/-- The erasure of a `Still` program has `StillBy`. -/
theorem Still.erase : ∀ {c : Step S sp α}, Still ag c → ∀ vs, (erase c vs).StillBy ag
  | .pure _, _, _ => trivial
  | .sample _ k, h, vs => fun r => Still.erase (c := k r) (h r) vs
  | .plain _ _ k, h, vs => ⟨h.1, fun r => Still.erase (c := k r) (h.2 r) vs⟩
  | .fresh _ k, h, vs => fun _ => Still.erase (c := k vs.length) (h _) _
  | .marked _ _ _ _ _ k, h, vs => ⟨h.1 _, fun _ => Still.erase (c := k _ vs.length) (h.2 _ _) _⟩
  | .reveal _ k, h, vs => Still.erase (c := k _) (h _) vs

/-- Sequential composition, for two algorithms that are the same tree but for their ends. -/
theorem OAlike.bind {R : α → α → Prop} {R' : β → β → Prop} {c c' : OComp S α} {g g' : α → OComp S β}
    (h : OAlike R c c') (hg : ∀ a a', R a a' → OAlike R' (g a) (g' a')) :
    OAlike R' (c.bind g) (c'.bind g') := by
  induction h with
  | pure h => exact hg _ _ h
  | sample n _ ih => exact .sample n ih
  | query o q _ ih => exact .query o q ih

namespace LiveW

variable {T : Tok → Prop} {TP : α → Tok → Prop}

/-- The end, for a g that gets the store (hypotheses below). -/
theorem eraseSt {c : Step S sp α} (h : LiveW ag T TP c) (vs : List Bits)
    (hp : ∀ u, T u → u < vs.length) (g : α × List Bits → OComp S γ)
    (h1 : ∀ d a st st', 0 < d → d < st.length → (∀ u, TP a u → u ≠ d) →
      StoreRel (fun t => t = d) st st' → g (a, st) = g (a, st'))
    (h2 : ∀ a st, (∀ u, TP a u → u < st.length) → (g (a, st)).FactorsBy ag) :
    ((Compile.erase c vs).bind g).FactorsBy ag :=
  facDeadErase S sp α γ ag _ _ c vs g (LiveWalk.fd h 0 vs.length (Nat.zero_le _) hp)
    (fun d a st st' hs x => h1 d a st st' x.1 x.2.2.1 x.2.2.2 hs) fun a st x => h2 a st x.2

/-- `eraseSt` where every value has G. -/
theorem eraseStG {G : α → Prop} {c : Step S sp α} (h : LiveW ag T TP c) (he : Ends G c)
    (vs : List Bits) (hp : ∀ u, T u → u < vs.length) (g : α × List Bits → OComp S γ)
    (h1 : ∀ d a st st', G a → 0 < d → d < st.length → (∀ u, TP a u → u ≠ d) →
      StoreRel (fun t => t = d) st st' → g (a, st) = g (a, st'))
    (h2 : ∀ a st, G a → (∀ u, TP a u → u < st.length) → (g (a, st)).FactorsBy ag) :
    ((Compile.erase c vs).bind g).FactorsBy ag :=
  facDeadErase S sp α γ ag _ _ c vs g
    (LiveWalk.fd (LiveWalk.andEnds h he) 0 vs.length (Nat.zero_le _) hp)
    (fun d a st st' hs x => h1 d a st st' x.2.2.2.1 x.1 x.2.2.1 x.2.2.2.2 hs)
    fun a st x => h2 a st x.2.1 x.2.2

end LiveW

end Compile
