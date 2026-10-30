-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/Skip.lean: two programs of the token language of which the second leaves out work that is never
shown. The relation and its rules; no probability.

A program of the language `Step` of Rom/Defer.lean may do work whose tokens are never revealed: it
samples a secret string, hashes it, hashes the answers again. In mode I of Rom/Defer.lean such work
leaves no trace: a marked evaluation is answered by a fresh uniform value and touches the table only
when it is released. `Skip Q w c₁ c₂` says, by rules on the text of the two programs, that c₂ is c₁
without such work. The two programs then number their tokens differently, so the relation carries a
correspondence w (`Wd`):
    w.ρ t₁ t₂     token t₁ of the first program and token t₂ of the second denote the same string
    w.dd t₁       token t₁ of the first program is dead: the second program has no such token, and
                  the first never reveals it
    w.sl t₁ t₂    t₁ and t₂ denote the same string and are sealed: both programs may put them into
                  points of marked evaluations, neither ever reveals them
    w.n₁, w.n₂    every token that is still to come has a number of at least w.n₁ (first program),
                  w.n₂ (second program)

The rules. Both programs make the same move (pure, sample, plain, fresh, marked, reveal), on tokens
related by ρ, in a marked evaluation also on sealed ones; `markedS` is `marked` with the two tails
sealed from the start; or the first program only
    sampleL   samples coins;
    freshL    samples a token, which is dead;
    markedL   makes a marked evaluation charged to a hidden token (dead or sealed); its tail is
              dead;
or
    markedF   the first program makes a marked evaluation charged to a hidden token, and the second
              samples a fresh token of the length of the tail; the two are related by ρ from now on.
A new token may get any number from w.n₁ (w.n₂) on: so a proof of `Skip` never looks at numbers. A
reveal shows only tokens in ρ, so, under the hypotheses of `TokRel.hid_shown` (Rom/SkipRel.lean), a
hidden token is never shown and an evaluation charged to it is never released. A token is sealed
from the start or never: there is no rule that seals a token of ρ, because nothing in the text of a
program says that it has not been shown already.

Both programs after a translation of token numbers: Compile/SkipVirt.lean. What the relation means
is proved in Rom/SkipRun.lean. Used, among others, in Compile/Batch/SpecSkipU.lean and
CompileK/Defer2Skip.lean.

Notation: (in the words of the head of Rom/Defer.lean)
  marked evaluation, charged: `Step.marked o t us pt inj k`: every marked evaluation is charged to
      one token t, in which its point is injective; it may hold further tokens us
  tail: the answer splits into a visible part, which the program gets, and a tail, which it gets as
      a new token

Limits: by itself the relation says nothing about real runs. Its rules do not test the rules of
Rom/Defer.lean: they relate, for instance, a program that evaluates the same point twice and shows
both tails to a program that samples two fresh strings, which differ in the real experiment with
probability almost 1. The theorem on its meaning (`Skip.run`) is about mode I, where answers do not
depend on points (the answers of marked evaluations); the way back to the real experiment is the
lemma on deferred programming (`Spec.defer`, Rom/Defer.lean), which requires that the runs of the
first program keep the rules and the counts (`DSt.Within`); `StRel.within` (Rom/SkipWithin.lean)
then gives the same for the second.
-/
import Rom.Defer

namespace Rom

/-- how the tokens of two programs correspond -/
structure Wd where
  n₁ : ℕ
  n₂ : ℕ
  ρ : Tok → Tok → Prop
  dd : Tok → Prop
  sl : Tok → Tok → Prop

namespace Wd

/-- the two tokens denote the same string -/
def rel (w : Wd) (a b : Tok) : Prop := w.ρ a b ∨ w.sl a b
/-- the first program never reveals the token (exactly: `w.dd a ∨ ∃ b, w.sl a b`) -/
def hid (w : Wd) (a : Tok) : Prop := w.dd a ∨ ∃ b, w.sl a b

/-- w' knows all that w knows -/
structure le (w w' : Wd) : Prop where
  n₁ : w.n₁ ≤ w'.n₁
  n₂ : w.n₂ ≤ w'.n₂
  ρ : ∀ a b, w.ρ a b → w'.ρ a b
  dd : ∀ a, w.dd a → w'.dd a
  sl : ∀ a b, w.sl a b → w'.sl a b

instance : LE Wd := ⟨le⟩

theorem le_refl (w : Wd) : w ≤ w :=
  ⟨Nat.le_refl _, Nat.le_refl _, fun _ _ h => h, fun _ h => h, fun _ _ h => h⟩
theorem le_trans {w w' w'' : Wd} (h : w ≤ w') (h' : w' ≤ w'') : w ≤ w'' :=
  ⟨Nat.le_trans h.n₁ h'.n₁,
    Nat.le_trans h.n₂ h'.n₂,
    fun a b x => h'.ρ a b (h.ρ a b x),
    fun a x => h'.dd a (h.dd a x),
    fun a b x => h'.sl a b (h.sl a b x)⟩
theorem le.rel {w w' : Wd} (h : w ≤ w') (a b : Tok) (x : w.rel a b) : w'.rel a b :=
  x.imp (h.ρ a b) (h.sl a b)
theorem le.hid {w w' : Wd} (h : w ≤ w') (a : Tok) (x : w.hid a) : w'.hid a :=
  x.imp (h.dd a) fun ⟨b, y⟩ => ⟨b, h.sl a b y⟩

/-- two new tokens that denote the same string -/
def pair (w : Wd) (t₁ t₂ : Tok) : Wd :=
  ⟨t₁ + 1, t₂ + 1, fun a b => w.ρ a b ∨ (a = t₁ ∧ b = t₂), w.dd, w.sl⟩
/-- two new tokens that denote the same string and are sealed -/
def shut (w : Wd) (t₁ t₂ : Tok) : Wd :=
  ⟨t₁ + 1, t₂ + 1, w.ρ, w.dd, fun a b => w.sl a b ∨ (a = t₁ ∧ b = t₂)⟩
/-- a new dead token of the first program -/
def dead (w : Wd) (t₁ : Tok) : Wd := ⟨t₁ + 1, w.n₂, w.ρ, fun a => w.dd a ∨ a = t₁, w.sl⟩

theorem le_pair (w : Wd) {t₁ t₂ : Tok} (h₁ : w.n₁ ≤ t₁) (h₂ : w.n₂ ≤ t₂) : w ≤ w.pair t₁ t₂ :=
  ⟨Nat.le_succ_of_le h₁, Nat.le_succ_of_le h₂, fun _ _ h => Or.inl h, fun _ h => h, fun _ _ h => h⟩
theorem le_shut (w : Wd) {t₁ t₂ : Tok} (h₁ : w.n₁ ≤ t₁) (h₂ : w.n₂ ≤ t₂) : w ≤ w.shut t₁ t₂ :=
  ⟨Nat.le_succ_of_le h₁, Nat.le_succ_of_le h₂, fun _ _ h => h, fun _ h => h, fun _ _ h => Or.inl h⟩
theorem le_dead (w : Wd) {t₁ : Tok} (h₁ : w.n₁ ≤ t₁) : w ≤ w.dead t₁ :=
  ⟨Nat.le_succ_of_le h₁, Nat.le_refl _, fun _ _ h => h, fun _ h => Or.inl h, fun _ _ h => h⟩
theorem pair_ρ (w : Wd) (t₁ t₂ : Tok) : (w.pair t₁ t₂).ρ t₁ t₂ := Or.inr ⟨rfl, rfl⟩
theorem shut_sl (w : Wd) (t₁ t₂ : Tok) : (w.shut t₁ t₂).sl t₁ t₂ := Or.inr ⟨rfl, rfl⟩
theorem dead_dd (w : Wd) (t₁ : Tok) : (w.dead t₁).dd t₁ := Or.inr rfl
theorem pair_mono {w w' : Wd} (h : w ≤ w') (t₁ t₂ : Tok) : w.pair t₁ t₂ ≤ w'.pair t₁ t₂ :=
  ⟨Nat.le_refl _, Nat.le_refl _, fun a b x => x.imp (h.ρ a b) id, h.dd, h.sl⟩
theorem shut_mono {w w' : Wd} (h : w ≤ w') (t₁ t₂ : Tok) : w.shut t₁ t₂ ≤ w'.shut t₁ t₂ :=
  ⟨Nat.le_refl _, Nat.le_refl _, h.ρ, h.dd, fun a b x => x.imp (h.sl a b) id⟩
theorem dead_mono {w w' : Wd} (h : w ≤ w') (t₁ : Tok) : w.dead t₁ ≤ w'.dead t₁ :=
  ⟨Nat.le_refl _, h.n₂, h.ρ, fun a x => x.imp (h.dd a) id, h.sl⟩

end Wd

variable {S : OSpec} {sp : Split S}

/-- The second program is the first without work that is never shown. Q: what holds of the two
results, with the correspondence at the end. -/
inductive Skip {α₁ α₂ : Type} (Q : Wd → α₁ → α₂ → Prop) : Wd → Step S sp α₁ → Step S sp α₂ → Prop
  | pure {w : Wd} {a₁ : α₁} {a₂ : α₂} (h : Q w a₁ a₂) : Skip Q w (.pure a₁) (.pure a₂)
  | sample {w : Wd} (n : ℕ) {k₁ : Fin (n + 1) → Step S sp α₁}
      {k₂ : Fin (n + 1) → Step S sp α₂} (h : ∀ r, Skip Q w (k₁ r) (k₂ r)) :
      Skip Q w (.sample n k₁) (.sample n k₂)
  | plain {w : Wd} (o : S.ι) (q : S.Dom o) {k₁ : S.Rng o → Step S sp α₁}
      {k₂ : S.Rng o → Step S sp α₂} (h : ∀ r, Skip Q w (k₁ r) (k₂ r)) :
      Skip Q w (.plain o q k₁) (.plain o q k₂)
  | fresh {w : Wd} (ℓ : ℕ) {k₁ : Tok → Step S sp α₁} {k₂ : Tok → Step S sp α₂}
      (h : ∀ t₁ t₂, w.n₁ ≤ t₁ → w.n₂ ≤ t₂ → Skip Q (w.pair t₁ t₂) (k₁ t₁) (k₂ t₂)) :
      Skip Q w (.fresh ℓ k₁) (.fresh ℓ k₂)
  | marked {w : Wd} (o : S.ι) {t₁ t₂ : Tok} {us₁ us₂ : List Tok} (pt : Bits → List Bits → S.Dom o)
      (inj : ∀ vs, Function.Injective fun v => pt v vs) {k₁ : sp.Vis o → Tok → Step S sp α₁}
      {k₂ : sp.Vis o → Tok → Step S sp α₂} (ht : w.rel t₁ t₂) (hus : List.Forall₂ w.rel us₁ us₂)
      (h : ∀ v t₁' t₂', w.n₁ ≤ t₁' → w.n₂ ≤ t₂' → Skip Q (w.pair t₁' t₂') (k₁ v t₁') (k₂ v t₂')) :
      Skip Q w (.marked o t₁ us₁ pt inj k₁) (.marked o t₂ us₂ pt inj k₂)
  | markedS {w : Wd} (o : S.ι) {t₁ t₂ : Tok} {us₁ us₂ : List Tok} (pt : Bits → List Bits → S.Dom o)
      (inj : ∀ vs, Function.Injective fun v => pt v vs) {k₁ : sp.Vis o → Tok → Step S sp α₁}
      {k₂ : sp.Vis o → Tok → Step S sp α₂} (ht : w.rel t₁ t₂) (hus : List.Forall₂ w.rel us₁ us₂)
      (h : ∀ v t₁' t₂', w.n₁ ≤ t₁' → w.n₂ ≤ t₂' → Skip Q (w.shut t₁' t₂') (k₁ v t₁') (k₂ v t₂')) :
      Skip Q w (.marked o t₁ us₁ pt inj k₁) (.marked o t₂ us₂ pt inj k₂)
  | reveal {w : Wd} {ts₁ ts₂ : List Tok} {k₁ : List Bits → Step S sp α₁}
      {k₂ : List Bits → Step S sp α₂} (hts : List.Forall₂ w.ρ ts₁ ts₂)
      (h : ∀ vs, Skip Q w (k₁ vs) (k₂ vs)) :
      Skip Q w (.reveal ts₁ k₁) (.reveal ts₂ k₂)
  | sampleL {w : Wd} (n : ℕ) {k₁ : Fin (n + 1) → Step S sp α₁}
      {c₂ : Step S sp α₂} (h : ∀ r, Skip Q w (k₁ r) c₂) : Skip Q w (.sample n k₁) c₂
  | freshL {w : Wd} (ℓ : ℕ) {k₁ : Tok → Step S sp α₁} {c₂ : Step S sp α₂}
      (h : ∀ t₁, w.n₁ ≤ t₁ → Skip Q (w.dead t₁) (k₁ t₁) c₂) : Skip Q w (.fresh ℓ k₁) c₂
  | markedL {w : Wd} (o : S.ι) {t₁ : Tok} (us₁ : List Tok) (pt : Bits → List Bits → S.Dom o)
      (inj : ∀ vs, Function.Injective fun v => pt v vs) {k₁ : sp.Vis o → Tok → Step S sp α₁}
      {c₂ : Step S sp α₂} (ht : w.hid t₁)
      (h : ∀ v t₁', w.n₁ ≤ t₁' → Skip Q (w.dead t₁') (k₁ v t₁') c₂) :
      Skip Q w (.marked o t₁ us₁ pt inj k₁) c₂
  | markedF {w : Wd} (o : S.ι) {t₁ : Tok} (us₁ : List Tok) (pt : Bits → List Bits → S.Dom o)
      (inj : ∀ vs, Function.Injective fun v => pt v vs) {k₁ : sp.Vis o → Tok → Step S sp α₁}
      {k₂ : Tok → Step S sp α₂} (ht : w.hid t₁)
      (h : ∀ v t₁' t₂', w.n₁ ≤ t₁' → w.n₂ ≤ t₂' → Skip Q (w.pair t₁' t₂') (k₁ v t₁') (k₂ t₂')) :
      Skip Q w (.marked o t₁ us₁ pt inj k₁) (.fresh (sp.tl o) k₂)

namespace Skip

variable {α₁ α₂ β₁ β₂ : Type}

theorem forall₂_mono {w w' : Wd} (h : w ≤ w') {l₁ l₂ : List Tok} (hl : List.Forall₂ w.ρ l₁ l₂) :
    List.Forall₂ w'.ρ l₁ l₂ :=
  hl.imp fun a b x => h.ρ a b x

theorem forall₂_rel_mono {w w' : Wd} (h : w ≤ w')
    {l₁ l₂ : List Tok} (hl : List.Forall₂ w.rel l₁ l₂) : List.Forall₂ w'.rel l₁ l₂ :=
  hl.imp fun a b x => h.rel a b x

theorem forall₂_rel {w : Wd} {l₁ l₂ : List Tok} (hl : List.Forall₂ w.ρ l₁ l₂) :
    List.Forall₂ w.rel l₁ l₂ :=
  hl.imp fun _ _ x => Or.inl x

/-- A larger correspondence, a weaker conclusion. -/
theorem mono {Q Q' : Wd → α₁ → α₂ → Prop} {w : Wd} {c₁ : Step S sp α₁}
    {c₂ : Step S sp α₂} (h : Skip Q w c₁ c₂) :
    ∀ {w' : Wd}, w ≤ w' → (∀ v v' a₁ a₂, v ≤ v' → Q v a₁ a₂ → Q' v' a₁ a₂) → Skip Q' w' c₁ c₂ := by
  induction h with
  | pure h => intro w' hw hQ; exact .pure (hQ _ _ _ _ hw h)
  | sample n _ ih => intro w' hw hQ; exact .sample n fun r => ih r hw hQ
  | plain o q _ ih => intro w' hw hQ; exact .plain o q fun r => ih r hw hQ
  | fresh ℓ _ ih => intro w' hw hQ; exact .fresh ℓ fun t₁ t₂ h₁ h₂ => ih t₁ t₂ (hw.n₁.trans h₁) (hw.n₂.trans h₂) (Wd.pair_mono hw _ _) hQ
  | marked o pt inj ht hus _ ih =>
    intro w' hw hQ
    exact .marked o pt inj (hw.rel _ _ ht) (forall₂_rel_mono hw hus)
      fun v t₁ t₂ h₁ h₂ => ih v t₁ t₂ (hw.n₁.trans h₁) (hw.n₂.trans h₂) (Wd.pair_mono hw _ _) hQ
  | markedS o pt inj ht hus _ ih =>
    intro w' hw hQ
    exact .markedS o pt inj (hw.rel _ _ ht) (forall₂_rel_mono hw hus)
      fun v t₁ t₂ h₁ h₂ => ih v t₁ t₂ (hw.n₁.trans h₁) (hw.n₂.trans h₂) (Wd.shut_mono hw _ _) hQ
  | reveal hts _ ih => intro w' hw hQ; exact .reveal (forall₂_mono hw hts) fun vs => ih vs hw hQ
  | sampleL n _ ih => intro w' hw hQ; exact .sampleL n fun r => ih r hw hQ
  | freshL ℓ _ ih => intro w' hw hQ; exact .freshL ℓ fun t₁ h₁ => ih t₁ (hw.n₁.trans h₁) (Wd.dead_mono hw _) hQ
  | markedL o us₁ pt inj ht _ ih =>
    intro w' hw hQ
    exact .markedL o us₁ pt inj (hw.hid _ ht) fun v t₁ h₁ =>
      ih v t₁ (hw.n₁.trans h₁) (Wd.dead_mono hw _) hQ
  | markedF o us₁ pt inj ht _ ih =>
    intro w' hw hQ
    exact .markedF o us₁ pt inj (hw.hid _ ht) fun v t₁ t₂ h₁ h₂ =>
      ih v t₁ t₂ (hw.n₁.trans h₁) (hw.n₂.trans h₂) (Wd.pair_mono hw _ _) hQ

/-- a weaker conclusion -/
theorem imp {Q Q' : Wd → α₁ → α₂ → Prop} {w : Wd} {c₁ : Step S sp α₁} {c₂ : Step S sp α₂}
    (h : Skip Q w c₁ c₂) (hQ : ∀ v a₁ a₂, Q v a₁ a₂ → Q' v a₁ a₂) : Skip Q' w c₁ c₂ := by
  induction h with
  | pure h => exact .pure (hQ _ _ _ h)
  | sample n _ ih => exact .sample n ih
  | plain o q _ ih => exact .plain o q ih
  | fresh ℓ _ ih => exact .fresh ℓ ih
  | marked o pt inj ht hus _ ih => exact .marked o pt inj ht hus ih
  | markedS o pt inj ht hus _ ih => exact .markedS o pt inj ht hus ih
  | reveal hts _ ih => exact .reveal hts ih
  | sampleL n _ ih => exact .sampleL n ih
  | freshL ℓ _ ih => exact .freshL ℓ ih
  | markedL o us₁ pt inj ht _ ih => exact .markedL o us₁ pt inj ht ih
  | markedF o us₁ pt inj ht _ ih => exact .markedF o us₁ pt inj ht ih

/-- Under the hypotheses below, the correspondence only grows. -/
theorem keep {Q : Wd → α₁ → α₂ → Prop} {w : Wd} {c₁ : Step S sp α₁}
    {c₂ : Step S sp α₂} (h : Skip Q w c₁ c₂) :
    ∀ {w₀ : Wd}, w₀ ≤ w → Skip (fun v a₁ a₂ => w₀ ≤ v ∧ Q v a₁ a₂) w c₁ c₂ := by
  induction h with
  | pure h => intro w₀ hw; exact .pure ⟨hw, h⟩
  | sample n _ ih => intro w₀ hw; exact .sample n fun r => ih r hw
  | plain o q _ ih => intro w₀ hw; exact .plain o q fun r => ih r hw
  | fresh ℓ _ ih => intro w₀ hw; exact .fresh ℓ fun t₁ t₂ h₁ h₂ => ih t₁ t₂ h₁ h₂ (Wd.le_trans hw (Wd.le_pair _ h₁ h₂))
  | marked o pt inj ht hus _ ih =>
    intro w₀ hw; exact .marked o pt inj ht hus fun v t₁ t₂ h₁ h₂ => ih v t₁ t₂ h₁ h₂ (Wd.le_trans hw (Wd.le_pair _ h₁ h₂))
  | markedS o pt inj ht hus _ ih =>
    intro w₀ hw; exact .markedS o pt inj ht hus fun v t₁ t₂ h₁ h₂ => ih v t₁ t₂ h₁ h₂ (Wd.le_trans hw (Wd.le_shut _ h₁ h₂))
  | reveal hts _ ih => intro w₀ hw; exact .reveal hts fun vs => ih vs hw
  | sampleL n _ ih => intro w₀ hw; exact .sampleL n fun r => ih r hw
  | freshL ℓ _ ih =>
    intro w₀ hw; exact .freshL ℓ fun t₁ h₁ => ih t₁ h₁ (Wd.le_trans hw (Wd.le_dead _ h₁))
  | markedL o us₁ pt inj ht _ ih => intro w₀ hw; exact .markedL o us₁ pt inj ht fun v t₁ h₁ => ih v t₁ h₁ (Wd.le_trans hw (Wd.le_dead _ h₁))
  | markedF o us₁ pt inj ht _ ih =>
    intro w₀ hw; exact .markedF o us₁ pt inj ht fun v t₁ t₂ h₁ h₂ => ih v t₁ t₂ h₁ h₂ (Wd.le_trans hw (Wd.le_pair _ h₁ h₂))

/-- Sequential composition. -/
theorem bind {Q : Wd → α₁ → α₂ → Prop} {Q' : Wd → β₁ → β₂ → Prop} {w : Wd} {c₁ : Step S sp α₁}
    {c₂ : Step S sp α₂} {g₁ : α₁ → Step S sp β₁} {g₂ : α₂ → Step S sp β₂} (h : Skip Q w c₁ c₂)
    (hg : ∀ v a₁ a₂, Q v a₁ a₂ → Skip Q' v (g₁ a₁) (g₂ a₂)) :
    Skip Q' w (c₁.bind g₁) (c₂.bind g₂) := by
  induction h with
  | pure h => exact hg _ _ _ h
  | sample n _ ih => exact .sample n ih
  | plain o q _ ih => exact .plain o q ih
  | fresh ℓ _ ih => exact .fresh ℓ ih
  | marked o pt inj ht hus _ ih => exact .marked o pt inj ht hus ih
  | markedS o pt inj ht hus _ ih => exact .markedS o pt inj ht hus ih
  | reveal hts _ ih => exact .reveal hts ih
  | sampleL n _ ih => exact .sampleL n ih
  | freshL ℓ _ ih => exact .freshL ℓ ih
  | markedL o us₁ pt inj ht _ ih => exact .markedL o us₁ pt inj ht ih
  | markedF o us₁ pt inj ht _ ih => exact .markedF o us₁ pt inj ht ih

/-- sequential composition, with the fact that the correspondence has grown -/
theorem bind' {Q : Wd → α₁ → α₂ → Prop} {Q' : Wd → β₁ → β₂ → Prop} {w : Wd} {c₁ : Step S sp α₁}
    {c₂ : Step S sp α₂} {g₁ : α₁ → Step S sp β₁} {g₂ : α₂ → Step S sp β₂} (h : Skip Q w c₁ c₂)
    (hg : ∀ v a₁ a₂, w ≤ v → Q v a₁ a₂ → Skip Q' v (g₁ a₁) (g₂ a₂)) :
    Skip Q' w (c₁.bind g₁) (c₂.bind g₂) :=
  (h.keep (Wd.le_refl w)).bind fun v a₁ a₂ hv => hg v a₁ a₂ hv.1 hv.2

/-- the first program alone does something, then both go on: c₂ = pure () >>= _ -/
theorem bindL {Q : Wd → α₁ → Unit → Prop} {Q' : Wd → β₁ → β₂ → Prop} {w : Wd} {c₁ : Step S sp α₁}
    {g₁ : α₁ → Step S sp β₁} {c₂ : Step S sp β₂} (h : Skip Q w c₁ (.pure ()))
    (hg : ∀ v a₁, w ≤ v → Q v a₁ () → Skip Q' v (g₁ a₁) c₂) : Skip Q' w (c₁.bind g₁) c₂ :=
  bind' (c₂ := Step.pure ()) (g₂ := fun _ => c₂) h fun v a₁ _ hv hq => hg v a₁ hv hq

/-! ### The rules, as a traversal of a program uses them: no numbers -/

theorem fresh' {Q : Wd → α₁ → α₂ → Prop} {w : Wd} (ℓ : ℕ) {k₁ : Tok → Step S sp α₁}
    {k₂ : Tok → Step S sp α₂} (h : ∀ v t₁ t₂, w ≤ v → v.ρ t₁ t₂ → Skip Q v (k₁ t₁) (k₂ t₂)) :
    Skip Q w (.fresh ℓ k₁) (.fresh ℓ k₂) :=
  .fresh ℓ fun t₁ t₂ h₁ h₂ => h _ t₁ t₂ (Wd.le_pair w h₁ h₂) (Wd.pair_ρ w t₁ t₂)

theorem marked' {Q : Wd → α₁ → α₂ → Prop} {w : Wd} (o : S.ι) {t₁ t₂ : Tok} {us₁ us₂ : List Tok}
    (pt : Bits → List Bits → S.Dom o) (inj : ∀ vs, Function.Injective fun v => pt v vs)
    {k₁ : sp.Vis o → Tok → Step S sp α₁} {k₂ : sp.Vis o → Tok → Step S sp α₂} (ht : w.ρ t₁ t₂)
    (hus : List.Forall₂ w.ρ us₁ us₂)
    (h : ∀ x v t₁' t₂', w ≤ v → v.ρ t₁' t₂' → Skip Q v (k₁ x t₁') (k₂ x t₂')) :
    Skip Q w (.marked o t₁ us₁ pt inj k₁) (.marked o t₂ us₂ pt inj k₂) :=
  .marked o pt inj (Or.inl ht) (forall₂_rel hus) fun x t₁' t₂' h₁ h₂ =>
    h x _ t₁' t₂' (Wd.le_pair w h₁ h₂) (Wd.pair_ρ w t₁' t₂')

/-- a marked evaluation of both programs, on tokens that may be sealed -/
theorem markedR' {Q : Wd → α₁ → α₂ → Prop} {w : Wd} (o : S.ι) {t₁ t₂ : Tok} {us₁ us₂ : List Tok}
    (pt : Bits → List Bits → S.Dom o) (inj : ∀ vs, Function.Injective fun v => pt v vs)
    {k₁ : sp.Vis o → Tok → Step S sp α₁} {k₂ : sp.Vis o → Tok → Step S sp α₂} (ht : w.rel t₁ t₂)
    (hus : List.Forall₂ w.rel us₁ us₂)
    (h : ∀ x v t₁' t₂', w ≤ v → v.ρ t₁' t₂' → Skip Q v (k₁ x t₁') (k₂ x t₂')) :
    Skip Q w (.marked o t₁ us₁ pt inj k₁) (.marked o t₂ us₂ pt inj k₂) :=
  .marked o pt inj ht hus fun x t₁' t₂' h₁ h₂ =>
    h x _ t₁' t₂' (Wd.le_pair w h₁ h₂) (Wd.pair_ρ w t₁' t₂')

/-- a marked evaluation of both programs whose tails are sealed from the start -/
theorem markedS' {Q : Wd → α₁ → α₂ → Prop} {w : Wd} (o : S.ι) {t₁ t₂ : Tok} {us₁ us₂ : List Tok}
    (pt : Bits → List Bits → S.Dom o) (inj : ∀ vs, Function.Injective fun v => pt v vs)
    {k₁ : sp.Vis o → Tok → Step S sp α₁} {k₂ : sp.Vis o → Tok → Step S sp α₂} (ht : w.rel t₁ t₂)
    (hus : List.Forall₂ w.rel us₁ us₂)
    (h : ∀ x v t₁' t₂', w ≤ v → v.sl t₁' t₂' → Skip Q v (k₁ x t₁') (k₂ x t₂')) :
    Skip Q w (.marked o t₁ us₁ pt inj k₁) (.marked o t₂ us₂ pt inj k₂) :=
  .markedS o pt inj ht hus fun x t₁' t₂' h₁ h₂ =>
    h x _ t₁' t₂' (Wd.le_shut w h₁ h₂) (Wd.shut_sl w t₁' t₂')

theorem freshL' {Q : Wd → α₁ → α₂ → Prop} {w : Wd} (ℓ : ℕ) {k₁ : Tok → Step S sp α₁}
    {c₂ : Step S sp α₂} (h : ∀ v t₁, w ≤ v → v.dd t₁ → Skip Q v (k₁ t₁) c₂) :
    Skip Q w (.fresh ℓ k₁) c₂ :=
  .freshL ℓ fun t₁ h₁ => h _ t₁ (Wd.le_dead w h₁) (Wd.dead_dd w t₁)

theorem markedL' {Q : Wd → α₁ → α₂ → Prop} {w : Wd} (o : S.ι) {t₁ : Tok} (us₁ : List Tok)
    (pt : Bits → List Bits → S.Dom o) (inj : ∀ vs, Function.Injective fun v => pt v vs)
    {k₁ : sp.Vis o → Tok → Step S sp α₁} {c₂ : Step S sp α₂} (ht : w.dd t₁)
    (h : ∀ x v t₁', w ≤ v → v.dd t₁' → Skip Q v (k₁ x t₁') c₂) :
    Skip Q w (.marked o t₁ us₁ pt inj k₁) c₂ :=
  .markedL o us₁ pt inj (Or.inl ht) fun x t₁' h₁ => h x _ t₁' (Wd.le_dead w h₁) (Wd.dead_dd w t₁')

theorem markedF' {Q : Wd → α₁ → α₂ → Prop} {w : Wd} (o : S.ι) {t₁ : Tok} (us₁ : List Tok)
    (pt : Bits → List Bits → S.Dom o) (inj : ∀ vs, Function.Injective fun v => pt v vs)
    {k₁ : sp.Vis o → Tok → Step S sp α₁} {k₂ : Tok → Step S sp α₂} (ht : w.dd t₁)
    (h : ∀ x v t₁' t₂', w ≤ v → v.ρ t₁' t₂' → Skip Q v (k₁ x t₁') (k₂ t₂')) :
    Skip Q w (.marked o t₁ us₁ pt inj k₁) (.fresh (sp.tl o) k₂) :=
  .markedF o us₁ pt inj (Or.inl ht) fun x t₁' t₂' h₁ h₂ =>
    h x _ t₁' t₂' (Wd.le_pair w h₁ h₂) (Wd.pair_ρ w t₁' t₂')

/-- markedF for a hidden token (dead or sealed) -/
theorem markedFH' {Q : Wd → α₁ → α₂ → Prop} {w : Wd} (o : S.ι) {t₁ : Tok} (us₁ : List Tok)
    (pt : Bits → List Bits → S.Dom o) (inj : ∀ vs, Function.Injective fun v => pt v vs)
    {k₁ : sp.Vis o → Tok → Step S sp α₁} {k₂ : Tok → Step S sp α₂} (ht : w.hid t₁)
    (h : ∀ x v t₁' t₂', w ≤ v → v.ρ t₁' t₂' → Skip Q v (k₁ x t₁') (k₂ t₂')) :
    Skip Q w (.marked o t₁ us₁ pt inj k₁) (.fresh (sp.tl o) k₂) :=
  .markedF o us₁ pt inj ht fun x t₁' t₂' h₁ h₂ =>
    h x _ t₁' t₂' (Wd.le_pair w h₁ h₂) (Wd.pair_ρ w t₁' t₂')

end Skip

end Rom
