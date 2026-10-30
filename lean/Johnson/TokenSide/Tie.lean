-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TokenSide/Tie.lean: "ALL COINS FIRST" AGAINST "EACH COIN WHEN IT IS NEEDED", for oracle
algorithms under ANY rule for answering queries. General in the family of oracles. Definitions, and
theorems with their proofs.

General definitions and lemmas. This file states no goal of the release.

Two ways to write one algorithm. On the right a FAMILY g of algorithms in a parameter ω : Ω ("the
coins"), run at an ω that is drawn first, from a law μ. On the left ONE algorithm c that draws each
coin at the place where it is first used. The file gives a relation between the two (Tie) that is
shown rule by rule along the two texts, with no probability, and one theorem (Tie.sound) that turns
it into an equation of laws, under every handler (Rom/Handle/Defs.lean).

  Resamples μ ν upd   (Rom/Handle/Coins.lean) THE LAW THAT IS ASKED OF THE COINS, one coordinate at
                  a time: to draw ω from μ is the same as to draw ω from μ and then to lay a fresh
                  value from ν into one coordinate. It is asked at the coordinates that a run reads,
                  and at no other: Ω may be an infinite type, on which no law makes ALL coordinates
                  uniform and independent.
  Tie μ φ Q c g   c and the family g do the same, step by step:
                    done   c ends with a, Q a holds, and g ω ends with φ a ω;
                    query  both ask the same oracle at the same point (which does not hang on ω),
                           and go on tied at each answer;
                    draw   both make the same draw, and go on tied at each value;
                    coin   c draws r; the family draws nothing; from here on the family is read at
                           upd (e r) ω in the place of ω: the drawn value laid into the coins.
                  After a step "coin" the letter ω stands for the coins BEFORE the drawn value is
                  written in. So φ a ω may still hang on ω, through coordinates that were not drawn.
  Tie.sound       μ.bind (run of g ω) = (run of c).bind (then ω from μ, the output φ a ω).
  Tie.sound_const the same where φ does not hang on ω: the run of c with its output mapped.
  Tie.bind        sequential composition. What follows the family's first part is ONE algorithm in
                  that part's output: a first part hands on whatever of ω is needed later.
  Tie.bindP, Tie.snd    two parts, each with coins of its own: the coins are an independent pair.
  Tie.bindW, Tie.left, Tie.leftP   the same where what follows reads the coins too; a first part
                  without coins; the same with a property of its outputs at hand.
  Tie.mono, Tie.congr, Tie.out, Tie.post   a weaker Q; an equal family; another form of the output;
                  a property of all outputs of c (Post) joins Q.
  Tie.coinsFirst  what it gives in the words of Rom/Handle/Coins.lean (CoinsFirst).
  Tie.obind_assoc sequential composition is associative: the statement of OComp.bind_assoc
                  (Rom/Bridge.lean), which this file does not import, with a proof of its own.

Beside Rom/Handle/Coins.lean: CoinsFirst is the equation of laws itself, for two programs with one
type of outputs. Tie is a relation on the two texts from which that equation follows. It is closed
under a sequential composition in which BOTH parts read the coins, and the two outputs may have
different types (on the left: handles and a store; on the right: values).

Limits. The points of the queries must agree for every ω, not only on μ's support.
Terms: lean/GLOSSARY.md.

-/
import Rom.Handle.Coins
import Prob.Count

set_option autoImplicit false

noncomputable section

namespace Rom
open Prob
variable {S : OSpec} {Ω σ α β α' β' : Type}

/-- **An algorithm that draws each coin when it is needed, and a family of algorithms in the coins,
do the same.** -/
inductive Tie (μ : PMF Ω) (φ : α → Ω → β) (Q : α → Prop) :
    OComp S α → (Ω → OComp S β) → Prop
  | done {a : α} {g : Ω → OComp S β} : Q a → (∀ ω, g ω = .pure (φ a ω)) → Tie μ φ Q (.pure a) g
  | query {o : S.ι} {q : S.Dom o} {k : S.Rng o → OComp S α} {g : Ω → OComp S β}
      (k' : Ω → S.Rng o → OComp S β) : (∀ ω, g ω = .query o q (k' ω)) →
      (∀ r, Tie μ φ Q (k r) fun ω => k' ω r) → Tie μ φ Q (.query o q k) g
  | draw {n : ℕ} {k : Fin (n + 1) → OComp S α} {g : Ω → OComp S β}
      (k' : Ω → Fin (n + 1) → OComp S β) : (∀ ω, g ω = .sample n (k' ω)) →
      (∀ r, Tie μ φ Q (k r) fun ω => k' ω r) → Tie μ φ Q (.sample n k) g
  | coin {n : ℕ} {k : Fin (n + 1) → OComp S α} {g : Ω → OComp S β} {Y : Type} {ν : PMF Y}
      (e : Fin (n + 1) → Y) (upd : Y → Ω → Ω) : (unif (Fin (n + 1))).map e = ν →
      Resamples μ ν upd → (∀ r, Tie μ φ Q (k r) fun ω => g (upd (e r) ω)) →
      Tie μ φ Q (.sample n k) g

/-- every output of c, on every path, has the property P -/
def Post (P : α → Prop) : OComp S α → Prop
  | .pure a => P a
  | .query _ _ k => ∀ r, Post P (k r)
  | .sample _ k => ∀ r, Post P (k r)

theorem Post.bind {P : α → Prop} {P' : α' → Prop} {f : α → OComp S α'} :
    ∀ {c : OComp S α}, Post P c → (∀ a, P a → Post P' (f a)) → Post P' (c.bind f)
  | .pure _, h, hf => hf _ h
  | .query _ _ _, h, hf => fun r => Post.bind (h r) hf
  | .sample _ _, h, hf => fun r => Post.bind (h r) hf

theorem Post.mono {P P' : α → Prop} (hP : ∀ a, P a → P' a) :
    ∀ {c : OComp S α}, Post P c → Post P' c
  | .pure _, h => hP _ h
  | .query _ _ _, h => fun r => Post.mono hP (h r)
  | .sample _ _, h => fun r => Post.mono hP (h r)

theorem Post.of_forall {P : α → Prop} (h : ∀ a, P a) : ∀ c : OComp S α, Post P c
  | .pure a => h a
  | .query _ _ k => fun r => Post.of_forall h (k r)
  | .sample _ k => fun r => Post.of_forall h (k r)

namespace Tie
variable {μ : PMF Ω} {φ : α → Ω → β} {Q : α → Prop}

/-- an equal family -/
theorem congr {c : OComp S α} {g g' : Ω → OComp S β} (h : Tie μ φ Q c g) (e : ∀ ω, g' ω = g ω) :
    Tie μ φ Q c g' := by
  have : g' = g := funext e
  rw [this]
  exact h

theorem mono {Q' : α → Prop} (hQ : ∀ a, Q a → Q' a) {c : OComp S α} {g : Ω → OComp S β}
    (h : Tie μ φ Q c g) : Tie μ φ Q' c g := by
  induction h with
  | done hq e => exact .done (hQ _ hq) e
  | query k' e _ ih => exact .query k' e ih
  | draw k' e _ ih => exact .draw k' e ih
  | coin e upd he hs _ ih => exact .coin e upd he hs ih

/-- a property of all outputs of c joins Q -/
theorem post {P : α → Prop} {c : OComp S α} {g : Ω → OComp S β} (h : Tie μ φ Q c g) :
    Post P c → Tie μ φ (fun a => Q a ∧ P a) c g := by
  induction h with
  | done hq e => exact fun hp => .done ⟨hq, hp⟩ e
  | query k' e _ ih => exact fun hp => .query k' e fun r => ih r (hp r)
  | draw k' e _ ih => exact fun hp => .draw k' e fun r => ih r (hp r)
  | coin e upd he hs _ ih => exact fun hp => .coin e upd he hs fun r => ih r (hp r)

/-- another form of the output, equal where Q holds -/
theorem out {φ' : α → Ω → β} (hφ : ∀ a, Q a → ∀ ω, φ a ω = φ' a ω) {c : OComp S α}
    {g : Ω → OComp S β} (h : Tie μ φ Q c g) : Tie μ φ' Q c g := by
  induction h with
  | done hq e => exact .done hq fun ω => by rw [e ω, hφ _ hq ω]
  | query k' e _ ih => exact .query k' e ih
  | draw k' e _ ih => exact .draw k' e ih
  | coin e upd he hs _ ih => exact .coin e upd he hs ih

/-- **Sequential composition.** -/
theorem bind {φ' : α' → Ω → β'} {Q' : α' → Prop} {c : OComp S α} {g : Ω → OComp S β}
    {f : α → OComp S α'} {f' : β → OComp S β'} (h : Tie μ φ Q c g)
    (hf : ∀ a, Q a → Tie μ φ' Q' (f a) fun ω => f' (φ a ω)) :
    Tie μ φ' Q' (c.bind f) fun ω => (g ω).bind f' := by
  induction h with
  | done hq e => exact (hf _ hq).congr fun ω => by rw [e ω]; rfl
  | query k' e _ ih => exact .query (fun ω r => (k' ω r).bind f') (fun ω => by rw [e ω]; rfl) ih
  | draw k' e _ ih => exact .draw (fun ω r => (k' ω r).bind f') (fun ω => by rw [e ω]; rfl) ih
  | coin e upd he hs _ ih => exact .coin e upd he hs ih

theorem obind_assoc {γ : Type} (c : OComp S α) (g : α → OComp S β) (h : β → OComp S γ) :
    (c.bind g).bind h = c.bind fun a => (g a).bind h := by
  induction c with
  | pure a => rfl
  | sample n k ih => exact congrArg (OComp.sample n) (funext ih)
  | query o q k ih => exact congrArg (OComp.query o q) (funext ih)

/-- Sequential composition where what follows reads the coins too: the first part hands them on
beside its output. -/
theorem bindW {φ : α → Ω → β × Ω} {φ' : α' → Ω → β'} {Q' : α' → Prop} {c : OComp S α}
    {g : Ω → OComp S β} {f : α → OComp S α'} {f' : Ω → β → OComp S β'}
    (h : Tie μ φ Q c fun ω => (g ω).bind fun b => .pure (b, ω))
    (hf : ∀ a, Q a → Tie μ φ' Q' (f a) fun ω => f' (φ a ω).2 (φ a ω).1) :
    Tie μ φ' Q' (c.bind f) fun ω => (g ω).bind (f' ω) :=
  (h.bind (f' := fun x => f' x.2 x.1) hf).congr fun ω => by rw [obind_assoc]; rfl

/-- A first part that is one algorithm on both sides: it reads no coin. -/
theorem left {γ : Type} (c₀ : OComp S γ) {f : γ → OComp S α} {f' : Ω → γ → OComp S β}
    (h : ∀ x, Tie μ φ Q (f x) fun ω => f' ω x) :
    Tie μ φ Q (c₀.bind f) fun ω => c₀.bind (f' ω) := by
  induction c₀ with
  | pure x => exact h x
  | query o q k ih => exact .query (fun ω r => (k r).bind (f' ω)) (fun _ => rfl) ih
  | sample n k ih => exact .draw (fun ω r => (k r).bind (f' ω)) (fun _ => rfl) ih

/-- The same, with a property of all outputs of the first part at hand for what follows. -/
theorem leftP {γ : Type} {P : γ → Prop} {c₀ : OComp S γ} (hp : Post P c₀) {f : γ → OComp S α}
    {f' : Ω → γ → OComp S β} (h : ∀ x, P x → Tie μ φ Q (f x) fun ω => f' ω x) :
    Tie μ φ Q (c₀.bind f) fun ω => c₀.bind (f' ω) := by
  induction c₀ with
  | pure x => exact h x hp
  | query o q k ih =>
    exact .query (fun ω r => (k r).bind (f' ω)) (fun _ => rfl) fun r => ih r (hp r)
  | sample n k ih =>
    exact .draw (fun ω r => (k r).bind (f' ω)) (fun _ => rfl) fun r => ih r (hp r)

/-- The same tie where the coins are the second component of an independent pair. -/
theorem snd {Ω₁ : Type} (μ₁ : PMF Ω₁) {c : OComp S α} {g : Ω → OComp S β} (h : Tie μ φ Q c g) :
    Tie (prod μ₁ μ) (fun a ω => φ a ω.2) Q c fun ω => g ω.2 := by
  induction h with
  | done hq e => exact .done hq fun ω => e ω.2
  | query k' e _ ih => exact .query (fun ω r => k' ω.2 r) (fun ω => e ω.2) ih
  | draw k' e _ ih => exact .draw (fun ω r => k' ω.2 r) (fun ω => e ω.2) ih
  | coin e upd he hs _ ih => exact .coin e (fun y ω => (ω.1, upd y ω.2)) he (hs.snd μ₁) ih

/-- **Sequential composition of two parts, each with coins of its own**: the coins are an
independent pair. The first part's output does not hang on its coins that were not drawn. -/
theorem bindP {Ω₂ : Type} {μ₂ : PMF Ω₂} {ψ : α → β} {φ' : α' → Ω₂ → β'} {Q' : α' → Prop}
    {c : OComp S α} {g : Ω → OComp S β} {f : α → OComp S α'} {f' : Ω₂ → β → OComp S β'}
    (h : Tie μ (fun a _ => ψ a) Q c g)
    (hf : ∀ a, Q a → Tie μ₂ φ' Q' (f a) fun ω₂ => f' ω₂ (ψ a)) :
    Tie (prod μ μ₂) (fun a' ω => φ' a' ω.2) Q' (c.bind f) fun ω => (g ω.1).bind (f' ω.2) := by
  induction h with
  | done hq e => exact ((hf _ hq).snd μ).congr fun ω => by rw [e ω.1]; rfl
  | query k' e _ ih =>
    exact .query (fun ω r => (k' ω.1 r).bind (f' ω.2)) (fun ω => by rw [e ω.1]; rfl) ih
  | draw k' e _ ih =>
    exact .draw (fun ω r => (k' ω.1 r).bind (f' ω.2)) (fun ω => by rw [e ω.1]; rfl) ih
  | coin e upd he hs _ ih => exact .coin e (fun y ω => (upd y ω.1, ω.2)) he (hs.fst μ₂) ih

/-- **From the relation to the laws**, under every handler. -/
theorem sound {c : OComp S α} {g : Ω → OComp S β} (hT : Tie μ φ Q c g) (h : Handler S σ) :
    ∀ s : σ, (μ.bind fun ω => (g ω).interp h s) =
      (c.interp h s).bind fun p => μ.map fun ω => (φ p.1 ω, p.2) := by
  induction hT with
  | @done a g _ e =>
    intro s
    have e1 : (fun ω => (g ω).interp h s) = fun ω => PMF.pure (φ a ω, s) :=
      funext fun ω => by rw [e ω]; rfl
    rw [e1, OComp.interp_pure, PMF.pure_bind]
    rfl
  | @query o q k g k' e _ ih =>
    intro s
    have e1 : (fun ω => (g ω).interp h s) =
        fun ω => (h s o q).bind fun p => (k' ω p.1).interp h p.2 :=
      funext fun ω => by rw [e ω]; rfl
    rw [e1, Prob.bind_comm, OComp.interp_query, PMF.bind_bind]
    exact congrArg _ (funext fun p => ih p.1 p.2)
  | @draw n k g k' e _ ih =>
    intro s
    have e1 : (fun ω => (g ω).interp h s) =
        fun ω => (unif (Fin (n + 1))).bind fun r => (k' ω r).interp h s :=
      funext fun ω => by rw [e ω]; rfl
    rw [e1, Prob.bind_comm, OComp.interp_sample, PMF.bind_bind]
    exact congrArg _ (funext fun r => ih r s)
  | @coin n k g Y ν e upd he hs _ ih =>
    intro s
    rw [hs.bind_eq, ← he, PMF.bind_map, OComp.interp_sample, PMF.bind_bind]
    exact congrArg _ (funext fun r => ih r s)

/-- The same where the output does not hang on the coins that were not drawn. -/
theorem sound_const {ψ : α → β} {c : OComp S α} {g : Ω → OComp S β}
    (hT : Tie μ (fun a _ => ψ a) Q c g) (h : Handler S σ) (s : σ) :
    (μ.bind fun ω => (g ω).interp h s) = (c.interp h s).map fun p => (ψ p.1, p.2) := by
  rw [hT.sound h s]
  refine congrArg _ (funext fun p => ?_)
  exact PMF.map_const _ _

/-- In the words of Rom/Handle/Coins.lean. -/
theorem coinsFirst {ψ : α → β} {c : OComp S α} {g : Ω → OComp S β}
    (hT : Tie μ (fun a _ => ψ a) Q c g) : CoinsFirst μ g (c.bind fun a => .pure (ψ a)) := by
  intro σ h s
  rw [hT.sound_const h s, OComp.interp_bind]
  rfl

end Tie

end Rom

#print axioms Rom.Tie.bind
#print axioms Rom.Tie.bindW
#print axioms Rom.Tie.bindP
#print axioms Rom.Tie.sound
#print axioms Rom.Tie.sound_const
#print axioms Rom.Tie.coinsFirst
