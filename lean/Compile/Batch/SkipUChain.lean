-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/SkipUChain.lean: the rounds and the Fiat-Shamir chains of the two provers, in the
relation `Rom.Skip`. Second part of the proof of `Spec.skipPp` (Compile/Batch/SpecSkipU.lean).
(Words of this library: lean/GLOSSARY.md.)

The first program is `chainT` of Compile/Batch/Prover.lean (an empty slot of a batch is hashed like
a full one), the second is `chainTU` of Compile/Batch/ProverU.lean (no query and no tree for an
empty slot). w : `Wd` (Rom/Skip.lean) says which tokens of the two programs correspond and which
tokens of the first are dead (without a counterpart). (The fields `dead` of `FullR` and `RA0` are
about something else: `SlotAcc.dead`, `Acc0.dead` (Compile/Batch/Prover.lean).)

`RS` (and `RAcc` at the end of the chains) says when two slots correspond under w. A full slot: the
same request and strategy on both sides, equal hash blocks, corresponding tokens and trees. An empty
slot: both are empty; nothing else is asked of the second program's slot; of the first program's
slot, for `RS`, that the token to which its next query is charged is dead: its chain token, and in
the phase `shr` its slot value. `RA0`, `RPh`: shared parts, phases. The rounds of the two chains are
written out in Compile/Batch/ChainUnfold.lean.

Notation:
  `Skip Q w c₁ c₂`: a proposition on two programs (`Step`, Rom/Defer.lean), "by rules on the text of
    the two programs" (the head of Rom/Skip.lean); Q: "what holds of the two results, with the
    correspondence at the end".
  in Part 2 (one query), names that begin sk_, skL_: the lemma on a program "made by both programs";
    "made by the first program alone (an empty slot)" (the doc comments of `sk_fbG`, `skL_fbG`).
  `fbT`: "a Fiat-Shamir query: charged to tk; its other tokens are us and then the root, if the
    component has a tree" (the root: rt here).
  `fbTw`: "fbT under the ghost name fbw t j (Compile/Batch/Oracles.lean): the same input, the same
    charge".
  `fbW`: "The attempts after the first"; dd: "the chaining values of the attempts that have failed
    so far, the newest first".
  `fbG`: "A Fiat-Shamir query, with a proof-of-work record or without."
  `fbSlotG`: "the Fiat-Shamir query of a slot in a local round" (`fbSlot`), "with a proof-of-work
    record or without".
  `gT`: "the query to g in the joining round: its answer is the slot value".
  `k₁`, `k₂`: what the two programs do next, as functions of the answer: at `fbT`, `fbTw`, `fbSlot`
    of bl : `Blk lam K`, tl : `Tok`, "the blocks and the chaining value" (`fbW`).
  (The programs `fbT` to `gT`: Compile/Batch/Prover.lean, in their doc comments' words.)

Limits: nothing is said about probability and nothing about runs: these are statements about
programs as terms.
-/
import Compile.Batch.SkipUTree
import Compile.Batch.ChainUnfold

noncomputable section

namespace Compile.Batch.SkipU
open Iop Rom

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} {Y : Type}

/-! ## Part 1. Corresponding slots, shared parts, phases -/

theorem f2_map {α β α' β' : Type} {R : α → β → Prop} {R' : α' → β' → Prop} {f : α → α'}
    {g : β → β'} (h : ∀ a b, R a b → R' (f a) (g b)) :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → List.Forall₂ R' (l₁.map f) (l₂.map g)
  | _, _, .nil => .nil
  | _, _, .cons x t => .cons (h _ _ x) (f2_map h t)

/-- what two full slots have gathered corresponds -/
structure FullR (w : Wd) (a₁ a₂ : SlotAcc lam K Y) : Prop where
  tk : w.ρ a₁.tk a₂.tk
  c : w.ρ a₁.c a₂.c
  blocks : a₁.blocks = a₂.blocks
  trees : List.Forall₂ (ROT w) a₁.trees a₂.trees
  toks : RL w a₁.toks a₂.toks
  nons : a₁.nons = a₂.nons
  dead : RL w a₁.dead a₂.dead

theorem FullR.mono {w v : Wd} (h : w ≤ v) {a₁ a₂ : SlotAcc lam K Y} (x : FullR w a₁ a₂) :
    FullR v a₁ a₂ :=
  ⟨h.ρ _ _ x.tk, h.ρ _ _ x.c, x.blocks, ROTs.mono h x.trees, RL.mono h x.toks,
    x.nons, RL.mono h x.dead⟩

/-- two slots correspond while the chains run; J: the next query of a local round is charged to
the slot value -/
inductive RS (w : Wd) (J : Prop) {s : Shape} : SlotSt lam K Y s → SlotSt lam K Y s → Prop
  | full {st : Strat s Unit} {a₁ a₂ : SlotAcc lam K Y} (y : Y) (h₁ : a₁.x = some y)
      (h₂ : a₂.x = some y) (h : FullR w a₁ a₂) : RS w J (st, a₁) (st, a₂)
  | empty {st₁ st₂ : Strat s Unit} {a₁ a₂ : SlotAcc lam K Y} (h₁ : a₁.x = none) (h₂ : a₂.x = none)
      (htk : w.dd a₁.tk) (hc : J → w.dd a₁.c) : RS w J (st₁, a₁) (st₂, a₂)

theorem RS.mono {w v : Wd} (h : w ≤ v) {J : Prop} {s : Shape}
    {z₁ z₂ : SlotSt lam K Y s} (x : RS w J z₁ z₂) : RS v J z₁ z₂ := by
  cases x with
  | full y h₁ h₂ hf => exact .full y h₁ h₂ (hf.mono h)
  | empty h₁ h₂ htk hc => exact .empty h₁ h₂ (h.dd _ htk) fun j => h.dd _ (hc j)

theorem RS.weak {w : Wd} {J J' : Prop} (hJ : J' → J) {s : Shape}
    {z₁ z₂ : SlotSt lam K Y s} (x : RS w J z₁ z₂) : RS w J' z₁ z₂ := by
  cases x with
  | full y h₁ h₂ hf => exact .full y h₁ h₂ hf
  | empty h₁ h₂ htk hc => exact .empty h₁ h₂ htk fun j => hc (hJ j)

theorem RSs.mono {w v : Wd} (h : w ≤ v) {J : Prop} {s : Shape}
    {l₁ l₂ : List (SlotSt lam K Y s)} (x : List.Forall₂ (RS w J) l₁ l₂) :
    List.Forall₂ (RS v J) l₁ l₂ :=
  x.imp fun _ _ y => y.mono h

/-- two slots correspond at the end of the chains -/
inductive RAcc (w : Wd) : SlotAcc lam K Y → SlotAcc lam K Y → Prop
  | full {a₁ a₂ : SlotAcc lam K Y}
      (y : Y) (h₁ : a₁.x = some y) (h₂ : a₂.x = some y) (h : FullR w a₁ a₂) : RAcc w a₁ a₂
  | empty {a₁ a₂ : SlotAcc lam K Y} (h₁ : a₁.x = none) (h₂ : a₂.x = none) : RAcc w a₁ a₂

theorem RAcc.mono {w v : Wd} (h : w ≤ v) {a₁ a₂ : SlotAcc lam K Y} (x : RAcc w a₁ a₂) :
    RAcc v a₁ a₂ := by
  cases x with
  | full y h₁ h₂ hf => exact .full y h₁ h₂ (hf.mono h)
  | empty h₁ h₂ => exact .empty h₁ h₂

theorem RS.acc {w : Wd} {J : Prop} {s : Shape} {z₁ z₂ : SlotSt lam K Y s} (x : RS w J z₁ z₂) :
    RAcc w z₁.2 z₂.2 := by
  cases x with
  | full y h₁ h₂ hf => exact .full y h₁ h₂ hf
  | empty h₁ h₂ _ _ => exact .empty h₁ h₂

/-- what the two shared parts have gathered corresponds -/
structure RA0 (w : Wd) (a b : Acc0) : Prop where
  trees : List.Forall₂ (ROT w) a.trees b.trees
  toks : RL w a.toks b.toks
  req : ROT w a.req b.req
  nons : a.nons = b.nons
  dead : RL w a.dead b.dead

theorem RA0.mono {w v : Wd} (h : w ≤ v) {a b : Acc0} (x : RA0 w a b) : RA0 v a b :=
  ⟨ROTs.mono h x.trees, RL.mono h x.toks, ROT.mono h x.req, x.nons, RL.mono h x.dead⟩

/-- the two phases correspond -/
def RPh (w : Wd) : PhT → PhT → Prop
  | .first, .first => True
  | .loc, .loc => True
  | .aft, .aft => True
  | .shr a, .shr b => w.ρ a b
  | _, _ => False

theorem RPh.mono {w v : Wd} (h : w ≤ v) : ∀ {p₁ p₂ : PhT}, RPh w p₁ p₂ → RPh v p₁ p₂
  | .first, .first, _ => trivial
  | .loc, .loc, _ => trivial
  | .aft, .aft, _ => trivial
  | .shr _, .shr _, x => h.ρ _ _ x

/-- the phase in which the query of a local round is charged to the slot value -/
def isShr : PhT → Prop
  | .shr _ => True
  | _ => False

theorem RPh.afterLo {w : Wd} : ∀ {p₁ p₂ : PhT}, RPh w p₁ p₂ → RPh w p₁.afterLo p₂.afterLo
  | .first, .first, _ => trivial
  | .loc, .loc, _ => trivial
  | .aft, .aft, _ => trivial
  | .shr _, .shr _, _ => trivial

theorem not_isShr_afterLo : ∀ p : PhT, isShr p.afterLo → False
  | .first, h => h
  | .loc, h => h
  | .aft, h => h
  | .shr _, h => h

/-! ## Part 2. One query -/

section Eval
variable {β₁ β₂ : Type} {Q : Wd → β₁ → β₂ → Prop} {w : Wd}

/-- two optional tokens of roots correspond: both are there and correspond, or none is there -/
def RO (w : Wd) : Option Tok → Option Tok → Prop
  | some a, some b => w.ρ a b
  | none, none => True
  | _, _ => False

theorem ROT.root {w : Wd} (h0 : w.ρ 0 0) :
    ∀ {t₁ t₂ : Option TTree}, ROT w t₁ t₂ → RO w (t₁.map TTree.root) (t₂.map TTree.root)
  | some _, some _, h => RT.root h0 h
  | none, none, _ => trivial

theorem sk_fbT (t : Tag) (i : ℕ) {tk₁ tk₂ : Tok} {us₁ us₂ : List Tok} {rt₁ rt₂ : Option Tok}
    (hd : List Bits → Bits → Head lam X) (hinj : ∀ vs, Function.Injective (hd vs))
    (pl : PlainPart (shapeOf L t) (annOf L t)) {k₁ : Blk lam K → Tok → St lam K L β₁}
    {k₂ : Blk lam K → Tok → St lam K L β₂} (htk : w.ρ tk₁ tk₂) (hus : RL w us₁ us₂)
    (hrt : RO w rt₁ rt₂)
    (h : ∀ bl v tl₁ tl₂, w ≤ v → v.ρ tl₁ tl₂ → Skip Q v (k₁ bl tl₁) (k₂ bl tl₂)) :
    Skip Q w (fbT t i tk₁ us₁ rt₁ hd hinj pl k₁) (fbT t i tk₂ us₂ rt₂ hd hinj pl k₂) := by
  unfold fbT
  simp only [hus.length_eq]
  match rt₁, rt₂, hrt with
  | some _, some _, hab => exact Skip.marked' _ _ _ htk (f2_app hus (.cons hab .nil)) h
  | none, none, _ => exact Skip.marked' _ _ _ htk (f2_app hus .nil) h

theorem skL_fbT (t : Tag) (i : ℕ) {tk : Tok} (us : List Tok) (rt : Option Tok)
    (hd : List Bits → Bits → Head lam X) (hinj : ∀ vs, Function.Injective (hd vs))
    (pl : PlainPart (shapeOf L t) (annOf L t)) {k₁ : Blk lam K → Tok → St lam K L β₁} {c₂ : St lam K L β₂}
    (htk : w.dd tk) (h : ∀ bl v tl, w ≤ v → v.dd tl → Skip Q v (k₁ bl tl) c₂) :
    Skip Q w (fbT t i tk us rt hd hinj pl k₁) c₂ :=
  Skip.markedL' _ _ _ _ htk h

theorem RO.mono {w v : Wd} (h : w ≤ v) : ∀ {a b : Option Tok}, RO w a b → RO v a b
  | some _, some _, x => h.ρ _ _ x
  | none, none, _ => trivial

/-! ### A Fiat-Shamir query with proof-of-work bits: the search over nonces -/

theorem sk_fbTw (t : Tag) (j i : ℕ) {tk₁ tk₂ : Tok} {us₁ us₂ : List Tok} {rt₁ rt₂ : Option Tok}
    (hd : List Bits → Bits → Head lam X) (hinj : ∀ vs, Function.Injective (hd vs))
    (pl : PlainPart (shapeOf L t) (annOf L t)) {k₁ : Blk lam K → Tok → St lam K L β₁}
    {k₂ : Blk lam K → Tok → St lam K L β₂} (htk : w.ρ tk₁ tk₂) (hus : RL w us₁ us₂)
    (hrt : RO w rt₁ rt₂)
    (h : ∀ bl v tl₁ tl₂, w ≤ v → v.ρ tl₁ tl₂ → Skip Q v (k₁ bl tl₁) (k₂ bl tl₂)) :
    Skip Q w (fbTw t j i tk₁ us₁ rt₁ hd hinj pl k₁) (fbTw t j i tk₂ us₂ rt₂ hd hinj pl k₂) := by
  unfold fbTw
  simp only [hus.length_eq]
  match rt₁, rt₂, hrt with
  | some _, some _, hab => exact Skip.marked' _ _ _ htk (f2_app hus (.cons hab .nil)) h
  | none, none, _ => exact Skip.marked' _ _ _ htk (f2_app hus .nil) h

theorem skL_fbTw (t : Tag) (j i : ℕ) {tk : Tok} (us : List Tok) (rt : Option Tok)
    (hd : List Bits → Bits → Head lam X) (hinj : ∀ vs, Function.Injective (hd vs))
    (pl : PlainPart (shapeOf L t) (annOf L t)) {k₁ : Blk lam K → Tok → St lam K L β₁} {c₂ : St lam K L β₂}
    (htk : w.dd tk) (h : ∀ bl v tl, w ≤ v → v.dd tl → Skip Q v (k₁ bl tl) c₂) :
    Skip Q w (fbTw t j i tk us rt hd hinj pl k₁) c₂ :=
  Skip.markedL' _ _ _ _ htk h

/-- the attempts after the first, made by both programs on corresponding tokens: the same attempts
(they see the same hash blocks); the chaining values of the failed ones correspond (not all
hypotheses are named here: see the statement below) -/
theorem sk_fbW {C P : Type} (g : GrW C P) (chal : Blk lam K → C) (t : Tag) (i : ℕ)
    (hd : List Bits → Bits → Head lam X) (hinj : ∀ vs, Function.Injective (hd vs))
    (emb : P → PlainPart (shapeOf L t) (annOf L t)) (α : P)
    {k₁ : ℕ → List Tok → Blk lam K → Tok → St lam K L β₁}
    {k₂ : ℕ → List Tok → Blk lam K → Tok → St lam K L β₂} {tk₁ tk₂ : Tok}
    {us₁ us₂ : List Tok} {rt₁ rt₂ : Option Tok} :
    ∀ (n j : ℕ) (w : Wd) (dd₁ dd₂ : List Tok), w.ρ tk₁ tk₂ → RL w us₁ us₂ →
      RO w rt₁ rt₂ → RL w dd₁ dd₂ →
      (∀ m dd₁ dd₂ bl v tl₁ tl₂,
        w ≤ v → RL v dd₁ dd₂ → v.ρ tl₁ tl₂ → Skip Q v (k₁ m dd₁ bl tl₁) (k₂ m dd₂ bl tl₂)) →
      Skip Q w (fbW g chal t i tk₁ us₁ rt₁ hd hinj emb α k₁ n j dd₁)
        (fbW g chal t i tk₂ us₂ rt₂ hd hinj emb α k₂ n j dd₂)
  | 0, j, w, dd₁, dd₂, htk, hus, hrt, hdd, h =>
    sk_fbTw t j i hd hinj _ htk hus hrt fun bl v tl₁ tl₂ hv htl =>
      h _ _ _ bl v tl₁ tl₂ hv (RL.mono hv hdd) htl
  | n + 1, j, w, dd₁, dd₂, htk, hus, hrt, hdd, h => sk_fbTw t j i hd hinj _ htk hus hrt fun bl v tl₁ tl₂ hv htl => by
      by_cases hok : g.ok (chal bl) = true
      · simp only [hok, if_true]; exact h _ _ _ bl v tl₁ tl₂ hv (RL.mono hv hdd) htl
      · simp only [hok]
        exact sk_fbW g chal t i hd hinj emb α n (j + 1) v (tl₁ :: dd₁) (tl₂ :: dd₂) (hv.ρ _ _ htk)
          (RL.mono hv hus) (RO.mono hv hrt) (.cons htl (RL.mono hv hdd))
          fun m e₁ e₂ bl v' u₁ u₂ hv' => h m e₁ e₂ bl v' u₁ u₂ (Wd.le_trans hv hv')

/-- A Fiat-Shamir query, with or without proof-of-work bits, made by both programs. -/
theorem sk_fbG {C P : Type} (gr : Option (GrW C P)) (chal : Blk lam K → C) (t : Tag) (i : ℕ)
    {tk₁ tk₂ : Tok} {us₁ us₂ : List Tok} {rt₁ rt₂ : Option Tok} (hd : List Bits → Bits → Head lam X)
    (hinj : ∀ vs, Function.Injective (hd vs)) (emb : P → PlainPart (shapeOf L t) (annOf L t)) (α : P)
    {k₁ : Option ℕ → List Tok → Blk lam K → Tok → St lam K L β₁}
    {k₂ : Option ℕ → List Tok → Blk lam K → Tok → St lam K L β₂} (htk : w.ρ tk₁ tk₂)
    (hus : RL w us₁ us₂) (hrt : RO w rt₁ rt₂)
    (h : ∀ nc dd₁ dd₂ bl v tl₁ tl₂,
      w ≤ v → RL v dd₁ dd₂ → v.ρ tl₁ tl₂ → Skip Q v (k₁ nc dd₁ bl tl₁) (k₂ nc dd₂ bl tl₂)) :
    Skip Q w (fbG gr chal t i tk₁ us₁ rt₁ hd hinj emb α k₁)
      (fbG gr chal t i tk₂ us₂ rt₂ hd hinj emb α k₂) := by
  cases gr with
  | none =>
    exact sk_fbT t i hd hinj _ htk hus hrt fun bl v tl₁ tl₂ hv htl =>
      h none [] [] bl v tl₁ tl₂ hv .nil htl
  | some g =>
    show Skip Q w (fbTG g chal t i tk₁ us₁ rt₁ hd hinj emb α fun m => k₁ (some m))
      (fbTG g chal t i tk₂ us₂ rt₂ hd hinj emb α fun m => k₂ (some m))
    unfold fbTG
    cases g.more with
    | zero =>
      exact sk_fbT t i hd hinj _ htk hus hrt fun bl v tl₁ tl₂ hv htl =>
        h (some 0) [] [] bl v tl₁ tl₂ hv .nil htl
    | succ n =>
      refine sk_fbT t i hd hinj _ htk hus hrt fun bl v tl₁ tl₂ hv htl => ?_
      by_cases hok : g.ok (chal bl) = true
      · simp only [hok, if_true]; exact h (some 0) [] [] bl v tl₁ tl₂ hv .nil htl
      · simp only [hok]
        exact sk_fbW g chal t i hd hinj emb α n 0 v [tl₁] [tl₂] (hv.ρ _ _ htk) (RL.mono hv hus)
          (RO.mono hv hrt) (.cons htl .nil)
          fun m e₁ e₂ bl v' u₁ u₂ hv' => h (some m) e₁ e₂ bl v' u₁ u₂ (Wd.le_trans hv hv')

/-- the attempts after the first, made by the first program alone, charged to a dead token: whatever
their number, the second program does nothing (not all hypotheses are named here: see the statement
below) -/
theorem skL_fbW {C P : Type} (g : GrW C P) (chal : Blk lam K → C) (t : Tag) (i : ℕ) {tk : Tok}
    (us : List Tok) (rt : Option Tok) (hd : List Bits → Bits → Head lam X)
    (hinj : ∀ vs, Function.Injective (hd vs)) (emb : P → PlainPart (shapeOf L t) (annOf L t)) (α : P)
    {k₁ : ℕ → List Tok → Blk lam K → Tok → St lam K L β₁} {c₂ : St lam K L β₂} :
    ∀ (n j : ℕ) (w : Wd) (dd : List Tok), w.dd tk →
      (∀ m dd bl v tl, w ≤ v → v.dd tl → Skip Q v (k₁ m dd bl tl) c₂) →
      Skip Q w (fbW g chal t i tk us rt hd hinj emb α k₁ n j dd) c₂
  | 0, j, w, dd, htk, h =>
    skL_fbTw t j i us rt hd hinj _ htk fun bl v tl hv htl => h _ _ bl v tl hv htl
  | n + 1, j, w, dd, htk, h => skL_fbTw t j i us rt hd hinj _ htk fun bl v tl hv htl => by
      split
      · exact h _ _ bl v tl hv htl
      · exact skL_fbW g chal t i us rt hd hinj emb α n (j + 1) v (tl :: dd) (hv.dd _ htk)
          fun m e bl v' u hv' => h m e bl v' u (Wd.le_trans hv hv')

/-- The same as `sk_fbG`, made by the first program alone (an empty slot) -/
theorem skL_fbG {C P : Type} (gr : Option (GrW C P)) (chal : Blk lam K → C) (t : Tag) (i : ℕ)
    {tk : Tok} (us : List Tok) (rt : Option Tok) (hd : List Bits → Bits → Head lam X)
    (hinj : ∀ vs, Function.Injective (hd vs)) (emb : P → PlainPart (shapeOf L t) (annOf L t)) (α : P)
    {k₁ : Option ℕ → List Tok → Blk lam K → Tok → St lam K L β₁} {c₂ : St lam K L β₂}
    (htk : w.dd tk) (h : ∀ nc dd bl v tl, w ≤ v → v.dd tl → Skip Q v (k₁ nc dd bl tl) c₂) :
    Skip Q w (fbG gr chal t i tk us rt hd hinj emb α k₁) c₂ := by
  cases gr with
  | none => exact skL_fbT t i us rt hd hinj _ htk fun bl v tl hv htl => h none [] bl v tl hv htl
  | some g =>
    show Skip Q w (fbTG g chal t i tk us rt hd hinj emb α fun m => k₁ (some m)) c₂
    unfold fbTG
    split
    · exact skL_fbT t i us rt hd hinj _ htk fun bl v tl hv htl => h (some 0) [] bl v tl hv htl
    · refine skL_fbT t i us rt hd hinj _ htk fun bl v tl hv htl => ?_
      split
      · exact h (some 0) [] bl v tl hv htl
      · exact skL_fbW g chal t i us rt hd hinj emb α _ 0 v [tl] (hv.dd _ htk)
          fun m e bl v' u hv' => h (some m) e bl v' u (Wd.le_trans hv hv')

theorem sk_fbSlotG {C P : Type} (gr : Option (GrW C P)) (chal : Blk lam K → C) (t : Tag) (i : ℕ)
    (cms : List (Dig lam)) (x : Option X) {ph₁ ph₂ : PhT} {tk₁ tk₂ c₁ c₂ : Tok}
    {rt₁ rt₂ : Option Tok} (emb : P → PlainPart (shapeOf L t) (annOf L t)) (α : P)
    {k₁ : Option ℕ → List Tok → Blk lam K → Tok → St lam K L β₁}
    {k₂ : Option ℕ → List Tok → Blk lam K → Tok → St lam K L β₂} (hph : RPh w ph₁ ph₂)
    (htk : w.ρ tk₁ tk₂) (hc : w.ρ c₁ c₂) (hrt : RO w rt₁ rt₂)
    (h : ∀ nc dd₁ dd₂ bl v tl₁ tl₂,
      w ≤ v → RL v dd₁ dd₂ → v.ρ tl₁ tl₂ → Skip Q v (k₁ nc dd₁ bl tl₁) (k₂ nc dd₂ bl tl₂)) :
    Skip Q w (fbSlotG gr chal t i cms x ph₁ tk₁ c₁ rt₁ emb α k₁)
      (fbSlotG gr chal t i cms x ph₂ tk₂ c₂ rt₂ emb α k₂) := by
  match ph₁, ph₂, hph with
  | .first, .first, _ =>
    exact sk_fbG gr chal t i (fun _ => Head.f1 cms (x.map L.early))
      (fun _ => f1_inj cms _) emb α htk .nil hrt h
  | .loc, .loc, _ =>
    exact sk_fbG gr chal t i (fun _ => Head.f2 (lateInstancePart L i x))
      (fun _ => f2_inj _) emb α htk .nil hrt h
  | .aft, .aft, _ =>
    exact sk_fbG gr chal t i (fun _ => Head.f2 (lateInstancePart L i x))
      (fun _ => f2_inj _) emb α htk .nil hrt h
  | .shr _, .shr _, h0 =>
    exact sk_fbG gr chal t i (fun vs => Head.f3 (vs.headD [])) (fun _ => f3_inj _)
      emb α hc (.cons h0 .nil) hrt h

theorem skL_fbSlotG {C P : Type} (gr : Option (GrW C P)) (chal : Blk lam K → C) (t : Tag) (i : ℕ)
    (cms : List (Dig lam)) (x : Option X) (ph : PhT) {tk c : Tok} (rt : Option Tok)
    (emb : P → PlainPart (shapeOf L t) (annOf L t)) (α : P)
    {k₁ : Option ℕ → List Tok → Blk lam K → Tok → St lam K L β₁} {c₂ : St lam K L β₂}
    (htk : w.dd tk) (hc : isShr ph → w.dd c)
    (h : ∀ nc dd bl v tl, w ≤ v → v.dd tl → Skip Q v (k₁ nc dd bl tl) c₂) :
    Skip Q w (fbSlotG gr chal t i cms x ph tk c rt emb α k₁) c₂ := by
  match ph, hc with
  | .first, _ =>
    exact skL_fbG gr chal t i _ _ (fun _ => Head.f1 cms (x.map L.early))
      (fun _ => f1_inj cms _) emb α htk h
  | .loc, _ =>
    exact skL_fbG gr chal t i _ _ (fun _ => Head.f2 (lateInstancePart L i x)) (fun _ => f2_inj _) emb α htk h
  | .aft, _ =>
    exact skL_fbG gr chal t i _ _ (fun _ => Head.f2 (lateInstancePart L i x)) (fun _ => f2_inj _) emb α htk h
  | .shr _, hc =>
    exact skL_fbG gr chal t i _ _ (fun vs => Head.f3 (vs.headD []))
      (fun _ => f3_inj _) emb α (hc trivial) h

theorem sk_fbSlot (t : Tag) (i : ℕ) (cms : List (Dig lam)) (x : Option X) {ph₁ ph₂ : PhT}
    {tk₁ tk₂ c₁ c₂ : Tok} {rt₁ rt₂ : Option Tok} (pl : PlainPart (shapeOf L t) (annOf L t))
    {k₁ : Blk lam K → Tok → St lam K L β₁} {k₂ : Blk lam K → Tok → St lam K L β₂}
    (hph : RPh w ph₁ ph₂) (htk : w.ρ tk₁ tk₂) (hc : w.ρ c₁ c₂) (hrt : RO w rt₁ rt₂)
    (h : ∀ bl v tl₁ tl₂, w ≤ v → v.ρ tl₁ tl₂ → Skip Q v (k₁ bl tl₁) (k₂ bl tl₂)) :
    Skip Q w (fbSlot t i cms x ph₁ tk₁ c₁ rt₁ pl k₁) (fbSlot t i cms x ph₂ tk₂ c₂ rt₂ pl k₂) := by
  match ph₁, ph₂, hph with
  | .first, .first, _ =>
    exact sk_fbT t i (fun _ => Head.f1 cms (x.map L.early))
      (fun _ => f1_inj cms _) pl htk .nil hrt h
  | .loc, .loc, _ =>
    exact sk_fbT t i (fun _ => Head.f2 (lateInstancePart L i x)) (fun _ => f2_inj _) pl htk .nil hrt h
  | .aft, .aft, _ =>
    exact sk_fbT t i (fun _ => Head.f2 (lateInstancePart L i x)) (fun _ => f2_inj _) pl htk .nil hrt h
  | .shr _, .shr _, h0 =>
    exact sk_fbT t i (fun vs => Head.f3 (vs.headD [])) (fun _ => f3_inj _)
      pl hc (.cons h0 .nil) hrt h

theorem skL_fbSlot (t : Tag) (i : ℕ) (cms : List (Dig lam)) (x : Option X) (ph : PhT) {tk c : Tok}
    (rt : Option Tok) (pl : PlainPart (shapeOf L t) (annOf L t)) {k₁ : Blk lam K → Tok → St lam K L β₁}
    {c₂ : St lam K L β₂} (htk : w.dd tk) (hc : isShr ph → w.dd c)
    (h : ∀ bl v tl, w ≤ v → v.dd tl → Skip Q v (k₁ bl tl) c₂) :
    Skip Q w (fbSlot t i cms x ph tk c rt pl k₁) c₂ := by
  match ph, hc with
  | .first, _ => exact skL_fbT t i _ _ (fun _ => Head.f1 cms (x.map L.early)) (fun _ => f1_inj cms _) pl htk h
  | .loc, _ => exact skL_fbT t i _ _ (fun _ => Head.f2 (lateInstancePart L i x)) (fun _ => f2_inj _) pl htk h
  | .aft, _ => exact skL_fbT t i _ _ (fun _ => Head.f2 (lateInstancePart L i x)) (fun _ => f2_inj _) pl htk h
  | .shr _, hc => exact skL_fbT t i _ _ (fun vs => Head.f3 (vs.headD [])) (fun _ => f3_inj _) pl (hc trivial) h

theorem sk_gT (t : Tag) (i : ℕ) {tk₁ tk₂ : Tok} {rt₁ rt₂ : Option Tok}
    (pl : PlainPart (shapeOf L t) (annOf L t)) {k₁ : Tok → St lam K L β₁} {k₂ : Tok → St lam K L β₂}
    (htk : w.ρ tk₁ tk₂) (hrt : RO w rt₁ rt₂)
    (h : ∀ v c₁ c₂, w ≤ v → v.ρ c₁ c₂ → Skip Q v (k₁ c₁) (k₂ c₂)) :
    Skip Q w (gT t i tk₁ rt₁ pl k₁) (gT t i tk₂ rt₂ pl k₂) := by
  match rt₁, rt₂, hrt with
  | some _, some _, hab => exact Skip.marked' _ _ _ htk (.cons hab .nil) fun _ => h
  | none, none, _ => exact Skip.marked' _ _ _ htk .nil fun _ => h

/-- the tree over a component, if it has one, made by both programs -/
theorem sk_withTree (sMT : ℕ) (has : Bool) (depth : ℕ) (leaf : ℕ → Body L)
    {k₁ : Option TTree → St lam K L β₁} {k₂ : Option TTree → St lam K L β₂}
    (h : ∀ v tr₁ tr₂, w ≤ v → ROT v tr₁ tr₂ → Skip Q v (k₁ tr₁) (k₂ tr₂)) :
    Skip Q w (withTree sMT has depth leaf k₁) (withTree sMT has depth leaf k₂) := by
  cases has with
  | true =>
    exact (sk_commitT sMT depth leaf w).bind' fun v t₁ t₂ hv ht => h v (some t₁) (some t₂) hv ht
  | false => exact h w none none (Wd.le_refl w) trivial

/-- The trees over a component, made by both programs: what follows gets two lists of trees that
correspond (`RLT`, Compile/Batch/SkipUTree.lean). That there are as many trees as depths is not
handed on. -/
theorem sk_withTrees (sMT : ℕ) :
    ∀ (ds : List ℕ) (leaf : ℕ → ℕ → Body L) {w : Wd} {k₁ : List TTree → St lam K L β₁}
      {k₂ : List TTree → St lam K L β₂},
      (∀ v trs₁ trs₂, w ≤ v → RLT v trs₁ trs₂ → Skip Q v (k₁ trs₁) (k₂ trs₂)) →
      Skip Q w (withTrees sMT ds leaf k₁) (withTrees sMT ds leaf k₂)
  | [], _, w, _, _, h => h w [] [] (Wd.le_refl w) .nil
  | d :: ds, leaf, w, _, _, h =>
    (sk_commitT sMT d (leaf 0) w).bind' fun _ t₁ t₂ hv ht =>
      sk_withTrees sMT ds (fun n => leaf (n + 1)) fun v' trs₁ trs₂ hv' hts =>
        h v' (t₁ :: trs₁) (t₂ :: trs₂) (Wd.le_trans hv hv') (.cons (RT.mono hv' ht) hts)

/-- the same, made by the first program alone -/
theorem skL_withTree (sMT : ℕ) (has : Bool) (depth : ℕ) (leaf : ℕ → Body L)
    {k₁ : Option TTree → St lam K L β₁} {c₂ : St lam K L β₂}
    (h : ∀ v tr, w ≤ v → Skip Q v (k₁ tr) c₂) :
    Skip Q w (withTree sMT has depth leaf k₁) c₂ := by
  cases has with
  | true => exact (skL_commitT sMT depth leaf w).bindL fun v tr hv _ => h v (some tr) hv
  | false => exact h w none (Wd.le_refl w)

/-- the trees over a component, made by the first program alone -/
theorem skL_withTrees (sMT : ℕ) :
    ∀ (ds : List ℕ) (leaf : ℕ → ℕ → Body L) {w : Wd} {k₁ : List TTree → St lam K L β₁}
      {c₂ : St lam K L β₂},
      (∀ v trs, w ≤ v → Skip Q v (k₁ trs) c₂) → Skip Q w (withTrees sMT ds leaf k₁) c₂
  | [], _, w, _, _, h => h w [] (Wd.le_refl w)
  | d :: ds, leaf, w, _, _, h =>
    (skL_commitT sMT d (leaf 0) w).bindL fun _ tr hv _ =>
      skL_withTrees sMT ds (fun n => leaf (n + 1)) fun v' trs hv' =>
        h v' (tr :: trs) (Wd.le_trans hv hv')

theorem skL_gT (t : Tag) (i : ℕ) {tk : Tok} (rt : Option Tok) (pl : PlainPart (shapeOf L t) (annOf L t))
    {k₁ : Tok → St lam K L β₁} {c₂ : St lam K L β₂} (htk : w.dd tk)
    (h : ∀ v c, w ≤ v → v.dd c → Skip Q v (k₁ c) c₂) :
    Skip Q w (gT t i tk rt pl k₁) c₂ :=
  Skip.markedL' _ _ _ _ htk fun _ => h

end Eval

/-! ## Part 3. One round -/

section Rounds
variable (sMT : ℕ) (t : Tag) (cms : List (Dig lam)) (xin : Y → Option X)

/-- A local round in one slot (hypotheses below). A full slot takes the same steps in both programs;
for an empty slot the first program alone builds a tree and queries the Fiat-Shamir oracle. -/
theorem sk_slotLo {r : Round} {s : Shape} (a : RAnn r) (wr : WireRB lam K r a)
    (emb : (p : r.Pos) → r.Sym p → Body L) (plJ : a.Pj → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ)
    {ph₁ ph₂ : PhT} {w : Wd} (h0 : w.ρ 0 0) (hph : RPh w ph₁ ph₂)
    {z₁ z₂ : SlotSt lam K Y (r :: s)} (hz : RS w (isShr ph₁) z₁ z₂) :
    Skip (fun v z₁' z₂' => RS v False z₁' z₂') w (slotLo sMT t cms xin a wr emb plJ i ph₁ z₁)
      (slotLoU sMT t cms xin a wr emb plJ i ph₂ z₂) := by
  cases hz with
  | @full st a₁ a₂ y h₁ h₂ hf =>
    obtain ⟨m, k⟩ := st
    have e : slotLoU sMT t cms xin a wr emb plJ i ph₂ ((m, k), a₂) =
        slotLo sMT t cms xin a wr emb plJ i ph₂ ((m, k), a₂) := by
      simp only [slotLoU, h₂]
    rw [e]
    have ex : a₁.x.bind xin = a₂.x.bind xin := by rw [h₁, h₂]
    dsimp only [slotLo]
    rw [ex]
    refine sk_withTree sMT wr.hasJ wr.depthJ _ fun v tr₁ tr₂ hv htr => ?_
    refine sk_fbSlotG wr.grJ wr.chal t i cms _ plJ _ (hph.mono hv) (hv.ρ _ _ hf.tk) (hv.ρ _ _ hf.c)
      (ROT.root (hv.ρ _ _ h0) htr) fun nc dd₁ dd₂ bl v' tl₁ tl₂ hv' hdd htl => ?_
    have hf' := hf.mono (Wd.le_trans hv hv')
    exact .pure
      (.full y h₁ h₂
        ⟨htl, hf'.c, by rw [hf.blocks], f2_snoc hf'.trees (ROT.mono hv' htr), f2_snoc hf'.toks htl,
          by rw [hf.nons], f2_app hdd hf'.dead⟩)
  | @empty st₁ st₂ a₁ a₂ h₁ h₂ htk hc =>
    obtain ⟨m, k⟩ := st₁
    have e : slotLoU sMT t cms xin a wr emb plJ i ph₂ (st₂, a₂) =
        Step.pure (st₂.2 (wr.chal (blk0 lam K)), a₂) := by
      simp only [slotLoU, h₂]
    rw [e]
    dsimp only [slotLo]
    refine skL_withTree sMT wr.hasJ wr.depthJ _ fun v tr hv => ?_
    refine skL_fbSlotG wr.grJ wr.chal t i cms _ ph₁ _ plJ _ (hv.dd _ htk)
      (fun j => hv.dd _ (hc j)) fun nc dd bl v' tl _ htl => ?_
    exact .pure (.empty h₁ h₂ htl fun j => j.elim)

/-- The joining round in one slot (hypotheses below). The slot value of an empty slot is dead. -/
theorem sk_slotJoin {r : Round} {s : Shape} (a : RAnn r) (wr : WireRB lam K r a)
    (emb : (p : r.Pos) → r.Sym p → Body L) (plJ : a.Pj → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ)
    {J : Prop} {w : Wd} (h0 : w.ρ 0 0) {z₁ z₂ : SlotSt lam K Y (r :: s)} (hz : RS w J z₁ z₂) :
    Skip (fun v z₁' z₂' => RS v True z₁' z₂') w (slotJoin sMT t a wr emb plJ i z₁)
      (slotJoinU sMT t a wr emb plJ i z₂) := by
  cases hz with
  | @full st a₁ a₂ y h₁ h₂ hf =>
    obtain ⟨m, k⟩ := st
    have e : slotJoinU sMT t a wr emb plJ i ((m, k), a₂) =
        slotJoin sMT t a wr emb plJ i ((m, k), a₂) := by
      simp only [slotJoinU, h₂]
    rw [e]
    dsimp only [slotJoin]
    refine sk_withTree sMT wr.hasJ wr.depthJ _ fun v tr₁ tr₂ hv htr => ?_
    refine sk_gT t i _ (hv.ρ _ _ hf.tk) (ROT.root (hv.ρ _ _ h0) htr) fun v' c₁ c₂ hv' hc => ?_
    have hf' := hf.mono (Wd.le_trans hv hv')
    exact .pure
      (.full y h₁ h₂
        ⟨hf'.tk, hc, hf.blocks, f2_snoc hf'.trees (ROT.mono hv' htr),
          f2_snoc hf'.toks hc, hf.nons, hf'.dead⟩)
  | @empty st₁ st₂ a₁ a₂ h₁ h₂ htk hc =>
    obtain ⟨m, k⟩ := st₁
    have e : slotJoinU sMT t a wr emb plJ i (st₂, a₂) = Step.pure (st₂, a₂) := by
      simp only [slotJoinU, h₂]
    rw [e]
    dsimp only [slotJoin]
    refine skL_withTree sMT wr.hasJ wr.depthJ _ fun v tr hv => ?_
    refine skL_gT t i _ _ (hv.dd _ htk) fun v' c hv' hc' => ?_
    exact .pure (.empty h₁ h₂ (hv'.dd _ (hv.dd _ htk)) fun _ => hc')

/-- after the joining round: the slot value of the first program against what the second program
puts into the request tree -/
theorem RS.rc {w : Wd} {s : Shape} {z₁ z₂ : SlotSt lam K Y s} (x : RS w True z₁ z₂) :
    RC w z₁.2.c (z₂.2.x.map fun _ => z₂.2.c) := by
  cases x with
  | full y h₁ h₂ hf => simp only [h₂]; exact hf.c
  | empty h₁ h₂ _ hc => simp only [h₂]; exact hc trivial

/-- the joining round in all slots -/
theorem sk_joinM {r : Round} {s : Shape} (a : RAnn r) (wr : WireRB lam K r a)
    (emb : (p : r.Pos) → r.Sym p → Body L)
    (plJ : a.Pj → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) {J : Prop} :
    ∀ (zs₁ zs₂ : List (SlotSt lam K Y (r :: s))) {w : Wd}, w.ρ 0 0 → List.Forall₂ (RS w J) zs₁ zs₂ →
      Skip (fun v o₁ o₂ => List.Forall₂ (RS v True) o₁.1 o₂.1 ∧ List.Forall₂ (RC v) o₁.2 o₂.2) w
        (joinM sMT t a wr emb plJ i zs₁) (joinMU sMT t a wr emb plJ i zs₂)
  | [], _, _, _, .nil => .pure ⟨.nil, .nil⟩
  | z₁ :: t₁, z₂ :: t₂, w, h0, .cons hz ht => by
    unfold joinM joinMU
    refine (sk_slotJoin sMT t a wr emb plJ i h0 hz).bind' fun v z₁' z₂' hv hz' => ?_
    refine (sk_joinM a wr emb plJ i t₁ t₂ (hv.ρ _ _ h0) (RSs.mono hv ht)).bind'
      fun v' o₁ o₂ hv' ho => ?_
    have hz'' := hz'.mono hv'
    exact .pure ⟨.cons hz'' ho.1, .cons hz''.rc ho.2⟩

/-- a slot that hears a shared verifier message keeps `RS` -/
theorem RS.hear {r : Round} {s : Shape} {a : RAnn r} (wr : WireRB lam K r a) (bl : Blk lam K)
    (noted : Bool) {w : Wd} {J : Prop} {z₁ z₂ : SlotSt lam K Y (r :: s)} (x : RS w J z₁ z₂) :
    RS w J (hear wr bl noted z₁) (hear wr bl noted z₂) := by
  cases x with
  | @full st a₁ a₂ y h₁ h₂ hf =>
    obtain ⟨m, k⟩ := st
    refine .full y h₁ h₂ ⟨hf.tk, hf.c, ?_, ?_, hf.toks, hf.nons, hf.dead⟩
    · show a₁.blocks ++ [bl] = a₂.blocks ++ [bl]
      rw [hf.blocks]
    · show List.Forall₂ (ROT w) (if noted then a₁.trees else a₁.trees ++ [none])
        (if noted then a₂.trees else a₂.trees ++ [none])
      cases noted
      · exact f2_snoc hf.trees trivial
      · exact hf.trees
  | @empty st₁ st₂ a₁ a₂ h₁ h₂ htk hc =>
    obtain ⟨m₁, k₁⟩ := st₁
    obtain ⟨m₂, k₂⟩ := st₂
    exact .empty h₁ h₂ htk hc

/-- under the hypotheses below, `eachM` on corresponding lists gives corresponding lists -/
theorem sk_eachM {σ₁ σ₂ τ₁ τ₂ : Type} {R : Wd → σ₁ → σ₂ → Prop} {R' : Wd → τ₁ → τ₂ → Prop}
    (hR : ∀ w v a b, w ≤ v → R w a b → R v a b) (hR' : ∀ w v a b, w ≤ v → R' w a b → R' v a b)
    {f₁ : σ₁ → St lam K L τ₁} {f₂ : σ₂ → St lam K L τ₂} {w₀ : Wd}
    (H : ∀ v a b, w₀ ≤ v → R v a b → Skip R' v (f₁ a) (f₂ b)) :
    ∀ (l₁ : List σ₁) (l₂ : List σ₂) {w : Wd}, w₀ ≤ w → List.Forall₂ (R w) l₁ l₂ →
      Skip (fun v r₁ r₂ => List.Forall₂ (R' v) r₁ r₂) w (eachM f₁ l₁) (eachM f₂ l₂)
  | [], _, _, _, .nil => .pure .nil
  | a :: t₁, b :: t₂, w, hw, .cons hab ht => by
    show Skip _ w ((f₁ a).bind fun x => (eachM f₁ t₁).bind fun r => Step.pure (x :: r))
      ((f₂ b).bind fun x => (eachM f₂ t₂).bind fun r => Step.pure (x :: r))
    refine (H w a b hw hab).bind' fun v x₁ x₂ hv hx => ?_
    refine (sk_eachM hR hR' H t₁ t₂ (Wd.le_trans hw hv) (ht.imp fun _ _ y => hR _ _ _ _ hv y)).bind'
      fun v' r₁ r₂ hv' hr => ?_
    exact .pure (.cons (hR' _ _ _ _ hv' hx) hr)

theorem sk_tree0 {β₁ β₂ : Type} {Q : Wd → β₁ → β₂ → Prop} {r : Round} (a : RAnn r)
    (wr : WireRB lam K r a) (emb : (p : r.Pos) → r.Sym p → Body L) (m0 : a.M0) {w : Wd}
    {k₁ : Option TTree → St lam K L β₁} {k₂ : Option TTree → St lam K L β₂}
    (h : ∀ v tr₁ tr₂, w ≤ v → ROT v tr₁ tr₂ → Skip Q v (k₁ tr₁) (k₂ tr₂)) :
    Skip Q w (tree0 sMT a wr emb m0 k₁) (tree0 sMT a wr emb m0 k₂) :=
  sk_withTree sMT _ _ _ h

end Rounds

/-! ## Part 4. All chains -/

/-- Under the hypotheses below: the second program is the first without the chains of the empty
slots. At the end the full slots and the shared parts correspond. -/
theorem sk_chain (sMT : ℕ) (t : Tag) (cms : List (Dig lam)) (xin : Y → Option X) (depthReq : ℕ) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (embS : (p : OPos s) → OSym s p → Body L)
        (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph₁ ph₂ : PhT) (st0 : SStrat s A)
        (zs₁ zs₂ : List (SlotSt lam K Y s)) (a₁ a₂ : Acc0) (w : Wd),
      w.ρ 0 0 → RPh w ph₁ ph₂ → List.Forall₂ (RS w (isShr ph₁)) zs₁ zs₂ → RA0 w a₁ a₂ →
      Skip (fun v o₁ o₂ => List.Forall₂ (RAcc v) o₁.1 o₂.1 ∧ RA0 v o₁.2 o₂.2) w
        (chainT sMT t cms xin depthReq s A W embS embP i ph₁ st0 zs₁ a₁)
        (chainTU sMT t cms xin depthReq s A W embS embP i ph₂ st0 zs₂ a₂)
  | [], _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hz, ha =>
    .pure ⟨f2_map (fun _ _ x => x.acc) hz, ha⟩
  | r :: s, (a, A), (wr, W), embS, embP, i, ph₁, ph₂, (m0, k0), zs₁, zs₂, a₁, a₂, w, h0, hph, hz, ha => by
    have hkk : a.kind = .lo ∨ a.kind = .sh := by cases a.kind <;> simp
    rcases hkk with hk | hk
    · rw [chainT_lo _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hk,
        chainTU_lo _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hk]
      refine (sk_eachM (R := fun v => RS v (isShr ph₁)) (R' := fun v => RS v False)
          (fun _ _ _ _ h x => x.mono h) (fun _ _ _ _ h x => x.mono h)
          (fun v z₁ z₂ hv hz' => sk_slotLo sMT t cms xin a wr _ _ i (hv.ρ _ _ h0) (hph.mono hv) hz')
          zs₁ zs₂ (Wd.le_refl w) hz).bind'
        fun v zs₁' zs₂' hv hz' => ?_
      have ha' := ha.mono hv
      exact sk_chain sMT t cms xin depthReq s A W _ _ (i + 1) _ _ _ zs₁' zs₂' _ _ v (hv.ρ _ _ h0)
        (hph.mono hv).afterLo (hz'.imp fun _ _ x => x.weak (not_isShr_afterLo ph₁))
        ⟨f2_snoc ha'.trees trivial, ha'.toks, ha'.req, ha'.nons, ha'.dead⟩
    · match ph₁, ph₂, hph, hz with
      | .loc, .loc, _, hz =>
        rw [chainT_join _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hk,
          chainTU_join _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hk]
        refine (sk_joinM sMT t a wr _ _ i zs₁ zs₂ h0 hz).bind' fun v o₁ o₂ hv ho => ?_
        refine (sk_req depthReq ho.2).bind' fun v₂ rq₁ rq₂ hv₂ hrq => ?_
        refine sk_tree0 sMT a wr _ m0 fun v₃ tr₁ tr₂ hv₃ htr => ?_
        have h03 : v₃.ρ 0 0 := hv₃.ρ _ _ (hv₂.ρ _ _ (hv.ρ _ _ h0))
        refine sk_fbG _ _ t i _ _ _ _ ((hrq.mono hv₃).root h03) .nil (ROT.root h03 htr)
          fun nc dd₁ dd₂ bl v₄ tl₁ tl₂ hv₄ hdd htl => ?_
        have hw4 : w ≤ v₄ := Wd.le_trans hv (Wd.le_trans hv₂ (Wd.le_trans hv₃ hv₄))
        have ha' := ha.mono hw4
        exact sk_chain sMT t cms xin depthReq s A W _ _ (i + 1) _ _ _ _ _ _ _ v₄ (hv₄.ρ _ _ h03) htl
          (f2_map (fun _ _ x => (x.hear wr bl true).weak fun _ => trivial)
            (RSs.mono (Wd.le_trans hv₂ (Wd.le_trans hv₃ hv₄)) ho.1))
          ⟨f2_snoc ha'.trees (ROT.mono hv₄ htr),
            f2_snoc ha'.toks htl,
            hrq.mono (Wd.le_trans hv₃ hv₄),
            congrArg (nc.toList ++ ·) ha'.nons,
            f2_app hdd ha'.dead⟩
      | .shr tk₁, .shr tk₂, hph, hz =>
        rw [chainT_shr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hk,
          chainTU_shr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hk]
        refine sk_tree0 sMT a wr _ m0 fun v tr₁ tr₂ hv htr => ?_
        refine sk_fbG _ _ t i _ _ _ _ (hv.ρ _ _ hph) .nil (ROT.root (hv.ρ _ _ h0) htr)
          fun nc dd₁ dd₂ bl v₂ tl₁ tl₂ hv₂ hdd htl => ?_
        have hw2 : w ≤ v₂ := Wd.le_trans hv hv₂
        have ha' := ha.mono hw2
        exact sk_chain sMT t cms xin depthReq s A W _ _ (i + 1) _ _ _ _ _ _ _ v₂ (hw2.ρ _ _ h0) htl
          (f2_map (fun _ _ x => x.hear wr bl false) (RSs.mono hw2 hz))
          ⟨f2_snoc ha'.trees (ROT.mono hv₂ htr), f2_snoc ha'.toks htl, ha'.req,
            congrArg (nc.toList ++ ·) ha'.nons, f2_app hdd ha'.dead⟩
      | .first, .first, hph, hz =>
        rw [chainT_skip _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hk _ (Or.inl rfl),
          chainTU_skip _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hk _ (Or.inl rfl)]
        exact sk_chain sMT t cms xin depthReq s A W _ _ (i + 1) _ _ _ _ _ _ _ w h0 hph
          (f2_map (fun _ _ x => x.hear wr _ false) hz)
          ⟨f2_snoc ha.trees trivial, ha.toks, ha.req, ha.nons, ha.dead⟩
      | .aft, .aft, hph, hz =>
        rw [chainT_skip _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hk _ (Or.inr rfl),
          chainTU_skip _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hk _ (Or.inr rfl)]
        exact sk_chain sMT t cms xin depthReq s A W _ _ (i + 1) _ _ _ _ _ _ _ w h0 hph
          (f2_map (fun _ _ x => x.hear wr _ false) hz)
          ⟨f2_snoc ha.trees trivial, ha.toks, ha.req, ha.nons, ha.dead⟩

end Compile.Batch.SkipU
