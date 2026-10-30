-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  Rom/Defer.lean: deferred programming in operational form. Definitions and one statement,
  `Spec.defer`; its proof is in Rom/DeferProof_tail.lean.

  The honest side of an experiment is written in a small language in which a secret string is a
  token (`Tok`):
  the program holds a handle and can (1) put the token into the point of a marked oracle evaluation,
  (2) reveal it.
  The compiled prover (`Pp`, Compile/Batch/Star.lean) is a program of this language.
  (Words of this library: lean/GLOSSARY.md.)

  Rules:
  * every marked evaluation is charged to one token t, in which its point is injective; it may hold
    further tokens us;
  * the answer splits into a visible part, which the program gets, and a tail, which it gets as a
    new token;
  * reveal ts shows the bits of ts and releases every evaluation charged to a token of ts;
  * a released evaluation must have all its tokens shown, its tail included (else: violation). Hence
    an unshown token occurs only in points of unreleased evaluations: "all in one step, or none
    ever";
  * a token that is shown, or that is in an earlier marked point of the same oracle, cannot be
    charged (violation);
  * a token that does not exist yet cannot be charged, used or revealed (violation);
  * the charged token is not among the further tokens of the same point (violation).
  With one chain and one slot every token is charged at most once and occurs nowhere else: us = [].

  Mode R: one lazily sampled table serves everybody; reveal changes nothing in the table.
  Mode I: a marked evaluation returns a fresh uniform answer and does not touch the table; its
  release writes it there, if the entry is still empty.

  Notation:
    `Step.plain o q k`: an evaluation of o at the query `q : S.Dom o`;
      `Step.marked o t us pt inj k`: an evaluation of o at the point `pt (d.val t) (us.map d.val)`,
      charged to the token t, with the further tokens us
    `c.run modeI d`: the run of a step; modeI = true is mode I, false is mode R
    `d.Within e M ℓ os`: what a run may do at most: e o plain and M o marked evaluations of o;
      marked ones only at oracles of os, each charged to a token of at least ℓ o bits; no violation
      of the rules
    `A.Bounded t N` (Rom/World.lean): at most t o queries to oracle o and at most N calls, on every
      path
    `tv p q` (Prob/Basic.lean): statistical (total variation) distance of two discrete distributions
-/
import Rom.World
noncomputable section -- Lean tags what it cannot compile

open scoped ENNReal
open Prob
namespace Rom

abbrev Bits := List Bool
abbrev Tok := ℕ

/-- how the answers of each oracle split into a visible part and a secret tail -/
structure Split (S : OSpec) where
  Vis : S.ι → Type
  tl : S.ι → ℕ
  split : ∀ o, S.Rng o ≃ Vis o × (Fin (tl o) → Bool)

variable {S : OSpec}

/-- One step of the challenger: a step may contain several evaluations and releases;
the adversary makes no query during a step. -/
inductive Step (S : OSpec) (sp : Split S) (α : Type) : Type
  | pure (a : α) : Step S sp α
  | sample (n : ℕ) (k : Fin (n + 1) → Step S sp α) : Step S sp α
  | plain (o : S.ι) (q : S.Dom o) (k : S.Rng o → Step S sp α) : Step S sp α
  | fresh (ℓ : ℕ) (k : Tok → Step S sp α) : Step S sp α
  | marked (o : S.ι) (t : Tok) (us : List Tok) (pt : Bits → List Bits → S.Dom o)
      (inj : ∀ vs, Function.Injective fun v => pt v vs) (k : sp.Vis o → Tok → Step S sp α) :
      Step S sp α
  | reveal (ts : List Tok) (k : List Bits → Step S sp α) : Step S sp α

namespace Step
variable {sp : Split S} {α β : Type}
def bind : Step S sp α → (α → Step S sp β) → Step S sp β
  | pure a, g => g a
  | sample n k, g => sample n fun r => (k r).bind g
  | plain o q k, g => plain o q fun r => (k r).bind g
  | fresh ℓ k, g => fresh ℓ fun t => (k t).bind g
  | marked o t us pt inj k, g => marked o t us pt inj fun v t' => (k v t').bind g
  | reveal ts k, g => reveal ts fun vs => (k vs).bind g
instance : Monad (Step S sp) where
  pure := Step.pure
  bind := Step.bind
end Step

/-- the record of one marked evaluation -/
structure Ev (S : OSpec) where
  o : S.ι
  pt : S.Dom o
  ans : S.Rng o
  charged : Tok
  others : List Tok
  tail : Tok
  released : Bool

/-- the state of the experiment beside the challenger's own -/
structure DSt (S : OSpec) where
  table : Table S
  vals : List Bits              -- the value of token i is at place i
  shown : List Tok
  evs : List (Ev S)
  nPlain : S.ι → ℕ
  viol : Bool

def DSt.init (S : OSpec) : DSt S := ⟨Table.empty S, [], [], [], fun _ => 0, false⟩
def DSt.val (d : DSt S) (t : Tok) : Bits := d.vals.getD t []

/-- release, in mode I, of all evaluations charged to a shown token: write the answers into the
empty entries of the table -/
def releaseAll (modeI : Bool) (shown : List Tok) :
    List (Ev S) → Table S → List (Ev S) × Table S
  | [], T => ([], T)
  | e :: es, T =>
      if !e.released && shown.contains e.charged then
        -- write only where the table is empty: mode I is then consistent, as
        -- ZKCP/Defs.lean asks of a simulator;
        -- outside the bad event (a hit: Rom/DeferProof_tail.lean) no release meets a defined entry,
        -- so the lemma and its bound do not depend on this
        let r := releaseAll modeI shown es
          (if modeI then (match T e.o e.pt with | none => T.set e.o e.pt e.ans | some _ => T)
            else T)
        ({ e with released := true } :: r.1, r.2)
      else
        let r := releaseAll modeI shown es T
        (e :: r.1, r.2)

/-- a released evaluation has all its tokens shown (exactly: its tail and its further tokens are
tested here) -/
def closedUnder (shown : List Tok) (evs : List (Ev S)) : Bool :=
  evs.all fun e => !e.released || (shown.contains e.tail && e.others.all shown.contains)

/-- the run of a step; modeI = true is mode I, false is mode R -/
def Step.run {sp : Split S} {α : Type} (modeI : Bool) :
    Step S sp α → DSt S → PMF (α × DSt S)
  | .pure a, d => PMF.pure (a, d)
  | .sample n k, d => (PMF.uniformOfFintype (Fin (n + 1))).bind fun r => (k r).run modeI d
  | .plain o q k, d => (lazyAnswer d.table o q).bind fun p =>
      (k p.1).run modeI
        { d with table := p.2, nPlain := Function.update d.nPlain o (d.nPlain o + 1) }
  | .fresh ℓ k, d => (PMF.uniformOfFintype (Fin ℓ → Bool)).bind fun u =>
      (k d.vals.length).run modeI { d with vals := d.vals ++ [List.ofFn u] }
  | .marked o t us pt _ k, d =>
      let P := pt (d.val t) (us.map d.val)
      -- a token that does not exist yet cannot be used (else the point is public and the bound
      -- false)
      -- the charged token is not among the others (inj is for fixed values of the others)
      let bad : Bool :=
        decide (d.vals.length ≤ t) || us.any (fun u => decide (d.vals.length ≤ u)) ||
          us.contains t || d.shown.contains t ||
          d.evs.any fun e => decide (e.o = o) && (e.charged == t || e.others.contains t)
      let go : S.Rng o → Table S → PMF (α × DSt S) := fun r T =>
        (k (sp.split o r).1 d.vals.length).run modeI
          { d with table := T, vals := d.vals ++ [List.ofFn (sp.split o r).2],
                   evs := d.evs ++ [⟨o, P, r, t, us, d.vals.length, false⟩], viol := d.viol || bad }
      if modeI then (PMF.uniformOfFintype (S.Rng o)).bind fun r => go r d.table
      else (lazyAnswer d.table o P).bind fun p => go p.1 p.2
  | .reveal ts k, d =>
      let shown := d.shown ++ ts
      let r := releaseAll modeI shown d.evs d.table
      (k (ts.map d.val)).run modeI
        { d with
          table := r.2, shown := shown, evs := r.1,
          viol := d.viol || !closedUnder shown r.1 || ts.any (fun u => decide (d.vals.length ≤ u)) }

/-- A challenger: a private state, and a step for each call of the adversary. -/
structure Chall (S : OSpec) (sp : Split S) (Out In : Type) where
  τ : Type
  step : τ → Out → Step S sp (In × τ)

/-- the `World` that a challenger makes, in either mode; the adversary's queries read the table -/
def Chall.world
    {sp : Split S} {Out In : Type} (C : Chall S sp Out In) (modeI : Bool) : World S Out In where
  σ := C.τ × DSt S
  answer := fun s o q =>
    (lazyAnswer s.2.table o q).map fun p => (p.1, (s.1, { s.2 with table := p.2 }))
  reply := fun s m => ((C.step s.1 m).run modeI s.2).map fun p => (p.1.1, (p.1.2, p.2))

/-- what a run may do at most: e o plain and M o marked evaluations of o; marked ones only at
oracles of os, each charged to a token of at least ℓ o bits; no violation of the rules -/
def DSt.Within (d : DSt S) (e M ℓ : S.ι → ℕ) (os : Finset S.ι) : Prop :=
  d.viol = false ∧
  (∀ o, d.nPlain o ≤ e o) ∧
  (∀ o, (d.evs.filter fun v => decide (v.o = o)).length ≤ M o) ∧
  ∀ v ∈ d.evs, v.o ∈ os ∧ ℓ v.o ≤ (d.val v.charged).length

/-- Deferred programming, with worst-case counts (a statement; proved in Rom/DeferProof_tail.lean):
for an adversary with at most t o queries to each oracle o and at most N calls (N is in no bound),
if every run in mode I stays within (e, M, ℓ, os), the outputs in the two modes are within Σ over o
in os of M o (t o + e o + M o) / 2^(ℓ o). -/
def Spec.defer : Prop :=
  ∀ (S : OSpec) (sp : Split S) (Out In α : Type) (C : Chall S sp Out In) (s₀ : C.τ)
      (A : Adv S Out In α) (t e M ℓ : S.ι → ℕ) (N : ℕ) (os : Finset S.ι),
    A.Bounded t N →
    (∀ x ∈ (interact (C.world true) A (s₀, DSt.init S)).support, x.2.2.Within e M ℓ os) →
    tv ((interact (C.world false) A (s₀, DSt.init S)).map Prod.fst)
        ((interact (C.world true) A (s₀, DSt.init S)).map Prod.fst) ≤
      ∑ o ∈ os, (M o : ℝ≥0∞) * (t o + e o + M o : ℕ) / 2 ^ ℓ o

end Rom
