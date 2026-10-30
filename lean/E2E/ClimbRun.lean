-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/ClimbRun.lean: strategies, runs and honest provers along a pair with bits (E2E/ClimbPair.lean),
and how "the verifier accepts the prover outside its abort set" reads on either side of the pair.

A pair between the lists of rounds s and t says that t is s with further verifier messages, all to
be rejected, and further content in its prover messages, which is ignored. Proof of work is the case
in view: t's prover message is s's with a nonce, t's verifier message is s's with further bits, and
the test says that the bits are 0. Here the same maps are applied to the verifier randomness of a
whole run, to a prover's strategy and to an honest prover.

  `Pair.oldR`, `Pair.passR`, `Pair.zeroR`: the verifier randomness of t read back as that of s; all
    its verifier messages pass; that of s as one of t. `Pair.BlindSet p B`: the set B holds ρ' if it
    holds the image of the old part of ρ' (`Pair.blindSet_old`: a set pulled back along `oldR` is
    one). `Pair.rho_strip`, `Pair.passTr_rho`: how they
    sit in a transcript. `Pair.oldR_zeroR`, `Pair.passR_zeroR`, `Pair.zeroR_oldR`: `zeroR` and
    `oldR` are a bijection between the verifier randomness of s and that of t that passes.
  `Pair.up`: a strategy of s played in t. Its messages are filled, and of a verifier message it
    hears the old part alone. `Pair.dn`: a strategy of t played in s. Its messages are stripped, and
    where the verifier of s sends c it hears zero c. `Pair.dn_up`: up and then down is the strategy.
  `Pair.strip_run_up`, `Pair.run_dn`: the runs, stripped, are the runs on the other side.
  `Pair.msgs_run_up`: the messages of a strategy carried up hang on the old parts of the verifier
    messages alone.
  `ProtoPair.accept_of_pass`: at a transcript all of whose verifier messages pass, P decides as P₀
    does on the stripped transcript. `ProtoPair.accept_congr`: P's decision reads of a transcript
    whether its verifier messages pass, and the stripped transcript, and nothing else.
    `ProtoPair.accept_run_up`: the decision on the run of a strategy carried up.
  `AccPassAt S x y σ' B`: P accepts every transcript all of whose verifier messages pass, whose
    verifier randomness lies outside B, and that is, stripped, the run of σ' stripped.
    `ProtoPair.accPassAt_iff_run`: that is no more than: P accepts the run of σ' itself there.
    `ProtoPair.accPassAt_up_iff`, `ProtoPair.accPassAt_dn_iff`: what it is on the side of P₀.
  `Honest.up`, `Honest.dn`: an honest prover carried over, with its coins, its external strings and
    its abort set read through `oldR` or `zeroR` (`Honest.mem_withheld_up`,
    `Honest.mem_withheld_dn`, `Honest.mem_withheld_up_zero`).
  `AccPass S H' valid`: `AccPassAt` for a valid input and all coins, at the prover's strategy and
    abort set. `Blind S H'`: the abort sets are blind sets.
    `Honest.up_blind`: a prover carried up is blind.
  `BlindUp S H'`: more than `Blind`: the abort set holds ρ' exactly if it holds the image of the old
    part of ρ', and each strategy is itself carried down and up again. `Honest.up_blindUp`: every
    prover carried up is a member. `blindUp_iff`: THE MEMBERS ARE EXACTLY THE PROVERS THAT AGREE, IN
    EVERY ABORT SET AND EVERY STRATEGY, WITH THEMSELVES CARRIED DOWN AND UP AGAIN. `BlindUp.blind`,
    `BlindUp.wh_congr`, `BlindUp.msgs`: so the abort set, the plain parts and the answers are the
    same at verifier randomness with the same old part.
  `ProtoPair.accPass_up_iff`: P₀ accepts H outside its abort set (`Honest.Acc`) if and only if H
    carried up has `AccPass`. `ProtoPair.accPass_dn_iff`: H' has `AccPass` if and only if P₀ accepts
    H' carried down outside its abort set; `ProtoPair.acc_dn` is its way from left to right.

What the equivalences are. One sentence said in two alphabets, along the bijection of `zeroR` and
`oldR`. There is no mathematics in them beyond the pair's four laws.

Which statements take a set that is handed more than an abort set is. `AccPassAt` has one strategy
and one free set B, so `accPassAt_iff_run`, `accPassAt_up_iff`, `accPassAt_dn_iff` and
`Pair.BlindSet` take any set, also one that hangs on the prover's coins or private input. `AccPass`,
`accPass_up_iff`, `accPass_dn_iff`, `acc_dn`, `Honest.up`, `Honest.dn`, `Blind` and `BlindUp` read
the abort set of the library's `Honest`, which is handed no coin.

For whoever writes a prover. By `blindUp_iff`, to show `BlindUp` of a prover that is typed at the
protocol with proof of work is to show an equation of strategies through all rounds. A prover that
is typed at P₀ and carried up has it for nothing (`Honest.up_blindUp`).

`AccPass` is modelled on the clause `acc` of the library's `GrFit` (Compile/Batch/SpecFit.lean),
which speaks of a wire and of numbers written in as nonces. `GrFit` has beside `acc` a clause `wh`,
that the abort set does not depend on the test bits, and a clause `run`, that the honest messages do
not; `Blind` is one direction of the like of `wh`, and `BlindUp` is modelled on both. No statement
here ties `AccPass`, `Blind` or `BlindUp` to `GrFit`.

Limits.
  * `AccPass` WITH A SMALL ABORT SET AT P SAYS NOTHING. The abort set that holds just the verifier
    randomness that passes gives `AccPass` to every strategy, and where each round's test is on b
    bits that set has probability 2^-(the sum of the bits) under P's own uniform verifier
    randomness. So the number that goes beside `AccPass S H'` is the probability of the abort set of
    `Honest.dn S H'`, over the verifier randomness of P₀; or that of the abort set of H' TOGETHER
    WITH `Blind S H'` (E2E/ClimbUnif.lean has the inequality between the two). Never that of the
    abort set of H' alone.
  * `Honest.Acc` and `AccPass` have no number in them: with everything in the abort set both hold of
    every strategy. Neither is called completeness here.
  * `Honest.dn S H'` IS ANOTHER PROVER, OF ANOTHER PROTOCOL, and so is a strategy carried down
    (`Pair.dn`): it is the strategy where every verifier message passes, stripped. Carried up again
    it is not H': the nonces of H' and all that it does after a verifier message that fails the test
    are not kept. So beside a statement on H' at P, the statement on the same prover is
    `AccPass S H'`, and not `Honest.Acc` of `Honest.dn S H'`. Under `BlindUp S H'` the two are
    closer: H' then agrees with `Honest.dn S H'` carried up in every strategy and every abort set
    (`blindUp_iff`). The agreement is in the abort set as a whole, not in its public part (`Bad`)
    and the rest (`Hid`) apart. Whether that makes it "the same prover" is not ours to say.
  * Plain honest provers alone (`Honest`). The library's honest prover of a batch (`BatchHonestProver`,
    Iop/Batch.lean) has a shared and a local strategy, and is accepted if the plain prover made of
    them (`BatchHonestProver.one`) is. A `BatchHonestProver.one` carried up or down is the `one` of no `BatchHonestProver` by any
    statement here, and nothing here moves `Honest.Acc` or `AccPass` between two provers with the
    same external strings, abort sets and stripped runs.
  * Acceptance alone, point by point in the verifier randomness. Nothing on probability: a pair does
    not say how many verifier messages of t fail the test, and `old` is free on those that fail.
  * `AccPass` says nothing where a verifier message fails the test. There P rejects whatever the
    prover sends, so `Honest.Acc` at P can hold only with all such verifier randomness in the abort
    set of every valid input (not proved here).
  * `AccPass` holds of itself where no input is valid. That some verifier randomness passes is
    `Pair.exists_passR`.
  * Nothing on queries or zero knowledge, and no view of s is tied to one of t: a pair ties no
    position, no answer and no cut of a prover message into oracle and plain part (the head of
    E2E/ClimbPair.lean). `Pair.msgs_run_up` and `BlindUp.msgs` compare two runs of t.
  * No prover is shown to be accepted here, and no honest prover is written.

What "without proof of work" means at the IOP as written in Lean is a reading of this folder's
writers and an open question: E2E/ClimbFiles.lean's head.

This file's definitions `AccPassAt`, `AccPass`, `Pair.BlindSet`, `Blind` and `BlindUp` may be read
as stating a goal, that is, something that is to be proved of a prover. They count as none.

-/
import E2E.ClimbPair

set_option autoImplicit false

noncomputable section

namespace AtPublicFiles.Climb
open Iop Prob

/-! ## 1. The verifier randomness of a whole run -/

/-- The verifier randomness of t read back as that of s: of each verifier message the old part. -/
def Pair.oldR : {s t : Iop.Shape} → Pair s t → Rho t → Rho s
  | [], [], _, _ => ()
  | [], _ :: _, p, _ => Empty.elim p
  | _ :: _, [], p, _ => Empty.elim p
  | _ :: _, _ :: _, (u, p), (c, ρ) => (u.old c, Pair.oldR p ρ)

/-- All verifier messages pass. -/
def Pair.passR : {s t : Iop.Shape} → Pair s t → Rho t → Bool
  | [], [], _, _ => true
  | [], _ :: _, p, _ => Empty.elim p
  | _ :: _, [], p, _ => Empty.elim p
  | _ :: _, _ :: _, (u, p), (c, ρ) => u.pass c && Pair.passR p ρ

/-- The verifier randomness of s as one of t: each verifier message c as zero c. -/
def Pair.zeroR : {s t : Iop.Shape} → Pair s t → Rho s → Rho t
  | [], [], _, _ => ()
  | [], _ :: _, p, _ => Empty.elim p
  | _ :: _, [], p, _ => Empty.elim p
  | _ :: _, _ :: _, (u, p), (c, ρ) => (u.zero c, Pair.zeroR p ρ)

/-- The verifier messages of a stripped transcript are the old parts of the transcript's. -/
theorem Pair.rho_strip : ∀ {s t : Iop.Shape} (p : Pair s t) (τ' : Tr t),
    (p.strip τ').rho = p.oldR τ'.rho
  | [], [], _, _ => rfl
  | [], _ :: _, p, _ => Empty.elim p
  | _ :: _, [], p, _ => Empty.elim p
  | _ :: _, _ :: _, (u, p), (_, c, τ') => congrArg (Prod.mk (u.old c)) (Pair.rho_strip p τ')

/-- Whether a transcript passes is read off its verifier messages. -/
theorem Pair.passTr_rho : ∀ {s t : Iop.Shape} (p : Pair s t) (τ' : Tr t),
    p.passTr τ' = p.passR τ'.rho
  | [], [], _, _ => rfl
  | [], _ :: _, p, _ => Empty.elim p
  | _ :: _, [], p, _ => Empty.elim p
  | _ :: _, _ :: _, (u, p), (_, c, τ') =>
    congrArg (fun b => u.pass c && b) (Pair.passTr_rho p τ')

theorem Pair.oldR_zeroR : ∀ {s t : Iop.Shape} (p : Pair s t) (ρ : Rho s), p.oldR (p.zeroR ρ) = ρ
  | [], [], _, () => rfl
  | [], _ :: _, p, _ => Empty.elim p
  | _ :: _, [], p, _ => Empty.elim p
  | _ :: _, _ :: _, (u, p), (c, ρ) => by
      show (u.old (u.zero c), p.oldR (p.zeroR ρ)) = (c, ρ)
      rw [u.old_zero, Pair.oldR_zeroR p ρ]

theorem Pair.passR_zeroR : ∀ {s t : Iop.Shape} (p : Pair s t) (ρ : Rho s),
    p.passR (p.zeroR ρ) = true
  | [], [], _, _ => rfl
  | [], _ :: _, p, _ => Empty.elim p
  | _ :: _, [], p, _ => Empty.elim p
  | _ :: _, _ :: _, (u, p), (c, ρ) => by
      show (u.pass (u.zero c) && p.passR (p.zeroR ρ)) = true
      rw [u.pass_zero, Pair.passR_zeroR p ρ, Bool.and_true]

/-- Verifier randomness that passes is the image of its old part. -/
theorem Pair.zeroR_oldR : ∀ {s t : Iop.Shape} (p : Pair s t) (ρ' : Rho t),
    p.passR ρ' = true → p.zeroR (p.oldR ρ') = ρ'
  | [], [], _, (), _ => rfl
  | [], _ :: _, p, _, _ => Empty.elim p
  | _ :: _, [], p, _, _ => Empty.elim p
  | _ :: _, _ :: _, (u, p), (c', ρ'), h => by
      have h0 : (u.pass c' && p.passR ρ') = true := h
      rw [Bool.and_eq_true] at h0
      show (u.zero (u.old c'), p.zeroR (p.oldR ρ')) = (c', ρ')
      rw [u.zero_old c' h0.1, Pair.zeroR_oldR p ρ' h0.2]

/-- Some verifier randomness of t passes. -/
theorem Pair.exists_passR {s t : Iop.Shape} (p : Pair s t) : ∃ ρ' : Rho t, p.passR ρ' = true :=
  (instNonemptyRho s).elim fun ρ => ⟨p.zeroR ρ, p.passR_zeroR ρ⟩

/-- A set of verifier randomness of t that holds ρ' as soon as it holds the image of the old part of
ρ'. ONE WAY: verifier randomness that fails may be added to such a set at will, and the set of all
that fails is one. It is the way that a bound on the measure needs (E2E/ClimbUnif.lean). -/
def Pair.BlindSet {s t : Iop.Shape} (p : Pair s t) (B : Set (Rho t)) : Prop :=
  ∀ ρ', p.zeroR (p.oldR ρ') ∈ B → ρ' ∈ B

/-- A member: the set of verifier randomness whose old part lies in a set of s. -/
theorem Pair.blindSet_old {s t : Iop.Shape} (p : Pair s t) (B₀ : Set (Rho s)) :
    p.BlindSet {ρ' | p.oldR ρ' ∈ B₀} := fun ρ' h => by
  have h' : p.oldR (p.zeroR (p.oldR ρ')) ∈ B₀ := h
  rw [p.oldR_zeroR] at h'
  exact h'

/-! ## 2. Strategies and their runs -/

/-- A strategy of s played in t: each message filled; of a verifier message the old part alone is
heard. -/
def Pair.up : {s t : Iop.Shape} → {β : Type} → Pair s t → Strat s β → Strat t β
  | [], [], _, _, b => b
  | [], _ :: _, _, p, _ => Empty.elim p
  | _ :: _, [], _, p, _ => Empty.elim p
  | _ :: _, _ :: _, _, (u, p), (m, k) => (u.fill m, fun c' => Pair.up p (k (u.old c')))

/-- A strategy of t played in s: each message stripped; where the verifier of s sends c the strategy
hears zero c. It is another strategy, of other rounds: what the strategy of t does after a verifier
message that fails the test is not kept. -/
def Pair.dn : {s t : Iop.Shape} → {β : Type} → Pair s t → Strat t β → Strat s β
  | [], [], _, _, b => b
  | [], _ :: _, _, p, _ => Empty.elim p
  | _ :: _, [], _, p, _ => Empty.elim p
  | _ :: _, _ :: _, _, (u, p), (m', k') => (u.strip m', fun c => Pair.dn p (k' (u.zero c)))

/-- The run of a strategy carried up, stripped, is the strategy's own run at the old parts. -/
theorem Pair.strip_run_up :
    ∀ {s t : Iop.Shape} {β : Type} (p : Pair s t) (σ : Strat s β) (ρ' : Rho t),
      p.strip ((p.up σ).run ρ').1 = (σ.run (p.oldR ρ')).1
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, _, p, _, _ => Empty.elim p
  | _ :: _, [], _, p, _, _ => Empty.elim p
  | _ :: _, _ :: _, _, (u, p), (m, k), (c', ρ') => by
      show (u.strip (u.fill m), u.old c', p.strip ((p.up (k (u.old c'))).run ρ').1) =
        (m, u.old c', ((k (u.old c')).run (p.oldR ρ')).1)
      rw [u.strip_fill, Pair.strip_run_up p (k (u.old c')) ρ']

/-- The run of a strategy carried down is the strategy's own run at the images, stripped. -/
theorem Pair.run_dn :
    ∀ {s t : Iop.Shape} {β : Type} (p : Pair s t) (σ' : Strat t β) (ρ : Rho s),
      ((p.dn σ').run ρ).1 = p.strip (σ'.run (p.zeroR ρ)).1
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, _, p, _, _ => Empty.elim p
  | _ :: _, [], _, p, _, _ => Empty.elim p
  | _ :: _, _ :: _, _, (u, p), (m', k'), (c, ρ) => by
      show (u.strip m', c, ((p.dn (k' (u.zero c))).run ρ).1) =
        (u.strip m', u.old (u.zero c), p.strip ((k' (u.zero c)).run (p.zeroR ρ)).1)
      rw [u.old_zero, Pair.run_dn p (k' (u.zero c)) ρ]

/-- Up and then down is the strategy itself. -/
theorem Pair.dn_up :
    ∀ {s t : Iop.Shape} {β : Type} (p : Pair s t) (σ : Strat s β), p.dn (p.up σ) = σ
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, p, _ => Empty.elim p
  | _ :: _, [], _, p, _ => Empty.elim p
  | _ :: _, _ :: _, _, (u, p), (m, k) => by
      show (u.strip (u.fill m), fun c => p.dn (p.up (k (u.old (u.zero c))))) = (m, k)
      rw [u.strip_fill]
      refine congrArg (Prod.mk m) (funext fun c => ?_)
      rw [u.old_zero, Pair.dn_up p (k c)]

/-- The messages of a strategy carried up hang on the old parts of the verifier messages alone: at
two values of the verifier randomness with the same old part, the runs have the same plain parts and
the same answers at every position. -/
theorem Pair.msgs_run_up :
    ∀ {s t : Iop.Shape} {β : Type} (p : Pair s t) (σ : Strat s β) (ρ₁ ρ₂ : Rho t),
      p.oldR ρ₁ = p.oldR ρ₂ →
      ((p.up σ).run ρ₁).1.plains = ((p.up σ).run ρ₂).1.plains ∧
        ∀ q, ((p.up σ).run ρ₁).1.read q = ((p.up σ).run ρ₂).1.read q
  | [], [], _, _, _, _, _, _ => ⟨rfl, fun q => nomatch q⟩
  | [], _ :: _, _, p, _, _, _, _ => Empty.elim p
  | _ :: _, [], _, p, _, _, _, _ => Empty.elim p
  | _ :: _, _ :: _, _, (u, p), (m, k), (c₁, ρ₁), (c₂, ρ₂), h => by
      have h' : (u.old c₁, p.oldR ρ₁) = (u.old c₂, p.oldR ρ₂) := h
      have hc : u.old c₁ = u.old c₂ := congrArg Prod.fst h'
      obtain ⟨i1, i2⟩ := Pair.msgs_run_up p (k (u.old c₁)) ρ₁ ρ₂ (congrArg Prod.snd h')
      constructor
      · show ((u.fill m).2, ((p.up (k (u.old c₁))).run ρ₁).1.plains) =
          ((u.fill m).2, ((p.up (k (u.old c₂))).run ρ₂).1.plains)
        rw [← hc, i1]
      · intro q
        cases q with
        | inl q => rfl
        | inr q =>
          show ((p.up (k (u.old c₁))).run ρ₁).1.read q = ((p.up (k (u.old c₂))).run ρ₂).1.read q
          rw [← hc]
          exact i2 q

/-! ## 3. The decision, point by point -/

variable {X : Type} {E : ExtSpec} {P₀ P : InteractiveOracleProof X E}

/-- **At a transcript all of whose verifier messages pass, P decides as P₀ does on the stripped
transcript.** -/
theorem ProtoPair.accept_of_pass (S : ProtoPair P₀ P) (x : X) (y : E.Str) (τ' : Tr P.shape)
    (h : S.pair.passTr τ' = true) : P.accept x y τ' = P₀.accept x y (S.pair.strip τ') := by
  rw [S.acc, h, Bool.true_and]

/-- Two transcripts that pass alike and are the same when stripped are decided alike. -/
theorem ProtoPair.accept_congr (S : ProtoPair P₀ P) (x : X) (y : E.Str) {τ' τ'' : Tr P.shape}
    (hp : S.pair.passTr τ' = S.pair.passTr τ'') (hs : S.pair.strip τ' = S.pair.strip τ'') :
    P.accept x y τ' = P.accept x y τ'' := by
  rw [S.acc x y τ', S.acc x y τ'', hp, hs]

/-- P accepts the run of a strategy carried up exactly if all verifier messages pass and P₀ accepts
the strategy's own run at the old parts. -/
theorem ProtoPair.accept_run_up (S : ProtoPair P₀ P) {β : Type} (σ : Strat P₀.shape β)
    (ρ' : Rho P.shape) (x : X) (y : E.Str) :
    P.accept x y ((S.pair.up σ).run ρ').1 =
      (S.pair.passR ρ' && P₀.accept x y (σ.run (S.pair.oldR ρ')).1) := by
  rw [S.acc, Pair.passTr_rho, Strat.rho_run, Pair.strip_run_up]

/-! ## 4. Acceptance where all verifier messages pass: the core, at a strategy and a set -/

/-- At every transcript all of whose verifier messages pass, whose verifier randomness lies outside
B, and that is, stripped, the strategy's own run stripped, P accepts. It is a notion of the pair: it
reads S through `passR` and `strip`. ALONE IT ASKS LITTLE: the set B of all verifier randomness that
passes gives it to every strategy. The number that goes beside it is the probability of
{ρ | zeroR ρ ∈ B} over the verifier randomness of P₀, not that of B (this file's head, Limits). -/
def AccPassAt (S : ProtoPair P₀ P) (x : X) (y : E.Str) {β : Type} (σ' : Strat P.shape β)
    (B : Set (Rho P.shape)) : Prop :=
  ∀ τ' : Tr P.shape, S.pair.passR τ'.rho = true → τ'.rho ∉ B →
    S.pair.strip τ' = S.pair.strip (σ'.run τ'.rho).1 → P.accept x y τ' = true

/-- The clause on all transcripts that are the same when stripped asks nothing more of the strategy:
it is the pair's own law (`ProtoPair.accept_congr`). `AccPassAt` says that P accepts the strategy's
own run at verifier randomness that passes and lies outside B. -/
theorem ProtoPair.accPassAt_iff_run (S : ProtoPair P₀ P) (x : X) (y : E.Str) {β : Type}
    (σ' : Strat P.shape β) (B : Set (Rho P.shape)) :
    AccPassAt S x y σ' B ↔
      ∀ ρ', S.pair.passR ρ' = true → ρ' ∉ B → P.accept x y (σ'.run ρ').1 = true := by
  constructor
  · intro h ρ' hp hB
    have hr : (σ'.run ρ').1.rho = ρ' := Strat.rho_run σ' ρ'
    refine h (σ'.run ρ').1 ?_ ?_ ?_
    · rw [hr]
      exact hp
    · rw [hr]
      exact hB
    · rw [hr]
  · intro h τ' hp hB hs
    have hq : S.pair.passTr τ' = S.pair.passTr (σ'.run τ'.rho).1 := by
      rw [Pair.passTr_rho, Pair.passTr_rho, Strat.rho_run]
    rw [S.accept_congr x y hq hs]
    exact h τ'.rho hp hB

/-- **P₀ accepts a strategy's runs outside B₀ if and only if the strategy carried up has
`AccPassAt` at the set of verifier randomness whose old part lies in B₀.** -/
theorem ProtoPair.accPassAt_up_iff (S : ProtoPair P₀ P) (x : X) (y : E.Str) {β : Type}
    (σ : Strat P₀.shape β) (B₀ : Set (Rho P₀.shape)) :
    (∀ ρ, ρ ∉ B₀ → P₀.accept x y (σ.run ρ).1 = true) ↔
      AccPassAt S x y (S.pair.up σ) {ρ' | S.pair.oldR ρ' ∈ B₀} := by
  rw [S.accPassAt_iff_run]
  constructor
  · intro h ρ' hp hB
    rw [S.accept_run_up, hp, Bool.true_and]
    exact h _ hB
  · intro h ρ hB
    have hB' : S.pair.zeroR ρ ∉ {ρ' | S.pair.oldR ρ' ∈ B₀} := fun hm => by
      have hm' : S.pair.oldR (S.pair.zeroR ρ) ∈ B₀ := hm
      rw [S.pair.oldR_zeroR] at hm'
      exact hB hm'
    have h1 := h (S.pair.zeroR ρ) (S.pair.passR_zeroR ρ) hB'
    rw [S.accept_run_up, S.pair.passR_zeroR, S.pair.oldR_zeroR, Bool.true_and] at h1
    exact h1

/-- **A strategy of P has `AccPassAt` at B if and only if P₀ accepts the runs of the strategy
carried down, at verifier randomness whose image lies outside B.** The way back uses that verifier
randomness that passes is the image of its old part. It holds of every strategy, since `AccPassAt`
reads a strategy only where every verifier message passes; the strategy carried down is another
strategy (`Pair.dn`). -/
theorem ProtoPair.accPassAt_dn_iff (S : ProtoPair P₀ P) (x : X) (y : E.Str) {β : Type}
    (σ' : Strat P.shape β) (B : Set (Rho P.shape)) :
    AccPassAt S x y σ' B ↔
      ∀ ρ, S.pair.zeroR ρ ∉ B → P₀.accept x y ((S.pair.dn σ').run ρ).1 = true := by
  rw [S.accPassAt_iff_run]
  constructor
  · intro h ρ hB
    have h1 := h (S.pair.zeroR ρ) (S.pair.passR_zeroR ρ) hB
    have hp : S.pair.passTr (σ'.run (S.pair.zeroR ρ)).1 = true := by
      rw [Pair.passTr_rho, Strat.rho_run, S.pair.passR_zeroR]
    rw [S.pair.run_dn]
    exact (S.accept_of_pass x y _ hp).symm.trans h1
  · intro h ρ' hp hB
    have hz : S.pair.zeroR (S.pair.oldR ρ') = ρ' := S.pair.zeroR_oldR ρ' hp
    have h1 := h (S.pair.oldR ρ') (by rw [hz]; exact hB)
    rw [S.pair.run_dn, hz] at h1
    have hq : S.pair.passTr (σ'.run ρ').1 = true := by
      rw [Pair.passTr_rho, Strat.rho_run, hp]
    exact (S.accept_of_pass x y _ hq).trans h1

/-! ## 5. Honest provers -/

/-- An honest prover of P₀ carried up to P: the same coins and external strings, each strategy
carried up. Verifier randomness is in the abort set if its old part is: whether it passes is not
looked at. -/
def Honest.up (S : ProtoPair P₀ P) {Wt : Type} (H : Honest P₀ Wt) : Honest P Wt where
  Coin := H.Coin
  ext := H.ext
  strat := fun w x c => S.pair.up (H.strat w x c)
  Bad := {ρ' | S.pair.oldR ρ' ∈ H.Bad}
  Hid := fun w x => {ρ' | S.pair.oldR ρ' ∈ H.Hid w x}

/-- An honest prover of P carried down to P₀: the same coins and external strings, each strategy
carried down. Verifier randomness is in the abort set if its image is. It is another prover, of
another protocol: what the prover of P does after a verifier message that fails the test is not
kept. -/
def Honest.dn (S : ProtoPair P₀ P) {Wt : Type} (H' : Honest P Wt) : Honest P₀ Wt where
  Coin := H'.Coin
  ext := H'.ext
  strat := fun w x c => S.pair.dn (H'.strat w x c)
  Bad := {ρ | S.pair.zeroR ρ ∈ H'.Bad}
  Hid := fun w x => {ρ | S.pair.zeroR ρ ∈ H'.Hid w x}

theorem Honest.mem_withheld_up (S : ProtoPair P₀ P) {Wt : Type} (H : Honest P₀ Wt) (w : Wt) (x : X)
    (ρ' : Rho P.shape) :
    ρ' ∈ (Honest.up S H).withheld w x ↔ S.pair.oldR ρ' ∈ H.withheld w x := Iff.rfl

theorem Honest.mem_withheld_dn (S : ProtoPair P₀ P) {Wt : Type} (H' : Honest P Wt) (w : Wt) (x : X)
    (ρ : Rho P₀.shape) :
    ρ ∈ (Honest.dn S H').withheld w x ↔ S.pair.zeroR ρ ∈ H'.withheld w x := Iff.rfl

/-- `AccPassAt` for a valid input and all coins, at the prover's external strings, its strategy and
its abort set. ALONE IT ASKS LITTLE: an abort set that holds all verifier randomness that passes
gives it to every strategy (this file's head, Limits). -/
def AccPass (S : ProtoPair P₀ P) {Wt : Type} (H' : Honest P Wt) (valid : Wt → X → Prop) : Prop :=
  ∀ w x c, valid w x → AccPassAt S x (H'.ext w) (H'.strat w x c) (H'.withheld w x)

/-- Each abort set holds ρ' as soon as it holds the image of the old part of ρ' (`Pair.BlindSet`:
one way). -/
def Blind (S : ProtoPair P₀ P) {Wt : Type} (H' : Honest P Wt) : Prop :=
  ∀ w x, S.pair.BlindSet (H'.withheld w x)

theorem Honest.mem_withheld_up_zero (S : ProtoPair P₀ P) {Wt : Type} (H : Honest P₀ Wt) (w : Wt)
    (x : X) (ρ' : Rho P.shape) :
    S.pair.zeroR (S.pair.oldR ρ') ∈ (Honest.up S H).withheld w x ↔
      ρ' ∈ (Honest.up S H).withheld w x := by
  rw [Honest.mem_withheld_up, Honest.mem_withheld_up, S.pair.oldR_zeroR]

/-- A prover carried up is blind. -/
theorem Honest.up_blind (S : ProtoPair P₀ P) {Wt : Type} (H : Honest P₀ Wt) :
    Blind S (Honest.up S H) :=
  fun w x ρ' => (Honest.mem_withheld_up_zero S H w x ρ').1

/-- Nothing on the prover's side looks at whether a verifier message passes, and what a prover
message holds beyond the stripped message is what `fill` puts there. `wh`: the abort set holds ρ'
exactly if it holds the image of the old part of ρ'. `run`: each strategy is itself carried down and
up again, so it hears of a verifier message the old part alone, also after one that fails the test,
and each of its messages is `fill` of a message of P₀. (What `fill` puts in is the pair's matter: at
a typed round with proof of work it is the nonce 0, by the text of `rpZ`, E2E/ClimbChain.lean.) -/
structure BlindUp (S : ProtoPair P₀ P) {Wt : Type} (H' : Honest P Wt) : Prop where
  wh : ∀ w x ρ', ρ' ∈ H'.withheld w x ↔ S.pair.zeroR (S.pair.oldR ρ') ∈ H'.withheld w x
  run : ∀ w x c, H'.strat w x c = S.pair.up (S.pair.dn (H'.strat w x c))

/-- A member: every prover carried up. -/
theorem Honest.up_blindUp (S : ProtoPair P₀ P) {Wt : Type} (H : Honest P₀ Wt) :
    BlindUp S (Honest.up S H) where
  wh := fun w x ρ' => (Honest.mem_withheld_up_zero S H w x ρ').symm
  run := fun w x c => (congrArg (fun σ => S.pair.up σ) (S.pair.dn_up (H.strat w x c))).symm

/-- **The members are exactly the provers that agree, in every abort set and every strategy, with
themselves carried down and up again.** -/
theorem blindUp_iff (S : ProtoPair P₀ P) {Wt : Type} (H' : Honest P Wt) :
    BlindUp S H' ↔
      (∀ w x, H'.withheld w x = (Honest.up S (Honest.dn S H')).withheld w x) ∧
        ∀ w x c, H'.strat w x c = (Honest.up S (Honest.dn S H')).strat w x c :=
  ⟨fun h => ⟨fun w x => Set.ext fun ρ' => h.wh w x ρ', h.run⟩,
    fun h => ⟨fun w x ρ' => Set.ext_iff.1 (h.1 w x) ρ', h.2⟩⟩

theorem BlindUp.blind {S : ProtoPair P₀ P} {Wt : Type} {H' : Honest P Wt} (h : BlindUp S H') :
    Blind S H' :=
  fun w x ρ' hm => (h.wh w x ρ').2 hm

/-- At two values of the verifier randomness with the same old part, membership in the abort set is
the same. -/
theorem BlindUp.wh_congr {S : ProtoPair P₀ P} {Wt : Type} {H' : Honest P Wt} (h : BlindUp S H')
    (w : Wt) (x : X) {ρ₁ ρ₂ : Rho P.shape} (e : S.pair.oldR ρ₁ = S.pair.oldR ρ₂) :
    ρ₁ ∈ H'.withheld w x ↔ ρ₂ ∈ H'.withheld w x := by
  rw [h.wh w x ρ₁, h.wh w x ρ₂, e]

/-- And the honest runs have the same plain parts and the same answers at every position. -/
theorem BlindUp.msgs {S : ProtoPair P₀ P} {Wt : Type} {H' : Honest P Wt} (h : BlindUp S H')
    (w : Wt) (x : X) (c : H'.Coin) {ρ₁ ρ₂ : Rho P.shape} (e : S.pair.oldR ρ₁ = S.pair.oldR ρ₂) :
    ((H'.strat w x c).run ρ₁).1.plains = ((H'.strat w x c).run ρ₂).1.plains ∧
      ∀ q, ((H'.strat w x c).run ρ₁).1.read q = ((H'.strat w x c).run ρ₂).1.read q := by
  rw [h.run w x c]
  exact S.pair.msgs_run_up _ ρ₁ ρ₂ e

/-- **P₀ accepts an honest prover outside its abort set (`Honest.Acc`) if and only if the prover
carried up has `AccPass`.** -/
theorem ProtoPair.accPass_up_iff (S : ProtoPair P₀ P) {Wt : Type} (H : Honest P₀ Wt)
    (valid : Wt → X → Prop) : H.Acc valid ↔ AccPass S (Honest.up S H) valid :=
  ⟨fun h w x c hv =>
      (S.accPassAt_up_iff x (H.ext w) (H.strat w x c) (H.withheld w x)).1
        fun ρ hρ => h w x c ρ hv hρ,
    fun h w x c ρ hv hρ =>
      (S.accPassAt_up_iff x (H.ext w) (H.strat w x c) (H.withheld w x)).2 (h w x c hv) ρ hρ⟩

/-- **An honest prover of P has `AccPass` if and only if P₀ accepts the prover carried down outside
its abort set (`Honest.Acc`).** -/
theorem ProtoPair.accPass_dn_iff (S : ProtoPair P₀ P) {Wt : Type} (H' : Honest P Wt)
    (valid : Wt → X → Prop) : AccPass S H' valid ↔ (Honest.dn S H').Acc valid :=
  ⟨fun h w x c ρ hv hρ =>
      (S.accPassAt_dn_iff x (H'.ext w) (H'.strat w x c) (H'.withheld w x)).1 (h w x c hv) ρ hρ,
    fun h w x c hv =>
      (S.accPassAt_dn_iff x (H'.ext w) (H'.strat w x c) (H'.withheld w x)).2
        fun ρ hρ => h w x c ρ hv hρ⟩

/-- Its way from left to right. -/
theorem ProtoPair.acc_dn (S : ProtoPair P₀ P) {Wt : Type} (H' : Honest P Wt)
    (valid : Wt → X → Prop) (h : AccPass S H' valid) : (Honest.dn S H').Acc valid :=
  (S.accPass_dn_iff H' valid).1 h

end AtPublicFiles.Climb

#print axioms AtPublicFiles.Climb.Pair.rho_strip
#print axioms AtPublicFiles.Climb.Pair.passTr_rho
#print axioms AtPublicFiles.Climb.Pair.oldR_zeroR
#print axioms AtPublicFiles.Climb.Pair.passR_zeroR
#print axioms AtPublicFiles.Climb.Pair.zeroR_oldR
#print axioms AtPublicFiles.Climb.Pair.exists_passR
#print axioms AtPublicFiles.Climb.Pair.blindSet_old
#print axioms AtPublicFiles.Climb.Pair.strip_run_up
#print axioms AtPublicFiles.Climb.Pair.run_dn
#print axioms AtPublicFiles.Climb.Pair.dn_up
#print axioms AtPublicFiles.Climb.Pair.msgs_run_up
#print axioms AtPublicFiles.Climb.ProtoPair.accept_of_pass
#print axioms AtPublicFiles.Climb.ProtoPair.accept_congr
#print axioms AtPublicFiles.Climb.ProtoPair.accept_run_up
#print axioms AtPublicFiles.Climb.ProtoPair.accPassAt_iff_run
#print axioms AtPublicFiles.Climb.ProtoPair.accPassAt_up_iff
#print axioms AtPublicFiles.Climb.ProtoPair.accPassAt_dn_iff
#print axioms AtPublicFiles.Climb.Honest.mem_withheld_up
#print axioms AtPublicFiles.Climb.Honest.mem_withheld_dn
#print axioms AtPublicFiles.Climb.Honest.mem_withheld_up_zero
#print axioms AtPublicFiles.Climb.Honest.up_blind
#print axioms AtPublicFiles.Climb.Honest.up_blindUp
#print axioms AtPublicFiles.Climb.blindUp_iff
#print axioms AtPublicFiles.Climb.BlindUp.blind
#print axioms AtPublicFiles.Climb.BlindUp.wh_congr
#print axioms AtPublicFiles.Climb.BlindUp.msgs
#print axioms AtPublicFiles.Climb.ProtoPair.accPass_up_iff
#print axioms AtPublicFiles.Climb.ProtoPair.accPass_dn_iff
#print axioms AtPublicFiles.Climb.ProtoPair.acc_dn
