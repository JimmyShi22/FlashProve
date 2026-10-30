-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/BatchSeqZk.lean: the honest side of chains of batch links: completeness and honest-verifier
exact zero knowledge for sets of slots, with further reads (`ExactB`; for one instance:
`Honest.Exact`, Ior/Honest.lean).

In standard terms: the honest prover's side of a sequential composition of interactive oracle
reductions that run on a batch of instances.

Definitions and statements; the proofs are in Ior/BatchSeqZkProofs.lean and
Ior/BatchSeqZkRules.lean. (Soundness of such chains: Ior/BatchSeq.lean.)

A slot is one of the N places of a batch, each with one instance or empty.

Why: a batch IOP may be a chain: a joining round (each slot sends, one verifier message for all),
rounds in which only the shared part of the prover speaks, an IOP on shared oracles, and at the
end an IOP in every slot. Ior/Batch.lean has the notions for a whole batch IOP (`BIOP.Honest`:
`Acc`, `Exact`). Here is the notion for one link, and the rules.

A link is an IOR R from statements (x; shared oracles, own oracles) with an annotation A of its
shape.
Its honest side (`IOR.HonestB R A W0 Wj W0' Wj'`). As `BIOP.Honest`, by type: the shared part is a
function of the shared witness W0, coins of its own and the shared verifier messages; a slot's
part of these, the slot's instance, witness and coins and the verifier messages of its local
transcript. Unlike there, both end with a result: the shared part with the shared witness W0' of
the next link, a slot's part with (the explicit part that it expects the verifier to output, the
slot's next witness Wj'). All that is withheld is public.

Main names:
  `AccB`: completeness for each slot, to an output relation on (x'; new implicit instance; (W0',
    Wj')).
  `ExactB`: honest-verifier exact zero knowledge for sets of slots with further reads, as
    `BIOP.Honest.Exact`, on views (`IOR.View`) in the place of disclosed views.
The rules, each under the hypotheses of its statement:
  `acc_seqB`, `exact_seqB`: a link, then a batch IOP (`seqB`) is a batch IOP with `Acc`, with
    `Exact` at the composed budget (`budSeqB`). Asked by `exact_seqB` beside the two properties:
    the link is local and complete, and the output relation determines the new shared oracles from
    the new shared witness (so that the slots of a batch hand on one shared oracle).
  `acc_localB`, `exact_localB`: an IOP in every slot, in local rounds in which only the slot
    speaks (`localB`, `localH`), from the properties of the IOP for one instance. The slots are
    independent; the budget is asked of each slot.
  `accB_shared`, `exactB_shared`: an IOR run by the shared part alone under shared verifier
    messages (`sharedH`), from its properties for one instance. All slots see one transcript; the
    budget is asked at the union of the further positions of the slots of J; it reads and ties
    only shared oracles.
A chain "joining round and shared reduction; shared IOP; local IOP" is `seqB` of the first link
with (`seqB` of the second link with `localB`); its honest side is `HonestB.seqB` of the first
link's with (`HonestB.seqB` of `sharedH` with `localH`).

Limits: this file says nothing on soundness, nothing on any protocol; nothing on running times
(simulators take transcripts that fit a view by choice). There is no Hid in a link: among
`HonestB` (this file), `BIOP.Honest` and `onlineHonest` (both Ior/Batch.lean) a secret-dependent
withheld set occurs only in the preamble before a batch IOP (Ior/Batch.lean: `online`).

Terms: lean/GLOSSARY.md.
-/
import Ior.Batch
import Ior.ExactSeq
import Ior.ToProto
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

/-! ## 1. Strategies with results -/

/-- Strategies for the shared part that end with a result. -/
def SStratR : (s : Shape) → RoundSplits s → Type → Type
  | [], _, β => β
  | r :: s, (a, A), β => a.M0 × (a.kind.Sh r.Chal → SStratR s A β)

/-- Strategies for the part of one slot that end with a result. -/
def LStratR : (s : Shape) → RoundSplits s → Type → Type
  | [], _, β => β
  | r :: s, (a, A), β => a.Mj × (r.Chal → LStratR s A β)

namespace SStratR

/-- The two together are a strategy on local transcripts, with both results. -/
def zip :
    {s : Shape} → {A : RoundSplits s} → {β γ : Type} → SStratR s A β → LStratR s A γ → Strat s (β × γ)
  | [], _, _, _, b, c => (b, c)
  | _ :: _, (a, _), _, _, (m0, k0), (mj, kj) =>
    (a.join m0 mj, fun c => zip (k0 (a.kind.shOf c)) (kj c))

/-- The result, a function of the shared verifier messages. -/
def res : {s : Shape} → {A : RoundSplits s} → {β : Type} → SStratR s A β → RhoSh s A → β
  | [], _, _, b, _ => b
  | _ :: _, (_, _), _, (_, k0), (c, σ) => res (k0 c) σ

/-- The shared part goes on with its result. -/
def bind :
    {s t : Shape} → {A : RoundSplits s} → {B : RoundSplits t} → {β : Type} → SStratR s A β →
    (β → SStrat t B) → SStrat (s ++ t) (RoundSplits.app A B)
  | [], _, _, _, _, b, g => g b
  | _ :: _, _, (_, _), _, _, (m, k), g => (m, fun c => bind (k c) g)

/-- A slot's part that also follows the shared part, and ends with both results (the slot sees the
shared verifier messages, the shared witness and the shared coins). -/
def along :
    {s : Shape} → {A : RoundSplits s} → {β γ : Type} → SStratR s A β → LStratR s A γ → LStratR s A (β × γ)
  | [], _, _, _, b, c => (b, c)
  | _ :: _, (a, _), _, _, (_, k0), (mj, kj) => (mj, fun c => along (k0 (a.kind.shOf c)) (kj c))

/-- All rounds shared, only the shared part speaks: a strategy as a strategy of the shared part. -/
def ofStrat : {s : Shape} → {β : Type} → Strat s β → SStratR s (RoundSplits.const (RAnn.ofShared .sh) s) β
  | [], _, b => b
  | _ :: _, _, (m, k) => (m, fun c => ofStrat (k c))

end SStratR

namespace LStratR

/-- A slot's part goes on with its result. -/
def bind :
    {s t : Shape} → {A : RoundSplits s} → {B : RoundSplits t} → {β : Type} → LStratR s A β →
    (β → LStrat t B) → LStrat (s ++ t) (RoundSplits.app A B)
  | [], _, _, _, _, b, g => g b
  | _ :: _, _, (_, _), _, _, (m, k), g => (m, fun c => bind (k c) g)

/-- The slot is silent where only the shared part speaks, and ends with b. -/
def mute : (s : Shape) → {β : Type} → β → LStratR s (RoundSplits.const (RAnn.ofShared .sh) s) β
  | [], _, b => b
  | _ :: s, _, b => ((), fun _ => mute s b)

end LStratR

/-! ## 2. The verifier's randomness of two annotated shapes in a row -/

def RhoLo.fstA :
    {s t : Shape} → (A : RoundSplits s) → (B : RoundSplits t) → RhoLo (s ++ t) (RoundSplits.app A B) → RhoLo s A
  | [], _, _, _, _ => ()
  | _ :: _, _, (_, A), B, (c, l) => (c, RhoLo.fstA A B l)

def RhoLo.sndA :
    {s t : Shape} → (A : RoundSplits s) → (B : RoundSplits t) → RhoLo (s ++ t) (RoundSplits.app A B) → RhoLo t B
  | [], _, _, _, l => l
  | _ :: _, _, (_, A), B, (_, l) => RhoLo.sndA A B l

def RhoSh.fstA :
    {s t : Shape} → (A : RoundSplits s) → (B : RoundSplits t) → RhoSh (s ++ t) (RoundSplits.app A B) → RhoSh s A
  | [], _, _, _, _ => ()
  | _ :: _, _, (_, A), B, (c, l) => (c, RhoSh.fstA A B l)

def RhoSh.sndA :
    {s t : Shape} → (A : RoundSplits s) → (B : RoundSplits t) → RhoSh (s ++ t) (RoundSplits.app A B) → RhoSh t B
  | [], _, _, _, l => l
  | _ :: _, _, (_, A), B, (_, l) => RhoSh.sndA A B l

def BRho.fstA {N : ℕ} :
    {s t : Shape} → (A : RoundSplits s) → (B : RoundSplits t) → BRho N (s ++ t) (RoundSplits.app A B) → BRho N s A
  | [], _, _, _, _ => ()
  | _ :: _, _, (_, A), B, (c, l) => (c, BRho.fstA A B l)

def BRho.sndA {N : ℕ} :
    {s t : Shape} → (A : RoundSplits s) → (B : RoundSplits t) → BRho N (s ++ t) (RoundSplits.app A B) → BRho N t B
  | [], _, _, _, l => l
  | _ :: _, _, (_, A), B, (_, l) => BRho.sndA A B l

/-- the shared part of a verifier message of the whole batch -/
def Kind.allSh {N : ℕ} {C : Type} : (k : Kind) → k.All N C → k.Sh C
  | .sh, c => c
  | .lo, _ => ()

/-- The shared verifier messages of an execution of the batch. -/
def BRho.shared {N : ℕ} : {s : Shape} → {A : RoundSplits s} → BRho N s A → RhoSh s A
  | [], _, _ => ()
  | _ :: _, (a, _), (v, ρ) => (a.kind.allSh v, BRho.shared ρ)

/-- With local rounds only, the local verifier messages are all. -/
def RhoLo.all : (s : Shape) → RhoLo s (RoundSplits.allLocal s) → Rho s
  | [], _ => ()
  | _ :: s, (c, l) => (c, RhoLo.all s l)

/-- With shared rounds only, the shared verifier messages are all. -/
def RhoSh.all : (s : Shape) → RhoSh s (RoundSplits.const (RAnn.ofShared .sh) s) → Rho s
  | [], _ => ()
  | _ :: s, (c, l) => (c, RhoSh.all s l)

/-! ## 3. A link and its honest side -/

namespace IOR
variable {X X' : Type} {E0 Ej Eo : ExtSpec}

/-- The honest side of a link. -/
structure HonestB (R : IOR X (E0.prod Ej) X' Eo) (A : RoundSplits R.shape) (W0 Wj W0' Wj' : Type) where
  Coin0 : Type
  Coin  : Type
  [finCoin0 : Fintype Coin0]
  [neCoin0  : Nonempty Coin0]
  [finCoin  : Fintype Coin]
  [neCoin   : Nonempty Coin]
  strat0 : W0 → Coin0 → SStratR R.shape A W0'
  strat  : W0 → Coin0 → X → Wj → Coin → LStratR R.shape A (X' × Wj')
  Bad    : Set (RhoLo R.shape A)
  stop0  : RhoSh R.shape A → Bool

attribute [instance] HonestB.finCoin0 HonestB.neCoin0 HonestB.finCoin HonestB.neCoin

/-- The type of a simulator of a link, for sets of slots. -/
abbrev SimL (R : IOR X (E0.prod Ej) X' Eo) (N : ℕ) : Type :=
  (J : Finset (Fin N)) → (J → X) → (J → Rho R.shape) → (J → Finset (OPos R.shape)) →
  (J → (E0.prod Ej).Pos → Option (E0.prod Ej).Sym) → PMF (J → Option (View R))

namespace HonestB
variable {R : IOR X (E0.prod Ej) X' Eo} {A : RoundSplits R.shape} {W0 Wj W0' Wj' : Type}

/-- the withheld set of a slot: public -/
def withheld (H : R.HonestB A W0 Wj W0' Wj') : Set (Rho R.shape) :=
  {ρ | Rho.lo A ρ ∈ H.Bad ∨ H.stop0 (Rho.sh A ρ) = true}

/-- the honest prover on the local transcript of one slot -/
def one (H : R.HonestB A W0 Wj W0' Wj') (w0 : W0) (x : X) (wj : Wj) (c : H.Coin0 × H.Coin) :
    Strat R.shape (W0' × X' × Wj') :=
  (H.strat0 w0 c.1).zip (H.strat w0 c.1 x wj c.2)

/-- Completeness for each slot. -/
def AccB (H : R.HonestB A W0 Wj W0' Wj') (Ri : X → (E0.prod Ej).Str → W0 × Wj → Prop)
    (Ro : X' → Eo.Str → W0' × Wj' → Prop) : Prop :=
  ∀ x y w c ρ, Ri x y w → ρ ∉ H.withheld →
    R.out x y ((H.one w.1 x w.2 c).run ρ).1 = some ((H.one w.1 x w.2 c).run ρ).2.2.1 ∧
    Ro ((H.one w.1 x w.2 c).run ρ).2.2.1 (R.imp y ((H.one w.1 x w.2 c).run ρ).1)
      (((H.one w.1 x w.2 c).run ρ).2.1, ((H.one w.1 x w.2 c).run ρ).2.2.2)

open Classical in
/-- The output for the set J of slots at ρ, with the further positions Ts. -/
def output (H : R.HonestB A W0 Wj W0' Wj') {N : ℕ} (w0 : W0)
    (a : Fin N → Option (X × Ej.Str × Wj)) (ρ : BRho N R.shape A)
    (J : Finset (Fin N)) (Ts : J → Finset (OPos R.shape)) : PMF (J → Option (View R)) :=
  (unif (H.Coin0 × (Fin N → H.Coin))).map fun c => fun j =>
    match a j with
    | none => none
    | some aj =>
      if ρ.slot j.1 ∈ H.withheld then none
      else some (R.view (Ts j) ((H.one w0 aj.1 aj.2.2 (c.1, c.2 j)).run (ρ.slot j.1)).1)

/-- Honest-verifier exact zero knowledge for sets of slots, with further reads, the simulator
named. -/
def ExactBWith (H : R.HonestB A W0 Wj W0' Wj') (N : ℕ) (Ri : X → (E0.prod Ej).Str → W0 × Wj → Prop)
    (bud : BudB R.shape N) (Sim : R.SimL N) : Prop :=
  ∀ (w0 : W0) (y0 : E0.Str) (a : Fin N → Option (X × Ej.Str × Wj)),
    (∀ j aj, a j = some aj → Ri aj.1 (y0, aj.2.1) (w0, aj.2.2)) →
    ∀ (J : Finset (Fin N)) (as : J → X × Ej.Str × Wj), (∀ j : J, a j = some (as j)) →
      ∀ (ρ : BRho N R.shape A) (Ts : J → Finset (OPos R.shape)), bud J (fun j => ρ.slot j.1) Ts →
        H.output w0 a ρ J Ts =
          Sim J (fun j => (as j).1) (fun j => ρ.slot j.1) Ts
            (fun j => (E0.prod Ej).ans (R.given (ρ.slot j.1) (Ts j)) (y0, (as j).2.1))

def ExactB (H : R.HonestB A W0 Wj W0' Wj') (N : ℕ)
    (Ri : X → (E0.prod Ej).Str → W0 × Wj → Prop) (bud : BudB R.shape N) : Prop :=
  ∃ Sim : R.SimL N, H.ExactBWith N Ri bud Sim

end HonestB
end IOR

/-! ## 4. A link, then a batch IOP -/

section Seq
variable {X X' : Type} {E0 Ej E0' Ej' : ExtSpec}

/-- A link, then a batch IOP. -/
def seqB (R : IOR X (E0.prod Ej) X' (E0'.prod Ej'))
    (A : RoundSplits R.shape) (Q : BIOP X' (E0'.prod Ej')) : BIOP X (E0.prod Ej) where
  ior := R.seq Q.ior
  ann := RoundSplits.app A Q.ann

/-- Its honest side. The coins are independent. A slot goes on with the shared part's result,
which it computes for itself. -/
def IOR.HonestB.seqB {R : IOR X (E0.prod Ej) X' (E0'.prod Ej')}
    {A : RoundSplits R.shape} {Q : BIOP X' (E0'.prod Ej')} {W0 Wj W0' Wj' : Type}
    (HR : R.HonestB A W0 Wj W0' Wj') (HQ : Q.Honest W0' Wj') : (seqB R A Q).Honest W0 Wj where
  Coin0 := HR.Coin0 × HQ.Coin0
  Coin := HR.Coin × HQ.Coin
  strat0 := fun w0 c0 => (HR.strat0 w0 c0.1).bind fun w0' => HQ.strat0 w0' c0.2
  strat := fun w0 c0 x wj c =>
    ((HR.strat0 w0 c0.1).along (HR.strat w0 c0.1 x wj c.1)).bind fun o =>
      HQ.strat o.1 c0.2 o.2.1 o.2.2 c.2
  Bad := {l | RhoLo.fstA A Q.ann l ∈ HR.Bad} ∪ {l | RhoLo.sndA A Q.ann l ∈ HQ.Bad}
  stop0 := fun σ => HR.stop0 (RhoSh.fstA A Q.ann σ) || HQ.stop0 (RhoSh.sndA A Q.ann σ)

/-- The budget of the composition. The link bears, as a family over J: the part of T_j in its
shape together with the sources of all that Q's simulator is given in slot j. Q bears the parts in
its shape, as a family, for every subset of J (a slot that the link withholds shows the notice
(`none`) and drops out of Q's simulation). -/
def budSeqB (R : IOR X (E0.prod Ej) X' (E0'.prod Ej')) (Q : BIOP X' (E0'.prod Ej'))
    {N : ℕ} (bR : BudB R.shape N) (bQ : BudB Q.ior.shape N) :
    BudB (R.shape ++ Q.ior.shape) N := fun J ρs Ts =>
  bR J (fun j => Rho.fst (ρs j)) (fun j => IOR.firstT R Q.ior (ρs j) (Ts j)) ∧
  ∀ (J' : Finset (Fin N)) (h : J' ⊆ J), bQ J' (fun j => Rho.snd (s := R.shape) (ρs ⟨j.1, h j.2⟩))
    (fun j => IOR.partR R.shape (Ts ⟨j.1, h j.2⟩))

end Seq

/-! ## 5. An IOP in every slot -/

section Local
variable {X : Type} {E0 Ej : ExtSpec}

/-- An IOP in every slot: local rounds in which only the slot speaks. -/
def localB (B : IOR X (E0.prod Ej) Unit extNone) : BIOP X (E0.prod Ej) := ⟨B, RoundSplits.allLocal B.shape⟩

/-- Its honest side, from the honest side for one instance; `mk` puts the witness of one instance
together. -/
def localH {B : IOR X (E0.prod Ej) Unit extNone} {Wi W0 Wj : Type}
    (H : B.Honest Wi Unit) (mk : W0 → Wj → Wi) : (localB B).Honest W0 Wj where
  Coin0 := Unit
  Coin := H.Coin
  strat0 := fun _ _ => SStrat.silent .lo B.shape
  strat := fun w0 _ x wj c => LStrat.last .lo (Strat.map (fun _ => ()) (H.strat (mk w0 wj) x c))
  Bad := {l | RhoLo.all B.shape l ∈ H.Bad}
  stop0 := fun _ => false

end Local

/-! ## 6. An IOR run by the shared part alone -/

section Shared
variable {X X' : Type} {E0 Ej Eo : ExtSpec}

open Classical in
/-- The honest side of a link in which all rounds are shared and only the shared part speaks. s0
is the shared part's strategy; a slot is silent and ends with `nx x wj`; Bad0 is the public bad
set. -/
def sharedH (R : IOR X (E0.prod Ej) X' Eo) {W0 Wj W0' Wj' : Type} (Coin : Type)
    [Fintype Coin] [Nonempty Coin] (s0 : W0 → Coin → Strat R.shape W0')
    (nx : X → Wj → X' × Wj') (Bad0 : Set (Rho R.shape)) :
    R.HonestB (RoundSplits.const (RAnn.ofShared .sh) R.shape) W0 Wj W0' Wj' where
  Coin0 := Coin
  Coin := Unit
  strat0 := fun w0 c => SStratR.ofStrat (s0 w0 c)
  strat := fun _ _ x wj _ => LStratR.mute R.shape (nx x wj)
  Bad := ∅
  stop0 := fun σ => decide (RhoSh.all R.shape σ ∈ Bad0)

end Shared

/-! ## 7. Statements -/

namespace Spec
open IOR

/-- Completeness of "a link, then a batch IOP". -/
def acc_seqB : Prop :=
  ∀ (X X' : Type) (E0 Ej E0' Ej' : ExtSpec) (R : IOR X (E0.prod Ej) X' (E0'.prod Ej'))
      (A : RoundSplits R.shape) (Q : BIOP X' (E0'.prod Ej')) (W0 Wj W0' Wj' : Type)
      (HR : R.HonestB A W0 Wj W0' Wj') (HQ : Q.Honest W0' Wj')
      (Ri : X → (E0.prod Ej).Str → W0 × Wj → Prop)
      (Ro : X' → (E0'.prod Ej').Str → W0' × Wj' → Prop),
    HR.AccB Ri Ro → HQ.Acc Ro → (HR.seqB HQ).Acc Ri

/-- Honest-verifier exact zero knowledge of "a link, then a batch IOP", for sets of slots, with
further reads. -/
def exact_seqB : Prop :=
  ∀ (X X' : Type) (E0 Ej E0' Ej' : ExtSpec) (R : IOR X (E0.prod Ej) X' (E0'.prod Ej'))
      (A : RoundSplits R.shape) (Q : BIOP X' (E0'.prod Ej')) (W0 Wj W0' Wj' : Type)
      (HR : R.HonestB A W0 Wj W0' Wj') (HQ : Q.Honest W0' Wj')
      (Ri : X → (E0.prod Ej).Str → W0 × Wj → Prop) (Ro : X' → (E0'.prod Ej').Str → W0' × Wj' → Prop)
      (N : ℕ) (bR : BudB R.shape N) (bQ : BudB Q.ior.shape N) (f : W0' → E0'.Str),
    R.IsLocal → HR.AccB Ri Ro → (∀ x y w, Ro x y w → y.1 = f w.1) →
    HR.ExactB N Ri bR → HQ.Exact N Ro bQ → (HR.seqB HQ).Exact N Ri (budSeqB R Q bR bQ)

/-- Completeness of an IOP in every slot. -/
def acc_localB : Prop :=
  ∀ (X : Type) (E0 Ej : ExtSpec) (B : IOR X (E0.prod Ej) Unit extNone) (Wi W0 Wj : Type)
      (H : B.Honest Wi Unit) (mk : W0 → Wj → Wi) (Ri : X → (E0.prod Ej).Str → Wi → Prop),
    H.Acc Ri IOR.triv → (∀ w x, H.Hid w x = ∅) →
    (localH H mk).Acc (fun x y w => Ri x y (mk w.1 w.2))

/-- Honest-verifier exact zero knowledge of an IOP in every slot: the budget is asked of each
slot. (not all hypotheses are named here: see the statement below) -/
def exact_localB : Prop :=
  ∀ (X : Type) (E0 Ej : ExtSpec) (B : IOR X (E0.prod Ej) Unit extNone) (Wi W0 Wj : Type)
      (H : B.Honest Wi Unit) (mk : W0 → Wj → Wi) (Ri : X → (E0.prod Ej).Str → Wi → Prop)
      (bud : Rho B.shape → Finset (OPos B.shape) → Prop) (N : ℕ),
    H.Exact Ri bud → (∀ w x, H.Hid w x = ∅) →
    (localH H mk).Exact N (fun x y w => Ri x y (mk w.1 w.2))
      (fun J ρs Ts => ∀ j : J, bud (ρs j) (Ts j))

/-- Completeness of an IOR run by the shared part alone, from completeness for one instance. (not
all hypotheses are named here: see the statement below) H is the honest side for one instance;
asked: on valid inputs its transcript is that of the shared strategy, and its results are those of
the link. -/
def accB_shared : Prop :=
  ∀ (X X' : Type) (E0 Ej Eo : ExtSpec) (R : IOR X (E0.prod Ej) X' Eo)
      (Wi Wo W0 Wj W0' Wj' : Type) (H : R.Honest Wi Wo) (s0 : W0 → H.Coin → Strat R.shape W0')
      (nx : X → Wj → X' × Wj') (mk : W0 → Wj → Wi) (mk' : W0' → Wj' → Wo)
      (Ri : X → (E0.prod Ej).Str → Wi → Prop) (Ro : X' → Eo.Str → Wo → Prop),
    H.Acc Ri Ro → (∀ w x, H.Hid w x = ∅) →
    (∀ x y w0 wj c ρ, Ri x y (mk w0 wj) →
      (H.strat (mk w0 wj) x c).run ρ =
        (((s0 w0 c).run ρ).1, ((nx x wj).1, mk' ((s0 w0 c).run ρ).2 (nx x wj).2))) →
    (sharedH R H.Coin s0 nx H.Bad).AccB
      (fun x y w => Ri x y (mk w.1 w.2)) (fun x y w => Ro x y (mk' w.1 w.2))

open Classical in
/-- Honest-verifier exact zero knowledge of an IOR run by the shared part alone. (not all
hypotheses are named here: see the statement below) All slots see one transcript. Asked: the
verifier reads, and the prover's oracles are tied to, shared oracles only; the budget is asked at
the union of the further positions of the slots of J. -/
def exactB_shared : Prop :=
  ∀ (X X' : Type) (E0 Ej Eo : ExtSpec) (R : IOR X (E0.prod Ej) X' Eo) (Wi Wo W0 Wj W0' Wj' : Type)
      (H : R.Honest Wi Wo) (s0 : W0 → H.Coin → Strat R.shape W0') (nx : X → Wj → X' × Wj')
      (mk : W0 → Wj → Wi) (Ri : X → (E0.prod Ej).Str → Wi → Prop)
      (bud : Rho R.shape → Finset (OPos R.shape) → Prop) (N : ℕ),
    H.Exact Ri bud → (∀ w x, H.Hid w x = ∅) →
    (∀ x y w0 wj c ρ,
      Ri x y (mk w0 wj) → ((H.strat (mk w0 wj) x c).run ρ).1 = ((s0 w0 c).run ρ).1) →
    (∀ ρ q, q ∈ R.extReads ρ → q.isLeft = true) → (∀ ρ p q, q ∈ R.tie ρ p → q.isLeft = true) →
    (sharedH (Wj' := Wj') R H.Coin s0 nx H.Bad).ExactB N (fun x y w => Ri x y (mk w.1 w.2))
      (fun J ρs Ts => ∀ j : J, bud (ρs j) (Finset.univ.biUnion Ts))

end Spec
end Iop
