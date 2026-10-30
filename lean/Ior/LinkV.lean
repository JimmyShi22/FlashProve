-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/LinkV.lean: the honest side of chains of batch links, over any implicit instance: vectors of
statements tied by the shared witness.

In standard terms: the honest prover's side of a sequential composition of interactive oracle
reductions that run on a batch of instances, whatever the form of their oracles.

Definitions and statements; the proofs are in Ior/LinkVSeq.lean (a link, then a link) and
Ior/LinkVRules.lean (the other rules). No protocol occurs here.

A statement has an explicit part, which the verifier holds, and an implicit part (the implicit
instance): oracles that it reads by queries. A slot is one of the N places of a batch; the
statements here speak of a set J of slots, each with one instance.

Why: Ior/BatchSeqZk.lean has the honest side of one link of a batch IOP (who speaks, which
verifier messages are shared; completeness for each slot; honest-verifier exact zero knowledge for
sets of slots with further reads) and rules for chains. It asks that the implicit instance at
every joint has the form (shared oracles, the slot's own oracles), knows "a link, then a batch
IOP" only, and lets a silent slot end with a result that no verifier message enters. A chain of
blocks that send oracle messages one after the other leaves nested products in the order of
sending, shared and own oracles mixed; and after a shared round the slot's new explicit part holds
the shared challenge and what the shared part answered. Soundness of such chains is stated for
admissible vectors of statements (Ior/BatchSeq.lean: `KnowB`). Here is the analogue for the honest
side.

A link is an IOR R from statements (x; y), y of any kind of oracles, with an annotation A of its
shape.

Main names:
  `R.HonestV A W0 Wj W0' Wj'`: its honest side: field for field `IOR.HonestB`. By type the shared
    part is a function of the shared witness W0, coins of its own and the shared verifier
    messages, and ends with the next shared witness; a slot's part sees these, its instance, its
    witness, its coins and the verifier messages of its local transcript, and ends with (the
    explicit part that it expects, its next witness).
  `AccV Ri Ro`: completeness for each slot; the relations are on (x; y; (shared witness, slot's
    witness)).
  `ExactV N Ri bud`: honest-verifier exact zero knowledge for sets of slots, with further reads:
    for every shared witness w0, every set J of slots and every family (x_j, y_j, w_j), j in J,
    with Ri x_j y_j (w0, w_j): at every ρ and every family of further positions within the budget,
    the views of the slots of J (`output`: a slot that the link withholds shows the notice
    (`none`)) have exactly the law that one simulator writes, which is given J, the x_j, the
    verifier messages, the further positions, and slot by slot the symbols of y_j at the positions
    `given`. What the slots share is said by Ri through w0, not by the form of y.
The rules, each under the hypotheses of its statement:
  `acc_seqV`, `exact_seqV`: a link, then a link (`H₁.seqV H₂`) is a link; the budget is `budSeqV`
    (as `budSeqB`). Asked beside the two properties: the first link is local and complete. (No
    "the relation determines the shared oracles": the second link's property speaks of all
    families.)
  `accV_local`, `exactV_local`: an IOR in every slot, in local rounds in which only the slot
    speaks (`H.localV`), from completeness and honest-verifier exact zero knowledge for one
    instance (`Honest.Acc`, `Honest.Exact`, Ior/Honest.lean). The slots are independent; the
    budget is asked of each slot.
  `accV_shared`, `exactV_shared`: an IOR run by the shared part alone, or by nobody, under shared
    verifier messages (`H.sharedV s0`), from its properties for one instance. s0 is the shared
    part's strategy, a function of the shared witness and the shared coins. The slot is silent and
    recomputes its result from the one-instance honest prover on its own witness and the shared
    coins; so its new explicit part and witness may hold shared challenges and shared answers.
    Asked: on inputs in the link's relation the one-instance prover's transcript is that of s0;
    for honest-verifier zero knowledge also: the symbols that the simulator is given are
    determined by the shared witness (it reads and ties shared oracles only). All slots see one
    transcript; the budget is asked at the union of the further positions.
  `acc_toB`, `exact_toB`: the bridge: a link to the trivial statement whose input has the form
    (shared oracles, own oracles) is a batch IOP of Ior/Batch.lean with `BIOP.Honest.Acc` and
    `BIOP.Honest.Exact` (`H.toB mk`).

Limits:
Declared. (1) On paper the real experiment runs ALL instances of the batch and shows the part of
the set J. Here "output" runs the slots of J alone. The two are equal because, by type, the shared
part is a function of the shared witness, its own coins and the shared verifier messages, and a
slot's part does not see another slot.
(2) A slot's part sees the shared witness and the shared coins (`strat w0 c0 x wj c`): an
instance's own test on a shared oracle needs that oracle's message and encoding randomness. When
this file was written this was our reading: the written description then said of what the shared
messages are functions and was silent on an instance's. A later edition says it so: an instance's
messages are functions of the prover encoded index, the instance's input, the shared messages with
the randomness from which they are encoded, and fresh randomness.
This file says nothing on soundness; nothing on running times (simulators take transcripts that
fit a view by choice). There is no Hid in a link (`Honest.Hid`, Ior/Honest.lean).

Terms: lean/GLOSSARY.md.
-/
import Ior.BatchSeqZk
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

/-! ## 1. Strategies with results -/

namespace SStratR

/-- The shared part goes on with its result, to a further result. -/
def bindR :
    {s t : Shape} → {A : RoundSplits s} → {B : RoundSplits t} → {β γ : Type} → SStratR s A β →
    (β → SStratR t B γ) → SStratR (s ++ t) (RoundSplits.app A B) γ
  | [], _, _, _, _, _, b, g => g b
  | _ :: _, _, (_, _), _, _, _, (m, k), g => (m, fun c => bindR (k c) g)

/-- The shared part is silent where only the slots speak, and ends with b. -/
def silentR : (s : Shape) → {β : Type} → β → SStratR s (RoundSplits.allLocal s) β
  | [], _, b => b
  | _ :: s, _, b => ((), fun _ => silentR s b)

/-- The result dropped. -/
def forget : {s : Shape} → {A : RoundSplits s} → {β : Type} → SStratR s A β → SStrat s A
  | [], _, _, _ => ()
  | _ :: _, (_, _), _, (m, k) => (m, fun c => forget (k c))

end SStratR

namespace LStratR

/-- A slot's part goes on with its result, to a further result. -/
def bindR :
    {s t : Shape} → {A : RoundSplits s} → {B : RoundSplits t} → {β γ : Type} → LStratR s A β →
    (β → LStratR t B γ) → LStratR (s ++ t) (RoundSplits.app A B) γ
  | [], _, _, _, _, _, b, g => g b
  | _ :: _, _, (_, _), _, _, _, (m, k), g => (m, fun c => bindR (k c) g)

/-- Local rounds in which only the slot speaks: a strategy as a slot's part. -/
def ofStrat : {s : Shape} → {β : Type} → Strat s β → LStratR s (RoundSplits.allLocal s) β
  | [], _, b => b
  | _ :: _, _, (m, k) => (m, fun c => ofStrat (k c))

/-- The slot is silent where only the shared part speaks; its result is a function of the verifier
messages. -/
def muteF : (s : Shape) → {β : Type} → (Rho s → β) → LStratR s (RoundSplits.const (RAnn.ofShared .sh) s) β
  | [], _, f => f ()
  | _ :: s, _, f => ((), fun c => muteF s fun ρ => f (c, ρ))

/-- The result dropped. -/
def forget : {s : Shape} → {A : RoundSplits s} → {β : Type} → LStratR s A β → LStrat s A
  | [], _, _, _ => ()
  | _ :: _, (_, _), _, (m, k) => (m, fun c => forget (k c))

end LStratR

/-! ## 2. A link and its honest side -/

namespace IOR
variable {X X' X'' : Type} {Ei Eo Eo' : ExtSpec}

/-- The honest side of a link, over any implicit instance. -/
structure HonestV (R : IOR X Ei X' Eo) (A : RoundSplits R.shape) (W0 Wj W0' Wj' : Type) where
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

attribute [instance] HonestV.finCoin0 HonestV.neCoin0 HonestV.finCoin HonestV.neCoin

/-- The type of a simulator of a link, for sets of slots. -/
abbrev SimV (R : IOR X Ei X' Eo) (N : ℕ) : Type :=
  (J : Finset (Fin N)) → (J → X) → (J → Rho R.shape) → (J → Finset (OPos R.shape)) →
  (J → Ei.Pos → Option Ei.Sym) → PMF (J → Option (View R))

namespace HonestV
variable {R : IOR X Ei X' Eo} {A : RoundSplits R.shape} {W0 Wj W0' Wj' : Type}

/-- the withheld set of a slot: public -/
def withheld (H : R.HonestV A W0 Wj W0' Wj') : Set (Rho R.shape) :=
  {ρ | Rho.lo A ρ ∈ H.Bad ∨ H.stop0 (Rho.sh A ρ) = true}

/-- the honest prover on the local transcript of one slot -/
def one (H : R.HonestV A W0 Wj W0' Wj') (w0 : W0) (x : X) (wj : Wj) (c : H.Coin0 × H.Coin) :
    Strat R.shape (W0' × X' × Wj') :=
  (H.strat0 w0 c.1).zip (H.strat w0 c.1 x wj c.2)

/-- Completeness for each slot. -/
def AccV (H : R.HonestV A W0 Wj W0' Wj') (Ri : X → Ei.Str → W0 × Wj → Prop)
    (Ro : X' → Eo.Str → W0' × Wj' → Prop) : Prop :=
  ∀ x y w c ρ, Ri x y w → ρ ∉ H.withheld →
    R.out x y ((H.one w.1 x w.2 c).run ρ).1 = some ((H.one w.1 x w.2 c).run ρ).2.2.1 ∧
    Ro ((H.one w.1 x w.2 c).run ρ).2.2.1 (R.imp y ((H.one w.1 x w.2 c).run ρ).1)
      (((H.one w.1 x w.2 c).run ρ).2.1, ((H.one w.1 x w.2 c).run ρ).2.2.2)

open Classical in
/-- The output for the set J of slots at ρ, with the further positions Ts; `as j` holds the
instance and the witness of slot j. -/
def output (H : R.HonestV A W0 Wj W0' Wj') {N : ℕ} (w0 : W0) (J : Finset (Fin N))
    (as : J → X × Wj) (ρ : BRho N R.shape A) (Ts : J → Finset (OPos R.shape)) :
    PMF (J → Option (View R)) :=
  (unif (H.Coin0 × (Fin N → H.Coin))).map fun c => fun j =>
    if ρ.slot j.1 ∈ H.withheld then none
    else some (R.view (Ts j) ((H.one w0 (as j).1 (as j).2 (c.1, c.2 j.1)).run (ρ.slot j.1)).1)

/-- Honest-verifier exact zero knowledge for sets of slots, with further reads, the simulator
named. -/
def ExactVWith (H : R.HonestV A W0 Wj W0' Wj') (N : ℕ) (Ri : X → Ei.Str → W0 × Wj → Prop)
    (bud : BudB R.shape N) (Sim : R.SimV N) : Prop :=
  ∀ (w0 : W0) (J : Finset (Fin N)) (as : J → X × Ei.Str × Wj),
    (∀ j, Ri (as j).1 (as j).2.1 (w0, (as j).2.2)) →
    ∀ (ρ : BRho N R.shape A) (Ts : J → Finset (OPos R.shape)), bud J (fun j => ρ.slot j.1) Ts →
      H.output w0 J (fun j => ((as j).1, (as j).2.2)) ρ Ts =
        Sim J (fun j => (as j).1) (fun j => ρ.slot j.1) Ts
          (fun j => Ei.ans (R.given (ρ.slot j.1) (Ts j)) (as j).2.1)

def ExactV (H : R.HonestV A W0 Wj W0' Wj') (N : ℕ)
    (Ri : X → Ei.Str → W0 × Wj → Prop) (bud : BudB R.shape N) : Prop :=
  ∃ Sim : R.SimV N, H.ExactVWith N Ri bud Sim

end HonestV

/-! ## 3. A link, then a link -/

/-- A link, then a link: the honest side. The coins are independent. A slot goes on with the
shared part's result, which it computes for itself. -/
def HonestV.seqV {R₁ : IOR X Ei X' Eo} {R₂ : IOR X' Eo X'' Eo'} {A₁ : RoundSplits R₁.shape}
    {A₂ : RoundSplits R₂.shape} {W0 Wj W0' Wj' W0'' Wj'' : Type} (H₁ : R₁.HonestV A₁ W0 Wj W0' Wj')
    (H₂ : R₂.HonestV A₂ W0' Wj' W0'' Wj'') :
    (R₁.seq R₂).HonestV (RoundSplits.app A₁ A₂) W0 Wj W0'' Wj'' where
  Coin0 := H₁.Coin0 × H₂.Coin0
  Coin := H₁.Coin × H₂.Coin
  strat0 := fun w0 c0 => (H₁.strat0 w0 c0.1).bindR fun w0' => H₂.strat0 w0' c0.2
  strat := fun w0 c0 x wj c =>
    ((H₁.strat0 w0 c0.1).along (H₁.strat w0 c0.1 x wj c.1)).bindR fun o =>
      H₂.strat o.1 c0.2 o.2.1 o.2.2 c.2
  Bad := {l | RhoLo.fstA A₁ A₂ l ∈ H₁.Bad} ∪ {l | RhoLo.sndA A₁ A₂ l ∈ H₂.Bad}
  stop0 := fun σ => H₁.stop0 (RhoSh.fstA A₁ A₂ σ) || H₂.stop0 (RhoSh.sndA A₁ A₂ σ)

/-- The budget of the composition. The first link bears, as a family over J: the part of T_j in
its shape together with the sources of all that the second simulator is given in slot j. The
second bears the parts in its shape, as a family, for every subset of J. -/
def budSeqV (R₁ : IOR X Ei X' Eo) (R₂ : IOR X' Eo X'' Eo') {N : ℕ}
    (b₁ : BudB R₁.shape N) (b₂ : BudB R₂.shape N) :
    BudB (R₁.shape ++ R₂.shape) N := fun J ρs Ts =>
  b₁ J (fun j => Rho.fst (ρs j)) (fun j => firstT R₁ R₂ (ρs j) (Ts j)) ∧
  ∀ (J' : Finset (Fin N)) (h : J' ⊆ J), b₂ J' (fun j => Rho.snd (s := R₁.shape) (ρs ⟨j.1, h j.2⟩))
    (fun j => partR R₁.shape (Ts ⟨j.1, h j.2⟩))

/-! ## 4. An IOR in every slot; an IOR run by the shared part alone -/

/-- An IOR in every slot: local rounds in which only the slot speaks. The slot's witness is the
witness for one instance; the shared witness is handed on. -/
def Honest.localV {R : IOR X Ei X' Eo} {Wi Wo : Type} (H : R.Honest Wi Wo) (W0 : Type) :
    R.HonestV (RoundSplits.allLocal R.shape) W0 Wi W0 Wo where
  Coin0 := Unit
  Coin := H.Coin
  strat0 := fun w0 _ => SStratR.silentR R.shape w0
  strat := fun _ _ x wi c => LStratR.ofStrat (H.strat wi x c)
  Bad := {l | RhoLo.all R.shape l ∈ H.Bad}
  stop0 := fun _ => false

open Classical in
/-- An IOR run by the shared part alone (or by nobody), under shared verifier messages. s0 is the
shared part's strategy. The slot is silent, and ends with the result of the honest prover for one
instance on its own witness and the shared coins. -/
def Honest.sharedV {R : IOR X Ei X' Eo} {Wi Wo W0 W0' : Type} (H : R.Honest Wi Wo)
    (s0 : W0 → H.Coin → Strat R.shape W0') :
    R.HonestV (RoundSplits.const (RAnn.ofShared .sh) R.shape) W0 Wi W0' Wo where
  Coin0 := H.Coin
  Coin := Unit
  strat0 := fun w0 c => SStratR.ofStrat (s0 w0 c)
  strat := fun _ c x wi _ => LStratR.muteF R.shape fun ρ => ((H.strat wi x c).run ρ).2
  Bad := ∅
  stop0 := fun σ => decide (RhoSh.all R.shape σ ∈ H.Bad)

/-! ## 5. The bridge to batch IOPs -/

/-- A link to the trivial statement as a batch IOP's honest side. mk puts the link's slot witness
together. -/
def HonestV.toB {E0 Ej : ExtSpec} {R : IOR X (E0.prod Ej) Unit extNone} {A : RoundSplits R.shape}
    {W0 Wi Wj W0' Wo : Type} (H : R.HonestV A W0 Wi W0' Wo) (mk : W0 → Wj → Wi) :
    (⟨R, A⟩ : BIOP X (E0.prod Ej)).Honest W0 Wj where
  Coin0 := H.Coin0
  Coin := H.Coin
  strat0 := fun w0 c0 => (H.strat0 w0 c0).forget
  strat := fun w0 c0 x wj c => (H.strat w0 c0 x (mk w0 wj) c).forget
  Bad := H.Bad
  stop0 := H.stop0

end IOR

/-! ## 6. Statements -/

namespace Spec
open IOR

/-- Completeness of "a link, then a link". -/
def acc_seqV : Prop :=
  ∀ (X X' X'' : Type) (Ei Eo Eo' : ExtSpec) (R₁ : IOR X Ei X' Eo) (R₂ : IOR X' Eo X'' Eo')
      (A₁ : RoundSplits R₁.shape) (A₂ : RoundSplits R₂.shape) (W0 Wj W0' Wj' W0'' Wj'' : Type)
      (H₁ : R₁.HonestV A₁ W0 Wj W0' Wj') (H₂ : R₂.HonestV A₂ W0' Wj' W0'' Wj'')
      (Ra : X → Ei.Str → W0 × Wj → Prop) (Rb : X' → Eo.Str → W0' × Wj' → Prop)
      (Rc : X'' → Eo'.Str → W0'' × Wj'' → Prop),
    H₁.AccV Ra Rb → H₂.AccV Rb Rc → (H₁.seqV H₂).AccV Ra Rc

/-- Honest-verifier exact zero knowledge of "a link, then a link", for sets of slots, with further
reads. -/
def exact_seqV : Prop :=
  ∀ (X X' X'' : Type) (Ei Eo Eo' : ExtSpec) (R₁ : IOR X Ei X' Eo) (R₂ : IOR X' Eo X'' Eo')
      (A₁ : RoundSplits R₁.shape) (A₂ : RoundSplits R₂.shape) (W0 Wj W0' Wj' W0'' Wj'' : Type)
      (H₁ : R₁.HonestV A₁ W0 Wj W0' Wj') (H₂ : R₂.HonestV A₂ W0' Wj' W0'' Wj'')
      (Ra : X → Ei.Str → W0 × Wj → Prop) (Rb : X' → Eo.Str → W0' × Wj' → Prop) (N : ℕ)
      (b₁ : BudB R₁.shape N) (b₂ : BudB R₂.shape N),
    R₁.IsLocal → H₁.AccV Ra Rb → H₁.ExactV N Ra b₁ → H₂.ExactV N Rb b₂ →
    (H₁.seqV H₂).ExactV N Ra (budSeqV R₁ R₂ b₁ b₂)

/-- Completeness of an IOR in every slot. (not all hypotheses are named here: see the statement
below) RiV, RoV: the link's relations; they say, beside the relations for one instance, how the
slot's witness is tied to the shared witness; the tie is to be carried along honest runs. -/
def accV_local : Prop :=
  ∀ (X X' : Type) (Ei Eo : ExtSpec) (R : IOR X Ei X' Eo) (Wi Wo W0 : Type) (H : R.Honest Wi Wo)
      (Ri : X → Ei.Str → Wi → Prop) (Ro : X' → Eo.Str → Wo → Prop)
      (RiV : X → Ei.Str → W0 × Wi → Prop) (RoV : X' → Eo.Str → W0 × Wo → Prop),
    H.Acc Ri Ro → (∀ w x, H.Hid w x = ∅) → (∀ x y w, RiV x y w → Ri x y w.2) →
    (∀ x y w c ρ, RiV x y w → ρ ∉ H.Bad →
      Ro ((H.strat w.2 x c).run ρ).2.1 (R.imp y ((H.strat w.2 x c).run ρ).1)
        ((H.strat w.2 x c).run ρ).2.2 →
      RoV ((H.strat w.2 x c).run ρ).2.1 (R.imp y ((H.strat w.2 x c).run ρ).1)
        (w.1, ((H.strat w.2 x c).run ρ).2.2)) →
    (H.localV W0).AccV RiV RoV

/-- Honest-verifier exact zero knowledge of an IOR in every slot: the budget is asked of each
slot. (not all hypotheses are named here: see the statement below) -/
def exactV_local : Prop :=
  ∀ (X X' : Type) (Ei Eo : ExtSpec) (R : IOR X Ei X' Eo) (Wi Wo W0 : Type) (H : R.Honest Wi Wo)
      (Ri : X → Ei.Str → Wi → Prop) (RiV : X → Ei.Str → W0 × Wi → Prop)
      (bud : Rho R.shape → Finset (OPos R.shape) → Prop) (N : ℕ),
    H.Exact Ri bud → (∀ w x, H.Hid w x = ∅) → (∀ x y w, RiV x y w → Ri x y w.2) →
    (H.localV W0).ExactV N RiV (fun J ρs Ts => ∀ j : J, bud (ρs j) (Ts j))

/-- Completeness of an IOR run by the shared part alone. -/
def accV_shared : Prop :=
  ∀ (X X' : Type) (Ei Eo : ExtSpec) (R : IOR X Ei X' Eo) (Wi Wo W0 W0' : Type)
      (H : R.Honest Wi Wo) (s0 : W0 → H.Coin → Strat R.shape W0')
      (Ri : X → Ei.Str → Wi → Prop) (Ro : X' → Eo.Str → Wo → Prop)
      (RiV : X → Ei.Str → W0 × Wi → Prop) (RoV : X' → Eo.Str → W0' × Wo → Prop),
    H.Acc Ri Ro → (∀ w x, H.Hid w x = ∅) → (∀ x y w, RiV x y w → Ri x y w.2) →
    (∀ x y w c ρ, RiV x y w → ((H.strat w.2 x c).run ρ).1 = ((s0 w.1 c).run ρ).1) →
    (∀ x y w c ρ, RiV x y w → ρ ∉ H.Bad →
      Ro ((H.strat w.2 x c).run ρ).2.1 (R.imp y ((H.strat w.2 x c).run ρ).1)
        ((H.strat w.2 x c).run ρ).2.2 →
      RoV ((H.strat w.2 x c).run ρ).2.1 (R.imp y ((H.strat w.2 x c).run ρ).1)
        (((s0 w.1 c).run ρ).2, ((H.strat w.2 x c).run ρ).2.2)) →
    (H.sharedV s0).AccV RiV RoV

open Classical in
/-- Honest-verifier exact zero knowledge of an IOR run by the shared part alone. (not all
hypotheses are named here: see the statement below) All slots see one transcript. Asked: the
symbols that the simulator is given are determined by the shared witness (f); the budget is asked
at the union of the further positions of the slots of J. -/
def exactV_shared : Prop :=
  ∀ (X X' : Type) (Ei Eo : ExtSpec) (R : IOR X Ei X' Eo) (Wi Wo W0 W0' : Type) (H : R.Honest Wi Wo)
      (s0 : W0 → H.Coin → Strat R.shape W0') (Ri : X → Ei.Str → Wi → Prop)
      (RiV : X → Ei.Str → W0 × Wi → Prop) (bud : Rho R.shape → Finset (OPos R.shape) → Prop)
      (N : ℕ) (f : W0 → Ei.Pos → Ei.Sym),
    H.Exact Ri bud → (∀ w x, H.Hid w x = ∅) → (∀ x y w, RiV x y w → Ri x y w.2) →
    (∀ x y w c ρ, RiV x y w → ((H.strat w.2 x c).run ρ).1 = ((s0 w.1 c).run ρ).1) →
    (∀ x y w ρ T p, RiV x y w → p ∈ R.given ρ T → Ei.rd y p = f w.1 p) →
    (H.sharedV s0).ExactV N RiV (fun J ρs Ts => ∀ j : J, bud (ρs j) (Finset.univ.biUnion Ts))

/-- The bridge: completeness. -/
def acc_toB : Prop :=
  ∀ (X : Type) (E0 Ej : ExtSpec) (R : IOR X (E0.prod Ej) Unit extNone) (A : RoundSplits R.shape)
      (W0 Wi Wj W0' Wo : Type) (H : R.HonestV A W0 Wi W0' Wo) (mk : W0 → Wj → Wi)
      (RiV : X → (E0.prod Ej).Str → W0 × Wi → Prop) (RoV : Unit → extNone.Str → W0' × Wo → Prop),
    H.AccV RiV RoV → (H.toB mk).Acc (fun x y w => RiV x y (w.1, mk w.1 w.2))

/-- The bridge: honest-verifier exact zero knowledge, same budget. -/
def exact_toB : Prop :=
  ∀ (X : Type) (E0 Ej : ExtSpec) (R : IOR X (E0.prod Ej) Unit extNone) (A : RoundSplits R.shape)
      (W0 Wi Wj W0' Wo : Type) (H : R.HonestV A W0 Wi W0' Wo) (mk : W0 → Wj → Wi)
      (RiV : X → (E0.prod Ej).Str → W0 × Wi → Prop) (N : ℕ) (bud : BudB R.shape N),
    H.ExactV N RiV bud → (H.toB mk).Exact N (fun x y w => RiV x y (w.1, mk w.1 w.2)) bud

end Spec
end Iop
