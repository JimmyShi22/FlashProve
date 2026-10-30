-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/More.lean: further reads of the prover's oracles as one more round.

In standard terms: a transformation of an interactive oracle reduction that adds one round, in
which the prover sends nothing and the verifier draws one more message.

Definitions, and the statements of the rules (proofs: Ior/MoreProofs.lean).

A statement has an explicit part, which the verifier holds, and an implicit part (below: the
implicit instance): oracles that it reads by queries. A batch IOP (`BIOP`, Ior/Batch.lean) runs N
slots together, each with one instance or empty: in a shared round one verifier message goes to
all slots, in a local round each slot gets its own.

Why: The zero-knowledge notion of a print of this protocol's technical report
(lean/CREDITS.md) lets a distinguisher read every oracle that the prover sent at further uniform
positions. The exact notion of Ior/Honest.lean and
Ior/Batch.lean has these reads as "a set T within a budget"; the interface to the compiler
(`Iop.BatchProtocol`) shows, of a blinded oracle, the verifier's reads only. Here the further reads are made
the verifier's: `R.more D plan` is R with one more round, in which the prover sends the empty
message and the verifier message is a uniform d in a finite set D of read plans; the verifier
reads what R's verifier reads, the positions plan d of the prover's oracles, and all positions of
the implicit instance that are tied to these; it decides as R's verifier does, so, if R is local
(`IOR.IsLocal`, Ior/Ior.lean), it ignores what it reads beyond R's positions. The disclosed view
of a run of `R.more` at (d, ρ) then holds the symbols at plan d. (t uniform positions of an
oracle: D = the t-tuples of its positions, plan = the set of the entries. Any finite non-empty D
and any map plan are allowed.)

The new round stands first, because on "r :: s" the notions over a shape (`Tr`, `Rho`, `OPos`,
`Strat`: Iop/Shape.lean) unfold by definition. What a run of `R.more` shows is proved, and does
not speak of the place of the round: at the verifier's randomness (d, ρ) the output of `R.more`'s
honest side is exactly the output of R's honest side at ρ with the further positions plan d (and
T), in the new format (`Spec.output_more`; for sets of slots `Spec.outputT_more`). (These
statements are pointwise in (d, ρ). That in an execution d is uniform and independent of ρ is the
definition of the verifier's randomness of the shape "ask :: s", the uniform law on D × Rho s;
that it is independent of the prover's coins is the definition of the output, whose coins are
drawn after (d, ρ) is fixed.) The honest prover ignores d (the terms `Honest.more`, `moreHonest`:
"fun _ => .."); no verifier's decision reads d or, for a local R, what is read at plan d beyond
R's positions, and the new round has error 0 (`Spec.know_more`).

What is stated. What a run shows (above). Locality, knowledge soundness, completeness are kept
(`Spec.isLocal_more`, `Spec.know_more`, `Spec.acc_more`); the verifier of `R.more` reads all that
is tied to its positions, by construction (`Spec.tied_more`); honest-verifier exact zero knowledge
of R at the budget bud gives honest-verifier exact zero knowledge of `R.more` at the budget "bud
bears plan d and T" (`Spec.exact_more`); the same for a batch IOP over one shared oracle
(`Spec.exactT_more`), where the new round is local: each slot has a plan of its own, for the
oracles of its local transcript (the shared part's and its own); and, under the hypotheses of
their statements, both in the form of the interface to the compiler (`Spec.hvzk_more`,
`hvzkB_more`), with the errors of R (for a set J of slots: |J| z, see its statement).

Limits: not defined and not proved here: the variant with the new round in the last place, and
that its views have the same law up to the order of the components.
Mind: (a) the plan is fixed before anything of the run is shown: it may not depend on the run's
view. This is what the exact notion allows: T is an argument of the output.
(b) What the simulator is given of the implicit instance, and so what counts in the budget of an
encoded index, are the verifier's positions and those tied to the verifier's positions in the
prover's oracles and to the plan (`IOR.given`): they are the `extReads` of `R.more`. (With further
positions T: `IOR.given_more`, Ior/MoreProofs.lean.)
This file says nothing on batches' soundness (Snd-B) for `Q.more`.

Terms: lean/GLOSSARY.md.
-/
import Ior.Batch
import Ior.ToProto
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

/-- The round of the read plans: the prover sends nothing; the verifier message is uniform in D. -/
def askRound (D : Type) [Fintype D] [Nonempty D] : Round where
  Orc := Unit
  Pos := Empty
  Sym := fun _ => Unit
  rd := fun _ _ => ()
  Plain := Unit
  Chal := D
  dOrc := ()
  dPlain := ()

/-- The part of a set of positions of "ask :: s" that lies in s (all of it: the new round has no
oracle). -/
def OPos.tail {D : Type} [Fintype D] [Nonempty D]
    {s : Shape} (T : Finset (OPos (askRound D :: s))) : Finset (OPos s) :=
  Finset.preimage (α := OPos s) (β := Empty ⊕ OPos s) T Sum.inr Sum.inr_injective.injOn

namespace IOR
variable {Xi Xo X : Type} {Ei Eo E : ExtSpec} (D : Type) [Fintype D] [Nonempty D]

open Classical in
/-- R with further reads by plan. -/
def more (R : IOR Xi Ei Xo Eo) (plan : D → Finset (OPos R.shape)) :
    IOR Xi Ei Xo Eo where
  shape := askRound D :: R.shape
  blinded := fun (p : Empty ⊕ OPos R.shape) => match p with
    | .inl e => e.elim
    | .inr p => R.blinded p
  extReads := fun (ρ : D × Rho R.shape) => R.given ρ.2 (plan ρ.1)
  reads := fun (ρ : D × Rho R.shape) =>
    Finset.image (α := OPos R.shape) (β := Empty ⊕ OPos R.shape) Sum.inr (R.reads ρ.2 ∪ plan ρ.1)
  out := fun x y (τ : (Unit × Unit) × D × Tr R.shape) => R.out x y τ.2.2
  imp := fun y (τ : (Unit × Unit) × D × Tr R.shape) => R.imp y τ.2.2
  srcE := fun (ρ : D × Rho R.shape) q => R.srcE ρ.2 q
  srcO := fun (ρ : D × Rho R.shape) q =>
    Finset.image (α := OPos R.shape) (β := Empty ⊕ OPos R.shape) Sum.inr (R.srcO ρ.2 q)
  tie := fun (ρ : D × Rho R.shape) (p : Empty ⊕ OPos R.shape) => match p with
    | .inl e => e.elim
    | .inr p => R.tie ρ.2 p

variable {D}
variable {R : IOR Xi Ei Xo Eo} {Wi Wo : Type}

/-- The honest side: the empty message, then the honest prover of R, whatever d is. Withheld is
what R's honest side withholds. -/
def Honest.more (H : R.Honest Wi Wo) (plan : D → Finset (OPos R.shape)) :
    (R.more D plan).Honest Wi Wo where
  Coin := H.Coin
  strat := fun w x c => (((), ()), fun _ => H.strat w x c)
  Bad := {ρ : D × Rho R.shape | ρ.2 ∈ H.Bad}
  Hid := fun w x => {ρ : D × Rho R.shape | ρ.2 ∈ H.Hid w x}

/-- What a run of R shows, as what a run of R.more shows. -/
def View.more (plan : D → Finset (OPos R.shape)) (v : View R) : View (R.more D plan) where
  plains := ((), v.plains)
  orc := fun (p : Empty ⊕ OPos R.shape) => match p with
    | .inl e => e.elim
    | .inr p => v.orc p

open Classical in
/-- The simulator: that of R, with plan d among the further positions. -/
def Honest.Sim.more (S : Honest.Sim R) (plan : D → Finset (OPos R.shape)) :
    Honest.Sim (R.more D plan) :=
  fun x (ρ : D × Rho R.shape) T a =>
    (S x ρ.2 (plan ρ.1 ∪ OPos.tail T) a).map (Option.map (View.more plan))

open Classical in
/-- The budget: R's budget bears plan d together with the further positions. -/
def budMore (R : IOR Xi Ei Xo Eo) (plan : D → Finset (OPos R.shape))
    (bud : Rho R.shape → Finset (OPos R.shape) → Prop) :
    Rho (R.more D plan).shape → Finset (OPos (R.more D plan).shape) → Prop :=
  fun (ρ : D × Rho R.shape) T => bud ρ.2 (plan ρ.1 ∪ OPos.tail T)

end IOR

/-- A disclosed view of R's IOP as one of R.more's. -/
def DView.more {X : Type} {E : ExtSpec} {D : Type} [Fintype D] [Nonempty D]
    {R : IOR X E Unit extNone} (plan : D → Finset (OPos R.shape)) (v : DView R.toInteractiveOracleProof) :
    DView (R.more D plan).toInteractiveOracleProof where
  plains := ((), v.plains)
  ext := v.ext
  orc := fun (p : Empty ⊕ OPos R.shape) => match p with
    | .inl e => e.elim
    | .inr p => v.orc p

namespace BIOP
variable {X Wt : Type} {E : ExtSpec} {D : Type} [Fintype D] [Nonempty D]

/-- A batch IOP with further reads by plan: the new round is local, and only the slots "speak" in
it. -/
def more (Q : BIOP X E) (plan : D → Finset (OPos Q.ior.shape)) : BIOP X E where
  ior := Q.ior.more D plan
  ann := (RAnn.ofSlot .lo (askRound D), Q.ann)

/-- The honest side: empty messages, then the honest prover, whatever the plans are. -/
def moreHonest (Q : BIOP X E) (H : BatchHonestProver Q.toBatch Wt) (plan : D → Finset (OPos Q.ior.shape)) :
    BatchHonestProver (Q.more plan).toBatch Wt where
  Coin0 := H.Coin0
  Coin := H.Coin
  ext := H.ext
  strat0 := fun w c0 => ((), fun _ => H.strat0 w c0)
  strat := fun w c0 x c => (((), ()), fun _ => H.strat w c0 x c)
  Bad := {l : D × RhoLo Q.ior.shape Q.ann | l.2 ∈ H.Bad}
  Hid := fun w x => {l : D × RhoLo Q.ior.shape Q.ann | l.2 ∈ H.Hid w x}
  stop0 := fun (σ : Unit × RhoSh Q.ior.shape Q.ann) => H.stop0 σ.2

open Classical in
def SimT.more {Q : BIOP X E} {N : ℕ} (S : Q.SimT N)
    (plan : D → Finset (OPos Q.ior.shape)) : (Q.more plan).SimT N :=
  fun J xs (ρs : J → D × Rho Q.ior.shape) Ts a =>
    (S J xs (fun j => (ρs j).2) (fun j => plan (ρs j).1 ∪ OPos.tail (Ts j)) a).map
      fun o => fun j => (o j).map (DView.more plan)

open Classical in
def budMore (Q : BIOP X E) (plan : D → Finset (OPos Q.ior.shape))
    {N : ℕ} (bud : BudB Q.ior.shape N) :
    BudB (Q.more plan).ior.shape N :=
  fun J (ρs : J → D × Rho Q.ior.shape) Ts =>
    bud J (fun j => (ρs j).2) (fun j => plan (ρs j).1 ∪ OPos.tail (Ts j))

end BIOP

namespace Spec
open IOR

def isLocal_more : Prop :=
  ∀ (Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (D : Type) [Fintype D]
      [Nonempty D] (plan : D → Finset (OPos R.shape)),
    R.IsLocal → (R.more D plan).IsLocal

/-- States: knowledge soundness is kept: same relations, the same extractor on R's part of the
transcript, error 0 in the new round. -/
def know_more : Prop :=
  ∀ (Xi Xo WA WB : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (D : Type) [Fintype D] [Nonempty D]
      (plan : D → Finset (OPos R.shape)) (on : Xi × Ei.Str → Prop) (RA : Xi × Ei.Str → WA → Prop)
      (RB : Xo × Eo.Str → WB → Prop) (ext : Xi × Ei.Str → Tr R.shape → WB → WA) (ε : Err R.shape),
    R.red.Know on RA RB ext ε →
    (R.more D plan).red.Know on RA RB
      (fun a (τ : (Unit × Unit) × D × Tr R.shape) w => ext a τ.2.2 w) ((0, ε) : ℕ × Err R.shape)

def acc_more : Prop :=
  ∀ (Xi Xo Wi Wo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (D : Type) [Fintype D]
      [Nonempty D] (plan : D → Finset (OPos R.shape)) (H : R.Honest Wi Wo)
      (Ri : Xi → Ei.Str → Wi → Prop) (Ro : Xo → Eo.Str → Wo → Prop),
    H.Acc Ri Ro → (H.more plan).Acc Ri Ro

/-- States: the verifier of `R.more` reads all that is tied to its positions. -/
def tied_more : Prop :=
  ∀ (Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (D : Type) [Fintype D]
      [Nonempty D] (plan : D → Finset (OPos R.shape)),
    (R.more D plan).Tied

/-- States: the withheld sets keep their probabilities. -/
def pr_more : Prop :=
  ∀ (D : Type) [Fintype D] [Nonempty D] (s : Shape) (S : Set (Rho s)),
    prRho (s := askRound D :: s) {ρ : D × Rho s | ρ.2 ∈ S} = prRho S

open Classical in
/-- What a run of `R.more` shows: at (d, ρ), what a run of R shows at ρ with the further positions
plan d (and T). -/
def output_more : Prop :=
  ∀ (Xi Xo Wi Wo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (D : Type) [Fintype D] [Nonempty D]
      (plan : D → Finset (OPos R.shape)) (H : R.Honest Wi Wo) (w : Wi) (x : Xi) (d : D)
      (ρ : Rho R.shape) (T : Finset (OPos (askRound D :: R.shape))),
    (H.more plan).output w x ((d, ρ) : D × Rho R.shape) T =
      (H.output w x ρ (plan d ∪ OPos.tail T)).map (Option.map (View.more plan))

open Classical in
/-- The same for a set J of slots: slot j has the plan v j. -/
def outputT_more : Prop :=
  ∀ (X Wt : Type) (E : ExtSpec) (Q : BIOP X E) (D : Type) [Fintype D] [Nonempty D]
      (plan : D → Finset (OPos Q.ior.shape)) (H : BatchHonestProver Q.toBatch Wt) (N : ℕ) (w : Wt)
      (x : Fin N → Option X) (v : Fin N → D) (ρ : BRho N Q.ior.shape Q.ann) (J : Finset (Fin N))
      (Ts : J → Finset (OPos (askRound D :: Q.ior.shape))),
    (Q.more plan).outputT (Q.moreHonest H plan) w x
        ((v, ρ) : (Fin N → D) × BRho N Q.ior.shape Q.ann) J Ts =
      (Q.outputT H w x ρ J fun j => plan (v j.1) ∪ OPos.tail (Ts j)).map fun o =>
        fun j => (o j).map (DView.more plan)

/-- States: honest-verifier exact zero knowledge with further reads is kept, the simulator named
(at the budget `budMore`). -/
def exact_more : Prop :=
  ∀ (Xi Xo Wi Wo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (D : Type) [Fintype D] [Nonempty D]
      (plan : D → Finset (OPos R.shape)) (H : R.Honest Wi Wo) (Ri : Xi → Ei.Str → Wi → Prop)
      (bud : Rho R.shape → Finset (OPos R.shape) → Prop) (S : Honest.Sim R),
    H.ExactWith Ri bud S → (H.more plan).ExactWith Ri (budMore R plan bud) (S.more plan)

/-- The same for sets of slots of a batch IOP over one shared oracle. -/
def exactT_more : Prop :=
  ∀ (X Wt : Type) (E : ExtSpec) (Q : BIOP X E) (D : Type) [Fintype D] [Nonempty D]
      (plan : D → Finset (OPos Q.ior.shape)) (H : BatchHonestProver Q.toBatch Wt) (N : ℕ)
      (valid : Wt → X → Prop) (bud : BudB Q.ior.shape N) (S : Q.SimT N),
    Q.ExactTWith H N valid bud S →
    (Q.more plan).ExactTWith (Q.moreHonest H plan) N valid (Q.budMore plan bud) (S.more plan)

/-- States, under the hypotheses below: in the form of the interface to the compiler: if R is
simulated exactly with further reads and its budget bears every plan, the IOP of `R.more` is
honest-verifier zero-knowledge, with the error of R: the probability of Hid. -/
def hvzk_more : Prop :=
  ∀ (X Wt Wi : Type) (E : ExtSpec) (R : IOR X E Unit extNone) (D : Type) [Fintype D] [Nonempty D]
      (plan : D → Finset (OPos R.shape)) (H : R.Honest Wi Unit) (ext : Wt → E.Str)
      (inp : Wt → X → Wi) (valid : Wt → X → Prop) (Ri : X → E.Str → Wi → Prop)
      (bud : Rho R.shape → Finset (OPos R.shape) → Prop) (z : ℝ≥0∞),
    H.Exact Ri bud → (∀ d ρ, bud ρ (plan d)) → (∀ w x, valid w x → Ri x (ext w) (inp w x)) →
    (∀ w x, valid w x → prRho (H.Hid (inp w x) x) ≤ z) →
    ((H.more plan).toProto ext inp).HVZK valid z

/-- The same for sets of slots: the budget bears every family of plans; the error for a set J of
slots is |J| z, where z bounds the probability of Hid. (not all hypotheses are named here: see the
statement below) -/
def hvzkB_more : Prop :=
  ∀ (X Wt : Type) (E : ExtSpec) (Q : BIOP X E) (D : Type) [Fintype D] [Nonempty D]
      (plan : D → Finset (OPos Q.ior.shape)) (H : BatchHonestProver Q.toBatch Wt) (N : ℕ)
      (valid : Wt → X → Prop) (bud : BudB Q.ior.shape N) (z : ℝ≥0∞),
    Q.ExactT H N valid bud →
    (∀ (J : Finset (Fin N)) (ρs : J → Rho Q.ior.shape) (ds : J → D),
      bud J ρs fun j => plan (ds j)) →
    (∀ w x, valid w x → prRho (H.one.Hid w x) ≤ z) → (Q.moreHonest H plan).HVZK N valid z

end Spec
end Iop
