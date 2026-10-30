-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/Batch.lean: batches: up to N instances proved together, with some verifier messages shared.
(1) (Snd-B) of Iop/Batch.lean with a witness and a named extractor (`SndBK`);
(2) batch IOPs whose slots have external oracles of their own beside a shared one (`BIOP`), their
honest side, completeness and honest-verifier exact zero knowledge for sets of slots with
further reads (`BIOP.Honest.Exact`);
(3) an IOR run in every slot, then a batch IOP (`online`), with its honest side, and honest-verifier
zero knowledge for a batch IOP over one shared oracle (`ExactT`): see `ExactTWith`;
(4) the statements of the composition theorems.

Definitions and statements only. The proofs are in Ior/BatchKProofs.lean, Ior/OnlineK.lean and
Ior/OnlineHon.lean.

Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md). The
theorems: `sndBK_iff`, `sndB_of_sndBK`, `sndBK_of_sndB`, `jointAll_of_sndBK`, `one_of_sndBK` in
Ior/BatchKProofs.lean; `sndBK_online` in Ior/OnlineK.lean; `acc_online`, `exact_online`,
`hvzk_of_exactT`, `hvzk_online` in Ior/OnlineHon.lean.

A batch IOP (`BatchInteractiveOracleProof`, Iop/Batch.lean) is one IOP, for the local transcript of a slot, with an
annotation of its shape (`RoundSplits`): which verifier messages the slots share, and how each prover
message splits into a shared part and a slot's part. A slot is one of the N places of a batch, each
with one instance or empty, with its own local transcript. (Snd-B) (`BatchInteractiveOracleProof.SndB`,
Iop/Batch.lean; late form: `SndBL`) is round-by-round soundness of a batch IOP by a state function:
errors for one slot in local rounds, joint errors in shared rounds.

(1) `SndBK`. Q is a batch IOP, R a relation on (x, y, w), wit a function that reads a witness off
the instance and the prover's oracles of a full local transcript. By its type it sees no verifier
message: the witness extractor of the compiled argument has no oracle access and is not given the
verifier's queries.
`Q.SndBK N early late R wit ε` says that the guarded protocol (`Q.guard R wit`) has (Snd-B), in the
late form of Iop/Batch.lean, for the empty language;
at early = id, late = none: there is a state function on partial local transcripts
   that is 0 at the start for every statement,
   that no prover message moves from 0 to 1,
   that is moved from 0 to 1 by at most ε_i values of the verifier message of round i (for one slot
     in a local round; for some slot, jointly, in a shared round),
   and at whose value 0 on a full transcript the verifier rejects or the extracted witness is valid.
For other early, late: `SndBL`, Iop/Batch.lean. Written out at early = id, late = none:
`Spec.sndBK_iff`.
This is the working form of round-by-round knowledge soundness (Ior/Know.lean) for the instances of
a batch: one-instance errors in the rounds of an instance, joint errors in the shared rounds, which
is the list that the compiler takes.
`early`, `late`: how an instance is written into the hash chain of its slot: early x into the first
query, x itself into the query of the round late (see the docstring of `BatchInteractiveOracleProof.SndBL`,
Iop/Batch.lean).

(2) The paper's IOPP for linear constraints runs on implicit instances (Π, aux_c): Π is shared by
the instances, aux_c is the instance's own. "curry" moves aux_c into the instance, so that the
notions of Iop/Batch.lean, which know one shared external oracle, apply to soundness. For
zero knowledge the simulator must not be given aux_c: hence a honest side and a notion of their own.

Further reads. As for one IOR (Ior/Honest.lean), the exact notion for sets of slots lets every
oracle that the prover sends be read further: for each slot j of J a set T_j of positions in the
oracles of its local transcript (the shared part's oracles and the slot's own).
The output shows the symbols at T_j too.
The simulator is given J, the instances of J, the verifier messages in the local transcripts of J,
the further positions, and for each slot of J the symbols of (shared oracle, own oracles) at that
slot's verifier's positions and at the positions tied to what is shown of that slot ("given";
exactly: `Q.ior.given (ρ.slot j.1) (Ts j)`; `IOR.given`, Ior/Honest.lean:
`R.extReads ρ ∪ (R.reads ρ ∪ T).biUnion (R.tie ρ)`), and nothing else.
The budget is a property of the family (J, (ρ_j), (T_j)): an oracle of the shared part is read
through all slots of J, and its encoding has to bear the union.
Without further reads a prover that writes its witness into a blinded oracle which the verifier
never reads would pass; with a budget that bears one position of that oracle it does not [no theorem
here; at a toy: Ior/BatchTest.lean: `exact_empty`, `not_exact_one`; for the batch IOP with it in
every slot: `exactB_empty`, `not_exactB_one`].
Terms: lean/GLOSSARY.md: annotation, batch IOP, blinded, compiler, external oracles, guard,
honest side, IOR, local round, (Snd-B).
-/
import Ior.Honest
import Ior.Know
import Iop.Batch
import Iop.Late
import Blocks.Batch.KitHon
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

/-! ## 1. (Snd-B) with a witness -/

/-- All symbols of all prover oracles of a transcript: what Tr.read returns. No verifier message, no
plain part, no external oracle. -/
abbrev Orcs (s : Shape) : Type := (p : OPos s) → OSym s p

/-- the oracles of the first, of the second part -/
def Orcs.fst {s t : Shape} (o : Orcs (s ++ t)) : Orcs s := fun p => OSym.ofLeft p (o (OPos.left p))
def Orcs.snd {s t : Shape} (o : Orcs (s ++ t)) : Orcs t := fun p =>
  OSym.ofRight p (o (OPos.right (s := s) p))

namespace BatchInteractiveOracleProof
variable {X W : Type} {E : ExtSpec}

open Classical in
/-- Q with a verifier that also rejects when the extracted witness is valid. -/
def guard (Q : BatchInteractiveOracleProof X E)
    (R : X → E.Str → W → Prop) (wit : X → Orcs Q.loc.shape → W) : BatchInteractiveOracleProof X E where
  loc := { Q.loc with accept := fun x y τ => Q.loc.accept x y τ && !decide (R x y (wit x τ.read)) }
  ann := Q.ann

/-- (Snd-B) with a witness: round-by-round knowledge soundness for the instances of a batch. By type
wit sees the instance and the prover's oracles, and nothing else: no verifier message, no external
oracle. -/
def SndBK (Q : BatchInteractiveOracleProof X E) (N : ℕ) (early : X → X) (late : Option ℕ) (R : X → E.Str → W → Prop)
    (wit : X → Orcs Q.loc.shape → W) (ε : Err Q.loc.shape) : Prop :=
  (Q.guard R wit).SndBL N early late (fun _ _ => False) ε

end BatchInteractiveOracleProof

/-- The law on verifier messages, fully joint: also in a local round the count is of the tuples
(ρ_1, .., ρ_N) after which the state of some slot has moved from 0 to 1. -/
def JointLawAll (N : ℕ) : (s : Shape) → RoundSplits s → Err s → (Fin N → Option (PTr s → Bool)) → Prop
  | [], _, _, _ => True
  | r :: s, (a, A), (e, ε), St =>
      ∀ (m0 : a.M0) (m : Fin N → a.Mj),
        cnt (fun v : a.kind.All N r.Chal =>
            ∃ j S,
              St j = some S ∧
              S (.atV (Sum.inl (a.join m0 (m j)))) = false ∧
              S (PTr.cons (a.join m0 (m j)) (a.kind.slot v j) (PTr.empty s)) = true) ≤ e ∧
        ∀ v : a.kind.All N r.Chal, JointLawAll N s A ε fun j =>
          (St j).map fun S τ => S (PTr.cons (a.join m0 (m j)) (a.kind.slot v j) τ)

/-- The errors of the fully joint law: N e |Chal|^(N-1) tuples in a local round (as a probability: N
times the error of one instance), e in a shared round. Mind: the entries in local rounds count
tuples, out of |Chal|^N. Err.Below and AtV.errPr, which divide by |Chal|, must not be used on this
list. -/
def Err.jointAll (N : ℕ) : {s : Shape} → RoundSplits s → Err s → Err s
  | [], _, _ => ()
  | r :: _, (a, A), (e, ε) => (match a.kind with
      | .lo => N * e * Fintype.card r.Chal ^ (N - 1)
      | .sh => e, Err.jointAll N A ε)

/-! ## 2. Batch IOPs whose slots have external oracles of their own -/

open Classical in
/-- The disclosed view with further positions T: the plain parts; the symbols of the external
oracles at the verifier's positions and at those tied to what is shown (exactly: `R.given τ.rho T`;
`IOR.given`, Ior/Honest.lean: `R.extReads ρ ∪ (R.reads ρ ∪ T).biUnion (R.tie ρ)`); the symbols of
the prover's oracles at the verifier's positions and at T, and every unblinded oracle in full. At T
= ∅, if the verifier itself reads all that is tied to its positions (IOR.Tied), it is the disclosed
view of Iop/InteractiveOracleProof.lean. -/
def IOR.dviewT {X : Type} {E : ExtSpec} (R : IOR X E Unit extNone)
    (T : Finset (OPos R.shape)) (y : E.Str) (τ : Tr R.shape) : DView R.toInteractiveOracleProof where
  plains := τ.plains
  ext := E.ans (R.given τ.rho T) y
  orc := fun p => if p ∈ R.reads τ.rho ∨ p ∈ T ∨ R.blinded p = false then some (τ.read p) else none

/-- The verifier itself reads all that is tied to its positions. (Written without a union, so that
no instance of decidable equality stands in the statement.) -/
def IOR.Tied {Xi Xo : Type} {Ei Eo : ExtSpec} (R : IOR Xi Ei Xo Eo) : Prop :=
  ∀ ρ p, p ∈ R.reads ρ → R.tie ρ p ⊆ R.extReads ρ

/-- A budget of further reads for sets of slots: which families (J, the verifier messages of the
slots of J, the further positions in each slot's local transcript) the encodings of the prover's
oracles bear. -/
abbrev BudB (s : Shape) (N : ℕ) : Type :=
  (J : Finset (Fin N)) → (J → Rho s) → (J → Finset (OPos s)) → Prop

/-- A batch IOP given as an IOR to the trivial statement with an annotation of its shape. -/
structure BIOP (X : Type) (E : ExtSpec) where
  ior : IOR X E Unit extNone
  ann : RoundSplits ior.shape

namespace BIOP
variable {X : Type} {E E0 Ej : ExtSpec}

/-- as a batch IOP of Iop/Batch.lean -/
def toBatch (Q : BIOP X E) : BatchInteractiveOracleProof X E := ⟨Q.ior.toInteractiveOracleProof, Q.ann⟩

open Classical in
/-- The slot's own oracles moved into the instance. -/
def curry (Q : BIOP X (E0.prod Ej)) : BatchInteractiveOracleProof (X × Ej.Str) E0 where
  loc :=
    { shape := Q.ior.shape
      blinded := Q.ior.blinded
      extReads := fun _ ρ => (Q.ior.extReads ρ).preimage Sum.inl (Sum.inl_injective.injOn)
      reads := fun _ ρ _ => Q.ior.reads ρ
      accept := fun a y0 τ => (Q.ior.out a.1 (y0, a.2) τ).isSome }
  ann := Q.ann

/-- The type of a simulator for sets of slots: J, the instances, the verifier messages, the further
positions, and for each slot symbols of its external oracles. -/
abbrev SimB (Q : BIOP X E) (N : ℕ) : Type :=
  (J : Finset (Fin N)) → (J → X) → (J → Rho Q.ior.shape) → (J → Finset (OPos Q.ior.shape)) →
  (J → E.Pos → Option E.Sym) → PMF (J → Option (DView Q.ior.toInteractiveOracleProof))

/-- The honest side: W0 is the private input for the shared oracle, Wj the witness of a slot. The
shared part of the prover is a function of W0, its own coins and the shared verifier messages by
type. All that is withheld is public. -/
structure Honest (Q : BIOP X (E0.prod Ej)) (W0 Wj : Type) where
  Coin0 : Type
  Coin  : Type
  [finCoin0 : Fintype Coin0]
  [neCoin0  : Nonempty Coin0]
  [finCoin  : Fintype Coin]
  [neCoin   : Nonempty Coin]
  strat0 : W0 → Coin0 → SStrat Q.ior.shape Q.ann
  strat  : W0 → Coin0 → X → Wj → Coin → LStrat Q.ior.shape Q.ann
  Bad    : Set (RhoLo Q.ior.shape Q.ann)
  stop0  : RhoSh Q.ior.shape Q.ann → Bool

attribute [instance] Honest.finCoin0 Honest.neCoin0 Honest.finCoin Honest.neCoin

namespace Honest
variable {Q : BIOP X (E0.prod Ej)} {W0 Wj : Type}

/-- the withheld set of a slot: public -/
def withheld (H : Q.Honest W0 Wj) : Set (Rho Q.ior.shape) :=
  {ρ | Rho.lo Q.ann ρ ∈ H.Bad ∨ H.stop0 (Rho.sh Q.ann ρ) = true}

/-- the honest prover on the local transcript of one slot -/
def one (H : Q.Honest W0 Wj) (w0 : W0) (x : X) (wj : Wj) (c : H.Coin0 × H.Coin) :
    Strat Q.ior.shape Unit :=
  (H.strat0 w0 c.1).zip (H.strat w0 c.1 x wj c.2)

/-- (Acc) for each slot. -/
def Acc (H : Q.Honest W0 Wj) (R : X → (E0.prod Ej).Str → W0 × Wj → Prop) : Prop :=
  ∀ x y w c ρ,
    R x y w → ρ ∉ H.withheld → (Q.ior.out x y ((H.one w.1 x w.2 c).run ρ).1).isSome = true

open Classical in
/-- The output for the set J of slots at ρ, with the further positions Ts. a j holds the instance,
the own oracles and the witness of slot j (none: the slot is empty). -/
def output (H : Q.Honest W0 Wj) {N : ℕ} (w0 : W0) (y0 : E0.Str)
    (a : Fin N → Option (X × Ej.Str × Wj)) (ρ : BRho N Q.ior.shape Q.ann)
    (J : Finset (Fin N)) (Ts : J → Finset (OPos Q.ior.shape)) :
    PMF (J → Option (DView Q.ior.toInteractiveOracleProof)) :=
  (unif (H.Coin0 × (Fin N → H.Coin))).map fun c => fun j =>
    match a j with
    | none => none
    | some aj =>
      if ρ.slot j.1 ∈ H.withheld then none
      else
        some (Q.ior.dviewT (Ts j) (y0, aj.2.1)
            ((H.one w0 aj.1 aj.2.2 (c.1, c.2 j)).run (ρ.slot j.1)).1)

/-- Honest-verifier exact zero knowledge for sets of slots, with further reads, the simulator named.
It is given J, the instances of J, the verifier messages in the local transcripts of J, the further
positions, and for each slot of J the symbols of (shared oracle, own oracles) at that slot's
verifier's positions and at the positions tied to what is shown of that slot (exactly:
`Q.ior.given (ρ.slot j.1) (Ts j)`; `IOR.given`, Ior/Honest.lean). Under the hypotheses below, at
every ρ and every family of further positions within the budget its output has exactly the law of
the output for J. -/
def ExactWith (H : Q.Honest W0 Wj) (N : ℕ) (R : X → (E0.prod Ej).Str → W0 × Wj → Prop)
    (bud : BudB Q.ior.shape N) (Sim : Q.SimB N) : Prop :=
  ∀ (w0 : W0) (y0 : E0.Str) (a : Fin N → Option (X × Ej.Str × Wj)),
    (∀ j aj, a j = some aj → R aj.1 (y0, aj.2.1) (w0, aj.2.2)) →
    ∀ (J : Finset (Fin N)) (as : J → X × Ej.Str × Wj), (∀ j : J, a j = some (as j)) →
      ∀ (ρ : BRho N Q.ior.shape Q.ann) (Ts : J → Finset (OPos Q.ior.shape)),
        bud J (fun j => ρ.slot j.1) Ts →
        H.output w0 y0 a ρ J Ts =
          Sim J (fun j => (as j).1) (fun j => ρ.slot j.1) Ts
            (fun j => (E0.prod Ej).ans (Q.ior.given (ρ.slot j.1) (Ts j)) (y0, (as j).2.1))

def Exact (H : Q.Honest W0 Wj) (N : ℕ)
    (R : X → (E0.prod Ej).Str → W0 × Wj → Prop) (bud : BudB Q.ior.shape N) : Prop :=
  ∃ Sim : Q.SimB N, H.ExactWith N R bud Sim

end Honest
end BIOP

/-! ## 3. An IOR in every slot, then a batch IOP -/

/-- The local verifier messages of the second part, behind a first part of local rounds. -/
def RhoLo.back :
    (s : Shape) → {t : Shape} → {A' : RoundSplits t} →
    RhoLo (s ++ t) (RoundSplits.app (RoundSplits.const (RAnn.ofSlot .lo) s) A') → RhoLo t A'
  | [], _, _, l => l
  | _ :: s, _, _, (_, l) => RhoLo.back s l

/-- The shared verifier messages of the second part, behind a first part of local rounds. -/
def RhoSh.back :
    (s : Shape) → {t : Shape} → {A' : RoundSplits t} →
    RhoSh (s ++ t) (RoundSplits.app (RoundSplits.const (RAnn.ofSlot .lo) s) A') → RhoSh t A'
  | [], _, _, l => l
  | _ :: s, _, _, (_, l) => RhoSh.back s l

section Online
variable {X Xl : Type} {E0 Ej : ExtSpec}

/-- F in every slot (local rounds, only the slot speaks), then Q. -/
def online (F : IOR X E0 Xl (E0.prod Ej)) (Q : BIOP Xl (E0.prod Ej)) : BIOP X E0 where
  ior := F.seq Q.ior
  ann := RoundSplits.app (RoundSplits.allLocal F.shape) Q.ann

/-- The extractor of the composition: that of the second part, on the oracles "aux" that the first
part leaves, then that of the first. -/
def witSeq {WA WB : Type} {s t : Shape} (aux : Orcs s → Ej.Str)
    (e₁ : X → Orcs s → WB → WA) (e₂ : Ej.Str → Orcs t → WB) : X → Orcs (s ++ t) → WA :=
  fun x o => e₁ x (Orcs.fst o) (e₂ (aux (Orcs.fst o)) (Orcs.snd o))

/-- The honest side of the composition, as a honest side of Iop/Batch.lean with the private input
Wt. "inp w x" is the witness that the honest prover of a slot uses for the instance x; "sh w" its
input for the shared part. -/
def onlineHonest {Wt WA W0 Wj : Type} (F : IOR X E0 Xl (E0.prod Ej))
    (Q : BIOP Xl (E0.prod Ej)) (HF : F.Honest WA (W0 × Wj)) (HQ : Q.Honest W0 Wj)
    (ext : Wt → E0.Str) (sh : Wt → W0) (inp : Wt → X → WA) :
    BatchHonestProver (online F Q).toBatch Wt where
  Coin0 := HQ.Coin0
  Coin := HF.Coin × HQ.Coin
  ext := ext
  strat0 := fun w c0 => SStrat.skip .lo F.shape (HQ.strat0 (sh w) c0)
  strat := fun w c0 x c =>
    LStrat.bind .lo (HF.strat (inp w x) x c.1) fun o => HQ.strat (sh w) c0 o.1 o.2.2 c.2
  Bad := {l | RhoLo.front F.shape (A' := Q.ann) l ∈ HF.Bad} ∪
    {l | RhoLo.back F.shape (A' := Q.ann) l ∈ HQ.Bad}
  Hid := fun w x => {l | RhoLo.front F.shape (A' := Q.ann) l ∈ HF.Hid (inp w x) x}
  stop0 := fun σ => HQ.stop0 (RhoSh.back F.shape (A' := Q.ann) σ)

/-- The parts of a set of positions in the two shapes. -/
def OPos.partL {s t : Shape} (T : Finset (OPos (s ++ t))) : Finset (OPos s) :=
  T.preimage OPos.left OPos.left_injective.injOn
def OPos.partR {s t : Shape} (T : Finset (OPos (s ++ t))) : Finset (OPos t) :=
  T.preimage (OPos.right (s := s)) OPos.right_injective.injOn

open Classical in
/-- The budget of the composition. For each slot of J: F bears the part of T_j in its shape together
with the sources of all that Q's simulator is given of the oracles that F leaves. Q bears the parts
in its shape, as a family, for every subset of J (a slot whose first part is withheld shows the
notice and drops out of Q's simulation; a budget that is kept by subsets asks no more here than at J
itself). -/
def budOnline (F : IOR X E0 Xl (E0.prod Ej)) (Q : BIOP Xl (E0.prod Ej)) {N : ℕ}
    (bF : Rho F.shape → Finset (OPos F.shape) → Prop) (bQ : BudB Q.ior.shape N) :
    BudB (F.shape ++ Q.ior.shape) N := fun J ρs Ts =>
  (∀ j, bF (Rho.fst (ρs j)) (OPos.partL (Ts j) ∪ (Q.ior.given (Rho.snd (s := F.shape) (ρs j)) (OPos.partR (s := F.shape) (Ts j))).biUnion (F.srcO (Rho.fst (ρs j))))) ∧
  ∀ (J' : Finset (Fin N)) (h : J' ⊆ J), bQ J' (fun j => Rho.snd (s := F.shape) (ρs ⟨j.1, h j.2⟩))
    (fun j => OPos.partR (s := F.shape) (Ts ⟨j.1, h j.2⟩))

end Online

/-!
### Honest-verifier exact zero knowledge with further reads for a batch IOP over one shared oracle
-/

namespace BIOP
variable {X Wt : Type} {E : ExtSpec}

open Classical in
/-- The output for J at ρ with the further positions Ts, for a honest side of Iop/Batch.lean:
BatchHonestProver.output with dviewT in the place of the disclosed view. -/
def outputT (Q : BIOP X E) (H : BatchHonestProver Q.toBatch Wt) {N : ℕ}
    (w : Wt) (x : Fin N → Option X) (ρ : BRho N Q.ior.shape Q.ann)
    (J : Finset (Fin N)) (Ts : J → Finset (OPos Q.ior.shape)) :
    PMF (J → Option (DView Q.ior.toInteractiveOracleProof)) :=
  (unif (H.Coin0 × (Fin N → H.Coin))).map fun c => fun j =>
    match x j with
    | none => none
    | some xj =>
      if ρ.slot j.1 ∈ H.one.withheld w xj then none
      else some (Q.ior.dviewT (Ts j) (H.ext w) ((H.one.strat w xj (c.1, c.2 j)).run (ρ.slot j.1)).1)

open Classical in
/-- The symbols of the shared oracle that the simulator is given: at the verifiers' positions of the
slots of J, and at those tied to what is shown of them (exactly:
`∃ j, p ∈ Q.ior.given (ρs j) (Ts j)`; `IOR.given`, Ior/Honest.lean). -/
def ansJ (Q : BIOP X E) {N : ℕ} (J : Finset (Fin N)) (ρs : J → Rho Q.ior.shape)
    (Ts : J → Finset (OPos Q.ior.shape)) (y : E.Str) : E.Pos → Option E.Sym :=
  fun p => if ∃ j, p ∈ Q.ior.given (ρs j) (Ts j) then some (E.rd y p) else none

/-- The type of a simulator. -/
abbrev SimT (Q : BIOP X E) (N : ℕ) : Type :=
  (J : Finset (Fin N)) → (J → X) → (J → Rho Q.ior.shape) → (J → Finset (OPos Q.ior.shape)) →
  (E.Pos → Option E.Sym) → PMF (J → Option (DView Q.ior.toInteractiveOracleProof))

/-- Honest-verifier exact zero knowledge for sets of slots, with further reads, the simulator named.
For every valid input, every set J of non-empty slots, every ρ at which no slot of J is in the
secret-dependent part Hid of its withheld set, and every family of further positions within the
budget, the simulator's output has exactly the law of the output for J. -/
def ExactTWith (Q : BIOP X E) (H : BatchHonestProver Q.toBatch Wt) (N : ℕ) (valid : Wt → X → Prop)
    (bud : BudB Q.ior.shape N) (Sim : Q.SimT N) : Prop :=
  ∀ (w : Wt) (x : Fin N → Option X), (∀ j xj, x j = some xj → valid w xj) →
    ∀ (J : Finset (Fin N)) (xs : J → X), (∀ j : J, x j = some (xs j)) →
      ∀ ρ : BRho N Q.ior.shape Q.ann, (∀ j : J, ρ.slot j.1 ∉ H.one.Hid w (xs j)) →
        ∀ Ts : J → Finset (OPos Q.ior.shape), bud J (fun j => ρ.slot j.1) Ts →
          Q.outputT H w x ρ J Ts =
            Sim J xs (fun j => ρ.slot j.1) Ts (Q.ansJ J (fun j => ρ.slot j.1) Ts (H.ext w))

def ExactT (Q : BIOP X E) (H : BatchHonestProver Q.toBatch Wt) (N : ℕ)
    (valid : Wt → X → Prop) (bud : BudB Q.ior.shape N) : Prop :=
  ∃ Sim : Q.SimT N, Q.ExactTWith H N valid bud Sim

end BIOP

/-! ## 4. Statements -/

namespace Spec

/-- `SndBK` written out, when the whole instance stands in the first query (early = id, late =
none). -/
def sndBK_iff : Prop :=
  ∀ (X W : Type) (E : ExtSpec) (Q : BatchInteractiveOracleProof X E) (N : ℕ) (R : X → E.Str → W → Prop)
      (wit : X → Orcs Q.loc.shape → W) (ε : Err Q.loc.shape),
    Q.SndBK N id none R wit ε ↔
    ∃ State : E.Str → X → PTr Q.loc.shape → Bool,
      (∀ y x, State y x (PTr.empty Q.loc.shape) = false) ∧
      (∀ y x (τ : AtP Q.loc.shape) (m : τ.round.Msg),
        State y x (.atP τ) = false → State y x (.atV (τ.snoc m)) = false) ∧
      (∀ y x (τ : Tr Q.loc.shape),
        State y x (.full τ) = false → Q.loc.accept x y τ = true → R x y (wit x τ.read)) ∧
      (∀ y (x : Fin N → Option X), JointLaw N Q.loc.shape Q.ann ε fun j => (x j).map (State y))

/-- States: knowledge soundness for the instances gives (Snd-B), in the late form, for the language
of the relation. -/
def sndB_of_sndBK : Prop :=
  ∀ (X W : Type) (E : ExtSpec) (Q : BatchInteractiveOracleProof X E) (N : ℕ) (early : X → X) (late : Option ℕ)
      (R : X → E.Str → W → Prop) (wit : X → Orcs Q.loc.shape → W) (ε : Err Q.loc.shape),
    Q.SndBK N early late R wit ε → Q.SndBL N early late (fun x y => ∃ w, R x y w) ε

/-- States: (Snd-B) gives knowledge soundness (early = id, late = none) when the instance determines
the witness: the extractor is d, a function of the instance alone. (For an IOPP: the own oracles of
a slot stand in the instance, by "curry", and d decodes them.) -/
def sndBK_of_sndB : Prop :=
  ∀ (X W : Type) (E : ExtSpec) (Q : BatchInteractiveOracleProof X E) (N : ℕ) (L : X → E.Str → Prop)
      (R : X → E.Str → W → Prop) (d : X → W) (ε : Err Q.loc.shape),
    Q.SndB N L ε → (∀ x y, L x y → R x y (d x)) → Q.SndBK N id none R (fun x _ => d x) ε

/-- The fully joint list of errors. -/
def jointAll_of_sndBK : Prop :=
  ∀ (X W : Type) (E : ExtSpec) (Q : BatchInteractiveOracleProof X E) (N : ℕ) (R : X → E.Str → W → Prop)
      (wit : X → Orcs Q.loc.shape → W) (ε : Err Q.loc.shape),
    Q.SndBK N id none R wit ε →
    ∃ State : E.Str → X → PTr Q.loc.shape → Bool,
      (∀ y x, State y x (PTr.empty Q.loc.shape) = false) ∧
      (∀ y x (τ : AtP Q.loc.shape) (m : τ.round.Msg),
        State y x (.atP τ) = false → State y x (.atV (τ.snoc m)) = false) ∧
      (∀ y x (τ : Tr Q.loc.shape),
        State y x (.full τ) = false → Q.loc.accept x y τ = true → R x y (wit x τ.read)) ∧
      (∀ y (x : Fin N → Option X),
        JointLawAll N Q.loc.shape Q.ann (Err.jointAll N Q.ann ε) fun j => (x j).map (State y))

/-- States, under the hypotheses below: the list for one fixed instance: the local protocol of one
slot has knowledge soundness in the working form of Ior/Know.lean, with the same list. -/
def one_of_sndBK : Prop :=
  ∀ (X W : Type) (E : ExtSpec) (Q : BatchInteractiveOracleProof X E) (N : ℕ) (R : X → E.Str → W → Prop)
      (wit : X → Orcs Q.loc.shape → W) (ε : Err Q.loc.shape),
    0 < N → Q.SndBK N id none R wit ε →
    ∀ x y, Doomed Q.loc.shape ε (fun τ => Q.loc.accept x y τ = true → R x y (wit x τ.read))

/-- Knowledge soundness of "an IOR in every slot, then a batch IOP", at early = id, late = none.
F has knowledge soundness from RA to RB on the statements with "on";
Q has it for its instances, for RB', on implicit instances that share their first component;
F copies that component and leaves beside it oracles that are a function "aux" of the oracles sent;
of statement and transcript the extractors read the instance and the prover's oracles only;
on the outputs of F on statements with "on", RB' implies RB.
Then the composition has it for the relation "on → RA"; the errors are concatenated and the
extractors composed. -/
def sndBK_online : Prop :=
  ∀ (X Xl WA WB : Type) (E0 Ej : ExtSpec) (F : IOR X E0 Xl (E0.prod Ej)) (Q : BIOP Xl (E0.prod Ej))
      (N : ℕ) (aux : Orcs F.shape → Ej.Str) (on : X × E0.Str → Prop) (RA : X × E0.Str → WA → Prop)
      (RB RB' : Xl × (E0.prod Ej).Str → WB → Prop) (e₁ : X → Orcs F.shape → WB → WA)
      (e₂ : Ej.Str → Orcs Q.ior.shape → WB) (ε₁ : Err F.shape) (ε₂ : Err Q.ior.shape),
    F.red.Know on RA RB (fun a τ w => e₁ a.1 τ.read w) ε₁ →
    Q.curry.SndBK N id none (fun a y0 w => RB' (a.1, (y0, a.2)) w) (fun a o => e₂ a.2 o) ε₂ →
    (∀ y τ, F.imp y τ = (y, aux τ.read)) →
    (∀ x y τ xl w,
      on (x, y) → F.out x y τ = some xl → RB' (xl, F.imp y τ) w → RB (xl, F.imp y τ) w) →
    (online F Q).toBatch.SndBK
      N id none (fun x y w => on (x, y) → RA (x, y) w) (witSeq aux e₁ e₂) (Err.app ε₁ ε₂)

/-- Completeness of the composition, for each slot. -/
def acc_online : Prop :=
  ∀ (X Xl Wt WA W0 Wj : Type) (E0 Ej : ExtSpec) (F : IOR X E0 Xl (E0.prod Ej))
      (Q : BIOP Xl (E0.prod Ej)) (HF : F.Honest WA (W0 × Wj)) (HQ : Q.Honest W0 Wj)
      (ext : Wt → E0.Str) (sh : Wt → W0) (inp : Wt → X → WA) (valid : Wt → X → Prop)
      (RA : X → E0.Str → WA → Prop) (RB : Xl → (E0.prod Ej).Str → W0 × Wj → Prop),
    HF.Acc RA RB → HQ.Acc RB → (∀ w x, valid w x → RA x (ext w) (inp w x)) →
    (∀ w x c ρ,
      valid w x → ρ ∉ HF.withheld (inp w x) x → ((HF.strat (inp w x) x c).run ρ).2.2.1 = sh w) →
    (onlineHonest F Q HF HQ ext sh inp).Acc valid

/-- Honest-verifier zero knowledge of the composition, for sets of slots, with further reads. F is
simulated exactly outside Hid, Q exactly; F copies the shared oracle, reads nothing of it and ties
nothing to it. Then, under the hypotheses below, the composition is simulated exactly, outside F's
Hid in the slots of J, at the composed budget. -/
def exact_online : Prop :=
  ∀ (X Xl Wt WA W0 Wj : Type) (E0 Ej : ExtSpec) (F : IOR X E0 Xl (E0.prod Ej))
      (Q : BIOP Xl (E0.prod Ej)) (HF : F.Honest WA (W0 × Wj)) (HQ : Q.Honest W0 Wj)
      (ext : Wt → E0.Str) (sh : Wt → W0) (inp : Wt → X → WA) (valid : Wt → X → Prop)
      (RA : X → E0.Str → WA → Prop) (RB : Xl → (E0.prod Ej).Str → W0 × Wj → Prop)
      (bF : Rho F.shape → Finset (OPos F.shape) → Prop) (N : ℕ) (bQ : BudB Q.ior.shape N),
    F.IsLocal → HF.Acc RA RB → HF.Exact RA bF → HQ.Exact N RB bQ →
    (∀ w x, valid w x → RA x (ext w) (inp w x)) →
    (∀ w x c ρ,
      valid w x → ρ ∉ HF.withheld (inp w x) x → ((HF.strat (inp w x) x c).run ρ).2.2.1 = sh w) →
    (∀ y τ, (F.imp y τ).1 = y) → (∀ ρ p, F.srcE ρ (Sum.inl p) = {p} ∧ F.srcO ρ (Sum.inl p) = ∅) →
    (∀ ρ q, F.srcE ρ (Sum.inr q) = ∅) → (∀ ρ, F.extReads ρ = ∅) → (∀ ρ p, F.tie ρ p = ∅) →
    (online F Q).ExactT (onlineHonest F Q HF HQ ext sh inp) N valid (budOnline F Q bF bQ)

/-- From the exact form with further reads to the form that the compiler takes: no further reads;
the verifier itself reads all that is tied to its positions; the error for a set J of slots is
|J| z, where z bounds the probability of Hid. Not all hypotheses are named here: see the statement
below. -/
def hvzk_of_exactT : Prop :=
  ∀ (X Wt : Type) (E : ExtSpec) (Q : BIOP X E) (H : BatchHonestProver Q.toBatch Wt) (N : ℕ)
      (valid : Wt → X → Prop) (bud : BudB Q.ior.shape N) (z : ℝ≥0∞),
    Q.ExactT H N valid bud → (∀ J ρs, bud J ρs fun _ => ∅) → Q.ior.Tied →
    (∀ w x, valid w x → prRho (H.one.Hid w x) ≤ z) → H.HVZK N valid z

open Classical in
/-- Honest-verifier zero knowledge of the composition, for sets of slots, in the form that the
compiler takes: a corollary of the two statements above. Not all hypotheses are named here: see the
statement below. F's budget bears what Q's verifier reads of F's oracles; Q's budget bears "no
further reads"; Q's verifier reads all that is tied to its positions; the error for a set J of slots
is |J| z, where z bounds the probability of Hid. -/
def hvzk_online : Prop :=
  ∀ (X Xl Wt WA W0 Wj : Type) (E0 Ej : ExtSpec) (F : IOR X E0 Xl (E0.prod Ej))
      (Q : BIOP Xl (E0.prod Ej)) (HF : F.Honest WA (W0 × Wj)) (HQ : Q.Honest W0 Wj)
      (ext : Wt → E0.Str) (sh : Wt → W0) (inp : Wt → X → WA) (valid : Wt → X → Prop)
      (RA : X → E0.Str → WA → Prop) (RB : Xl → (E0.prod Ej).Str → W0 × Wj → Prop)
      (bud : Rho F.shape → Finset (OPos F.shape) → Prop) (N : ℕ)
      (bQ : BudB Q.ior.shape N) (z : ℝ≥0∞),
    F.IsLocal → HF.Acc RA RB → HF.Exact RA bud → HQ.Exact N RB bQ →
    (∀ w x, valid w x → RA x (ext w) (inp w x)) →
    (∀ w x c ρ,
      valid w x → ρ ∉ HF.withheld (inp w x) x → ((HF.strat (inp w x) x c).run ρ).2.2.1 = sh w) →
    (∀ y τ, (F.imp y τ).1 = y) → (∀ ρ p, F.srcE ρ (Sum.inl p) = {p} ∧ F.srcO ρ (Sum.inl p) = ∅) →
    (∀ ρ q, F.srcE ρ (Sum.inr q) = ∅) → (∀ ρ, F.extReads ρ = ∅) → (∀ ρ p, F.tie ρ p = ∅) →
    (∀ ρ₁ ρ₂, bud ρ₁ ((Q.ior.extReads ρ₂).biUnion (F.srcO ρ₁))) → (∀ J ρs, bQ J ρs fun _ => ∅) →
    Q.ior.Tied → (∀ w x, valid w x → prRho (HF.Hid (inp w x) x) ≤ z) →
    (onlineHonest F Q HF HQ ext sh inp).HVZK N valid z

end Spec
end Iop
