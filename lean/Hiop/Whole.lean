-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Hiop/Whole.lean: honest-verifier zero knowledge of the whole object.

DEFINITIONS AND STATEMENTS; the proofs are in Hiop/WholeProof.lean, a test that the definition can
fail in Hiop/WholeTest.lean.

Which statement is which: here the view of a run is its output, with the notice in the place of the
whole run where the verifier's randomness is withheld (difference 5 below): what the compiled,
non-interactive prover shows, and what the compiler takes. The true, never censored view of the
interactive object, with the probabilities of the withheld sets in the error, is
Hiop/WholeTrue.lean.

What is defined, for an arbitrary interface L : `Iop.BatchProtocol I X` (Hiop/Interface.lean has the
dictionary):
* The experiment. First the offline phase: an encoded index (number 0) is made with fresh
  randomness and the offline IOP is run on it. Then an environment, which has seen everything shown
  so far, asks step by step for
    `fresh`: a further encoded index, made with fresh randomness, and its link IOP with encoded
      index 0;
    `session`: a session on the encoded index number e, with a batch of instances and a set J of
      its slots that are shown;
    `read`: the symbol at one position of the encoded index number e;
  or it draws coins, or it stops with an output.
* What is shown of a run: the verifier's randomness of the run and its output (`Iop.DView`: the
  plain parts, the positions read with their answers, the unblinded oracles; or the notice, where
  the randomness lies in the withheld set). Of a session: this for the slots of J only (the shared
  verifier messages stand in the local randomness of each slot of J). These are `Sess` and `BSess`
  of Compile/Life.lean and Compile/Batch/SpecLife.lean.
* An environment is a decision tree (`Env`): its children at a request are indexed by what is shown
  of the run. So each request is an arbitrary function of the whole view so far and of the
  environment's coins; there is no bound on running time; every play ends. Its output at `stop` may
  be its whole view: closeness of the outputs of all environments is closeness of the views, with
  any distinguisher applied afterwards. The same for environments written as functions of the view,
  with the view as an explicit list of steps: `Env.ofFun`, `viewOf`, `Spec.hvzk_view`.
* The two sides answer through one structure (`Host`). The real side is `realHost L i`. A simulator
  (`Simulator`) has, by its type, no access to the index, and of a request for a session it is
  given the number e, the set J and the instances of J: not what the other slots hold, nor how many
  of them are filled.
* The bounds (`Bounds`, `Env.Adm`): at most nenc further encoded indices; at most sess e sessions
  and reads e single reads on the encoded index e, which must exist; at most `shown` slots shown in
  a session (shown = L.maxBatchSize is no restriction); all instances of a batch, the hidden ones too, in the
  relation with the index. They are asked on every path of the tree, whatever the answers.
* `HVZKWhole L Ryes B S z`: for every index and every environment within the bounds B, the real
  output and the output with the simulator S are within z in statistical distance.

Main names (stated here, proved in Hiop/WholeProof.lean):
  `Spec.hvzk_whole`: if the honest sides speak of the encodings (`Wired`), the runs read qT, qpar,
    qch, qon positions of encoded indices and an encoded index hides any b positions (`Reads`), Sm
    are good simulators of single runs (`Sims.Good`) and
      qT + nenc·qpar + sess 0·qon + reads 0 ≤ b, qch + sess j·qon + reads j ≤ b for 1 ≤ j ≤ nenc,
    then the named simulator `simWhole L Sm i₀` (encodings of a fixed index i₀, the three run
    simulators on them) has error zT + nenc·zL + (Σ_j sess j)·shown·zO.
  `Spec.hvzk_whole_hiding`: the same from `BatchProtocol.Hiding`, one triple of run simulators for all
    bounds.

How this differs from the definition of a print of this protocol's technical report, which
FOLLOWS (CY24) AND further work that this protocol builds on (lean/CREDITS.md; restated above in our
own words).
 1. Further reads. Their final distinguisher reads further UNIFORM positions, after the last step,
    of the encoded indices AND of the oracles that the prover sent in the runs. Here: further reads
    of ENCODED INDICES, at any step after the offline phase, at any position, chosen adaptively
    (`read`); they count in the budget as theirs do. Further reads of the prover's oracles of a run
    are not a request of their own: this file is about an arbitrary interface `Iop.BatchProtocol`, whose views
    hold the verifier's reads only (exactly, of the prover's oracles of a run: the unblinded oracles
    and the verifier's reads: `InteractiveOracleProof.dview`, Iop/InteractiveOracleProof.lean).





 2. No witnesses in a request: the honest prover of the interface recomputes what it needs from
    index and instance; "in the relation" is Ryes i x.
 3. A batch is a vector of L.maxBatchSize slots, some of them empty (all of them may be: theirs has at least
    one instance); its size is not shown. J may be empty (theirs may not): such a session shows
    nothing, costs nothing and still counts. The simulator learns the slot numbers of J, not only
    how many instances are shown.
 4. Under `BatchProtocol.Reads` (any b positions): the encodings hide exactly (`BatchProtocol.Reads.hidE`), so there is
    no term for the encoded indices in the error.
 5. Where the verifier's randomness lies in the withheld set of the honest side, the notice is
    shown in place of the view.
 6. A session costs zO for each slot shown (at most shown·zO), as in `BatchProtocol.Hiding`.
 7. Nothing on the simulator's running time, nor on HOW it samples (their lemma adds that it
    answers from a list of b uniform positions made with each encoded index).
A request on an encoded index that does not exist is excluded by `Env.Adm`; the hosts answer it
from encoded index 0 (a convention that no admissible environment meets).

Terms: lean/GLOSSARY.md.
"The technical report": this protocol's technical report (lean/CREDITS.md), in an earlier edition.
-/
import Hiop.Interface
import Compile.Batch.SpecLife

set_option autoImplicit false

noncomputable section

namespace Hiop
open Prob Iop Compile.Lifetime Compile.BatchLife
open scoped ENNReal

variable {I X : Type}

/-! ## 1. Environments, hosts, the experiment -/

/-- An environment after the offline phase, as a decision tree with outputs in α. -/
inductive Env (L : BatchProtocol I X) (α : Type) : Type 1
  /-- stop, with an output -/
  | stop (a : α) : Env L α
  /-- a further encoded index and its link; go on by what is shown of the link IOP -/
  | fresh (k : Sess L.link → Env L α) : Env L α
  /-- a session on the encoded index e: the slots J are shown and hold the instances xs; rest is
  what the other slots hold -/
  | session (e : ℕ) (J : Finset (Fin L.maxBatchSize)) (xs : J → X)
      (rest : {j : Fin L.maxBatchSize // j ∉ J} → Option X) (k : BSess L.onlineBatch J → Env L α) : Env L α
  /-- the symbol at position p of the encoded index e -/
  | read (e : ℕ) (p : Fin L.wordLength) (k : L.Symbol → Env L α) : Env L α
  /-- coins of the environment's own choice -/
  | draw (β : Type) (d : PMF β) (k : β → Env L α) : Env L α

/-- Who answers the environment: a state, the offline phase, and an answer to each kind of
request. -/
structure Host (L : BatchProtocol I X) where
  σ : Type
  off : PMF (Sess L.offline × σ)
  fresh : σ → PMF (Sess L.link × σ)
  session : σ → ℕ → (J : Finset (Fin L.maxBatchSize)) → (J → X) →
    ({j : Fin L.maxBatchSize // j ∉ J} → Option X) → PMF (BSess L.onlineBatch J × σ)
  read : σ → ℕ → Fin L.wordLength → PMF (L.Symbol × σ)

variable {L : BatchProtocol I X} {α : Type}

/-- The law of the environment's output when H answers, from the state s on. -/
def Env.run (H : Host L) : Env L α → H.σ → PMF α
  | .stop a, _ => PMF.pure a
  | .fresh k, s => (H.fresh s).bind fun p => (k p.1).run H p.2
  | .session e J xs rest k, s => (H.session s e J xs rest).bind fun p => (k p.1).run H p.2
  | .read e p k, s => (H.read s e p).bind fun q => (k q.1).run H q.2
  | .draw _ d k, s => d.bind fun y => (k y).run H s

/-- The experiment: the offline phase; then the environment, which has seen what is shown of the
offline IOP. -/
def Host.view (H : Host L) (E : Sess L.offline → Env L α) : PMF α :=
  H.off.bind fun p => (E p.1).run H p.2

/-- The real side on the index i. The state: the number of further encoded indices, and the
encoding randomness of each encoded index (that of number 0 at the numbers that do not exist).
Every run has fresh verifier randomness and fresh prover coins, and uses nothing of the state but
the encoding randomness of the encoded indices on which it runs. -/
def realHost (L : BatchProtocol I X) (i : I) : Host L where
  σ := ℕ × (ℕ → L.EncodingRandomness)
  off := (unif L.EncodingRandomness).bind fun r => (sess L.honestOfflineProver (i, r) ()).map fun a => (a, (0, fun _ => r))
  fresh := fun s =>
    (unif L.EncodingRandomness).bind fun r =>
      (sess L.honestLinkProver (i, s.2 0, r) ()).map fun a => (a, (s.1 + 1, Function.update s.2 (s.1 + 1) r))
  session := fun s e J xs rest => (bsess L.honestOnlineBatchProver (i, s.2 e) (vec J xs rest) J).map fun a => (a, s)
  read := fun s e p => PMF.pure (L.encodeIndex i (s.2 e) p, s)

/-- A simulator. No index; of a session: e, J and the instances of J. -/
structure Simulator (L : BatchProtocol I X) where
  σ : Type
  off : PMF (Sess L.offline × σ)
  fresh : σ → PMF (Sess L.link × σ)
  session : σ → ℕ → (J : Finset (Fin L.maxBatchSize)) → (J → X) → PMF (BSess L.onlineBatch J × σ)
  read : σ → ℕ → Fin L.wordLength → PMF (L.Symbol × σ)

/-- The simulator in the experiment: what the other slots hold is dropped. -/
def Simulator.host (S : Simulator L) : Host L where
  σ := S.σ
  off := S.off
  fresh := S.fresh
  session := fun s e J xs _ => S.session s e J xs
  read := S.read

/-- The simulator of the theorem: it keeps an encoding of the fixed index i₀ in the place of each
encoded index and answers each request for a run by the simulator of the run, which is given the
symbols of these encodings at the verifier's positions (exactly: `simSess`, Compile/Life.lean;
`simBsess`, Compile/Batch/SpecLife.lean). -/
def simWhole (L : BatchProtocol I X) (Sm : Sims L) (i₀ : I) : Simulator L where
  σ := ℕ × (ℕ → L.EncodingRandomness)
  off := (unif L.EncodingRandomness).bind fun r =>
    (simSess L.offline Sm.T () (L.encodeIndex i₀ r)).map fun a => (a, (0, fun _ => r))
  fresh := fun s => (unif L.EncodingRandomness).bind fun r =>
    (simSess L.link Sm.Lk () (L.encodeIndex i₀ (s.2 0), L.encodeIndex i₀ r)).map fun a =>
      (a, (s.1 + 1, Function.update s.2 (s.1 + 1) r))
  session := fun s e J xs => (simBsess L.onlineBatch Sm.B J xs (L.encodeIndex i₀ (s.2 e))).map fun a => (a, s)
  read := fun s e p => PMF.pure (L.encodeIndex i₀ (s.2 e) p, s)

/-! ## 2. The bounds -/

/-- The bounds on an environment. -/
structure Bounds where
  /-- further encoded indices -/
  nenc : ℕ
  /-- sessions on the encoded index e -/
  sess : ℕ → ℕ
  /-- single reads of the encoded index e -/
  reads : ℕ → ℕ
  /-- slots shown in one session -/
  shown : ℕ

/-- The environment keeps the bounds, on every path, when c further encoded indices exist and the
encoded index e has served us e sessions and ur e reads. ok: the instance is in the relation with
the index. -/
def Env.Adm (B : Bounds) (ok : X → Prop) : Env L α → ℕ → (ℕ → ℕ) → (ℕ → ℕ) → Prop
  | .stop _, _, _, _ => True
  | .fresh k, c, us, ur => c < B.nenc ∧ ∀ a, (k a).Adm B ok (c + 1) us ur
  | .session e J xs rest k, c, us, ur =>
    e ≤ c ∧ us e < B.sess e ∧ J.card ≤ B.shown ∧ (∀ j, ok (xs j)) ∧
    (∀ j x, rest j = some x → ok x) ∧ ∀ a, (k a).Adm B ok c (Function.update us e (us e + 1)) ur
  | .read e _ k, c, us, ur =>
    e ≤ c ∧ ur e < B.reads e ∧ ∀ y, (k y).Adm B ok c us (Function.update ur e (ur e + 1))
  | .draw _ _ k, c, us, ur => ∀ y, (k y).Adm B ok c us ur

/-- With `BatchProtocol.Reads` and `Env.Adm`, the budget: no encoded index is read at more than b positions
in all. -/
def Bounds.Fits (B : Bounds) (b qT qpar qch qon : ℕ) : Prop :=
  qT + B.nenc * qpar + B.sess 0 * qon + B.reads 0 ≤ b ∧
  ∀ j, 1 ≤ j → j ≤ B.nenc → qch + B.sess j * qon + B.reads j ≤ b

/-- The number of sessions allowed in all. -/
def Bounds.total (B : Bounds) : ℕ := ∑ j ∈ Finset.range (B.nenc + 1), B.sess j

/-- The error. -/
def Bounds.err (B : Bounds) (zT zL zO : ℝ≥0∞) : ℝ≥0∞ := zT + B.nenc * zL + B.total * (B.shown * zO)

/-! ## 3. The property -/

/-- Honest-verifier zero knowledge of the whole object, for environments within the bounds B, with
the simulator S and the error z. -/
def HVZKWhole (L : BatchProtocol I X) (Ryes : I → X → Prop) (B : Bounds) (S : Simulator L) (z : ℝ≥0∞) :
    Prop :=
  ∀ (i : I) (α : Type) (E : Sess L.offline → Env L α),
    (∀ a, (E a).Adm B (Ryes i) 0 (fun _ => 0) fun _ => 0) →
    tv ((realHost L i).view E) (S.host.view E) ≤ z

/-! ## 4. The same with the view written out -/

/-- What one step adds to the view: the public part of the request, and what is shown of the run. -/
inductive Step (L : BatchProtocol I X) : Type
  | off (a : Sess L.offline) : Step L
  | link (a : Sess L.link) : Step L
  | session (e : ℕ) (J : Finset (Fin L.maxBatchSize)) (xs : J → X) (a : BSess L.onlineBatch J) : Step L
  | read (e : ℕ) (p : Fin L.wordLength) (y : L.Symbol) : Step L

/-- A request. -/
inductive Req (L : BatchProtocol I X) : Type
  | stop : Req L
  | fresh : Req L
  | session (e : ℕ) (J : Finset (Fin L.maxBatchSize)) (xs : J → X) (rest : {j : Fin L.maxBatchSize // j ∉ J} → Option X) : Req L
  | read (e : ℕ) (p : Fin L.wordLength) : Req L

/-- An environment that is a function F from the view so far to the next request, played for at
most n steps from the view v on; its output is the view. -/
def Env.ofFun (F : List (Step L) → Req L) : ℕ → List (Step L) → Env L (List (Step L))
  | 0, v => .stop v
  | n + 1, v => match F v with
    | .stop => .stop v
    | .fresh => .fresh fun a => Env.ofFun F n (v ++ [.link a])
    | .session e J xs rest => .session e J xs rest fun a => Env.ofFun F n (v ++ [.session e J xs a])
    | .read e p => .read e p fun y => Env.ofFun F n (v ++ [.read e p y])

/-- The view of at most n steps with an environment that has coins ω of law ν. -/
def viewOf (H : Host L) {Ω : Type} (ν : PMF Ω) (F : Ω → List (Step L) → Req L) (n : ℕ) :
    PMF (List (Step L)) :=
  H.view fun a => .draw Ω ν fun ω => Env.ofFun (F ω) n [.off a]

namespace Spec

/-- Honest-verifier zero knowledge of the whole object from zero knowledge of the runs, simulator
named. (not all hypotheses are named here: see the statement below) -/
def hvzk_whole : Prop :=
  ∀ (I X : Type) (L : BatchProtocol I X) (Ryes : I → X → Prop) (b qT qpar qch qon : ℕ) (zT zL zO : ℝ≥0∞),
    L.Wired → L.Reads b qT qpar qch qon →
    ∀ Sm : Sims L, Sm.Good Ryes zT zL zO →
      ∀ B : Bounds,
        B.Fits b qT qpar qch qon → ∀ i₀ : I, HVZKWhole L Ryes B (simWhole L Sm i₀) (B.err zT zL zO)

/-- The same from the hiding properties of the interface: one triple of run simulators for all
bounds and all i₀. (not all hypotheses are named here: see the statement below) -/
def hvzk_whole_hiding : Prop :=
  ∀ (I X : Type) (L : BatchProtocol I X) (Ryes : I → X → Prop) (b qT qpar qch qon : ℕ) (zT zL zO : ℝ≥0∞),
    L.Wired → L.Reads b qT qpar qch qon → L.Hiding Ryes zT zL zO →
    ∃ Sm : Sims L, ∀ B : Bounds,
      B.Fits b qT qpar qch qon → ∀ i₀ : I, HVZKWhole L Ryes B (simWhole L Sm i₀) (B.err zT zL zO)

/-- Under the hypotheses below: the property gives closeness of the views, for environments that
are functions of the view, with coins, and for any number of steps. -/
def hvzk_view : Prop :=
  ∀ (I X : Type) (L : BatchProtocol I X) (Ryes : I → X → Prop) (B : Bounds) (S : Simulator L) (z : ℝ≥0∞),
    HVZKWhole L Ryes B S z →
    ∀ (i : I) (Ω : Type) (ν : PMF Ω) (F : Ω → List (Step L) → Req L) (n : ℕ),
      (∀ ω a, (Env.ofFun (F ω) n [.off a]).Adm B (Ryes i) 0 (fun _ => 0) fun _ => 0) →
      tv (viewOf (realHost L i) ν F n) (viewOf S.host ν F n) ≤ z

end Spec
end Hiop
