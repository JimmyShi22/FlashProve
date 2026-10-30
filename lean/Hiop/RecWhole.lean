-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Hiop/RecWhole.lean: honest-verifier zero knowledge of the whole object, with records.

Definitions and statements (the proofs: Hiop/RecWholeProof.lean; of `Spec.rec_main_zk`:
Hiop/RecWholeMain.lean). Hiop/Whole.lean's header says what an
environment, a host and a simulator are, and how the notion differs from the one on paper; these
are not told whole here.
The object is an `Iop.HolographicProtocol` (Hiop/RecInterface.lean), the holographic interactive oracle proof with a
record phase.

The experiment, for an object L : Iop.HolographicProtocol I X. At the start an encoded index (number 0) is made with
fresh committer's randomness, and its record phase is played: a uniform seed, the honest answer. The
record is shown. Then an environment, which has seen everything shown so far, asks step by step for
    "fresh": a further encoded index, made with fresh randomness, with its record phase; the record
      is shown;
    "test e": the offline IOP on the encoded index e and its record;
    "link e": the link IOP on the encoded indices 0 and e (1 ≤ e) and their records;
    "session": a session on the encoded index e and its record, with a batch of instances and a set
      J of slots that are shown;
    "read": the symbol at one position of the encoded index e;
  or it draws coins, or it stops with an output.
Each encoded index has exactly one record phase, by the form of the experiment: there is no request
for a second one. The record phase lies outside the three protocols and is simulated with the
encoded index.
WIDER THAN ON PAPER: the offline IOP and a link are requests of their own. So they may be made late,
never, or again on the same encoded index with the same record; each one begun counts in the budget.
The paper's course (one offline IOP at the start; each further encoded index followed by its link)
is the case tests 0 = 1, tests e = 0, links e = 1.
A simulator has, by its type, no access to the index; of a session it is given e, J and the
instances of J. The simulator of the theorem (`simWholeR`) keeps, in the place of each encoded
index, an encoding of a fixed index i₀ with a uniform seed and the answer of i₀, shows that record,
and answers each request for a run by the simulator of the run, which is given the record(s) as part
of the explicit instance and the symbols at the verifier's positions (exactly, by its type:
`SimOf Q`, Compile/Life.lean:
`Y → (ρ : Rho Q.shape) → (E.Pos → Option E.Sym) → PMF (Option (DView Q))`; `BSimOf Q N`,
Compile/Batch/SpecLife.lean: `(J : Finset (Fin N)) → (J → X) → (J → Rho Q.loc.shape) →`
`(E.Pos → Option E.Sym) → PMF (J → Option (DView Q.loc))`).
The budget (`BoundsR.Fits`): for each encoded index e: tests e · qT + (if e = 0: all links · qpar) +
links e · qch + sess e · qon + reads e ≤ b. b is the number of positions that an encoded index hides
beside its record (`ReadsR.hidE`): the record costs nothing.
The error: (all tests) · zT + (all links) · zL + (all sessions) · shown · zO. No term for the
encoded indices and their records: they hide exactly (`ReadsR.hidE`: by type an equation of laws; a
field of `HolographicProtocol.ReadsR`, Hiop/RecInterface.lean, which is a premise of `Spec.rec_hvzk_whole`).

Main names:
  `Spec.rec_hvzk_whole`: from `WiredR`, `ReadsR` and good simulators of the runs, simulator named.
    (not all hypotheses are named here: see its statement)
  `Spec.rec_hvzk_whole_hiding`: from `HidingR`: one triple of run simulators for all bounds. (not
    all hypotheses are named here: see its statement)
  `Spec.rec_main_zk`: for the object that the four sub-protocols form (Hiop/RecBuild.lean), from the
    lists without their items on knowledge soundness (`SubsR.HypH`, Hiop/RecBuild.lean). (not all
    hypotheses are named here: see its statement)

Limits: declared, beside the differences that Hiop/Whole.lean lists: a run that is broken off is not
modelled (every run asked for is played to its end and counts in full); the simulator does not
answer from a list of uniform locations made in advance.
Terms: lean/GLOSSARY.md.
-/
/- Limits: at a record phase that is not empty no theorem of this library states that the hypotheses
   of `rec_main_zk` can be met together. -/
import Hiop.RecMain
import Compile.Batch.SpecLife

set_option autoImplicit false

noncomputable section

namespace Hiop
open Prob Iop Compile.Lifetime Compile.BatchLife
open scoped ENNReal

variable {I X : Type}

/-! ## 1. Environments, hosts, the experiment -/

/-- An environment, after the first encoded index and its record phase, as a decision tree with
outputs in α. -/
inductive EnvR (L : HolographicProtocol I X) (α : Type) : Type 1
  | stop (a : α) : EnvR L α
  /-- a further encoded index and its record phase; go on by the record -/
  | fresh (k : L.Rec → EnvR L α) : EnvR L α
  /-- the offline IOP on the encoded index e -/
  | test (e : ℕ) (k : Sess L.offline → EnvR L α) : EnvR L α
  /-- the link IOP on the encoded indices 0 and e -/
  | link (e : ℕ) (k : Sess L.link → EnvR L α) : EnvR L α
  /-- a session on the encoded index e: the slots J are shown and hold the instances xs; rest is
  what the other slots hold -/
  | session (e : ℕ) (J : Finset (Fin L.maxBatchSize)) (xs : J → X)
      (rest : {j : Fin L.maxBatchSize // j ∉ J} → Option X) (k : BSess L.onlineBatch J → EnvR L α) : EnvR L α
  /-- the symbol at position p of the encoded index e -/
  | read (e : ℕ) (p : Fin L.wordLength) (k : L.Symbol → EnvR L α) : EnvR L α
  | draw (β : Type) (d : PMF β) (k : β → EnvR L α) : EnvR L α

/-- Who answers the environment. -/
structure HostR (L : HolographicProtocol I X) where
  σ : Type
  start : PMF (L.Rec × σ)
  fresh : σ → PMF (L.Rec × σ)
  test : σ → ℕ → PMF (Sess L.offline × σ)
  link : σ → ℕ → PMF (Sess L.link × σ)
  session : σ → ℕ → (J : Finset (Fin L.maxBatchSize)) → (J → X) →
    ({j : Fin L.maxBatchSize // j ∉ J} → Option X) → PMF (BSess L.onlineBatch J × σ)
  read : σ → ℕ → Fin L.wordLength → PMF (L.Symbol × σ)

variable {L : HolographicProtocol I X} {α : Type}

def EnvR.run (H : HostR L) : EnvR L α → H.σ → PMF α
  | .stop a, _ => PMF.pure a
  | .fresh k, s => (H.fresh s).bind fun p => (k p.1).run H p.2
  | .test e k, s => (H.test s e).bind fun p => (k p.1).run H p.2
  | .link e k, s => (H.link s e).bind fun p => (k p.1).run H p.2
  | .session e J xs rest k, s => (H.session s e J xs rest).bind fun p => (k p.1).run H p.2
  | .read e p k, s => (H.read s e p).bind fun q => (k q.1).run H q.2
  | .draw _ d k, s => d.bind fun y => (k y).run H s

/-- The experiment: the first encoded index and its record phase; then the environment, which has
seen the record. -/
def HostR.view (H : HostR L) (E : L.Rec → EnvR L α) : PMF α :=
  H.start.bind fun p => (E p.1).run H p.2

/-- The real side on the index i. The state: the number of further encoded indices, and (committer's
randomness, seed) of each encoded index. -/
def realHostR (L : HolographicProtocol I X) (i : I) : HostR L where
  σ := ℕ × (ℕ → L.EncodingRandomness × L.OutOfDomainSeed)
  start := (unif (L.EncodingRandomness × L.OutOfDomainSeed)).map fun u => (L.recOf i u.1 u.2, (0, fun _ => u))
  fresh := fun s =>
    (unif (L.EncodingRandomness × L.OutOfDomainSeed)).map fun u =>
      (L.recOf i u.1 u.2, (s.1 + 1, Function.update s.2 (s.1 + 1) u))
  test := fun s e =>
    (sess L.honestOfflineProver (i, (s.2 e).1, (s.2 e).2) (L.recOf i (s.2 e).1 (s.2 e).2)).map fun a => (a, s)
  link := fun s e =>
    (sess L.honestLinkProver (i, s.2 0, s.2 e) (L.recOf i (s.2 0).1 (s.2 0).2, L.recOf i (s.2 e).1 (s.2 e).2)).map
      fun a => (a, s)
  session := fun s e J xs rest =>
    (bsess L.honestOnlineBatchProver (i, (s.2 e).1, (s.2 e).2)
        (vec J (fun j => (xs j, L.recOf i (s.2 e).1 (s.2 e).2))
          (fun j => (rest j).map fun x => (x, L.recOf i (s.2 e).1 (s.2 e).2))) J).map
      fun a => (a, s)
  read := fun s e p => PMF.pure (L.encodeIndex i (s.2 e).1 p, s)

/-- A simulator. No index; of a session: e, J and the instances of J. -/
structure SimulatorR (L : HolographicProtocol I X) where
  σ : Type
  start : PMF (L.Rec × σ)
  fresh : σ → PMF (L.Rec × σ)
  test : σ → ℕ → PMF (Sess L.offline × σ)
  link : σ → ℕ → PMF (Sess L.link × σ)
  session : σ → ℕ → (J : Finset (Fin L.maxBatchSize)) → (J → X) → PMF (BSess L.onlineBatch J × σ)
  read : σ → ℕ → Fin L.wordLength → PMF (L.Symbol × σ)

def SimulatorR.host (S : SimulatorR L) : HostR L where
  σ := S.σ
  start := S.start
  fresh := S.fresh
  test := S.test
  link := S.link
  session := fun s e J xs _ => S.session s e J xs
  read := S.read

/-- One simulator for each of the three protocols. -/
structure SimsR (L : HolographicProtocol I X) where
  T : SimOf L.offline
  Lk : SimOf L.link
  B : BSimOf L.onlineBatch L.maxBatchSize

/-- The three simulators are good, on honest records (exactly: `validT`, `validL`, `validB Ryes`,
Hiop/RecInterface.lean). -/
structure SimsR.Good (Sm : SimsR L) (Ryes : I → X → Prop) (zT zL zO : ℝ≥0∞) : Prop where
  goodT : ∀ w x,
    L.validT w x → prRho {ρ | L.honestOfflineProver.output w x ρ ≠ Sm.T x ρ (L.offline.extAns x ρ (L.honestOfflineProver.ext w))} ≤ zT
  goodL : ∀ w x,
    L.validL w x → prRho {ρ | L.honestLinkProver.output w x ρ ≠ Sm.Lk x ρ (L.link.extAns x ρ (L.honestLinkProver.ext w))} ≤ zL
  goodB : ∀ (w : I × L.EncodingRandomness × L.OutOfDomainSeed) (x : Fin L.maxBatchSize → Option (X × L.Rec)),
    (∀ j xj, x j = some xj → L.validB Ryes w xj) →
    ∀ (J : Finset (Fin L.maxBatchSize)) (xs : J → X × L.Rec), (∀ j : J, x j = some (xs j)) →
      prBRho {ρ | L.honestOnlineBatchProver.output w x ρ J ≠
            Sm.B J xs (fun j => ρ.slot j.1)
              (L.onlineBatch.extAnsJ J xs (fun j => ρ.slot j.1) (L.honestOnlineBatchProver.ext w))} ≤ J.card * zO

/-- The simulator of the theorem. -/
def simWholeR (L : HolographicProtocol I X) (Sm : SimsR L) (i₀ : I) : SimulatorR L where
  σ := ℕ × (ℕ → L.EncodingRandomness × L.OutOfDomainSeed)
  start := (unif (L.EncodingRandomness × L.OutOfDomainSeed)).map fun u => (L.recOf i₀ u.1 u.2, (0, fun _ => u))
  fresh := fun s =>
    (unif (L.EncodingRandomness × L.OutOfDomainSeed)).map fun u =>
      (L.recOf i₀ u.1 u.2, (s.1 + 1, Function.update s.2 (s.1 + 1) u))
  test := fun s e =>
    (simSess L.offline Sm.T (L.recOf i₀ (s.2 e).1 (s.2 e).2) (L.encodeIndex i₀ (s.2 e).1)).map fun a => (a, s)
  link := fun s e =>
    (simSess L.link Sm.Lk (L.recOf i₀ (s.2 0).1 (s.2 0).2, L.recOf i₀ (s.2 e).1 (s.2 e).2)
        (L.encodeIndex i₀ (s.2 0).1, L.encodeIndex i₀ (s.2 e).1)).map fun a => (a, s)
  session := fun s e J xs =>
    (simBsess L.onlineBatch Sm.B J (fun j => (xs j, L.recOf i₀ (s.2 e).1 (s.2 e).2))
        (L.encodeIndex i₀ (s.2 e).1)).map fun a => (a, s)
  read := fun s e p => PMF.pure (L.encodeIndex i₀ (s.2 e).1 p, s)

/-! ## 2. The bounds -/

/-- The bounds on an environment. -/
structure BoundsR where
  /-- further encoded indices -/
  nenc : ℕ
  /-- offline IOPs begun on the encoded index e -/
  tests : ℕ → ℕ
  /-- links begun on the encoded indices 0 and e -/
  links : ℕ → ℕ
  /-- sessions begun on the encoded index e -/
  sess : ℕ → ℕ
  /-- single reads of the encoded index e -/
  reads : ℕ → ℕ
  /-- slots shown in one session -/
  shown : ℕ

/-- What has been asked of each encoded index so far. -/
structure UsedR where
  tests : ℕ → ℕ
  links : ℕ → ℕ
  sess  : ℕ → ℕ
  reads : ℕ → ℕ

def UsedR.zero : UsedR := ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0⟩

/-- one more at e -/
def bump (u : ℕ → ℕ) (e : ℕ) : ℕ → ℕ := Function.update u e (u e + 1)

/-- The environment keeps the bounds, on every path, when c further encoded indices exist and u has
been asked so far. ok: the instance is in the relation with the index. -/
def EnvR.Adm (B : BoundsR) (ok : X → Prop) : EnvR L α → ℕ → UsedR → Prop
  | .stop _, _, _ => True
  | .fresh k, c, u => c < B.nenc ∧ ∀ a, (k a).Adm B ok (c + 1) u
  | .test e k, c, u => e ≤ c ∧ u.tests e < B.tests e ∧ ∀ a, (k a).Adm B ok c { u with tests := bump u.tests e }
  | .link e k, c, u => 1 ≤ e ∧ e ≤ c ∧ u.links e < B.links e ∧ ∀ a, (k a).Adm B ok c { u with links := bump u.links e }
  | .session e J xs rest k, c, u =>
    e ≤ c ∧ u.sess e < B.sess e ∧ J.card ≤ B.shown ∧ (∀ j, ok (xs j)) ∧
    (∀ j x, rest j = some x → ok x) ∧ ∀ a, (k a).Adm B ok c { u with sess := bump u.sess e }
  | .read e _ k, c, u =>
    e ≤ c ∧ u.reads e < B.reads e ∧ ∀ y, (k y).Adm B ok c { u with reads := bump u.reads e }
  | .draw _ _ k, c, u => ∀ y, (k y).Adm B ok c u

/-- sums over the encoded indices -/
def BoundsR.sum (B : BoundsR) (f : ℕ → ℕ) : ℕ := ∑ j ∈ Finset.range (B.nenc + 1), f j

/-- The budget: no encoded index is read at more than b positions in all. (So it reads under
`ReadsR b qT qpar qch qon` and `EnvR.Adm B`: the definition is the inequality alone.) The record
costs nothing. -/
def BoundsR.Fits (B : BoundsR) (b qT qpar qch qon : ℕ) : Prop :=
  ∀ e, e ≤ B.nenc →
    B.tests e * qT + (if e = 0 then B.sum B.links * qpar else 0) +
        B.links e * qch + B.sess e * qon + B.reads e ≤ b

/-- The error. -/
def BoundsR.err (B : BoundsR) (zT zL zO : ℝ≥0∞) : ℝ≥0∞ :=
  B.sum B.tests * zT + B.sum B.links * zL + B.sum B.sess * (B.shown * zO)

/-! ## 3. The property -/

/-- Honest-verifier zero knowledge of the whole object with records, for environments within the
bounds B, with the simulator S and the error z. (`EnvR.Adm B (Ryes i)`: all instances of a batch,
the hidden ones too, in the relation with the index) -/
def HVZKWholeR (L : HolographicProtocol I X) (Ryes : I → X → Prop) (B : BoundsR) (S : SimulatorR L) (z : ℝ≥0∞) :
    Prop :=
  ∀ (i : I) (α : Type) (E : L.Rec → EnvR L α), (∀ a, (E a).Adm B (Ryes i) 0 UsedR.zero) →
    tv ((realHostR L i).view E) (S.host.view E) ≤ z

namespace Spec

/-- Honest-verifier zero knowledge of the whole object from honest-verifier zero knowledge of the
runs, simulator named. (not all hypotheses are named here: see the statement below) -/
def rec_hvzk_whole : Prop :=
  ∀ (I X : Type) (L : HolographicProtocol I X) (Ryes : I → X → Prop) (b qT qpar qch qon : ℕ) (zT zL zO : ℝ≥0∞),
    L.WiredR → L.ReadsR b qT qpar qch qon →
    ∀ Sm : SimsR L, Sm.Good Ryes zT zL zO →
      ∀ B : BoundsR, B.Fits b qT qpar qch qon →
        ∀ i₀ : I, HVZKWholeR L Ryes B (simWholeR L Sm i₀) (B.err zT zL zO)

/-- The same from the hiding properties of the interface: one triple of run simulators for all
bounds and all i₀. (not all hypotheses are named here: see the statement below) -/
def rec_hvzk_whole_hiding : Prop :=
  ∀ (I X : Type) (L : HolographicProtocol I X) (Ryes : I → X → Prop) (b qT qpar qch qon : ℕ) (zT zL zO : ℝ≥0∞),
    L.WiredR → L.ReadsR b qT qpar qch qon → L.HidingR Ryes zT zL zO →
    ∃ Sm : SimsR L, ∀ B : BoundsR,
      B.Fits b qT qpar qch qon → ∀ i₀ : I, HVZKWholeR L Ryes B (simWholeR L Sm i₀) (B.err zT zL zO)

/-- For the object that the four sub-protocols form. -/
def rec_main_zk : Prop :=
  ∀ (C : ConfigurationWithOutOfDomainSample) (S : SubsR C) (P : S.Nums) (b eR : ℕ), C.Props b eR → S.HypH P →
    ∃ Sm : SimsR S.lhr, ∀ B : BoundsR, B.Fits b P.linOff.q P.link.qpar P.link.qch P.linOn.q →
      ∀ i₀ : C.I, HVZKWholeR S.lhr (fun i x => ∃ c, C.Ryes i x c) B
        (simWholeR S.lhr Sm i₀) (B.err P.wf.pHid 0 P.req.pHid)

end Spec
end Hiop
