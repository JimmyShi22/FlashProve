-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Hiop/Seeded/Form.lean: the experiment of Hiop/Seeded/Whole.lean, free of the three protocols.

Definitions and one statement; its proof is in Hiop/Seeded/FormProof.lean. A general theorem's type;
it states no goal of the release.

Hiop/Seeded/Whole.lean has an experiment on the whole object in which the environment names the seed
of each out-of-domain (OOD) sample. Its proof uses of the three protocols only this: a simulated run
draws something, reads the encoded index(es) at positions that hang on what it drew, and then draws
what it shows from the symbols read. Here that is all that is left of a run. Of the object
L : `Iop.HolographicProtocol` (Hiop/RecInterface.lean) only the encoding and the OOD answer occur: `encodeIndex`, `honestOutOfDomainAnswer`,
their types. So one proof serves several experiments:
  sessions with batches and uniform verifier's randomness (Hiop/Seeded/Whole.lean);
  sessions with one slot whose verifier's randomness is read off an auxiliary value with a law of
    its own, which is shown too (Hiop/Seeded/Game.lean).

Main names:
  `Form`: the types of what a run is asked with and of what it shows.
  `RunSim`: a simulated run as data: `Aux`, its law `μ`, the positions `reads a`, the law
    `out a answers` of what is shown. `RunSim.law str`: its law on the word(s) str.
  `EnvF`, `HostF`, `EnvF.run`, `HostF.view`, `EnvF.Adm`: the experiment, as in
    Hiop/Seeded/Whole.lean.
  `LawsF`, `LawsF.host`: the real side, for given laws of runs.
  `SimulatorF`, `SimsF`, `simWholeF`: the simulator.
  The premises: `HidE` (at every seed of Gs the law of (honest answer, any b positions) does not
    depend on the index), `SimsF.Counts` (how many positions a simulated run reads), `LawsF.Near`
    (each real run is near the simulated run on the true encodings), `BoundsR.Fits`.
  `ViewNearF`: the property, for one host: on the real side that is ONE index.
  `Spec.form_laws`: the statement. It speaks of ONE index: the simulated runs Sm stand under the
    same quantifier as the index, so a caller could take others for each index. Alone it is NO
    statement on hiding: it holds even of a real side that shows the index outright, with simulated
    runs that do the same. A statement on hiding fixes Sm and i₀ before the index, as those of
    Hiop/Seeded/Whole.lean for given provers and `Spec.lifeSeeded` (Hiop/Seeded/Game.lean) do.

Limits: those of Hiop/Seeded/Whole.lean.
Terms: lean/GLOSSARY.md.

-/
import Hiop.RecWhole

set_option autoImplicit false

noncomputable section

namespace Hiop.Seeded
open Prob Iop
open scoped ENNReal

/-! ## 1. Forms of runs, simulated runs -/

/-- What the three kinds of runs are asked with and what they show, as types. -/
structure Form (X : Type) where
  /-- what a run of the first kind (on one encoded index) shows -/
  RT : Type
  /-- what a run of the second kind (on the encoded indices 0 and e) shows -/
  RL : Type
  /-- what a session is asked with, as far as the simulator is told -/
  QB : Type
  /-- the rest of what a session is asked with -/
  HB : QB → Type
  /-- what a session shows -/
  RB : QB → Type
  /-- how many slots a session shows: its error is counted that often -/
  wt : QB → ℕ
  /-- all instances of the session meet ok -/
  okB : (X → Prop) → (q : QB) → HB q → Prop

/-- A simulated run: draw a from μ; read the positions `reads a`; draw what is shown from a and the
symbols read. -/
structure RunSim (Pos Sym Out : Type) where
  Aux : Type
  μ : PMF Aux
  reads : Aux → Finset Pos
  out : Aux → (Pos → Option Sym) → PMF Out

open Classical in
/-- The law of the simulated run on the word(s) str. -/
def RunSim.law {Pos Sym Out : Type} (R : RunSim Pos Sym Out) (str : Pos → Sym) : PMF Out :=
  R.μ.bind fun a => R.out a fun p => if p ∈ R.reads a then some (str p) else none

variable {I X : Type}

/-! ## 2. Environments, hosts, the experiment -/

/-- An environment, after the first encoded index and its OOD sample, as a decision tree with
outputs in α. -/
inductive EnvF (L : HolographicProtocol I X) (F : Form X) (α : Type) : Type 1
  | stop (a : α) : EnvF L F α
  /-- a further encoded index, with its OOD sample at the seed s; go on by the sample -/
  | fresh (s : L.OutOfDomainSeed) (k : L.Rec → EnvF L F α) : EnvF L F α
  /-- a run of the first kind on the encoded index e -/
  | test (e : ℕ) (k : F.RT → EnvF L F α) : EnvF L F α
  /-- a run of the second kind on the encoded indices 0 and e -/
  | link (e : ℕ) (k : F.RL → EnvF L F α) : EnvF L F α
  /-- a session on the encoded index e -/
  | session (e : ℕ) (q : F.QB) (h : F.HB q) (k : F.RB q → EnvF L F α) : EnvF L F α
  /-- the symbol at position p of the encoded index e -/
  | read (e : ℕ) (p : Fin L.wordLength) (k : L.Symbol → EnvF L F α) : EnvF L F α
  | draw (β : Type) (d : PMF β) (k : β → EnvF L F α) : EnvF L F α

/-- Who answers the environment. `start` and `fresh` are handed the seed. -/
structure HostF (L : HolographicProtocol I X) (F : Form X) where
  σ : Type
  start : L.OutOfDomainSeed → PMF (L.Rec × σ)
  fresh : σ → L.OutOfDomainSeed → PMF (L.Rec × σ)
  test : σ → ℕ → PMF (F.RT × σ)
  link : σ → ℕ → PMF (F.RL × σ)
  session : σ → ℕ → (q : F.QB) → F.HB q → PMF (F.RB q × σ)
  read : σ → ℕ → Fin L.wordLength → PMF (L.Symbol × σ)

variable {L : HolographicProtocol I X} {F : Form X} {α : Type}

def EnvF.run (H : HostF L F) : EnvF L F α → H.σ → PMF α
  | .stop a, _ => PMF.pure a
  | .fresh s k, st => (H.fresh st s).bind fun p => (k p.1).run H p.2
  | .test e k, st => (H.test st e).bind fun p => (k p.1).run H p.2
  | .link e k, st => (H.link st e).bind fun p => (k p.1).run H p.2
  | .session e q h k, st => (H.session st e q h).bind fun p => (k p.1).run H p.2
  | .read e p k, st => (H.read st e p).bind fun y => (k y.1).run H y.2
  | .draw _ d k, st => d.bind fun y => (k y).run H st

/-- The experiment: the environment names s₀; the first encoded index and its OOD sample at s₀; then
the environment, which has seen the sample. -/
def HostF.view (H : HostF L F) (s₀ : L.OutOfDomainSeed) (E : L.Rec → EnvF L F α) : PMF α :=
  (H.start s₀).bind fun p => (E p.1).run H p.2

/-! ## 3. The real side, for given laws of runs -/

/-- The OOD sample, the laws of what is shown of the three kinds of runs, and the symbols of an
encoded index, as functions of (committer's randomness, seed). The laws of runs are also handed the
number of the encoded index on which the run was asked for (second kind: of the further one). -/
structure LawsF (L : HolographicProtocol I X) (F : Form X) where
  rc : L.EncodingRandomness × L.OutOfDomainSeed → L.Rec
  T : ℕ → L.EncodingRandomness × L.OutOfDomainSeed → PMF F.RT
  Lk : ℕ → L.EncodingRandomness × L.OutOfDomainSeed → L.EncodingRandomness × L.OutOfDomainSeed → PMF F.RL
  B : ℕ → L.EncodingRandomness × L.OutOfDomainSeed → (q : F.QB) → F.HB q → PMF (F.RB q)
  y : L.EncodingRandomness × L.OutOfDomainSeed → Fin L.wordLength → L.Symbol

/-- The host with these laws. The state: the number of further encoded indices, and (committer's
randomness, seed) of each encoded index. The seed is the one that was handed in; the committer's
randomness is drawn uniformly after that. -/
def LawsF.host (W : LawsF L F) : HostF L F where
  σ := ℕ × (ℕ → L.EncodingRandomness × L.OutOfDomainSeed)
  start := fun s => (unif L.EncodingRandomness).map fun r => (W.rc (r, s), (0, fun _ => (r, s)))
  fresh := fun st s =>
    (unif L.EncodingRandomness).map fun r => (W.rc (r, s), (st.1 + 1, Function.update st.2 (st.1 + 1) (r, s)))
  test := fun st e => (W.T e (st.2 e)).map fun a => (a, st)
  link := fun st e => (W.Lk e (st.2 0) (st.2 e)).map fun a => (a, st)
  session := fun st e q h => (W.B e (st.2 e) q h).map fun a => (a, st)
  read := fun st e p => PMF.pure (W.y (st.2 e) p, st)

/-! ## 4. Simulators -/

/-- A simulator. No index; of a session: e and the part q of what it was asked with. -/
structure SimulatorF (L : HolographicProtocol I X) (F : Form X) where
  σ : Type
  start : L.OutOfDomainSeed → PMF (L.Rec × σ)
  fresh : σ → L.OutOfDomainSeed → PMF (L.Rec × σ)
  test : σ → ℕ → PMF (F.RT × σ)
  link : σ → ℕ → PMF (F.RL × σ)
  session : σ → ℕ → (q : F.QB) → PMF (F.RB q × σ)
  read : σ → ℕ → Fin L.wordLength → PMF (L.Symbol × σ)

def SimulatorF.host (S : SimulatorF L F) : HostF L F where
  σ := S.σ
  start := S.start
  fresh := S.fresh
  test := S.test
  link := S.link
  session := fun st e q _ => S.session st e q
  read := S.read

/-- The simulated runs: for each number of an encoded index, each OOD sample (second kind: both) and
each q. -/
structure SimsF (L : HolographicProtocol I X) (F : Form X) where
  T : ℕ → L.Rec → RunSim (Fin L.wordLength) L.Symbol F.RT
  Lk : ℕ → L.Rec × L.Rec → RunSim (Fin L.wordLength ⊕ Fin L.wordLength) L.Symbol F.RL
  B : ℕ → (q : F.QB) → L.Rec → RunSim (Fin L.wordLength) L.Symbol (F.RB q)

/-- The laws of the simulator's side: encodings of the index j, j's own answers, simulated runs. -/
def simLawsF (L : HolographicProtocol I X) (F : Form X) (Sm : SimsF L F) (j : I) : LawsF L F where
  rc := fun u => L.recOf j u.1 u.2
  T := fun e u => (Sm.T e (L.recOf j u.1 u.2)).law (L.encodeIndex j u.1)
  Lk := fun e u u' =>
    (Sm.Lk e (L.recOf j u.1 u.2, L.recOf j u'.1 u'.2)).law (Sum.elim (L.encodeIndex j u.1) (L.encodeIndex j u'.1))
  B := fun e u q _ => (Sm.B e q (L.recOf j u.1 u.2)).law (L.encodeIndex j u.1)
  y := fun u p => L.encodeIndex j u.1 p

/-- The simulator of the theorem: an encoding of the fixed index i₀ in the place of each encoded
index, i₀'s own answer at the seed that was handed in, the simulated runs. -/
def simWholeF (L : HolographicProtocol I X) (F : Form X) (Sm : SimsF L F) (i₀ : I) : SimulatorF L F where
  σ := ℕ × (ℕ → L.EncodingRandomness × L.OutOfDomainSeed)
  start := (simLawsF L F Sm i₀).host.start
  fresh := (simLawsF L F Sm i₀).host.fresh
  test := (simLawsF L F Sm i₀).host.test
  link := (simLawsF L F Sm i₀).host.link
  session := fun st e q =>
    ((Sm.B e q (L.recOf i₀ (st.2 e).1 (st.2 e).2)).law (L.encodeIndex i₀ (st.2 e).1)).map fun a => (a, st)
  read := (simLawsF L F Sm i₀).host.read

/-! ## 5. The bounds -/

/-- The environment keeps the bounds (`BoundsR`, `UsedR`: Hiop/RecWhole.lean) and names seeds of Gs
alone, on every path, when c further encoded indices exist and u has been asked so far. -/
def EnvF.Adm (B : BoundsR) (Gs : L.OutOfDomainSeed → Prop) (ok : X → Prop) : EnvF L F α → ℕ → UsedR → Prop
  | .stop _, _, _ => True
  | .fresh s k, c, u => Gs s ∧ c < B.nenc ∧ ∀ a, (k a).Adm B Gs ok (c + 1) u
  | .test e k, c, u =>
    e ≤ c ∧ u.tests e < B.tests e ∧ ∀ a, (k a).Adm B Gs ok c { u with tests := bump u.tests e }
  | .link e k, c, u =>
    1 ≤ e ∧ e ≤ c ∧ u.links e < B.links e ∧
      ∀ a, (k a).Adm B Gs ok c { u with links := bump u.links e }
  | .session e q h k, c, u =>
    e ≤ c ∧ u.sess e < B.sess e ∧ F.wt q ≤ B.shown ∧ F.okB ok q h ∧
      ∀ a, (k a).Adm B Gs ok c { u with sess := bump u.sess e }
  | .read e _ k, c, u =>
    e ≤ c ∧ u.reads e < B.reads e ∧ ∀ y, (k y).Adm B Gs ok c { u with reads := bump u.reads e }
  | .draw _ _ k, c, u => ∀ y, (k y).Adm B Gs ok c u

/-! ## 6. The premises -/

/-- At every seed of Gs the law of (honest answer, the encoded index at any b positions) does not
depend on the index. -/
def HidE (L : HolographicProtocol I X) (Gs : L.OutOfDomainSeed → Prop) (b : ℕ) : Prop :=
  ∀ (S : Finset (Fin L.wordLength)), S.card ≤ b → ∀ (s : L.OutOfDomainSeed), Gs s →
    ∀ i i', (unif L.EncodingRandomness).map (fun r => (L.honestOutOfDomainAnswer i r s, fun p : S => L.encodeIndex i r p)) =
      (unif L.EncodingRandomness).map (fun r => (L.honestOutOfDomainAnswer i' r s, fun p : S => L.encodeIndex i' r p))

/-- How many positions the simulated runs read. -/
structure SimsF.Counts (Sm : SimsF L F) (qT qpar qch qon : ℕ) : Prop where
  cntT  : ∀ e x a, ((Sm.T e x).reads a).card ≤ qT
  cntLp : ∀ e x a, (((Sm.Lk e x).reads a).filter (fun p => p.isLeft)).card ≤ qpar
  cntLc : ∀ e x a, (((Sm.Lk e x).reads a).filter (fun p => p.isRight)).card ≤ qch
  cntB  : ∀ e q x a, ((Sm.B e q x).reads a).card ≤ qon

/-- What the theorem needs of the real side: its OOD samples and symbols are those of the encodings
of i, and each of its runs is near the simulated run on the true encodings and samples, at every
number, for EVERY value of the committer's randomness and every seed of Gs. -/
structure LawsF.Near (W : LawsF L F) (Sm : SimsF L F) (Gs : L.OutOfDomainSeed → Prop) (i : I) (ok : X → Prop)
    (zT zL zO : ℝ≥0∞) : Prop where
  rc : ∀ u, W.rc u = L.recOf i u.1 u.2
  y  : ∀ u p, W.y u p = L.encodeIndex i u.1 p
  T  : ∀ e u, Gs u.2 → tv (W.T e u) ((simLawsF L F Sm i).T e u) ≤ zT
  Lk : ∀ e u u', Gs u.2 → Gs u'.2 → tv (W.Lk e u u') ((simLawsF L F Sm i).Lk e u u') ≤ zL
  B  : ∀ e u q h, Gs u.2 → F.okB ok q h →
    tv (W.B e u q h) ((simLawsF L F Sm i).B e u q h) ≤ F.wt q * zO

/-! ## 7. The property and the statement -/

/-- What an environment within the bounds B, which names the seeds (in Gs), sees of the host H is
within z of what it sees of the simulator S. One host: on the real side that is ONE index. -/
def ViewNearF (H : HostF L F) (Gs : L.OutOfDomainSeed → Prop) (ok : X → Prop) (B : BoundsR)
    (S : SimulatorF L F) (z : ℝ≥0∞) : Prop :=
  ∀ (α : Type) (s₀ : L.OutOfDomainSeed) (E : L.Rec → EnvF L F α), Gs s₀ →
    (∀ a, (E a).Adm B Gs ok 0 UsedR.zero) → tv (H.view s₀ E) (S.host.view s₀ E) ≤ z

namespace Spec

/-- For given laws of runs: any real side that is near the simulated runs. It speaks of ONE index i:
the simulated runs Sm stand under the same quantifier, so nothing here says that one Sm serves all
indices. -/
def form_laws : Prop :=
  ∀ (I X : Type) (L : HolographicProtocol I X) (F : Form X) (Gs : L.OutOfDomainSeed → Prop) (ok : X → Prop)
      (b qT qpar qch qon : ℕ) (zT zL zO : ℝ≥0∞),
    HidE L Gs b →
    ∀ Sm : SimsF L F, Sm.Counts qT qpar qch qon →
      ∀ (W : LawsF L F) (i : I), W.Near Sm Gs i ok zT zL zO →
        ∀ B : BoundsR, B.Fits b qT qpar qch qon →
          ∀ i₀ : I, ViewNearF W.host Gs ok B (simWholeF L F Sm i₀) (B.err zT zL zO)

end Spec
end Hiop.Seeded
