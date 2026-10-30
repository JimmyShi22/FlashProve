-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Hiop/Seeded/Whole.lean: what an environment sees of the whole object can be simulated without the
index, when the environment itself names the seed of each out-of-domain (OOD) sample.

Definitions and statements; the proofs are in Hiop/Seeded/WholeProof.lean. This file states general
theorems' types, for any object of the interface's type. It states no goal of the release, and at
the release's own object none of its premises has been shown.

The object is an `Iop.HolographicProtocol` (Hiop/RecInterface.lean): a holographic interactive oracle proof in which
each encoded index is followed by one OOD sample, the pair (seed, answer). That file and
Hiop/RecWhole.lean call the pair the record of the encoded index; `L.Rec`, `L.recOf` are its names.

Why this file. Hiop/RecWhole.lean has the same experiment with three differences.
  (1) There the host draws each seed uniformly. In a compiled argument the seed is computed from a
      hash value, by a map that need not be one to one, so its law is only near uniform. Here THE
      ENVIRONMENT NAMES THE SEED of each encoded index, the first one too, BEFORE the randomness of
      that encoded index is drawn, and after it has seen everything shown so far. So a seed may be
      any function of what has been shown and of coins of the environment's own. Of a seed that
      hangs on anything hidden (the randomness of its own or of another encoded index, a prover's
      coins) this file says nothing.
  (2) There the honest sides are the object's own fields honestOfflineProver, honestLinkProver, honestOnlineBatchProver. An object may hold silent
      placeholders in these fields. Here THE HONEST SIDES ARE ARGUMENTS: either three families of
      honest sides (`ProversS`) or, more generally, the laws of what is shown of a run (`LawsS`).
  (3) There a run is not told on which encoded index it runs. Here THE NUMBER e OF THE ENCODED INDEX
      IS HANDED to the honest side of a run and to its simulator: one honest side and one simulator
      for each number. (A prover may write that number in a plain part of its messages. One
      simulator for all numbers, which is not told the number, could not follow.)
What the premises leave out against Hiop/RecWhole.lean: nothing is asked of the index decoder (no
`dec_enc`). On acceptance nothing is asked here, as nothing is asked there.

The experiment, for an object L. The environment names a seed s₀. An encoded index (number 0) is
made with fresh committer's randomness, and the honest answer at s₀ is shown. Then the environment,
which has seen everything shown so far, asks step by step for
    "fresh s": a further encoded index, made with fresh randomness; the honest answer at the seed s
      is shown;
    "test e", "link e", "session e ..", "read e p": as in Hiop/RecWhole.lean;
  or it draws coins, or it stops with an output.
Each encoded index has exactly one OOD sample, by the form of the experiment: there is no request
for a second one.

The letter Gs: a set of seeds, public and fixed before the experiment. The encoding is asked to hide
at the seeds of Gs (`ReadsS.hidE`), the runs are asked to be near their simulators at the seeds of
Gs (`LawsS.Near`, `SimsS.Good`), and an admissible environment names seeds of Gs alone
(`EnvS.Adm`). At Gs = all seeds `ReadsS` is `HolographicProtocol.ReadsR` (`readsS_iff`). The letter is there for an
encoding that does not hide at a few seeds: whoever calls the theorem then stops at such a seed and
pays its probability. A set of seeds that hangs on the index or on the committer's randomness cannot
be seated in Gs. Gs IS A LETTER OF THE PROPERTY: at the empty set the property holds of anything,
with error 0. So whoever quotes the theorem quotes it AT ALL SEEDS: `Spec.whole_all_seeds`.
AN ENVIRONMENT THAT NAMES THE SEED CAN AIM. So "near at every seed of Gs, for EVERY value of the
committer's randomness" is a real premise: an honest side that behaves otherwise at some pairs
(randomness, seed) does not meet it, however few these pairs are. ("For every value of the
randomness" is the form of Hiop/RecWhole.lean's premises too; new is that the seed is aimed.)

The simulator of the theorem (`simWholeS`) is made from L, the simulators of runs Sm and a fixed
index i₀, and from nothing else. It keeps, in the place of each encoded index, an encoding of i₀
with fresh randomness, shows i₀'s own answer at the seed that was named, and answers each request
for a run by the simulator of that run at that number. It chooses no seed. That it does not hang on
the index of the real side is said by THE ORDER OF QUANTIFIERS in `HidesWhole` and in the statements
for given provers: Sm and i₀ are fixed before the index. `Spec.whole_laws` alone is NO statement on
hiding: there Sm stands beside the index, and it holds even of a real side that shows the index
outright, with simulators of runs that do the same.
The budget (`BoundsR.Fits`, Hiop/RecWhole.lean) is for each encoded index apart. The OOD sample
costs nothing in it, and only because the premise `ReadsS.hidE` is JOINT: it speaks of the answer
together with any b positions, so whatever pays for the answer (pads in the committer's randomness)
is inside that premise. The error (`BoundsR.err`):
(all tests) · zT + (all links) · zL + (all sessions) · shown · zO.
No term for the encoded indices and their OOD samples, and none for the seeds.

Main names:
  `EnvS`, `HostS`, `EnvS.run`, `HostS.view`, `EnvS.Adm`: the experiment.
  `LawsS`, `LawsS.host`; `ProversS`, `realLawsS`, `realHostS`: the real side.
  `SimulatorS`, `SimsS`, `simWholeS`: the simulator.
  `ReadsS`, `LawsS.Near`, `ProversS.Ext`, `SimsS.Good`, `ProversS.Hiding`: the premises.
  `ViewNear` (for one host, so for ONE index), `HidesWhole` (for given provers, all indices): the
    property.
  `Spec.whole_all_seeds`: THE FORM TO QUOTE: for given provers, at all seeds.
  `Spec.whole_laws`: for given laws of runs, on ONE index: its simulators of runs stand under the
    same quantifier as the index, so a caller could take others for each index. The statements for
    given provers have one family of simulators for all indices.
  `Spec.whole_provers`: for given provers, at the seeds of Gs.
  `Spec.whole_hiding`: from honest-verifier zero knowledge of each honest side.
  `freshAll`, `HostS.viewAll`, `Spec.whole_vector`: the case in which ALL encoded indices are made
    at the start, at a given list of seeds, before anything else is asked: the property gives the
    same bound for it. (A committer that makes all its encoded indices before any run is this case.)

Limits. (a) ON THE NAME: silent provers, which show nothing, meet every premise on provers with
error 0. So `HidesWhole` earns the name of honest-verifier zero knowledge of the whole object only
beside completeness OF THE SAME PROVERS, which this file does not state. (b) One seed is named for
each encoded index: of two OOD samples on one encoded index it says nothing. (c) A seed is a
function of what has been shown and of the environment's own coins, and it is named before the
randomness of its encoded index is drawn: that is the FORM of the experiment, no premise. In a
compiled argument the seed is a hash of a commitment to the encoded index, so it is learnt after
that randomness is drawn, by the prover and by a compiled simulator alike. That this is NEAR the
order of this file (after a passage to fresh oracle answers), and at what price; that the seed comes
from the commitment alone, so that no later run gives a second OOD sample; and that no seed hangs on
anything hidden otherwise than through the hashed commitment: all that is owed by whoever compiles.
This file has no term for that price. (d) There is no seat for a set of seeds that is set aside and
hangs on (index, committer's randomness): the premises on runs are at EVERY value of the randomness.
(e) WHERE THE PROPERTY SAYS NOTHING: at the empty set Gs; at an error of 1 or more; for a set of
indices with one element. (f) The limits of Hiop/RecWhole.lean stay: a run that is broken off is not
modelled; honest-verifier zero knowledge of a run is in this library's exact form. (g) This file
says nothing on whether any object or prover meets the premises. Hiop/Seeded/Members.lean and
Hiop/Seeded/Pad.lean have small members that do, and an object and two provers that do not.
Terms: lean/GLOSSARY.md.

-/
import Hiop.RecWhole

set_option autoImplicit false

noncomputable section

namespace Hiop.Seeded
open Prob Iop Compile.Lifetime Compile.BatchLife
open scoped ENNReal

variable {I X : Type}

/-! ## 1. Environments, hosts, the experiment -/

/-- An environment, after the first encoded index and its OOD sample, as a decision tree with
outputs in α. -/
inductive EnvS (L : HolographicProtocol I X) (α : Type) : Type 1
  | stop (a : α) : EnvS L α
  /-- a further encoded index, with its OOD sample at the seed s; go on by the sample -/
  | fresh (s : L.OutOfDomainSeed) (k : L.Rec → EnvS L α) : EnvS L α
  /-- the offline IOP on the encoded index e -/
  | test (e : ℕ) (k : Sess L.offline → EnvS L α) : EnvS L α
  /-- the link IOP on the encoded indices 0 and e -/
  | link (e : ℕ) (k : Sess L.link → EnvS L α) : EnvS L α
  /-- a session on the encoded index e: the slots J are shown and hold the instances xs; rest is
  what the other slots hold -/
  | session (e : ℕ) (J : Finset (Fin L.maxBatchSize)) (xs : J → X)
      (rest : {j : Fin L.maxBatchSize // j ∉ J} → Option X) (k : BSess L.onlineBatch J → EnvS L α) : EnvS L α
  /-- the symbol at position p of the encoded index e -/
  | read (e : ℕ) (p : Fin L.wordLength) (k : L.Symbol → EnvS L α) : EnvS L α
  | draw (β : Type) (d : PMF β) (k : β → EnvS L α) : EnvS L α

/-- Who answers the environment. `start` and `fresh` are handed the seed. -/
structure HostS (L : HolographicProtocol I X) where
  σ : Type
  start : L.OutOfDomainSeed → PMF (L.Rec × σ)
  fresh : σ → L.OutOfDomainSeed → PMF (L.Rec × σ)
  test : σ → ℕ → PMF (Sess L.offline × σ)
  link : σ → ℕ → PMF (Sess L.link × σ)
  session : σ → ℕ → (J : Finset (Fin L.maxBatchSize)) → (J → X) →
    ({j : Fin L.maxBatchSize // j ∉ J} → Option X) → PMF (BSess L.onlineBatch J × σ)
  read : σ → ℕ → Fin L.wordLength → PMF (L.Symbol × σ)

variable {L : HolographicProtocol I X} {α : Type}

def EnvS.run (H : HostS L) : EnvS L α → H.σ → PMF α
  | .stop a, _ => PMF.pure a
  | .fresh s k, st => (H.fresh st s).bind fun p => (k p.1).run H p.2
  | .test e k, st => (H.test st e).bind fun p => (k p.1).run H p.2
  | .link e k, st => (H.link st e).bind fun p => (k p.1).run H p.2
  | .session e J xs rest k, st => (H.session st e J xs rest).bind fun p => (k p.1).run H p.2
  | .read e p k, st => (H.read st e p).bind fun q => (k q.1).run H q.2
  | .draw _ d k, st => d.bind fun y => (k y).run H st

/-- The experiment: the environment names s₀; the first encoded index and its OOD sample at s₀; then
the environment, which has seen the sample. (An environment that draws coins before it names s₀:
`ViewNear.pre`, Hiop/Seeded/WholeProof.lean.) -/
def HostS.view (H : HostS L) (s₀ : L.OutOfDomainSeed) (E : L.Rec → EnvS L α) : PMF α :=
  (H.start s₀).bind fun p => (E p.1).run H p.2

/-! ## 2. The real side -/

/-- The OOD sample, the laws of what is shown of the three kinds of runs, and the symbols of an
encoded index, as functions of (committer's randomness, seed). The laws of runs are also handed the
number of the encoded index on which the run was asked for (for a link: of the further one). -/
structure LawsS (L : HolographicProtocol I X) where
  rc : L.EncodingRandomness × L.OutOfDomainSeed → L.Rec
  T : ℕ → L.EncodingRandomness × L.OutOfDomainSeed → PMF (Sess L.offline)
  Lk : ℕ → L.EncodingRandomness × L.OutOfDomainSeed → L.EncodingRandomness × L.OutOfDomainSeed → PMF (Sess L.link)
  B : ℕ → L.EncodingRandomness × L.OutOfDomainSeed → (J : Finset (Fin L.maxBatchSize)) → (J → X) →
    ({j : Fin L.maxBatchSize // j ∉ J} → Option X) → PMF (BSess L.onlineBatch J)
  y : L.EncodingRandomness × L.OutOfDomainSeed → Fin L.wordLength → L.Symbol

/-- The host with these laws. The state: the number of further encoded indices, and (committer's
randomness, seed) of each encoded index. The seed is the one that was handed in; the committer's
randomness is drawn uniformly after that. -/
def LawsS.host (W : LawsS L) : HostS L where
  σ := ℕ × (ℕ → L.EncodingRandomness × L.OutOfDomainSeed)
  start := fun s => (unif L.EncodingRandomness).map fun r => (W.rc (r, s), (0, fun _ => (r, s)))
  fresh := fun st s =>
    (unif L.EncodingRandomness).map fun r => (W.rc (r, s), (st.1 + 1, Function.update st.2 (st.1 + 1) (r, s)))
  test := fun st e => (W.T e (st.2 e)).map fun a => (a, st)
  link := fun st e => (W.Lk e (st.2 0) (st.2 e)).map fun a => (a, st)
  session := fun st e J xs rest => (W.B e (st.2 e) J xs rest).map fun a => (a, st)
  read := fun st e p => PMF.pure (W.y (st.2 e) p, st)

/-- The honest sides, as arguments: for each number of an encoded index one for each of the three
protocols. Their types are those of the object's fields honestOfflineProver, honestLinkProver, honestOnlineBatchProver. -/
structure ProversS (L : HolographicProtocol I X) where
  T : ℕ → Honest L.offline (I × L.EncodingRandomness × L.OutOfDomainSeed)
  Lk : ℕ → Honest L.link (I × (L.EncodingRandomness × L.OutOfDomainSeed) × (L.EncodingRandomness × L.OutOfDomainSeed))
  B : ℕ → BatchHonestProver L.onlineBatch (I × L.EncodingRandomness × L.OutOfDomainSeed)

/-- The object's own fields, at every number. -/
def ProversS.own (L : HolographicProtocol I X) : ProversS L := ⟨fun _ => L.honestOfflineProver, fun _ => L.honestLinkProver, fun _ => L.honestOnlineBatchProver⟩

/-- The laws of the real side on the index i with the provers P. -/
def realLawsS (L : HolographicProtocol I X) (P : ProversS L) (i : I) : LawsS L where
  rc := fun u => L.recOf i u.1 u.2
  T := fun e u => sess (P.T e) (i, u.1, u.2) (L.recOf i u.1 u.2)
  Lk := fun e u u' => sess (P.Lk e) (i, u, u') (L.recOf i u.1 u.2, L.recOf i u'.1 u'.2)
  B := fun e u J xs rest =>
    bsess (P.B e) (i, u.1, u.2)
      (vec J (fun j => (xs j, L.recOf i u.1 u.2))
        (fun j => (rest j).map fun x => (x, L.recOf i u.1 u.2))) J
  y := fun u p => L.encodeIndex i u.1 p

/-- The real side on the index i with the provers P. -/
def realHostS (L : HolographicProtocol I X) (P : ProversS L) (i : I) : HostS L := (realLawsS L P i).host

/-! ## 3. Simulators -/

/-- A simulator. No index; of a session: e, J and the instances of J. It is handed the seeds as the
real side is. -/
structure SimulatorS (L : HolographicProtocol I X) where
  σ : Type
  start : L.OutOfDomainSeed → PMF (L.Rec × σ)
  fresh : σ → L.OutOfDomainSeed → PMF (L.Rec × σ)
  test : σ → ℕ → PMF (Sess L.offline × σ)
  link : σ → ℕ → PMF (Sess L.link × σ)
  session : σ → ℕ → (J : Finset (Fin L.maxBatchSize)) → (J → X) → PMF (BSess L.onlineBatch J × σ)
  read : σ → ℕ → Fin L.wordLength → PMF (L.Symbol × σ)

def SimulatorS.host (S : SimulatorS L) : HostS L where
  σ := S.σ
  start := S.start
  fresh := S.fresh
  test := S.test
  link := S.link
  session := fun st e J xs _ => S.session st e J xs
  read := S.read

/-- For each number of an encoded index one simulator for each of the three protocols. -/
structure SimsS (L : HolographicProtocol I X) where
  T : ℕ → SimOf L.offline
  Lk : ℕ → SimOf L.link
  B : ℕ → BSimOf L.onlineBatch L.maxBatchSize

/-- The simulator of the theorem: an encoding of the fixed index i₀ in the place of each encoded
index, i₀'s own answer at the seed that was handed in, the simulators of runs. -/
def simWholeS (L : HolographicProtocol I X) (Sm : SimsS L) (i₀ : I) : SimulatorS L where
  σ := ℕ × (ℕ → L.EncodingRandomness × L.OutOfDomainSeed)
  start := fun s => (unif L.EncodingRandomness).map fun r => (L.recOf i₀ r s, (0, fun _ => (r, s)))
  fresh := fun st s =>
    (unif L.EncodingRandomness).map fun r =>
      (L.recOf i₀ r s, (st.1 + 1, Function.update st.2 (st.1 + 1) (r, s)))
  test := fun st e =>
    (simSess L.offline (Sm.T e) (L.recOf i₀ (st.2 e).1 (st.2 e).2) (L.encodeIndex i₀ (st.2 e).1)).map
      fun a => (a, st)
  link := fun st e =>
    (simSess L.link (Sm.Lk e) (L.recOf i₀ (st.2 0).1 (st.2 0).2, L.recOf i₀ (st.2 e).1 (st.2 e).2)
        (L.encodeIndex i₀ (st.2 0).1, L.encodeIndex i₀ (st.2 e).1)).map fun a => (a, st)
  session := fun st e J xs =>
    (simBsess L.onlineBatch (Sm.B e) J (fun j => (xs j, L.recOf i₀ (st.2 e).1 (st.2 e).2))
        (L.encodeIndex i₀ (st.2 e).1)).map fun a => (a, st)
  read := fun st e p => PMF.pure (L.encodeIndex i₀ (st.2 e).1 p, st)

/-! ## 4. The bounds -/

/-- The environment keeps the bounds (`BoundsR`, `UsedR`: Hiop/RecWhole.lean) and names seeds of Gs
alone, on every path, when c further encoded indices exist and u has been asked so far. ok: the
instance is in the relation with the index. -/
def EnvS.Adm (B : BoundsR) (Gs : L.OutOfDomainSeed → Prop) (ok : X → Prop) : EnvS L α → ℕ → UsedR → Prop
  | .stop _, _, _ => True
  | .fresh s k, c, u => Gs s ∧ c < B.nenc ∧ ∀ a, (k a).Adm B Gs ok (c + 1) u
  | .test e k, c, u =>
    e ≤ c ∧ u.tests e < B.tests e ∧ ∀ a, (k a).Adm B Gs ok c { u with tests := bump u.tests e }
  | .link e k, c, u =>
    1 ≤ e ∧ e ≤ c ∧ u.links e < B.links e ∧
      ∀ a, (k a).Adm B Gs ok c { u with links := bump u.links e }
  | .session e J xs rest k, c, u =>
    e ≤ c ∧ u.sess e < B.sess e ∧ J.card ≤ B.shown ∧ (∀ j, ok (xs j)) ∧
    (∀ j x, rest j = some x → ok x) ∧ ∀ a, (k a).Adm B Gs ok c { u with sess := bump u.sess e }
  | .read e _ k, c, u =>
    e ≤ c ∧ u.reads e < B.reads e ∧ ∀ y, (k y).Adm B Gs ok c { u with reads := bump u.reads e }
  | .draw _ _ k, c, u => ∀ y, (k y).Adm B Gs ok c u

/-! ## 5. The premises -/

/-- `HolographicProtocol.ReadsR` (Hiop/RecInterface.lean), with its clause on hiding asked at the seeds of Gs alone:
the numbers of positions that the three verifiers read, and: at every seed of Gs the law of (honest
answer, the encoded index at any b positions) does not depend on the index. -/
structure ReadsS (L : HolographicProtocol I X) (Gs : L.OutOfDomainSeed → Prop) (b qT qpar qch qon : ℕ) : Prop where
  cntT  : ∀ x ρ, (L.offline.extReads x ρ).card ≤ qT
  cntLp : ∀ x ρ, ((L.link.extReads x ρ).filter (fun p => p.isLeft)).card ≤ qpar
  cntLc : ∀ x ρ, ((L.link.extReads x ρ).filter (fun p => p.isRight)).card ≤ qch
  cntB  : L.onlineBatch.ReadsAtMost L.maxBatchSize qon
  hidE  : ∀ (S : Finset (Fin L.wordLength)), S.card ≤ b → ∀ (s : L.OutOfDomainSeed), Gs s →
    ∀ i i', (unif L.EncodingRandomness).map (fun r => (L.honestOutOfDomainAnswer i r s, fun p : S => L.encodeIndex i r p)) =
      (unif L.EncodingRandomness).map (fun r => (L.honestOutOfDomainAnswer i' r s, fun p : S => L.encodeIndex i' r p))

/-- At all seeds it is the interface's own property. -/
theorem readsS_iff {b qT qpar qch qon : ℕ} :
    ReadsS L (fun _ => True) b qT qpar qch qon ↔ L.ReadsR b qT qpar qch qon :=
  ⟨fun h => ⟨h.cntT, h.cntLp, h.cntLc, h.cntB, fun S hS s i i' => h.hidE S hS s trivial i i'⟩,
    fun h => ⟨h.cntT, h.cntLp, h.cntLc, h.cntB, fun S hS s _ i i' => h.hidE S hS s i i'⟩⟩

/-- What the theorem needs of the real side: its OOD samples and symbols are those of the encodings
of i, and each of its runs is near the simulated run on the true encodings and samples, at every
number, for EVERY value of the committer's randomness and every seed of Gs (the field `B`: under
`(∀ j, ok (xs j))` and `(∀ j x, rest j = some x → ok x)`). -/
structure LawsS.Near (W : LawsS L) (Sm : SimsS L) (Gs : L.OutOfDomainSeed → Prop) (i : I) (ok : X → Prop)
    (zT zL zO : ℝ≥0∞) : Prop where
  rc : ∀ u, W.rc u = L.recOf i u.1 u.2
  y  : ∀ u p, W.y u p = L.encodeIndex i u.1 p
  T  : ∀ e u, Gs u.2 →
    tv (W.T e u) (simSess L.offline (Sm.T e) (L.recOf i u.1 u.2) (L.encodeIndex i u.1)) ≤ zT
  Lk : ∀ e u u', Gs u.2 → Gs u'.2 →
    tv (W.Lk e u u')
        (simSess L.link (Sm.Lk e) (L.recOf i u.1 u.2, L.recOf i u'.1 u'.2)
          (L.encodeIndex i u.1, L.encodeIndex i u'.1)) ≤ zL
  B  : ∀ e u J xs rest, Gs u.2 → (∀ j, ok (xs j)) → (∀ j x, rest j = some x → ok x) →
    tv (W.B e u J xs rest)
        (simBsess L.onlineBatch (Sm.B e) J (fun j => (xs j, L.recOf i u.1 u.2)) (L.encodeIndex i u.1)) ≤
      J.card * zO

/-- The provers speak of the encodings: the external strings of each honest side are the encoded
index(es) of its private input. (The three clauses extT, extL, extB of `HolographicProtocol.WiredR`, at the
provers.) -/
structure ProversS.Ext (P : ProversS L) : Prop where
  extT : ∀ e i r s, (P.T e).ext (i, r, s) = L.encodeIndex i r
  extL : ∀ e i r s r' s', (P.Lk e).ext (i, (r, s), (r', s')) = (L.encodeIndex i r, L.encodeIndex i r')
  extB : ∀ e i r s, (P.B e).ext (i, r, s) = L.encodeIndex i r

/-- The simulators of runs are good for the provers P, at every number, on honest OOD samples
(`validT`, `validL`, `validB Ryes`, Hiop/RecInterface.lean) at seeds of Gs. -/
structure SimsS.Good (Sm : SimsS L) (P : ProversS L) (Gs : L.OutOfDomainSeed → Prop) (Ryes : I → X → Prop)
    (zT zL zO : ℝ≥0∞) : Prop where
  goodT : ∀ e w x, L.validT w x → Gs w.2.2 →
    prRho {ρ | (P.T e).output w x ρ ≠ Sm.T e x ρ (L.offline.extAns x ρ ((P.T e).ext w))} ≤ zT
  goodL : ∀ e w x, L.validL w x → Gs w.2.1.2 → Gs w.2.2.2 →
    prRho {ρ | (P.Lk e).output w x ρ ≠ Sm.Lk e x ρ (L.link.extAns x ρ ((P.Lk e).ext w))} ≤ zL
  goodB : ∀ e (w : I × L.EncodingRandomness × L.OutOfDomainSeed) (x : Fin L.maxBatchSize → Option (X × L.Rec)), Gs w.2.2 →
    (∀ j xj, x j = some xj → L.validB Ryes w xj) →
    ∀ (J : Finset (Fin L.maxBatchSize)) (xs : J → X × L.Rec), (∀ j : J, x j = some (xs j)) →
      prBRho {ρ | (P.B e).output w x ρ J ≠
            Sm.B e J xs (fun j => ρ.slot j.1)
              (L.onlineBatch.extAnsJ J xs (fun j => ρ.slot j.1) ((P.B e).ext w))} ≤ J.card * zO

/-- Each honest side is honest-verifier zero-knowledge (`Honest.HVZK`, Iop/InteractiveOracleProof.lean;
`BatchHonestProver.HVZK`, Iop/Batch.lean) on honest OOD samples at seeds of Gs. (`HolographicProtocol.HidingR`, at the
provers.) -/
structure ProversS.Hiding (P : ProversS L) (Gs : L.OutOfDomainSeed → Prop) (Ryes : I → X → Prop)
    (zT zL zO : ℝ≥0∞) : Prop where
  hidT : ∀ e, (P.T e).HVZK (fun w x => L.validT w x ∧ Gs w.2.2) zT
  hidL : ∀ e, (P.Lk e).HVZK (fun w x => L.validL w x ∧ Gs w.2.1.2 ∧ Gs w.2.2.2) zL
  hidB : ∀ e, (P.B e).HVZK L.maxBatchSize (fun w x => L.validB Ryes w x ∧ Gs w.2.2) zO

/-! ## 6. The property and the statements -/

/-- What an environment within the bounds B, which names the seeds (in Gs), sees of the host H is
within z of what it sees of the simulator S. One host: on the real side that is ONE index. -/
def ViewNear (H : HostS L) (Gs : L.OutOfDomainSeed → Prop) (ok : X → Prop) (B : BoundsR) (S : SimulatorS L)
    (z : ℝ≥0∞) : Prop :=
  ∀ (α : Type) (s₀ : L.OutOfDomainSeed) (E : L.Rec → EnvS L α), Gs s₀ →
    (∀ a, (E a).Adm B Gs ok 0 UsedR.zero) → tv (H.view s₀ E) (S.host.view s₀ E) ≤ z

/-- What an environment within the bounds B, which names the seeds (in Gs), sees of the whole object
with the provers P on any index is within z of what it sees of the simulator S.
(`EnvS.Adm B Gs (Ryes i)`: all instances of a batch, the hidden ones too, in the relation with the
index.) On the name of this property see the head of this file, Limits (a). -/
def HidesWhole (L : HolographicProtocol I X) (P : ProversS L) (Gs : L.OutOfDomainSeed → Prop) (Ryes : I → X → Prop)
    (B : BoundsR) (S : SimulatorS L) (z : ℝ≥0∞) : Prop :=
  ∀ i : I, ViewNear (realHostS L P i) Gs (Ryes i) B S z

/-- Further encoded indices at the seeds of a list, one after the other; then K, with their OOD
samples in their order. -/
def freshAll : List L.OutOfDomainSeed → (List L.Rec → EnvS L α) → EnvS L α
  | [], K => K []
  | s :: ss, K => .fresh s fun a => freshAll ss fun as => K (a :: as)

/-- The experiment in which all encoded indices are made at the start: the first one at the seed s₀,
the further ones at the seeds ss; then K, which has seen all their OOD samples. -/
def HostS.viewAll (H : HostS L) (s₀ : L.OutOfDomainSeed) (ss : List L.OutOfDomainSeed)
    (K : L.Rec → List L.Rec → EnvS L α) : PMF α :=
  H.view s₀ fun a => freshAll ss (K a)

namespace Spec

/-- For given laws of runs: any real side that is near the simulated runs. It speaks of ONE index i:
the simulators of runs Sm stand under the same quantifier, so nothing here says that one Sm serves
all indices. -/
def whole_laws : Prop :=
  ∀ (I X : Type) (L : HolographicProtocol I X) (Gs : L.OutOfDomainSeed → Prop) (ok : X → Prop) (b qT qpar qch qon : ℕ)
      (zT zL zO : ℝ≥0∞),
    ReadsS L Gs b qT qpar qch qon →
    ∀ (Sm : SimsS L) (W : LawsS L) (i : I), W.Near Sm Gs i ok zT zL zO →
      ∀ B : BoundsR, B.Fits b qT qpar qch qon →
        ∀ i₀ : I, ViewNear W.host Gs ok B (simWholeS L Sm i₀) (B.err zT zL zO)

/-- For given provers, at the seeds of Gs: from good simulators of the runs, simulator named. -/
def whole_provers : Prop :=
  ∀ (I X : Type) (L : HolographicProtocol I X) (Gs : L.OutOfDomainSeed → Prop) (Ryes : I → X → Prop)
      (b qT qpar qch qon : ℕ) (zT zL zO : ℝ≥0∞),
    ReadsS L Gs b qT qpar qch qon →
    ∀ P : ProversS L, P.Ext →
      ∀ Sm : SimsS L, Sm.Good P Gs Ryes zT zL zO →
        ∀ B : BoundsR, B.Fits b qT qpar qch qon →
          ∀ i₀ : I, HidesWhole L P Gs Ryes B (simWholeS L Sm i₀) (B.err zT zL zO)

/-- The same from honest-verifier zero knowledge of each honest side: one family of run simulators
for all bounds and all i₀. -/
def whole_hiding : Prop :=
  ∀ (I X : Type) (L : HolographicProtocol I X) (Gs : L.OutOfDomainSeed → Prop) (Ryes : I → X → Prop)
      (b qT qpar qch qon : ℕ) (zT zL zO : ℝ≥0∞),
    ReadsS L Gs b qT qpar qch qon →
    ∀ P : ProversS L, P.Ext → P.Hiding Gs Ryes zT zL zO →
      ∃ Sm : SimsS L, ∀ B : BoundsR, B.Fits b qT qpar qch qon →
        ∀ i₀ : I, HidesWhole L P Gs Ryes B (simWholeS L Sm i₀) (B.err zT zL zO)

/-- THE FORM TO QUOTE: for given provers, AT ALL SEEDS. The premise on the encoding is the
interface's own `HolographicProtocol.ReadsR`; the environment may name any seed. "All seeds" is: all values of the
object's own type `L.OutOfDomainSeed`. That type may itself shut values out (a factor that must not be 0, say):
of such values nothing is said, since no seed of the object is one. For an encoding that fails to
hide at one value of that type the premise fails, and this form says nothing: `whole_provers` at a
smaller Gs is for that case. -/
def whole_all_seeds : Prop :=
  ∀ (I X : Type) (L : HolographicProtocol I X) (Ryes : I → X → Prop) (b qT qpar qch qon : ℕ) (zT zL zO : ℝ≥0∞),
    L.ReadsR b qT qpar qch qon →
    ∀ P : ProversS L, P.Ext →
      ∀ Sm : SimsS L, Sm.Good P (fun _ => True) Ryes zT zL zO →
        ∀ B : BoundsR, B.Fits b qT qpar qch qon →
          ∀ i₀ : I, HidesWhole L P (fun _ => True) Ryes B (simWholeS L Sm i₀) (B.err zT zL zO)

/-- All encoded indices made at the start, at a given list of seeds: the same bound. K goes on when
`ss.length` further encoded indices exist and nothing has been asked of them. -/
def whole_vector : Prop :=
  ∀ (I X : Type) (L : HolographicProtocol I X) (H : HostS L) (Gs : L.OutOfDomainSeed → Prop) (ok : X → Prop) (B : BoundsR)
      (S : SimulatorS L) (z : ℝ≥0∞),
    ViewNear H Gs ok B S z →
    ∀ (α : Type) (s₀ : L.OutOfDomainSeed) (ss : List L.OutOfDomainSeed) (K : L.Rec → List L.Rec → EnvS L α),
      Gs s₀ → (∀ s ∈ ss, Gs s) → ss.length ≤ B.nenc →
      (∀ a as, (K a as).Adm B Gs ok ss.length UsedR.zero) →
        tv (H.viewAll s₀ ss K) (S.host.viewAll s₀ ss K) ≤ z

end Spec
end Hiop.Seeded
