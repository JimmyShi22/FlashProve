-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/FrontBinds.lean: from a hypothesis on openings of the key, and smaller ones, to binding
of the commitment, for the argument system whose verifier is the front verifier (`systemPortC p`,
Johnson/Top/OnFilesPortC.lean): in the opening form (the second clause of `SoundAndBinding`,
VerifiableInference/Statements.lean), `SoundAndBinding` itself, and no two openings ("nobody opens
one commitment to two different weights"). General in the input r: no written value stands here.

Why. The front theorem (`front_sound_plain`, Johnson/TypedOracleCompiler/Top/FrontPlain.lean) ends in soundness
alone. Binding comes by a row of general
lemmas from "whoever opens a key opens it to the index that the extractor gives"
(ZKCP/WithOpenings.lean, Compile/DigestKeyWithOpenings.lean,
VerifiableInference/OfArgumentBinds.lean). Here that row is called at the front's scheme. What is
left is `HoleArmsC.opens`, and smaller hypotheses: two on the committer (hcode, hS), one on the code
(hinj), one that names the error (hβ). None is proved of any input here. THAT HYPOTHESIS IS ITSELF A
STATEMENT OF OPENING-FORM BINDING, AT THE KEY: the game of `BindsWith` with the key in the place of
its hash. What is proved here is the step behind that one hash, and that the verifier plays no part.

`BindsWith` and `NoTwoOpenings` are defined in VerifiableInference/MoreStatements.lean. Definitions,
statements and proofs.

Main definitions.
  `HoleArmsC.opens b β`: index binding, at the bound β, of the scheme of the three checks with
    openings in the place of proofs (`ZKCP.Arg.withOpenings`: an instance is an index with a number;
    the verifier runs the committer again and compares keys), for the index part of the inner
    extractor b.E.
  `epsOpens β tS`: the bound behind the hash of the key's code, where tS bounds the queries of the
    scheme's committer: at tC and tO it is β tC (tO + tS) plus the square of tC + tO + tS + 2 over
    2^256.
Main theorems.
  `BindsWith.withVerifier`, `NoTwoOpenings.withVerifier`: another verifier, honest prover and type
    of proofs change nothing in the two notions.
  `Rec.bindsWith_systemE`: `bindsWith_ofArgument` at `Rec.tokenArgumentSystem` (Johnson/Top/FrontEnc.lean).
  `Rec.opens_digestSchemeE`: `HasIndexBindingWith.withOpenings_digestKey`, then
    `opensToExtracted_of_binding`. Hypotheses: h: index binding of the scheme with openings; hinj:
    no two keys have one code; hcode: every key that the committer can put out has a code; hS: tS.
  `front_bindsWith_of_opens`: UNDER `HoleArmsC.opens b β`, hinj, hcode, hS and hβ: `BindsWith
    (systemPortC p)` at the extractor of `verify_sound_arms_C_plain`
    (Johnson/TypedOracleCompiler/Top/OnFilesArmsCPlain.lean). No bound of a check is among its hypotheses.
  `front_soundAndBinding_of_opens`: UNDER `HoleArmsC.opens b β`, hcode, hS, hβ AND all named
    hypotheses of the front theorem (`FrontFieldsPlain`, of which none is proved there):
    `SoundAndBinding (systemPortC p)`, at the larger of the two errors.
  `front_noTwoOpenings_of_opens`: UNDER the hypotheses of `front_bindsWith_of_opens`: `NoTwoOpenings
    (systemPortC p)` at twice the second error.
Controls: where the notions must fail.
  `BindsWith.one_le_of_blind`, `NoTwoOpenings.one_le_of_blind`: a committer that is one and the same
    algorithm at two different weights, under some randomness, forces the error to be at least 1 at
    that committer's number of queries, whatever the extractor.
  `BindsWith.one_le_of_never`: so do weights that the extractor never gives, whatever the committer
    does at them. A neighbour: `BindsWith.atRandomness` (VerifiableInference/BindsAtRandomness.lean)
    bounds by ε the probability that the extractor does not give back honestly committed weights, at
    given randomness; this control follows from it too.
  Their tools: `DeterministicAlgorithm.logUnder`, `run_withQueryLog_toRandomized`: a deterministic
    algorithm's query log under a hash function; `DeterministicAlgorithm.picking` with
    `evaluate_picking`, `logUnder_picking`, `queryBound_picking`: the same algorithm, handing on a
    function of its result and of its own log, with the same queries.

NOTHING HERE SHOWS OPENING-FORM BINDING, `SoundAndBinding`, NO TWO OPENINGS OR WHATEVER ELSE NAMES A
COMMITTER, OF ANY WRITTEN SYSTEM. AT THE WRITTEN INPUT OF THE FRONT THEOREM AT THE WRITTEN VERIFIER
(an input that is not in this library) THE THREE ENDS SAY NOTHING, for two reasons.
(1) Its committer is a placeholder that ignores the index. There the first control strikes
`BindsWith`, `SoundAndBinding` and `NoTwoOpenings` alike, whatever the extractor. Whoever spends the
statements of this file brings another committer, so another input.
(2) An argument; no theorem. The indices of that input are all matrices, and its decoder gives
matrices in range alone. Take a b whose E decodes by it (the field `extractor` of `CoreArmsC`,
Johnson/Top/OnFilesArmsC.lean: `front_soundAndBinding_of_opens` asks it through `FrontFieldsPlain`,
the two others do not), and let some matrix be out of range. Then by the second control every error
ε' that `front_bindsWith_of_opens` yields at that b is at least 1 at the number of queries of the
system's committer at that matrix. So there, under hinj, hcode and hS, `HoleArmsC.opens b β` cannot
hold at a β for which `epsOpens β tS` stays below 1. `front_bindsWith_of_opens` and
`front_noTwoOpenings_of_opens` leave b free: at another extractor this does not strike them.
`NoTwoOpenings` names no extractor: the second control does not strike it, only this way to it.

Limits.
* `HoleArmsC.opens b β` IS THE WHOLE WEIGHT, and it is a hypothesis. So are hinj, hcode, hS and hβ;
  hcode and hS speak of r.commit. `front_soundAndBinding_of_opens` takes every field of
  `FrontFieldsPlain` besides, the bounds of the three checks among them.
* At a committer that is one algorithm at two different indices, `BindsWith`, `SoundAndBinding` and
  `NoTwoOpenings` hold at no error below 1 at its number of queries (the first control): so there,
  under the other hypotheses, `opens` cannot hold at a small β.
* By the second control `BindsWith` and `SoundAndBinding` at an extractor hold at no error below 1
  wherever r.I holds an index that this extractor never gives.
* tS HAS TWO SENSES. In hS it bounds the scheme's committer, before the hash of the key's code. In
  the controls it bounds the system's committer, which asks up to one query more.
* The adversary of `BindsWith.one_le_of_blind` computes the extractor's answer from its own
  commitment and log. That costs no query, and the game bounds queries alone.
* p IS FREE in `front_bindsWith_of_opens` and `front_noTwoOpenings_of_opens`: they hold for every
  front verifier, one that accepts everything among them. They say nothing on proofs.
* β, ε and ε' are letters: nothing asks that they are below 1. At the infinite error every
  hypothesis on errors is met for nothing, and the ends say nothing.
* b.E is a letter: the commitment binds to whatever b.E gives.
* Opening-form binding is to the index. Nothing on two openings with the same index and other
  randomness. One opening in a run. The extractor reads the commitment and its maker's queries.
* That r.commit is a committer that any program runs is not said.
* The hash function is drawn at random and asked as an oracle by all parties, as in
  VerifiableInference/Statements.lean. No statement names a fixed hash function.
For proofs only; no program imports this file.


-/
import Johnson.TypedOracleCompiler.Top.FrontPlain
import VerifiableInference.Binds
import VerifiableInference.NoTwoOpenings
import VerifiableInference.OfArgumentBinds
import Compile.DigestKeyWithOpenings
import VerifiableInference.NotComplete

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal

/-! ## Binding reads no verifier; three controls -/

namespace VerifiableInference
open RandomizedAlgorithm

/-- Binding reads nothing of the verifier, the honest prover or the type of proofs. -/
theorem BindsWith.withVerifier (system : ArgumentSystem) (Proof' : Type)
    (prove' : system.Weights → system.CommitmentRandomness → List Token → List Token →
      RandomizedAlgorithm Proof')
    (verify' : Commitment → List Token → List Token → Proof' → DeterministicAlgorithm Bool)
    (extractor : Commitment → QueryLog → Option system.Weights) (ε : ℕ → ℝ≥0∞) :
    BindsWith (system.withVerifier Proof' prove' verify') extractor ε ↔
      BindsWith system extractor ε :=
  Iff.rfl

/-- Nor does "nobody opens one commitment to two different weights". -/
theorem NoTwoOpenings.withVerifier (system : ArgumentSystem) (Proof' : Type)
    (prove' : system.Weights → system.CommitmentRandomness → List Token → List Token →
      RandomizedAlgorithm Proof')
    (verify' : Commitment → List Token → List Token → Proof' → DeterministicAlgorithm Bool)
    (ε : ℕ → ℝ≥0∞) :
    NoTwoOpenings (system.withVerifier Proof' prove' verify') ε ↔ NoTwoOpenings system ε :=
  Iff.rfl

/-! ### tools for the controls: a deterministic algorithm that hands on a function of its own log -/

/-- The query log of a deterministic algorithm under a hash function. -/
def DeterministicAlgorithm.logUnder {α : Type} (hash : Hash) : DeterministicAlgorithm α → QueryLog
  | .done _ => []
  | .query input next => (input, hash input) :: (next (hash input)).logUnder hash

/-- Under a hash function a deterministic algorithm, run with its query log, gives its value and
that log. -/
theorem run_withQueryLog_toRandomized {α : Type} (hash : Hash) :
    ∀ D : DeterministicAlgorithm α,
      D.toRandomized.withQueryLog.run hash = PMF.pure (D.evaluate hash, D.logUnder hash)
  | .done _ => rfl
  | .query input next => by
      show ((next (hash input)).toRandomized.withQueryLog.bind fun rest =>
        RandomizedAlgorithm.done (rest.1, (input, hash input) :: rest.2)).run hash = _
      rw [run_bind, run_withQueryLog_toRandomized hash (next (hash input)), PMF.pure_bind, run_done]
      rfl

/-- The same algorithm, handing on beside its result what pick makes of the result and of the
queries made so far: acc holds the earlier ones, the last first. -/
def DeterministicAlgorithm.picking {α σ : Type} (pick : α → QueryLog → σ) :
    DeterministicAlgorithm α → QueryLog → DeterministicAlgorithm (α × σ)
  | .done result, acc => .done (result, pick result acc.reverse)
  | .query input next, acc => .query input fun answer => (next answer).picking pick
      ((input, answer) :: acc)

/-- Its value: the algorithm's own, and pick at that value and at the earlier queries followed by
the algorithm's log. -/
theorem DeterministicAlgorithm.evaluate_picking {α σ : Type} (pick : α → QueryLog → σ)
    (hash : Hash) : ∀ (D : DeterministicAlgorithm α) (acc : QueryLog),
      (D.picking pick acc).evaluate hash =
        (D.evaluate hash, pick (D.evaluate hash) (acc.reverse ++ D.logUnder hash))
  | .done result, acc => by
      show (result, pick result acc.reverse) = (result, pick result (acc.reverse ++ []))
      rw [List.append_nil]
  | .query input next, acc => by
      show ((next (hash input)).picking pick ((input, hash input) :: acc)).evaluate hash =
        ((next (hash input)).evaluate hash, pick ((next (hash input)).evaluate hash)
          (acc.reverse ++ (input, hash input) :: (next (hash input)).logUnder hash))
      rw [evaluate_picking pick hash (next (hash input)), List.reverse_cons, List.append_assoc]
      rfl

/-- It asks what the algorithm asks. -/
theorem DeterministicAlgorithm.logUnder_picking {α σ : Type} (pick : α → QueryLog → σ)
    (hash : Hash) : ∀ (D : DeterministicAlgorithm α) (acc : QueryLog),
      (D.picking pick acc).logUnder hash = D.logUnder hash
  | .done _, _ => rfl
  | .query input next, acc => by
      show (input, hash input) ::
          ((next (hash input)).picking pick ((input, hash input) :: acc)).logUnder hash =
        (input, hash input) :: (next (hash input)).logUnder hash
      rw [logUnder_picking pick hash (next (hash input))]

/-- It keeps every bound on the number of queries. -/
theorem DeterministicAlgorithm.queryBound_picking {α σ : Type} (pick : α → QueryLog → σ) :
    ∀ (D : DeterministicAlgorithm α) (acc : QueryLog) (queries : ℕ),
      D.toRandomized.QueryBound queries → (D.picking pick acc).toRandomized.QueryBound queries
  | .done _, _, _, _ => trivial
  | .query _ _, _, 0, h => h.elim
  | .query input next, acc, queries + 1, h => fun answer =>
      queryBound_picking pick (next answer) ((input, answer) :: acc) queries (h answer)

/-- A control. A committer that is one and the same algorithm at two different weights, under the
randomness ρ and with at most tS queries: then binding holds at no error below 1 at tS, whatever the
extractor. The adversary runs that committer, computes the extractor's answer from its own
commitment and log, which costs no query, and opens to whichever of the two the extractor does not
give. -/
theorem BindsWith.one_le_of_blind {system : ArgumentSystem}
    {extractor : Commitment → QueryLog → Option system.Weights} {ε : ℕ → ℝ≥0∞}
    (h : BindsWith system extractor ε) {w w' : system.Weights} (hne : w ≠ w')
    (ρ : system.CommitmentRandomness) (hc : system.commit w ρ = system.commit w' ρ) {tS : ℕ}
    (hS : (system.commit w ρ).toRandomized.QueryBound tS) : 1 ≤ ε tS := by
  classical
  let pick : Commitment → QueryLog → system.Weights :=
    fun c l => if extractor c l = some w then w' else w
  have key := h tS 0 system.Weights ((system.commit w ρ).picking pick []).toRandomized
    (DeterministicAlgorithm.queryBound_picking pick _ [] tS hS)
    (fun state => RandomizedAlgorithm.done (state, ρ)) fun _ => trivial
  refine le_trans (le_of_eq (Eq.symm ?_)) key
  refine Prob_eq_one _ _ fun hash => ?_
  show ZKCP.prob ((((system.commit w ρ).picking pick []).toRandomized.withQueryLog.bind fun c =>
      (RandomizedAlgorithm.done (c.1.2, ρ)).bind fun y =>
        (system.commit y.1 y.2).toRandomized.bind fun recomputed =>
          RandomizedAlgorithm.done (extractor c.1.1 c.2, c.1.1, y.1, recomputed)).run hash) _ = 1
  rw [run_bind, run_withQueryLog_toRandomized, PMF.pure_bind,
    DeterministicAlgorithm.evaluate_picking, DeterministicAlgorithm.logUnder_picking, run_bind,
    run_done, PMF.pure_bind, run_bind, DeterministicAlgorithm.run_toRandomized, PMF.pure_bind,
    run_done, ZKCP.prob_pure]
  refine if_pos ⟨?_, ?_⟩
  · show (system.commit (pick _ _) ρ).evaluate hash = (system.commit w ρ).evaluate hash
    by_cases e : extractor ((system.commit w ρ).evaluate hash)
        ([].reverse ++ (system.commit w ρ).logUnder hash) = some w
    · rw [show pick _ _ = w' from if_pos e, hc]
    · rw [show pick _ _ = w from if_neg e]
  · show extractor ((system.commit w ρ).evaluate hash) ((system.commit w ρ).logUnder hash) ≠
      some (pick _ _)
    by_cases e : extractor ((system.commit w ρ).evaluate hash)
        ([].reverse ++ (system.commit w ρ).logUnder hash) = some w
    · rw [show pick _ _ = w' from if_pos e]
      intro e'
      exact hne (Option.some.inj (e.symm.trans e'))
    · rw [show pick _ _ = w from if_neg e]
      exact e

/-- A control. Weights w that the extractor never gives: then binding holds at no error below 1 at
the number of queries of the committer at w, whatever that committer does. The adversary commits
and opens honestly. -/
theorem BindsWith.one_le_of_never {system : ArgumentSystem}
    {extractor : Commitment → QueryLog → Option system.Weights} {ε : ℕ → ℝ≥0∞}
    (h : BindsWith system extractor ε) (w : system.Weights)
    (hn : ∀ c l, extractor c l ≠ some w) (ρ : system.CommitmentRandomness) {tS : ℕ}
    (hS : (system.commit w ρ).toRandomized.QueryBound tS) : 1 ≤ ε tS := by
  have key := h tS 0 Unit ((system.commit w ρ).toRandomized.bind fun c =>
      RandomizedAlgorithm.done (c, ())) (queryBound_map _ _ tS hS)
    (fun _ => RandomizedAlgorithm.done (w, ρ)) fun _ => trivial
  refine le_trans (le_of_eq (Eq.symm ?_)) key
  refine Prob_eq_one _ _ fun hash => ?_
  show ZKCP.prob ((((system.commit w ρ).toRandomized.bind fun c =>
      RandomizedAlgorithm.done (c, ())).withQueryLog.bind fun c =>
      (RandomizedAlgorithm.done (w, ρ)).bind fun y =>
        (system.commit y.1 y.2).toRandomized.bind fun recomputed =>
          RandomizedAlgorithm.done (extractor c.1.1 c.2, c.1.1, y.1, recomputed)).run hash) _ = 1
  rw [run_bind, run_withQueryLog_map, run_withQueryLog_toRandomized]
  simp only [PMF.pure_bind, run_bind, run_done, DeterministicAlgorithm.run_toRandomized,
    ZKCP.prob_pure]
  exact if_pos ⟨rfl, hn _ _⟩

/-- The first control for "nobody opens one commitment to two different weights": the committer is
one and the same algorithm at both. -/
theorem NoTwoOpenings.one_le_of_blind {system : ArgumentSystem} {ε : ℕ → ℝ≥0∞}
    (h : NoTwoOpenings system ε) {w w' : system.Weights} (hne : w ≠ w')
    (ρ : system.CommitmentRandomness) (hc : system.commit w ρ = system.commit w' ρ) {tS : ℕ}
    (hS : (system.commit w ρ).toRandomized.QueryBound tS) : 1 ≤ ε tS := by
  have key := h tS ((system.commit w ρ).toRandomized.bind fun c =>
      RandomizedAlgorithm.done (c, (w, ρ), (w', ρ))) (queryBound_map _ _ tS hS)
  refine le_trans (le_of_eq (Eq.symm ?_)) key
  refine Prob_eq_one _ _ fun hash => ?_
  show ZKCP.prob ((((system.commit w ρ).toRandomized.bind fun c =>
      RandomizedAlgorithm.done (c, (w, ρ), (w', ρ))).bind fun a =>
      (system.commit a.2.1.1 a.2.1.2).toRandomized.bind fun r₁ =>
        (system.commit a.2.2.1 a.2.2.2).toRandomized.bind fun r₂ =>
          RandomizedAlgorithm.done (a.1, a.2.1.1, a.2.2.1, r₁, r₂)).run hash) _ = 1
  simp only [run_bind, run_done, PMF.pure_bind, DeterministicAlgorithm.run_toRandomized,
    ZKCP.prob_pure]
  exact if_pos ⟨rfl, by rw [hc], hne⟩

end VerifiableInference

/-! ## From openings of the key to binding of the commitment -/

namespace VerifiableInference.Rec
open Rom ZKCP

variable {I X IVK ISK Pf : Type} (G : ZKCP.Gen.Arg (rom 256) I X Unit IVK ISK Pf)
  (E : ZKCP.Gen.Extractor (rom 256) I X Unit IVK Pf) (enc : IVK → Option ZKCP.Str) (bound : ℕ)
  (build : List Token × List Token → List Token → Option X) (π₀ : IVK × Pf)
  (nextToken : I → List Token → Option Token)

/-- If whoever opens a digest of the scheme behind the hash of its key's code opens it to the index
that the extractor gives, the commitment of `tokenArgumentSystem` binds in the opening form to that index. -/
theorem bindsWith_systemE {β : ℕ → ℕ → ℝ≥0∞} {ε : ℕ → ℝ≥0∞}
    (h : ZKCP.OpensToExtracted (digestKeyScheme G enc) ((ZKCP.Special.extOf E).digestKey enc).Ei β)
    (hε : ∀ tC tO, β tC tO ≤ ε (tC + tO)) :
    BindsWith (tokenArgumentSystem G enc bound build π₀ nextToken) (tokenExtractorE (X := X) E enc).Ei ε :=
  bindsWith_ofArgument (tokenScheme G enc bound build π₀) (commitE G enc bound) nextToken
    (digestKeyScheme G enc) (fun _ _ => rfl) _ β ε h hε

/-- From index binding of the scheme with openings, whose verifier holds the key itself, to the
statement on openings behind the hash of the key's code. hinj: no two keys have one code; hcode:
every key that the committer can put out has a code; hS: the committer asks at most tS queries. -/
theorem opens_digestSchemeE {β : ℕ → ℕ → ℝ≥0∞} (hinj : ZKCP.CodeIsOneToOne enc)
    (hcode : (ZKCP.SpecialAny.oneOf G).KeysHaveCodes enc) {tS : ℕ}
    (hS : ∀ i, ((ZKCP.SpecialAny.oneOf G).C i).QueryBound tS)
    (h : ZKCP.HasIndexBindingWith (ZKCP.openingRelation I) (ZKCP.SpecialAny.oneOf G).withOpenings
      (ZKCP.Special.extOf E).withOpenings β) :
    ZKCP.OpensToExtracted (digestKeyScheme G enc) ((ZKCP.Special.extOf E).digestKey enc).Ei
      fun tC tO => β tC (tO + tS) + (((tC + (tO + tS) + 2) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 :=
  ZKCP.opensToExtracted_of_binding (h.withOpenings_digestKey hinj hcode hS)

end VerifiableInference.Rec

/-! ## The hypothesis and the three statements at the front's scheme -/

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {r : InputArmsC}

/-- **The hypothesis on openings**: whoever opens a key of the scheme of the three checks opens it
to the index that the inner extractor b.E gives from that key and its maker's queries, up to β. A
hypothesis: this file proves it of no input. It itself states opening-form binding, at the key. -/
def HoleArmsC.opens (b : BesideArmsC r) (β : ℕ → ℕ → ℝ≥0∞) : Prop :=
  ZKCP.HasIndexBindingWith (ZKCP.openingRelation r.I)
    (ZKCP.SpecialAny.oneOf (schemeArmsC r)).withOpenings (ZKCP.Special.extOf b.E).withOpenings β

/-- The error of the second clause, from β and the bound tS on the committer's queries. -/
def epsOpens (β : ℕ → ℕ → ℝ≥0∞) (tS : ℕ) : ℕ → ℕ → ℝ≥0∞ :=
  fun tC tO => β tC (tO + tS) + (((tC + (tO + tS) + 2) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256

variable {p : PortArmsC r} {b : BesideArmsC r} {ε ε' : ℕ → ℝ≥0∞} {β : ℕ → ℕ → ℝ≥0∞} {tS : ℕ}

/-- **Under the hypothesis on openings, the commitment of the system whose verifier is the front
verifier binds in the opening form to the index that the front theorem's own extractor gives.**
hinj, hcode, hS: as in `Rec.opens_digestSchemeE`; hβ: ε' bounds `epsOpens β tS`. -/
theorem front_bindsWith_of_opens (hinj : ZKCP.CodeIsOneToOne r.enc)
    (hcode : (ZKCP.SpecialAny.oneOf (schemeArmsC r)).KeysHaveCodes r.enc)
    (hS : ∀ i, ((ZKCP.SpecialAny.oneOf (schemeArmsC r)).C i).QueryBound tS)
    (ho : HoleArmsC.opens b β) (hβ : ∀ tC tO, epsOpens β tS tC tO ≤ ε' (tC + tO)) :
    BindsWith (systemPortC p)
      ((extCodeC b).buildInstance : ZKCP.Extractor 256 r.I (List Token × List Token) Unit
        (ZKCP.Digest 256)
        (List Token × ((r.C × KeyRoot 256 r.L) × OfflineLinkOnlineProof 256 r.L r.aT r.aL))).Ei ε' :=
  (BindsWith.withVerifier (systemArmsC r) p.Files p.prove p.port _ ε').2
    (Rec.bindsWith_systemE (schemeArmsC r) b.E r.enc r.bound r.build r.π₀ r.nextToken
      (Rec.opens_digestSchemeE (schemeArmsC r) b.E r.enc hinj hcode hS ho) hβ)

/-- **Under the front theorem's named hypotheses and the hypothesis on openings: soundness and
opening-form binding for one extractor.** hcode, hS, hβ: as in `front_bindsWith_of_opens`. -/
theorem front_soundAndBinding_of_opens (h : FrontFieldsPlain p b ε)
    (hcode : (ZKCP.SpecialAny.oneOf (schemeArmsC r)).KeysHaveCodes r.enc)
    (hS : ∀ i, ((ZKCP.SpecialAny.oneOf (schemeArmsC r)).C i).QueryBound tS)
    (ho : HoleArmsC.opens b β) (hβ : ∀ tC tO, epsOpens β tS tC tO ≤ ε' (tC + tO)) :
    SoundAndBinding (systemPortC p) fun t => max (ε (t + p.n) + p.δ t) (ε' t) :=
  soundAndBinding_of_le (systemPortC p) _ (fun t => ε (t + p.n) + p.δ t) ε' _
    (verify_sound_portC h.parts.ties
      (verify_sound_arms_C_plain (systemArmsC r).IsModelOutput ε h.arms h.code h.meaning h.error))
    (front_bindsWith_of_opens h.code hcode hS ho hβ) (fun _ => le_max_left _ _)
    fun _ => le_max_right _ _

/-- **Under the hypotheses of `front_bindsWith_of_opens` nobody opens one commitment to two
different indices.** No bound of a check is among them. -/
theorem front_noTwoOpenings_of_opens (hinj : ZKCP.CodeIsOneToOne r.enc)
    (hcode : (ZKCP.SpecialAny.oneOf (schemeArmsC r)).KeysHaveCodes r.enc)
    (hS : ∀ i, ((ZKCP.SpecialAny.oneOf (schemeArmsC r)).C i).QueryBound tS)
    (ho : HoleArmsC.opens b β) (hβ : ∀ tC tO, epsOpens β tS tC tO ≤ ε' (tC + tO)) :
    NoTwoOpenings (systemPortC p) fun t => 2 * ε' t :=
  (front_bindsWith_of_opens (p := p) hinj hcode hS ho hβ).noTwoOpenings

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.BindsWith.withVerifier
#print axioms VerifiableInference.NoTwoOpenings.withVerifier
#print axioms VerifiableInference.run_withQueryLog_toRandomized
#print axioms VerifiableInference.DeterministicAlgorithm.evaluate_picking
#print axioms VerifiableInference.DeterministicAlgorithm.logUnder_picking
#print axioms VerifiableInference.DeterministicAlgorithm.queryBound_picking
#print axioms VerifiableInference.BindsWith.one_le_of_blind
#print axioms VerifiableInference.BindsWith.one_le_of_never
#print axioms VerifiableInference.NoTwoOpenings.one_le_of_blind
#print axioms VerifiableInference.Rec.bindsWith_systemE
#print axioms VerifiableInference.Rec.opens_digestSchemeE
#print axioms VerifiableInference.OnPublicFiles.front_bindsWith_of_opens
#print axioms VerifiableInference.OnPublicFiles.front_soundAndBinding_of_opens
#print axioms VerifiableInference.OnPublicFiles.front_noTwoOpenings_of_opens
