-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/SpecLife.lean: the lifetime experiment for the encodings, with batches and coalitions.
Definitions and one small lemma with its proof (`lt_of_mem_slotsOf`). The proofs on these
definitions are in Compile/Batch/Life.lean.
(Words of this library: lean/GLOSSARY.md.)

The protocols are those of a record `BatchProtocol` (Iop/Batch.lean).

Game 1 (`Call`, `real`, `ideal`; the theorem is lifetime in Compile/Batch/Life.lean). A batch call
names the encoding e, the set J of slots that the adversary owns (the coalition), the request of
each slot of J, and what the other slots hold (a request, or nothing). It returns the verifier
messages of the transcripts of the slots of J, that is ρ_0 and (ρ_j) for j in J, and the output for
J. The simulated answer is, by its type, a function of e, J and the requests of J alone: not of the
other slots (exactly: `simO`: `.bat e J xs _ => simBsess L.onlineBatch Sm.B J xs (Ps e)`).

Game 2 (its PCall, realP, idealP and the statement Spec.lifePlaced are not in this library;
`slotsOf`, `ownAt`, `slotList` are): a batch call names prompts, those of the coalition and the
others. The challenger computes the answers from the index, leaves out the prompts without an
answer, places the requests in the slots at random, and returns the answers to the coalition's
prompts, their slot numbers, and what game 1 returns. The simulator is given the coalition's
prompts' answers and nothing else about the call. Game 2 is meant to be game 1 with an adversary
that does the placement itself (not stated in Lean).

Notation: `ι`: the type of the names of the encodings; `e`, `e'`, `a`: in `ι`; `idx`: of type
`ι → I`; `J`: a `Finset (Fin N)`; ρ_0, ρ_j: the parts of the verifier randomness ρ = (ρ_0, ρ_1, ..,
ρ_N) (the doc comment of `bsess`); `zT`, `zL`, `zO`: in `ℝ≥0∞`: arguments of `Sims.Good` and of
`err`; `qT`, `qpar`, `qch`, `qon`: natural numbers: arguments of `load`, and of `BatchProtocol.Reads`
(Iop/Batch.lean); `Ryes`: of type `I → X → Prop`: an argument of `Allowed` and of `Sims.Good`.

What the experiments leave out, and details.
* No conditioned sessions: the verifier randomness of every session is uniform, and where it is in
  the withheld set the output is `none`. So no factor 1/(1 - p) for conditioning occurs in the
  bound.
* The names of the encodings form a finite type, the randomness of all encodings is sampled at the
  start, and the index idx e of each encoding e is fixed before the experiment: there is no call
  "new". Several indices, forests of runs of Link, repeated runs of Test and of Link are covered.
  The call `link` names parent and child, which must have the same index.
* In game 2 the placement is the restriction of a uniform permutation of the slots to the first
  places, in which the coalition's requests come first. This is a uniform injection of the requests
  into the slots (`pr_placement_eq` in Compile/Batch/Life.lean).
* The simulators read at the positions of the verifiers of J, which are a function of requests and
  verifier randomness (Iop/Batch.lean, (D5)).
-/
import Iop.Batch
import Compile.Life

noncomputable section

namespace Compile.BatchLife

open Prob Iop Compile.Lifetime
open scoped ENNReal

/-! ## 1. One session of a `BatchInteractiveOracleProof`, for a coalition J -/

section Session
variable {X : Type} {E : ExtSpec} {Wt : Type}

/-- What the experiment returns of a session of a `BatchInteractiveOracleProof` to the owner of the slots J: for each
slot of J the verifier messages of its transcript (so ρ_0 and ρ_j), and the output for J (for each
slot of J a disclosed view (`DView`, Iop/InteractiveOracleProof.lean), or `none`). -/
abbrev BSess (Q : BatchInteractiveOracleProof X E) {N : ℕ} (J : Finset (Fin N)) : Type :=
  (J → Rho Q.loc.shape) × (J → Option (DView Q.loc))

/-- The type of the simulators of Iop.BatchHonestProver.HVZK. -/
abbrev BSimOf (Q : BatchInteractiveOracleProof X E) (N : ℕ) : Type :=
  (J : Finset (Fin N)) → (J → X) → (J → Rho Q.loc.shape) →
  (E.Pos → Option E.Sym) → PMF (J → Option (DView Q.loc))

/-- A session: uniform verifier randomness ρ = (ρ_0, ρ_1, .., ρ_N), fresh prover coins, the output
for J at ρ. -/
def bsess {Q : BatchInteractiveOracleProof X E} (H : BatchHonestProver Q Wt) {N : ℕ} (w : Wt)
    (x : Fin N → Option X) (J : Finset (Fin N)) : PMF (BSess Q J) :=
  (unif (BRho N Q.loc.shape Q.ann)).bind fun ρ =>
    (H.output w x ρ J).map fun o => (fun j => ρ.slot j.1, o)

/-- A simulated session on the external string str: uniform verifier randomness, then the simulator,
which is given J, the requests of J, the verifier messages of the slots of J, and the answers of str
where the verifiers of J read. -/
def simBsess (Q : BatchInteractiveOracleProof X E) {N : ℕ} (Sim : BSimOf Q N) (J : Finset (Fin N))
    (xs : J → X) (str : E.Str) : PMF (BSess Q J) :=
  (unif (BRho N Q.loc.shape Q.ann)).bind fun ρ =>
    (Sim J xs (fun j => ρ.slot j.1) (Q.extAnsJ J xs (fun j => ρ.slot j.1) str)).map
      fun o => (fun j => ρ.slot j.1, o)

/-- The vector of requests: the requests of J, and what the other slots hold. -/
def vec {N : ℕ} (J : Finset (Fin N)) (xs : J → X) (rest : {j : Fin N // j ∉ J} → Option X) :
    Fin N → Option X :=
  fun j => if h : j ∈ J then some (xs ⟨j, h⟩) else rest ⟨j, h⟩

end Session

/-! ## 2. Game 1 -/

section Game
variable {I X ι : Type}

/-- The calls. ι is the set of names of the encodings, N the number of slots. -/
inductive Call (ι X : Type) (N : ℕ) : Type
  /-- a session of Test on encoding e -/
  | test (e : ι) : Call ι X N
  /-- a session of Link on the encodings e (parent) and e' (child) -/
  | link (e e' : ι) : Call ι X N
  /-- a session of Batch on encoding e: the adversary owns the slots J, with the requests xs; rest
  is what the other slots hold -/
  | bat (e : ι) (J : Finset (Fin N)) (xs : J → X) (rest : {j : Fin N // j ∉ J} → Option X) :
      Call ι X N

/-- The answer to a call. -/
def Ans (L : BatchProtocol I X) : Call ι X L.maxBatchSize → Type
  | .test _ => Sess L.offline
  | .link _ _ => Sess L.link
  | .bat _ J _ _ => BSess L.onlineBatch J

abbrev Adversary (L : BatchProtocol I X) (ι α : Type) : Type 1 := Play (Call ι X L.maxBatchSize) (Ans (ι := ι) L) α

/-- The sessions of the real experiment: encoding e is an encoding of the index idx e with the
randomness r e. -/
def realO (L : BatchProtocol I X) (idx : ι → I) (r : ι → L.EncodingRandomness) : ∀ c : Call ι X L.maxBatchSize, PMF (Ans L c)
  | .test e => sess L.honestOfflineProver (idx e, r e) ()
  | .link e e' => sess L.honestLinkProver (idx e, r e, r e') ()
  | .bat e J xs rest => bsess L.honestOnlineBatchProver (idx e, r e) (vec J xs rest) J

/-- One simulator for each of the three protocols. -/
structure Sims (L : BatchProtocol I X) where
  T : SimOf L.offline
  Lk : SimOf L.link
  B : BSimOf L.onlineBatch L.maxBatchSize

/-- The three simulators are good in the sense of (Hid-TL) and (Hid-B) (`BatchProtocol.Hiding`,
Iop/Batch.lean). -/
structure Sims.Good {L : BatchProtocol I X} (Sm : Sims L) (Ryes : I → X → Prop) (zT zL zO : ℝ≥0∞) : Prop where
  goodT : ∀ w x, prRho {ρ | L.honestOfflineProver.output w x ρ ≠ Sm.T x ρ (L.offline.extAns x ρ (L.honestOfflineProver.ext w))} ≤ zT
  goodL : ∀ w x, prRho {ρ | L.honestLinkProver.output w x ρ ≠ Sm.Lk x ρ (L.link.extAns x ρ (L.honestLinkProver.ext w))} ≤ zL
  goodB : ∀ (w : I × L.EncodingRandomness) (x : Fin L.maxBatchSize → Option X), (∀ j xj, x j = some xj → Ryes w.1 xj) →
    ∀ (J : Finset (Fin L.maxBatchSize)) (xs : J → X), (∀ j : J, x j = some (xs j)) →
      prBRho {ρ | L.honestOnlineBatchProver.output w x ρ J ≠
            Sm.B J xs (fun j => ρ.slot j.1)
              (L.onlineBatch.extAnsJ J xs (fun j => ρ.slot j.1) (L.honestOnlineBatchProver.ext w))} ≤ J.card * zO

/-- Simulated sessions on the strings Ps e. The answer to a batch call does not depend on "rest". -/
def simO (L : BatchProtocol I X) (Sm : Sims L) (Ps : ι → Fin L.wordLength → L.Symbol) : ∀ c : Call ι X L.maxBatchSize, PMF (Ans L c)
  | .test e => simSess L.offline Sm.T () (Ps e)
  | .link e e' => simSess L.link Sm.Lk () (Ps e, Ps e')
  | .bat e J xs _ => simBsess L.onlineBatch Sm.B J xs (Ps e)

/-- The real experiment: the distribution of the adversary's output. -/
def real [Fintype ι] [DecidableEq ι] (L : BatchProtocol I X) (idx : ι → I) {α : Type} (t : Adversary L ι α) :
    PMF α :=
  (unif (ι → L.EncodingRandomness)).bind fun r => t.run (realO L idx r)

/-- The simulated experiment: the simulator keeps an encoding of a fixed index i₀ in the place of
each encoding and answers each call by a simulated session on these. It answers the calls one by one
and does not depend on the adversary. -/
def ideal [Fintype ι] [DecidableEq ι] (L : BatchProtocol I X) (Sm : Sims L) (i₀ : I)
    {α : Type} (t : Adversary L ι α) : PMF α :=
  (unif (ι → L.EncodingRandomness)).bind fun r => t.run (simO L Sm fun e => L.encodeIndex i₀ (r e))

/-- A call is allowed: parent and child of a call `link` have the same index; all requests of a
batch, those of the other slots included, are in the relation with the index. -/
def Allowed {N : ℕ} (Ryes : I → X → Prop) (idx : ι → I) : Call ι X N → Prop
  | .test _ => True
  | .link e e' => idx e = idx e'
  | .bat e _ xs rest => (∀ j, Ryes (idx e) (xs j)) ∧ ∀ j x, rest j = some x → Ryes (idx e) x

/-- The error of the session that a call starts: a coalition J costs |J| zO. -/
def err {N : ℕ} (zT zL zO : ℝ≥0∞) : Call ι X N → ℝ≥0∞
  | .test _ => zT
  | .link _ _ => zL
  | .bat _ J _ _ => J.card * zO

/-- The query complexity of the session that a call starts to encoding a. A batch loads q_on
whatever |J| is: BatchProtocol.Reads.cntB (BatchInteractiveOracleProof.ReadsAtMost) bounds by q_on the number of positions that
the verifiers of all non-empty slots read together in one execution (the union), not those of one
slot. -/
def load {N : ℕ} [DecidableEq ι] (qT qpar qch qon : ℕ) : Call ι X N → ι → ℕ
  | .test e, a => if a = e then qT else 0
  | .link e e', a => (if a = e then qpar else 0) + if a = e' then qch else 0
  | .bat e _ _ _, a => if a = e then qon else 0

end Game

/-! ## 3. Game 2: helpers for the placement -/

section Placed
variable {I X Pr ι : Type}


variable {N : ℕ}

/-- the slots of the first k places under the placement σ -/
def slotsOf (σ : Equiv.Perm (Fin N)) (k : ℕ) : Finset (Fin N) :=
  Finset.univ.filter fun j => (σ.symm j).val < k

theorem lt_of_mem_slotsOf {σ : Equiv.Perm (Fin N)} {k : ℕ} (j : slotsOf σ k) :
    (σ.symm j.1).val < k :=
  (Finset.mem_filter.1 j.2).2

/-- the requests of these slots: request number a is in slot σ a -/
def ownAt (σ : Equiv.Perm (Fin N)) (own : List X) : slotsOf σ own.length → X := fun j =>
  own[(σ.symm j.1).val]'(lt_of_mem_slotsOf j)

/-- the slot numbers of the first k places, in their order (those places that exist) -/
def slotList (σ : Equiv.Perm (Fin N)) (k : ℕ) : List (Fin N) :=
  (List.finRange N).filterMap fun a => if a.val < k then some (σ a) else none

variable (L : BatchProtocol I X) (ans : I → Pr → Option X)





end Placed

end Compile.BatchLife
