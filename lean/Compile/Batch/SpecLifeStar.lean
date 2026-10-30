-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/SpecLifeStar.lean: the lifetime experiment for one first encoding of the index and its
copies, with batches. Definitions and one statement. Proofs: Compile/Batch/LifeStar.lean. (Words of
this library: lean/GLOSSARY.md.)

The lifetime experiment and the lifetime theorem for one first encoding and m copies: one session of
Test on the first encoding, one of Link for each copy, at most s1 of Batch on each copy, without
conditioned sessions. This is the form in which the compiler (Compile/) uses the theorem.

* Calls (`LifeOutB`): "setup"; a batch on copy j with the requests xs, where xs are the adversary's
  own requests and nothing else. What the other slots hold is not part of the call: the session, as
  the owner of a set J of slots sees it, does not depend on it (`bsess_vec_congr`, with
  `output_vec`, in Compile/Batch/Life.lean: a fact about the definition of `Iop.BatchHonestProver.output`). So
  a challenger with these calls is never given the hidden slots or their number, and a batch without
  an own slot needs no call.
* Replies: to "setup": the session of Test on the first encoding and the sessions of Link, one for
  each copy; to a batch: the slot numbers of the requests, in their order; the set J of these slots;
  for each slot of J the verifier messages of its transcript (so ρ_0 and ρ_j); the output for J.
  (none: there is no such copy, or "setup" has not been made.)
* Placement: the experiment samples a uniform permutation σ of the maxBatchSize slots and puts request number a
  into slot σ a: a uniform injection of the requests into the slots (`pr_placement_eq` in
  Compile/Batch/Life.lean), which is the marginal of any uniform placement of all requests of the
  batch.
* `StarWB`: the experiment for arbitrary distributions of the three kinds of sessions, as functions
  of the encoding randomness. The real experiment `LifeB` and the simulator `simWorldB` are two
  instances of it.
* `LifeAdmB`: one "setup", first; then at most n batches, at most s1 on each copy, each with at most
  maxBatchSize requests, all allowed.

The bound. zT + m zL + n (maxBatchSize zO): a batch costs zO for each own slot. The hypotheses of
`Spec.lifeStarBWith`, beside `LifeAdmB`: `L.Wired`, `L.Reads`, simulators that are good
(`Sims.Good`), and the two inequalities qT + m qpar ≤ b and qch + s1 qon ≤ b.

The load. A batch loads its copy with q_on whatever the number of own slots is (`BatchProtocol.Reads.cntB`
bounds the positions read by all verifiers together).
-/
import Compile.Batch.SpecLife
import Rom.World

noncomputable section

namespace Compile.BatchLife

open Prob Iop Rom Compile.Lifetime
open scoped ENNReal

variable {I X : Type}

/-- calls: setup; a batch on copy j with the adversary's own requests xs -/
abbrev LifeOutB (X : Type) : Type := Unit ⊕ (ℕ × List X)

/-- what a batch returns: the slot numbers of the requests, in their order; the set J of these
slots, with the verifier messages and the output for J -/
abbrev BRet (L : BatchProtocol I X) : Type := List (Fin L.maxBatchSize) × Σ J : Finset (Fin L.maxBatchSize), BSess L.onlineBatch J

abbrev LifeInB (L : BatchProtocol I X) : Type := (Sess L.offline × List (Sess L.link)) ⊕ Option (BRet L)

/-- the distribution of a session of Batch, as a function of the set of the adversary's own slots,
their requests, and what the other slots hold -/
abbrev BLaw (L : BatchProtocol I X) : Type :=
  (J : Finset (Fin L.maxBatchSize)) → (J → X) → ({j : Fin L.maxBatchSize // j ∉ J} → Option X) → PMF (BSess L.onlineBatch J)

/-- Placement: a uniform permutation σ of the slots; request number a is in slot σ a; the other
slots are empty. -/
def placeB (L : BatchProtocol I X) (F : BLaw L) (xs : List X) : PMF (BRet L) :=
  (unif (Equiv.Perm (Fin L.maxBatchSize))).bind fun σ =>
    (F (slotsOf σ xs.length) (ownAt σ xs) fun _ => none).map fun a =>
      (slotList σ xs.length, ⟨slotsOf σ xs.length, a⟩)

section Star
variable {L : BatchProtocol I X} (sT : L.EncodingRandomness → PMF (Sess L.offline))
  (sL : L.EncodingRandomness → L.EncodingRandomness → PMF (Sess L.link)) (sB : L.EncodingRandomness → BLaw L)

/-- n fresh copies, each with a session of Link with the first encoding -/
def linksGB (r₀ : L.EncodingRandomness) : ℕ → PMF (List (L.EncodingRandomness × Sess L.link))
  | 0 => PMF.pure []
  | n + 1 =>
    (unif L.EncodingRandomness).bind fun r => (sL r₀ r).bind fun s => (linksGB r₀ n).map fun t => (r, s) :: t

/-- The experiment with m copies, for arbitrary distributions of the three kinds of sessions. The
state holds the encoding randomness of the copies, once "setup" is made. Oracle queries are answered
by lazy sampling; no session touches the table. -/
def StarWB (S : OSpec) (m : ℕ) : World S (LifeOutB X) (LifeInB L) where
  σ := Option (List L.EncodingRandomness) × Table S
  answer := fun s o q => (lazyAnswer s.2 o q).map fun a => (a.1, (s.1, a.2))
  reply := fun s c => match c with
    | .inl () => (unif L.EncodingRandomness).bind fun r₀ => (sT r₀).bind fun a => (linksGB sL r₀ m).map fun ls =>
        (.inl (a, ls.map Prod.snd), (some (ls.map Prod.fst), s.2))
    | .inr (j, xs) => match s.1.bind (fun l => l[j]?) with
        | none => PMF.pure (.inr none, s)
        | some r => (placeB L (sB r) xs).map fun o => (.inr (some o), s)

end Star

/-- The real lifetime experiment on the index i. -/
def LifeB (S : OSpec) (L : BatchProtocol I X) (m : ℕ) (i : I) : World S (LifeOutB X) (LifeInB L) :=
  StarWB (fun r => sess L.honestOfflineProver (i, r) ()) (fun r r' => sess L.honestLinkProver (i, r, r') ())
    (fun r J xs rest => bsess L.honestOnlineBatchProver (i, r) (vec J xs rest) J) S m

/-- The simulator: the same experiment on encodings of the fixed index i₀, with simulated sessions.
-/
def simWorldB (S : OSpec) (L : BatchProtocol I X) (m : ℕ) (Sm : Sims L) (i₀ : I) :
    World S (LifeOutB X) (LifeInB L) :=
  StarWB (fun r => simSess L.offline Sm.T () (L.encodeIndex i₀ r))
    (fun r r' => simSess L.link Sm.Lk () (L.encodeIndex i₀ r, L.encodeIndex i₀ r'))
    (fun r J xs _ => simBsess L.onlineBatch Sm.B J xs (L.encodeIndex i₀ r)) S m

/-- (Life): one setup, first; then at most s1 batches on each copy, at most n in all, each with at
most maxBatchSize requests, all allowed. c counts the batches on each copy. -/
def LifeAdmB {L : BatchProtocol I X} {S : OSpec} {α : Type} (ok : X → Prop) (s1 : ℕ) :
    Adv S (LifeOutB X) (LifeInB L) α → (ℕ → ℕ) → Bool → ℕ → Prop
  | .halt _, _, _, _ => True
  | .sample _ k, c, b, n => ∀ r, LifeAdmB ok s1 (k r) c b n
  | .query _ _ k, c, b, n => ∀ r, LifeAdmB ok s1 (k r) c b n
  | .call (.inl ()) k, c, b, n => b = false ∧ ∀ a, LifeAdmB ok s1 (k a) c true n
  | .call (.inr _) _, _, _, 0 => False
  | .call (.inr (j, xs)) k, c, b, n + 1 =>
      b = true ∧ c j < s1 ∧ xs.length ≤ L.maxBatchSize ∧ (∀ x ∈ xs, ok x) ∧
      ∀ a, LifeAdmB ok s1 (k a) (Function.update c j (c j + 1)) b n

/-- The lifetime theorem with batches, simulator named (hypotheses below). -/
def Spec.lifeStarBWith : Prop :=
  ∀ (S : OSpec) (I X : Type) (L : BatchProtocol I X) (Ryes : I → X → Prop) (M : LH.Nums) (m s1 : ℕ), L.Wired →
    L.Reads M.b M.qT M.qpar M.qch M.qon →
    ∀ Sm : Sims L, Sm.Good Ryes M.zT M.zL M.zO →
      M.qT + m * M.qpar ≤ M.b → M.qch + s1 * M.qon ≤ M.b →
      ∀ (i i₀ : I) (α : Type) (B : Adv S (LifeOutB X) (LifeInB L) α) (n : ℕ),
        LifeAdmB (Ryes i) s1 B (fun _ => 0) false n →
        tv ((interact (LifeB S L m i) B (none, Table.empty S)).map Prod.fst)
            ((interact (simWorldB S L m Sm i₀) B (none, Table.empty S)).map Prod.fst) ≤
          M.zT + m * M.zL + n * (L.maxBatchSize * M.zO)

end Compile.BatchLife
