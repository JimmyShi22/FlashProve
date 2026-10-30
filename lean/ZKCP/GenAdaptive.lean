-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ZKCP/GenAdaptive.lean: completeness against an adaptive environment, in the form of ZKCP/Gen.lean.

Not part of the definitions of ZKCP/Defs.lean, and not part of Gen.IsZKCPArg. It is to ZKCP/Gen.lean
(a family of oracles, R_yes ⊆ R_no, batches) what ZKCP/Adaptive.lean is to ZKCP/Defs.lean.

`sessions_of_refined` (ZKCP/Basic.lean): from refined completeness with (α_C, α_P)
(`HasRefinedCompletenessError`, ZKCP/Defs.lean), for every i and adaptively chosen pairs (x_j, w_j),
j ≤ N, with (i, x_j, w_j) ∈ R, and π_j ← P^f(isk, x_j, w_j): Pr[ V rejects π_j for some j ≤ N ] ≤
α_C + N α_P. ZKCP/Adaptive.lean states this conclusion as a property for the environments of its
kind (trees with t queries that are given ivk; `sessions_of_refined` of ZKCP/Basic.lean is for a
chooser without coins that knows the whole oracle and both keys), for sessions of one pair over one
oracle. Here is the same property where a session is a batch: the environment names a list of at
most B pairs, the honest prover proves them at once, and the environment receives all proofs of the
batch and V's bit on each. N counts batches here, so up to N · B proofs, where the N of
`sessions_of_refined` counts pairs.

  `BEnv`                          The environment: a tree that queries the oracles, draws coins, and
                                  names the next batch; it is given ivk, every honest proof and V's
                                  bit on it; it is not given isk.
  `adaptiveLoop`, `adaptiveExp`   The experiment: an honest key for i, then at most N honest
                                  batches.
  `HasAdaptiveCompletenessError`  For every index i, every t-query environment all of whose batches
                                  are valid for i, and every N: Pr[ V rejects some honest proof of
                                  the first N batches ] ≤ α(t, N).
  `completeness_of_adaptive`      A sanity lemma: the property implies `Gen.HasCompletenessError`,
                                  with α(0, 1). The converse is false: see below.

Related fact (said here without a theorem): there is an example scheme that, at B = 1, is complete
with error 1/2 and has α(0, 1) ≥ 1 here.

How to read it. (a) `QueryBound` counts the environment's queries only: those of C, P and V are not
in t. (b) `QueryBound` and `Valid` are required on every path of the tree, also on paths that no
honest run produces (lists of proofs of a wrong length, bits that V would not give). Pruning such
paths changes no behaviour, so no environment is lost (this is argued, not proved in Lean). (c) What
it does not cover: the environment is not given isk, cannot submit proofs of its own to V, and all
batches are for one index and one key. (d) At B = 0, or for an index without any pair in R_yes, only
empty batches are valid and every scheme has the property with α = 0 (for one such index: its bound
alone holds with 0); `Gen.HasCompletenessError` behaves the same way.

What to expect of a bound. In `Gen.HasCompletenessError` the batch is fixed before the key and the
oracles, so a scheme whose failures depend on them can have it without any term in the number of
queries. Here already the first batch may depend on ivk, on the environment's coins and on its
queries, and every later batch also on the proofs seen so far. So a term in t can be needed, already
at N = 1.
-/
import ZKCP.Gen

open scoped ENNReal

namespace ZKCP.Gen

open Rom (OSpec Fam)

/-- The environment. It halts, queries an oracle, draws coins, or names the next batch; it then
receives the honest proofs of all slots of the batch and V's bits on them. So each choice may depend
on ivk, on all earlier proofs and bits, on its queries and on its coins. It is given neither isk nor
the oracles as a whole. -/
inductive BEnv (S : OSpec) (X W Pf : Type) : Type
  | halt : BEnv S X W Pf
  | query (o : S.ι) (q : S.Dom o) (k : S.Rng o → BEnv S X W Pf) : BEnv S X W Pf
  | sample (n : ℕ) (k : Fin (n + 1) → BEnv S X W Pf) : BEnv S X W Pf
  | batch (b : List (X × W)) (k : List Pf → List Bool → BEnv S X W Pf) : BEnv S X W Pf

section Adaptive
variable {S : OSpec} {I X W PP IVK ISK Pf : Type}

/-- The environment makes at most t queries, on every path. -/
def BEnv.QueryBound : BEnv S X W Pf → ℕ → Prop
  | .halt, _ => True
  | .query _ _ _, 0 => False
  | .query _ _ k, t + 1 => ∀ r, (k r).QueryBound t
  | .sample _ k, t => ∀ r, (k r).QueryBound t
  | .batch _ k, t => ∀ πs bs, (k πs bs).QueryBound t

/-- Every batch that the environment names is allowed (`ok`), whatever it has received. -/
def BEnv.Valid (ok : List (X × W) → Prop) : BEnv S X W Pf → Prop
  | .halt => True
  | .query _ _ k => ∀ r, (k r).Valid ok
  | .sample _ k => ∀ r, (k r).Valid ok
  | .batch b k => ok b ∧ ∀ πs bs, (k πs bs).Valid ok

variable (R : RelPair I X W PP) (A : Arg S I X W IVK ISK Pf)

/-- Run V on every pair; the list of its bits. -/
def verifyBits (ivk : IVK) : List (X × Pf) → Rom.OComp S (List Bool)
  | [] => pure []
  | (x, π) :: rest => do
      let c ← A.V ivk x π
      let cs ← verifyBits ivk rest
      pure (c :: cs)

/-- The batches on one key; n is the number of batches still allowed. The result is true if V has
accepted every proof. -/
def adaptiveLoop (ivk : IVK) (isk : ISK) : BEnv S X W Pf → ℕ → Rom.OComp S Bool
  | .halt, _ => pure true
  | .query o q k, n => .query o q fun r => adaptiveLoop ivk isk (k r) n
  | .sample m k, n => .sample m fun r => adaptiveLoop ivk isk (k r) n
  | .batch _ _, 0 => pure true
  | .batch b k, n + 1 =>
      (A.P isk b).bind fun πs => (verifyBits A ivk ((b.map Prod.fst).zip πs.val)).bind fun bs =>
        (adaptiveLoop ivk isk (k πs.val bs) n).bind fun rest => pure (bs.all id && rest)

/-- The experiment: an honest key for i, then at most N honest batches that the environment
chooses. -/
def adaptiveExp (E : IVK → BEnv S X W Pf) (i : I) (N : ℕ) : Rom.OComp S Bool :=
  (A.C i).bind fun key => adaptiveLoop A key.1 key.2 (E key.1) N

/-- Completeness against an adaptive environment, for batches of at most B pairs (our notion for
the claim of `sessions_of_refined` (ZKCP/Basic.lean)): for each index i, each environment with at
most
t queries, chosen after i, all of whose batches are valid for i, and each N, the probability that V
rejects at least one honest proof of the first N batches is at most α t N. -/
def HasAdaptiveCompletenessError (B : ℕ) (α : ℕ → ℕ → ℝ≥0∞) : Prop :=
  ∀ (i : I) (t N : ℕ) (E : IVK → BEnv S X W Pf), (∀ ivk, (E ivk).QueryBound t) →
    (∀ ivk, (E ivk).Valid (ValidBatch R B i)) →
    Rom.Pr (adaptiveExp A E i N) (fun _ => {b | b = false}) ≤ α t N

variable {R A}

private theorem bindAssoc {α β γ : Type} (c : Rom.OComp S α)
    (g : α → Rom.OComp S β) (h : β → Rom.OComp S γ) :
    (c.bind g).bind h = c.bind fun a => (g a).bind h := by
  induction c with
  | pure a => rfl
  | query o q k ih => exact congrArg _ (funext ih)
  | sample n k ih => exact congrArg _ (funext ih)

theorem verifyAll_eq (ivk : IVK) :
    ∀ l : List (X × Pf), verifyAll A ivk l = (verifyBits A ivk l).bind fun bs => pure (bs.all id)
  | [] => rfl
  | (x, π) :: rest => by
      have e1 : verifyAll A ivk ((x, π) :: rest) =
          (A.V ivk x π).bind fun c => (verifyAll A ivk rest).bind fun cs => pure (c && cs) := rfl
      have e2 : verifyBits A ivk ((x, π) :: rest) =
          (A.V ivk x π).bind fun c => (verifyBits A ivk rest).bind fun cs => pure (c :: cs) := rfl
      rw [e1, e2, verifyAll_eq ivk rest]
      simp only [bindAssoc]
      rfl

/-- A sanity lemma. The property implies completeness in the sense of `Gen.HasCompletenessError`,
with α(0, 1): take the constant environment that names the batch b and halts. (Not conversely: at no
queries and one batch the environment is still given ivk.) -/
theorem completeness_of_adaptive
    {B : ℕ} {α : ℕ → ℕ → ℝ≥0∞} (h : HasAdaptiveCompletenessError R A B α) :
    HasCompletenessError R A B (α 0 1) := by
  intro i b hb
  have e : completenessExp A i b = adaptiveExp A (fun _ => .batch b fun _ _ => .halt) i 1 := by
    have e1 : completenessExp A i b =
        (A.C i).bind fun k =>
          (A.P k.2 b).bind fun πs => verifyAll A k.1 ((b.map Prod.fst).zip πs.val) := rfl
    rw [e1]
    simp only [verifyAll_eq]
    unfold adaptiveExp
    congr 1
    funext k
    show _ =
        (A.P k.2 b).bind fun πs => (verifyBits A k.1 ((b.map Prod.fst).zip πs.val)).bind fun bs =>
      (pure true : Rom.OComp S Bool).bind fun rest => pure (bs.all id && rest)
    congr 1
    funext πs
    congr 1
    funext bs
    show pure (bs.all id) = (pure (bs.all id && true) : Rom.OComp S Bool)
    rw [Bool.and_true]
  rw [e]
  exact h i 0 1 _ (fun _ _ _ => trivial) fun _ => ⟨hb, fun _ _ => trivial⟩

end Adaptive

end ZKCP.Gen
