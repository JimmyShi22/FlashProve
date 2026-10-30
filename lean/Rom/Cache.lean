-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/Cache.lean: what a prover may keep beside its key. A transformation of any commit-and-prove
argument of ZKCP/Gen.lean, over any family of oracles.

The transformation. A = (C, P, V) is a scheme; m is an oracle algorithm without coins that computes
a value (the cache) from the prover's key. `withCache A m P'` is the scheme in which
    C' i            runs C i, then m on the prover's key, and keeps (isk, cache) in place of isk;
    P' (isk, c) b   is any algorithm;
    V'              is V.

The theorem (`sameRunVia_withCache`). If, for every family g of oracle functions, every key k and
every batch b, P' on (k, the value of m k under g) has the output distribution of P on k, then A and
`withCache A m P'` are in the relation `A.SameRunVia Prod.fst` of ZKCP/GenSameRun.lean. So every
property listed there (completeness, index binding, index privacy, and the three together) holds for
the one if and only if it holds for the other, with the same relations, extractor, simulator and
bounds.

What this allows. An implementation may keep beside isk any value that an oracle algorithm without
coins computes from isk, and may use it in any way that leaves the output distribution of P as it
is, for every oracle: read it instead of computing it again, compare it with what it computes, stop
if the two differ.

Why without coins. Under fixed oracles such an algorithm has one value (`NoCoin.runEager`: the run
is the point mass at `det g`), so the cache is a function of the key and the oracles, and P' can be
compared with P key by key. An algorithm whose coins are derived from a seed through an oracle
(`derive`, Rom/SpecDerive.lean) has no coins, whether or not the original algorithm had any
(`noCoin_derive`).

Notation:
  `A`: `Gen.Arg S I X W IVK ISK Pf` (ZKCP/Gen.lean): ARG = (C, P, V) over the family S;
    `A.C : I → OComp S (IVK × ISK)`, `A.P : ISK → (b : List (X × W)) → OComp S (Gen.Slots Pf b)`,
    `A.V : IVK → X → Pf → OComp S Bool`
  `Gen.HasCompletenessError R A B α`, `Gen.HasIndexBindingWith R A E ε`,
    `Gen.HasIndexPrivacyWith R A B Sim ζ` (ZKCP/Gen.lean): the three fields of
    `Gen.IsZKCPArgWith R A B E Sim α ε ζ`
  `B`: `ℕ`: the bound on the length of a batch (doc comment of `Gen.Arg`, ZKCP/Gen.lean)
  `E`: `Gen.Extractor S I X W IVK Pf`; `Sim`: `Gen.Simulator S PP IVK X Pf` (ZKCP/Gen.lean)
  `α` in `isZKCPArgWith_withCache`: `ℝ≥0∞`: the last argument of `Gen.HasCompletenessError R A B α`
    (ZKCP/Gen.lean)
  `ε`: `ℕ → ℕ → ℝ≥0∞`: in `Gen.HasIndexBindingWith R A E ε` (ZKCP/Gen.lean) it stands as `ε tC tP`,
    with `Ct.QueryBound tC` and `∀ st, (Pt st).QueryBound tP`; `Ct : OComp S (IVK × St)`,
    `Pt : St → OComp S (X × Pf)`
  `ζ`: `ℕ → ℕ → ℝ≥0∞`: in `Gen.PrivacyFor R A Sim ζ i Z` (ZKCP/Gen.lean) it stands as `ζ tV N`, with
    `∀ ivk, (Vt ivk).QueryBound tV`; N counts batches

Limits:
  * Nothing on cost: neither that P' is faster than P nor how large the cache is.
  * Nothing on a cache that somebody else has written, or that has been damaged: of P' nothing is
    asked on a pair (isk, c) that C' cannot return because c is not the value of m on isk under the
    oracles at hand.
  * Nothing on secrecy beyond the properties of the scheme: the cache is a part of the prover's key
    and is given to no one; whoever reads it may learn what isk and the oracles determine.
  * Nothing on queries: C' makes the queries of m too, and P' may make other queries than P; a bound
    on the queries of an honest algorithm does not carry over from A to `withCache A m P'`.

Which cache the implementation keeps is the subject of Compile/Batch/SeedCache.lean.
"The implementation" in this file's comments is not the released programs: what is said of it need
not hold of them (lean/LIMITS.md, L1).
-/
import ZKCP.GenSameRun
import Rom.SpecDerive
import Rom.EagerLazy

open scoped ENNReal

namespace Rom

variable {S : OSpec} {α β : Type}

namespace OComp

/-- no path of the algorithm samples coins -/
def NoCoin : OComp S α → Prop
  | pure _ => True
  | query _ _ k => ∀ r, (k r).NoCoin
  | sample _ _ => False

/-- the result of the run under the oracle functions g in which every sample is 0 -/
def det (g : Fam S) : OComp S α → α
  | pure a => a
  | query o q k => (k (g o q)).det g
  | sample _ k => (k 0).det g

theorem noCoin_pure (a : α) : (pure a : OComp S α).NoCoin := trivial

theorem NoCoin.bind {c : OComp S α} {k : α → OComp S β} (hc : c.NoCoin) (hk : ∀ a, (k a).NoCoin) :
    (c.bind k).NoCoin := by
  induction c with
  | pure a => exact hk a
  | query o q f ih => exact fun r => ih r (hc r)
  | sample n f _ => exact hc.elim

/-- An algorithm whose coins are derived has no coins. -/
theorem noCoin_derive (σ : SeedOracle S) (s : Fin (σ.sd + 1)) (c : OComp S α) :
    ∀ j, (c.derive σ s j).NoCoin := by
  induction c with
  | pure a => exact fun _ => trivial
  | query o q f ih => exact fun j r => ih r j
  | sample n f ih => exact fun j d => ih _ (j + 1)

theorem det_bind (g : Fam S) (c : OComp S α) (k : α → OComp S β) :
    (c.bind k).det g = (k (c.det g)).det g := by
  induction c with
  | pure a => rfl
  | query o q f ih => exact ih _
  | sample n f ih => exact ih _

/-- Under fixed oracles an algorithm without coins has one value. -/
theorem NoCoin.runEager {c : OComp S α} (hc : c.NoCoin) (g : Fam S) :
    c.runEager g = PMF.pure (c.det g) := by
  induction c with
  | pure a => rfl
  | query o q f ih => exact ih _ (hc _)
  | sample n f _ => exact hc.elim

/-- an algorithm without coins, followed by anything: under fixed oracles, what follows is run on
its value -/
theorem NoCoin.runEager_bind {c : OComp S α} (hc : c.NoCoin) (k : α → OComp S β) (g : Fam S) :
    (c.bind k).runEager g = (k (c.det g)).runEager g := by
  rw [OComp.runEager_bind, hc.runEager g, PMF.pure_bind]

/-- For an algorithm without coins, `derive` returns the algorithm itself. -/
theorem NoCoin.derive_eq (σ : SeedOracle S) (s : Fin (σ.sd + 1)) {c : OComp S α} (hc : c.NoCoin) :
    ∀ j, c.derive σ s j = c := by
  induction c with
  | pure a => exact fun _ => rfl
  | query o q f ih => exact fun j => congrArg _ (funext fun r => ih r (hc r) j)
  | sample n f _ => exact hc.elim

end OComp

open ZKCP

variable {I X W PP IVK ISK Ca Pf : Type}

/-- The scheme A with a cache: the committer also runs m on the prover's key and keeps the result
beside it; the prover is P'. -/
def withCache (A : Gen.Arg S I X W IVK ISK Pf) (m : ISK → OComp S Ca)
    (P' : ISK × Ca → (b : List (X × W)) → OComp S (Gen.Slots Pf b)) :
    Gen.Arg S I X W IVK (ISK × Ca) Pf where
  C := fun i => (A.C i).bind fun o => (m o.2).bind fun c => OComp.pure (o.1, (o.2, c))
  P := P'
  V := A.V

section
variable {A : Gen.Arg S I X W IVK ISK Pf}
  {m : ISK → OComp S Ca} {P' : ISK × Ca → (b : List (X × W)) → OComp S (Gen.Slots Pf b)}

/-- what the committer with a cache returns, under fixed oracles -/
theorem runEager_withCache_C (hm : ∀ k, (m k).NoCoin) (i : I) (g : Fam S) :
    ((withCache A m P').C i).runEager g =
      ((A.C i).runEager g).map fun o => (o.1, (o.2, (m o.2).det g)) := by
  show ((A.C i).bind fun o => (m o.2).bind fun c => OComp.pure (o.1, (o.2, c))).runEager g = _
  rw [OComp.runEager_bind]
  refine congrArg _ (funext fun o => ?_)
  rw [OComp.runEager_bind, (hm o.2).runEager g, PMF.pure_bind]
  rfl

/-- If m has no coins and, for every g, k and b, P' on (k, `(m k).det g`) has under g the output
distribution of P on k, then the scheme with a cache has the output distributions of the scheme
without (the prover: on every key that its committer can return). -/
theorem sameRunVia_withCache_det (hm : ∀ k, (m k).NoCoin)
    (hP : ∀ g k b, (P' (k, (m k).det g) b).runEager g = (A.P k b).runEager g) :
    A.SameRunVia Prod.fst (withCache A m P') where
  C i g := by
    rw [runEager_withCache_C hm, PMF.map_comp]
    exact (PMF.map_id _).symm
  P i g key hkey b := by
    rw [runEager_withCache_C hm, PMF.support_map] at hkey
    obtain ⟨o, -, rfl⟩ := hkey
    exact hP g o.2 b
  V _ _ _ _ := rfl

/-- If m has no coins and, on every key, with the value that m has under g, P' has under g the
output distribution of P, then the scheme with a cache has the output distributions of the scheme
without (the prover: on every key that its committer can return). -/
theorem sameRunVia_withCache (hm : ∀ k, (m k).NoCoin)
    (hP : ∀ g k c b,
      (m k).runEager g = PMF.pure c → (P' (k, c) b).runEager g = (A.P k b).runEager g) :
    A.SameRunVia Prod.fst (withCache A m P') :=
  sameRunVia_withCache_det hm fun g k b => hP g k _ b ((hm k).runEager g)

/-- Under the two conditions of `sameRunVia_withCache`: the primitive passes from the scheme to the
scheme with a cache and back: same relations, extractor, simulator and bounds. -/
theorem isZKCPArgWith_withCache (hm : ∀ k, (m k).NoCoin)
    (hP : ∀ g k c b,
      (m k).runEager g = PMF.pure c → (P' (k, c) b).runEager g = (A.P k b).runEager g)
    (R : Gen.RelPair I X W PP) (B : ℕ) (E : Gen.Extractor S I X W IVK Pf)
    (Sim : Gen.Simulator S PP IVK X Pf) (α : ℝ≥0∞) (ε ζ : ℕ → ℕ → ℝ≥0∞) :
    Gen.IsZKCPArgWith R A B E Sim α ε ζ ↔ Gen.IsZKCPArgWith R (withCache A m P') B E Sim α ε ζ :=
  (sameRunVia_withCache hm hP).isZKCPArgWith_iff R B E Sim α ε ζ

end

end Rom
