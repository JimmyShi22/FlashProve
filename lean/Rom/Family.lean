-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/Family.lean: typed random oracles implemented by one random oracle on bit strings.

A family `S` of random oracles whose answers are tuples of hash blocks of `lam` bits is implemented
by one oracle f from bit strings to `lam` bits: hash block j of the answer of oracle o at query q is
f (code o q j), for one bijective encoding of queries (the query encoding: `OracleCoding`, with the field
`code`). `Spec.family` (if the extractor meets `LocalTo`, the same three bounds hold over f:
`Gen.IsZKCPArg`, ZKCP/Gen.lean) is proved in Rom/ExitPriv.lean.

Notation:
  `m`: `OracleCoding S lam`, with the fields `blocks : S.ι → ℕ`,
    `rng : ∀ o, S.Rng o ≃ (Fin (blocks o) → Fin lam → Bool)`,
    `code : (o : S.ι) → S.Dom o → Fin (blocks o) → List Bool` and
    `inv : List Bool → (Σ o, S.Dom o × Fin (blocks o))`, with `inv_code`, `code_inv`
  `rom lam` (Rom/OSpec.lean): the model of ZKCP/Defs.lean: one oracle {0,1}* → {0,1}^lam
  `Gen.`: the namespace `ZKCP.Gen` of ZKCP/Gen.lean
  `Gen.IsZKCPArg R A B α ε ζ` (ZKCP/Gen.lean): the fields
    `completeness : HasCompletenessError R A B α`, `indexBinding : HasIndexBinding R A ε`,
    `indexPrivacy : HasIndexPrivacy R A B ζ`; the three bounds: α, ε, ζ
  `B`: `ℕ`: the bound on the length of a batch (doc comment of `Gen.Arg`, ZKCP/Gen.lean)
  `ε`: `ℕ → ℕ → ℝ≥0∞`: in `Gen.HasIndexBindingWith R A E ε` (ZKCP/Gen.lean) it stands as `ε tC tP`,
    with `Ct.QueryBound tC` and `∀ st, (Pt st).QueryBound tP`; `Ct : OComp S (IVK × St)`,
    `Pt : St → OComp S (X × Pf)`
  `ζ`: `ℕ → ℕ → ℝ≥0∞`: in `Gen.PrivacyFor R A Sim ζ i Z` (ZKCP/Gen.lean) it stands as `ζ tV N`, with
    `∀ ivk, (Vt ivk).QueryBound tV`; N counts batches
-/
import Rom.OComp
import ZKCP.Gen

namespace Rom
open ZKCP
open scoped ENNReal

structure OracleCoding (S : OSpec) (lam : ℕ) where
  blocks : S.ι → ℕ
  rng : ∀ o, S.Rng o ≃ (Fin (blocks o) → Fin lam → Bool)
  code : (o : S.ι) → S.Dom o → Fin (blocks o) → List Bool
  /-- Every bit string is the encoding of exactly one point: an oracle, a query and the index of a
  hash block of the answer, so every query of an adversary to f belongs to a typed query. (An
  auxiliary oracle on bit strings, `ON.other` of Compile/Oracles.lean and of
  Compile/Batch/Oracles.lean, makes the encoding onto; the scheme with fresh coins never queries it,
  the schemes with a seed derive their coins from it.) The inverse is data, so that the extractor
  and the simulator over f use no choice either. -/
  inv : List Bool → (Σ o, S.Dom o × Fin (blocks o))
  inv_code : ∀ x : (Σ o, S.Dom o × Fin (blocks o)), inv (code x.1 x.2.1 x.2.2) = x
  code_inv : ∀ s : List Bool, code (inv s).1 (inv s).2.1 (inv s).2.2 = s

theorem OracleCoding.bij {S : OSpec} {lam : ℕ} (m : OracleCoding S lam) :
    Function.Bijective fun x : (Σ o, S.Dom o × Fin (m.blocks o)) => m.code x.1 x.2.1 x.2.2 :=
  ⟨fun a b h => by rw [← m.inv_code a, ← m.inv_code b]; exact congrArg m.inv h,
    fun s => ⟨m.inv s, m.code_inv s⟩⟩

theorem OracleCoding.inj {S : OSpec} {lam : ℕ} (m : OracleCoding S lam) :
    Function.Injective fun x : (Σ o, S.Dom o × Fin (m.blocks o)) => m.code x.1 x.2.1 x.2.2 :=
  m.bij.injective

/-- query f at n bit strings, one after the other -/
def askAll (lam : ℕ) : (n : ℕ) → (Fin n → List Bool) → OComp (rom lam) (Fin n → Fin lam → Bool)
  | 0, _ => .pure fun i => i.elim0
  | n + 1, g => .query (S := rom lam) () (g 0) fun r =>
      (askAll lam n fun i => g i.succ).bind fun rest =>
        .pure (Fin.cons (α := fun _ => Fin lam → Bool) r rest)

variable {S : OSpec} {lam : ℕ} {α : Type}

/-- the same algorithm over f -/
def OComp.overOne (m : OracleCoding S lam) : OComp S α → OComp (rom lam) α
  | .pure a => .pure a
  | .sample n k => .sample n fun r => (k r).overOne m
  | .query o q k =>
    (askAll lam (m.blocks o) (m.code o q)).bind fun bs => (k ((m.rng o).symm bs)).overOne m

def schemeOverOneHashFunction {I X W IVK ISK Pf : Type} (m : OracleCoding S lam) (A : Gen.Arg S I X W IVK ISK Pf) :
    Gen.Arg (rom lam) I X W IVK ISK Pf where
  C := fun i => (A.C i).overOne m
  P := fun k b => (A.P k b).overOne m
  V := fun v x π => (A.V v x π).overOne m

/-- the entries of a trace at oracles whose answer is one hash block -/
def single (m : OracleCoding S lam) (tr : Trace S) : Trace S := tr.filter fun e => decide (m.blocks e.1 = 1)

/-- The extractor reads only entries at oracles whose answer is one hash block. Over f a committer
may query only some hash blocks of an answer, and an extractor that reads one which the committer
never queried has no counterpart. Without this condition the statement below is false (argued, not
proved): let ivk be hash block 0 of the answer at q, and the index hash block 1. An extractor that
reads only Merkle oracles, whose answers are one hash block, meets the condition. -/
def LocalTo {I X W IVK Pf : Type} (E : Gen.Extractor S I X W IVK Pf) (m : OracleCoding S lam) : Prop :=
  (∀ v tr, E.Ei v tr = E.Ei v (single m tr)) ∧
  (∀ v tr x π tr', E.Ew v tr x π tr' = E.Ew v (single m tr) x π (single m tr'))

/-- The statement: if the extractor meets `LocalTo`, the same three bounds hold over f; the numbers
of queries now count queries to f. -/
def Spec.family : Prop :=
  ∀ (S : OSpec) (lam : ℕ) (m : OracleCoding S lam) (I X W PP IVK ISK Pf : Type)
      (R : Gen.RelPair I X W PP) (A : Gen.Arg S I X W IVK ISK Pf) (B : ℕ)
      (E : Gen.Extractor S I X W IVK Pf) (α : ℝ≥0∞) (ε ζ : ℕ → ℕ → ℝ≥0∞),
    LocalTo E m → Gen.HasCompletenessError R A B α → Gen.HasIndexBindingWith R A E ε →
    Gen.HasIndexPrivacy R A B ζ → Gen.IsZKCPArg R (schemeOverOneHashFunction m A) B α ε ζ

end Rom
