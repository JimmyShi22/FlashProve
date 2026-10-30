-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/SeedShape.lean: a property of token programs: the samples have a total weight that does not
depend on the path, and one given oracle is never queried (tokens: `Step`, Rom/Defer.lean; stores:
`erase`, Compile/Star.lean; words of this library: lean/GLOSSARY.md).

In Rom/SpecDerive.lean the label of a sample is its number in the run. A prover that derives only a
part of the committer's run again must know the number of the first sample of that part. So the
number of samples of every earlier part must be the same on all paths.

  `Sh o₀ μ n c`          Every path of the token program c has samples (a `sample`, or a fresh
                         token) of the total weight n, where a sample with m + 1 outcomes weighs μ
                         m, and c never queries the oracle o₀. Rules for the constructors and for
                         sequences. With μ = 1 the weight is the number of samples; with the weights
                         of Rom/Blocks.lean it is the number of small samples.
  `Sh.wt`, `Sh.avoids`   The same for the erased program, on every store.
  `cLeaves`, `cTree`     Numbers of salted leaves.

The lemmas for the programs of the compiled prover, with the auxiliary oracle (`OracleName.other`,
Compile/Batch/Oracles.lean) as o₀, are in Compile/Batch/SeedShape.lean (`sh_slotLo`, `sh_chainT`,
`sh_proveB`).
-/
import Compile.SeedKit

open Rom Iop

namespace Compile
namespace Seed

variable {S : OSpec} {sp : Split S} {α β : Type}

/-- every path has uniform samples of the total weight n, and the oracle o₀ is never queried -/
inductive Sh (o₀ : S.ι) (μ : ℕ → ℕ) : ℕ → Step S sp α → Prop
  | pure (a : α) : Sh o₀ μ 0 (.pure a)
  | sample {n : ℕ} (m : ℕ) {k : Fin (m + 1) → Step S sp α} (h : ∀ r, Sh o₀ μ n (k r)) :
      Sh o₀ μ (n + μ m) (.sample m k)
  | plain {n : ℕ} (o : S.ι) (ho : o ≠ o₀) (q : S.Dom o)
      {k : S.Rng o → Step S sp α} (h : ∀ r, Sh o₀ μ n (k r)) : Sh o₀ μ n (.plain o q k)
  | fresh {n : ℕ} (ℓ : ℕ) {k : Tok → Step S sp α} (h : ∀ t, Sh o₀ μ n (k t)) :
      Sh o₀ μ (n + μ (2 ^ ℓ - 1)) (.fresh ℓ k)
  | marked {n : ℕ} (o : S.ι) (ho : o ≠ o₀) (t : Tok) (us : List Tok)
      (pt : Bits → List Bits → S.Dom o) (inj : ∀ vs, Function.Injective fun v => pt v vs)
      {k : sp.Vis o → Tok → Step S sp α} (h : ∀ v t', Sh o₀ μ n (k v t')) :
      Sh o₀ μ n (.marked o t us pt inj k)
  | reveal {n : ℕ} (ts : List Tok) {k : List Bits → Step S sp α} (h : ∀ w, Sh o₀ μ n (k w)) :
      Sh o₀ μ n (.reveal ts k)

variable {o₀ : S.ι} {μ : ℕ → ℕ}

theorem Sh.cast {n m : ℕ} {c : Step S sp α} (h : Sh o₀ μ n c) (e : n = m) : Sh o₀ μ m c := e ▸ h

theorem Sh.bind {n m : ℕ} {c : Step S sp α} {g : α → Step S sp β}
    (hc : Sh o₀ μ n c) (hg : ∀ a, Sh o₀ μ m (g a)) : Sh o₀ μ (n + m) (c.bind g) := by
  induction hc with
  | pure a => simpa [Step.bind] using hg a
  | @sample n m' k _ ih => exact (Sh.sample m' ih).cast (by omega)
  | plain o ho q _ ih => exact .plain o ho q ih
  | @fresh n ℓ k _ ih => exact (Sh.fresh ℓ ih).cast (by omega)
  | marked o ho t us pt inj _ ih => exact .marked o ho t us pt inj ih
  | reveal ts _ ih => exact .reveal ts ih

/-- a sequence whose second part has the weight 0 -/
theorem Sh.bind0 {n : ℕ} {c : Step S sp α} {g : α → Step S sp β}
    (hc : Sh o₀ μ n c) (hg : ∀ a, Sh o₀ μ 0 (g a)) : Sh o₀ μ n (c.bind g) := hc.bind hg

theorem Sh.wt {n : ℕ} {c : Step S sp α} (h : Sh o₀ μ n c) : ∀ vs, Wt μ n (erase c vs) := by
  induction h with
  | pure a => exact fun vs => .pure _
  | sample m _ ih => exact fun vs => .sample m fun r => ih r vs
  | plain o _ q _ ih => exact fun vs => .query o q fun r => ih r vs
  | fresh ℓ _ ih => exact fun vs => .sample _ fun r => ih _ _
  | marked o _ t us pt inj _ ih => exact fun vs => .query o _ fun r => ih _ _ _
  | reveal ts _ ih => exact fun vs => ih _ vs

theorem Sh.avoids {n : ℕ} {c : Step S sp α} (h : Sh o₀ μ n c) : ∀ vs, (erase c vs).Avoids o₀ := by
  induction h with
  | pure a => exact fun vs => trivial
  | sample m _ ih => exact fun vs r => ih r vs
  | plain o ho q _ ih => exact fun vs => ⟨ho, fun r => ih r vs⟩
  | fresh ℓ _ ih => exact fun vs r => ih _ _
  | marked o ho t us pt inj _ ih => exact fun vs => ⟨ho, fun r => ih _ _ _⟩
  | reveal ts _ ih => exact fun vs => ih _ vs

/-! ## Numbers of salted leaves -/

section Bcs
variable {I X : Type} {lam K : ℕ}

variable (μ : ℕ → ℕ)

/-- the salted leaves of a list -/
def cLeaves {B : Type} (l : List (B × Bool)) : ℕ := l.countP fun x => x.2

/-- the salted leaves of a tree -/
def cTree {B : Type} (d : ℕ) (leaf : ℕ → B × Bool) : ℕ := cLeaves ((List.range (2 ^ d)).map leaf)

end Bcs

end Seed
end Compile
