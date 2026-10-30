-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/AdaptiveExit.lean: adaptive completeness, from the family of oracles to ZKCP/Adaptive.lean.

`Compile.Adaptive.HasAdaptiveCompleteness` (Compile/SpecAdaptive.lean) is about any argument system
over any family of oracles. It says: for each index i and each environment that makes at most t
queries and chooses only pairs in R.yes i, the probability that V rejects at least one of the first
N honest proofs is at most α t N.
  `adaptive_overOne`  family → one hash function f, for any query encoding `m : OracleCoding S lam`
                      (Rom/Family.lean): the same bound for the scheme over f; query bounds now
                      count queries to f (proved)
  `adaptive_of_gen`   one hash function, R_yes = R_no, for a scheme `toGen A` →
                      `ZKCP.HasAdaptiveCompletenessError` of ZKCP/Adaptive.lean, with the same bound
                      (proved)

Notation: R_yes, R_no: the fields `yes`, `no` of a `ZKCP.Gen.RelPair` (ZKCP/Gen.lean): two indexed
relations R_yes ⊆ R_no; `toPair R` (ZKCP/SpecialDefs.lean), a `RelPair`: R_yes = R_no = R; `toGen A`
(the same file): a scheme of ZKCP/Defs.lean in the form of ZKCP/Gen.lean, over `rom lam`
(Rom/OSpec.lean): one oracle {0,1}* → {0,1}^lam; `schemeOverOneHashFunction m A` (Rom/Family.lean): C, P, V of A,
each `.overOne m`: the same algorithm over f.
-/
import Compile.SpecAdaptive
import ZKCP.Adaptive
import ZKCP.Special
import Rom.ExitBind

noncomputable section

namespace Compile.Adaptive
open Rom Prob
open scoped ENNReal

/-! ## Family → one hash function -/

section OverOne
variable {S : OSpec} {lam : ℕ} {I X Wn PP IVK ISK Pf : Type}

/-- The environment over the family: a query at a string becomes the typed query that it encodes,
and of its answer the encoded block is kept. -/
def downE (m : OracleCoding S lam) : CEnv (rom lam) X Wn Pf → CEnv S X Wn Pf
  | .halt => .halt
  | .sample n k => .sample n fun r => downE m (k r)
  | .query _ s k => .query (m.dec s).1 (m.dec s).2.1 fun r => downE m (k (m.blk r (m.dec s).2.2))
  | .session x w k => .session x w fun π b => downE m (k π b)

theorem queryBound_downE (m : OracleCoding S lam) (E : CEnv (rom lam) X Wn Pf) :
    ∀ t, E.QueryBound t → (downE m E).QueryBound t := by
  induction E with
  | halt => intro t _; trivial
  | sample n k ih => exact fun t h r => ih r t (h r)
  | query u s k ih =>
    intro t h
    cases t with
    | zero => exact h
    | succ t => exact fun r => ih _ t (h _)
  | session x w k ih => exact fun t h π b => ih π b t (h π b)

theorem valid_downE (m : OracleCoding S lam) (ok : X → Wn → Prop) (E : CEnv (rom lam) X Wn Pf) :
    E.Valid ok → (downE m E).Valid ok := by
  induction E with
  | halt => intro _; trivial
  | sample n k ih => exact fun h r => ih r (h r)
  | query u s k ih => exact fun h r => ih _ (h _)
  | session x w k ih => exact fun h => ⟨h.1, fun π b => ih π b (h.2 π b)⟩

private theorem overOneArg_C (m : OracleCoding S lam) (A : ZKCP.Gen.Arg S I X Wn IVK ISK Pf) (i : I) :
    (schemeOverOneHashFunction m A).C i = (A.C i).overOne m := rfl
private theorem overOneArg_P
    (m : OracleCoding S lam) (A : ZKCP.Gen.Arg S I X Wn IVK ISK Pf) (k : ISK) (b : List (X × Wn)) :
    (schemeOverOneHashFunction m A).P k b = (A.P k b).overOne m := rfl
private theorem overOneArg_V
    (m : OracleCoding S lam) (A : ZKCP.Gen.Arg S I X Wn IVK ISK Pf) (v : IVK) (x : X) (π : Pf) :
    (schemeOverOneHashFunction m A).V v x π = (A.V v x π).overOne m := rfl

private theorem runEager_overOne_glue {α : Type} (m : OracleCoding S lam) (F : Fam S) (c : OComp S α) :
    (c.overOne m).runEager (glue m F) = c.runEager F := by
  rw [runEager_overOne, readBlocks_glue]

/-- With the oracles fixed, the sessions over the hash function are the sessions over the family. -/
theorem loop_glue (m : OracleCoding S lam) (A : ZKCP.Gen.Arg S I X Wn IVK ISK Pf) (F : Fam S) (ivk : IVK)
    (isk : ISK) (E : CEnv (rom lam) X Wn Pf) :
    ∀ n : ℕ, (loop (schemeOverOneHashFunction m A) ivk isk E n).runEager (glue m F) =
      (loop A ivk isk (downE m E) n).runEager F := by
  induction E with
  | halt => intro n; rfl
  | sample n' k ih => intro n; simp only [loop, downE, OComp.runEager, ih]
  | query u s k ih =>
    intro n
    cases u
    simp only [loop, downE, OComp.runEager, ih]
    rfl
  | session x w k ih =>
    intro n
    cases n with
    | zero => rfl
    | succ n =>
      simp only [loop, downE, OComp.runEager_bind, overOneArg_P, overOneArg_V,
        runEager_overOne_glue, ih]
      rfl

theorem exp_glue (m : OracleCoding S lam) (A : ZKCP.Gen.Arg S I X Wn IVK ISK Pf) (F : Fam S)
    (E : IVK → CEnv (rom lam) X Wn Pf) (i : I) (N : ℕ) :
    (exp (schemeOverOneHashFunction m A) E i N).runEager (glue m F) =
      (exp A (fun ivk => downE m (E ivk)) i N).runEager F := by
  simp only [exp, OComp.runEager_bind, loop_glue, overOneArg_C, runEager_overOne_glue]

/-- Family → one hash function: if A has `HasAdaptiveCompleteness` with the bound α (`h`), then for
any query encoding m the scheme over one hash function, `schemeOverOneHashFunction m A`, has it with the same
bound. -/
theorem adaptive_overOne (m : OracleCoding S lam) (A : ZKCP.Gen.Arg S I X Wn IVK ISK Pf)
    (R : ZKCP.Gen.RelPair I X Wn PP) (α : ℕ → ℕ → ℝ≥0∞) (h : HasAdaptiveCompleteness A R α) :
    HasAdaptiveCompleteness (schemeOverOneHashFunction m A) R α := by
  intro i t N E hq hv
  refine le_trans (le_of_eq ?_)
    (h i t N (fun ivk => downE m (E ivk)) (fun ivk => queryBound_downE m _ t (hq ivk))
      fun ivk => valid_downE m _ _ (hv ivk))
  unfold Rom.Pr
  rw [lintegral_glue m (fun g => PrCoins g (exp (schemeOverOneHashFunction m A) E i N) {b | b = false})]
  · simp only [PrCoins, exp_glue]
  · simp only [PrCoins, exp_glue]
    exact measurable_PrCoins _ _

end OverOne

/-! ## One hash function, R_yes = R_no → ZKCP/Adaptive.lean -/

section ToLiteral
variable {lam : ℕ} {I X W PP IVK ISK Pf : Type}
open ZKCP.Special (toGen toPair proveAll)

/-- An environment of ZKCP/Adaptive.lean as a `Compile.Adaptive.CEnv`, constructor by
constructor. -/
def envTo : ZKCP.CEnv lam X W Pf → CEnv (rom lam) X W Pf
  | .halt => .halt
  | .query q k => .query () q fun r => envTo (k r)
  | .sample n k => .sample n fun r => envTo (k r)
  | .session x w k => .session x w fun π b => envTo (k π b)

theorem queryBound_envTo (E : ZKCP.CEnv lam X W Pf) :
    ∀ t, E.QueryBound t → (envTo E).QueryBound t := by
  induction E with
  | halt => intro t _; trivial
  | sample n k ih => exact fun t h r => ih r t (h r)
  | query q k ih =>
    intro t h
    cases t with
    | zero => exact h
    | succ t => exact fun r => ih r t (h r)
  | session x w k ih => exact fun t h π b => ih π b t (h π b)

theorem valid_envTo (ok : X → W → Prop) (E : ZKCP.CEnv lam X W Pf) :
    E.Valid ok → (envTo E).Valid ok := by
  induction E with
  | halt => intro _; trivial
  | sample n k ih => exact fun h r => ih r (h r)
  | query q k ih => exact fun h r => ih r (h r)
  | session x w k ih => exact fun h => ⟨h.1, fun π b => ih π b (h.2 π b)⟩

private theorem toGen_P (A : ZKCP.Arg lam I X W IVK ISK Pf) (isk : ISK) (b : List (X × W)) :
    (toGen A).P isk b = proveAll A isk b := rfl
private theorem toGen_V (A : ZKCP.Arg lam I X W IVK ISK Pf) (ivk : IVK) (x : X) (π : Pf) :
    (toGen A).V ivk x π = toRom (A.V ivk x π) := rfl
private theorem toGen_C (A : ZKCP.Arg lam I X W IVK ISK Pf) (i : I) :
    (toGen A).C i = toRom (A.C i) := rfl
private theorem one_single {β : Type} {a : β} (π : Pf) (h : [π].length = [a].length) :
    one (⟨[π], h⟩ : ZKCP.Gen.Slots Pf [a]) = π := rfl

theorem loop_toGen (A : ZKCP.Arg lam I X W IVK ISK Pf) (ivk : IVK)
    (isk : ISK) (E : ZKCP.CEnv lam X W Pf) :
    ∀ n : ℕ, loop (toGen A) ivk isk (envTo E) n = toRom (ZKCP.adaptiveLoop A ivk isk E n) := by
  induction E with
  | halt => intro n; rfl
  | sample n' k ih => intro n; simp only [envTo, loop, ZKCP.adaptiveLoop, toRom, ih]
  | query q k ih => intro n; simp only [envTo, loop, ZKCP.adaptiveLoop, toRom, ih]
  | session x w k ih =>
    intro n
    cases n with
    | zero => rfl
    | succ n =>
      simp only [envTo, loop, ZKCP.adaptiveLoop, toRom_bind, toRom_pure, toGen_P, toGen_V, proveAll,
        OComp.bind_assoc, OComp.bind, one_single, ih]
      rfl

/-- To ZKCP/Adaptive.lean, for `toGen A`: if `toGen A` has `HasAdaptiveCompleteness` at `toPair R`
with the bound α (`h`), then A has `ZKCP.HasAdaptiveCompletenessError` at R with the same bound. -/
theorem adaptive_of_gen (R : ZKCP.IndexedRelation I X W PP) (A : ZKCP.Arg lam I X W IVK ISK Pf)
    (α : ℕ → ℕ → ℝ≥0∞) (h : HasAdaptiveCompleteness (toGen A) (toPair R) α) :
    ZKCP.HasAdaptiveCompletenessError R A α := by
  intro i t N E hq hv
  have h1 := h i t N (fun ivk => envTo (E ivk))
    (fun ivk => queryBound_envTo _ t (hq ivk)) fun ivk => valid_envTo _ _ (hv ivk)
  have e : exp (toGen A) (fun ivk => envTo (E ivk)) i N = toRom (ZKCP.adaptiveExp A E i N) := by
    simp only [exp, ZKCP.adaptiveExp, toRom_bind, loop_toGen, toGen_C]
  rwa [e, Pr_toRom] at h1

end ToLiteral
end Compile.Adaptive

