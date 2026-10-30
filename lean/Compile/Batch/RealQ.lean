-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/RealQ.lean: what commutes with `realQ` (Compile/Batch/Oracles.lean: queries to the
ghost names `fbw` become queries to `fb`). Small lemmas, by induction on the algorithm (words of
this library: lean/GLOSSARY.md).

  `realQ_pure`, `realQ_sample`, `realQ_fbw`, `realQ_query`, `realQ_bind`
      How `realQ` unfolds; it commutes with sequential composition.
  `eraseR c vs`
      What a scheme runs of a program with tokens: realQ (erase c vs); `eraseR_bind`,
      `eraseR_pure`, `eraseR_sample`.
  `realQ_blocks`, `realQ_derive`
      `realQ` commutes with making every sample from small ones (`blocks`) and with deriving the
      coins through an oracle that is no ghost name (`derive`).
  `queryBound_realQ`, `avoids_realQ`, `wt_realQ`
      A bound on the queries on every path still holds; an oracle other than a Fiat-Shamir oracle
      that is never queried is still never queried; the samples have the same weight.
-/
import Compile.Batch.TokTree
import Compile.Batch.Verifier
import Compile.SeedKit
import Compile.EraseKit
import Rom.Blocks
import Rom.SpecDerive
noncomputable section -- Lean tags what it cannot compile

namespace Compile.Batch
open Iop Rom

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} {α β : Type}

theorem realQ_pure (a : α) : realQ (OComp.pure a : OComp (spec lam K L) α) = .pure a := rfl
theorem realQ_sample (n : ℕ) (k : Fin (n + 1) → OComp (spec lam K L) α) :
    realQ (.sample n k) = .sample n fun r => realQ (k r) := rfl
theorem realQ_fbw (t : Tag) (j : ℕ) (q : (spec lam K L).Dom (.fbw t j))
    (k : (spec lam K L).Rng (.fbw t j) → OComp (spec lam K L) α) :
    realQ (.query (.fbw t j) q k) = .query (S := spec lam K L) (.fb t) q fun r => realQ (k r) := rfl

/-- a query to an oracle that is no ghost name is kept -/
theorem realQ_query (o : OracleName) (ho : ∀ t j, o ≠ .fbw t j) (q : (spec lam K L).Dom o)
    (k : (spec lam K L).Rng o → OComp (spec lam K L) α) :
    realQ (.query o q k) = .query o q fun r => realQ (k r) := by
  cases o with
  | fbw t j => exact absurd rfl (ho t j)
  | _ => rfl

theorem realQ_bind (c : OComp (spec lam K L) α) (g : α → OComp (spec lam K L) β) :
    realQ (c.bind g) = (realQ c).bind fun a => realQ (g a) := by
  induction c with
  | pure a => rfl
  | sample n k ih => exact congrArg (OComp.sample n) (funext ih)
  | query o q k ih =>
    cases o with
    | fbw t j => exact congrArg (OComp.query (S := spec lam K L) (.fb t) q) (funext ih)
    | leaf => exact congrArg (OComp.query (S := spec lam K L) .leaf q) (funext ih)
    | node => exact congrArg (OComp.query (S := spec lam K L) .node q) (funext ih)
    | rleaf => exact congrArg (OComp.query (S := spec lam K L) .rleaf q) (funext ih)
    | rnode => exact congrArg (OComp.query (S := spec lam K L) .rnode q) (funext ih)
    | fb t => exact congrArg (OComp.query (S := spec lam K L) (.fb t) q) (funext ih)
    | g t => exact congrArg (OComp.query (S := spec lam K L) (.g t) q) (funext ih)
    | ann => exact congrArg (OComp.query (S := spec lam K L) .ann q) (funext ih)
    | other => exact congrArg (OComp.query (S := spec lam K L) .other q) (funext ih)

theorem queryBound_realQ :
    ∀ (c : OComp (spec lam K L) α) (n : ℕ), c.QueryBound n → (realQ c).QueryBound n := by
  intro c
  induction c with
  | pure a => intro n _; trivial
  | sample m k ih => intro n h r; exact ih r n (h r)
  | query o q k ih =>
    intro n h
    cases n with
    | zero => exact absurd h (by simp [OComp.QueryBound])
    | succ n =>
      cases o <;> exact fun r => ih r n (h r)

/-- an oracle that is no Fiat-Shamir oracle and is never queried is still never queried -/
theorem avoids_realQ (o₀ : OracleName) (h₀ : ∀ t, o₀ ≠ .fb t) :
    ∀ c : OComp (spec lam K L) α, c.Avoids o₀ → (realQ c).Avoids o₀ := by
  intro c
  induction c with
  | pure a => intro _; trivial
  | sample m k ih => intro h r; exact ih r (h r)
  | query o q k ih =>
    intro h
    cases o with
    | fbw t j => exact ⟨fun e => h₀ t e.symm, fun r => ih r (h.2 r)⟩
    | _ => exact ⟨h.1, fun r => ih r (h.2 r)⟩

theorem wt_realQ {μ : ℕ → ℕ} {n : ℕ} {c : OComp (spec lam K L) α} (h : Compile.Seed.Wt μ n c) :
    Compile.Seed.Wt μ n (realQ c) := by
  induction h with
  | pure a => exact .pure a
  | sample m _ ih => exact .sample m ih
  | query o q _ ih =>
    cases o with
    | fbw t j => exact .query (S := spec lam K L) (.fb t) q ih
    | _ => exact .query _ q ih

/-! ## The erased program with the ghost names written back (`realQ`) -/

/-- What a scheme runs of a program with tokens: its erasure with the ghost names written back
(`realQ`) -/
def eraseR (c : St lam K L α) (vs : List Bits) : TypedOracleComputation lam K L (α × List Bits) :=
  realQ (erase c vs)

theorem eraseR_bind (c : St lam K L α) (g : α → St lam K L β) (vs : List Bits) :
    eraseR (c.bind g) vs = (eraseR c vs).bind fun o => eraseR (g o.1) o.2 := by
  unfold eraseR
  rw [erase_bind, realQ_bind]

theorem eraseR_pure (a : α) (vs : List Bits) :
    eraseR (Step.pure a : St lam K L α) vs = .pure (a, vs) := rfl

theorem eraseR_sample (n : ℕ) (k : Fin (n + 1) → St lam K L α) (vs : List Bits) :
    eraseR (Step.sample n k) vs = .sample n fun r => eraseR (k r) vs := rfl

/-! ## `realQ` and the two transformations of samples -/

theorem realQ_tossN (w : ℕ) :
    ∀ (m : ℕ) (f : (Fin m → Fin (w + 1)) → OComp (spec lam K L) α),
      realQ (OComp.tossN w m f) = OComp.tossN w m fun v => realQ (f v)
  | 0, _ => rfl
  | m + 1, f => by
      show OComp.sample w (fun r => realQ (OComp.tossN w m fun v => f (Fin.cons r v))) =
        OComp.sample w fun r => OComp.tossN w m fun v => realQ (f (Fin.cons r v))
      exact congrArg _ (funext fun r => realQ_tossN w m _)

/-- every sample made from small ones: before or after the ghost names are written back -/
theorem realQ_blocks (bk : CoinPlan) (c : OComp (spec lam K L) α) :
    realQ (c.blocks bk) = (realQ c).blocks bk := by
  induction c with
  | pure a => rfl
  | sample n k ih =>
    show realQ (OComp.tossN bk.w (bk.m n) fun v => (k (bk.φ n v)).blocks bk) =
      OComp.tossN bk.w (bk.m n) fun v => (realQ (k (bk.φ n v))).blocks bk
    rw [realQ_tossN]
    exact congrArg _ (funext fun v => ih _)
  | query o q k ih =>
    cases o <;> exact congrArg _ (funext ih)

/-- the coins derived through an oracle that is no ghost name: before or after the ghost names are
written back -/
theorem realQ_derive (σ : SeedOracle (spec lam K L)) (hσ : ∀ t j, σ.o ≠ OracleName.fbw t j)
    (s : Fin (σ.sd + 1)) (c : OComp (spec lam K L) α) :
    ∀ j, realQ (c.derive σ s j) = (realQ c).derive σ s j := by
  induction c with
  | pure a => intro j; rfl
  | sample n k ih =>
    intro j
    show realQ (OComp.query σ.o (σ.pt s j) fun d => (k (σ.ψ n d)).derive σ s (j + 1)) =
      OComp.query σ.o (σ.pt s j) fun d => (realQ (k (σ.ψ n d))).derive σ s (j + 1)
    rw [realQ_query σ.o hσ]
    exact congrArg _ (funext fun d => ih _ _)
  | query o q k ih =>
    intro j
    cases o <;> exact congrArg _ (funext fun r => ih r j)

end Compile.Batch
