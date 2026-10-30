-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Spec.lean: definitions (words of this library: lean/GLOSSARY.md): `mapSlots`, `relPair`,
`Params.leaves` (`Params`, Compile/Star.lean), `nLeaves`, `binTail`, `Budget`, `RunsIn`, `Sess`,
`sess`, `PCall`. No other file reads `nLeaves` or `PCall`.
-/
import Compile.Star
import ZKCP.Gen

noncomputable section

namespace Compile
open Iop Rom Prob ZKCP
open scoped ENNReal

variable {I X : Type} {lam : ℕ}

/-! ## Slots and relations -/

def mapSlots {S : OSpec} {β Pf : Type} (g : β → OComp S Pf) :
    (b : List β) → OComp S (Gen.Slots Pf b)
  | [] => pure ⟨[], rfl⟩
  | a :: t =>
    (g a).bind fun π => (mapSlots g t).bind fun r => pure ⟨π :: r.val, by simp [r.property]⟩

def relPair (Ryes Rno : I → X → Prop) (sub : ∀ i x, Ryes i x → Rno i x) :
    Gen.RelPair I X Unit Unit :=
  ⟨fun i x _ => Ryes i x, fun i x _ => Rno i x, fun i x _ => sub i x, fun _ => ()⟩

/-! ## Counts and bounds -/

def Params.leaves (p : Params) : ℕ := p.M + 1

/-- leaves of all trees of one execution -/
def nLeaves {K : ℕ} : (s : Shape) → WireS lam K s → ℕ
  | [], _ => 0
  | _ :: s, (w, W) => 2 ^ w.depth + nLeaves s W

variable (p : Params)

/-- Pr[Bin(n, 1/m) > s], as an exact finite sum -/
def binTail (n m s : ℕ) : ℝ≥0∞ :=
  ∑ j ∈ Finset.Icc (s + 1) n, (n.choose j : ℝ≥0∞) * ((m - 1 : ℕ) : ℝ≥0∞) ^ (n - j) / (m : ℝ≥0∞) ^ n

/-- the budget of every encoding: the first (Test and M + 1 links) and each copy (one link and s1
sessions) -/
def Budget (N : LH.Nums) : Prop := N.qT + p.leaves * N.qpar ≤ N.b ∧ N.qch + p.s1 * N.qon ≤ N.b

/-! ## Runs within a trace -/

/-- a coin-free algorithm runs to the result a with all its queries and answers taken from the
trace -/
inductive RunsIn {S : OSpec} {α : Type} (tr : Trace S) : OComp S α → α → Prop
  | pure (a : α) : RunsIn tr (.pure a) a
  | query (o : S.ι) (q : S.Dom o) (k : S.Rng o → OComp S α) (r : S.Rng o) (a : α) :
      (⟨o, q, r⟩ : QA S) ∈ tr → RunsIn tr (k r) a → RunsIn tr (.query o q k) a

/-! ## Sessions -/

/-- an execution as the game returns it: the verifier randomness and the output (a disclosed view,
or `none`) -/
abbrev Sess {Y : Type} {E : ExtSpec} (Q : InteractiveOracleProof Y E) : Type := Rho Q.shape × Option (DView Q)

def sess {Y : Type} {E : ExtSpec} {Q : InteractiveOracleProof Y E} {Wt : Type} (H : Honest Q Wt) (w : Wt) (y : Y) :
    PMF (Sess Q) :=
  (unif (Rho Q.shape)).bind fun ρ => (H.output w y ρ).map fun o => (ρ, o)

/-! ## Calls to a challenger -/

/-- Calls of the privacy adversary to a challenger: setup = "give me ivk" (once, first); a
session on x whose proof is shown;
a session on x whose proof is not shown (a slot of a batch that is not the adversary's own:
Gen.Batch).
The environment is folded into the adversary (it is chosen after i, and may know i). -/
inductive PCall (X : Type)
  | setup
  | shown (x : X)
  | hidden (x : X)

end Compile
