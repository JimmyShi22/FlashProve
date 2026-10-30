-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/ViewKit.lean: helper lemmas for proofs of exact honest-verifier zero knowledge.

No particular protocol occurs. The definitions (the disclosed view `DView`, the honest prover's
output at the verifier randomness ρ, honest-verifier zero knowledge in the exact form) are in
Iop/InteractiveOracleProof.lean (words of this library: lean/GLOSSARY.md).

 1. The answers of the external strings (`extAns_congr`).
 2. The output at ρ, inside and outside the abort set (`Honest.withheld`): `Honest.output_of_mem`,
     `Honest.output_of_not_mem`.
 3. Over rounds whose oracles are strings, a transcript is given by ρ, the plain parts and all
     symbols (`Tr.ofParts`). A simulator uses this to write down a transcript from what a view
     shows, with fixed symbols elsewhere.
 4. The plain parts of a transcript for s ++ t (`Tr.plains_eq_of`).
 5. Probabilities of two simple sets of ρ (`prRho_empty`, `prRho_head_le`).
-/
import Iop.InteractiveOracleProof
import Iop.ShapeKit

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

/-! ## 1. The disclosed view (`extAns_congr`) -/

section View
variable {X : Type} {E : ExtSpec}


/-- The answers of the external strings depend on them only at the positions read. -/
theorem extAns_congr (Q : InteractiveOracleProof X E) (x : X) (ρ : Rho Q.shape) {y y' : E.Str}
    (h : ∀ p ∈ Q.extReads x ρ, E.rd y p = E.rd y' p) :
    Q.extAns x ρ y = Q.extAns x ρ y' := by
  funext p
  unfold InteractiveOracleProof.extAns
  by_cases hp : p ∈ Q.extReads x ρ
  · rw [if_pos hp, if_pos hp, h p hp]
  · rw [if_neg hp, if_neg hp]

/-! ## 2. The output at ρ -/

variable {Q : InteractiveOracleProof X E} {Wt : Type}

theorem Honest.output_of_mem
    (H : Honest Q Wt) {w : Wt} {x : X} {ρ : Rho Q.shape} (h : ρ ∈ H.withheld w x) :
    H.output w x ρ = PMF.pure none := if_pos h

theorem Honest.output_of_not_mem
    (H : Honest Q Wt) {w : Wt} {x : X} {ρ : Rho Q.shape} (h : ρ ∉ H.withheld w x) :
    H.output w x ρ =
      (unif H.Coin).map fun c => some (Q.dview x (H.ext w) ((H.strat w x c).run ρ).1) := if_neg h

end View

/-! ## 3. A transcript from its parts -/

/-- The fixed symbol at every position of rounds whose oracles are strings. -/
def Shape.IsPoint.zeroSym : {s : Shape} → s.IsPoint → (p : OPos s) → OSym s p
  | _ :: _, (h, _), .inl p => h.zero p
  | _ :: _, (_, hs), .inr p => zeroSym hs p

namespace Tr

/-- The transcript with the verifier's randomness ρ, the plain parts pl and the symbols f. -/
def ofParts : {s : Shape} → s.IsPoint → Rho s → Plains s → ((p : OPos s) → OSym s p) → Tr s
  | [], _, _, _, _ => ()
  | _ :: _, (h, hs), (c, ρ), (pl, pls), f =>
    ((h.ofSyms fun p => f (.inl p), pl), c, ofParts hs ρ pls fun p => f (.inr p))

theorem rho_ofParts :
    ∀ {s : Shape} (h : s.IsPoint) (ρ : Rho s) (pl : Plains s) (f : (p : OPos s) → OSym s p),
      (ofParts h ρ pl f).rho = ρ
  | [], _, (), _, _ => rfl
  | _ :: _, (_, hs), (c, ρ), (_, pls), f => by
      show (c, (ofParts hs ρ pls fun p => f (.inr p)).rho) = (c, ρ)
      rw [rho_ofParts hs ρ pls]

theorem plains_ofParts :
    ∀ {s : Shape} (h : s.IsPoint) (ρ : Rho s) (pl : Plains s) (f : (p : OPos s) → OSym s p),
      (ofParts h ρ pl f).plains = pl
  | [], _, _, (), _ => rfl
  | _ :: _, (_, hs), (_, ρ), (pl, pls), f => by
      show (pl, (ofParts hs ρ pls fun p => f (.inr p)).plains) = (pl, pls)
      rw [plains_ofParts hs ρ pls]

theorem read_ofParts :
    ∀ {s : Shape} (h : s.IsPoint) (ρ : Rho s) (pl : Plains s)
        (f : (p : OPos s) → OSym s p) (p : OPos s),
      (ofParts h ρ pl f).read p = f p
  | _ :: _, (h, _), (_, _), (_, _), f, .inl p => h.rd_ofSyms (fun p => f (.inl p)) p
  | _ :: _, (_, hs), (_, ρ), (_, pls), f, .inr p => read_ofParts hs ρ pls (fun p => f (.inr p)) p

/-! ## 4. The plain parts for s ++ t -/

/-- Two transcripts for s ++ t have the same plain parts if their two parts have. -/
theorem plains_eq_of {s t : Shape} (τ τ' : Tr (s ++ t)) (h1 : (fst τ).plains = (fst τ').plains)
    (h2 : (snd (s := s) τ).plains = (snd (s := s) τ').plains) : τ.plains = τ'.plains := by
  rw [← Plains.app_fst_snd τ.plains, ← Plains.app_fst_snd τ'.plains, ← plains_fst, ← plains_snd,
    ← plains_fst, ← plains_snd, h1, h2]

end Tr

/-! ## 5. Probabilities of sets of ρ -/

/-- A set without elements has probability 0. -/
theorem prRho_empty {s : Shape} (S : Set (Rho s)) (h : ∀ ρ, ρ ∉ S) : prRho S ≤ 0 :=
  le_of_eq (pr_eq_zero_of_forall_not_mem _ fun ρ _ => h ρ)

/-- The probability of an event on the first challenge only: a bound. -/
theorem prRho_head_le (r : Round) (s : Shape) (P : r.Chal → Prop) (k : ℕ) (h : cnt P ≤ k) :
    prRho (s := r :: s) {ρ | P (show r.Chal × Rho s from ρ).1} ≤
      (k : ℝ≥0∞) / Fintype.card r.Chal := by
  have h1 : pr (unif (r.Chal × Rho s)) (Prod.fst ⁻¹' {c | P c}) = pr (unif r.Chal) {c | P c} := by
    rw [← pr_map, map_fst_unif]
  exact le_of_eq_of_le h1 (pr_unif_le_of_cnt_le h)

end Iop
