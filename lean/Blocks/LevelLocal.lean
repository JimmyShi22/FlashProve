-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/LevelLocal.lean: lemmas on the levels (Blocks/LevelDef.lean). (Words of this library:
lean/GLOSSARY.md.) The rounds of a sumcheck and the round of θ have no oracles, so transcripts with
the same verifier messages and plain parts agree there. The claim of the next level depends on the
word only at the positions sampled (`nextClaim_congr`).
-/
import Blocks.Local
import Blocks.Block

set_option autoImplicit false

namespace Blocks
namespace LevelLocal
open Iop Prob

variable {F : Type} [Field F] (a : LevSpec F) {E : Type} [Field E] [Fintype E]
  [DecidableEq E] [Algebra F E]

omit [Field F] [Fintype E] [Algebra F E] in
omit [DecidableEq E] in
theorem foldW_congr {w w' : a.Word E} {p : Fin a.code.n} (h : w p = w' p) (ζ : ℕ → E) :
    a.foldW w ζ p = a.foldW w' ζ p := by
  unfold LevSpec.foldW
  rw [h]

omit [Field F] [Fintype E] [Algebra F E] in
omit [DecidableEq E] in
theorem combW_congr {w w' : a.Word E} {p : Fin a.code.n} (h : w p = w' p) (θ : Fin a.rows → E) :
    a.combW w θ p = a.combW w' θ p := by
  unfold LevSpec.combW
  rw [h]

omit [Fintype E] in
omit [DecidableEq E] in
/-- The claim of the next level depends on the word only at the positions sampled. -/
theorem nextClaim_congr (b : LevSpec F) (c : a.Claim E) {w w' : a.Word E} (ζ s0 s2 : ℕ → E)
    (θ : Fin a.rows → E) (ch : (Fin a.q → Fin a.code.n) × E × E × (Fin a.q → E))
    (h : ∀ i, w (ch.1 i) = w' (ch.1 i)) :
    a.nextClaim b c w ζ s0 s2 θ ch = a.nextClaim b c w' ζ s0 s2 θ ch := by
  unfold LevSpec.nextClaim
  congr 2
  exact Finset.sum_congr rfl fun i _ => by rw [foldW_congr a (h i), combW_congr a (h i)]

variable (E) in
omit [Field F] [Algebra F E] in
omit [DecidableEq E] in
theorem noOrc_sc (n : ℕ) : NoOrc (List.replicate n (LinSh.rSC E)) :=
  NoOrc.replicate (inferInstanceAs (Subsingleton Unit)) n

omit [Field F] [Algebra F E] in
omit [DecidableEq E] in
/-- The rounds of the sumcheck agree, under `hρ`, `hπ`. -/
theorem fst_eq {n : ℕ} {t : Shape} {τ τ' : Tr (List.replicate n (LinSh.rSC E) ++ t)}
    (hρ : τ.rho = τ'.rho) (hπ : τ.plains = τ'.plains) : Tr.fst τ = Tr.fst τ' :=
  Tr.eq_of_noOrc (noOrc_sc E n)
    (by rw [Tr.rho_fst, Tr.rho_fst, hρ]) (by rw [plains_fst, plains_fst, hπ])

omit [Field F] [Algebra F E] in
omit [DecidableEq E] in
theorem snd_rho_eq {n : ℕ} {t : Shape}
    {τ τ' : Tr (List.replicate n (LinSh.rSC E) ++ t)} (hρ : τ.rho = τ'.rho) :
    (Tr.snd (s := List.replicate n (LinSh.rSC E)) τ).rho =
      (Tr.snd (s := List.replicate n (LinSh.rSC E)) τ').rho := by
  rw [Tr.rho_snd, Tr.rho_snd, hρ]

omit [Field F] [Algebra F E] in
omit [DecidableEq E] in
theorem snd_plains_eq {n : ℕ} {t : Shape}
    {τ τ' : Tr (List.replicate n (LinSh.rSC E) ++ t)} (hπ : τ.plains = τ'.plains) :
    (Tr.snd (s := List.replicate n (LinSh.rSC E)) τ).plains =
      (Tr.snd (s := List.replicate n (LinSh.rSC E)) τ').plains := by
  rw [plains_snd, plains_snd, hπ]

open Classical in
/-- the verifier of the last level, unfolded on the two parts of a transcript -/
theorem okNil_eq (c : a.Claim E) (w : a.Word E) (τ : Tr (levelsShape E a []))
    (σ : Tr (List.replicate a.mu (LinSh.rSC E)))
    (tl : Tr [a.rTheta E, a.rLast E])
    (h1 : Tr.fst (s := List.replicate a.mu (LinSh.rSC E)) (t := [a.rTheta E, a.rLast E]) τ = σ)
    (h2 : Tr.snd (s := List.replicate a.mu (LinSh.rSC E)) (t := [a.rTheta E, a.rLast E]) τ = tl) :
    levelsOk a [] c w τ = decide (
      a.endVal c (ofList ((trList (LinSh.rSC E) a.mu σ).map fun x => x.2)) (nat tl.2.2.1.2.1) =
        a.clEnd c.v (ofList ((trList (LinSh.rSC E) a.mu σ).map fun x => x.2))
          (ofList ((trList (LinSh.rSC E) a.mu σ).map fun x => x.1.2.1))
          (ofList ((trList (LinSh.rSC E) a.mu σ).map fun x => x.1.2.2)) ∧
      ∀ i, a.encRow tl.2.2.1.2.1 (tl.2.2.2.1 i) =
        a.foldW w (ofList ((trList (LinSh.rSC E) a.mu σ).map fun x => x.2)) (tl.2.2.2.1 i) ∧
        a.encRow tl.2.2.1.2.2 (tl.2.2.2.1 i) = a.combW w tl.2.1 (tl.2.2.2.1 i)) := by
  subst h1 h2
  rfl

/-- the verifier of a level that is not the last, unfolded on the two parts of a transcript -/
theorem okCons_eq (b : LevSpec F) (rest : List (LevSpec F)) (c : a.Claim E) (w : a.Word E)
    (τ : Tr (levelsShape E a (b :: rest))) (σ : Tr (List.replicate a.mu (LinSh.rSC E)))
    (tl : Tr (a.rTheta E :: a.rNext E b :: levelsShape E b rest))
    (h1 : Tr.fst (s := List.replicate a.mu (LinSh.rSC E))
        (t := a.rTheta E :: a.rNext E b :: levelsShape E b rest) τ = σ)
    (h2 : Tr.snd (s := List.replicate a.mu (LinSh.rSC E))
        (t := a.rTheta E :: a.rNext E b :: levelsShape E b rest) τ = tl) :
    levelsOk a (b :: rest) c w τ =
      levelsOk b rest
        (a.nextClaim b c w (ofList ((trList (LinSh.rSC E) a.mu σ).map fun x => x.2))
          (ofList ((trList (LinSh.rSC E) a.mu σ).map fun x => x.1.2.1))
          (ofList ((trList (LinSh.rSC E) a.mu σ).map fun x => x.1.2.2)) tl.2.1 tl.2.2.2.1)
        (tl.2.2.1.1 ()) tl.2.2.2.2 := by
  subst h1 h2
  rfl

end LevelLocal

end Blocks
