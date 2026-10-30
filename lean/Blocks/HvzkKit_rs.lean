-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/HvzkKit_rs.lean: helper lemmas for exact simulation.

Nothing here depends on a particular protocol. (Words of this library: lean/GLOSSARY.md.)
 * Part 1: the plain parts of two concatenated transcripts (`Tr.app`), and the symbols of the
   second, as congruences.
 * Part 2: the disclosed view (`DView`) depends on a transcript only through ρ, the plain parts and
   the symbols read, if every oracle is blinded (`dview_congr_rs`).
 * Part 3: the probabilistic core (`map_unif_four_rs`): coins (a, γ, c_B, c_C), each from a finite
   nonempty type; a quantity p(a) with a known distribution; a quantity s(a, γ) that is uniform for
   every a ([Fintype Sg] [Nonempty Sg], Sg its type); two quantities whose distributions over c_B
   and over c_C depend only on p and s. Then the distribution of any function of the four quantities
   is known.

Notation: `Plains s`: the plain parts of all prover messages; `OPos s`: positions of all prover
oracles; `OSym s p`: the alphabet at a position (these three: Iop/Shape.lean); `Ex : ExtSpec`:
external strings: oracles that are fixed before the first message;
`Q.blinded : OPos Q.shape → Bool`: a field of `InteractiveOracleProof` (these two: Iop/InteractiveOracleProof.lean). In
`map_unif_four_rs`: `A`, `Γ`, `CB`, `CC`: the types of the coins a, γ, c_B, c_C; `pl : A → Pl`: p;
`s : A → Γ → Sg`: s; `vB : A → Γ → CB → VB`, `vC : A → Γ → CC → VC`: the two quantities over c_B and
over c_C; `Φ : Pl → Sg → VB → VC → Out`: the function of the four quantities; `SimP : PMF Pl`: a
distribution; `KB : Pl → Sg → PMF VB`, `KC : Pl → Sg → PMF VC`: families of distributions.
-/
import Iop.InteractiveOracleProof
import Iop.ShapeKit
import Blocks.Basic
import Prob.Count

set_option autoImplicit false

namespace Blocks

open Iop Prob

/-! ## Part 1. The concatenation of two transcripts -/

theorem plains_app_congr_rs :
    ∀ {s t : Shape} {a a' : Tr s} {b b' : Tr t},
      a.plains = a'.plains → b.plains = b'.plains → (Tr.app a b).plains = (Tr.app a' b').plains
  | [], _, _, _, _, _, _, h => h
  | _ :: _, _, (m, _, a), (m', _, a'), b, b', h, hb => by
      have h1 : m.2 = m'.2 := congrArg Prod.fst h
      have h2 : a.plains = a'.plains := congrArg Prod.snd h
      show (m.2, (Tr.app a b).plains) = (m'.2, (Tr.app a' b').plains)
      rw [h1, plains_app_congr_rs h2 hb]

theorem read_posR_congr_rs :
    ∀ {s t : Shape} (a a' : Tr s) {b b' : Tr t} (p : OPos t), b.read p = b'.read p →
      (Tr.app a b).read (posR (s := s) p) = (Tr.app a' b').read (posR (s := s) p)
  | [], _, _, _, _, _, _, h => h
  | _ :: s, _, (_, _, a), (_, _, a'), _, _, p, h => read_posR_congr_rs (s := s) a a' p h

/-! ## Part 2. The disclosed view -/

/-- The disclosed view sees a transcript only through ρ, the plain parts and the symbols read, if
every oracle is blinded; and the external strings only at the positions read. -/
theorem dview_congr_rs {X : Type} {Ex : ExtSpec} (Q : InteractiveOracleProof X Ex) (x : X) {y y' : Ex.Str}
    {τ τ' : Tr Q.shape} (hρ : τ.rho = τ'.rho) (hpl : τ.plains = τ'.plains)
    (hext : ∀ p ∈ Q.extReads x τ.rho, Ex.rd y p = Ex.rd y' p)
    (hrd : ∀ p ∈ Q.reads x τ.rho τ.plains, τ.read p = τ'.read p) (hbl : ∀ p, Q.blinded p = true) :
    Q.dview x y τ = Q.dview x y' τ' := by
  classical
  have h1 : Q.extAns x τ.rho y = Q.extAns x τ'.rho y' := by
    funext p
    unfold InteractiveOracleProof.extAns
    rw [← hρ]
    by_cases hp : p ∈ Q.extReads x τ.rho
    · rw [if_pos hp, if_pos hp, hext p hp]
    · rw [if_neg hp, if_neg hp]
  have h2 : (fun p =>
        if p ∈ Q.reads x τ.rho τ.plains ∨ Q.blinded p = false then some (τ.read p) else none) =
      fun p =>
        if p ∈ Q.reads x τ'.rho τ'.plains ∨ Q.blinded p = false then some (τ'.read p)
        else none := by
    funext p
    rw [← hρ, ← hpl]
    by_cases hp : p ∈ Q.reads x τ.rho τ.plains
    · rw [if_pos (Or.inl hp), if_pos (Or.inl hp), hrd p hp]
    · have hn : ¬ (p ∈ Q.reads x τ.rho τ.plains ∨ Q.blinded p = false) := by
        rintro (h | h)
        · exact hp h
        · rw [hbl p] at h
          exact Bool.noConfusion h
      rw [if_neg hn, if_neg hn]
  unfold InteractiveOracleProof.dview
  refine congr (congr (congrArg DView.mk hpl) h1) ?_
  convert h2

/-! ## Part 3. The probabilistic core -/

/-- A function of a uniform pair, both parts from finite nonempty types: sample the first part, then
the second. -/
theorem map_unif_pair_eq_bind_rs
    {C D β : Type} [Fintype C] [Nonempty C] [Fintype D] [Nonempty D] (f : C × D → β) :
    (unif (C × D)).map f = (unif C).bind fun c => (unif D).map fun d => f (c, d) := by
  rw [unif_prod]
  unfold Prob.prod
  rw [PMF.map_bind]
  refine congrArg _ (funext fun c => ?_)
  rw [PMF.map_comp]
  rfl

/-- The probabilistic core of an exact simulation. (The statement in words: the head, Part 3; which
binder is which of its letters: the head, "Notation".) -/
theorem map_unif_four_rs {A Γ CB CC Pl Sg VB VC Out : Type} [Fintype A] [Nonempty A] [Fintype Γ]
    [Nonempty Γ] [Fintype CB] [Nonempty CB] [Fintype CC] [Nonempty CC] [Fintype Sg] [Nonempty Sg]
    (pl : A → Pl) (s : A → Γ → Sg) (vB : A → Γ → CB → VB) (vC : A → Γ → CC → VC)
    (Φ : Pl → Sg → VB → VC → Out) (SimP : PMF Pl) (KB : Pl → Sg → PMF VB) (KC : Pl → Sg → PMF VC)
    (h1 : (unif A).map pl = SimP) (h2 : ∀ a, (unif Γ).map (s a) = unif Sg)
    (h3 : ∀ a γ, (unif CB).map (vB a γ) = KB (pl a) (s a γ))
    (h4 : ∀ a γ, (unif CC).map (vC a γ) = KC (pl a) (s a γ)) :
    (unif (A × Γ × CB × CC)).map
        (fun c => Φ (pl c.1) (s c.1 c.2.1) (vB c.1 c.2.1 c.2.2.1) (vC c.1 c.2.1 c.2.2.2)) =
      SimP.bind fun p =>
        (unif Sg).bind fun σ => (KB p σ).bind fun b => (KC p σ).map fun c => Φ p σ b c := by
  rw [← h1, PMF.bind_map, map_unif_pair_eq_bind_rs]
  refine congrArg _ (funext fun a => ?_)
  show _ =
    (unif Sg).bind fun σ => (KB (pl a) σ).bind fun b => (KC (pl a) σ).map fun c => Φ (pl a) σ b c
  rw [← h2 a, PMF.bind_map, map_unif_pair_eq_bind_rs]
  refine congrArg _ (funext fun γ => ?_)
  show _ = (KB (pl a) (s a γ)).bind fun b => (KC (pl a) (s a γ)).map fun c => Φ (pl a) (s a γ) b c
  rw [← h3 a γ, PMF.bind_map, map_unif_pair_eq_bind_rs]
  refine congrArg _ (funext fun cb => ?_)
  show _ = (KC (pl a) (s a γ)).map fun c => Φ (pl a) (s a γ) (vB a γ cb) c
  rw [← h4 a γ, PMF.map_comp]
  rfl

end Blocks
