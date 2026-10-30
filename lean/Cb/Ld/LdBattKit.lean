-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdBattKit.lean: a kit for blocks that are made of a draw and a sumcheck on a cube.

Two lemmas on interactive oracle reductions (two reductions in a row; a round in which the verifier
alone speaks), and two facts on a sumcheck (degrees; over the cube, the product of the public
polynomials (`hPsi`, Cb/Ld/LdHide.lean)).
Statements and proofs; no protocol.
`GoodAt` (Cb/Ld/LdSigLift.lean) is a record of properties of an interactive oracle reduction between
two joints, among them completeness of the honest prover and, for each fixed tuple of messages, on
the statements that meet the first joint's condition (`on`), round-by-round knowledge soundness with
a given extractor and a given count of bad challenges for each round.
A draw (`IOR.draw`, Ior/Draw.lean) is a reduction of one round: the prover sends nothing, the
verifier sends a value β of a finite set that is not empty, and the explicit part x becomes nx x β.

Main names:
  `Spec.goodAt_seq_ext`: two blocks with `GoodAt` in a row have `GoodAt`: errors in a row,
    probabilities added; for any extractor that agrees with "the second's, then the first's".
  `Spec.goodAt_draw`: the verifier draws a value (Ior/Draw.lean), from a finite set that is not
    empty: `GoodAt` with one error err, the identity as extractor, if every drawn value carries the
    exact relation (`rel`) and the condition (`on`) over, the two cores (`core`) agree (fields of
    `IOR.Rels`, Ior/Chain.lean), and, at each statement with the condition, for each fixed tuple at
    most err values β are such that some further part wp is in `A'.relR` for the new statement and
    not in `A.relR` for the old one.
  The next two are on the variables of a sumcheck, the second on a cube, with the definitions of
    Cb/Ld/LdPscVars.lean.
  `Spec.kit_deg`: the k variables have one format, and n is its degree: then a function of the point
    with degree at most n in each variable (`Alg.DegLE`) has the degrees of the variables (`HDeg`,
    Cb/Ld/LdPsc.lean: in each variable, all others fixed, it is a polynomial with the n + 1
    coefficients of that variable).
  `Spec.kit_psi_plains`: if 1 ≤ n, the product of the public polynomials of k plain variables at a
    point is the product of the coordinates.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdSigLift
import Cb.Ld.LdPscVars
import Cb.Ld.LdHideProofs
import Ior.Draw
import Ior.SeqProofs
import Ior.ChainProofs
import Alg.Poly

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop

namespace Spec
open IOR

/-- Two blocks in a row, for each fixed tuple of messages. -/
def goodAt_seq_ext : Prop :=
  ∀ (K M X₁ X₂ X₃ : Type) (E₁ E₂ E₃ : ExtSpec) (W₁ W₂ W₃ : Type) (R₁ : IOR X₁ E₁ X₂ E₂)
      (R₂ : IOR X₂ E₂ X₃ E₃) (H₁ : R₁.Honest (M × W₁) (M × W₂)) (H₂ : R₂.Honest (M × W₂) (M × W₃))
      (A : Rels K X₁ E₁ (M × W₁)) (B : Rels K X₂ E₂ (M × W₂)) (C : Rels K X₃ E₃ (M × W₃))
      (e₁ : M → X₁ × E₁.Str → Tr R₁.shape → W₂ → W₁) (e₂ : M → X₂ × E₂.Str → Tr R₂.shape → W₃ → W₂)
      (ext : M → X₁ × E₁.Str → Tr (R₁.shape ++ R₂.shape) → W₃ → W₁) (P₁ : Nums K R₁)
      (P₂ : Nums K R₂),
    GoodAt R₁ H₁ A B e₁ P₁ → GoodAt R₂ H₂ B C e₂ P₂ →
    (∀ m a (τ₁ : Tr R₁.shape) (τ₂ : Tr R₂.shape) b w,
      R₁.red.out a τ₁ = some b → ext m a (Tr.app τ₁ τ₂) w = e₁ m a τ₁ (e₂ m b τ₂ w)) →
    GoodAt (R₁.seq R₂) (H₁.seq H₂) A C ext (P₁.seq P₂)

/-- A draw, for each fixed tuple of messages. -/
def goodAt_draw : Prop :=
  ∀ (K M X X' : Type) (Ex : ExtSpec) (Wp D : Type) [Fintype D] [Nonempty D] (nx : X → D → X')
      (A : Rels K X Ex (M × Wp)) (A' : Rels K X' Ex (M × Wp)) (err : ℕ),
    (∀ x y w β, A.rel x y w → A'.rel (nx x β) y w) →
    (∀ x y β, A.on (x, y) → A'.on (nx x β, y)) → (∀ w, A'.core w = A.core w) →
    (∀ x y (m : M), A.on (x, y) →
      cnt (fun β => ∃ wp, A'.relR (nx x β, y) (m, wp) ∧ ¬ A.relR (x, y) (m, wp)) ≤ err) →
    GoodAt (IOR.draw D nx Ex) (Honest.draw D nx Ex (M × Wp)) A A'
      (fun _ _ _ wp => wp) (Nums.draw K D nx Ex err)

def kit_deg : Prop :=
  ∀ (E : Type) [Field E] (f : PFmt E) (k : ℕ)
      (d : PDats (List.replicate k f)) (g : (Fin k → E) → E),
    Alg.DegLE (fun _ => f.n) g → HDeg (pVars (List.replicate k f) d) fun X => g (hFnOf f k d X)

def kit_psi_plains : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (n k : ℕ), 1 ≤ n →
    ∀ X, hPsi (pVars (List.replicate k (pfCube E n)) (pdPlains E n k)) X =
      ∏ i, hFnOf (pfCube E n) k (pdPlains E n k) X i

end Spec

open IOR ChainKit

theorem goodAt_seq_ext : Spec.goodAt_seq_ext := by
  intro K M X₁ X₂ X₃ E₁ E₂ E₃ W₁ W₂ W₃ R₁ R₂ H₁ H₂ A B C e₁ e₂ ext P₁ P₂ g₁ g₂ he
  exact
    { point := g₁.point.elim fun p₁ => g₂.point.elim fun p₂ => ⟨Shape.IsPoint.append p₁ p₂⟩
      isLocal := g₁.isLocal.seq g₂.isLocal
      acc := g₁.acc.seq g₂.acc
      onOut := by
        intro a τ c ha hc
        obtain ⟨b, hb, hc'⟩ := Option.bind_eq_some_iff.1 ((IOR.red_seq_out R₁ R₂ a τ).symm.trans hc)
        exact g₂.onOut b _ c (g₁.onOut a _ b ha hb) hc'
      keeps := by
        intro w x c ρ
        rw [Honest.run_seq]
        exact (g₂.keeps _ _ _ _).trans (g₁.keeps _ _ _ _)
      prBad := le_trans (prRho_cyl_union_le H₁.Bad H₂.Bad) (add_le_add g₁.prBad g₂.prBad)
      cover := by
        rintro w x ρ (hρ | ⟨_, c, hc⟩)
        · exact Or.inl (g₁.cover w x hρ)
        · have h := g₂.cover _ _ hc
          rw [g₁.keeps] at h
          exact Or.inr h
      prCov := fun k =>
        le_trans (prRho_cyl_union_le (P₁.cov k) (P₂.cov k)) (add_le_add (g₁.prCov k) (g₂.prCov k))
      same := by
        intro w x c ρ
        rw [Honest.run_seq]
        exact (g₂.same _ _ _ _).trans (g₁.same _ _ _ _)
      know := by
        intro m a ha
        refine Doomed.mono _ _ ?_
          (Reduction.Know.seq_ext (g₁.know m) (g₂.know m) g₁.onOut (ext m) (he m) a ha)
        intro τ h b w hb hw
        exact h b w ((IOR.red_seq_out R₁ R₂ a τ).symm.trans hb) hw }

theorem goodAt_draw : Spec.goodAt_draw := by
  intro K M X X' Ex Wp D _ _ nx A A' err hfw hon hcore hcnt
  have g := (piece_draw K X X' Ex (M × Wp) D nx A A' (Fintype.card D) (fun _ => True)
    hfw hon hcore fun _ _ _ => cnt_le_card _).good
  exact
    { point := g.point
      isLocal := g.isLocal
      acc := g.acc
      onOut := g.onOut
      keeps := g.keeps
      prBad := g.prBad
      cover := g.cover
      prCov := g.prCov
      same := fun _ _ _ _ => rfl
      know := fun m =>
        (piece_draw K X X' Ex Wp D nx ⟨fun x y wp => A.rel x y (m, wp),
          fun a wp => A.relR a (m, wp), A.on, fun wp => A.core (m, wp)⟩
          ⟨fun x y wp => A'.rel x y (m, wp), fun a wp => A'.relR a (m, wp),
            A'.on, fun wp => A'.core (m, wp)⟩
          err (fun _ => True)
          (fun x y wp β h => hfw x y (m, wp) β h) hon
            (fun wp => hcore (m, wp)) fun x y h => hcnt x y m h).good.know }

theorem kit_deg : Spec.kit_deg := by
  intro E _ f k
  induction k with
  | zero => intro _ _ _; trivial
  | succ k ih =>
      intro d g hg
      refine ⟨fun xs => ?_, fun x => ?_⟩
      · obtain ⟨q, hq, he⟩ := hg (Fin.cons 0 (hFnOf f k d.2 xs)) 0
        refine ⟨fun t => q.coeff t, fun x => ?_⟩
        show g (Fin.cons x (hFnOf f k d.2 xs)) = _
        have e : (Fin.cons x (hFnOf f k d.2 xs) : Fin (k + 1) → E) =
            Function.update (Fin.cons 0 (hFnOf f k d.2 xs)) 0 x := by
          rw [Fin.update_cons_zero]
        rw [e, he, Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hq)]
        unfold hev
        rw [Fin.sum_univ_eq_sum_range (fun t => x ^ t • q.coeff t) (f.n + 1)]
        exact Finset.sum_congr rfl fun t _ => by rw [smul_eq_mul, mul_comm]
      · refine ih d.2 (fun z => g (Fin.cons x z)) fun z i => ?_
        obtain ⟨q, hq, he⟩ := hg (Fin.cons x z) i.succ
        refine ⟨q, hq, fun t => ?_⟩
        show g (Fin.cons x (Function.update z i t)) = _
        rw [← he t, Fin.cons_update]

theorem kit_psi_plains : Spec.kit_psi_plains := by
  intro E _ _ n k hn
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
      intro X
      show hev (pvX E n) X.1 * hPsi (pVars (List.replicate k (pfCube E n)) (pdPlains E n k)) X.2 = _
      have hx : hev (pvX E n) X.1 = X.1 := plain_psi E n X.1 hn
      rw [hx, ih X.2, Fin.prod_univ_succ]
      rfl

end Cb
