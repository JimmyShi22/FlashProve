-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/StageRows.lean: rows (a row: one stage of a `Chain`, Blocks/Stage.lean) that every segment
needs, as stages: a challenge that combines equations, and a sumcheck by whose challenges a later
block divides. (Words of this library: lean/GLOSSARY.md.)

In each case but the last (`stageNz`) hidden quantities are claimed to be 0, the verifier sends one
challenge, and afterwards one combination of them (or one for each member of a family) is claimed to
be 0; there is no prover message and no pad, and the withheld set (`Hon.withheld`,
Blocks/BlockHon.lean) is empty.
 * `Stage.test`, `props_test`: the common form. Z says that all quantities are 0, T c that the
   combinations under the challenge c are 0; if Z fails, at most e challenges satisfy T (hcnt).
 * `Stage.coef`, `props_coef`: independent coefficients c_j, one for each j : J: d0 i + ∑_j c_j d i
   j = 0 for every member i. At most |E|^(|J| - 1) of the |E|^|J| tuples are bad.
 * `Stage.ptFam`, `props_ptFam`: a point p of g coordinates: the multilinear extensions of the
   functions d m on {0,1}^g vanish at p, for every member m of a finite, linearly ordered family. At
   most g |E|^(g - 1) of the |E|^g points are bad.
 * `Stage.pow`, `props_pow`: the powers of one challenge γ: ∑_(s<n) γ^s d m s = 0 for every member
   m. At most n - 1 values are bad.
 * `SC.Prover.stageNz`, `props_stageNz`: the masked sumcheck as a stage when a later block divides
   by some of its challenges: the verifier rejects if such a challenge is 0, and the public part of
   the withheld set has probability at most (number of rounds) / |E|. `SC.Prover.stage`
   (Blocks/SumCheckStage.lean) is the case in which no block divides. The protocol and the tracking
   data are the same: `H.core l`, `H.track l`.
A stage of this file other than `stageNz` is `Stage.sample` with the check that always passes. So
its tracking data, number of rounds and bounds are those of `Stage.sample`.
How a row uses them. The relations before and after the stage are the caller's. hout says what the
relation after the stage gives: the combinations vanish, and a further condition Q; hin says that
the quantities being 0, with Q, give the relation before the stage; hfwd and hV are the steps for
the honest run and for validity, as for `Stage.sample`. A point, or a tuple of coefficients, is one
verifier message.

The counts are `Alg.count_affine_form_le_pow`, `Blocks.cnt_badPtFam_le` and `Alg.count_roots_le`.

Notation: `Sorts`: the types between two stages: the explicit part X and the implicit part Y of a
statement, and the state I of the honest prover; `Cut`: the relations between two stages: `R`: the
relation for soundness; `Hn`: the relation of the honest run; `V`: validity of the honest state
(both: Blocks/Stage.lean); `pBad`, `pWin`: fields of a `Stage` (see the record, Blocks/Stage.lean);
`cnt P`: the number of elements of a finite type with the property P (Prob/Cnt.lean); `ext g v pt`:
the multilinear extension of the vector v of length 2^g at the point pt (its first g coordinates)
(Blocks/Ext.lean); `nat v`: a vector as a function on ℕ, 0 beyond its end (Blocks/Basic.lean).
-/
import Blocks.StageLib
import Blocks.StageSide
import Blocks.LookupRel
import Blocks.ProductStage
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Blocks

open Iop Prob Finset
open scoped ENNReal

variable {P E : Type} [Field E] [Fintype E] [DecidableEq E] [Fintype P] [DecidableEq P] {a : Sorts}

/-- A challenge that combines equations: the protocol. The verifier sends c : C and records it; the
honest prover's state becomes nx s c. -/
@[reducible] def Core.test (a : Sorts) (I' C : Type) [Fintype C] [Nonempty C] (nx : a.I → C → I') :
    Core P E a ⟨a.X × C, a.Y, I'⟩ :=
  Core.sample a I' C (fun _ => true) nx

namespace Stage

/-- A challenge that combines equations, with at most e bad values. -/
abbrev test (a : Sorts) (I' C : Type) [Fintype C] [Nonempty C]
    (nx : a.I → C → I') (e : ℕ) :
    Stage P E a ⟨a.X × C, a.Y, I'⟩ :=
  Stage.sample a I' C (fun _ => true) nx e 0

omit [Fintype E] [Fintype P] [DecidableEq P] in
omit [DecidableEq E] in
theorem toCore_test (I' C : Type) [Fintype C] [Nonempty C] (nx : a.I → C → I') (e : ℕ) :
    (test (P := P) (E := E) a I' C nx e).toCore = Core.test a I' C nx := rfl

omit [Fintype E] [Fintype P] [DecidableEq P] in
omit [DecidableEq E] in
/-- For a nonempty C, the check that always passes fails with probability 0. -/
theorem prRho_pass (C : Type) [Fintype C] [Nonempty C] :
    prRho {ρ : Rho [Block.chalRound E C] | (fun _ : C => true) ρ.1 = false} ≤ 0 := by
  have h : {ρ : Rho [Block.chalRound E C] | (fun _ : C => true) ρ.1 = false} = ∅ :=
    Set.eq_empty_of_forall_notMem fun _ h => Bool.noConfusion h
  rw [h]
  unfold prRho
  rw [pr_empty]

/-- `Stage.Props`, for a nonempty C, under hcnt, hout, hin, hfwd, hV. -/
theorem props_test {I' C : Type} [Fintype C] [Nonempty C] (nx : a.I → C → I') (e : ℕ)
    {ca : Cut P E a} {cb : Cut P E ⟨a.X × C, a.Y, I'⟩} (Z Q : a.X → a.Y → Prop)
    (T : a.X → a.Y → C → Prop) (hcnt : ∀ x y, ¬ Z x y → cnt (fun c => T x y c) ≤ e)
    (hout : ∀ x y c, cb.R (x, c) y → T x y c ∧ Q x y) (hin : ∀ x y, Z x y → Q x y → ca.R x y)
    (hfwd : ∀ s π x y c, ca.Hn s π x y → cb.Hn (nx s c) π (x, c) y)
    (hV : ∀ s c, ca.V s → cb.V (nx s c)) :
    (test (P := P) (E := E) a I' C nx e).Props ca cb :=
  Stage.props_sample (ca := ca) (cb := cb) _ _ _ _ (fun x y => {c | ¬ Z x y ∧ T x y c})
    (fun x y => by
      by_cases hz : Z x y
      · rw [cnt_false fun c hc => hc.1 hz]
        exact Nat.zero_le _
      · exact (cnt_mono fun c hc => hc.2).trans (hcnt x y hz))
    (fun x y c hc _ hR => by
      obtain ⟨hT, hQ⟩ := hout x y c hR
      refine hin x y ?_ hQ
      by_contra hz
      exact hc ⟨hz, hT⟩)
    (fun s π x y c h _ => hfwd s π x y c h) hV (prRho_pass _)

/-! ### Independent coefficients -/

section Coef
variable {J : Type} [Fintype J] [DecidableEq J]

/-- Independent coefficients. -/
abbrev coef (a : Sorts) (I' J : Type) [Fintype J]
    [DecidableEq J] (nx : a.I → (J → E) → I') :
    Stage P E a ⟨a.X × (J → E), a.Y, I'⟩ :=
  test a I' (J → E) nx (Fintype.card E ^ (Fintype.card J - 1))

/-- `Stage.Props` of `coef`, under hout, hin, hfwd, hV. The hidden quantities are d0 i and d i j,
for the members i of a family that shares the coefficients. -/
theorem props_coef {I' M : Type} (nx : a.I → (J → E) → I') {ca : Cut P E a}
    {cb : Cut P E ⟨a.X × (J → E), a.Y, I'⟩} (d0 : a.X → a.Y → M → E) (d : a.X → a.Y → M → J → E)
    (Q : a.X → a.Y → Prop)
    (hout : ∀ x y c, cb.R (x, c) y → (∀ i, d0 x y i + ∑ j, c j * d x y i j = 0) ∧ Q x y)
    (hin : ∀ x y, (∀ i, d0 x y i = 0 ∧ ∀ j, d x y i j = 0) → Q x y → ca.R x y)
    (hfwd : ∀ s π x y c, ca.Hn s π x y → cb.Hn (nx s c) π (x, c) y)
    (hV : ∀ s c, ca.V s → cb.V (nx s c)) :
    (coef (P := P) (E := E) a I' J nx).Props ca cb :=
  props_test nx _ (fun x y => ∀ i, d0 x y i = 0 ∧ ∀ j, d x y i j = 0) Q
    (fun x y c => ∀ i, d0 x y i + ∑ j, c j * d x y i j = 0)
    (fun x y hz => by
      obtain ⟨i, hi⟩ := not_forall.mp hz
      have h : d0 x y i ≠ 0 ∨ d x y i ≠ 0 := by
        by_contra hc
        rw [not_or, not_not, not_not] at hc
        exact hi ⟨hc.1, fun j => congrFun hc.2 j⟩
      exact (cnt_mono fun c hc => hc i).trans (Alg.count_affine_form_le_pow (d0 x y i) (d x y i) h))
    hout hin hfwd hV

end Coef

/-! ### One point for a family of functions on a hypercube -/

/-- A point of g coordinates. -/
abbrev ptFam (a : Sorts) (I' : Type) (g : ℕ) (nx : a.I → (Fin g → E) → I') :
    Stage P E a ⟨a.X × (Fin g → E), a.Y, I'⟩ :=
  test a I' (Fin g → E) nx (g * Fintype.card E ^ (g - 1))

/-- `Stage.Props` of `ptFam`, for a finite, linearly ordered family M, under hout, hin, hfwd, hV.
The hidden quantities are the values d m X, X < 2^g, of the members m of a family of functions on
the cube. -/
theorem props_ptFam {I' M : Type} [LinearOrder M] [Finite M] (g : ℕ) (nx : a.I → (Fin g → E) → I')
    {ca : Cut P E a} {cb : Cut P E ⟨a.X × (Fin g → E), a.Y, I'⟩} (d : a.X → a.Y → M → ℕ → E)
    (Q : a.X → a.Y → Prop)
    (hout : ∀ x y p, cb.R (x, p) y → (∀ m, ext g (d x y m) (nat p) = 0) ∧ Q x y)
    (hin : ∀ x y, (∀ m, ∀ X < 2 ^ g, d x y m X = 0) → Q x y → ca.R x y)
    (hfwd : ∀ s π x y p, ca.Hn s π x y → cb.Hn (nx s p) π (x, p) y)
    (hV : ∀ s p, ca.V s → cb.V (nx s p)) :
    (ptFam (P := P) (E := E) a I' g nx).Props ca cb :=
  props_test nx _ (fun x y => ∀ m, ∀ X < 2 ^ g, d x y m X = 0) Q
    (fun x y p => ∀ m, ext g (d x y m) (nat p) = 0)
    (fun x y hz => (cnt_mono fun p hp => by
      by_contra hb
      exact hz (eq_zero_of_not_badPtFam hb hp)).trans (cnt_badPtFam_le g (d x y)))
    hout hin hfwd hV

/-! ### The powers of one challenge -/

open Polynomial in
omit [DecidableEq E] in
/-- For n coefficients v s that are not all 0, at most n - 1 values γ satisfy ∑_s γ^s v s = 0. -/
theorem cnt_pow_le {n : ℕ} (v : Fin n → E) (hv : v ≠ 0) :
    cnt (fun γ : E => ∑ s, γ ^ s.val * v s = 0) ≤ n - 1 := by
  classical
  have hq : (∑ s : Fin n, C (v s) * X ^ s.val : E[X]) ≠ 0 := by
    intro h0
    refine hv (funext fun s => ?_)
    have h1 := congrArg (fun q : E[X] => q.coeff s.val) h0
    simp only [finset_sum_coeff, coeff_C_mul, coeff_X_pow, coeff_zero] at h1
    rw [Finset.sum_eq_single s
        (fun s' _ hne => by rw [if_neg fun h => hne (Fin.ext h.symm), mul_zero])
        (fun h => absurd (mem_univ s) h)] at h1
    simpa using h1
  have hd : (∑ s : Fin n, C (v s) * X ^ s.val : E[X]).natDegree ≤ n - 1 :=
    natDegree_sum_le_of_forall_le _ _ fun s _ =>
      (natDegree_C_mul_X_pow_le _ _).trans (by have := s.2; omega)
  refine le_trans (cnt_mono fun γ hγ => ?_) (Alg.count_roots_le hq hd)
  rw [eval_finset_sum]
  simp only [eval_mul, eval_C, eval_pow, eval_X]
  rw [← hγ]
  exact Finset.sum_congr rfl fun s _ => mul_comm _ _

/-- The powers of one challenge. -/
abbrev pow (a : Sorts) (I' : Type) (n : ℕ) (nx : a.I → E → I') :
    Stage P E a ⟨a.X × E, a.Y, I'⟩ :=
  test a I' E nx (n - 1)

/-- `Stage.Props` of `pow`, under hout, hin, hfwd, hV. The hidden quantities are d m s, s < n, for
the members m of a family that shares the challenge. -/
theorem props_pow {I' M : Type} (n : ℕ) (nx : a.I → E → I') {ca : Cut P E a}
    {cb : Cut P E ⟨a.X × E, a.Y, I'⟩} (d : a.X → a.Y → M → Fin n → E) (Q : a.X → a.Y → Prop)
    (hout : ∀ x y γ, cb.R (x, γ) y → (∀ m, ∑ s, γ ^ s.val * d x y m s = 0) ∧ Q x y)
    (hin : ∀ x y, (∀ m s, d x y m s = 0) → Q x y → ca.R x y)
    (hfwd : ∀ s π x y γ, ca.Hn s π x y → cb.Hn (nx s γ) π (x, γ) y)
    (hV : ∀ s γ, ca.V s → cb.V (nx s γ)) :
    (pow (P := P) (E := E) a I' n nx).Props ca cb :=
  props_test nx _ (fun x y => ∀ m s, d x y m s = 0) Q
    (fun x y γ => ∀ m, ∑ s, γ ^ s.val * d x y m s = 0)
    (fun x y hz => by
      obtain ⟨m, hm⟩ := not_forall.mp hz
      exact (cnt_mono fun γ hγ => hγ m).trans
        (cnt_pow_le (d x y m) fun h0 => hm fun s => congrFun h0 s))
    hout hin hfwd hV

end Stage

/-! ### A sumcheck by whose challenges a later block divides -/

namespace SC.Prover

variable {Y Ξ ι A : Type} [DecidableEq E] [DecidableEq ι] {S : SC E Y P Ξ ι} (H : S.Prover A)

/-- The masked sumcheck that binds the variables of l, as a stage, whatever the flags nzv are
(`S.nzv i`: a later block divides by the challenge of i). -/
def stageNz (l : List ι) : Stage P E ⟨S.X, Y, A × (ι → E)⟩ ⟨S.X, Y, A × (ι → E)⟩ where
  toCore := H.core l
  ε := S.scErr l
  U := S.padsOf l
  D := S.padsOf l
  Sim := S.simSc l
  pBad := (l.length : ℝ≥0∞) / Fintype.card E
  pWin := 0

omit [Fintype P] [DecidableEq P] in
theorem toCore_stageNz (l : List ι) : (H.stageNz l).toCore = H.core l := rfl

/-- `Stage.Props`, under the hypotheses below, from the start claim (`S.Rsum`) to the end claim
(`S.Reval`). -/
theorem props_stageNz {Φ : Ξ → Y → (ι → E) → E} (h : S.OK Φ)
    (hnode : ∀ i, Function.Injective (Alg.node (S.e i) : Fin (S.e i + 2) → E)) {l : List ι}
    (hp : S.PlacesOnceOn l) (hl : l.Nodup) {Link : A → (P → E) → Ξ → Y → Prop}
    (hLink : ∀ a π ξ y,
      Link a π ξ y → S.wt ξ = H.wt a ∧ ∀ p ∈ S.padsOf l, S.forms.val y (S.forms.pad p) = π p)
    (V : A → Prop) :
    (H.stageNz l).Props ⟨S.Rsum Φ l, H.Hsum Link l, fun s => V s.1⟩
      ⟨S.Reval Φ, H.Hsum Link [], fun s => V s.1⟩ where
  clean := S.clean_sc_eval h l
  acc := by
    have hacc := H.accOn_sc h.forms hnode l [] hLink
    rw [List.append_nil] at hacc
    exact hacc
  masked := H.masked_sc_on V l [] hp hl
  keeps := fun s ρ hs => by
    show V ((H.sc l []).next s ρ).1
    rw [next_fst]
    exact hs
  prBad := H.prBad_sc l []
  prWin := fun s _ => prRho_empty _ fun ρ hρ => by
    have h1 : ρ ∈ (H.sc l []).Win s := hρ
    rw [H.win_sc l [] s] at h1
    exact h1

end SC.Prover

end Blocks
