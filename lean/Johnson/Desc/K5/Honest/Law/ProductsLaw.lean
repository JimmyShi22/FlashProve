-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/ProductsLaw.lean: the honest prover's side of an attention segment's own
rounds: the law of a summand that is a sum of weighted products of two hidden maps. If its weights
and its maps, read in a field, are given functions of the point, read, then its sum over the cube is
the sum of these functions' products over the library's vertices; if moreover each of the functions
is the multilinear extension of its values on the cube, the summand has the properties that the
masked sumcheck's prover asks of it. Definitions, and statements with their proofs.

Main names:
  `ProductReads rho S np Wl Al Bl`   the terms of S are W_b e_(2b) e_(2b+1), b below np; at every
                    point x of the summand's length the weight W_b, the map number 2 b and the map
                    number 2 b + 1 read as Wl b, Al b and Bl b at x, read
  `ExtOfCube n F`   F is the multilinear extension of its values at the cube's vertices
  `extOfCube_ext`   the extension of a table is one
  `ofProducts_terms`, `ofProducts_even`, `ofProducts_odd`
                    the form of Johnson/Desc/K5/Honest/Products.lean has these terms and maps
  `ProductReads.at`, `ProductReads.total`   the summand at a point; its sum over the cube
  `ProductReads.named`   `Summand.Named`: every factor names one of the 2 np end values
  `ProductReads.tame`   `Summand.Tame` (Johnson/Desc/K5/Honest/Law/TermsLaw.lean) at 4 coefficients
                    a variable and degree 2 in the further variable
  `StepReads`, `StepReads.total`, `StepReads.tame`   the same against the library's `Wb`, `Aext`,
                    `Bext` of a step (Inst/Model/Att/Sums.lean): the sum is `sumPhi`

The statements in the namespaces `ProductReads` and `StepReads`, but for `ProductReads.pt_list`, are
conditional, each on the proposition of that name, which the files on the single summands are meant
to show, each under its own premises. `ProductReads.tame` also asks `ExtOfCube` of the weights and
of both maps; `StepReads.tame` of the weights alone; `ProductReads.named` that the summand has 2 np
end values; `ProductReads.at` that the point has as many coordinates as the summand has variables.
The other statements ask at most a bound on a number.
Limits. Nothing is said of a summand of another form. No property is claimed by a definition.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.K5.Honest.Law.Cells
import Johnson.Desc.K5.Honest.Law.TermsLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes (E addE subE mulE zeroE oneE)
open OnBytes.Model (Reading)
open OnBytes.Road (pt)
open Inst.Model.AttSeg
open Finset

variable {K : Type} [Field K] (ρ : Reading K)

/-! ## The premises -/

/-- **The summand is a sum of weighted products of two maps, which read as given functions.** -/
structure ProductReads (S : Summand) (np : ℕ) (Wl Al Bl : ℕ → (ℕ → K) → K) : Prop where
  terms : ∃ W : List E → Array E, (∀ x, S.terms x = pairsOf np (W x)) ∧
    ∀ x, x.length = S.vars → ∀ b < np, ρ.val ((W x).getD b zeroE) = Wl b (pt ρ x.toArray)
  A : ∀ x, x.length = S.vars → ∀ b < np, ρ.val (S.endAt x (2 * b)) = Al b (pt ρ x.toArray)
  B : ∀ x, x.length = S.vars → ∀ b < np, ρ.val (S.endAt x (2 * b + 1)) = Bl b (pt ρ x.toArray)

/-- **F is the multilinear extension of its values at the vertices of the cube of n variables.** -/
def ExtOfCube (n : ℕ) (F : (ℕ → K) → K) : Prop :=
  ∀ ξ, Blocks.ext n (fun X => F (Blocks.cubePt n X)) ξ = F ξ

/-- The extension of a table is the extension of its values at the vertices. -/
theorem extOfCube_ext (n : ℕ) (v : ℕ → K) : ExtOfCube n (Blocks.ext n v) := fun ξ =>
  Blocks.ext_congr (fun _ hX => Blocks.ext_cubePt n v hX) ξ

/-! ## The form of the five products -/

theorem ofProducts_terms (vars np : ℕ) (W : Array E → Array E) (A B : Array E → ℕ → E)
    (x : List E) : (ofProducts vars np W A B).terms x = pairsOf np (W x.toArray) := rfl

theorem ofProducts_even (vars np : ℕ) (W : Array E → Array E) (A B : Array E → ℕ → E)
    (x : List E) (b : ℕ) : (ofProducts vars np W A B).endAt x (2 * b) = A x.toArray b := by
  show (if 2 * b % 2 == 0 then A x.toArray (2 * b / 2) else B x.toArray (2 * b / 2)) = _
  rw [Nat.mul_mod_right, Nat.mul_div_cancel_left b (by norm_num)]
  rfl

theorem ofProducts_odd (vars np : ℕ) (W : Array E → Array E) (A B : Array E → ℕ → E)
    (x : List E) (b : ℕ) : (ofProducts vars np W A B).endAt x (2 * b + 1) = B x.toArray b := by
  show (if (2 * b + 1) % 2 == 0 then A x.toArray ((2 * b + 1) / 2)
    else B x.toArray ((2 * b + 1) / 2)) = _
  rw [show (2 * b + 1) % 2 = 1 by omega, show (2 * b + 1) / 2 = b by omega]
  rfl

/-! ## The law -/

/-- A factor that is the bare map. -/
theorem read_bare (S : Summand) (x : List E) (n : ℕ) :
    ρ.val (S.factorAt x ⟨oneE, n, zeroE⟩) = ρ.val (S.endAt x n) := by
  rw [read_factorAt]
  show ρ.val oneE * _ + ρ.val zeroE = _
  rw [ρ.one, ρ.zero, one_mul, add_zero]

/-- A factor that is 0 times a map plus 0. -/
theorem read_noFactor (S : Summand) (x : List E) :
    ρ.val (S.factorAt x ⟨zeroE, 0, zeroE⟩) = 0 := by
  rw [read_factorAt]
  show ρ.val zeroE * _ + ρ.val zeroE = _
  rw [ρ.zero, zero_mul, add_zero]

theorem pairsOf_length (n : ℕ) (W : Array E) : (pairsOf n W).length = n := by
  unfold pairsOf
  simp

theorem pairsOf_getD (n : ℕ) (W : Array E) {b : ℕ} (hb : b < n) :
    (pairsOf n W).getD b ⟨zeroE, []⟩ =
      ⟨W.getD b zeroE, [⟨oneE, 2 * b, zeroE⟩, ⟨oneE, 2 * b + 1, zeroE⟩]⟩ := by
  unfold pairsOf
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hb]
  rfl

theorem pairsOf_getD_ge (n : ℕ) (W : Array E) {b : ℕ} (hb : n ≤ b) :
    (pairsOf n W).getD b ⟨zeroE, []⟩ = ⟨zeroE, []⟩ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [pairsOf_length]; exact hb)]
  rfl

namespace ProductReads
variable {ρ} {S : Summand} {np : ℕ} {Wl Al Bl : ℕ → (ℕ → K) → K}

/-- **The summand at a point.** -/
theorem «at» (R : ProductReads ρ S np Wl Al Bl) (x : List E) (hx : x.length = S.vars) :
    ρ.val (S.at x) = ∑ b ∈ range np,
      Wl b (pt ρ x.toArray) * Al b (pt ρ x.toArray) * Bl b (pt ρ x.toArray) := by
  obtain ⟨W, hT, hW⟩ := R.terms
  rw [S.read_at ρ x, hT x]
  unfold pairsOf
  rw [List.map_map, sum_list_range]
  refine sum_congr rfl fun b hb => ?_
  have hb' := mem_range.mp hb
  show ρ.val ((W x).getD b zeroE) * ([(⟨oneE, 2 * b, zeroE⟩ : Factor),
    ⟨oneE, 2 * b + 1, zeroE⟩].map fun f => ρ.val (S.factorAt x f)).prod = _
  rw [List.map_cons, List.map_cons, List.map_nil, List.prod_cons, List.prod_cons, List.prod_nil,
    read_bare, read_bare, hW x hx b hb', R.A x hx b hb', R.B x hx b hb']
  ring

/-- **The sum over the cube.** -/
theorem total (R : ProductReads ρ S np Wl Al Bl) :
    ρ.val S.total = ∑ X ∈ range (2 ^ S.vars), ∑ b ∈ range np,
      Wl b (Blocks.cubePt S.vars X) * Al b (Blocks.cubePt S.vars X) *
        Bl b (Blocks.cubePt S.vars X) := by
  rw [S.read_total ρ, sum_cube]
  refine sum_congr rfl fun X _ => ?_
  rw [R.at (vertex S.vars X) (vertex_length _ _), pt_vertex_eq]

/-- **Every factor names one of the 2 np end values.** Conditional on `ProductReads` and on hE: the
summand has so many. -/
theorem named (R : ProductReads ρ S np Wl Al Bl) (hE : S.ends = 2 * np) : S.Named (2 * np) := by
  obtain ⟨W, hT, _⟩ := R.terms
  refine ⟨hE, fun x _ t ht f hf => ?_⟩
  rw [hT x] at ht
  unfold pairsOf at ht
  obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ht
  have hb' := List.mem_range.1 hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · show 2 * b < 2 * np
    omega
  · show 2 * b + 1 < 2 * np
    omega

/-- The point of a list, read, in the two ways of writing it. -/
theorem pt_list (ρ : Reading K) (x : List E) :
    (fun i => ρ.val (x.getD i zeroE)) = pt ρ x.toArray :=
  funext fun i => (pt_toArray ρ x i).symm

/-- **The summand has what the masked sumcheck's prover asks of it**: the skeleton of its terms does
not depend on the point; weights and maps are of degree at most 1 in each variable; a round
polynomial has at most 4 coefficients, the polynomial in the further variable at most 3. -/
theorem tame (R : ProductReads ρ S np Wl Al Bl) (hW : ∀ b < np, ExtOfCube S.vars (Wl b))
    (hA : ∀ b < np, ExtOfCube S.vars (Al b)) (hB : ∀ b < np, ExtOfCube S.vars (Bl b)) :
    S.Tame ρ (List.replicate S.vars 4) 2 := by
  obtain ⟨W, hT, hWr⟩ := R.terms
  have zero : ∀ f : List E → E, (∀ x, ρ.val (f x) = 0) → IsExt ρ S.vars f := fun f hf =>
    ⟨fun _ => 0, fun x _ => by rw [hf x, Blocks.ext_const]⟩
  have ofF : ∀ (f : List E → E) (F : (ℕ → K) → K), ExtOfCube S.vars F →
      (∀ x, x.length = S.vars → ρ.val (f x) = F (pt ρ x.toArray)) → IsExt ρ S.vars f :=
    fun f F hF hf => ⟨fun X => F (Blocks.cubePt S.vars X), fun x hx => by
      rw [hf x hx, pt_list, hF]⟩
  refine tame_of_isExt ρ S _ 2 2 (List.length_replicate ..) ?_ ?_ ?_ ?_ ?_ (le_refl _)
  · intro x y _ _
    rw [hT x, hT y]
    unfold pairsOf
    rw [List.map_map, List.map_map]
    rfl
  · intro t
    by_cases ht : t < np
    · refine ofF _ (Wl t) (hW t ht) fun x hx => ?_
      show ρ.val ((S.terms x).getD t ⟨zeroE, []⟩).c = _
      rw [hT x, pairsOf_getD np _ ht]
      exact hWr x hx t ht
    · refine zero _ fun x => ?_
      show ρ.val ((S.terms x).getD t ⟨zeroE, []⟩).c = _
      rw [hT x, pairsOf_getD_ge np _ (by omega)]
      exact ρ.zero
  · intro t j
    by_cases ht : t < np
    · match j with
      | 0 =>
        refine ofF _ (Al t) (hA t ht) fun x hx => ?_
        show ρ.val (S.factorAt x (((S.terms x).getD t ⟨zeroE, []⟩).fs.getD 0 ⟨zeroE, 0, zeroE⟩)) = _
        rw [hT x, pairsOf_getD np _ ht]
        show ρ.val (S.factorAt x ⟨oneE, 2 * t, zeroE⟩) = _
        rw [read_bare, R.A x hx t ht]
      | 1 =>
        refine ofF _ (Bl t) (hB t ht) fun x hx => ?_
        show ρ.val (S.factorAt x (((S.terms x).getD t ⟨zeroE, []⟩).fs.getD 1 ⟨zeroE, 0, zeroE⟩)) = _
        rw [hT x, pairsOf_getD np _ ht]
        show ρ.val (S.factorAt x ⟨oneE, 2 * t + 1, zeroE⟩) = _
        rw [read_bare, R.B x hx t ht]
      | j + 2 =>
        refine zero _ fun x => ?_
        show ρ.val (S.factorAt x
          (((S.terms x).getD t ⟨zeroE, []⟩).fs.getD (j + 2) ⟨zeroE, 0, zeroE⟩)) = _
        rw [hT x, pairsOf_getD np _ ht]
        exact read_noFactor ρ S x
    · refine zero _ fun x => ?_
      show ρ.val (S.factorAt x (((S.terms x).getD t ⟨zeroE, []⟩).fs.getD j ⟨zeroE, 0, zeroE⟩)) = _
      rw [hT x, pairsOf_getD_ge np _ (by omega)]
      exact read_noFactor ρ S x
  · intro x t ht
    rw [hT x] at ht
    unfold pairsOf at ht
    obtain ⟨b, _, rfl⟩ := List.mem_map.1 ht
    exact le_refl _
  · intro d hd
    rw [List.eq_of_mem_replicate hd]

end ProductReads

/-! ## Against a step of the library -/

/-- **The summand's weights and maps read as the library's of the step s.** -/
structure StepReads (S : Summand) (D : Dim) (C : Calls) (p : Pub K) (t : Raw → K) (s : Step) :
    Prop where
  vars : S.vars = s.g D
  reads : ProductReads ρ S D.nb (Wb D C p s) (Aext D C p t s) (Bext D C p t s)

namespace StepReads
variable {ρ} {S : Summand} {D : Dim} {C : Calls} {p : Pub K} {t : Raw → K} {s : Step}

/-- **The sum over the cube is the library's sum of the step.** -/
theorem total (R : StepReads ρ S D C p t s) : ρ.val S.total = sumPhi D C p t s := by
  rw [R.reads.total, R.vars]
  rfl

/-- **The summand has what the masked sumcheck's prover asks of it**, where the step's weight is
the extension of its values on the cube. -/
theorem tame (R : StepReads ρ S D C p t s) (hE : ∀ b, ExtOfCube (s.g D) (Wb D C p s b)) :
    S.Tame ρ (List.replicate S.vars 4) 2 :=
  R.reads.tame (fun b _ => by rw [R.vars]; exact hE b)
    (fun b _ => by rw [R.vars]; exact extOfCube_ext _ _)
    (fun b _ => by rw [R.vars]; exact extOfCube_ext _ _)

end StepReads

end H2K5.Honest

#print axioms H2K5.Honest.extOfCube_ext
#print axioms H2K5.Honest.ofProducts_terms
#print axioms H2K5.Honest.ofProducts_even
#print axioms H2K5.Honest.ofProducts_odd
#print axioms H2K5.Honest.read_bare
#print axioms H2K5.Honest.read_noFactor
#print axioms H2K5.Honest.pairsOf_length
#print axioms H2K5.Honest.pairsOf_getD
#print axioms H2K5.Honest.pairsOf_getD_ge
#print axioms H2K5.Honest.ProductReads.at
#print axioms H2K5.Honest.ProductReads.total
#print axioms H2K5.Honest.ProductReads.named
#print axioms H2K5.Honest.ProductReads.pt_list
#print axioms H2K5.Honest.ProductReads.tame
#print axioms H2K5.Honest.StepReads.total
#print axioms H2K5.Honest.StepReads.tame
