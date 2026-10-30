-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/MergeBlock.lean: the two merges of claims on the committed matrix, as blocks.

A merge combines several linear claims on the matrix W into one index claim, by random coefficients
and one masked sumcheck (Blocks/SumCheckBlock.lean). The file proves soundness (`Block.Clean`),
completeness (`Hon.AccOn`) and masked form (`Hon.Masked`). (Words of this library:
lean/GLOSSARY.md.)

One block for both merges. A column claim (γ, ε, f) says that the value of the form f is ∑_c ε(c)
(γᵀ W)[c]. An index claim (g, ψ, f) is the column claim with ε = eq(ψ, ·); a tensor claim is the
column claim with its γ_a and ε_a. `MG.mergeC` merges any number of column claims: the verifier
sends independent coefficients α_j, a masked sumcheck of degree 2 with plain weights runs for ∑_j
α_j val(f_j) = ∑_c ∑_j α_j ε_j(c) (γ_jᵀ W)[c], and the output is the index claim with g = ∑_j α_j
ε̃_j(ψ) γ_j, the end point ψ and the end form.
 * `mergeC` (the general block), `merge` (index claims go in), `rename` (a masked scalar for the end
   form, and the deferred claim LIN(end form − scalar): this form has the value 0): each with
   clean_, accOn_ and masked_ theorems.
 * `tensorMerge`, with `clean_tensorMerge`: soundness only.
The theorems on `mergeC`, `merge` and `tensorMerge` have hypotheses: `Forms.OK` and that the list l
names every variable once (soundness, completeness); that the block's pads are in Q (completeness);
`SC.PlacesOnce` and `l.Nodup` (the masked_ theorems). `accOn_rename`: `Forms.OK`, p ∈ Q.
`accOn_mergeC` and `accOn_merge` also need 2 ≠ 0 in E (the instance NeZero (2 : E)): the honest
scalars of a sumcheck round of degree 2 are computed from the values at 0, 1, 2
(Alg/RoundValues.lean).

The form of an index claim. An index claim (g, ψ, c, v) says ⟨g ⊗ eq(ψ, ·), W⟩ + ⟨c, η⟩ = v. Here
the pair (c, v) is a form f, with the value v − ⟨c, η⟩. The state function is the chain of relations
between the parts of the block: all claims hold; ∑_j α_j δ_j = 0 (`MG.Joined`; δ_j: `MG.defect`);
the running claim of the sumcheck (`SC.Rsum`); the output claim. Errors are counts (`MG.mergeErr`;
`Alg.count_affine_form_le_pow`).

The layout enters through the structure `TLay`. `TLay.Tn_eq`: a tensor claim is a column claim. That
the layout has this structure: Blocks/Layout.lean. (Variable 0 is the highest bit of a column
number, as in `Alg.bits` and `Blocks.eqN`.)

P indexes the pads; Q is the set of indices of the pads in the pad vectors that have been sent. The
relations for the honest run say that the implicit part of the statement (the matrix and all vectors
sent so far, Blocks/Block.lean) holds the pads in Q, and each block asks that its own pads are in Q.

Notation: `J`: a finite type: it indexes the claims that go in; n is its number of elements
(`Fintype.card J` in `mergeErr`); `l`: a `List ι`: the sumcheck binds the variables of the list, in
this order (`SC.sc`, Blocks/SumCheckBlock.lean); `eqk z b`: eq(z, b) = ∏_v (z_v if b_v = 1, else 1 -
z_v), for a point z and a vertex b of the cube; `eqPt x y`: eq(x, y) for two points; `mle`: the
multilinear extension ~u(z) = ∑_b eq(z, b) u[b]; `corner b`: a vertex of the cube as a point of K^ι;
`num b`: the number of a vertex (these: Alg/Mle.lean); `eqN m off a z` (Blocks/Basic.lean): eq(a, z)
for the m coordinates a (off), .., a (off + m - 1) and the m-bit number z; `Hon.Masked`:
Blocks/BlockHon.lean.

Limits. Left to the segment that uses the merge: the merge of tensor claims as one block. Also left
out: which coefficients (c, v) the forms have, and whether g, ψ and c are computed from verifier
messages alone. Not here: blocks for the first step of the merge of tensor claims (the masked
scalars of the tensor claims) and for the first step of `merge` (the pad vector is sent first);
completeness and masked form of `tensorMerge`.
No challenge of the merge's sumcheck is rejected at 0: its flags are fixed to "nobody divides"
(`MG.sc`: nzv = false); they are no parameter. The output's column factor is eq(ψ, ·); a later block
that divides by a coordinate of ψ (a sumcheck with an equality factor at ψ) would need the premise
"no coordinate of ψ is 0", which `mergeC` does not supply.
-/
import Blocks.SumCheckBlock
import Blocks.BlockFront
import Blocks.EqN
import Alg.Mle
import Alg.Poly
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Blocks

open Iop Prob Alg

/-- The data of a merge. Rw indexes the rows of the hidden matrix and ι the variables of its
columns: a column is a vertex ι → Bool of the hypercube. The matrix is read off the implicit part;
it may be any matrix over E. Each of the rounds of the sumcheck has two masked scalars, with the
pads `idx`. -/
structure MG (E Y P Rw ι : Type) [Field E] where
  forms : Forms E Y P
  mat : Y → Rw → (ι → Bool) → E
  idx : ι → Fin 2 → P

namespace MG

variable {E Y P Rw ι : Type} [Field E] (M : MG E Y P Rw ι)

/-- A column claim: a vector γ on the rows, weights ε on the columns, and a form f. -/
structure CClaim where
  γ : Rw → E
  ε : (ι → Bool) → E
  f : M.forms.Fm

/-- An index claim, in the form that blocks use: ⟨g ⊗ eq(ψ, ·), W⟩ is the value of the form f. -/
structure Idx where
  g : Rw → E
  ψ : ι → E
  f : M.forms.Fm

variable [Fintype Rw]

/-- (γᵀ W)[c] -/
def colSum (γ : Rw → E) (y : Y) : (ι → Bool) → E := fun c => ∑ r, γ r * M.mat y r c

theorem colSum_sum {J : Type} (s : Finset J) (a : J → E) (γ : J → Rw → E) (y : Y) (c : ι → Bool) :
    M.colSum (fun r => ∑ j ∈ s, a j * γ j r) y c = ∑ j ∈ s, a j * M.colSum (γ j) y c := by
  unfold colSum
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun r _ => by ring

variable [Fintype ι] [DecidableEq ι]

variable {M} in
/-- The column claim is true for the implicit part y. -/
def CClaim.Holds (a : M.CClaim) (y : Y) : Prop := M.forms.val y a.f = ∑ c, a.ε c * M.colSum a.γ y c

variable {M} in
/-- The index claim is true for the implicit part y: the value of f is the multilinear extension of
gᵀ W at ψ. -/
def Idx.Holds (a : M.Idx) (y : Y) : Prop := M.forms.val y a.f = mle (M.colSum a.g y) a.ψ

variable {M} in
/-- An index claim is the column claim with the weights eq(ψ, ·). -/
def Idx.toC (a : M.Idx) : M.CClaim := ⟨a.g, eqk a.ψ, a.f⟩

variable {M} in
theorem Idx.holds_toC (a : M.Idx) (y : Y) : a.toC.Holds y ↔ a.Holds y := by
  unfold Idx.Holds CClaim.Holds Idx.toC mle
  exact Iff.rfl

variable (J : Type) [Fintype J] [DecidableEq J]

/-- The true polynomial of the sumcheck of a merge: Φ = ∑_j α_j ε̃_j · (γ_jᵀ W)~. -/
def scPhi (ξ : (J → M.CClaim) × (J → E)) (y : Y) (z : ι → E) : E :=
  ∑ j, ξ.2 j * (mle (ξ.1 j).ε z * mle (M.colSum (ξ.1 j).γ y) z)

/-- The data of the sumcheck of a merge of the claims x_j with the coefficients α_j: plain weights,
degree 2. -/
def sc : SC E Y P ((J → M.CClaim) × (J → E)) ι where
  forms := M.forms
  wt := fun _ => plainW
  e := fun _ => 1
  idx := M.idx
  nzv := fun _ => false

omit [DecidableEq J] in
theorem sc_ok (h : M.forms.OK) : (M.sc J).OK (M.scPhi J) :=
  { forms := h,
    deg := fun _ _ => DegLE.sum _ fun _ _ => DegLE.const_mul _ ((DegLE.mle _).mul (DegLE.mle _)) }

variable [Fintype E] [DecidableEq E]

/-- the start of the sumcheck: the form ∑_j α_j f_j, no point yet -/
@[reducible] def start : Block ((J → M.CClaim) × (J → E)) Y (M.sc J).X Y :=
  Block.pure (fun xa => some (∑ j, xa.2 j • (xa.1 j).f, 0, xa)) id

/-- the output claim, from the verifier's state at the end of the sumcheck -/
def outIdx (x : (M.sc J).X) : M.Idx :=
  ⟨fun r => ∑ j, (x.2.2.2 j * mle (x.2.2.1 j).ε x.2.1) * (x.2.2.1 j).γ r, x.2.1, x.1⟩

omit [DecidableEq J] [Fintype E] [DecidableEq E] in
/-- The output claim says that the end form has the value Φ(ψ). -/
theorem holds_outIdx_iff (x : (M.sc J).X) (y : Y) :
    (M.outIdx J x).Holds y ↔ (M.sc J).Reval (M.scPhi J) x y := by
  have h2 : M.colSum (fun r => ∑ j, (x.2.2.2 j * mle (x.2.2.1 j).ε x.2.1) * (x.2.2.1 j).γ r) y
      = fun c => ∑ j, (x.2.2.2 j * mle (x.2.2.1 j).ε x.2.1) * M.colSum (x.2.2.1 j).γ y c :=
    funext fun c => M.colSum_sum Finset.univ _ _ y c
  have key : mle (M.colSum (M.outIdx J x).g y) x.2.1 = M.scPhi J x.2.2 y x.2.1 := by
    show mle (M.colSum (fun r => ∑ j, (x.2.2.2 j * mle (x.2.2.1 j).ε x.2.1) * (x.2.2.1 j).γ r) y)
        x.2.1 =
      ∑ j, x.2.2.2 j * (mle (x.2.2.1 j).ε x.2.1 * mle (M.colSum (x.2.2.1 j).γ y) x.2.1)
    rw [h2, mle_sum]
    simp only [mle_smul]
    exact Finset.sum_congr rfl fun j _ => by ring
  show M.forms.val y x.1 = mle (M.colSum (M.outIdx J x).g y) x.2.1
    ↔ ((∀ v, (M.sc J).nzv v = true → x.2.1 v ≠ 0) → M.forms.val y x.1 = M.scPhi J x.2.2 y x.2.1)
  rw [key]
  exact ⟨fun h _ => h, fun h => h fun _ hv => (by cases hv)⟩

/-- the verifier computes the output claim -/
@[reducible] def finish : Block (M.sc J).X Y M.Idx Y :=
  Block.pure (fun x => some (M.outIdx J x)) id

/-- The merge of column claims into one index claim; the sumcheck binds the variables of the list l;
the verifier checks nothing. -/
@[reducible] def mergeC (l : List ι) : Block (J → M.CClaim) Y M.Idx Y :=
  (Block.sample (J → M.CClaim) Y E (J → E) fun _ => true).seq
    ((M.start J).seq (((M.sc J).sc l).seq (M.finish J)))

/-- The errors of `mergeC`: |E|^(n−1) of the |E|^n tuples of coefficients, that is a fraction 1/|E|
for n ≥ 1; then 2 values of each coordinate of ψ. -/
def mergeErr (l : List ι) : Err (M.mergeC J l).shape :=
  Err.app (s := (Block.sample (J → M.CClaim) Y E (J → E) fun _ => true).shape)
    (Fintype.card E ^ (Fintype.card J - 1), ())
    (Err.app (s := (M.start J).shape) () (Err.app ((M.sc J).scErr l) (t := (M.finish J).shape) ()))

/-- the defect of a column claim -/
def defect (a : M.CClaim) (y : Y) : E := M.forms.val y a.f - ∑ c, a.ε c * M.colSum a.γ y c

omit [Fintype E] [DecidableEq E] in
theorem holds_iff_defect (a : M.CClaim) (y : Y) : a.Holds y ↔ M.defect a y = 0 := by
  unfold CClaim.Holds defect
  exact sub_eq_zero.symm

/-- the combined claim after the coefficients: ∑_j α_j δ_j = 0 -/
def Joined (xa : (J → M.CClaim) × (J → E)) (y : Y) : Prop := ∑ j, xa.2 j * M.defect (xa.1 j) y = 0

/-- First step of the state function: if not all claims hold, ∑_j α_j δ_j = 0 for at most |E|^(n−1)
tuples α. -/
theorem clean_coeffs :
    (Block.sample (J → M.CClaim) Y E (J → E) fun _ => true).Clean
      (fun x y => ∀ j, (x j).Holds y) (M.Joined J) (Fintype.card E ^ (Fintype.card J - 1), ()) := by
  refine Block.clean_sample
    (fun x y => {α | (fun j => M.defect (x j) y) ≠ 0 ∧ 0 + ∑ j, α j * M.defect (x j) y = 0}) _
    (fun x y => ?_) fun x y α hα _ hJ j => ?_
  · by_cases h : (fun j => M.defect (x j) y) = 0
    · exact le_trans (le_of_eq (cnt_false fun α hα => hα.1 h)) (Nat.zero_le _)
    · exact le_trans (cnt_mono fun α hα => hα.2) (count_affine_form_le_pow 0 _ (Or.inr h))
  · rw [holds_iff_defect]
    by_contra hj
    exact hα ⟨fun h => hj (congrFun h j), by rw [zero_add]; exact hJ⟩

omit [DecidableEq J] [Fintype E] [DecidableEq E] in
/-- Second step, under `hl`, `hall`: the start claim of the sumcheck implies the combined claim. -/
theorem clean_start {l : List ι} (hl : l.Nodup) (hall : ∀ v, v ∈ l) :
    (M.start J).Clean (M.Joined J) ((M.sc J).Rsum (M.scPhi J) l) () := by
  refine Block.clean_pure_iff.2 fun xa y xo hxo hR => ?_
  obtain rfl := Option.some.inj hxo
  have h1 := ((M.sc J).rsum_plain (fun _ => rfl) hl hall _ y).1 hR
  have h2 : M.forms.val y (∑ j, xa.2 j • (xa.1 j).f) =
      ∑ b : ι → Bool,
        ∑ j, xa.2 j * (mle (xa.1 j).ε (corner b) * mle (M.colSum (xa.1 j).γ y) (corner b)) := h1
  simp only [mle_corner, map_sum, map_smul, smul_eq_mul] at h2
  rw [Finset.sum_comm] at h2
  unfold Joined defect
  simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  rw [h2, sub_self]

omit [DecidableEq J] [Fintype E] [DecidableEq E] in
/-- Last step: the output claim is the end claim of the sumcheck. -/
theorem clean_finish : (M.finish J).Clean ((M.sc J).Reval (M.scPhi J)) (fun a y => a.Holds y) () :=
  Block.clean_pure_iff.2 fun x y xo hxo hR => by
    obtain rfl := Option.some.inj hxo
    exact (M.holds_outIdx_iff J x y).1 hR

/-- Soundness of the merge, under `h`, `hl`, `hall`. If the output claim is true and no challenge is
bad, all input claims are true. It holds for every matrix over E and for all vectors in place of the
pad vectors, whatever the number of claims. (Without any claim the input relation is true.) -/
theorem clean_mergeC (h : M.forms.OK) {l : List ι} (hl : l.Nodup) (hall : ∀ v, v ∈ l) :
    (M.mergeC J l).Clean (fun x y => ∀ j, (x j).Holds y) (fun a y => a.Holds y) (M.mergeErr J l) :=
  (M.clean_coeffs J).comp
    ((M.clean_start J hl hall).comp
      (((M.sc J).clean_sc_eval (M.sc_ok J h) l).comp (M.clean_finish J)))

/-! ## Merge, for any number of index claims -/

/-- index claims, read as column claims -/
@[reducible] def asC : Block (J → M.Idx) Y (J → M.CClaim) Y :=
  Block.pure (fun x => some fun j => (x j).toC) id

/-- The merge of index claims, after its pad vector has been sent: n index claims to one. -/
@[reducible] def merge (l : List ι) : Block (J → M.Idx) Y M.Idx Y :=
  (M.asC J).seq (M.mergeC J l)

/-- Soundness of `merge`, round by round, under `h`, `hl`, `hall`, with the relations (R_idx^n,
R_idx), that is from "all n index claims hold" to "the output claim holds" (`Idx.Holds`): at most a
fraction 1/|E| of the tuples (α_i) is bad (for n ≥ 1), and 2 values of each coordinate of ψ. -/
theorem clean_merge (h : M.forms.OK) {l : List ι} (hl : l.Nodup) (hall : ∀ v, v ∈ l) :
    (M.merge J l).Clean (fun x y => ∀ j, (x j).Holds y) (fun a y => a.Holds y)
      (Err.app (s := (M.asC J).shape) () (M.mergeErr J l)) :=
  Block.Clean.comp (Block.clean_pure_iff.2 fun x y xo hxo hR j => by
    obtain rfl := Option.some.inj hxo
    exact ((x j).holds_toC y).1 (hR j)) (M.clean_mergeC J h hl hall)

omit [Fintype Rw] [Fintype J] [DecidableEq J] [Fintype E] [DecidableEq E] in
/-- For index claims the weight of the i-th claim in the output is α_i eq(ψ_i, ψ). -/
theorem mle_toC (a : M.Idx) (z : ι → E) : mle a.toC.ε z = eqPt a.ψ z := mle_eqk a.ψ z

/-! ## The last step of the merge of tensor claims -/

/-- a round with one masked scalar and no challenge that counts -/
abbrev sRound (E : Type) [Zero E] : Round :=
  vRound E Empty (fun a => Empty.elim a) (fun a => Empty.elim a) Unit Unit

omit [Fintype Rw] [Fintype ι] [DecidableEq ι] [Fintype E] in
/-- Renaming: the prover sends a masked scalar, with the pad p, for the value of the form of an
index claim. The claim now has the form of this scalar, and LIN(old form − scalar) is deferred: the
second component of the output. -/
@[reducible] def rename (p : P) : Block M.Idx Y (M.Idx × M.forms.Fm) Y :=
  Block.one (sRound E)
    (fun a _ s => some (⟨a.g, a.ψ, M.forms.scalar (s ()) p⟩, a.f - M.forms.scalar (s ()) p))
    fun y _ _ => y

omit [Fintype E] [DecidableEq E] in
/-- Soundness of renaming: no challenge counts. -/
theorem clean_rename (p : P) :
    (M.rename p).Clean (fun a y => a.Holds y)
      (fun o y => o.1.Holds y ∧ M.forms.val y o.2 = 0) (0, ()) :=
  Block.clean_one (fun _ _ _ => ∅)
      0 (fun _ _ _ => le_of_eq (cnt_false fun _ h => h)) fun a y m c xo _ hxo hRo => by
    obtain rfl := Option.some.inj hxo
    have h1 : M.forms.val y (M.forms.scalar (m.2 ()) p) = mle (M.colSum a.g y) a.ψ := hRo.1
    have h2 : M.forms.val y (a.f - M.forms.scalar (m.2 ()) p) = 0 := hRo.2
    rw [map_sub, sub_eq_zero] at h2
    exact h2.trans h1

/-- The merge of the tensor claims of a segment, after its first step. A tensor claim enters as a
column claim with its γ_a and ε_a, and the form is that of the masked scalar v_a, which the first
step records (there is no block for the first step here). -/
@[reducible] def tensorMerge (l : List ι) (p : P) :
    Block (J → M.CClaim) Y (M.Idx × M.forms.Fm) Y :=
  (M.mergeC J l).seq (M.rename p)

/-- Soundness of the merge of tensor claims, under `h`, `hl`, `hall`: if no challenge is bad, the
deferred LIN is true and the index claim is true, then every tensor claim is true. -/
theorem clean_tensorMerge (h : M.forms.OK) {l : List ι} (hl : l.Nodup) (hall : ∀ v, v ∈ l) (p : P) :
    (M.tensorMerge J l p).Clean (fun x y => ∀ j, (x j).Holds y)
      (fun o y => o.1.Holds y ∧ M.forms.val y o.2 = 0)
      (Err.app (M.mergeErr J l) (t := (M.rename p).shape) (0, ())) :=
  (M.clean_mergeC J h hl hall).comp (M.clean_rename p)

/-! ## The honest prover -/

/-- What the honest prover knows of a column claim: γ and ε. The form is not part of its state,
since it holds scalars that were sent under pads. -/
abbrev Ten (E Rw ι : Type) : Type := (Rw → E) × ((ι → Bool) → E)
/-- the matrix -/
abbrev Mat (E Rw ι : Type) : Type := Rw → (ι → Bool) → E
/-- the honest state before the merge: the pairs (γ_j, ε_j) and the matrix -/
abbrev St0 (E Rw ι J : Type) : Type := (J → Ten E Rw ι) × Mat E Rw ι
/-- the honest state after the coefficients α -/
abbrev St1 (E Rw ι J : Type) : Type := (J → Ten E Rw ι) × Mat E Rw ι × (J → E)
/-- the honest state after the merge: g, ψ and the matrix -/
abbrev St2 (E Rw ι : Type) : Type := ((Rw → E) × (ι → E)) × Mat E Rw ι

omit [Fintype ι] [DecidableEq ι] [Fintype E] in
/-- (γᵀ W)[c], for the prover -/
def colSumW (γ : Rw → E) (W : Mat E Rw ι) : (ι → Bool) → E := fun c => ∑ r, γ r * W r c

omit [DecidableEq J] [Fintype E] in
/-- The honest prover of the sumcheck. -/
def prover : (M.sc J).Prover (St1 E Rw ι J) where
  wt := fun _ => plainW
  Φ := fun a z => ∑ j, a.2.2 j * (mle (a.1 j).2 z * mle (colSumW (a.1 j).1 a.2.1) z)
  deg := fun _ => DegLE.sum _ fun _ _ => DegLE.const_mul _ ((DegLE.mle _).mul (DegLE.mle _))

/-- The public data and the implicit part match the honest state and the pads in Q. -/
def link (Q : Set P) (a : St1 E Rw ι J) (π : P → E) (ξ : (J → M.CClaim) × (J → E)) (y : Y) : Prop :=
  (∀ j, (ξ.1 j).γ = (a.1 j).1 ∧ (ξ.1 j).ε = (a.1 j).2) ∧ ξ.2 = a.2.2 ∧ M.mat y = a.2.1 ∧
    ∀ p ∈ Q, M.forms.val y (M.forms.pad p) = π p

omit [DecidableEq J] [Fintype E] [DecidableEq E] in
theorem phi_link {Q : Set P} {a : St1 E Rw ι J} {π : P → E} {ξ : (J → M.CClaim) × (J → E)} {y : Y}
    (h : M.link J Q a π ξ y) (z : ι → E) :
    M.scPhi J ξ y z = (M.prover J).Φ a z := by
  obtain ⟨h1, h2, h3, -⟩ := h
  show ∑ j, ξ.2 j * (mle (ξ.1 j).ε z * mle (M.colSum (ξ.1 j).γ y) z)
    = ∑ j, a.2.2 j * (mle (a.1 j).2 z * mle (colSumW (a.1 j).1 a.2.1) z)
  refine Finset.sum_congr rfl fun j _ => ?_
  have h4 : M.colSum (ξ.1 j).γ y = colSumW (a.1 j).1 a.2.1 := by
    unfold colSum colSumW; rw [h3, (h1 j).1]
  rw [h2, (h1 j).2, h4]

/-- The statement matches the honest state before the merge, and all its claims are true. -/
def HiC (Q : Set P) (a : St0 E Rw ι J) (π : P → E) (x : J → M.CClaim) (y : Y) : Prop :=
  (∀ j, (x j).γ = (a.1 j).1 ∧ (x j).ε = (a.1 j).2) ∧
  M.mat y = a.2 ∧
  (∀ p ∈ Q, M.forms.val y (M.forms.pad p) = π p) ∧
  ∀ j, (x j).Holds y

/-- The index claim matches the honest state after the merge, and it is true. -/
def HoI (Q : Set P) (b : St2 E Rw ι) (π : P → E) (o : M.Idx) (y : Y) : Prop :=
  o.g = b.1.1 ∧ o.ψ = b.1.2 ∧ M.mat y = b.2 ∧
  (∀ p ∈ Q, M.forms.val y (M.forms.pad p) = π p) ∧ o.Holds y

/-- The honest prover of the merge of column claims. Nothing is withheld. -/
@[reducible] def honMergeC (l : List ι) :
    Hon (M.mergeC J l) P E (St0 E Rw ι J) (St2 E Rw ι) :=
  (Hon.sample (P := P) (E := E) (J → M.CClaim) Y (fun _ => true)
      fun (a : St0 E Rw ι J) (α : J → E) => ((a.1, a.2, α) : St1 E Rw ι J)).seq
    ((Hon.pure (P := P) (E := E) _ _ fun a : St1 E Rw ι J => (a, (0 : ι → E))).seq
      (((M.prover J).sc l []).seq
        (Hon.pure (P := P) (E := E) _ _ fun s : St1 E Rw ι J × (ι → E) =>
          (((fun r => ∑ j, (s.1.2.2 j * mle (s.1.1 j).2 s.2) * (s.1.1 j).1 r, s.2),
            s.1.2.1) : St2 E Rw ι))))

variable [NeZero (2 : E)]

/-- Completeness of the merge, under the hypotheses below and 2 ≠ 0 in E: if all input claims are
true and the prover is honest, the output claim is true, at every value of the challenges and for
all pads. -/
theorem accOn_mergeC (h : M.forms.OK) {l : List ι} (hl : l.Nodup) (hall : ∀ v, v ∈ l)
    {Q : Set P} (hQ : (M.sc J).padsOf l ⊆ Q) :
    (M.honMergeC J l).AccOn (M.HiC J Q) (M.HoI Q) := by
  have a3 := (M.prover J).accOn_sc (Link := M.link J Q) h
    (fun _ => node_injective_one (NeZero.ne 2)) l []
    fun a π ξ y hL => ⟨rfl, fun p hp => hL.2.2.2 p (hQ hp)⟩
  rw [List.append_nil] at a3
  have s2 : ∀ (a : St1 E Rw ι J) (π : P → E) (xa : (J → M.CClaim) × (J → E)) (y : Y),
      (M.link J Q a π xa y ∧ ∀ j, (xa.1 j).Holds y) →
      M.forms.val y (∑ j, xa.2 j • (xa.1 j).f) = sumOutL plainW l ((M.prover J).Φ a) 0 := by
    intro a π xa y hi
    rw [sumOutL_plain l hl hall]
    simp only [← M.phi_link J hi.1]
    show _ = ∑ b : ι → Bool,
        ∑ j, xa.2 j * (mle (xa.1 j).ε (corner b) * mle (M.colSum (xa.1 j).γ y) (corner b))
    simp only [mle_corner, map_sum, map_smul, smul_eq_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hi.2 j, Finset.mul_sum]
  have s4 : ∀ (s : St1 E Rw ι J × (ι → E)) (π : P → E) (x : (M.sc J).X) (y : Y),
      (M.prover J).Hsum (M.link J Q) [] s π x y →
      M.HoI Q (((fun r => ∑ j, (s.1.2.2 j * mle (s.1.1 j).2 s.2) * (s.1.1 j).1 r, s.2),
          s.1.2.1) : St2 E Rw ι)
        π (M.outIdx J x) y := by
    intro s π x y hi
    obtain ⟨hL, hz, -, -, hv⟩ := hi
    have hR : (M.sc J).Reval (M.scPhi J) x y := by
      intro _
      show M.forms.val y x.1 = M.scPhi J x.2.2 y x.2.1
      rw [M.phi_link J hL, hz]; exact hv
    refine ⟨?_, hz, hL.2.2.1, hL.2.2.2, (M.holds_outIdx_iff J x y).2 hR⟩
    funext r
    show ∑ j, (x.2.2.2 j * mle (x.2.2.1 j).ε x.2.1) * (x.2.2.1 j).γ r =
      ∑ j, (s.1.2.2 j * mle (s.1.1 j).2 s.2) * (s.1.1 j).1 r
    rw [hL.2.1, hz]
    exact Finset.sum_congr rfl fun j _ => by rw [(hL.1 j).1, (hL.1 j).2]
  exact Hon.AccOn.comp (R₂ := fun a π xa y => M.link J Q a π xa y ∧ ∀ j, (xa.1 j).Holds y)
    (Hon.accOn_sample _ _ fun a π x y α hi _ => ⟨⟨hi.1, rfl, hi.2.1, hi.2.2.1⟩, hi.2.2.2⟩)
    (Hon.AccOn.comp
      (Hon.accOn_pure fun a π xa y hi =>
        ⟨_, rfl, hi.1, rfl, fun _ _ => one_ne_zero, fun _ hv _ => (by cases hv), s2 a π xa y hi⟩)
      (Hon.AccOn.comp a3 (Hon.accOn_pure fun s π x y hi => ⟨_, rfl, s4 s π x y hi⟩)))

variable [Fintype P] [DecidableEq P]

/-- The simulator of the plain parts of the merge: independent uniform scalars. -/
def simMergeC (l : List ι) :
    Rho (M.mergeC J l).shape → PMF (Plains (M.mergeC J l).shape) :=
  Hon.simSeq (s := (Block.sample (J → M.CClaim) Y E (J → E) fun _ => true).shape)
    (fun _ => PMF.pure ((fun k => Empty.elim k), ()))
    (Hon.simSeq (s := (M.start J).shape) (fun _ => PMF.pure ())
      (Hon.simSeq (s := ((M.sc J).sc l).shape) ((M.sc J).simSc l)
        (t := (M.finish J).shape) fun _ => PMF.pure ()))

omit [NeZero (2 : E)] in
/-- The merge is in masked form, under `hp`, `hl`: it masks with the pads `idx` and reads no other
pad; its plain parts are uniform. -/
theorem masked_mergeC (hp : (M.sc J).PlacesOnce) {l : List ι} (hl : l.Nodup) :
    (M.honMergeC J l).Masked (fun _ => True) ((M.sc J).padsOf l)
      ((M.sc J).padsOf l) (M.simMergeC J l) := by
  have m3 := (M.prover J).masked_sc hp (fun _ => True) l [] hl
  have m34 := m3.comp
    (Hon.masked_pure (P := P) (E := E) (fun x => some (M.outIdx J x)) (id : Y → Y)
      (fun s : St1 E Rw ι J × (ι → E) =>
        (((fun r => ∑ j, (s.1.2.2 j * mle (s.1.1 j).2 s.2) * (s.1.1 j).1 r, s.2),
          s.1.2.1) : St2 E Rw ι)) fun _ => True)
    (fun _ _ _ _ => trivial) (Set.disjoint_empty _) (Set.disjoint_empty _)
  have m234 := (Hon.masked_pure (P := P) (E := E)
      (fun xa : (J → M.CClaim) × (J → E) => some ((∑ j, xa.2 j • (xa.1 j).f, 0, xa) : (M.sc J).X))
      (id : Y → Y) (fun a : St1 E Rw ι J => (a, (0 : ι → E))) fun _ => True).comp
    m34 (fun _ _ _ _ => trivial) (Set.empty_disjoint _) (Set.empty_disjoint _)
  have m := (Hon.masked_sample (P := P) (E := E) (Xi := J → M.CClaim) (Yi := Y)
      (fun _ : J → E => true)
      (fun (a : St0 E Rw ι J) (α : J → E) => ((a.1, a.2, α) : St1 E Rw ι J)) fun _ => True).comp
    m234 (fun _ _ _ _ => trivial) (Set.empty_disjoint _) (Set.empty_disjoint _)
  simp only [Set.empty_union, Set.union_empty] at m
  exact m

/-! ### Renaming -/

omit [Fintype J] [DecidableEq J] [Fintype P] [DecidableEq P] [Fintype E] in
/-- The honest prover of renaming: the value of the claim plus the pad. -/
@[reducible] def honRename (p : P) : Hon (M.rename p) P E (St2 E Rw ι) (St2 E Rw ι) :=
  Hon.one (fun b π => (fun a => Empty.elim a, fun _ => mle (colSumW b.1.1 b.2) b.1.2 + π p))
    (fun b _ => b) ∅ fun _ => ∅

omit [Fintype P] [DecidableEq P] [Fintype E] [DecidableEq E] in
omit [NeZero (2 : E)] in
/-- Completeness of renaming, under `h`, `hpQ`: the new claim and the deferred LIN are true. -/
theorem accOn_rename (h : M.forms.OK) {p : P} {Q : Set P} (hpQ : p ∈ Q) :
    (M.honRename p).AccOn (M.HoI Q) (fun b π o y => M.HoI Q b π o.1 y ∧ M.forms.val y o.2 = 0) :=
  Hon.accOn_one fun b π a y _ hi _ _ => by
    obtain ⟨hg, hψ, hW, hpad, hH⟩ := hi
    have hv : mle (M.colSum a.g y) a.ψ = mle (colSumW b.1.1 b.2) b.1.2 := by
      unfold colSum colSumW; rw [hg, hψ, hW]
    have hs : M.forms.val y (M.forms.scalar (mle (colSumW b.1.1 b.2) b.1.2 + π p) p) =
        mle (M.colSum a.g y) a.ψ := by
      rw [M.forms.val_scalar h, hpad p hpQ, add_sub_cancel_right, hv]
    refine ⟨_, rfl, ⟨hg, hψ, hW, hpad, hs⟩, ?_⟩
    show M.forms.val y (a.f - M.forms.scalar (mle (colSumW b.1.1 b.2) b.1.2 + π p) p) = 0
    rw [map_sub, hs, sub_eq_zero]
    exact hH

omit [DecidableEq E] in
omit [NeZero (2 : E)] in
/-- Renaming is in masked form: one scalar, under the pad p. -/
theorem masked_rename (p : P) :
    (M.honRename p).Masked (fun _ => True) {p} {p}
      (Hon.simOne (r := sRound E) (K := Unit) E id) := by
  have h := Hon.masked_one (r := sRound E)
    (pb := fun (a : M.Idx) _ s =>
        some ((⟨a.g, a.ψ, M.forms.scalar (s ()) p⟩ : M.Idx), a.f - M.forms.scalar (s ()) p))
    (im := fun (y : Y) _ _ => y)
    (msg := fun (b : St2 E Rw ι) (π : P → E) =>
        ((fun a => Empty.elim a, fun _ => mle (colSumW b.1.1 b.2) b.1.2 + π p) : (sRound E).Msg))
    (nx := fun b _ => b) (Bd := ∅) (Wn := fun _ => ∅) (K := Unit) (enc := id) (fun _ => True)
    (fun _ => p) (fun _ _ _ => Subsingleton.elim _ _) (fun b _ _ => mle (colSumW b.1.1 b.2) b.1.2) ∅
    (fun _ _ _ => rfl) (fun _ _ _ _ _ => rfl) (Set.empty_disjoint _)
  have hr : Set.range (fun _ : Unit => p) = {p} := Set.range_const
  rw [Set.empty_union, hr] at h
  exact h

/-! ### The honest prover of `merge` -/

/-- the honest state before `merge`: (g_i, ψ_i) for each claim, and the matrix -/
abbrev StI (E Rw ι J : Type) : Type := (J → (Rw → E) × (ι → E)) × Mat E Rw ι

/-- The honest prover of `merge`. -/
@[reducible] def honMerge (l : List ι) :
    Hon (M.merge J l) P E (StI E Rw ι J) (St2 E Rw ι) :=
  (Hon.pure (P := P) (E := E) _ _ fun a : StI E Rw ι J =>
      ((fun j => ((a.1 j).1, eqk (a.1 j).2), a.2) : St0 E Rw ι J)).seq
    (M.honMergeC J l)

/-- The index claims match the honest state, and all are true. -/
def HiI (Q : Set P) (a : StI E Rw ι J) (π : P → E) (x : J → M.Idx) (y : Y) : Prop :=
  (∀ j, (x j).g = (a.1 j).1 ∧ (x j).ψ = (a.1 j).2) ∧
  M.mat y = a.2 ∧
  (∀ p ∈ Q, M.forms.val y (M.forms.pad p) = π p) ∧
  ∀ j, (x j).Holds y

omit [Fintype P] [DecidableEq P] in
/-- Completeness of `merge` (perfect completeness), under the hypotheses below and 2 ≠ 0 in E, at
every value of the challenges and for all pads. -/
theorem accOn_merge (h : M.forms.OK) {l : List ι} (hl : l.Nodup) (hall : ∀ v, v ∈ l)
    {Q : Set P} (hQ : (M.sc J).padsOf l ⊆ Q) :
    (M.honMerge J l).AccOn (M.HiI J Q) (M.HoI Q) :=
  Hon.AccOn.comp (Hon.accOn_pure fun a π x y hi =>
    ⟨_, rfl, fun j => ⟨(hi.1 j).1, by show eqk (x j).ψ = _; rw [(hi.1 j).2]⟩, hi.2.1, hi.2.2.1,
      fun j => ((x j).holds_toC y).2 (hi.2.2.2 j)⟩) (M.accOn_mergeC J h hl hall hQ)

omit [NeZero (2 : E)] in
/-- `merge` is in masked form, under `hp`, `hl`. -/
theorem masked_merge (hp : (M.sc J).PlacesOnce) {l : List ι} (hl : l.Nodup) :
    (M.honMerge J l).Masked (fun _ => True) ((M.sc J).padsOf l) ((M.sc J).padsOf l)
      (Hon.simSeq (s := (M.asC J).shape) (fun _ => PMF.pure ()) (M.simMergeC J l)) := by
  have m := (Hon.masked_pure (P := P) (E := E) (fun x : J → M.Idx => some fun j => (x j).toC)
      (id : Y → Y)
      (fun a : StI E Rw ι J => ((fun j => ((a.1 j).1, eqk (a.1 j).2), a.2) : St0 E Rw ι J))
      fun _ => True).comp
    (M.masked_mergeC J hp hl) (fun _ _ _ _ => trivial) (Set.empty_disjoint _) (Set.empty_disjoint _)
  simp only [Set.empty_union] at m
  exact m

/-! ## The value of a tensor claim -/

/-- the value of a tensor claim: ∑_c ε(c) (γᵀ W)[c] -/
def tval (a : Ten E Rw ι) (y : Y) : E := ∑ c, a.2 c * M.colSum a.1 y c

end MG

namespace MG

/-! ## The matrix part of an index claim -/

section Lower

variable {E : Type} [Field E]

/-- The matrix part of an index claim, with rows and columns numbered: the first coordinate of ψ
belongs to the most significant bit of the number of the column. -/
theorem mle_colSum_eq (h k : ℕ) (g : Fin h → E) (ψ : Fin k → E) (W : ℕ → ℕ → E) :
    mle (fun c : Fin k → Bool => ∑ r : Fin h, g r * W r (num c)) ψ
      = ∑ y ∈ Finset.range h, ∑ c ∈ Finset.range (2 ^ k), nat g y * eqN k 0 (nat ψ) c * W y c := by
  have h1 : ∀ c : ℕ, ∑ r : Fin h, g r * W r c = ∑ y ∈ Finset.range h, nat g y * W y c := by
    intro c
    rw [← Fin.sum_univ_eq_sum_range fun y => nat g y * W y c]
    refine Finset.sum_congr rfl fun r _ => ?_
    have : nat g r.val = g r := dif_pos r.2
    rw [this]
  rw [← mleN_eq_mle (fun c => ∑ r : Fin h, g r * W r c) ψ]
  unfold mleN
  simp only [h1, Finset.mul_sum, eqN_nat]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun c _ => by ring

end Lower

/-! ## A tensor claim as a column claim -/

/-- What the merge uses of the layout of one unit: the data. I is the set of index tuples of the
tensor. Every tuple splits into a column part and a row part, and the splits are all pairs. Byte b
of the entry i is in the row `row` b iʳ and the column `col` iᶜ. -/
structure TLay (Rw ι : Type) where
  I : Type
  Ic : Type
  Ir : Type
  [finI : Fintype I]
  [finIc : Fintype Ic]
  [finIr : Fintype Ir]
  /-- the number of bytes of an entry -/
  nB : ℕ
  split : I ≃ Ic × Ir
  col : Ic → ι → Bool
  row : Fin nB → Ir → Rw

attribute [instance] TLay.finI TLay.finIc TLay.finIr

namespace TLay

variable {E Rw ι : Type} [Field E] [Fintype Rw] [DecidableEq Rw] [Fintype ι]
  [DecidableEq ι] (T : TLay Rw ι)

omit [Fintype Rw] [DecidableEq Rw] [Fintype ι] [DecidableEq ι] in
/-- the entry i of the tensor that a matrix W' holds: ∑_b 256^b W'[row][column] -/
def entry (W' : Rw → (ι → Bool) → E) (i : T.I) : E :=
  ∑ b : Fin T.nB, (256 : E) ^ (b : ℕ) * W' (T.row b (T.split i).2) (T.col (T.split i).1)

omit [Fintype Rw] [DecidableEq Rw] [Fintype ι] [DecidableEq ι] in
/-- The functional of a tensor claim whose factor is a product over the split: ∑_i fᶜ[iᶜ] fʳ[iʳ] ·
entry i. -/
def Tn (fc : T.Ic → E) (fr : T.Ir → E) (W' : Rw → (ι → Bool) → E) : E :=
  ∑ i, fc (T.split i).1 * fr (T.split i).2 * T.entry W' i

omit [Fintype Rw] [DecidableEq Rw] in
/-- the column weights ε: the sum of fᶜ[iᶜ] over the iᶜ with the column c. If `col` is injective
this is fᶜ[iᶜ] at the column of iᶜ, and it is 0 at every other column. -/
def eps (fc : T.Ic → E) (c : ι → Bool) : E := ∑ ic, if T.col ic = c then fc ic else 0

omit [Fintype Rw] [Fintype ι] [DecidableEq ι] in
/-- the row weights γ: the sum of 256^b fʳ[iʳ] over the (b, iʳ) with the row y. If `row` is
injective this is 256^b fʳ[iʳ] in the row of (b, iʳ), and it is 0 outside the unit. -/
def gam (fr : T.Ir → E) (y : Rw) : E :=
  ∑ b : Fin T.nB, ∑ ir, if T.row b ir = y then (256 : E) ^ (b : ℕ) * fr ir else 0

omit [Fintype Rw] [DecidableEq Rw] [DecidableEq ι] in
/-- If `col` is injective, ε has the value fc iᶜ at the column `col` iᶜ. -/
theorem eps_col (hc : Function.Injective T.col) (fc : T.Ic → E) (ic : T.Ic) :
    T.eps fc (T.col ic) = fc ic := by
  classical
  unfold eps
  rw [Finset.sum_eq_single ic]
  · simp
  · intro ic' _ hb; rw [if_neg fun h => hb (hc h)]
  · intro h; exact absurd (Finset.mem_univ _) h

omit [Fintype Rw] [DecidableEq Rw] [DecidableEq ι] in
theorem eps_of_notMem (fc : T.Ic → E) {c : ι → Bool} (h : c ∉ Set.range T.col) : T.eps fc c = 0 :=
  Finset.sum_eq_zero fun ic _ => if_neg fun e => h ⟨ic, e⟩

omit [Fintype Rw] [Fintype ι] [DecidableEq ι] in
/-- If `row` is injective, γ has the value 256^b · fr iʳ at the row `row` b iʳ. -/
theorem gam_row (hr : Function.Injective fun q : Fin T.nB × T.Ir => T.row q.1 q.2) (fr : T.Ir → E)
    (b : Fin T.nB) (ir : T.Ir) :
    T.gam fr (T.row b ir) = (256 : E) ^ (b : ℕ) * fr ir := by
  classical
  unfold gam
  rw [Finset.sum_eq_single b, Finset.sum_eq_single ir]
  · simp
  · intro ir' _ hne; rw [if_neg fun h => hne (congrArg Prod.snd (hr (a₁ := (b, ir')) (a₂ := (b, ir)) h))]
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro b' _ hne
    exact Finset.sum_eq_zero fun ir' _ =>
      if_neg fun h => hne (congrArg Prod.fst (hr (a₁ := (b', ir')) (a₂ := (b, ir)) h))
  · intro h; exact absurd (Finset.mem_univ _) h

omit [Fintype Rw] [Fintype ι] [DecidableEq ι] in
theorem gam_of_notMem (fr : T.Ir → E) {y : Rw} (h : ∀ b ir, T.row b ir ≠ y) : T.gam fr y = 0 :=
  Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun ir _ => if_neg (h b ir)

omit [Fintype Rw] [DecidableEq ι] in
/-- If ε(c) γ[y] ≠ 0, the cell in the row y and the column c holds a byte of the tensor. -/
theorem cell_of_ne_zero (fc : T.Ic → E) (fr : T.Ir → E) {c : ι → Bool}
    {y : Rw} (h : T.eps fc c * T.gam fr y ≠ 0) :
    ∃ (i : T.I) (b : Fin T.nB), T.col (T.split i).1 = c ∧ T.row b (T.split i).2 = y := by
  have hc : c ∈ Set.range T.col := by
    by_contra hn
    exact h (by rw [T.eps_of_notMem fc hn, zero_mul])
  have hy : ∃ b ir, T.row b ir = y := by
    by_contra hn
    exact h (by rw [T.gam_of_notMem fr fun b ir e => hn ⟨b, ir, e⟩, mul_zero])
  obtain ⟨ic, rfl⟩ := hc
  obtain ⟨b, ir, rfl⟩ := hy
  exact ⟨T.split.symm (ic, ir), b, by simp, by simp⟩

/-- A tensor claim as a sum over columns, for every matrix W', whatever the cells contain that hold
no byte of the tensor. -/
theorem Tn_eq (fc : T.Ic → E) (fr : T.Ir → E) (W' : Rw → (ι → Bool) → E) :
    T.Tn fc fr W' = ∑ c, T.eps fc c * ∑ y, T.gam fr y * W' y c := by
  have hX : ∀ c, ∑ y, T.gam fr y * W' y c =
      ∑ b : Fin T.nB, ∑ ir, (256 : E) ^ (b : ℕ) * fr ir * W' (T.row b ir) c := by
    intro c
    unfold gam
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ir _ => ?_
    simp [ite_mul]
  have hE : ∀ X : (ι → Bool) → E, ∑ c, T.eps fc c * X c = ∑ ic, fc ic * X (T.col ic) := by
    intro X
    unfold eps
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ic _ => ?_
    simp [ite_mul]
  rw [hE]
  simp only [hX]
  unfold Tn entry
  rw [Equiv.sum_comp T.split fun p : T.Ic × T.Ir =>
        fc p.1 * fr p.2 * ∑ b : Fin T.nB, (256 : E) ^ (b : ℕ) * W' (T.row b p.2) (T.col p.1),
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun ic _ => ?_
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun ir _ => by ring

/-- the pair (γ, ε) with which a tensor claim enters the merge -/
def toTen (fc : T.Ic → E) (fr : T.Ir → E) : Ten E Rw ι := (T.gam fr, T.eps fc)

/-- The value of that pair is the functional of the tensor claim on the matrix of the implicit
part. -/
theorem tval_toTen {Y P : Type} (M : MG E Y P Rw ι) (fc : T.Ic → E) (fr : T.Ir → E) (y : Y) :
    M.tval (T.toTen fc fr) y = T.Tn fc fr (M.mat y) := (T.Tn_eq fc fr (M.mat y)).symm

end TLay

end MG

end Blocks
