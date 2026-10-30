-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/ProductBlock.lean: the product layer as a block, with soundness, completeness and masked form
(`Hon.Masked`, Blocks/BlockHon.lean).

Given two vectors f0, f1 of length 2^g, a point ϱ of earlier challenges and an affine form C, a
product layer reduces the claim val(C) = ∑_X eq(ϱ, X) f0[X] f1[X] to claims on the multilinear
extensions ~f0, ~f1 at one point ϱ̂. It runs a masked sumcheck of g rounds and degree 2
(Blocks/SumCheckBlock.lean), with end point ϱ̂ and end form C'. Then the prover sends two masked
scalars v0, v1, honestly ~f0(ϱ̂) and ~f1(ϱ̂), and the verifier a challenge ζ. The verifier adds v0
and v1 as opened forms and the claim REL(C'; v0 v1), that is val(C') = val(v0) val(v1), to its list
of deferred claims (`Ledger`, Blocks/Form.lean), and outputs the point (ζ | ϱ̂) and the form (1 - ζ)
v0 + ζ v1. If f0, f1 are the halves of a vector f, the claimed value of that form is ~f(ζ | ϱ̂), so
layers can follow one another (words of this library: lean/GLOSSARY.md).

The block `PL.pl` has two soundness theorems (`Block.Clean`, Blocks/Block.lean) with the same input
relation `PL.Rin`, which has the premise that no coordinate of ϱ is 0. In both at most 2 values of
each round challenge are bad. Neither asks anything of the flags `nz`.
  `PL.clean_pl_a`: output relation: all deferred claims are true and (val v0, val v1) is the true
      pair. No value of ζ is bad.
  `PL.clean_pl_b`: output relation: all deferred claims are true and, if no coordinate of the next
      point that the verifier has tested is 0, the next form has the value (1 - ζ) ~f0(ϱ̂) + ζ
      ~f1(ϱ̂). At most one value of ζ is bad. If all coordinates are tested, this premise is that
      of `PL.Rin` of a next layer.

Completeness, outside the withheld set (`Hon.withheld`, Blocks/BlockHon.lean), is
`PL.Prover.accOn_pl`, which needs 2 ≠ 0 in E and two conditions on how the caller's prover stores
its state (`hset`, `hInv`); masked form is `PL.Prover.masked_pl`, if no pad of the layer is used
twice. All four ask that the list `ord`, the order in which the rounds bind the variables, names
each variable once.

The true vectors are not part of the protocol's record `PL`: they are functions of public data and
of the implicit part (`PL.Vecs`), and only the relations mention them. A sumcheck with a factor
eq(ϱ, ·) divides by the coordinates of ϱ, so the flags `nz` say by which coordinates of the next
point a later block divides: there the verifier rejects a challenge 0, which is in the withheld set.
Before it extends the list, the verifier also checks that no deferred claim refers to an opened form
beyond the end of the opened forms (`Ledger.wf`).
-/
import Blocks.SumCheckBlock
import Blocks.EqN
import Blocks.Form
import Blocks.Ext
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Blocks

open Iop Prob Alg

/-! ## 1. A sumcheck changes neither the public data nor the implicit part -/

namespace SC

variable {E Y P Ξ ι : Type} [Field E] [Fintype E] [DecidableEq E] [DecidableEq ι] (S : SC E Y P Ξ ι)

omit [Fintype E] in
/-- One round passes the public data on unchanged. -/
theorem data_of_pb {i : ι} {x xo : S.X} {r : E}
    {m : Fin (S.e i + 1) → E} (h : S.pb i x r m = some xo) : xo.2.2 = x.2.2 := by
  unfold pb at h
  by_cases hr : S.nzv i = true ∧ r = 0
  · rw [if_pos hr] at h
    exact absurd h (by simp)
  · rw [if_neg hr] at h
    rw [← Option.some.inj h]

/-- The public data are passed on unchanged. -/
theorem data_of_pub_sc :
    ∀ (l : List ι) (x xo : S.X) (ρ : Rho (S.sc l).shape) (p : Plains (S.sc l).shape),
      (S.sc l).pub x ρ p = some xo → xo.2.2 = x.2.2
  | [], x, xo, _, _, h => by rw [← Option.some.inj h]
  | i :: l, x, xo, ρ, p, h => by
      obtain ⟨x', hx', hxo⟩ := Option.bind_eq_some_iff.mp h
      exact (data_of_pub_sc l x' xo _ _ hxo).trans (S.data_of_pb hx')

/-- The implicit part does not change. -/
theorem imp_sc : ∀ (l : List ι) (y : Y) (τ : Tr (S.sc l).shape), (S.sc l).imp y τ = y
  | [], _, _ => rfl
  | _ :: l, y, _ => imp_sc l y _

end SC

/-! ## 2. Multilinear extensions of vectors that are indexed by numbers, at points that are
sequences -/

namespace PL

section Ext

variable {E : Type} [Field E]

/-- The extension ~f(z) of Blocks/Ext.lean, in the notation of the algebra library. -/
theorem ext_eq_mleN (g : ℕ) (f z : ℕ → E) : ext g f z = Alg.mleN f fun t : Fin g => z t := by
  unfold ext Alg.mleN
  refine Finset.sum_congr rfl fun X _ => ?_
  rw [eqN_eq]
  simp only [Nat.zero_add]

/-- The extension depends on the first g coordinates of the point only. -/
theorem ext_congr_pt {g : ℕ} {z z' : ℕ → E} (h : ∀ t < g, z t = z' t) (f : ℕ → E) :
    ext g f z = ext g f z' := by
  rw [ext_eq_mleN, ext_eq_mleN,
    show (fun t : Fin g => z t) = fun t : Fin g => z' t from funext fun t => h t t.2]

/-- It has degree at most 1 in each coordinate. -/
theorem degLE_ext (g : ℕ) (f : ℕ → E) : DegLE (fun _ => 1) (ext g f) := by
  have h1 : DegLE (fun _ => 1) (fun x : Fin g → E => Alg.mleN f x) := by
    simp only [Alg.mleN_eq_mle]
    exact DegLE.mle _
  have h2 := h1.comp (fun t : Fin g => (t : ℕ)) Fin.val_injective (fun _ => 1) fun _ => le_rfl
  rwa [show (fun z : ℕ → E => Alg.mleN f fun t : Fin g => z t) = ext g f
      from funext fun z => (ext_eq_mleN g f z).symm] at h2

/-- The start claim of a product layer: summing ~f0 ~f1 out over the g variables, with the weights
of the equality factor eq(ϱ, ·), gives ∑_X eq(ϱ, X) f0[X] f1[X]. -/
theorem sumOutL_ext_mul (g : ℕ) (ϱ f0 f1 z : ℕ → E) :
    sumOutL (eqW ϱ) (vars g) (fun x => ext g f0 x * ext g f1 x) z =
      ext g (fun X => f0 X * f1 X) ϱ := by
  have h1 := sumOutL_comp (fun t : Fin g => (t : ℕ)) Fin.val_injective (eqW ϱ)
    (fun x : Fin g → E => Alg.mleN f0 x * Alg.mleN f1 x) (List.finRange g) z
  have h2 := sumOutL_eq (fun t : Fin g => ϱ t) (List.finRange g) (List.nodup_finRange g)
    (List.mem_finRange) (fun x : Fin g → E => Alg.mleN f0 x * Alg.mleN f1 x) (fun t : Fin g => z t)
  simp only [ext_eq_mleN]
  refine h1.trans (h2.trans ?_)
  simp only [Alg.mleN_eq_mle, Alg.mle_corner]
  rfl

/-- Summing out does not depend on the order of the variables (in a list without repetition). -/
theorem sumOutL_perm {ι K : Type} [DecidableEq ι] [Field K] (wt : ι → Bool → K) {l l' : List ι}
    (h : l.Perm l') (hl : l'.Nodup) (G : (ι → K) → K) (z : ι → K) :
    sumOutL wt l G z = sumOutL wt l' G z := by
  rw [sumOutL_eq_sum_powerset wt l (h.nodup_iff.mpr hl),
    sumOutL_eq_sum_powerset wt l' hl, List.toFinset_eq_of_perm _ _ h]

/-- The start claim of a product layer, whatever the order in which the rounds bind the
variables. -/
theorem sumOutL_ext_mul_of_perm {g : ℕ} {l : List ℕ} (hl : l.Perm (vars g)) (ϱ f0 f1 z : ℕ → E) :
    sumOutL (eqW ϱ) l (fun x => ext g f0 x * ext g f1 x) z = ext g (fun X => f0 X * f1 X) ϱ :=
  (sumOutL_perm _ hl (nodup_vars g) _ z).trans (sumOutL_ext_mul g ϱ f0 f1 z)

end Ext

end PL

/-! ## 3. Adding a product claim to the list of deferred claims -/

namespace Ledger

variable {N E : Type}

/-- Every term of every REL names opened forms that are on the list. The verifier can test this. -/
def wf (x : Ledger N E) : Bool :=
  x.rel.all fun r => r.2.all fun t => decide (t.2.1 < x.opn.length) && decide (t.2.2 < x.opn.length)

/-- The list with two more opened forms a, b and the claim REL(f; a · b). -/
def addProd [One E] (x : Ledger N E) (f a b : Form N E) : Ledger N E :=
  ⟨x.lin, x.opn ++ [a, b], x.rel ++ [(f, [(1, x.opn.length, x.opn.length + 1)])]⟩

/-- The test, written out. -/
theorem wf_iff {x : Ledger N E} :
    x.wf = true ↔ ∀ r ∈ x.rel, ∀ t ∈ r.2, t.2.1 < x.opn.length ∧ t.2.2 < x.opn.length := by
  unfold wf
  simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq]

/-- If the list passes the test, the longer list passes it again. -/
theorem wf_addProd [One E] {x : Ledger N E} (h : x.wf = true) (f a b : Form N E) :
    (x.addProd f a b).wf = true := by
  rw [wf_iff] at h ⊢
  intro r hr t ht
  have hlen : (x.addProd f a b).opn.length = x.opn.length + 2 := by simp [addProd]
  rw [hlen]
  rcases List.mem_append.mp hr with hr | hr
  · have := h r hr t ht
    omega
  · obtain rfl := List.mem_singleton.mp hr
    obtain rfl := List.mem_singleton.mp ht
    exact ⟨by show x.opn.length < _; omega, by show x.opn.length + 1 < _; omega⟩

variable [Fintype N] [CommRing E]

/-- If the list passes the test, the longer list says: what the list said, and val f = val a · val
b. -/
theorem true_addProd {x : Ledger N E} (h : x.wf = true) (f a b : Form N E) (y : N → E) :
    (x.addProd f a b).True y ↔ x.True y ∧ Form.val y f = Form.val y a * Form.val y b := by
  rw [wf_iff] at h
  have hold : ∀ i < x.opn.length, (x.addProd f a b).opv y i = x.opv y i := fun i hi => by
    unfold opv addProd
    rw [List.getD_append _ _ _ _ hi]
  have ha : (x.addProd f a b).opv y x.opn.length = Form.val y a := by
    unfold opv addProd
    rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]
    rfl
  have hb : (x.addProd f a b).opv y (x.opn.length + 1) = Form.val y b := by
    unfold opv addProd
    rw [List.getD_append_right _ _ _ _ (Nat.le_succ _),
      show x.opn.length + 1 - x.opn.length = 1 by omega]
    rfl
  have hts : ∀ r ∈ x.rel,
      termSum ((x.addProd f a b).opv y) r.2 = termSum (x.opv y) r.2 := fun r hr => by
    unfold termSum
    refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
    rw [hold _ (h r hr t ht).1, hold _ (h r hr t ht).2]
  have hnew : termSum ((x.addProd f a b).opv y) [(1, x.opn.length, x.opn.length + 1)] =
      Form.val y a * Form.val y b := by
    simp [termSum, ha, hb]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨h1, fun r hr => ?_⟩, ?_⟩
    · rw [← hts r hr]
      exact h2 r (List.mem_append_left _ hr)
    · rw [← hnew]
      exact h2 (f, _) (List.mem_append_right _ (List.mem_singleton.mpr rfl))
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨h1, fun r hr => ?_⟩
    rcases List.mem_append.mp hr with hr | hr
    · rw [hts r hr]
      exact h2 r hr
    · obtain rfl := List.mem_singleton.mp hr
      exact h3.trans hnew.symm

end Ledger

/-! ## 4. The product layer: the data -/

/-- The parameters of a product layer. The shape of the protocol depends on `ord` (g rounds and one
more, under `OrdOK`); which pads mask its scalars is given by `idx` and `pv`. These are values: no
type depends on them. The type Ξ of the public data occurs in no field; it fixes the type of the
statements. -/
structure PL (E Y P N Ξ : Type) where
  /-- the number of variables: the vectors have length 2^g -/
  g : ℕ
  /-- the order in which the rounds bind the variables 0, .., g - 1 (variable t belongs to
  coordinate t of the point ϱ; coordinate 0 belongs to the top bit of the index) -/
  ord : List ℕ := PL.vars g
  /-- which coordinates of the next point (ζ | ϱ̂) are rejected at 0 (those by which a later block
  divides): coordinate 0 is ζ, coordinate t + 1 is the challenge of the round that binds the
  variable t -/
  nz : ℕ → Bool
  /-- the entries of the vectors and pad vectors, read off the implicit part -/
  proj : Y → N → E
  /-- where the pads are among the entries -/
  place : P → N
  /-- the pads of the two scalars of the round that binds the variable t -/
  idx : ℕ → Fin 2 → P
  /-- the pads of v0 (false) and v1 (true) -/
  pv : Bool → P

/-- The true vectors f0, f1 of a product layer: functions of the public data and the implicit part.
They are not part of the protocol (the structure PL holds what the verifier and the format of the
messages need): the relations of a layer are about them. -/
structure PL.Vecs (E Y Ξ : Type) where
  f0 : Ξ → Y → ℕ → E
  f1 : Ξ → Y → ℕ → E

/-- The explicit part of a statement between product layers. -/
structure PLX (N E Ξ : Type) where
  /-- the running form -/
  C : Form N E
  /-- the point ϱ -/
  pt : ℕ → E
  /-- the deferred claims -/
  led : Ledger N E
  /-- other public data -/
  pub : Ξ

/-- The point (ζ | z): ζ first. -/
def consPt {E : Type} (ζ : E) (z : ℕ → E) : ℕ → E
  | 0 => ζ
  | t + 1 => z t

/-- The two halves of a vector (top bit 0, 1): ~f(ζ | z) = (1 - ζ) ~f0(z) + ζ ~f1(z), where f0[X] =
f[X] and f1[X] = f[X + 2^g]. So for the halves of a vector f of length 2^(g+1) the next start claim
of a product layer says that the next start form has the value ~f at the next point. -/
theorem ext_succ_consPt {E : Type} [Field E] (g : ℕ) (f : ℕ → E) (ζ : E) (z : ℕ → E) :
    ext (g + 1) f (consPt ζ z) = (1 - ζ) * ext g f z + ζ * ext g (fun X => f (X + 2 ^ g)) z := by
  have hs : ∀ b, eqN g (0 + 1) (consPt ζ z) b = eqN g 0 z b := fun b => by
    unfold eqN
    refine Finset.prod_congr rfl fun t _ => ?_
    rw [show 0 + 1 + t = t + 1 by omega, Nat.zero_add]
    rfl
  have h0 : eqN 1 0 (consPt ζ z) 0 = 1 - ζ := by simp [eqN, consPt]
  have h1 : eqN 1 0 (consPt ζ z) 1 = ζ := by simp [eqN, consPt]
  unfold ext
  rw [pow_succ, Nat.mul_comm, Alg.sum_range_mul_add 2 (2 ^ g), Finset.sum_range_succ,
    Finset.sum_range_one, Finset.mul_sum, Finset.mul_sum, Nat.add_comm g 1]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun b hb => ?_)
    (Finset.sum_congr rfl fun b hb => ?_)
  · rw [eqN_append' 1 g 0 _ 0 (Finset.mem_range.mp hb), h0, hs, Nat.zero_mul,
      Nat.zero_add, mul_assoc]
  · rw [eqN_append' 1 g 0 _ 1 (Finset.mem_range.mp hb), h1, hs, Nat.one_mul,
      Nat.add_comm (2 ^ g) b, mul_assoc]

namespace PL

variable {E Y P N Ξ : Type} [Field E] [Fintype E] [DecidableEq E] [Fintype N] [DecidableEq N]
  (L : PL E Y P N Ξ) (T : PL.Vecs E Y Ξ)

/-- The order of the rounds names every variable once. A premise of soundness, completeness and
masked form, and of the count of the rounds. -/
def OrdOK : Prop := L.ord.Perm (vars L.g)

omit [Field E] [Fintype E] [DecidableEq E] [Fintype N] [DecidableEq N] in
theorem OrdOK.mem {L : PL E Y P N Ξ} (h : L.OrdOK) {v : ℕ} : v ∈ L.ord ↔ v < L.g :=
  (List.Perm.mem_iff h).trans mem_vars

omit [Field E] [Fintype E] [DecidableEq E] [Fintype N] [DecidableEq N] in
theorem OrdOK.nodup {L : PL E Y P N Ξ} (h : L.OrdOK) : L.ord.Nodup :=
  (List.Perm.nodup_iff h).mpr (nodup_vars L.g)

omit [Field E] [Fintype E] [DecidableEq E] [Fintype N] [DecidableEq N] in
theorem OrdOK.length {L : PL E Y P N Ξ} (h : L.OrdOK) : L.ord.length = L.g :=
  (List.Perm.length_eq h).trans (length_vars L.g)

/-- The public data of the sumcheck of the layer: the point ϱ, the list, the other public
data. -/
abbrev Pub (_ : PL E Y P N Ξ) : Type := (ℕ → E) × Ledger N E × Ξ

/-- The true polynomial of the sumcheck of the layer: ~f0 ~f1. -/
@[reducible] def scPhi (ξ : L.Pub) (y : Y) (z : ℕ → E) : E :=
  ext L.g (T.f0 ξ.2.2 y) z * ext L.g (T.f1 ξ.2.2 y) z

/-- The format of the sumcheck of the layer: with the equality factor eq(ϱ, ·), two scalars in each
round. The challenge of the round that binds the variable v is rejected at 0 if nz is set at the
coordinate v + 1 of the next point. -/
@[reducible] def sc : SC E Y P L.Pub ℕ where
  forms := Forms.ofForm L.proj L.place
  wt ξ := eqW ξ.1
  e _ := 1
  idx := L.idx
  nzv v := L.nz (v + 1) && decide (v < L.g)

omit [Fintype E] [DecidableEq E] in
/-- The parameters of the sumcheck are in order: ~f0 ~f1 has degree at most 2 in each variable. -/
theorem sc_ok : L.sc.OK (L.scPhi T) :=
  { forms := Forms.ofForm_ok _ _,
    deg := fun ξ y => (degLE_ext L.g (T.f0 ξ.2.2 y)).mul (degLE_ext L.g (T.f1 ξ.2.2 y)) }

omit [Fintype E] [DecidableEq E] in
/-- The challenge of a variable v below g is rejected at 0 if nz is set at v + 1. -/
theorem nzv_iff {v : ℕ} : L.sc.nzv v = true ↔ L.nz (v + 1) = true ∧ v < L.g := by
  show (L.nz (v + 1) && decide (v < L.g)) = true ↔ _
  rw [Bool.and_eq_true, decide_eq_true_eq]

/-- The public test of ζ. -/
def okE (r : E) : Bool := !L.nz 0 || decide (r ≠ 0)

omit [Fintype E] [Fintype N] [DecidableEq N] in
/-- A challenge that has passed the test is not 0, if nz is set. -/
theorem ne_zero_of_okE {r : E} (h : L.okE r = true) (hnz : L.nz 0 = true) : r ≠ 0 := by
  unfold okE at h
  rw [hnz] at h
  simpa using h

omit [Fintype E] [Fintype N] [DecidableEq N] in
/-- A challenge other than 0 passes the test. -/
theorem okE_of_ne_zero {r : E} (h : L.nz 0 = true → r ≠ 0) : L.okE r = true := by
  unfold okE
  cases hnz : L.nz 0
  · rfl
  · simpa using h hnz

/-! ## 5. Soundness of the rounds -/

/-- All deferred claims are true. -/
def LedTrue (x : L.sc.X) (y : Y) : Prop := x.2.2.2.1.True (L.proj y)

/-- The sumcheck of the layer, with the list: from the start claim to the end claim, at most 2
bad values in each round. -/
theorem clean_rounds :
    (L.sc.sc L.ord).Clean (fun x y => L.sc.Rsum (L.scPhi T) L.ord x y ∧ L.LedTrue x y)
      (fun x y => L.sc.Reval (L.scPhi T) x y ∧ L.LedTrue x y) (L.sc.scErr L.ord) :=
  (L.sc.clean_sc_eval (L.sc_ok T) L.ord).frame fun x y τ xo hxo _ _ hS => by
    unfold LedTrue at hS ⊢
    rwa [L.sc.data_of_pub_sc _ _ _ _ _ hxo, L.sc.imp_sc] at hS

/-! ## 6. The last round: v0, v1 and ζ -/

variable (E) in
/-- The prover sends two masked scalars v0 (false) and v1 (true); then ζ. -/
abbrev rV : Round := vRound E Empty (fun a => Empty.elim a) (fun a => Empty.elim a) Bool E

/-- The explicit part after a product layer: the statement for the next layer, and the value forms
of v0 and v1. -/
abbrev XOut (N' E' Ξ' : Type) : Type := PLX N' E' Ξ' × Form N' E' × Form N' E'

/-- The value forms of v0 and v1. -/
def vform (s : Bool → E) (b : Bool) : Form N E := Form.masked (s b) (L.place (L.pv b))

/-- What the verifier computes at the end of the layer: the next start form (1 - ζ) v0 + ζ v1, the
next point (ζ | ϱ̂), and the list with OPEN(v0), OPEN(v1), REL(C'; v0 v1). -/
def out (x : L.sc.X) (ζ : E) (s : Bool → E) : XOut N E Ξ :=
  (⟨(1 - ζ) • L.vform s false + ζ • L.vform s true,
      consPt ζ x.2.1,
      x.2.2.2.1.addProd x.1 (L.vform s false) (L.vform s true),
      x.2.2.2.2⟩,
    L.vform s false, L.vform s true)

/-- The last round of a product layer. The verifier rejects if ζ fails the test, or if the list
names opened forms that are not there. -/
@[reducible] def fin : Block L.sc.X Y (XOut N E Ξ) Y :=
  Block.one (rV E) (fun x ζ s => if L.okE ζ && x.2.2.2.1.wf then some (L.out x ζ s) else none)
    (fun y _ _ => y)

/-- After the layer, relation (a): all deferred claims are true, and v0, v1 have the values ~f0(ϱ̂),
~f1(ϱ̂). The end point ϱ̂ is the next point without its first coordinate. -/
def Ra (xo : XOut N E Ξ) (y : Y) : Prop :=
  xo.1.led.True (L.proj y) ∧
  Form.val (L.proj y) xo.2.1 = ext L.g (T.f0 xo.1.pub y) (fun t => xo.1.pt (t + 1)) ∧
  Form.val (L.proj y) xo.2.2 = ext L.g (T.f1 xo.1.pub y) (fun t => xo.1.pt (t + 1))

/-- After the layer, relation (b): all deferred claims are true, and, if no coordinate of the next
point (ζ | ϱ̂) at which nz is set is 0, the next start form has the value (1 - ζ) ~f0(ϱ̂) + ζ
~f1(ϱ̂). -/
def Rb (xo : XOut N E Ξ) (y : Y) : Prop :=
  xo.1.led.True (L.proj y) ∧
  ((∀ t < L.g + 1, L.nz t = true → xo.1.pt t ≠ 0) →
    Form.val (L.proj y) xo.1.C =
      (1 - xo.1.pt 0) * ext L.g (T.f0 xo.1.pub y) (fun t => xo.1.pt (t + 1)) +
        xo.1.pt 0 * ext L.g (T.f1 xo.1.pub y) (fun t => xo.1.pt (t + 1)))

omit [Fintype E] in
/-- If the verifier of the last round does not reject, then ζ has passed its test, the list is
well-formed (`Ledger.wf`), and the output is `out`. -/
theorem fin_some {x : L.sc.X} {ζ : E} {s : Bool → E} {xo : XOut N E Ξ}
    (h : (if L.okE ζ && x.2.2.2.1.wf then some (L.out x ζ s) else none) = some xo) :
    L.okE ζ = true ∧ x.2.2.2.1.wf = true ∧ xo = L.out x ζ s := by
  by_cases hg : (L.okE ζ && x.2.2.2.1.wf) = true
  · rw [if_pos hg] at h
    exact ⟨(Bool.and_eq_true _ _ ▸ hg).1, (Bool.and_eq_true _ _ ▸ hg).2, (Option.some.inj h).symm⟩
  · rw [if_neg hg] at h
    exact absurd h (by simp)

/-- If the relation of the REL is true and (val v0, val v1) is the true pair, then the end claim of
the sumcheck is true. No value of ζ is bad. -/
theorem clean_fin_a :
    L.fin.Clean (fun x y => L.sc.Reval (L.scPhi T) x y ∧ L.LedTrue x y) (L.Ra T) (0, ()) := by
  refine Block.clean_one (fun _ _ _ => ∅) 0
    (fun _ _ _ => le_of_eq (cnt_false fun _ h => h)) fun x y m c xo _ hxo hRo => ?_
  obtain ⟨_, hwf, rfl⟩ := L.fin_some hxo
  obtain ⟨hled, h0, h1⟩ := hRo
  have h2 := (Ledger.true_addProd hwf x.1 (L.vform m.2 false) (L.vform m.2 true) (L.proj y)).mp hled
  have h0' : Form.val (L.proj y) (L.vform m.2 false) = ext L.g (T.f0 x.2.2.2.2 y) x.2.1 := h0
  have h1' : Form.val (L.proj y) (L.vform m.2 true) = ext L.g (T.f1 x.2.2.2.2 y) x.2.1 := h1
  refine ⟨fun _ => ?_, h2.1⟩
  exact h2.2.trans (by rw [h0', h1'])

/-- (val v0, val v1) is the true pair (~f0(ϱ̂), ~f1(ϱ̂)). -/
def TruePair (x : L.sc.X) (y : Y) (s : Bool → E) : Prop :=
  Form.val (L.proj y) (L.vform s false) = ext L.g (T.f0 x.2.2.2.2 y) x.2.1 ∧
  Form.val (L.proj y) (L.vform s true) = ext L.g (T.f1 x.2.2.2.2 y) x.2.1

/-- The bad values of ζ: the pair is not the true pair, and the affine functions (1 - ζ) val v0 + ζ
val v1 and (1 - ζ) ~f0(ϱ̂) + ζ ~f1(ϱ̂) agree at ζ. -/
def badZ (x : L.sc.X) (y : Y) (s : Bool → E) : Set E :=
  {ζ | ¬ (L.TruePair T) x y s ∧
    (1 - ζ) * Form.val (L.proj y) (L.vform s false) + ζ * Form.val (L.proj y) (L.vform s true) =
      (1 - ζ) * ext L.g (T.f0 x.2.2.2.2 y) x.2.1 + ζ * ext L.g (T.f1 x.2.2.2.2 y) x.2.1}

/-- Two different affine functions agree at no more than one point. -/
theorem cnt_badZ (x : L.sc.X) (y : Y) (s : Bool → E) : cnt (fun ζ => ζ ∈ (L.badZ T) x y s) ≤ 1 := by
  by_cases hp : (L.TruePair T) x y s
  · rw [cnt_false fun ζ hζ => hζ.1 hp]
    exact Nat.zero_le _
  · refine le_trans (cnt_mono fun ζ hζ => ?_) (Alg.count_affine_le_one
      (Form.val (L.proj y) (L.vform s false) - ext L.g (T.f0 x.2.2.2.2 y) x.2.1)
      ((Form.val (L.proj y) (L.vform s true) - ext L.g (T.f1 x.2.2.2.2 y) x.2.1)
        - (Form.val (L.proj y) (L.vform s false) - ext L.g (T.f0 x.2.2.2.2 y) x.2.1)) ?_)
    · linear_combination hζ.2
    · by_contra hcon
      push Not at hcon
      exact hp
        ⟨sub_eq_zero.mp hcon.1, sub_eq_zero.mp (by rw [hcon.1, sub_zero] at hcon; exact hcon.2)⟩

omit [Fintype E] [DecidableEq E] in
/-- The backward step at ζ. Suppose that ζ is not bad, that the list passes the test, that the
longer list is true and that the next start form has the value (1 - ζ) ~f0(ϱ̂) + ζ ~f1(ϱ̂). Then the
list is true and the end form of the sumcheck has the value ~f0(ϱ̂) ~f1(ϱ̂). -/
theorem back_fin {x : L.sc.X} {y : Y} {s : Bool → E} {c : E} (hc : c ∉ (L.badZ T) x y s)
    (hwf : x.2.2.2.1.wf = true) (hled : (L.out x c s).1.led.True (L.proj y))
    (h3 : Form.val (L.proj y) ((1 - c) • L.vform s false + c • L.vform s true) =
      (1 - c) * ext L.g (T.f0 x.2.2.2.2 y) x.2.1 + c * ext L.g (T.f1 x.2.2.2.2 y) x.2.1) :
    Form.val (L.proj y) x.1 = ext L.g (T.f0 x.2.2.2.2 y) x.2.1 * ext L.g (T.f1 x.2.2.2.2 y) x.2.1 ∧
    L.LedTrue x y := by
  have h2 := (Ledger.true_addProd hwf x.1 (L.vform s false) (L.vform s true) (L.proj y)).mp hled
  have h5 : (L.TruePair T) x y s := by
    by_contra hne
    refine hc ⟨hne, ?_⟩
    rw [← h3, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  exact ⟨h2.2.trans (by rw [h5.1, h5.2]), h2.1⟩

/-- Soundness of the last round with relation (b): at most one value of ζ is bad. The relation after
the layer has the premise that no coordinate of the next point that the verifier has tested is 0. If
all are tested, that is the premise of the relation before the next layer. -/
theorem clean_fin_b :
    L.fin.Clean (fun x y => L.sc.Reval (L.scPhi T) x y ∧ L.LedTrue x y) (L.Rb T) (1, ()) := by
  refine Block.clean_one (fun x y m => (L.badZ T) x y m.2) 1
    (fun x y m => (L.cnt_badZ T) x y m.2) fun x y m c xo hc hxo hRo => ?_
  obtain ⟨hok, hwf, rfl⟩ := L.fin_some hxo
  have hT : L.LedTrue x y :=
    ((Ledger.true_addProd hwf x.1 (L.vform m.2 false) (L.vform m.2 true) (L.proj y)).mp hRo.1).1
  refine ⟨fun hA => ?_, hT⟩
  exact ((L.back_fin T) hc hwf hRo.1 (hRo.2 fun t ht hnz => by
    cases t with
    | zero => exact L.ne_zero_of_okE hok hnz
    | succ t => exact hA t (L.nzv_iff.mpr ⟨hnz, by omega⟩))).1

/-! ## 7. The product layer -/

/-- The statement of the layer as a statement of its sumcheck. -/
@[reducible] def init : Block (PLX N E Ξ) Y L.sc.X Y :=
  Block.pure (fun x => some (x.C, fun _ => 0, (x.pt, x.led, x.pub))) id

/-- The product layer. -/
@[reducible] def pl : Block (PLX N E Ξ) Y (XOut N E Ξ) Y :=
  L.init.seq ((L.sc.sc L.ord).seq L.fin)

/-- Its errors: 2 in each round of the sumcheck, e at ζ. -/
def plErr (e : ℕ) : Err L.pl.shape :=
  Err.app (s := L.init.shape)
    () (Err.app (s := (L.sc.sc L.ord).shape) (t := L.fin.shape) (L.sc.scErr L.ord) (e, ()))

/-- Before the layer: all deferred claims are true, and, if no coordinate of ϱ is 0, val(C) = ∑_X
eq(ϱ, X) f0[X] f1[X]. -/
def Rin (x : PLX N E Ξ) (y : Y) : Prop :=
  x.led.True (L.proj y) ∧
  ((∀ t < L.g, x.pt t ≠ 0) →
    Form.val (L.proj y) x.C = ext L.g (fun X => T.f0 x.pub y X * T.f1 x.pub y X) x.pt)

omit [Fintype E] [DecidableEq E] in
/-- Under `OrdOK`: before the first round no challenge of the layer is stored, so nothing is asked
of the stored challenges. -/
theorem nz_start (ho : L.OrdOK) (z : ℕ → E) : L.sc.NZ L.ord z := fun _ hv hvl =>
  absurd (ho.mem.mpr (L.nzv_iff.mp hv).2) hvl

omit [Fintype E] [DecidableEq E] in
/-- Under `OrdOK`: the start claim of the sumcheck, with the list, implies the relation before the
layer. -/
theorem clean_init (ho : L.OrdOK) :
    L.init.Clean (L.Rin T) (fun x y => L.sc.Rsum (L.scPhi T) L.ord x y ∧ L.LedTrue x y) () :=
  Block.clean_pure_iff.2 fun x y xo hxo hR => by
    obtain rfl := Option.some.inj hxo
    refine ⟨hR.2, fun hpt => ?_⟩
    exact (hR.1 (fun v hv => hpt v (ho.mem.mp hv)) (L.nz_start ho _)).trans
      (sumOutL_ext_mul_of_perm ho x.pt _ _ _)

/-- Under `OrdOK`: soundness of the product layer, with conclusion (a). At most 2 values of each
round challenge are bad and none of ζ. -/
theorem clean_pl_a (ho : L.OrdOK) : L.pl.Clean (L.Rin T) (L.Ra T) (L.plErr 0) :=
  (L.clean_init T ho).comp ((L.clean_rounds T).comp (L.clean_fin_a T))

/-- Under `OrdOK`: soundness of the product layer, with conclusion (b), under the premise that the
tested coordinates of the next point are not 0. At most 2 values of each round challenge and 1 value
of ζ are bad. -/
theorem clean_pl_b (ho : L.OrdOK) : L.pl.Clean (L.Rin T) (L.Rb T) (L.plErr 1) :=
  (L.clean_init T ho).comp ((L.clean_rounds T).comp (L.clean_fin_b T))

/-! ## 8. The honest prover -/

/-- What the honest prover of a product layer knows. Its state a : A holds the point ϱ and the two
vectors. `set` stores the next point and the values of v0 and v1, which the prover needs again in
the closing block of the segment (it turns all deferred claims into one linear claim). The state
holds no pad. -/
structure Prover (_ : PL E Y P N Ξ) (A : Type) where
  pt : A → ℕ → E
  f0 : A → ℕ → E
  f1 : A → ℕ → E
  set : A → (ℕ → E) → E → E → A

variable {L} {A : Type} (H : L.Prover A)

namespace Prover

/-- The honest prover of the sumcheck of the layer. -/
@[reducible] def scP : L.sc.Prover A where
  wt a := eqW (H.pt a)
  Φ a z := ext L.g (H.f0 a) z * ext L.g (H.f1 a) z
  deg a := (degLE_ext L.g (H.f0 a)).mul (degLE_ext L.g (H.f1 a))

/-- The honest values of v0 and v1: ~f0(ϱ̂), ~f1(ϱ̂). -/
def vval (s : A × (ℕ → E)) (b : Bool) : E :=
  if b then ext L.g (H.f1 s.1) s.2 else ext L.g (H.f0 s.1) s.2

/-- The honest prover of the last round. -/
@[reducible] def fin : Hon L.fin P E (A × (ℕ → E)) A :=
  Hon.one (fun s π => (fun e => Empty.elim e, fun b => H.vval s b + π (L.pv b)))
    (fun s ζ => H.set s.1 (consPt ζ s.2) (H.vval s false) (H.vval s true))
    {ζ | L.okE ζ = false} fun _ => ∅

/-- The honest prover of the product layer. Its withheld set: a challenge of the layer at whose
coordinate nz is set is 0. -/
@[reducible] def pl : Hon L.pl P E A A :=
  (Hon.pure (fun x : PLX N E Ξ => some (x.C, fun _ => 0, (x.pt, x.led, x.pub)))
      id fun a => (a, fun _ => 0)).seq
    ((H.scP.sc L.ord []).seq H.fin)

end Prover

variable (L) in
/-- The pads of the layer. -/
def pads : Set P := L.sc.padsOf (vars L.g) ∪ Set.range L.pv

omit [Fintype E] [DecidableEq E] in
variable (L) in
/-- Under `OrdOK`: the pads of the rounds do not depend on the order of the rounds. -/
theorem padsOf_ord (ho : L.OrdOK) : L.sc.padsOf L.ord = L.sc.padsOf (vars L.g) :=
  Set.ext fun p => by rw [SC.mem_padsOf, SC.mem_padsOf]; exact ⟨fun ⟨v, hv, h⟩ => ⟨v, (List.Perm.mem_iff ho).mp hv, h⟩, fun ⟨v, hv, h⟩ => ⟨v, (List.Perm.mem_iff ho).mpr hv, h⟩⟩

namespace Prover

variable (Inv : A → (P → E) → Ledger N E → Ξ → Y → Prop)

/-- The public data and the implicit part belong to the honest state: the point and the vectors are
those of the state, the pads of the layer are at their entries, the list is well-formed and true.
Inv is whatever else the caller needs to carry through the layer; it sees the list, so that it can
say, for the closing block, how long the list is and that the state holds the values of the opened
forms and the terms. -/
def Link (a : A) (π : P → E) (ξ : L.Pub) (y : Y) : Prop :=
  ξ.1 = H.pt a ∧ T.f0 ξ.2.2 y = H.f0 a ∧ T.f1 ξ.2.2 y = H.f1 a ∧
  (∀ p ∈ L.pads, L.proj y (L.place p) = π p) ∧ ξ.2.1.wf = true ∧
  ξ.2.1.True (L.proj y) ∧ Inv a π ξ.2.1 ξ.2.2 y

/-- Before the layer, for the honest prover: the statement belongs to the state, no coordinate of ϱ
is 0, and the start claim is true. -/
def HIn (a : A) (π : P → E) (x : PLX N E Ξ) (y : Y) : Prop :=
  H.Link T Inv a π (x.pt, x.led, x.pub) y ∧ (∀ t < L.g, x.pt t ≠ 0) ∧
    Form.val (L.proj y) x.C = ext L.g (fun X => T.f0 x.pub y X * T.f1 x.pub y X) x.pt

/-- After the layer, for the honest prover: the next point is that of the next state; none of its
coordinates at which nz is set is 0; the list is well-formed; both relations (a) and (b) after the
layer hold (the second without its premise); and Inv holds for the next state. -/
def HOut (a : A) (π : P → E) (xo : XOut N E Ξ) (y : Y) : Prop :=
  xo.1.pt = H.pt a ∧
  (∀ t < L.g + 1, L.nz t = true → xo.1.pt t ≠ 0) ∧
  xo.1.led.wf = true ∧ (L.Ra T) xo y ∧
  Form.val (L.proj y) xo.1.C =
    (1 - xo.1.pt 0) * ext L.g (T.f0 xo.1.pub y) (fun t => xo.1.pt (t + 1)) +
      xo.1.pt 0 * ext L.g (T.f1 xo.1.pub y) (fun t => xo.1.pt (t + 1)) ∧
  Inv a π xo.1.led xo.1.pub y

omit [Fintype E] [DecidableEq E] in
/-- Under `OrdOK`: completeness of the first step: the honest start claim of the sumcheck. -/
theorem accOn_init (ho : L.OrdOK) :
    (Hon.pure (P := P) (E := E)
        (fun x : PLX N E Ξ => some ((x.C, fun _ => 0, (x.pt, x.led, x.pub)) : L.sc.X)) (id : Y → Y)
        fun a : A => (a, fun _ : ℕ => (0 : E))).AccOn
      (H.HIn T Inv) (H.scP.Hsum (H.Link T Inv) (L.ord ++ [])) :=
  Hon.accOn_pure fun a π x y hi => by
    obtain ⟨hL, hpt, hC⟩ := hi
    refine ⟨_, rfl, hL, rfl, fun v hv => ?_, ?_, ?_⟩
    · rw [List.append_nil] at hv
      show (if true = true then H.pt a v else 1 - H.pt a v) ≠ 0
      rw [if_pos rfl, ← hL.1]
      exact hpt v (ho.mem.mp hv)
    · rw [List.append_nil]
      exact L.nz_start ho _
    · rw [List.append_nil]
      refine hC.trans ?_
      rw [hL.2.1, hL.2.2.1, show x.pt = H.pt a from hL.1]
      exact (sumOutL_ext_mul_of_perm ho (H.pt a) _ _ _).symm

variable [NeZero (2 : E)]

/-- Under `OrdOK`: completeness of the rounds of the sumcheck. It asks 2 ≠ 0 in E: the honest
scalars of a round of degree 2 are computed from the values at 0, 1, 2. -/
theorem accOn_rounds (ho : L.OrdOK) :
    (H.scP.sc L.ord []).AccOn (H.scP.Hsum (H.Link T Inv) (L.ord ++ []))
      (H.scP.Hsum (H.Link T Inv) []) :=
  H.scP.accOn_sc (L.sc_ok T).forms
      (fun _ => node_injective_one (NeZero.ne 2)) L.ord [] fun a π ξ y hL =>
    ⟨by show eqW ξ.1 = eqW (H.pt a); rw [hL.1], fun p hp => by
      show Form.val (L.proj y) (Form.ent (L.place p)) = π p
      rw [Form.val_ent]
      exact hL.2.2.2.1 p (Or.inl (by rw [← L.padsOf_ord ho]; exact hp))⟩

omit [NeZero (2 : E)] in
/-- Completeness of the last round, under `hset` and `hInv` (explained at `accOn_pl`). -/
theorem accOn_fin (hset : ∀ a p e0 e1, H.pt (H.set a p e0 e1) = p)
    (hInv : ∀ a p π led ξ y f w0 w1, Inv a π led ξ y →
      Inv (H.set a p (Form.val (L.proj y) w0) (Form.val (L.proj y) w1)) π
        (led.addProd f w0 w1) ξ y) :
    H.fin.AccOn (H.scP.Hsum (H.Link T Inv) []) (H.HOut T Inv) :=
  Hon.accOn_one fun s π x y c hi hc _ => by
    obtain ⟨hL, hz, _, hNZ, hv⟩ := hi
    obtain ⟨_, hf0, hf1, hpads, hwf, htrue, hinv⟩ := hL
    have hok : L.okE c = true := by
      cases h : L.okE c
      · exact absurd h hc
      · rfl
    have hv0 : Form.val (L.proj y) (L.vform (fun b => H.vval s b + π (L.pv b)) false) =
        ext L.g (T.f0 x.2.2.2.2 y) x.2.1 := by
      unfold vform
      rw [Form.val_masked, hpads _ (Or.inr ⟨false, rfl⟩), add_sub_cancel_right, hf0, hz]
      rfl
    have hv1 : Form.val (L.proj y) (L.vform (fun b => H.vval s b + π (L.pv b)) true) =
        ext L.g (T.f1 x.2.2.2.2 y) x.2.1 := by
      unfold vform
      rw [Form.val_masked, hpads _ (Or.inr ⟨true, rfl⟩), add_sub_cancel_right, hf1, hz]
      rfl
    have hC : Form.val (L.proj y) x.1 =
        ext L.g (T.f0 x.2.2.2.2 y) x.2.1 * ext L.g (T.f1 x.2.2.2.2 y) x.2.1 := by
      rw [hf0, hf1, hz]
      exact hv
    refine ⟨L.out x c _, if_pos (by rw [hok, hwf]; rfl), ?_, fun t ht hnz => ?_,
      Ledger.wf_addProd hwf _ _ _, ⟨?_, hv0, hv1⟩, ?_, ?_⟩
    · show consPt c x.2.1 = H.pt (H.set s.1 (consPt c s.2) _ _)
      rw [hset, hz]
    · show consPt c x.2.1 t ≠ 0
      cases t with
      | zero => exact L.ne_zero_of_okE hok hnz
      | succ t =>
        show x.2.1 t ≠ 0
        rw [hz]
        exact hNZ t (L.nzv_iff.mpr ⟨hnz, by omega⟩) List.not_mem_nil
    · exact (Ledger.true_addProd hwf _ _ _ _).mpr ⟨htrue, by rw [hC, hv0, hv1]⟩
    · show Form.val (L.proj y) ((1 - c) • L.vform _ false + c • L.vform _ true) =
        (1 - c) * _ + c * _
      rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, hv0, hv1]
      rfl
    · have h6 := hInv s.1 (consPt c s.2) π x.2.2.2.1 x.2.2.2.2 y x.1
        (L.vform (fun b => H.vval s b + π (L.pv b)) false)
        (L.vform (fun b => H.vval s b + π (L.pv b)) true) hinv
      rw [hv0, hv1, hf0, hf1, hz] at h6
      exact h6

/-- Under `OrdOK`, `hset`, `hInv` and 2 ≠ 0 in E: completeness of the product layer, for all pads
and at every ρ outside the withheld set. hset: the state that the prover sets after the layer holds
the new point. hInv: the caller's invariant Inv survives that step, with the list grown by the
layer's REL. -/
theorem accOn_pl (ho : L.OrdOK) (hset : ∀ a p e0 e1, H.pt (H.set a p e0 e1) = p)
    (hInv : ∀ a p π led ξ y f w0 w1, Inv a π led ξ y →
      Inv (H.set a p (Form.val (L.proj y) w0) (Form.val (L.proj y) w1)) π
        (led.addProd f w0 w1) ξ y) :
    H.pl.AccOn (H.HIn T Inv) (H.HOut T Inv) :=
  (H.accOn_init T Inv ho).comp ((H.accOn_rounds T Inv ho).comp (H.accOn_fin T Inv hset hInv))

variable [Fintype P] [DecidableEq P]

omit [NeZero (2 : E)] in
/-- If the pads of v0 and v1 are different, the last round is in masked form: v0 and v1 are values
plus their own pads, and the values read no pad. -/
theorem masked_fin (hpv : Function.Injective L.pv) :
    H.fin.Masked (fun _ => True) (Set.range L.pv) (∅ ∪ Set.range L.pv)
      (Hon.simOne (r := rV E) (K := Bool) E id) :=
  Hon.masked_one (r := rV E) (K := Bool) id (fun _ => True) L.pv hpv (fun s _ b => H.vval s b) ∅
    (fun _ _ _ => rfl) (fun _ _ _ _ _ => rfl) (Set.empty_disjoint _)

variable (L) in
/-- The simulator of the plain parts of a layer: independent uniform scalars. -/
def simPl : Rho L.pl.shape → PMF (Plains L.pl.shape) :=
  Hon.simSeq (s := L.init.shape) (fun _ => PMF.pure ())
    (Hon.simSeq (s := (L.sc.sc L.ord).shape) (L.sc.simSc L.ord)
      (Hon.simOne (r := rV E) (K := Bool) E id))

omit [NeZero (2 : E)] in
/-- Under `OrdOK` and the two conditions on pads below, the product layer is in masked form, given
that its sumcheck is: it masks with its own pads and reads no other pad, and its plain parts are
uniform outside the withheld set. -/
theorem masked_pl_of_rounds (ho : L.OrdOK) (V : A → Prop)
    (hsc : (H.scP.sc L.ord []).Masked
      (fun s => V s.1) (L.sc.padsOf L.ord) (L.sc.padsOf L.ord) (L.sc.simSc L.ord))
    (hpv : Function.Injective L.pv) (hd : Disjoint (L.sc.padsOf L.ord) (Set.range L.pv)) :
    H.pl.Masked V L.pads L.pads (simPl L) := by
  have h := (Hon.masked_pure
      (fun x : PLX N E Ξ => some ((x.C, fun _ => 0, (x.pt, x.led, x.pub)) : L.sc.X)) (id : Y → Y)
      (fun a : A => (a, fun _ : ℕ => (0 : E))) V).comp
    (hsc.comp (H.masked_fin hpv) (fun _ _ _ _ => trivial) hd hd) (fun _ _ ha _ => ha)
    (Set.empty_disjoint _) (Set.empty_disjoint _)
  simp only [Set.empty_union] at h
  unfold pads
  rw [← L.padsOf_ord ho]
  exact h

omit [NeZero (2 : E)] in
/-- Under `OrdOK`, the product layer is in masked form, if every pad of the layer is used for one
masked scalar only: the pads of the 2 g scalars of the rounds are different from one another, so are
those of v0 and v1, and no pad of a round is that of v0 or v1. The condition is about the names of
the pads (the type P). That different pads are at different entries (`place`) is not asked here;
without it the honest relation before the layer fails for most pads, and completeness says little.
-/
theorem masked_pl (ho : L.OrdOK) (V : A → Prop) (hp : L.sc.PlacesOnceOn (vars L.g))
    (hpv : Function.Injective L.pv) (hd : Disjoint (L.sc.padsOf (vars L.g)) (Set.range L.pv)) :
    H.pl.Masked V L.pads L.pads (simPl L) :=
  H.masked_pl_of_rounds ho V
    (H.scP.masked_sc_on V L.ord [] (hp.mono fun _ h => (List.Perm.mem_iff ho).mp h) ho.nodup)
    hpv (by rw [L.padsOf_ord ho]; exact hd)

end Prover

end PL

end Blocks
