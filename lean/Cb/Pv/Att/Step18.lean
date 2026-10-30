-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/Pv/Att/Step18.lean: step 18 of an attention segment, as the library's own description has it
(Inst/Model/Att/Sums.lean), as parameters of the sumcheck for the key at the index of the maximum.

Inst/Model/Att/Sums.lean defines the summand of step 18, `AttSeg.Phi18`, in g18 = lT + lg + lT
variables ξ = (X_j | X_g | X_i):
    eq(f_i, X_i) eq(f_g, X_g) * the sum over b of
      o'_b * ~kc_λ(b)(X_g, X_j) * the product over k of eq1(~ib_(b,k)(X_g, X_i), ξ (lT - 1 - k)).
This file fills the record `Scd` (Cb/Pv/Att/Scd.lean) with it, so that the statements of
Cb/Pv/Att/ScdProofs.lean hold of that step.

Main names:
  `size18 D`: the sizes: lt = D.lT, lgk = D.lg, Lam = D.nl, HA = D.na. So pairs = D.nb, the number
    of variables is `AttSeg.g18 D`, and the layer of a pair, b / HA, is `D.lamOf b`: all three by
    definition (`size18_pairs`, `size18_k`, `size18_lay`).
  `step18 D rd inc wAt cAt`: the parameters. The public states are the challenges (`AttSeg.Pub`);
    ri, rg, om are f_i, f_g, o'; rd says how the cells' content is read off the entries; the maps
    are the description's own extensions, each read at its own coordinates of the point; the
    incoming form and the entries that serve as masks stay parameters.
  `step18_at`: at every point, on the cube or off it, the summand `scdS` on the maps is
    `AttSeg.Phi18`.
  `step18_sum`: the sum claim says: the sum of `AttSeg.Phi18` over the hypercube plus the incoming
    form is the target.
  `step18_knowAt`: the block with n further scalars in its first message has knowledge soundness
    (`TWhole.KnowAt`), for all sizes. `step18_nums`: its errors.

Limits: the limits of Cb/Pv/Att/Scd.lean hold here too. That the programs' sumcheck is this step is
not stated: the description's step is taken as it is defined. Two differences of form, both closed
by `step18_at`: the description writes eq1(v, y) = v y + (1 - v) (1 - y) where `scdS` has
v (y + y - 1) + (1 - y), and it takes points as functions on the natural numbers. Nothing is said on
an honest prover or on hiding.
-/
import Cb.Pv.Att.ScdProofs
import Inst.Model.Att.Sums
import Cb.Part.LdPartPscFamProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Att
open Iop Prob Cb TWhole Inst.Model

/-- The sizes of step 18. -/
abbrev size18 (D : AttSeg.Dim) : ScdSize := ⟨D.lT, D.lg, D.nl, D.na⟩

theorem size18_pairs (D : AttSeg.Dim) : (size18 D).pairs = D.nb := rfl
theorem size18_k (D : AttSeg.Dim) : (size18 D).k = AttSeg.g18 D := rfl
theorem size18_lay (D : AttSeg.Dim) (b : Fin (size18 D).pairs) :
    ((size18 D).lay b).1 = D.lamOf b.1 := rfl

section Points
variable {E : Type} [Field E]

theorem nat_val {n : ℕ} (z : Fin n → E) (i : Fin n) : Blocks.nat z i.1 = z i := by
  simp [Blocks.nat, i.2]

/-- An extension reads the first g coordinates of its point alone. -/
theorem ext_first (g : ℕ) (u pt : ℕ → E) :
    Blocks.ext g u pt = Blocks.ext g u (Blocks.nat fun t : Fin g => pt t.1) := by
  unfold Blocks.ext
  refine Finset.sum_congr rfl fun X _ => ?_
  rw [Blocks.eqN_eq, Blocks.eqN_nat]
  simp only [Nat.zero_add]

variable (D : AttSeg.Dim)

/-- where the coordinates (X_g | X_j) stand among the variables -/
def gjAt (t : Fin (D.lg + D.lT)) : Fin (size18 D).k :=
  if h : t.1 < D.lg then ⟨D.lT + t.1, by show _ < D.lT + D.lg + D.lT; omega⟩
  else ⟨t.1 - D.lg, by have := t.2; show _ < D.lT + D.lg + D.lT; omega⟩

/-- where the coordinates (X_g | X_i) stand -/
def giAt (t : Fin (D.lg + D.lT)) : Fin (size18 D).k :=
  ⟨D.lT + t.1, by have := t.2; show _ < D.lT + D.lg + D.lT; omega⟩

theorem gjAt_inj : Function.Injective (gjAt D) := fun a b h => by
  have h1 := congrArg Fin.val h
  have ha := a.2
  have hb := b.2
  unfold gjAt at h1
  refine Fin.ext ?_
  split_ifs at h1 <;> simp only at h1 <;> omega

theorem giAt_inj : Function.Injective (giAt D) := fun a b h => by
  have h1 := congrArg Fin.val h
  unfold giAt at h1
  simp only at h1
  exact Fin.ext (by omega)

theorem cat_at (z : Fin (size18 D).k → E) (t : Fin (D.lg + D.lT)) :
    AttSeg.cat D.lg (AttSeg.sh (Blocks.nat z) D.lT) (Blocks.nat z) t.1 = z (gjAt D t) := by
  rw [← nat_val z (gjAt D t)]
  unfold AttSeg.cat AttSeg.sh gjAt
  split_ifs <;> rfl

theorem sh_at (z : Fin (size18 D).k → E) (t : Fin (D.lg + D.lT)) :
    AttSeg.sh (Blocks.nat z) D.lT t.1 = z (giAt D t) := by
  rw [← nat_val z (giAt D t)]
  rfl

theorem degKC_ext (u : ℕ → E) :
    Alg.DegLE (size18 D).degKC fun z : Fin (size18 D).k → E =>
      Blocks.ext (D.lg + D.lT) u
        (AttSeg.cat D.lg (AttSeg.sh (Blocks.nat z) D.lT) (Blocks.nat z)) := by
  have h := (ldPart_ext_deg (D.lg + D.lT) u).comp (gjAt D) (gjAt_inj D) (size18 D).degKC fun v => by
    have := v.2
    unfold ScdSize.degKC gjAt
    split_ifs <;> simp only at * <;> omega
  refine (congrArg (Alg.DegLE (size18 D).degKC) (funext fun z => ?_)).mp h
  rw [ext_first (D.lg + D.lT) u (AttSeg.cat _ _ _)]
  simp only [cat_at]

theorem degIB_ext (u : ℕ → E) :
    Alg.DegLE (size18 D).degIB fun z : Fin (size18 D).k → E =>
      Blocks.ext (D.lg + D.lT) u (AttSeg.sh (Blocks.nat z) D.lT) := by
  have h := (ldPart_ext_deg (D.lg + D.lT) u).comp (giAt D) (giAt_inj D) (size18 D).degIB fun v => by
    unfold ScdSize.degIB giAt
    split_ifs <;> simp only at * <;> omega
  refine (congrArg (Alg.DegLE (size18 D).degIB) (funext fun z => ?_)).mp h
  rw [ext_first (D.lg + D.lT) u (AttSeg.sh _ _)]
  simp only [sh_at]

end Points

variable {E : Type} [Field E] [Fintype E] (D : AttSeg.Dim) {J : Type} [Fintype J]
  (rd : (J → E) → AttSeg.Raw → E) (inc : AttSeg.Pub E → J → E)
  (wAt : PIdx (ldPartFmt E (size18 D).k (size18 D).deg ++ [pDummy E ((size18 D).lt + 1)]) → J)
  (cAt : (size18 D).A → J)

/-- The parameters of step 18. -/
noncomputable def step18 : Scd E (size18 D) where
  St := AttSeg.Pub E
  J := J
  ri := fun p a => p.fi a.1
  rg := fun p a => p.fg a.1
  om := fun p b => p.o' b.1
  mapKC := fun p m l z =>
    Blocks.ext (D.lg + D.lT) (AttSeg.kc D p (rd m) l.1)
      (AttSeg.cat D.lg (AttSeg.sh (Blocks.nat z) D.lT) (Blocks.nat z))
  mapIB := fun _ m b t z =>
    Blocks.ext (D.lg + D.lT) (fun X => AttSeg.ibV (rd m) t.1 b.1 (X / D.T) (X % D.T))
      (AttSeg.sh (Blocks.nat z) D.lT)
  inc := inc
  wAt := wAt
  cAt := cAt
  degK := fun _ _ _ => degKC_ext D _
  degI := fun _ _ _ _ => degIB_ext D _

/-- The summand on the maps is the description's summand, at every point. -/
theorem step18_at (p : AttSeg.Pub E) (m : J → E) (z : Fin (size18 D).k → E) :
    scdS (size18 D) (fun a => p.fi a.1) (fun a => p.fg a.1) (fun b => p.o' b.1) z
        (fun a => (step18 D rd inc wAt cAt).map p m a z) =
      AttSeg.Phi18 D p (rd m) (Blocks.nat z) := by
  unfold scdS AttSeg.Phi18 AttSeg.eqPt Alg.eqPt
  rw [← Fin.prod_univ_eq_prod_range
      (fun k => AttSeg.eq1 (p.fi k) (AttSeg.sh (Blocks.nat z) (D.lT + D.lg) k)) D.lT,
    ← Fin.prod_univ_eq_prod_range
      (fun k => AttSeg.eq1 (p.fg k) (AttSeg.sh (Blocks.nat z) D.lT k)) D.lg,
    ← Fin.sum_univ_eq_sum_range _ D.nb]
  congr 1
  · congr 1
    · refine Finset.prod_congr rfl fun a _ => ?_
      show Alg.eq1 (p.fi a.1) (z ((size18 D).iAt a)) = _
      rw [← nat_val z ((size18 D).iAt a)]
      rfl
    · refine Finset.prod_congr rfl fun a _ => ?_
      show Alg.eq1 (p.fg a.1) (z ((size18 D).gAt a)) = _
      rw [← nat_val z ((size18 D).gAt a)]
      rfl
  · refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Fin.prod_univ_eq_prod_range _ D.lT]
    congr 1
    refine Finset.prod_congr rfl fun t _ => ?_
    have e : Blocks.nat z (D.lT - 1 - t.1) = z ((size18 D).jAt t.rev) := by
      rw [← nat_val z ((size18 D).jAt t.rev)]
      congr 1
      have e2 : t.rev.1 = D.lT - (t.1 + 1) := Fin.val_rev t
      show D.lT - 1 - t.1 = t.rev.1
      rw [e2]
      omega
    rw [e]
    show _ = AttSeg.eq1 ((step18 D rd inc wAt cAt).map p m (.inr (b, t)) z) _
    unfold AttSeg.eq1
    ring

/-- What the sum claim of step 18 says. -/
theorem step18_sum (x : E × AttSeg.Pub E) (m : J → E) :
    (step18 D rd inc wAt cAt).plain.our.par.SumHolds x m ↔
      ∑ X ∈ Finset.range (2 ^ AttSeg.g18 D),
          AttSeg.Phi18 D x.2 (rd m) (Blocks.cubePt (AttSeg.g18 D) X) +
        ∑ j, inc x.2 j * m j = x.1 := by
  rw [scd_sum]
  have hc : ∀ c : Fin (size18 D).k → Bool,
      Blocks.nat (Alg.corner c : Fin (size18 D).k → E) =
        Blocks.cubePt (AttSeg.g18 D) (Alg.num c) := fun c => by
    unfold Blocks.cubePt
    show _ = Blocks.nat (Alg.corner (Alg.bits (size18 D).k (Alg.num c)))
    rw [Alg.bits_num]
  have e : ∑ c : Fin (size18 D).k → Bool,
        scdS (size18 D) ((step18 D rd inc wAt cAt).ri x.2) ((step18 D rd inc wAt cAt).rg x.2)
          ((step18 D rd inc wAt cAt).om x.2) (Alg.corner c)
          (fun a => (step18 D rd inc wAt cAt).map x.2 m a (Alg.corner c)) =
      ∑ X ∈ Finset.range (2 ^ AttSeg.g18 D),
        AttSeg.Phi18 D x.2 (rd m) (Blocks.cubePt (AttSeg.g18 D) X) := by
    exact (Finset.sum_congr rfl fun c _ =>
      (step18_at D rd inc wAt cAt x.2 m (Alg.corner c)).trans
        (congrArg (AttSeg.Phi18 D x.2 (rd m)) (hc c))).trans
      (Alg.sum_num (n := (size18 D).k)
        fun X => AttSeg.Phi18 D x.2 (rd m) (Blocks.cubePt (AttSeg.g18 D) X))
  exact Iff.of_eq (congrArg (fun t => t + ∑ j, inc x.2 j * m j = x.1) e)

section Block
variable (n : ℕ) {X : Type} (cl : X → (Fin n → E) → E × AttSeg.Pub E) (Ex : ExtSpec)
  {M Wp Kc : Type} (A0 : IOR.Rels Kc X Ex (M × Wp)) (msg : M → J → E)
  (Θ : X → (Fin n → E) → (J → E) → Prop)

/-- Knowledge soundness of the block of step 18. -/
theorem step18_knowAt :
    KnowAt (scdR (step18 D rd inc wAt cAt) n cl Ex)
      (scdIn (step18 D rd inc wAt cAt) n cl Ex A0 msg Θ)
      (scdOut (step18 D rd inc wAt cAt) n Ex A0 msg Θ) (fun _ _ _ wp => wp)
      (scdE (step18 D rd inc wAt cAt) n cl Ex) :=
  scd_knowAt (step18 D rd inc wAt cAt) n cl Ex A0 msg Θ

/-- Its errors. -/
theorem step18_nums :
    errList (scdE (step18 D rd inc wAt cAt) n cl Ex) =
      1 :: (List.replicate D.lT 2 ++ List.replicate D.lg (D.lT + 2) ++
        List.replicate D.lT (D.lT + 1) ++ [D.lT + 1] ++ [0]) :=
  scd_nums (step18 D rd inc wAt cAt) n cl Ex

end Block

end Cb.Pv.Att

#print axioms Cb.Pv.Att.step18_at
#print axioms Cb.Pv.Att.step18_sum
#print axioms Cb.Pv.Att.step18_knowAt
#print axioms Cb.Pv.Att.step18_nums
