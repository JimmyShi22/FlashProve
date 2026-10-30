-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Att/ScdProofs.lean: the proofs on the sumcheck for the key at the index of the maximum
(Cb/Pv/Att/Scd.lean).

Main names:
  `scd_know`: the statement `H_scd` holds, at every list of sizes. `scd_know_at`: the same at one
    tuple of parameters, written out.
  `scd_point`, `scd_local`, `scd_onOut`: the three facts that stand beside it. `scd_knowAt`: the
    four together (`TWhole.KnowAt`). `scd_knowAt_of`: the four together, with `H_scd` as a premise.
  `scd_nums`: the errors as a list of counts: 1; 2 for each bit of j; lt + 2 for each bit of g;
    lt + 1 for each bit of i; lt + 1 for the further variable (of the challenges other than 0); 0.
  `scd_sum`: the sum claim is the sum over the corners of the cube that the head of
    Cb/Pv/Att/Scd.lean writes. `scd_sum_unique`: for each state and each tuple of entries it holds
    of exactly one target.
  `scd_val`: the claim on an end value behind the block.
  `scd_fix`: the programs' choice of the coefficients that are left out is lawful. `scd_out`: so the
    block's verifier hands on a statement for every transcript: it tests nothing.
  `scd_ok`: the conditions of a plain sumcheck. `scd_degLE`: the degrees of the summand, variable by
    variable. `degKC_mle`, `degIB_mle`: multilinear extensions of tables over the corners of (j, g),
    and of (g, i), have the degrees that the parameters ask of the maps. `Scd.ofTab`: so every
    choice of such tables gives parameters.

Limits: as in Cb/Pv/Att/Scd.lean.

-/
import Cb.Pv.Att.Scd
import Cb.G6.Value
import Cb.Ld.LdPscVarsProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Att
open Iop Prob Cb TWhole Finset

/-! ## The sizes -/

namespace ScdSize
variable (s : ScdSize)

@[simp] theorem jAt_val (a : Fin s.lt) : (s.jAt a).1 = a.1 := rfl
@[simp] theorem gAt_val (a : Fin s.lgk) : (s.gAt a).1 = s.lt + a.1 := rfl
@[simp] theorem iAt_val (a : Fin s.lt) : (s.iAt a).1 = s.lt + s.lgk + a.1 := rfl

theorem jAt_inj : Function.Injective s.jAt := fun a b h =>
  Fin.ext (by have := congrArg Fin.val h; simpa using this)
theorem gAt_inj : Function.Injective s.gAt := fun a b h =>
  Fin.ext (by have := congrArg Fin.val h; simp only [gAt_val] at this; omega)
theorem iAt_inj : Function.Injective s.iAt := fun a b h =>
  Fin.ext (by have := congrArg Fin.val h; simp only [iAt_val] at this; omega)

theorem deg_pos (i : Fin s.k) : 1 ≤ s.deg i := by
  unfold deg
  split_ifs <;> omega

theorem ofFn_deg : List.ofFn s.deg =
    List.replicate s.lt 2 ++ List.replicate s.lgk (s.lt + 2) ++ List.replicate s.lt (s.lt + 1) := by
  apply List.ext_getElem
  · simp [k]
    omega
  · intro i h1 h2
    simp only [List.getElem_ofFn, List.getElem_append, List.getElem_replicate, List.length_append,
      List.length_replicate, deg]
    split_ifs <;> first | rfl | omega

/-- a variable is the partner of at most one bit of the index, and only if it is a bit of j -/
theorem sum_at (i : Fin s.k) :
    ∑ t : Fin s.lt, (if i = s.jAt t.rev then 1 else 0) ≤ if i.1 < s.lt then 1 else 0 := by
  by_cases h : i.1 < s.lt
  · rw [if_pos h, Finset.sum_boole]
    simp only [Nat.cast_id]
    refine Finset.card_le_one.2 fun a ha b hb => ?_
    have e : s.jAt a.rev = s.jAt b.rev :=
      (Finset.mem_filter.1 ha).2.symm.trans (Finset.mem_filter.1 hb).2
    exact Fin.rev_injective (s.jAt_inj e)
  · rw [if_neg h]
    refine le_of_eq (Finset.sum_eq_zero fun t _ => if_neg fun e => h ?_)
    rw [e, jAt_val]
    exact t.rev.2

end ScdSize

/-! ## The degrees of the summand -/

section Degrees
variable {E : Type} [Field E]

/-- A coordinate has the degree 1 in its own variable and 0 in the others. -/
theorem degLE_at {ι : Type} [DecidableEq ι] (j : ι) :
    Alg.DegLE (fun i => if i = j then 1 else 0) (fun z : ι → E => z j) :=
  (Alg.DegLE.coord (K := E) ()).comp (fun _ : Unit => j) (fun a b _ => Subsingleton.elim a b) _
    fun _ => by simp

theorem scd_degLE (s : ScdSize) (ri : Fin s.lt → E) (rg : Fin s.lgk → E) (om : Fin s.pairs → E)
    (kc : Fin s.Lam → (Fin s.k → E) → E) (ib : Fin s.pairs → Fin s.lt → (Fin s.k → E) → E)
    (hk : ∀ l, Alg.DegLE s.degKC (kc l)) (hi : ∀ b t, Alg.DegLE s.degIB (ib b t)) :
    Alg.DegLE s.deg fun z =>
      Alg.eqPt ri (fun a => z (s.iAt a)) * Alg.eqPt rg (fun a => z (s.gAt a)) *
        ∑ b : Fin s.pairs, om b * kc (s.lay b) z *
          ∏ t : Fin s.lt, (ib b t z * (z (s.jAt t.rev) + z (s.jAt t.rev) - 1) +
            (1 - z (s.jAt t.rev))) := by
  have h1 : Alg.DegLE (fun i : Fin s.k => if s.lt + s.lgk ≤ i.1 then 1 else 0)
      (fun z : Fin s.k → E => Alg.eqPt ri fun a => z (s.iAt a)) :=
    (Alg.DegLE.eqPt ri).comp s.iAt s.iAt_inj _ fun v => by
      simp only [ScdSize.iAt_val]
      split_ifs <;> omega
  have h2 : Alg.DegLE (fun i : Fin s.k => if s.lt ≤ i.1 ∧ i.1 < s.lt + s.lgk then 1 else 0)
      (fun z : Fin s.k → E => Alg.eqPt rg fun a => z (s.gAt a)) :=
    (Alg.DegLE.eqPt rg).comp s.gAt s.gAt_inj _ fun v => by
      have := v.2
      simp only [ScdSize.gAt_val]
      split_ifs <;> omega
  have hy : ∀ t : Fin s.lt, Alg.DegLE (fun i => if i = s.jAt t.rev then 1 else 0)
      (fun z : Fin s.k → E => z (s.jAt t.rev)) := fun t => degLE_at _
  have hf : ∀ b t, Alg.DegLE (fun i => s.degIB i + if i = s.jAt t.rev then 1 else 0)
      (fun z : Fin s.k → E => ib b t z * (z (s.jAt t.rev) + z (s.jAt t.rev) - 1) +
        (1 - z (s.jAt t.rev))) := fun b t =>
    ((hi b t).mul (((hy t).add (hy t)).sub (Alg.DegLE.const _ 1))).add
      (((Alg.DegLE.const _ 1).sub (hy t)).mono fun i => Nat.le_add_left _ _)
  have hp := fun b => Alg.DegLE.prod (Finset.univ : Finset (Fin s.lt)) fun t _ => hf b t
  have hs := Alg.DegLE.sum (Finset.univ : Finset (Fin s.pairs)) fun b _ =>
    ((hk (s.lay b)).const_mul (om b)).mul (hp b)
  refine ((h1.mul h2).mul hs).mono fun i => ?_
  have h3 := s.sum_at i
  have e : ∑ t : Fin s.lt, (s.degIB i + if i = s.jAt t.rev then 1 else 0) =
      s.lt * s.degIB i + ∑ t : Fin s.lt, (if i = s.jAt t.rev then 1 else 0) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [e]
  generalize (∑ t : Fin s.lt, (if i = s.jAt t.rev then 1 else 0)) = S at h3 ⊢
  unfold ScdSize.degKC ScdSize.degIB ScdSize.deg
  split_ifs at h3 ⊢ <;> omega

end Degrees

/-- The multilinear extension of a table over the corners of (j, g). -/
theorem degKC_mle {E : Type} [Field E] (s : ScdSize) (u : (Fin s.lt ⊕ Fin s.lgk → Bool) → E) :
    Alg.DegLE s.degKC fun x : Fin s.k → E => Alg.mle u fun v => x (Sum.elim s.jAt s.gAt v) := by
  refine (Alg.DegLE.mle u).comp (Sum.elim s.jAt s.gAt) ?_ _ ?_
  · rintro (a | a) (b | b) h
    · exact congrArg Sum.inl (s.jAt_inj h)
    · have h1 := congrArg Fin.val h
      have h2 := a.2
      simp only [Sum.elim_inl, Sum.elim_inr, ScdSize.jAt_val, ScdSize.gAt_val] at h1
      omega
    · have h1 := congrArg Fin.val h
      have h2 := b.2
      simp only [Sum.elim_inl, Sum.elim_inr, ScdSize.jAt_val, ScdSize.gAt_val] at h1
      omega
    · exact congrArg Sum.inr (s.gAt_inj h)
  · rintro (a | a)
    · have := a.2
      simp only [Sum.elim_inl, ScdSize.degKC, ScdSize.jAt_val]
      split_ifs <;> omega
    · have := a.2
      simp only [Sum.elim_inr, ScdSize.degKC, ScdSize.gAt_val]
      split_ifs <;> omega

/-- The multilinear extension of a table over the corners of (g, i). -/
theorem degIB_mle {E : Type} [Field E] (s : ScdSize) (u : (Fin s.lgk ⊕ Fin s.lt → Bool) → E) :
    Alg.DegLE s.degIB fun x : Fin s.k → E => Alg.mle u fun v => x (Sum.elim s.gAt s.iAt v) := by
  refine (Alg.DegLE.mle u).comp (Sum.elim s.gAt s.iAt) ?_ _ ?_
  · rintro (a | a) (b | b) h
    · exact congrArg Sum.inl (s.gAt_inj h)
    · have h1 := congrArg Fin.val h
      have h2 := a.2
      simp only [Sum.elim_inl, Sum.elim_inr, ScdSize.iAt_val, ScdSize.gAt_val] at h1
      omega
    · have h1 := congrArg Fin.val h
      have h2 := b.2
      simp only [Sum.elim_inl, Sum.elim_inr, ScdSize.iAt_val, ScdSize.gAt_val] at h1
      omega
    · exact congrArg Sum.inr (s.iAt_inj h)
  · rintro (a | a)
    · simp only [Sum.elim_inl, ScdSize.degIB, ScdSize.gAt_val]
      split_ifs <;> omega
    · simp only [Sum.elim_inr, ScdSize.degIB, ScdSize.iAt_val]
      split_ifs <;> omega

/-! ## The conditions of a plain sumcheck -/

variable {E : Type} [Field E] [Fintype E] {s : ScdSize} (T : Scd E s)

/-- Parameters whose maps are the multilinear extensions of tables: KC_l of a table over the corners
of (j, g), IB_(b,t) of a table over the corners of (g, i). The tables may be any functions of state
and entries. -/
def Scd.ofTab (s : ScdSize) (St J : Type) [Fintype J] (ri : St → Fin s.lt → E)
    (rg : St → Fin s.lgk → E) (om : St → Fin s.pairs → E)
    (kt : St → (J → E) → Fin s.Lam → (Fin s.lt ⊕ Fin s.lgk → Bool) → E)
    (it : St → (J → E) → Fin s.pairs → Fin s.lt → (Fin s.lgk ⊕ Fin s.lt → Bool) → E)
    (inc : St → J → E) (wAt : PIdx (ldPartFmt E s.k s.deg ++ [pDummy E (s.lt + 1)]) → J)
    (cAt : s.A → J) : Scd E s where
  St := St
  J := J
  ri := ri
  rg := rg
  om := om
  mapKC := fun st m l x => Alg.mle (kt st m l) fun v => x (Sum.elim s.jAt s.gAt v)
  mapIB := fun st m b t x => Alg.mle (it st m b t) fun v => x (Sum.elim s.gAt s.iAt v)
  inc := inc
  wAt := wAt
  cAt := cAt
  degK := fun st m l => degKC_mle s (kt st m l)
  degI := fun st m b t => degIB_mle s (it st m b t)

theorem scd_degX (st : T.St) (m : T.J → E) (u : s.A → E) :
    Alg.DegLE s.deg fun x =>
      scdS s (T.ri st) (T.rg st) (T.om st) x fun a => T.map st m a x + u a :=
  scd_degLE s (T.ri st) (T.rg st) (T.om st) (fun l x => T.mapKC st m l x + u (.inl l))
    (fun b t x => T.mapIB st m b t x + u (.inr (b, t)))
    (fun l => (T.degK st m l).add (Alg.DegLE.const _ _))
    fun b t => (T.degI st m b t).add (Alg.DegLE.const _ _)

theorem scd_degY (st : T.St) (x : Fin s.k → E) (v u : s.A → E) :
    ∃ c : Fin (s.lt + 1 + 1) → E, ∀ y : E,
      scdS s (T.ri st) (T.rg st) (T.om st) x (fun a => v a + u a * y) = hev c y := by
  have hl : ∀ a : s.A, Alg.DegLE (fun _ : Unit => 1) (fun w : Unit → E => v a + u a * w ()) :=
    fun a => (Alg.DegLE.const _ (v a)).add ((Alg.DegLE.coord ()).const_mul (u a))
  have hf := fun (b : Fin s.pairs) (t : Fin s.lt) =>
    ((hl (.inr (b, t))).mul_const (x (s.jAt t.rev) + x (s.jAt t.rev) - 1)).add
      (Alg.DegLE.const _ (1 - x (s.jAt t.rev)))
  have hp := fun b => Alg.DegLE.prod (Finset.univ : Finset (Fin s.lt)) fun t _ => hf b t
  have hs := Alg.DegLE.sum (Finset.univ : Finset (Fin s.pairs)) fun b _ =>
    ((hl (.inl (s.lay b))).const_mul (T.om st b)).mul (hp b)
  have hg := (hs.const_mul
    (Alg.eqPt (T.ri st) (fun a => x (s.iAt a)) * Alg.eqPt (T.rg st) (fun a => x (s.gAt a)))).mono
    (d' := fun _ => s.lt + 1) fun _ => by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      omega
  obtain ⟨q, hq, he⟩ := hg (fun _ => 0) ()
  refine ⟨fun t => q.coeff t, fun y => ?_⟩
  rw [hev_of_poly E q hq y, ← he y]
  simp only [Function.update_self]
  rfl

theorem scd_ok : T.plain.OK where
  one := s.deg_pos
  degX := scd_degX T
  degY := scd_degY T

/-! ## The statement, and what stands beside it -/

section Block
variable (n : ℕ) {X : Type} (cl : X → (Fin n → E) → E × T.St) (Ex : ExtSpec) {M Wp Kc : Type}
  (A0 : IOR.Rels Kc X Ex (M × Wp)) (msg : M → T.J → E) (Θ : X → (Fin n → E) → (T.J → E) → Prop)

theorem scd_knowAt :
    KnowAt (scdR T n cl Ex) (scdIn T n cl Ex A0 msg Θ) (scdOut T n Ex A0 msg Θ)
      (fun _ _ _ wp => wp) (scdE T n cl Ex) :=
  plain_knowAt T.plain T.plain.fix n cl Ex A0 msg Θ (scd_ok T)

/-- The statement at one tuple of parameters, written out. -/
theorem scd_know_at (m : M) :
    (scdR T n cl Ex).red.Know (scdIn T n cl Ex A0 msg Θ).on
      (fun a wp => (scdIn T n cl Ex A0 msg Θ).relR a (m, wp))
      (fun b wp => (scdOut T n Ex A0 msg Θ).relR b (m, wp))
      (fun _ _ wp => wp) (scdE T n cl Ex) :=
  (scd_knowAt T n cl Ex A0 msg Θ).know m

theorem scd_point : Nonempty (scdR T n cl Ex).shape.IsPoint :=
  (scd_knowAt (M := Unit) (Wp := Unit) (Kc := Unit) T n cl Ex
    ⟨fun _ _ _ => True, fun _ _ => True, fun _ => True, fun _ => ()⟩ (fun _ _ => 0)
    fun _ _ _ => True).point

theorem scd_local : (scdR T n cl Ex).IsLocal :=
  (scd_knowAt (M := Unit) (Wp := Unit) (Kc := Unit) T n cl Ex
    ⟨fun _ _ _ => True, fun _ _ => True, fun _ => True, fun _ => ()⟩ (fun _ _ => 0)
    fun _ _ _ => True).isLocal

theorem scd_onOut : ∀ a τ b, (scdIn T n cl Ex A0 msg Θ).on a →
    (scdR T n cl Ex).red.out a τ = some b → (scdOut T n Ex A0 msg Θ).on b :=
  (scd_knowAt T n cl Ex A0 msg Θ).onOut

/-- The four together, from the statement as a premise. -/
theorem scd_knowAt_of (sizes : List ScdSize) (H : H_scd E sizes) (hs : s ∈ sizes) :
    KnowAt (scdR T n cl Ex) (scdIn T n cl Ex A0 msg Θ) (scdOut T n Ex A0 msg Θ)
      (fun _ _ _ wp => wp) (scdE T n cl Ex) where
  point := scd_point T n cl Ex
  isLocal := scd_local T n cl Ex
  onOut := scd_onOut T n cl Ex A0 msg Θ
  know := H s hs T n X cl Ex M Wp Kc A0 msg Θ

/-- The errors. -/
theorem scd_nums : errList (scdE T n cl Ex) =
    1 :: (List.replicate s.lt 2 ++ List.replicate s.lgk (s.lt + 2) ++
      List.replicate s.lt (s.lt + 1) ++ [s.lt + 1] ++ [0]) := by
  have h := plain_nums T.plain n Ex
  have h2 : List.ofFn T.plain.deg = _ := s.ofFn_deg
  rw [h2] at h
  exact h

end Block

variable (E) in
/-- THE STATEMENT HOLDS. -/
theorem scd_know (sizes : List ScdSize) : H_scd E sizes :=
  fun _ _ T n _ cl Ex _ _ _ A0 msg Θ m => scd_know_at T n cl Ex A0 msg Θ m

/-! ## What the two joints say -/

theorem scd_sum (x : E × T.St) (m : T.J → E) :
    T.plain.our.par.SumHolds x m ↔
      ∑ c : Fin s.k → Bool, scdS s (T.ri x.2) (T.rg x.2) (T.om x.2) (Alg.corner c)
          (fun a => T.map x.2 m a (Alg.corner c)) +
        ∑ j, T.inc x.2 j * m j = x.1 :=
  plain_sum T.plain x m

theorem scd_sum_unique (st : T.St) (m : T.J → E) :
    ∃! t : E, T.plain.our.par.SumHolds (t, st) m :=
  ⟨hSumAll (T.plain.our.par.vars st) (T.plain.our.par.sum st m) + T.plain.our.par.inc st m, rfl,
    fun _ h => Eq.symm h⟩

theorem scd_val (o : T.plain.our.par.Out) (m : T.J → E) (a : s.A) :
    T.plain.our.par.EHolds o m a ↔
      T.map o.st m a (ldPartIni s.k s.deg (pDummy E (s.lt + 1)) o.pt) +
        m (T.cAt a) * ldPartLast s.k s.deg (pDummy E (s.lt + 1)) o.pt = o.vals a := by
  rw [psc_our_val E T.plain.our o m a]
  have h1 :=
    ldPartVars_ini E s.k s.deg T.plain.dat (pDummy E (s.lt + 1)) (pDummyD E (s.lt + 1)) o.pt
  have h2 :=
    ldPartVars_last E s.k s.deg T.plain.dat (pDummy E (s.lt + 1)) (pDummyD E (s.lt + 1)) o.pt
  exact Iff.of_eq (congrArg₂
    (fun p q => T.map o.st m a p + m (T.cAt a) * q = o.vals a) h1 h2)

/-! ## The coefficients that are left out -/

theorem scd_fix : ∀ st, HFixs.OK (T.plain.our.par.vars st) (T.plain.fix st) :=
  plain_fix T.plain (scd_ok T)

/-- The block's verifier tests nothing. -/
theorem scd_out (n : ℕ) {X : Type} (cl : X → (Fin n → E) → E × T.St) (Ex : ExtSpec) (x : X)
    (y : Ex.Str) (τ : Tr (scdR T n cl Ex).shape) :
    (scdR T n cl Ex).out x y τ =
      some ((x, riders T.plain.our.par n τ),
        shortV T.plain.our.par T.plain.fix (cl x (riders T.plain.our.par n τ))
          (unrideN T.plain.our.par n τ)) := by
  show ((shortR T.plain.our.par T.plain.fix Ex).out _ y _).map _ = _
  rw [short_out T.plain.our.par T.plain.fix Ex (scd_fix T)]
  rfl

end Cb.Pv.Att

#print axioms Cb.Pv.Att.scd_know
#print axioms Cb.Pv.Att.scd_knowAt
#print axioms Cb.Pv.Att.scd_knowAt_of
#print axioms Cb.Pv.Att.scd_point
#print axioms Cb.Pv.Att.scd_local
#print axioms Cb.Pv.Att.scd_onOut
#print axioms Cb.Pv.Att.scd_nums
#print axioms Cb.Pv.Att.scd_sum
#print axioms Cb.Pv.Att.scd_sum_unique
#print axioms Cb.Pv.Att.scd_val
#print axioms Cb.Pv.Att.scd_fix
#print axioms Cb.Pv.Att.scd_out
#print axioms Cb.Pv.Att.Scd.ofTab
