-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/Kept.lean: a sum of terms over maps, some of which are not revealed, as the parameters
of a sumcheck.

The library's builder (Cb/Part/LdPartPsc.lean) turns a sum of terms over maps into the parameters
of a masked sumcheck in which every map is revealed at the end. A sumcheck of the layers'
sub-proof keeps maps: the summand is
    S0(X, revealed values) + sum over b of S1_b(X, revealed values) * Fb_b(X),
it is affine in each kept map Fb_b, and the value of a kept map at the last point is never sent.
It then stands in the first output row. This file adds the kept maps to the builder's data and
proves what the sumcheck asks.

Main names:
  `KeptSm S`: over the builder's data S: the kept maps, and for each of them the sum of terms that
    multiplies it.
  `KeptSm.our`: the sumcheck's parameters. Format, data of the variables, revealed maps and own
    masks are those of `S.our M`.
  `KeptSm.OK`: the conditions, for degrees da of the revealed maps and db of the kept ones.
  `KeptSm.conds`: the four conditions of the sumcheck.
  `KeptSm.sum_iff`: what the input claim says.
  `KeptSm.val_iff`: what the output row on a revealed map's value says.
  `KeptSm.degs`: the degrees of the rounds.

Limits: nothing is said on what the first output row says (it bears the kept maps' values at the
last point). Nothing is said on the honest prover, on completeness or on zero knowledge. The
sentences on what the programs do are by reading: nothing is compared with the programs here.

-/
import Cb.Part.LdPartPscProofs
import Cb.Ld.LdPscProofsOur

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Lay
open Iop Prob Hiop Cb Finset Polynomial

noncomputable section

/-- The kept maps over a sum of terms. -/
structure KeptSm {E St J : Type} (S : LdPartSm E St J) where
  /-- the names of the kept maps -/
  B : Type
  [finB : Fintype B]
  Fb : St → (J → E) → B → (Fin S.k → E) → E
  /-- the sum of terms that multiplies a kept map -/
  kt : B → List (LdPartTm E St S.A S.k)

attribute [instance] KeptSm.finB

namespace KeptSm
variable {E St J : Type} [Field E] {S : LdPartSm E St J} (Q : KeptSm S)

/-- the factor of a kept map, as a function of the point and of the revealed maps' values -/
def polB (st : St) (z : Fin S.k → E) (v : S.A → E) (b : Q.B) : E :=
  ((Q.kt b).map fun t => t.coef st z * (t.atoms.map v).prod).sum

/-- the summand at the maps' own values -/
def val (st : St) (m : J → E) (z : Fin S.k → E) : E :=
  S.val st m z + ∑ b, Q.polB st z (fun a => S.F st m a z) b * Q.Fb st m b z

variable [Fintype E] [Fintype J] (M : LdPartMk S)

/-- The sumcheck. -/
@[reducible] def our : PscOur E where
  St := St
  J := J
  fmt := ldPartFmt E S.k M.n
  dat := fun st => ldPartDat E S.k M.n (S.w st)
  A := S.A
  B := Q.B
  F := fun st m a X => S.F st m a (S.fn M st X)
  Fb := fun st m b X => Q.Fb st m b (S.fn M st X)
  S0 := fun st X v => S.pol st (S.fn M st X) v
  S1 := fun st X v b => Q.polB st (S.fn M st X) v b
  DY := M.DY
  slS := M.slS
  wAt := M.wAt
  cAt := M.cAt

/-- The conditions on the kept maps and their factors. -/
structure OK (da : S.A → Fin S.k → ℕ) (db : Q.B → Fin S.k → ℕ) : Prop where
  base : S.OK M da
  mapB : ∀ st m b, Alg.DegLE (db b) (Q.Fb st m b)
  fitB : ∀ b, ∀ t ∈ Q.kt b, ∃ dc : Fin S.k → ℕ,
    (∀ st, Alg.DegLE dc (t.coef st)) ∧
      ∀ i, dc i + (t.atoms.map fun a => da a i).sum + db b i ≤ M.n i
  dyB : ∀ b, ∀ t ∈ Q.kt b, t.atoms.length ≤ M.DY

theorem vars (h : ∀ st i, S.w st i = none → 1 ≤ M.n i) : (Q.our M).VarsOK := fun st =>
  ldPartVars_ok E S.k M.n (S.w st) (h st)

theorem inj : (Q.our M).ValInj := ldPartVars_inj E S.k M.n

theorem degX (da : S.A → Fin S.k → ℕ) (db : Q.B → Fin S.k → ℕ) (h : Q.OK M da db) :
    (Q.our M).DegX := by
  intro st m u
  have h0 : Alg.DegLE M.n fun z => S.pol st z fun a => S.F st m a z + u a := by
    unfold LdPartSm.pol
    refine ldPart_degLE_sum S.terms M.n
      (fun (t : LdPartTm E St S.A S.k) z =>
        t.coef st z * (t.atoms.map fun a => S.F st m a z + u a).prod) fun t ht => ?_
    obtain ⟨dc, h1, h2⟩ := h.base.fit t ht
    exact ((h1 st).mul
      (ldPart_degLE_prod t.atoms da (fun a z => S.F st m a z + u a) fun a =>
        (h.base.map st m a).add (Alg.DegLE.const _ (u a)))).mono h2
  have hb : ∀ b, Alg.DegLE M.n fun z =>
      Q.polB st z (fun a => S.F st m a z + u a) b * Q.Fb st m b z := by
    intro b
    have e : (fun z => Q.polB st z (fun a => S.F st m a z + u a) b * Q.Fb st m b z) =
        fun z => ((Q.kt b).map fun t =>
          t.coef st z * (t.atoms.map fun a => S.F st m a z + u a).prod * Q.Fb st m b z).sum := by
      funext z
      unfold polB
      rw [← List.sum_map_mul_right]
    rw [e]
    refine ldPart_degLE_sum (Q.kt b) M.n
      (fun (t : LdPartTm E St S.A S.k) z =>
        t.coef st z * (t.atoms.map fun a => S.F st m a z + u a).prod * Q.Fb st m b z) fun t ht => ?_
    obtain ⟨dc, h1, h2⟩ := h.fitB b t ht
    exact (((h1 st).mul
      (ldPart_degLE_prod t.atoms da (fun a z => S.F st m a z + u a) fun a =>
        (h.base.map st m a).add (Alg.DegLE.const _ (u a)))).mul (h.mapB st m b)).mono h2
  have hs : Alg.DegLE M.n fun z =>
      ∑ b, Q.polB st z (fun a => S.F st m a z + u a) b * Q.Fb st m b z := by
    have := ldPart_degLE_sum (Finset.univ : Finset Q.B).toList M.n
      (fun b z => Q.polB st z (fun a => S.F st m a z + u a) b * Q.Fb st m b z) fun b _ => hb b
    simpa only [Finset.sum_map_toList] using this
  exact ldPartVars_deg E S.k M.n _ _ (h0.add hs)

theorem degY (h0 : ∀ t ∈ S.terms, t.atoms.length ≤ M.DY)
    (hB : ∀ b, ∀ t ∈ Q.kt b, t.atoms.length ≤ M.DY) : (Q.our M).DegY := by
  intro st P v u r
  obtain ⟨q, hq, he⟩ :=
    ldPart_line_sum S.terms (fun t => t.coef st (S.fn M st P)) (fun t => t.atoms) M.DY h0 v u
  have hb := fun b =>
    ldPart_line_sum (Q.kt b) (fun t => t.coef st (S.fn M st P)) (fun t => t.atoms) M.DY (hB b) v u
  choose qb hqb heb using hb
  have hd : (q + ∑ b, C (r b) * qb b).natDegree ≤ M.DY :=
    natDegree_add_le_of_degree_le hq
      (natDegree_sum_le_of_forall_le _ _ fun b _ => (natDegree_C_mul_le _ _).trans (hqb b))
  refine ⟨fun t => (q + ∑ b, C (r b) * qb b).coeff t, fun y => ?_⟩
  rw [hev_of_poly E _ hd, eval_add, he, eval_finset_sum]
  refine congrArg _ (Finset.sum_congr rfl fun b _ => ?_)
  rw [eval_mul, eval_C, heb, mul_comm]
  rfl

/-- The four conditions of the sumcheck. -/
theorem conds (da : S.A → Fin S.k → ℕ) (db : Q.B → Fin S.k → ℕ) (h : Q.OK M da db) :
    (Q.our M).VarsOK ∧ (Q.our M).ValInj ∧ (Q.our M).DegX ∧ (Q.our M).DegY :=
  ⟨Q.vars M h.base.plain, Q.inj M, Q.degX M da db h, Q.degY M h.base.dy h.dyB⟩

/-- What the input claim says. -/
theorem sum_iff (τ : E) (st : St) (m : J → E) :
    (Q.our M).SumHolds (τ, st) m ↔
      ∑ b : Fin S.k → Bool, (∏ i, ldPartWt (S.w st i) (b i)) * Q.val st m (Alg.corner b) +
        ∑ j, M.slS st j * m j = τ := by
  have e : ∀ b : Fin S.k → Bool,
      (Q.our M).sum st m (pH _ (ldPartDat E S.k M.n (S.w st)) (ldPartPP S.k M.n (Alg.corner b))) =
        Q.val st m (Alg.corner b) := by
    intro b
    show S.pol st (ldPartFn S.k M.n _ (pH _ _ (ldPartPP S.k M.n (Alg.corner b))))
        (fun a => S.F st m a (ldPartFn S.k M.n _ (pH _ _ (ldPartPP S.k M.n (Alg.corner b))))) +
      ∑ c, Q.polB st (ldPartFn S.k M.n _ (pH _ _ (ldPartPP S.k M.n (Alg.corner b))))
        (fun a => S.F st m a (ldPartFn S.k M.n _ (pH _ _ (ldPartPP S.k M.n (Alg.corner b))))) c *
        Q.Fb st m c (ldPartFn S.k M.n _ (pH _ _ (ldPartPP S.k M.n (Alg.corner b)))) = _
    rw [ldPartVars_fn]
    rfl
  show hSumAll (pVars (ldPartFmt E S.k M.n) (ldPartDat E S.k M.n (S.w st))) ((Q.our M).sum st m) +
        ∑ j, M.slS st j * m j = τ ↔ _
  rw [ldPartVars_sum]
  simp only [e]

/-- the verifier's point, read off an output claim; the further variable's challenge -/
def outPt (o : (Q.our M).par.Out) : Fin S.k → E := ldPartIni S.k M.n (pDummy E M.DY) o.pt
def outB (o : (Q.our M).par.Out) : E := ldPartLast S.k M.n (pDummy E M.DY) o.pt

/-- What the output row on a revealed map's value says. -/
theorem val_iff (o : (Q.our M).par.Out) (m : J → E) (a : S.A) :
    (Q.our M).par.EHolds o m a ↔
      S.F o.st m a (Q.outPt M o) + m (M.cAt a) * Q.outB M o = o.vals a := by
  unfold outPt outB
  rw [← ldPartVars_ini E S.k M.n (ldPartDat E S.k M.n (S.w o.st))
        (pDummy E M.DY) (pDummyD E M.DY) o.pt,
    ← ldPartVars_last E S.k M.n (ldPartDat E S.k M.n (S.w o.st))
      (pDummy E M.DY) (pDummyD E M.DY) o.pt]
  exact Iff.rfl

/-- The degrees of the rounds. -/
theorem degs : (Q.our M).par.fmt.map PFmt.n = List.ofFn M.n ++ [M.DY] := by
  show ((ldPartFmt E S.k M.n) ++ [pDummy E M.DY]).map PFmt.n = _
  rw [List.map_append, ldPartVars_degs E]
  rfl

end KeptSm
end
end Cb.Pv.Lay

#print axioms Cb.Pv.Lay.KeptSm.conds
#print axioms Cb.Pv.Lay.KeptSm.sum_iff
#print axioms Cb.Pv.Lay.KeptSm.val_iff
