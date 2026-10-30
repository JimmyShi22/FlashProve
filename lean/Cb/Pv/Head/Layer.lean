-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Head/Layer.lean: one layer of a product tree as a masked sumcheck with short messages.

A layer states that a hidden value is the sum, over the corners of a cube under the equality
weights of a public point, of the product of two vectors (its two halves). The verifier's routine
runs a masked sumcheck on it: the sum of a hiding polynomial and a factor eps; one round for each
variable, of degree 2, in which the constant coefficient is not sent; one round in a further
variable Y, whose challenge is not 0; the two end values. It leaves one claim on mask entries (the
row) and, for each half, the claim that its extension at the point of challenges is the hidden end
value.

Here a layer is a record of data (LayerKind), from which the library's builder for a sum of
products of maps (Cb/Part/LdPartPsc.lean) makes the parameters of the library's sumcheck. The block
is the sumcheck with short messages at these parameters (Cb/G6/Pick.lean: the constant coefficient
is left out). Its knowledge soundness between the sumcheck's own joints follows from the degrees.

Main definitions: placeNo, LayerKind, LayerKind.sm, places, our, par, R, err.
Main theorems: LayerKind.ok, conds, knowAt, eq0, out_some, nums, in_iff, end_iff, F_at, s0_at.

The places of the masks. The layer's slots are counted from the slot of the hiding polynomial's
sum. The coefficients of the hiding polynomial lie under the first 2 k + 3 slots: by variable, then
by degree from 1 up; the further variable has its constant first. The masks of the two end values
follow.

What is not claimed. That the verifier's routine computes this block's output is not shown here.
Soundness does not depend on the places of the masks; that they are the routine's is not shown
here. Nothing is said about hiding.


-/
import Cb.G6.Pick
import Cb.G6.Join
import Cb.Part.LdPartPscProofs
import Cb.Part.LdPartVarsProofs
import Cb.Ld.LdPscProofsOur

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Head
open Iop Prob TWhole

/-- The slot of a coefficient of the hiding polynomial, counted from s: by variable, then by degree
from 1 up; the last variable has the constant first. -/
def placeNo {E : Type} : (l : List (PFmt E)) → ℕ → PIdx l → ℕ
  | [], s, _ => s
  | [_], s, .inl t => s + 1 + t.val
  | [_], s, .inr _ => s
  | _ :: _ :: _, s, .inl t => s + t.val
  | f :: f' :: l, s, .inr i => placeNo (f' :: l) (s + f.n) i

/-- The data of a layer. St: what is public before the layer. J: the entries that are committed
before the layer's first draw; that they are is the caller's to show. -/
structure LayerKind (E St J : Type) where
  /-- the number of variables -/
  k : ℕ
  /-- the point of the equality weights -/
  pt : St → Fin k → E
  /-- the two halves, as vectors on the corners of the cube: false is the left one -/
  half : St → (J → E) → Bool → (Fin k → Bool) → E
  /-- the form in mask entries that comes in with the claim -/
  inc : Slf E St J
  /-- the mask entry of the layer's slot number i -/
  mask : ℕ → J

namespace LayerKind
variable {E St J : Type} [Field E] [Fintype E] [Fintype J] (L : LayerKind E St J)

/-- The summand: the product of the extensions of the two halves. -/
@[reducible] def sm : LdPartSm E St J where
  k := L.k
  A := Bool
  F := fun st m a z => Alg.mle (L.half st m a) z
  terms := [⟨fun _ _ => 1, [false, true]⟩]
  w := fun st i => some (L.pt st i)

/-- Degrees and places. -/
@[reducible] noncomputable def places : LdPartMk L.sm where
  n := fun _ => 2
  DY := 2
  slS := L.inc
  wAt := fun i => L.mask (placeNo _ 0 i)
  cAt := fun a => L.mask (2 * L.k + 3 + if a then 1 else 0)

/-- The parameters of the library's sumcheck. -/
noncomputable abbrev our : PscOur E := L.sm.our L.places
noncomputable abbrev par : PscPar E := L.our.par

omit [Fintype J] in
/-- The builder's conditions: each half's extension has degree 1 in each variable. -/
theorem ok : L.sm.OK L.places (fun _ _ => 1) where
  map := fun _ _ _ => Alg.DegLE.mle _
  fit := fun t ht => by
    obtain rfl := List.mem_singleton.1 ht
    exact ⟨fun _ => 0, fun _ => Alg.DegLE.const _ _, fun _ => le_refl 2⟩
  plain := fun _ _ h => by cases h
  dy := fun t ht => by
    obtain rfl := List.mem_singleton.1 ht
    exact le_refl 2

/-- The three conditions of the sumcheck's soundness. -/
theorem conds : L.par.VarsOK ∧ L.par.DegOK ∧ L.par.ValInj := by
  obtain ⟨hV, hI, hX, hY⟩ := ldPartPsc_ok E St J L.sm L.places _ L.ok
  exact ⟨(psc_our_ok E L.our).1 hV, psc_our_deg E L.our hX hY, (psc_our_ok E L.our).2 hI⟩

variable (Ex : ExtSpec)

/-- The block. -/
noncomputable def R : IOR (E × St) Ex L.par.Out Ex := (V₀ L.par Ex).R

/-- Its errors, as counts of draws. -/
noncomputable def err : Err (L.R Ex).shape := (V₀ L.par Ex).ε

/-- The block between the sumcheck's own joints. A0: whatever else is claimed rides along. -/
theorem knowAt (M Wp Kc : Type) (A0 : IOR.Rels Kc St Ex (M × Wp)) (msg : M → J → E) :
    KnowAt (L.R Ex) (L.par.baseIn A0 fun w => msg w.1) (L.par.baseOut A0 fun w => msg w.1)
      (fun _ _ _ wp => wp) (L.err Ex) :=
  (V₀ L.par Ex).know L.conds.1 L.conds.2.1 L.conds.2.2 M Wp Kc A0 msg

/-- Every variable's weights sum to 1, so the constant coefficient may be the one that is left
out. -/
theorem eq0 : Eq0 L.par :=
  our_eq0 L.our fun st => ldPart_eq0 L.k (fun _ => 2) (L.pt st)

/-- The block rejects no transcript: its output is the value that Cb/G6/Value.lean writes out. So
the soundness property is not met for want of an output. -/
theorem out_some (x : E × St) (y : Ex.Str) (τ : Tr (Johnson.L5.Layers.shapeS L.par)) :
    (L.R Ex).out x y τ = some (shortV L.par (F₀ L.par) x τ) :=
  short_out L.par (F₀ L.par) Ex (F₀_ok L.par L.eq0) x y τ

/-- The errors: 1 for eps, 2 for each variable, 2 for the further variable (of the elements other
than 0), 0 for the round of the end values. -/
theorem nums : errList (L.err Ex) = 1 :: (List.replicate L.k 2 ++ [2] ++ [0]) := by
  have h := (V₀ L.par Ex).nums
  rw [psc_our_degs E L.our, ldPartVars_degs E L.k fun _ => 2, List.ofFn_const] at h
  exact h

/-- What the claim before the layer says: the sum over the corners, under the equality weights, of
the product of the two halves, plus the incoming form, is the target. -/
theorem in_iff (τ : E) (st : St) (m : J → E) :
    L.par.SumHolds (τ, st) m ↔
      ∑ b : Fin L.k → Bool, Alg.eqk (L.pt st) b * (L.half st m false b * L.half st m true b) +
        ∑ j, L.inc st j * m j = τ := by
  refine (psc_our_sum E L.our (τ, st) m).trans
    ((ldPartPsc_sum E St J L.sm L.places τ st m).trans ?_)
  have e : ∀ b : Fin L.k → Bool,
      (∏ i, ldPartWt (L.sm.w st i) (b i)) * L.sm.val st m (Alg.corner b) =
        Alg.eqk (L.pt st) b * (L.half st m false b * L.half st m true b) := by
    intro b
    have e1 : L.sm.val st m (Alg.corner b) = L.half st m false b * L.half st m true b := by
      simp [LdPartSm.val, LdPartSm.pol, LayerKind.sm, Alg.mle_corner]
    rw [e1]
    rfl
  have hs : ∑ b : Fin L.k → Bool,
        (∏ i, ldPartWt (L.sm.w st i) (b i)) * L.sm.val st m (Alg.corner b) =
      ∑ b : Fin L.k → Bool,
        Alg.eqk (L.pt st) b * (L.half st m false b * L.half st m true b) :=
    Finset.sum_congr rfl fun b _ => e b
  constructor
  · intro h
    exact (congrArg (· + ∑ j, L.inc st j * m j) hs).symm.trans h
  · intro h
    exact (congrArg (· + ∑ j, L.inc st j * m j) hs).trans h

/-- What the claim on an end value says: the half's extension at the point of challenges, plus the
last challenge times the end value's mask entry, is what was sent. -/
theorem end_iff (o : L.par.Out) (m : J → E) (a : Bool) :
    L.par.EHolds o m a ↔
      Alg.mle (L.half o.st m a) (L.sm.outPt L.places o) +
        m (L.mask (2 * L.k + 3 + if a then 1 else 0)) * L.sm.outB L.places o = o.vals a :=
  ldPartPsc_val E St J L.sm L.places o m a

/-- The map of a half at the point of an output statement, as the sumcheck's parameters write it,
is the half's extension at the point of challenges. -/
theorem F_at (o : L.par.Out) (m : J → E) (a : Bool) :
    L.our.F o.st m a (L.our.ini o.st (L.par.hp o.st o.pt)) =
      Alg.mle (L.half o.st m a) (L.sm.outPt L.places o) :=
  congrArg (Alg.mle (L.half o.st m a))
    (ldPartVars_ini E L.k (fun _ => 2) (ldPartDat E L.k (fun _ => 2) (L.sm.w o.st))
      (pDummy E 2) (pDummyD E 2) o.pt)

/-- The public part of the row: the product of the two values that were sent. -/
theorem s0_at (o : L.par.Out) :
    L.par.S0 o.st (L.par.hp o.st o.pt) o.vals = o.vals false * o.vals true := by
  rw [ldPartPsc_s0 E St J L.sm L.places o]
  simp [LdPartSm.pol, LayerKind.sm]

end LayerKind

end Cb.Pv.Head

#print axioms Cb.Pv.Head.LayerKind.knowAt
#print axioms Cb.Pv.Head.LayerKind.out_some
#print axioms Cb.Pv.Head.LayerKind.nums
#print axioms Cb.Pv.Head.LayerKind.in_iff
#print axioms Cb.Pv.Head.LayerKind.end_iff
#print axioms Cb.Pv.Head.LayerKind.F_at
#print axioms Cb.Pv.Head.LayerKind.s0_at
