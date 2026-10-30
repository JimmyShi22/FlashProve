-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/JobsSpecTies.lean: the honest side of the kind "lookup" (K3): at a
proof file's lookup the public factor and the table by which the verifier's text goes are those that
the specification's jobs read. Two theorems with a helper; no definition.

Terms. Honest/K3/GLOSSARY.md ("specification", "face", "library's field").

Why it is wanted. The tie's first masked sumcheck claims Z - a P_1^2 G_0 = 0. The verifier's text
takes a from the face (`Face.factor`, on the program's elements: one run of padding keys for each
tree). The specification's job takes a from its public numbers (`Data.a`: one padding row for each
call). If the two were not one element, the honest polynomial in Y would belong to another claim
than the one that is left.
The leaves' sumcheck ends at 1 + (the planes' value at the point) times (alpha - 1 - the table's row
at the point). The verifier's text takes the second factor from the face; the specification's job
sums over `Nums.tab`.

What is shown.
  `fold_up`: a product that is folded from two starts with one reading has one reading.
  `factor_tie`: under `FoNums.ok h`: the face's factor, read in the library's field, is `Data.a` at
    `Fo.numsF h lm jLK`.
  `leaf_tie`: under `FoNums.ok h`, at a point of 5 + d coordinates: the face's `leaf`, read, is the
    extension of alpha - 1 - `Nums.tab` at the rows' coordinates of the translated point: the factor
    of the planes' value in `TwV.rowEnd`.

Hypotheses that remain.
  `hok`: the test `FoNums.ok h` of the shape's public numbers.
  `hz`: (in `leaf_tie`) the point has 5 + d coordinates.
  In `fold_up`, without a name, in front of an arrow: the two starts read as one element.

How the proof goes. It rests on `Fo.fac_val'` and `Fo.ok_callOf`
(OnBytes/Tie/Pv/Lookup/Forest/FoTwinsFac.lean) and `Cb.Fo.PadFac.pad_fac`
(OnBytes/Tie/Pv/Lookup/Forest/FoPadFac.lean); for the table on `Fo.leavesA_val`
(OnBytes/Tie/Pv/Lookup/Port/FoTwins.lean), `Fo.tab_ext_g`
(OnBytes/Tie/Pv/Lookup/Forest/FoPlaneRows.lean) and `Fo.ok_k64`
(OnBytes/Tie/Pv/Lookup/Forest/FoEndsTwins.lean).

Limits. Conditional on the test `FoNums.ok h` of the shape's public numbers; this file shows no
shape that passes it. Shown in part: Honest/K3/Law/SitesOk.lean (`sites_shape_ok`): the shape of
every site of a public part passes it. That theorem too exhibits no shape: it speaks of whatever
sites a public part has. A shape that passes it, by evaluation: Honest/K3/FastLaw/RealMember.lean
[not in this library].
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.JobsSpec
import OnBytes.Tie.Pv.Lookup.Forest.FoTwinsFac
import OnBytes.Tie.Pv.Lookup.Forest.FoEndsTwins

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3
open OnBytes (E zeroE oneE mulE powE subE)

/-- A product folded from two starts that are read as one element is read as one element. -/
theorem fold_up {α : Type} (g : α → E) : ∀ (l : List α) (a b : E), up a = up b →
    up (l.foldl (fun a y => mulE a (g y)) a) = up (l.foldl (fun a y => mulE a (g y)) b)
  | [], _, _, h => h
  | y :: l, a, b, h => by
    simp only [List.foldl_cons]
    refine fold_up g l _ _ ?_
    show OnBytes.Slice.readE _ = OnBytes.Slice.readE _
    rw [OnBytes.Slice.readE_mul, OnBytes.Slice.readE_mul]
    exact congrArg (· * _) h

/-- **The face's public factor is the specification's.** Conditional on `FoNums.ok h`. -/
theorem factor_tie (h : OnBytes.Model.Forest.Shape) (hok : FoNums.ok h = true) (lm jLK : Nat)
    (w : Hidden) (p : Pts) :
    up ((VerifiableInference.Desc.K3.faceOf h).factor p.theta p.alpha) =
      (dataAt (fun theta => _root_.Fo.numsF h lm jLK theta) w p).a := by
  have e1 : (dataAt (fun theta => _root_.Fo.numsF h lm jLK theta) w p).a =
      TwV.fac (_root_.Fo.numsF h lm jLK (up p.theta)) (up p.alpha) := rfl
  rw [e1, Cb.Fo.PadFac.pad_fac h hok lm jLK]
  refine Eq.trans ?_ (_root_.Fo.fac_val' OnBytes.Model.Reading.gl h p.theta p.alpha
    (fun y hy => _root_.Fo.ok_callOf hok y hy))
  show up _ = up _
  unfold VerifiableInference.Desc.K3.Face.factor VerifiableInference.Desc.K3.faceOf
  simp only [List.foldl_cons, List.foldl_map]
  refine fold_up _ _ _ _ ?_
  show OnBytes.Slice.readE _ = OnBytes.Slice.readE _
  rw [OnBytes.Slice.readE_mul, OnBytes.Slice.readE_one, one_mul]

/-- **The face's table at the leaves' point is the specification's.** Conditional on `FoNums.ok h`,
at a point of 5 + d coordinates (`hz`). -/
theorem leaf_tie (h : OnBytes.Model.Forest.Shape) (hok : FoNums.ok h = true) (lm jLK : Nat)
    (theta alpha : E) (zb0 : Array E) (hz : zb0.size = 5 + h.d) :
    up ((VerifiableInference.Desc.K3.faceOf h).leaf theta alpha zb0) =
      ((List.range (2 ^ h.d)).map fun r =>
        TwV.eqN ((byBit zb0).drop 5) r *
          (up alpha - 1 - (_root_.Fo.numsF h lm jLK (up theta)).tab r)).sum := by
  obtain ⟨_, _, _, _, _, _, hN, _⟩ := Cb.Fo.ok_parts hok
  have e := _root_.Fo.tab_ext_g h hok (up theta) (up alpha) (byBit zb0)
    (by simp [byBit, ups, hz, FoNums.w])
  refine Eq.trans ?_ e.symm
  have e2 : (byBit zb0).reverse = _root_.Fo.rdL OnBytes.Model.Reading.gl zb0 := by
    simp [byBit, ups, _root_.Fo.rdL]
    exact fun _ _ => rfl
  rw [e2]
  exact _root_.Fo.leavesA_val OnBytes.Model.Reading.gl h theta alpha zb0 (by omega)
    (_root_.Fo.ok_k64 hok)

#print axioms ProofFile.Honest.K3.leaf_tie
#print axioms ProofFile.Honest.K3.fold_up
#print axioms ProofFile.Honest.K3.factor_tie

end ProofFile.Honest.K3
