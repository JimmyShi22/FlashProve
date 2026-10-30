-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoAt.lean: the lookup of a sub-proof with the short sumcheck filled,
and at the challenge field.

HoleC and forB_four are stated for every filling V, VC of the short sumcheck. Such a filling is a
record with a field that is a proposition (knowledge soundness of the short sumcheck at its own
joints), so a statement «for every V, VC» leaves it to its user to hand one in. Here the filling is
the named one, V₀ and V₀C (Cb/G6/Pick.lean).
 - HoleC₀: the statement of HoleC at V₀, V₀C, a closed proposition; holeC₀ proves it. Of the
   statements on the knowledge soundness of a sub-proof's lookup this is the one to use. HC and
   HCgen (OnBytes/Tie/Pv/Lookup/Holes/HoleC.lean) are the forms for every record of letters, HoleC
   is the form for every filling.
 - HoleCgl: the same at the challenge field Cb.Gl.E. The one premise left is FoNums.ok h = true, a
   test on the forest's public numbers: the premise on the characteristic follows from the test's
   clause 2^(d + 32) < p.
 - forB_four_gl: the three facts of forB_four (OnBytes/Tie/Pv/Lookup/Forest/FoFour.lean) at V₀, V₀C
   and Cb.Gl.E, for every setting over the prime p with extension degree 3 and every plan that the
   verifier's planner makes of the forest's sizes.

Main definitions: HoleC₀, HoleCgl. Main theorems: holeC₀, holeCgl, forB_four_gl.
Letters that stay: the forest h, the caller's layout L, the joint R0, the reading msg₀, Ex.
Not claimed: that the planner does not refuse; whatever the heads of
OnBytes/Tie/Pv/Lookup/Forest/FoHole.lean and OnBytes/Tie/Pv/Lookup/Forest/FoFour.lean do not claim.
That FoNums.ok h follows from the success of Forest.shape and Forest.pubAsk is shape_ok
(OnBytes/Tie/Pv/Lookup/Port/FoShape.lean).
Not claimed: anything on completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoFour
import Cb.G6.Pick

set_option autoImplicit false

namespace Cb.Fo
open Iop Prob Hiop IOR Cb Cb.LdLkp Cb.Lkp Cb.LdLkp.Kn TWhole TwRound TwPlan TwErr TwLaw OnBytes.G4
open OnBytes.Params (Setting Scope Planned finish planForest)

/-- The lookup of a sub-proof, the short sumcheck filled: knowledge soundness between the block's
own joints. -/
def HoleC₀ : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (p : ℕ) [CharP E p] (St₀ J₀ : Type) [Fintype J₀]
      [DecidableEq J₀]
    (h : Sh) (L : Lay E St₀ J₀) (Ex : ExtSpec) (Kc M Wp : Type) (R0 : Rels Kc St₀ Ex (M × Wp))
        (msg₀ : M → J₀ → E),
    FoNums.ok h = true → 2 ^ h.d * (2 ^ 32 - 1) < p →
    KnowAt (forB E h L V₀ V₀C (Ex := Ex)).R (forIn E h L R0 msg₀) (forOut E h L R0 msg₀)
        (fun _ _ _ wp => wp)
      (forB E h L V₀ V₀C (Ex := Ex)).e

theorem holeC₀ : HoleC₀ := fun E _ _ p _ St₀ J₀ _ _ h L Ex Kc M Wp R0 msg₀ H hp =>
  holeC E p St₀ J₀ h L V₀ V₀C Ex Kc M Wp R0 msg₀ H hp

/-- the verifier's prime is the challenge field's characteristic -/
theorem pW_gl : OnBytes.pW.toNat = Cb.Gl.p := by decide +kernel

/-- The same at the challenge field: one premise, a test on public numbers. -/
def HoleCgl : Prop :=
  ∀ (St₀ J₀ : Type) [Fintype J₀] [DecidableEq J₀] (h : Sh) (L : Lay Cb.Gl.E St₀ J₀) (Ex : ExtSpec)
      (Kc M Wp : Type)
    (R0 : Rels Kc St₀ Ex (M × Wp)) (msg₀ : M → J₀ → Cb.Gl.E),
    FoNums.ok h = true →
    KnowAt (forB Cb.Gl.E h L V₀ V₀C (Ex := Ex)).R (forIn Cb.Gl.E h L R0 msg₀)
        (forOut Cb.Gl.E h L R0 msg₀) (fun _ _ _ wp => wp)
      (forB Cb.Gl.E h L V₀ V₀C (Ex := Ex)).e

theorem holeCgl : HoleCgl := fun St₀ J₀ _ _ h L Ex Kc M Wp R0 msg₀ H =>
  holeC₀ Cb.Gl.E Cb.Gl.p St₀ J₀ h L Ex Kc M Wp R0 msg₀ H (ok_wrap H (le_of_eq pW_gl))

/-- forB_four at V₀, V₀C and the challenge field. -/
theorem forB_four_gl {St₀ J₀ : Type} [Fintype J₀] [DecidableEq J₀] (h : Sh) (L : Lay Cb.Gl.E St₀ J₀)
    (Ex : ExtSpec) (Kc M Wp : Type)
    (R0 : Rels Kc St₀ Ex (M × Wp)) (msg₀ : M → J₀ → Cb.Gl.E) (H : FoNums.ok h = true)
    (s : Setting) (sc : Scope) (hs : s.p = Cb.Gl.p ∧ s.degree = 3) (P : Planned)
    (hf : finish s sc (planForest (OnBytes.Model.forestSize h)) = .ok P) :
    KnowAt (forB Cb.Gl.E h L V₀ V₀C (Ex := Ex)).R (forIn Cb.Gl.E h L R0 msg₀)
        (forOut Cb.Gl.E h L R0 msg₀) (fun _ _ _ wp => wp)
      (forB Cb.Gl.E h L V₀ V₀C (Ex := Ex)).e ∧
    ShapeIs Cb.Gl.E (forB Cb.Gl.E h L V₀ V₀C (Ex := Ex)).R.shape (P.rounds.map (·.entry)) ∧
    ∃ Q : List Quad,
      Q.map (·.1) = errList (forB Cb.Gl.E h L V₀ V₀C (Ex := Ex)).e ∧
      Q.map (·.2.1) = (forB Cb.Gl.E h L V₀ V₀C (Ex := Ex)).R.shape.map (fun r => Nat.card r.Chal) ∧
      Q.map (fun x => errOf s sc x.2.2) = P.rounds.map (·.error) ∧
      ∀ x ∈ Q, x.1 * bOf s.cardE x.2.2.2 = x.2.2.1 * x.2.1 :=
  forB_four Cb.Gl.E h L V₀ V₀C Ex Cb.Gl.p Kc M Wp R0 msg₀ H (ok_wrap H (le_of_eq pW_gl)) s sc
    (by rw [OnBytes.Params.Setting.cardE, hs.1, hs.2]; exact Cb.Gl.gl_card.2.1.symm) P hf

end Cb.Fo
