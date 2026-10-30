-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoArrow.lean.
The lookup of a sub-proof, ending at a caller's joint.

`holeC` (OnBytes/Tie/Pv/Lookup/Forest/FoHole.lean) states knowledge soundness of the lookup's block
between joints of its own: `forIn`
(what rides, and each call's keys lie in that call's table) and `forOut` (what rides, and the
lookup's out-claim: the masked claim on the keys and all rows hold). A caller that goes on with a
chain of its own wants the block to end at the claim with which that chain starts. This file states
that it does, if that claim gives the lookup's out-claim.

Main names:
  `look_any`: the block ends at any joint B' whose condition on statements holds wherever
    `forOut`'s does and whose relation gives `forOut`'s.
  `jtL A0 pr G`: a joint: what rides (A0, read through pr), and a claim G on the statement and the
    messages.
  `look_arrow`: the block ends at `jtL (ShiftQ.ride R0) Prod.fst G`, if G gives the lookup's
    out-claim.
  `look_arrow_self`: the hypothesis can be met: G may be the out-claim itself, beside any other
    claim.
  `look_arrow_gl`: the same at the field Cb.Gl.E with the short sumcheck filled by V₀, V₀C: no
    hypothesis on the characteristic is left.

Under: the shape is lawful (`FoNums.ok`); the characteristic p of the finite field has
2 ^ d * (2 ^ 32 - 1) < p. `look_any`, `look_arrow` and `look_arrow_self` stand for every filling V,
VC of the short sumcheck: a filling is a record that holds the short sumcheck's knowledge soundness
as a field, and it is the user's to hand one in (OnBytes/Tie/Pv/Lookup/Forest/FoAt.lean).

Not claimed: anything on completeness or hiding. That a caller's claim gives the lookup's out-claim
is the caller's to prove. The stronger the claim G, the less the statement says: at a G that never
holds it is empty. Nor is claimed what the head of OnBytes/Tie/Pv/Lookup/Forest/FoHole.lean does not
claim, among it that the errors are small.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoAt

set_option autoImplicit false

namespace Cb.Fo
open Iop Prob Hiop IOR Cb Cb.LdLkp Cb.Lkp Cb.LdLkp.Kn TWhole

/-- What rides, read through pr, and a claim on the statement and the messages. -/
def jtL {K X X0 M Wp : Type} {Ex : ExtSpec} (A0 : Rels K X0 Ex (M × Wp)) (pr : X → X0)
    (G : X → M → Prop) : Rels K X Ex (M × Wp) :=
  ⟨fun x y w => A0.rel (pr x) y w ∧ G x w.1, fun b w => A0.relR (pr b.1, b.2) w ∧ G b.1 w.1,
    fun b => A0.on (pr b.1, b.2), A0.core⟩

section
variable (E : Type) [Field E] [Fintype E] (p : ℕ) [CharP E p] {St₀ J₀ : Type} [Fintype J₀]
  [DecidableEq J₀] (h : Sh) (L : Lay E St₀ J₀) (V : ∀ (Y : PscPar E) Ex, ShortK Y Ex)
  (VC : ∀ (Y : PscPar E) Ex, ShortKC Y Ex) {Ex : ExtSpec} {Kc M Wp : Type}
  (R0 : Rels Kc St₀ Ex (M × Wp)) (msg₀ : M → J₀ → E)

/-- The block ends at any joint whose relation gives the block's own. -/
theorem look_any (H : FoNums.ok h = true) (hp : 2 ^ h.d * (2 ^ 32 - 1) < p)
    (B' : Rels Kc (TX (St₀ × E) E (Option J₀)) Ex (M × Wp))
    (hon : ∀ b, (forOut E h L R0 msg₀).on b → B'.on b)
    (hrel : ∀ b w, B'.relR b w → (forOut E h L R0 msg₀).relR b w) :
    KnowAt (forB E h L V VC (Ex := Ex)).R (forIn E h L R0 msg₀) B' (fun _ _ _ wp => wp)
      (forB E h L V VC (Ex := Ex)).e := by
  refine knowAt_mono (holeC E p St₀ J₀ h L V VC Ex Kc M Wp R0 msg₀ H hp) (fun _ ha => ha)
    (fun _ _ _ hw => hw) ?_ hon
  intro b w
  intros
  exact hrel b w (by assumption)

/-- **The block ends at a caller's claim that gives the lookup's out-claim.** -/
theorem look_arrow (H : FoNums.ok h = true) (hp : 2 ^ h.d * (2 ^ 32 - 1) < p)
    (G : TX (St₀ × E) E (Option J₀) → M → Prop)
    (hG : ∀ x m, G x m → (forA E h L).lk.out id id x (zext (msg₀ m))) :
    KnowAt (forB E h L V VC (Ex := Ex)).R (forIn E h L R0 msg₀)
      (jtL (ShiftQ.ride R0) Prod.fst G) (fun _ _ _ wp => wp) (forB E h L V VC (Ex := Ex)).e :=
  look_any E p h L V VC R0 msg₀ H hp _ (fun _ hb => hb) fun b w hw => ⟨hw.1, hG b.1 w.1 hw.2⟩

/-- The hypothesis can be met: the out-claim itself, beside any other claim. -/
theorem look_arrow_self (H : FoNums.ok h = true) (hp : 2 ^ h.d * (2 ^ 32 - 1) < p)
    (T : TX (St₀ × E) E (Option J₀) → M → Prop) :
    KnowAt (forB E h L V VC (Ex := Ex)).R (forIn E h L R0 msg₀)
      (jtL (ShiftQ.ride R0) Prod.fst fun x m =>
        (forA E h L).lk.out id id x (zext (msg₀ m)) ∧ T x m)
      (fun _ _ _ wp => wp) (forB E h L V VC (Ex := Ex)).e :=
  look_arrow E p h L V VC R0 msg₀ H hp _ fun _ _ hg => hg.1

end

/-- At the field Cb.Gl.E, the short sumcheck filled. -/
theorem look_arrow_gl {St₀ J₀ : Type} [Fintype J₀] [DecidableEq J₀] (h : Sh)
    (L : Lay Cb.Gl.E St₀ J₀) {Ex : ExtSpec} {Kc M Wp : Type} (R0 : Rels Kc St₀ Ex (M × Wp))
    (msg₀ : M → J₀ → Cb.Gl.E) (H : FoNums.ok h = true)
    (G : TX (St₀ × Cb.Gl.E) Cb.Gl.E (Option J₀) → M → Prop)
    (hG : ∀ x m, G x m → (forA Cb.Gl.E h L).lk.out id id x (zext (msg₀ m))) :
    KnowAt (forB Cb.Gl.E h L V₀ V₀C (Ex := Ex)).R (forIn Cb.Gl.E h L R0 msg₀)
      (jtL (ShiftQ.ride R0) Prod.fst G) (fun _ _ _ wp => wp)
      (forB Cb.Gl.E h L V₀ V₀C (Ex := Ex)).e := by
  refine knowAt_mono (holeCgl St₀ J₀ h L Ex Kc M Wp R0 msg₀ H) (fun _ ha => ha)
    (fun _ _ _ hw => hw) ?_ fun _ hb => hb
  have key : ∀ b w, (jtL (ShiftQ.ride R0) Prod.fst G).relR b w →
      (forOut Cb.Gl.E h L R0 msg₀).relR b w := fun b w hw => ⟨hw.1, hG b.1 w.1 hw.2⟩
  intro b w
  intros
  exact key b w (by assumption)

end Cb.Fo
