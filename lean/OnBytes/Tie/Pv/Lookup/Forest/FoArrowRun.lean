-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoArrowRun.lean.
The lookup of a sub-proof, ending at a caller's free joint, with the run in hand.

OnBytes/Tie/Pv/Lookup/Forest/FoArrow.lean lets the lookup's block end at any joint B' whose relation
gives the block's own
out-relation.
Here both hypotheses on B' may use that the statement at hand is put out by a run of the block from
a statement that meets the in-joint's condition; and B' may say so in its own condition on
statements, so that blocks behind may use it.

Main names:
  `knowAt_into`: for any block with `KnowAt` from A to B: it ends at B', if at every statement b put
    out by a run from a statement with A's condition, B's condition gives B''s, and B''s relation
    gives B's.
  `RunOf R A b`: b is put out by a run of R from a statement with A's condition.
  `withRun R A pr A0`: the joint A0, read through pr, whose condition on statements says also
    `RunOf`.
  `look_any_run`: the lookup's block ends at a free joint B', with the run in hand in both
    hypotheses.
  `look_arrow_run`: the lookup's block ends at `jtL (withRun .. pr A0) id G`, for ANY joint A0 over
    any type of statements, read through a map pr from the out-statements: if R0's condition at the
    caller's state gives A0's, and A0's relation with
    G gives R0's relation at the caller's state and the lookup's out-claim. What rides through the
    lookup (R0) and what rides on behind it (A0) are two letters.
  `look_arrow_run_gl`: the same at the field Cb.Gl.E with the short sumcheck filled.

Under: the shape is lawful (`FoNums.ok`); the characteristic p of the finite field has
2 ^ d * (2 ^ 32 - 1) < p. `look_any_run` and `look_arrow_run` stand for every filling V, VC of the
short sumcheck, which is the user's to hand in (OnBytes/Tie/Pv/Lookup/Forest/FoAt.lean).

Not claimed: anything on completeness or hiding. That a caller's joint meets the two hypotheses is
the caller's to prove.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoArrow

set_option autoImplicit false

namespace Cb.Fo
open Iop Prob Hiop IOR Cb Cb.LdLkp Cb.Lkp Cb.LdLkp.Kn TWhole

/-- b is put out by a run of R from a statement with A's condition. -/
def RunOf {K Xi Xo W : Type} {Ei Eo : ExtSpec} (R : IOR Xi Ei Xo Eo) (A : Rels K Xi Ei W)
    (b : Xo × Eo.Str) : Prop :=
  ∃ a τ, A.on a ∧ R.red.out a τ = some b

/-- A block ends at B', with the run in hand. -/
theorem knowAt_into {K M Xi Xo Wi Wo : Type} {Ei Eo : ExtSpec} {R : IOR Xi Ei Xo Eo}
    {A : Rels K Xi Ei (M × Wi)} {B B' : Rels K Xo Eo (M × Wo)}
    {ext : M → Xi × Ei.Str → Tr R.shape → Wo → Wi} {ε : Err R.shape} (g : KnowAt R A B ext ε)
    (hon : ∀ b, B.on b → RunOf R A b → B'.on b)
    (hrel : ∀ b w, B.on b → RunOf R A b → B'.relR b w → B.relR b w) : KnowAt R A B' ext ε where
  point := g.point
  isLocal := g.isLocal
  onOut := fun a τ b ha hb => hon b (g.onOut a τ b ha hb) ⟨a, τ, ha, hb⟩
  know := fun m a ha =>
    Doomed.mono _ _
      (fun τ hτ b w hb hw => hτ b w hb (hrel b _ (g.onOut a τ b ha hb) ⟨a, τ, ha, hb⟩ hw))
      (g.know m a ha)

/-- A0, read through pr; the condition on statements says also that the statement is put out by a
run of R from a statement with A's condition. -/
def withRun {K Xi Xo X0 W W' : Type} {Ei Eo : ExtSpec} (R : IOR Xi Ei Xo Eo) (A : Rels K Xi Ei W)
    (pr : Xo → X0) (A0 : Rels K X0 Eo W') : Rels K Xo Eo W' :=
  ⟨fun x y w => A0.rel (pr x) y w, fun b w => A0.relR (pr b.1, b.2) w,
    fun b => A0.on (pr b.1, b.2) ∧ RunOf R A b, A0.core⟩

section
variable (E : Type) [Field E] [Fintype E] (p : ℕ) [CharP E p] {St₀ J₀ : Type} [Fintype J₀]
  [DecidableEq J₀] (h : Sh) (L : Lay E St₀ J₀) (V : ∀ (Y : PscPar E) Ex, ShortK Y Ex)
  (VC : ∀ (Y : PscPar E) Ex, ShortKC Y Ex) {Ex : ExtSpec} {Kc M Wp : Type}
  (R0 : Rels Kc St₀ Ex (M × Wp)) (msg₀ : M → J₀ → E)

/-- The lookup's block ends at a free joint, with the run in hand. -/
theorem look_any_run (H : FoNums.ok h = true) (hp : 2 ^ h.d * (2 ^ 32 - 1) < p)
    (B' : Rels Kc (TX (St₀ × E) E (Option J₀)) Ex (M × Wp))
    (hon : ∀ b, R0.on (b.1.1.1, b.2) →
      RunOf (forB E h L V VC (Ex := Ex)).R (forIn E h L R0 msg₀) b → B'.on b)
    (hrel : ∀ b w, R0.on (b.1.1.1, b.2) →
      RunOf (forB E h L V VC (Ex := Ex)).R (forIn E h L R0 msg₀) b → B'.relR b w →
      R0.relR (b.1.1.1, b.2) w ∧ (forA E h L).lk.out id id b.1 (zext (msg₀ w.1))) :
    KnowAt (forB E h L V VC (Ex := Ex)).R (forIn E h L R0 msg₀) B' (fun _ _ _ wp => wp)
      (forB E h L V VC (Ex := Ex)).e :=
  knowAt_into (holeC E p St₀ J₀ h L V VC Ex Kc M Wp R0 msg₀ H hp) hon hrel

/-- **What rides through the lookup and what rides on behind it are two letters.** -/
theorem look_arrow_run (H : FoNums.ok h = true) (hp : 2 ^ h.d * (2 ^ 32 - 1) < p) {X0 : Type}
    (pr : TX (St₀ × E) E (Option J₀) → X0) (A0 : Rels Kc X0 Ex (M × Wp))
    (G : TX (St₀ × E) E (Option J₀) → M → Prop)
    (hon : ∀ b, R0.on (b.1.1.1, b.2) →
      RunOf (forB E h L V VC (Ex := Ex)).R (forIn E h L R0 msg₀) b → A0.on (pr b.1, b.2))
    (hrel : ∀ b w, R0.on (b.1.1.1, b.2) →
      RunOf (forB E h L V VC (Ex := Ex)).R (forIn E h L R0 msg₀) b → A0.relR (pr b.1, b.2) w →
      G b.1 w.1 → R0.relR (b.1.1.1, b.2) w ∧ (forA E h L).lk.out id id b.1 (zext (msg₀ w.1))) :
    KnowAt (forB E h L V VC (Ex := Ex)).R (forIn E h L R0 msg₀)
      (jtL (withRun (forB E h L V VC (Ex := Ex)).R (forIn E h L R0 msg₀) pr A0) id G)
      (fun _ _ _ wp => wp) (forB E h L V VC (Ex := Ex)).e :=
  look_any_run E p h L V VC R0 msg₀ H hp _ (fun b h0 hr => ⟨hon b h0 hr, hr⟩)
    fun b w h0 hr hw => hrel b w h0 hr hw.1 hw.2

end

/-- At the field Cb.Gl.E, the short sumcheck filled. -/
theorem look_arrow_run_gl {St₀ J₀ : Type} [Fintype J₀] [DecidableEq J₀] (h : Sh)
    (L : Lay Cb.Gl.E St₀ J₀) {Ex : ExtSpec} {Kc M Wp : Type} (R0 : Rels Kc St₀ Ex (M × Wp))
    (msg₀ : M → J₀ → Cb.Gl.E) (H : FoNums.ok h = true) {X0 : Type}
    (pr : TX (St₀ × Cb.Gl.E) Cb.Gl.E (Option J₀) → X0) (A0 : Rels Kc X0 Ex (M × Wp))
    (G : TX (St₀ × Cb.Gl.E) Cb.Gl.E (Option J₀) → M → Prop)
    (hon : ∀ b, R0.on (b.1.1.1, b.2) →
      RunOf (forB Cb.Gl.E h L V₀ V₀C (Ex := Ex)).R (forIn Cb.Gl.E h L R0 msg₀) b →
      A0.on (pr b.1, b.2))
    (hrel : ∀ b w, R0.on (b.1.1.1, b.2) →
      RunOf (forB Cb.Gl.E h L V₀ V₀C (Ex := Ex)).R (forIn Cb.Gl.E h L R0 msg₀) b →
      A0.relR (pr b.1, b.2) w → G b.1 w.1 →
      R0.relR (b.1.1.1, b.2) w ∧ (forA Cb.Gl.E h L).lk.out id id b.1 (zext (msg₀ w.1))) :
    KnowAt (forB Cb.Gl.E h L V₀ V₀C (Ex := Ex)).R (forIn Cb.Gl.E h L R0 msg₀)
      (jtL (withRun (forB Cb.Gl.E h L V₀ V₀C (Ex := Ex)).R (forIn Cb.Gl.E h L R0 msg₀) pr A0) id G)
      (fun _ _ _ wp => wp) (forB Cb.Gl.E h L V₀ V₀C (Ex := Ex)).e :=
  knowAt_into (holeCgl St₀ J₀ h L Ex Kc M Wp R0 msg₀ H) (fun b h0 hr => ⟨hon b h0 hr, hr⟩)
    fun b w h0 hr hw => hrel b w h0 hr hw.1 hw.2

end Cb.Fo
