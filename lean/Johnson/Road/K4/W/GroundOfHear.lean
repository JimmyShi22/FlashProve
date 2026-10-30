-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/W/GroundOfHear.lean: CONDITIONAL.

Not shown here. THAT A FORM IS WORTH 0 ANYWHERE. That a hearing returns. The nine facts hold at the
public parameters' own data of the layers, under the library's head (`k4Plan_head`,
Johnson/Desc/ProofFile/Honest/K4/Law/W/PlanHead.lean); the switches (Switches hS) fail at a shape
without routed experts (said here without a theorem). Nothing on soundness, on completeness or on
any other property. No property is claimed.

The public hypothesis K4Ground (W/Ground.lean) at what a hearing of the layers' own rounds
(sub-protocol K4) returned, from the hearing's return and nine public facts on the plan.

  `K4Plan hS pc P g tl D`   the nine public facts on the plan.
  `ground_of_hear`   where the hearing returns o, K4Ground holds at o's parts, the group is g and
      the layout is the plan's.
-/
import Johnson.Road.K4.W.Ground
import Johnson.Road.K4.PubOfHearTied

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.W
open OnBytes OnBytes.Model OnBytes.Road OnBytes.K.Kc
open OnBytes.Model.Layer (Env Lay Heard Pub Own Reads layout scalesHeld readsOf)
open Inst.Model.FFSeg (Dim)
open OnBytes.Desc.First.K4 (engFl hear)

/-- **The public facts on the plan.** This defines a hypothesis; the definition claims nothing. -/
structure K4Plan (hS : Layer.Shape) (pc : List (List String)) (P : Pub) (g : ℕ) (tl : HTailF2)
    (D : Dim) : Prop where
  lay : layout hS pc = .ok P.y
  sw : Switches hS
  scales : scalesHeld hS P.sc = .ok ()
  grp : g < P.y.NGr
  reads : readsOf P.y = .ok P.rd
  tails : ((P.tails.getD g {}).mats.map fun M => (M.m, M.k)) = matsR P.y g
  mats : (tl.mats.map fun M => (M.m, M.k)) = matsR P.y g
  NM : tl.NM = tl.mats.size
  sized : Sized hS D

/-- **K4Ground at what a hearing returned.** CONDITIONAL: on the hearing's return and on A. -/
theorem ground_of_hear {P : Pub} {hp : Layer.HPlan2} {g : ℕ} {fo : Forest.Heard} {F G : Fork}
    {t u : Tape} {o : Own} (h : hear engFl P hp g fo F t = some (o, G, u)) {hS : Layer.Shape}
    {pc : List (List String)} {tl : HTailF2} {D : Dim} (A : K4Plan hS pc P g tl D) :
    o.v.g = g ∧ o.v.y = P.y ∧
      ∃ r pts, K4Ground hS pc o.v P.rd r tl o.H o.hd o.hd2 pts o.funs D := by
  obtain ⟨_, _, iU3, tab, laid, nU3, _, _, pts, hd2, _, _, e5, _, ev, _, _, ehd2, e9, e10⟩ :=
    Desc.First.K4.hear_public h
  obtain ⟨_, H1, G1, u1, G2, u2, n1, n2, _⟩ := Desc.First.K4.hear_calls h
  obtain ⟨_, _, _, _, _, _, q5, q6⟩ := Desc.First.K4.hearNorms_public n1
  obtain ⟨kfo, _, _, _, kzt, _⟩ := Desc.First.K4.hearTerms_keeps n2
  have efo : o.H.fo = fo := by rw [kfo, q6]
  have ezt : o.H.ztF = H1.ztF := kzt
  have vy : o.v.y = P.y := by rw [ev]
  have vsc : o.v.sc = P.sc := by rw [ev]
  have vg : o.v.g = g := by rw [ev]
  have vtab : o.v.tab = tab := by rw [ev]
  exact ⟨vg, vy, (tab, laid, nU3), pts,
    { lay := by rw [vy]; exact A.lay
      sw := A.sw
      scales := by rw [vsc]; exact A.scales
      grp := by rw [vg, vy]; exact A.grp
      reads := by rw [vy]; exact A.reads
      tables := by rw [vy, vg, ← A.tails]; exact e5
      tab := vtab
      mats := by rw [vy, vg]; exact A.mats
      NM := A.NM
      points := by rw [vy, ehd2]; exact e9
      zt := by rw [efo, vy, ezt]; exact Road.ok_of_toOption q5
      funs := by rw [vy, efo]; exact e10
      sized := A.sized }⟩

end OnBytes.Road.K4.W

#print axioms OnBytes.Road.K4.W.ground_of_hear
