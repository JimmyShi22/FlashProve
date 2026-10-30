-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/JoinSpell.lean: CONDITIONAL.

What is here. THE LOOKUP's JOIN IN ITS TWO SPELLINGS IS ONE CLAIM. The library states the claim
that the lookup reads at a public structure X as X.Join W Mm M
(Johnson/Road/Rows/LayerEnds34.lean): the form that the lookup's key side leaves is worth the
weighted sum of the extensions of the eight key vectors, with the weights wc and the points zc of
the library's point, which is made from the lookup's two points. The laws of this folder on the
lookup's own part (joinWorth_one's first equation, Law/JoinOne.lean; look_part_zero_heard,
Law/JoinAtHear.lean) end in the same sum with the weights that were heard (fo.e) and the points
that were sampled (zk), brought to one side. In every world the two say the same: parts_of_pub
(Law/PartsOfPub.lean) has both ties. parts_of_pub asks a world with the true entries; joinK_spell's
statement names none, so its proof supplies one.

  `joinK_spell`      the library's weighted sum, in the heard weights and the sampled points.
  **`join_iff_part`**   the title's sentence.

Not shown here. Either side. No theorem says that a structure X exists (the head of
Johnson/Road/Rows/LayerEnds34Ref.lean). The letters of look_part_zero_heard's end are not laid
against X's here (the heard data, alpha, theta, the table, the cells, the weights' matrix): that
wants X's ties to the hearing. THE FULL SIZE ALONE (X).

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.PartsOfPub

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes (E zeroE)
open OnBytes.Model (Reading World)
open OnBytes.Road (pt padOf sclOf cellsAt cellsOf Mats Wm)
open OnBytes.Road.K4 (entryOf)
open Inst.Model (Scl)
open Inst.Model.FFSeg (aC keyVec layerR)

/-- The library's weighted sum, in the heard weights and the sampled points. CONDITIONAL: on every
hypothesis named. THE FULL SIZE ALONE (X). -/
theorem joinK_spell [scl : Scl] (X : OnBytes.Road.Rows.Pub34 Cb.Gl.E) (Xρ : X.ρ = Reading.gl)
    (hscl : scl = sclOf X.h X.p.v.sc X.p.v.g X.p.v.y.Lam) (Mm : Mats Cb.Gl.E) (M : Wm Cb.Gl.E) :
    X.joinK Mm M =
      (∑ q : Fin 8, Reading.gl.val (X.H.fo.e.getD q.val zeroE) *
        (Reading.gl.val X.alpha - (q.val : Cb.Gl.E) * Reading.gl.val X.theta -
          Blocks.ext (aC X.D q)
            (keyVec X.D (cellsOf X.D (cellsAt X.p.v.y Mm)) X.tb (X.c.v.g * X.c.v.y.Lam)
              (fun l => layerR X.D.P X.lk M (X.c.v.g * X.c.v.y.Lam + l)) q)
            (pt Reading.gl (X.p.v.zk.getD q.val #[])))) +
      Reading.gl.val (padOf X.H) := by
  obtain ⟨_, _, Lz, Lw, _, _⟩ := parts_of_pub X Xρ hscl
    ⟨fun _ => 0, entryOf X.ρ X.tl X.funs X.p.v.iU3 X.p.v.K3 Mm⟩ Mm rfl (X.c.v.g * X.c.v.y.Lam)
    (fun l => layerR X.D.P X.lk M (X.c.v.g * X.c.v.y.Lam + l))
  unfold OnBytes.Road.Rows.Pub34.joinK
  rw [← hscl, Xρ]
  exact congrArg (· + Reading.gl.val (padOf X.H)) (Finset.sum_congr rfl fun c _ => by
    rw [Lw c, OnBytes.Road.ext_congr_pt _ _ (Lz c)])

/-- **The lookup's join in its two spellings is one claim.** CONDITIONAL: on every hypothesis named.
THE FULL SIZE ALONE (X). -/
theorem join_iff_part [scl : Scl] (X : OnBytes.Road.Rows.Pub34 Cb.Gl.E) (Xρ : X.ρ = Reading.gl)
    (hscl : scl = sclOf X.h X.p.v.sc X.p.v.g X.p.v.y.Lam) (W : World Cb.Gl.E) (Mm : Mats Cb.Gl.E)
    (M : Wm Cb.Gl.E) :
    X.Join W Mm M ↔
      (∑ q : Fin 8, Reading.gl.val (X.H.fo.e.getD q.val zeroE) *
        (Reading.gl.val X.alpha - (q.val : Cb.Gl.E) * Reading.gl.val X.theta -
          Blocks.ext (aC X.D q)
            (keyVec X.D (cellsOf X.D (cellsAt X.p.v.y Mm)) X.tb (X.c.v.g * X.c.v.y.Lam)
              (fun l => layerR X.D.P X.lk M (X.c.v.g * X.c.v.y.Lam + l)) q)
            (pt Reading.gl (X.p.v.zk.getD q.val #[])))) +
      Reading.gl.val (padOf X.H) -
        X.H.fo.cEnd.value Reading.gl W = 0 := by
  have e := joinK_spell X Xρ hscl Mm M
  unfold OnBytes.Road.Rows.Pub34.Join
  rw [Xρ, e]
  constructor
  · intro q
    rw [q]
    exact sub_self _
  · intro q
    exact (sub_eq_zero.mp q).symm

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.joinK_spell
#print axioms ProofFile.Honest.K4.join_iff_part
