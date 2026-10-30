-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/KeysLetters.lean: CONDITIONAL.

What is here. THE KEY VECTOR OF THE LOOKUP's CALLER AT A LAYERS' LINK, IN THE LETTERS OF THE
FEED-FORWARD LAYERS' OWN ROUNDS (sub-protocol K4). The lookup's own sentence on the keys speaks of
the caller's key vectors: forK of the layout layLay (Johnson/Desc/First/Look/K3CallerLay.lean) at
the entries μ with one more entry, read as 0. By that layout's text the vector of call c is the
library's keyVec at the reference sizes and tables, at the cells that cellsAt reads off the
matrices matsOfE μ and at the layers' matrices that layerR cuts out of wOfE μ. forK_lay says so, at
every μ. forK_lay_at is the same at other letters for the shape, the scales, the layout, the group,
the matrices and the weights, from one equation each.

  `forK_lay`      the caller's key vector of a call, unfolded; general in μ.
  `forK_lay_at`   the same at K4's letters, from seven ties.

Not shown here. That any of the seven ties holds. THE TIE ON THE WEIGHTS (hW) IS ASKED OF WHAT
layerR CUTS OUT AT LAYER 4 g + l, AT EVERY l: there is no bound, so also behind the group's four
layers and behind the model's last layer. Outside nr rows and nc columns wOfE μ reads the one entry
that is no cell, where the caller's own reading msgLay has 0. WHERE layerR READS SUCH PLACES, hW IS
A SENTENCE ON Wm OUTSIDE THE TABLE. That a tie at the group's own layers would do is not shown. The
reference sizes, tables and layout of the weights are the full size's: THE FULL SIZE ALONE. Nothing
on what a form is worth.

No property is claimed.
-/
import Johnson.Desc.First.Look.K3CallerLay

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model
open OnBytes.Road (Mats cellsOf cellsAt sclOf)
open OnBytes.Model.Layer (Lay Shape Scales)
open Inst.Model (ppref tbRef)
open Inst.Model.All (DF)
open Inst.Model.Layout (kRef)
open Inst.Model.FFSeg (keyVec layerR)
open VerifiableInference.Desc.First.Look (JLay LayPub layLay layLay_K matsOfE wOfE)

/-- **The caller's key vector of a call, unfolded.** General in the entries μ. -/
theorem forK_lay (q : LayPub) (fs : Forest.Shape) (lm first ns : ℕ) (tl : HTailF2) (nr nc : ℕ)
    (μ : JLay ns tl nr nc → Cb.Gl.E) (c : Fin 8) :
    Cb.Fo.forK Cb.Gl.E (layLay q fs lm first ns tl nr nc) () (Cb.Fo.zext μ) c.val =
      keyVec (scl := sclOf q.h q.sc q.g 4) DF (cellsOf DF (cellsAt q.y (matsOfE μ))) tbRef
        (4 * q.g) (fun l => layerR ppref kRef (wOfE μ) (4 * q.g + l)) c :=
  funext fun X => layLay_K fs lm first ns μ c X

/-- **The same at K4's letters.** CONDITIONAL: on the seven ties. hW: the tie on the weights, asked
of what layerR cuts out at layer 4 g + l, at every l. -/
theorem forK_lay_at {q : LayPub} (fs : Forest.Shape) (lm first ns : ℕ) (tl : HTailF2) (nr nc : ℕ)
    (μ : JLay ns tl nr nc → Cb.Gl.E) {h : Shape} {sc : Scales} {y : Lay} {g : ℕ}
    {Mm : Mats Cb.Gl.E} {Wm : ℕ → ℕ → Cb.Gl.E} (eh : q.h = h) (es : q.sc = sc) (ey : q.y = y)
    (eg : q.g = g) (eL : y.Lam = 4) (hM : matsOfE μ = Mm)
    (hW : ∀ l, layerR ppref kRef (wOfE μ) (4 * g + l) = layerR ppref kRef Wm (4 * g + l))
    (c : Fin 8) :
    Cb.Fo.forK Cb.Gl.E (layLay q fs lm first ns tl nr nc) () (Cb.Fo.zext μ) c.val =
      keyVec (scl := sclOf h sc g y.Lam) DF (cellsOf DF (cellsAt y Mm)) tbRef (g * y.Lam)
        (fun l => layerR DF.P kRef Wm (g * y.Lam + l)) c := by
  subst eh es ey eg hM
  rw [forK_lay, eL, Nat.mul_comm q.g 4]
  exact congrArg
    (fun w => keyVec (scl := sclOf q.h q.sc q.g 4) DF (cellsOf DF (cellsAt q.y (matsOfE μ))) tbRef
      (4 * q.g) w c) (funext hW)

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.forK_lay
#print axioms OnBytes.Road.K4.C.forK_lay_at
