-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/W/OpenedOwn.lean: DEFINITIONS OF HYPOTHESES ALONE; no statement.

Not shown here. THAT ANY FIELD HOLDS ANYWHERE: no example is known. That these fields, with Opened
and OpenedBack (W/Ground.lean), are all that the proofs of the six own claims read: the list is
drawn from the statements in W/Gated.lean, W/Wo.lean, C/StackEnds.lean (h1_read, h2_read) and
from the library's in-claim of the second token sumcheck. THE SLOT o.sVE IS NAMED TWICE, IN TWO
TERMS: here as the embedding claim's value on the committed matrix, in Opened.emb as a sum over the
stream that comes in; that the two agree follows where the stream is the embedding of the tokens
(the library's identity j11), and from nothing else that is known. Nothing on soundness, on
completeness or on any other property. No property is claimed.

The equations "a slot holds this term" that no form of the two runs of the layers' own rounds
(sub-protocol K4) asks by itself, and that a proof of an own claim of a sumcheck (OwnFront, OwnBack:
W/Join.lean) reads: so that the list of such equations is seen whole.

  `OpenedOwn ρ W lay o D t M cl clE cr cm`   the slots of the never-sent vectors; of the weight
      claims' values; of the embedding claim's value; and the value that the merge shows.
  `OpenedFull X W Mm M`   the hidden sum of the second token sumcheck. Its term stands at the
      library's full-size structure alone (Rows.Pub34, Johnson/Road/Rows/LayerEnds34.lean).
-/
import Johnson.Road.Rows.LayerEnds34
import Johnson.Road.Rows.GatedEnds
import Johnson.Road.FormsKeysMerge

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.W
open Finset
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Own downFrom)
open Inst.Model.FFSeg (Dim Cell slV upV lF lFe)

variable {K : Type} [Field K]

/-- **The slots that only the proofs of the own claims read.** lay: the layout of the committed
matrix; M: that matrix; cl: the panels' weight claims, in their order; clE: the embedding's claim,
if there is one; cr: the merge's claims with their coefficients; cm: the entry of the index masks
that masks the value which the merge shows. This defines a hypothesis; the definition claims
nothing. -/
structure OpenedOwn (ρ : Reading K) (W : World K) (lay : WsLay) (o : Own) (D : Dim) (t : Cell → K)
    (M : Wm K) (cl : List WsClaim) (clE : Option WsClaim) (cr : List (WsClaim × E)) (cm : K) :
    Prop where
  /-- the first never-sent vector's value: the gated products of all layers, at the batched
  sumcheck's challenges and the lookup's token point -/
  h1 : W.slot o.K.sH1 = Blocks.ext (D.lL + lF D + D.lT) (fun X => slV D t X * upV D t X)
    (pt ρ (downFrom o.K.rs (D.lL + lF D) ++ o.H.ztF))
  /-- the others': the routed experts' gated products, at the second token sumcheck's end point -/
  h2 : ∀ tT, o.H.tT = some tT → ∀ lm, lm < o.v.y.LamM → W.slot (o.K.sH1 + 1 + lm) =
    ∑ yv ∈ range (2 ^ lFe D), eqR ρ o.K.rs 0 (lFe D) yv *
      Rows.hvOf D t (pt ρ o.H.ztF) (pt ρ tT.r) (1 + lm) yv
  /-- each weight claim's value on the committed matrix -/
  merged : ∀ a x, cl[a]? = some x → W.slot (o.K.sV + a) = claimVal ρ lay M x
  /-- in the first group: the embedding claim's value on the committed matrix -/
  embV : o.v.g = 0 → ∀ x, clE = some x → W.slot o.sVE = claimVal ρ lay M x
  /-- the value that the merge shows: the merged function at the merge's point, plus its mask. No
  slot of the world stands here: the mask is an entry of another message -/
  shown : ρ.val o.wo.toWsMerged.fvp =
    fmAt ρ lay M cr o.wo.toWsMerged.rm + cm * ρ.val o.wo.toWsMerged.beta

/-- **The hidden sum of the second token sumcheck**, at the library's full-size structure X: its
in-claim `Rows.Pub34.InL3`. This defines a hypothesis; the definition claims nothing. -/
structure OpenedFull (X : Rows.Pub34 K) (W : World K) (Mm : Mats K) (M : Wm K) : Prop where
  in3 : X.InL3 W Mm M

end OnBytes.Road.K4.W
