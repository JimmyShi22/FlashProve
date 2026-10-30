-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/RightStack.lean: CONDITIONAL.

Not shown here. THAT THE FUNCTION WHICH MAKES THE BATCHED SUMCHECK's DATA RETURNS, THAT ITS END
VALUES ARE THERE, AND THAT THE CHALLENGES AND POINTS WHICH THE HONEST SIDE HAS HEARD ARE THOSE THAT
THE VERIFIER HOLDS: StackAt is a hypothesis. What that function reads of the rounds shown in front
(seen) is a free letter here: own_h1 and own_h2 hold whatever it reads. TensorIs and three sizes:
hypotheses. That they can hold together: no example is known. THE FIELDS merged, embV AND shown OF
OpenedOwn ARE NOT REACHED HERE. By a walk of import lines the closure holds seven modules under
Johnson/RecCompile/ (Join, Wire, Pass, CmsGlue, CmsBcs, Cms, Bcs), through Law/SlotsTrue.lean's
imports; none under Johnson/Goal/ or Johnson/D/; under Johnson/RecCompile/ none of the names
Honest…, Both…, PassH…. Nothing on soundness, on completeness or on any other property.
No property is claimed.

Two fields of `OpenedOwn` (Johnson/Road/K4/W/OpenedOwn.lean), h1 and h2, each as a copy of that
field's text, at the reading Reading.gl: from the left half (`OpenedLeft`, Law/SlotsTrue.lean: slot
sA0 + e is worth the reading of end value e) and the right half (`h1_read`, `h2_read`,
Johnson/Road/K4/C/StackEnds.lean). No term of the structure is built here: that the copies are the
fields is held in Law/W/OwnOf.lean, which builds one.

  `pts4 Q w h ds`   the sampled values as the batched sumcheck's job finds them.
  `StackAt Q w h ds seen o SD e`   the maker's data SD and its end values e are there; the
      challenges by bit are o.K.rs; the lookup's token point is o.H.ztF; the second token sumcheck's
      end point is tT.r; the layouts agree.
  `stack_word`   end value number i, as OpenedLeft names it, is member i of e.
  `own_h1`, `own_h2`   the two fields.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.Halves
import Johnson.Road.K4.W.OpenedOwn
import Johnson.Road.K4.C.DownPanel

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open Finset
open OnBytes (E zeroE)
open OnBytes.Model (Reading World)
open OnBytes.Model.Layer (Own Ten SBlk downFrom)
open OnBytes.Road (pt eqR)
open OnBytes.Road.K4.C (TensorIs GatedNums StackIs stackIs_of down_nums h1_read h2_read)
open OnBytes.Desc.First.K4.Honest
open Inst.Model.FFSeg (Dim Cell lF lFe slV upV)
open Blocks (ext)

/-- The sampled values as the batched sumcheck's job finds them. -/
def pts4 (Q : K4Pub) (w : K4In) (h ds : List Fmt.Drawn) : Pts :=
  ptsOf Q w (h ++ ds.take (rJ4 Q.P Q.g))

/-- **The batched sumcheck's job against what the verifier holds.** This defines a hypothesis; the
definition claims nothing. -/
structure StackAt (Q : K4Pub) (w : K4In) (h ds : List Fmt.Drawn) (seen : Seen) (o : Own)
    (SD : StackData) (e : List E) : Prop where
  data : stackData Q w (pts4 Q w h ds) (k4SentAt seen.rounds (k4TermsEnds Q)) = some SD
  ends : SD.endsAt (ownE ds (rJ4 Q.P Q.g + 1) Q.hp.lamS).toArray.reverse = some e
  rs : (ownE ds (rJ4 Q.P Q.g + 1) Q.hp.lamS).toArray.reverse = o.K.rs
  zt : ztOf Q (pts4 Q w h ds) = o.H.ztF
  rt : ∀ tT, o.H.tT = some tT → (pts4 Q w h ds).rt = tT.r
  y : o.v.y = Q.P.y

variable {Q : K4Pub} {w : K4In} {h ds : List Fmt.Drawn} {seen : Seen} {o : Own}
  {SD : StackData} {e : List E} {D : Dim} {t : Cell → Cb.Gl.E} {Wd : World Cb.Gl.E}

/-- End value number i, as the left half names it, is member i of the maker's list. -/
theorem stack_word (A : StackAt Q w h ds seen o SD e) (i : Nat) :
    wStack Q w h ds seen i = e.getD i zeroE := by
  show ((((jobStack Q w (pts4 Q w h ds) (k4SentAt seen.rounds (k4TermsEnds Q))).map
    (·.ends (ownE ds (rJ4 Q.P Q.g + 1) Q.hp.lamS))).getD []).getD i zeroE) = _
  unfold jobStack
  rw [A.data]
  show ((SD.endsAt (ownE ds (rJ4 Q.P Q.g + 1) Q.hp.lamS).toArray.reverse).getD []).getD i zeroE = _
  rw [A.ends]
  rfl

/-- **THE FIELD h1 OF OpenedOwn.** CONDITIONAL: on every hypothesis named. -/
theorem own_h1 (L : OpenedLeft Wd Q o w h ds seen) (A : StackAt Q w h ds seen o SD e)
    {ts tu : Ten} (hts : Q.P.y.T_ "s" = some ts) (htu : Q.P.y.T_ "u" = some tu)
    (Ss : TensorIs Q w t .sl ts) (Su : TensorIs Q w t .up tu) (N : GatedNums Q D)
    (hzt : o.H.ztF.size = D.lT) (hrs : D.lL + lF D ≤ o.K.rs.size) :
    Wd.slot o.K.sH1 = ext (D.lL + lF D + D.lT) (fun X => slV D t X * upV D t X)
      (pt Reading.gl (downFrom o.K.rs (D.lL + lF D) ++ o.H.ztF)) := by
  obtain ⟨ez, tb, I⟩ := stackIs_of A.data
  have ez' : SD.S.zt = o.H.ztF := ez.trans A.zt
  have hn : 1 < nStack Q.P Q.hp Q.g := by
    unfold nStack
    omega
  have hE := A.ends
  rw [A.rs] at hE
  have r := h1_read hts htu Ss Su N I (by rw [ez']; exact hzt) hrs hE (down_nums A.data N)
  rw [ez'] at r
  rw [L.sH1, L.stack 1 hn, ← r]
  exact congrArg Reading.gl.val (stack_word A 1)

/-- **THE FIELD h2 OF OpenedOwn.** CONDITIONAL: on every hypothesis named. -/
theorem own_h2 (L : OpenedLeft Wd Q o w h ds seen) (A : StackAt Q w h ds seen o SD e)
    {ts tu : Ten} (hts : Q.P.y.T_ "s" = some ts) (htu : Q.P.y.T_ "u" = some tu)
    (Ss : TensorIs Q w t .sl ts) (Su : TensorIs Q w t .up tu) (N : GatedNums Q D)
    (hrs : lFe D ≤ o.K.rs.size) (hsz : ∀ tT, o.H.tT = some tT → tT.r.size = D.lT) :
    ∀ tT, o.H.tT = some tT → ∀ lm, lm < o.v.y.LamM →
      Wd.slot (o.K.sH1 + 1 + lm) =
        ∑ yv ∈ range (2 ^ lFe D), eqR Reading.gl o.K.rs 0 (lFe D) yv *
          OnBytes.Road.Rows.hvOf D t (pt Reading.gl o.H.ztF) (pt Reading.gl tT.r) (1 + lm) yv := by
  intro tT hT lm hlm
  obtain ⟨_, tb, I⟩ := stackIs_of A.data
  rw [A.rt tT hT] at I
  rw [A.y] at hlm
  have hn : 2 + lm < nStack Q.P Q.hp Q.g := by
    unfold nStack
    omega
  have hE := A.ends
  rw [A.rs] at hE
  have r := h2_read hts htu Ss Su N I (hsz tT hT) hrs hE (pt Reading.gl o.H.ztF) lm hlm
  rw [← r, L.sH1, show o.K.sA0 + 1 + 1 + lm = o.K.sA0 + (2 + lm) by omega, L.stack (2 + lm) hn]
  exact congrArg Reading.gl.val (stack_word A (2 + lm))

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.stack_word
#print axioms ProofFile.Honest.K4.W.own_h1
#print axioms ProofFile.Honest.K4.W.own_h2
