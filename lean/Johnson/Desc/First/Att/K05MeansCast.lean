-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05MeansCast.lean: K05_means AT THE CAST OF THE INTEGERS BEHIND THE COMMITTED
SYMBOLS, WITH NO PREMISE ON THE PACKING; and three small things.

The trace cellsBy (Att/K05MeansOrd.lean) reads cellValS y at a map of places. By the library's own
make cellValS y j is the cast of cellsOf y (Cb/Pv/Tail/CellMap.lean: cellVal; Unique.lean: cellsOf:
the small integers of which a column's symbols are the packing; 0 WHERE THERE ARE NONE), and mzAt y
(Johnson/Road/Rows/HeadBase.lean) is cellsOf y. So cellsBy is castT (cellsA S (zsOf pl (mzAt y))) by
definition: the identities at cellsBy are the identities "in the field, at the integers' cast".

Main names:
  `cellsBy_cast`: cellsBy x S tl D rad pl m = castT (cellsA S (zsOf pl (mzAt (symsA x tl D rad
    m)))).
  `K05_means_cast`: **Todo gives own1 and own2 at that cast**; `K05_rider_means_cast`: the lookup's
    base joint in front gives ridden there. Premises: those of K05_means_at | K05_rider_means_at
    (PlaceOK, InsideA): NOT "the committed symbols are the packing of small integers".
  `nameJ_inhabited`: the type NameJ D ls lmS of the late entries' names has a member at every ls and
    lmS, wherever there is a pair.
  `K05_yes_fails_seats`: the check against the text that says yes to all (Att/K05SeamSilly.lean), AT
    THE LATER LAW's FORM: at seatSO, at the closed caller's letters and the law's own errors, the
    yes-text is NOT good (Piece.GoodIn) from Todo at the world's part to the relation behind.

Limits. The cast is into the challenge field Cb.Gl.E. The integer model's clauses on an attention
segment's own identities stand at the cast into the base field: the step down, and "by the make" in
that model's files' letters, are those files' lemmas, whose premise is this file's conclusion: not
typed twice. What lacks between the two is the tie of K5's and those files' readings of the symbols.
WHAT THE CAST SPEAKS OF: at a column whose symbols are no packing of small integers mzAt reads 0 in
silence: the identities then speak of zeros, not of what is committed: that the cells are the
committed ones wants the packing (the smallness test's law) and the guards of the caller's reading.
K05_yes_fails_seats stands under a pair (a, w) that is a premise (on a; Todo fails at (x0 a, part
w); the relation behind holds at the record as it came), a yes of k5Held kc, which is evaluated in
no file of this tree, and p.work < kc. No (x0, m) with Todo is shown.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05MeansOrd
import Johnson.Desc.First.Att.K05SeamParts
import Johnson.Road.Rows.HeadBase

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb IOR TWhole Cb.Fo Cb.LdLkp Cb.Pv.Att Cb.Pv.Att.End Inst.Model Inst.Model.AttSeg
open OnBytes OnBytes.Model OnBytes.Model.Road
open OnBytes.Tie.Pv.Att (recOf)
open OnBytes.Road.L5 (callsOf dimOf cellsA)
open OnBytes.Road.Rows (PlaceOK zsOf mzAt)
open OnBytes.Maker Run
open Cb.Pv.Tail (JCell)
open VerifiableInference.OnPublicFiles (kLookupCR)
open VerifiableInference.Desc.First.Look (Sent attSg JAtt AttOK attRider szOf)
open VerifiableInference.Desc.Sound (Frame Piece)

/-- **By the make**: the cells by a map of places are the casts of the integers behind the symbols.
-/
theorem cellsBy_cast (x : VerifiableInference.Desc.First.Look.Place) (S : Attention.Shape)
    (tl : HTailF2) (D : Sent) (rad : OracleShape → Nat) (pl : ℕ → ℕ → ℕ → JCell (szOf tl))
    (m : (attSg x D rad).Msg) :
    cellsBy x S tl D rad pl m =
      (castT (cellsA S (zsOf pl (mzAt (symsA x tl D rad m)))) : Raw → Cb.Gl.E) := rfl

/-- The late entries' names have a member wherever there is a pair. -/
theorem nameJ_inhabited (D : Dim) (ls lmS : ℕ) (hb : D.nb ≠ 0) : Nonempty (NameJ D ls lmS) :=
  ⟨⟨(.tMm, .mx 0 0 0 0), in_row D ls lmS (fun k b g => .mx k b g 0) rfl (by norm_num)
    (Nat.pos_of_ne_zero hb) (Nat.two_pow_pos _)⟩⟩

section
variable (x : VerifiableInference.Desc.First.Look.Place) (tl : HTailF2) (D : Sent)
  (rad : OracleShape → Nat) (Ex : Iop.ExtSpec) (Wp : Type)
  (α : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl)) → Cb.Gl.E)

/-- **own1 and own2 in the field, at the cast of the integers behind the symbols.** -/
theorem K05_means_cast {settings : Model.Settings} {i : Attention.In} {cf : Attention.Cfg}
    {A : Attention.Plan} (hA : Attention.plan settings i cf = Except.ok A) (ns : ℕ) (N : Nums)
    (x0 : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl))) (m : (attSg x D rad).Msg)
    (h : ((closedOf (attBase x A.S tl D rad) (attLin x A.S tl D rad Ex Wp α ns N) ns N).own (theMeans Cb.Gl.E _ _ _)).ch.Todo x0 m)
    (pl : ℕ → ℕ → ℕ → JCell (szOf tl)) (hp : PlaceOK pl) (hin : InsideA tl A.S) :
    (∀ j b g i, (Idn.at1 j b g i).Valid (dimOf A.S) →
        idnVal (dimOf A.S)
          (castT (cellsA A.S (zsOf pl (mzAt (symsA x tl D rad m)))) : Raw → Cb.Gl.E)
          (.at1 j b g i) = 0) ∧
      ∀ b g i, (Idn.at2 b g i).Valid (dimOf A.S) →
        idnVal (dimOf A.S)
          (castT (cellsA A.S (zsOf pl (mzAt (symsA x tl D rad m)))) : Raw → Cb.Gl.E)
          (.at2 b g i) = 0 :=
  K05_means_at x tl D rad Ex Wp α hA ns N x0 m h pl hp hin

/-- **ridden there.** -/
theorem K05_rider_means_cast {set : Params.Setting} {S : Attention.Shape}
    (H : AttOK set x S tl D rad) (a : Unit × Ex.Str) (w : (attSg x D rad).Msg × Wp)
    (h : ((kLookupCR [attRider x S tl D rad Ex Wp]).A (attRider x S tl D rad Ex Wp)).relR a w)
    (pl : ℕ → ℕ → ℕ → JCell (szOf tl)) (hp : PlaceOK pl) (hin : InsideA tl S) :
    ∀ b g i, (Idn.at3 b g i).Valid (dimOf S) →
      idnVal (dimOf S) (castT (cellsA S (zsOf pl (mzAt (symsA x tl D rad w.1)))) : Raw → Cb.Gl.E)
        (.at3 b g i) = 0 :=
  K05_rider_means_at x tl D rad Ex Wp H a w h pl hp hin

open Classical in
/-- **The yes-text has not the later law's form**, at the law's own errors. -/
theorem K05_yes_fails_seats {W Ck : Type} {Fr : Frame} {settings : Model.Settings}
    {i : Attention.In} {cf : Attention.Cfg} {A : Attention.Plan}
    (hA : Attention.plan settings i cf = Except.ok A) (hok : planOkAll cf A.S A.fs = true)
    (claims : List (String × (Nat → First.S → Except String (List Ck × First.S)))) (p : Par)
    (hp : p.own = A.own) (ns : ℕ) (N : Nums) (base kc : ℕ)
    (hc : k5Held kc (zOf p.own) ((rounds p).map fun r => (r.entry, kindFmt r.entry)) = true)
    (hw : p.work < kc)
    (x0 : First.S × Fr.E.Str → TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl)))
    (part : W → (attSg x D rad).Msg) (on on' : First.S × Fr.E.Str → Prop)
    (R' : First.S × Fr.E.Str → W → Prop) (a : First.S × Fr.E.Str) (w : W) (ha : on a)
    (hR : ¬ ((closedOf (attBase x A.S tl D rad) (attLin x A.S tl D rad Ex Wp α ns N) ns N).own (theMeans Cb.Gl.E _ _ _)).ch.Todo (x0 a) (part w))
    (hR' : ∀ y', R' (a.1, y') w) :
    ¬ (pieceAt (W := W) (F := Fr) (k5Yes seatSO claims p) p base
        (bearErr (written p) _ (((closedOf (attBase x A.S tl D rad) (attLin x A.S tl D rad Ex Wp α ns N) ns N).own (theMeans Cb.Gl.E _ _ _)).ch.eps Ex))).GoodIn on on'
      (fun a w => ((closedOf (attBase x A.S tl D rad) (attLin x A.S tl D rad Ex Wp α ns N) ns N).own (theMeans Cb.Gl.E _ _ _)).ch.Todo (x0 a) (part w)) R' := by
  have hid := (OnBytes.Road.L5.plan_shape hA).1
  have PA := plan_all hid hok
  obtain ⟨_, _, _, _, _, _, _, U⟩ := PA.units
  have hrec : p.own = recOf (closedOf (attBase x A.S tl D rad)
      (attLin x A.S tl D rad Ex Wp α ns N) ns N) A.own.rows :=
    hp.trans (rec_of_plan hA PA.law.place (OnBytes.Road.Rows.norm_of_hid hid)
      (Nat.le_of_succ_le (OnBytes.Road.Rows.sizes_of_hid hid).lnT) U _ rfl rfl rfl)
  exact K05_yes_fails _ rfl A.own.rows p hrec Ex kc hc hw seatSO claims base on on'
    (fun a w => ((closedOf (attBase x A.S tl D rad) (attLin x A.S tl D rad Ex Wp α ns N) ns N).own (theMeans Cb.Gl.E _ _ _)).ch.Todo (x0 a) (part w)) R' a w ha hR hR'

end

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.cellsBy_cast
#print axioms VerifiableInference.Desc.First.Att.P.nameJ_inhabited
#print axioms VerifiableInference.Desc.First.Att.P.K05_means_cast
#print axioms VerifiableInference.Desc.First.Att.P.K05_rider_means_cast
#print axioms VerifiableInference.Desc.First.Att.P.K05_yes_fails_seats
