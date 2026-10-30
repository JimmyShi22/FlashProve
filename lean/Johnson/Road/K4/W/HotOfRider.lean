-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/W/HotOfRider.lean: CONDITIONAL.

Not shown here. THAT THE LOOKUP's ITEM worth "rider" HOLDS ANYWHERE: hO and hW are hypotheses. THAT
THERE IS A LIST OF ROUNDS WHOSE END VALUES ARE WHAT THE STATE HOLDS AS HEARD: hS (`K3Stands`,
Johnson/Top/H/K3RowOut.lean) is a hypothesis, AND WITHOUT IT THE ITEM SAYS NOTHING: it speaks at all
such lists. The numbers of the trees (`TreesFit`, Johnson/Road/FormsKeysLook.lean) and two sizes:
hypotheses on public numbers. hzt cuts at `DF.lT`, where the verifier cuts at the layout's number of
position bits: that the two are one number is a caller's to show. g IS WHAT THE STATE HOLDS AS HEARD
BY THE LOOKUP; what K4's own hearing is handed is another field of the state: that the two are one
is a caller's to show. Of the hypotheses together no example is known. `atCoords_of_out`,
`hotPoint_of_out`, `pt_heard` and `hotPoint_heard` are general in the sizes; `hotPoint_of_worth`
stands AT THE FULL SIZE ALONE: the lookup's caller reads its cells at the library's reference sizes
`DF`. Nothing on soundness, on completeness or on any other property.
No property is claimed.
WHAT THIS FILE's IMPORTS REACH, by a program's walk from import to import that stops, unopened, at
every module under Johnson/Goal/, Johnson/D/, Johnson/Bridge/ or ThirdParty/, at every module whose
name begins Cb.Bridge, and at the names RecCompile.Honest…, RecCompile.Both… and RecCompile.PassH…:
it stopped at 1 under Johnson/Bridge/; it saw 28 modules whose names hold RecCompile, none under
Johnson/Goal/, Johnson/D/ or ThirdParty/, none that begins Cb.Bridge and none of the three names.
What lies behind the 1 is not counted: all the numbers are floors. They come with the lookup's
files. It imports nothing of the honest side (Johnson/Desc/ProofFile/Honest/).

The hypothesis `HotPoint` (W/HotEmb.lean: the selector's identity at one point) at the token point
that the feed-forward layers' own rounds (sub-protocol K4) hold, from the item worth "rider" of the
lookup in front. That item is the same identity at the last places of the first part of the key
point that the lookup has heard; K4's token point is these places (`lastOf fo.zx lt`,
OnBytes/Desc/First/K4/Hear.lean). The library's `rider_of_point` (Johnson/Top/H/K3RowOutRider.lean)
goes the other way, and needs no rounds. Statements with their proofs: unfolding, and calls of the
library's `zpos_of_look` and `point_lay`.

  `atCoords_of_out`   the converse of `rider_of_point`, general in the caller.
  `hotPoint_of_out`   the item's sentence at a caller with that identity (`crHot`,
      Johnson/Top/H/LookupCRModel.lean), under hS: `HotPoint` at the last D.lT places of the first
      part of the heard key point.
  `pt_heard`   these places are the point of the array that `lastOf` cuts.
  `hotPoint_heard`   so `HotPoint` at that array's point.
  `hotPoint_of_worth`   **the same from the item as the table's meaning has it at a layers'
      segment** (`layWorthRider`, Johnson/Desc/First/Look/K3LayTies.lean), at the caller's own
      cells.
-/
import Johnson.Desc.First.Look.K3LayTies
import Johnson.Road.K4.K4PinsRider
import Johnson.Road.K4.W.HotEmb

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.W
open OnBytes OnBytes.Model OnBytes.Road
open Inst.Model (Scl)
open Inst.Model.All (DF)
open Inst.Model.FFSeg (Dim Cell Dk)
open OnBytes.Road.K4 (deep_ref)
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.First.Look (Sent sigListCalls LayPub layCells)
open VerifiableInference.OnPublicFiles (LookupCCaller LookupCRCaller crHot K3OutRider K3Stands keyPt
        layWorthRider layMs)
open Cb.Rider (AtCoords)

/-- **The converse of the library's `rider_of_point`**, where what was heard stands for some rounds:
each member's extension is 0 at its places of the heard key point. General in the caller.
CONDITIONAL: on hO and hS. -/
theorem atCoords_of_out (r : LookupCRCaller) (lm first : ℕ) (st : r.c.St₀) (m : r.c.Sg.Msg)
    (g : Forest.Heard) (F' : Fork) (hO : K3OutRider r lm first st m g F')
    (hS : K3Stands r.c.h lm first Reading.gl g F') :
    AtCoords r.g r.sel r.f st
      (fun t => (_root_.Fo.rdA Reading.gl g.zx ++ _root_.Fo.rdA Reading.gl g.zy).getD t 0) m := by
  obtain ⟨rs, hI⟩ := hS
  have q := hO rs hI
  unfold keyPt at q
  rw [← hI.zx, ← hI.zy] at q
  exact q

/-- **The item's sentence gives the selector's identity at the heard point**, where what was heard
stands for some rounds. CONDITIONAL: on hO and hS. -/
theorem hotPoint_of_out [scl : Scl] (c : LookupCCaller) (D : Dim)
    (cells : c.St₀ → c.Sg.Msg → Cell → Cb.Gl.E) (lm first : ℕ) (st : c.St₀) (m : c.Sg.Msg)
    (g : Forest.Heard) (F' : Fork) (hO : K3OutRider (crHot c D cells) lm first st m g F')
    (hS : K3Stands c.h lm first Reading.gl g F') :
    HotPoint D (cells st m) fun t =>
      (_root_.Fo.rdA Reading.gl g.zx ++ _root_.Fo.rdA Reading.gl g.zy).getD
        (c.h.dT - D.lT + t) 0 :=
  fun l hl => atCoords_of_out (crHot c D cells) lm first st m g F' hO hS (⟨l, hl⟩ : Fin D.ne)

/-- The last D.lT places of the first part of the heard key point are the point of the array that
`lastOf` cuts. CONDITIONAL: on four hypotheses on public numbers and sizes. -/
theorem pt_heard {fo : Forest.Shape} {D : Dim} (T : TreesFit fo D) (g : Forest.Heard)
    (hsx : g.zx.size = fo.dT) {zt : Array E} (hzt : lastOf g.zx D.lT = .ok zt)
    (hl : D.lT ≤ Dk D) (t : ℕ) (ht : t < D.lT) :
    pt Reading.gl zt t =
      (_root_.Fo.rdA Reading.gl g.zx ++ _root_.Fo.rdA Reading.gl g.zy).getD
        (Dk D - D.lT + t) 0 :=
  (zpos_of_look (ρ := Reading.gl) (zy := g.zy) T hsx hzt t ht).symm.trans
    (point_lay D g (hsx.trans T.dT) hl t ht)

/-- **`HotPoint` at the point of the array that `lastOf` cuts.** CONDITIONAL: on hO, hS and the
hypotheses of `pt_heard`; the caller's shape of the trees is fo. -/
theorem hotPoint_heard [scl : Scl] (c : LookupCCaller) (D : Dim)
    (cells : c.St₀ → c.Sg.Msg → Cell → Cb.Gl.E) (lm first : ℕ) (st : c.St₀) (m : c.Sg.Msg)
    (g : Forest.Heard) (F' : Fork) (hO : K3OutRider (crHot c D cells) lm first st m g F')
    (hS : K3Stands c.h lm first Reading.gl g F') (T : TreesFit c.h D) (hsx : g.zx.size = c.h.dT)
    {zt : Array E} (hzt : lastOf g.zx D.lT = .ok zt) (hl : D.lT ≤ Dk D) :
    HotPoint D (cells st m) (pt Reading.gl zt) := by
  intro l hl'
  have q := hotPoint_of_out c D cells lm first st m g F' hO hS l hl'
  rw [T.dT] at q
  rw [ext_congr_pt D.lT _ (fun t ht => pt_heard T g hsx hzt hl t ht)]
  exact q

section
variable {S Cells Tok : Type} (x : VerifiableInference.Desc.First.Look.Place) (q : LayPub)
  (tl : HTailF2) (Ds : Sent) (rad : OracleShape → ℕ) (oW : Cb.OMsg Cb.Gl.E)
  (wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E) (nr nc : ℕ)
  (seatT : Fin (sigListCalls Ds rad x.link).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
  (msgW : Wit Cells Tok MsgT → oW.Msg) (fork : S → Option Fork)
  (heard : S → Option Forest.Heard)

/-- **From the item as the table's meaning has it at a layers' segment.** s: a state that holds the
ledger F' and the heard structure g. w: a witness. CONDITIONAL: on hW, hf, hh, hS, T, hsx and hzt.
-/
theorem hotPoint_of_worth {s : S} {w : Wit Cells Tok MsgT}
    (hW : layWorthRider x q tl Ds rad oW wOf nr nc seatT arr msgW fork heard s w) {F' : Fork}
    {g : Forest.Heard} (hf : fork s = some F') (hh : heard s = some g)
    (hS : K3Stands x.fs x.lm x.F.next Reading.gl g F') (T : TreesFit x.fs DF)
    (hsx : g.zx.size = x.fs.dT) {zt : Array E} (hzt : lastOf g.zx DF.lT = .ok zt) :
    HotPoint DF (layCells x q tl Ds rad oW wOf nr nc (layMs x Ds rad oW seatT arr msgW w))
      (pt Reading.gl zt) :=
  hotPoint_heard (scl := sclOf q.h q.sc q.g 4) _ DF _ x.lm x.F.next () _ g F' (hW g F' hf hh) hS T
    hsx hzt deep_ref

end

end OnBytes.Road.K4.W

#print axioms OnBytes.Road.K4.W.atCoords_of_out
#print axioms OnBytes.Road.K4.W.hotPoint_of_out
#print axioms OnBytes.Road.K4.W.pt_heard
#print axioms OnBytes.Road.K4.W.hotPoint_heard
#print axioms OnBytes.Road.K4.W.hotPoint_of_worth
