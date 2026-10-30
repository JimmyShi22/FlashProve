-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/TokAtY.lean: CONDITIONAL.

What is here. TokAtX.lean's `tokAll_x` (what is left at one token, from one of the library's public
structures `Pub34` at the token's corner) WITH ITS WORLD MADE AND ITS TWO HYPOTHESES ON THAT WORLD
PAID. The world has the true entries at X's tables and the matrices Mm, and holds under the slots of
X's second token sumcheck the values that the honest side computes for the end values at the token.
That the verifier's claims on these values are worth 0 there is EndsAtTok.lean's `claims_zero`. So
no hypothesis on a world is left at a token.

  `tokWorld`   the world
  `tokAll_y`   **what is left at a token, from a structure at its corner**

Limits. At the reading `Reading.gl`. THE FULL SIZE ALONE (X). Such a structure holds a hearing that
no run has, whose end point is the corner: Pub34At.lean's `pub34At` makes one from a structure at
the end point, and TokOfPub.lean's `tokAll_pub` calls this law there. HYPOTHESES: those of
`tokAll_x` but hW, hsl, hlE and hE; in their place three returns: the honest reads at the corner,
the honest end values there, the verifier's list of claims on the end values at X's hearing. SOME OF
THE HYPOTHESES FOLLOW FROM THE OTHERS and are asked all the same: Xv from Xp; the list of claims'
return from the honest side's; hlt, hf, hB and hpp from X's own fields. `tokAll_pub` with
TokRetOf.lean's `tokRet_of` draws all of these but hB, which JoinHeard.lean's `joinWorth_tied`
draws. No example is known.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.TokAtX
import Johnson.Desc.ProofFile.Honest.K4.Law.EndsAtTok
import Johnson.Road.K4.ListsTie2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes (E zeroE)
open OnBytes.Model (Reading Aff World)
open OnBytes.Model.Layer (ClaimEnv Ten layTables tableAsks funsOf)
open OnBytes.Road (pt sclOf cellsAt cellsOf zOf Mats sentAt admitted_of_layout)
open OnBytes.Road.K4 (entryOf termsForms_termsL)
open OnBytes.Road.K4.C (sidesEnv stack_open CellsAre PtsPart TensorIs GatedNums tokPts)
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim Cell)
open OnBytes.Desc.First.K4.Honest

/-- **The world at a token**: the true entries at X's tables and the matrices Mm; under slot number
e of X's second token sumcheck's end values, value number e of sh; under each slot in front of
these, value number 0. -/
noncomputable def tokWorld (X : OnBytes.Road.Rows.Pub34 Cb.Gl.E) (Mm : Mats Cb.Gl.E)
    (sh : Array E) : World Cb.Gl.E where
  slot := fun j => sentAt Reading.gl sh (j - X.tT.sEnd)
  entry := entryOf X.ρ X.tl X.funs X.p.v.iU3 X.p.v.K3 Mm

/-- **WHAT IS LEFT AT TOKEN NUMBER i, FROM A PUBLIC STRUCTURE AT THE TOKEN's CORNER; NO HYPOTHESIS
ON A WORLD.** CONDITIONAL: on every hypothesis named. THE FULL SIZE ALONE (X). -/
theorem tokAll_y [scl : Scl] {Q : K4Pub} {w : K4In} {p : Pts} {shownT : Array E}
    {SD : StackData} (h : stackData Q w p shownT = some SD) {i : ℕ} {rs : Array E}
    (X : OnBytes.Road.Rows.Pub34 Cb.Gl.E) (Xρ : X.ρ = Reading.gl)
    (hscl : scl = sclOf X.h X.p.v.sc X.p.v.g X.p.v.y.Lam)
    (Xp : ∀ R sh, SD.S.readsTok (OnBytes.Desc.First.K4.Honest.bitsOf SD.S.v.y.h.lt i) = some R →
      endsOn SD.S R = some sh → X.p = sidesEnv SD.S sh)
    (Xv : X.p.v = SD.S.v)
    (Xc : X.c =
      { SD.S.ce with rs := rs, rt := OnBytes.Desc.First.K4.Honest.bitsOf SD.S.v.y.h.lt i })
    (hTS : SD.S.TS = [0, 1, 2, 5]) (Mm : Mats Cb.Gl.E) {R0 : Reads} {sh0 : Array E}
    (hR0 : SD.S.readsTok (OnBytes.Desc.First.K4.Honest.bitsOf SD.S.v.y.h.lt i) = some R0)
    (hsh0 : endsOn SD.S R0 = some sh0) {lE : List Aff}
    (hlF : OnBytes.Desc.First.K4.termsForms SD.S.v X.H = some lE)
    (hl : layTables (matsOf Q) (tableAsks Q.P.y Q.P.rd Q.g) 0 = some X.r)
    (hf : funsOf Q.P.y X.H.fo X.pts X.r.2.1 = some X.funs)
    (hpp : PtsPart (tokPts SD.S.zlow (OnBytes.Desc.First.K4.Honest.bitsOf SD.S.v.y.h.lt i)) X.pts)
    (hm : (X.tl.mats.map fun M => (M.m, M.k)) = matsOf Q) (hC : CellsAre Q w Mm) {tB0 : ℕ}
    (hB : SD.S.v.tabAt "b-bits-0" = some tB0)
    {D : Dim} (hD : D = X.D) {lk : ℕ} (hlk : lk = X.lk) {L0 : ℕ}
    (hL0 : L0 = SD.S.ce.v.g * SD.S.ce.v.y.Lam) {t : Cell → Cb.Gl.E}
    (ht : t = cellsOf X.D (cellsAt SD.S.v.y Mm)) {z : ℕ → Cb.Gl.E}
    (hz : z = zOf Reading.gl X.H.fo.zx X.H.fo.zy) {tb : Tables} (htb : tb = X.tb)
    {ts tu : Ten} (hts : Q.P.y.T_ "s" = some ts) (htu : Q.P.y.T_ "u" = some tu)
    (Ss : TensorIs Q w t .sl ts) (Su : TensorIs Q w t .up tu) (N : GatedNums Q D)
    (hlt : D.lT = SD.S.v.y.h.lt) (hne : 2 * D.ne ≤ 2 ^ D.lL) (hi : i < 2 ^ D.lT) :
    TokAll SD.S D t tb L0 lk z i := by
  have hS := (stack_open h).1
  have hv : SD.S.v.tab = X.r.1 := by
    rw [← Xv]
    exact X.ht
  have hp3 : X.p.v.y.h.p3 = true := by
    rw [(admitted_of_layout X.hy X.S.p3).shape]
    exact X.S.p3
  have hsl0 : ∀ e, (tokWorld X Mm sh0).slot (X.tT.sEnd + e) = sentAt Reading.gl sh0 e := fun e => by
    show sentAt Reading.gl sh0 (X.tT.sEnd + e - X.tT.sEnd) = _
    rw [Nat.add_sub_cancel_left]
  have hW' : (tokWorld X Mm sh0).entry =
      entryOf Reading.gl X.tl X.funs SD.S.v.iU3 SD.S.v.K3 Mm := by
    show entryOf X.ρ X.tl X.funs X.p.v.iU3 X.p.v.K3 Mm = _
    rw [Xρ, Xv]
  have hE := claims_zero hS hR0 hsh0 hl hf hpp hm X.hNM hC hv hB X.hT hlF hW' hsl0
  refine tokAll_x h X Xρ hscl Xp Xv Xc hTS (tokWorld X Mm sh0) Mm rfl (fun R sh hR hsh e => ?_)
    (termsForms_termsL X.hT hp3 (by rw [Xv]; exact hlF)) (by rw [Xρ]; exact hE) hl hf hpp hm hC hB
    hD hlk hL0 ht hz htb hts htu Ss Su N hlt hne hi
  obtain rfl : R0 = R := Option.some.inj (hR0.symm.trans hR)
  obtain rfl : sh0 = sh := Option.some.inj (hsh0.symm.trans hsh)
  exact hsl0 e

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.tokAll_y
