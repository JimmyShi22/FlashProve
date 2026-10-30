-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/TokAtX.lean: CONDITIONAL.

What is here. The hypothesis `TokAll` of JoinPub.lean, JoinOne.lean and JoinAtX.lean (what is left
at one token) FROM ONE OF THE LIBRARY's PUBLIC STRUCTURES `Pub34` AT THE TOKEN's CORNER: one whose
environment of the claims has the corner for the second token sumcheck's end point, and whose
environment of the panels has the true end values at that token for the shown ones. All of
`TokAll`'s clauses become calls. `SigFits`: SigOfPub.lean's `sig_of_pub`. The honest values of the
panels' forms: HvalOf.lean's `hval_true`. The honest table of the gated products: GatedOf.lean's
`hhAt_gated`. That the true end values are the library's contractions: the library's `l3EndShown`
(Johnson/Road/Rows/LayerEnds3S.lean): where the verifier's claims on the end values are worth 0 on
true reads, the values under their slots are the contractions.

  `tokAll_x`   **what is left at a token, from a structure at its corner**

Limits. At the reading `Reading.gl`. THE FULL SIZE ALONE (X). Such a structure holds a hearing that
no run has, whose end point is the corner: Pub34At.lean's `pub34At` makes one from a structure at
the end point. HYPOTHESES: X is given, at this reading, with its two environments as said (Xp, Xc)
and its sizes, tables, weights' bits and lookup's points those of the letters D, tb, lk, z
(equations); the table of scales is X's; the world Wo has the true entries at X's tables and the
matrices Mm (hW), holds the true end values under the slots of X's second token sumcheck (hsl), and
in it the verifier's claims on the end values are worth 0 (hE): these two are paid two files on: hE
by EndsAtTok.lean's `claims_zero`, hsl by the make of TokAtY.lean's `tokWorld`; X's laying, list of
tables and matrices written in the plan's letters (hl, hf, hm), the token's two points a part of its
points (hpp); `CellsAre`; `TensorIs` twice; `GatedNums`; the family "b-bits-0" is found; the routed
layers lie in the library's range. No example is known.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.JoinOne
import Johnson.Road.Rows.LayerEnds3S
import Johnson.Road.K4.C.TermsAtOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes (E zeroE)
open OnBytes.Model (Reading Aff World)
open OnBytes.Model.Layer (ClaimEnv Ten layTables tableAsks funsOf)
open OnBytes.Road (pt sclOf cellsAt cellsOf zOf Mats sentAt ts_eq)
open OnBytes.Road.Rows (l3EndShown termsL)
open OnBytes.Road.K4 (entryOf reads_true_pub)
open OnBytes.Road.K4.C (sidesEnv stack_open sides_fields CellsAre PtsPart TensorIs GatedNums tokPts)
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim Cell)
open OnBytes.Desc.First.K4.Honest

/-- **WHAT IS LEFT AT TOKEN NUMBER i, FROM A PUBLIC STRUCTURE AT THE TOKEN's CORNER.** CONDITIONAL:
on every hypothesis named. THE FULL SIZE ALONE (X). -/
theorem tokAll_x [scl : Scl] {Q : K4Pub} {w : K4In} {p : Pts} {shownT : Array E}
    {SD : StackData} (h : stackData Q w p shownT = some SD) {i : ℕ} {rs : Array E}
    (X : OnBytes.Road.Rows.Pub34 Cb.Gl.E) (Xρ : X.ρ = Reading.gl)
    (hscl : scl = sclOf X.h X.p.v.sc X.p.v.g X.p.v.y.Lam)
    (Xp : ∀ R sh, SD.S.readsTok (OnBytes.Desc.First.K4.Honest.bitsOf SD.S.v.y.h.lt i) = some R →
      endsOn SD.S R = some sh → X.p = sidesEnv SD.S sh)
    (Xv : X.p.v = SD.S.v)
    (Xc : X.c =
      { SD.S.ce with rs := rs, rt := OnBytes.Desc.First.K4.Honest.bitsOf SD.S.v.y.h.lt i })
    (hTS : SD.S.TS = [0, 1, 2, 5]) (Wo : World Cb.Gl.E) (Mm : Mats Cb.Gl.E)
    (hW : Wo.entry = entryOf X.ρ X.tl X.funs X.p.v.iU3 X.p.v.K3 Mm)
    (hsl : ∀ R sh, SD.S.readsTok (OnBytes.Desc.First.K4.Honest.bitsOf SD.S.v.y.h.lt i) = some R →
      endsOn SD.S R = some sh → ∀ e, Wo.slot (X.tT.sEnd + e) = sentAt Reading.gl sh e)
    {lE : List Aff} (hlE : termsL X.p.v X.tT.sEnd = some lE)
    (hE : ∀ f ∈ lE, f.value X.ρ Wo = 0)
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
  subst hD hlk hL0 ht hz htb
  have hS := (stack_open h).1
  obtain ⟨eQ, ew, _, _, _, _, _⟩ := sides_fields hS
  have eTS : X.TS = SD.S.TS := by
    rw [hTS]
    exact ts_eq X.hy X.S.p3 X.hN X.hrd X.hTS
  have hcl := X.hcl
  rw [Xc, eTS] at hcl
  have hv : SD.S.v.tab = X.r.1 := by
    rw [← Xv]
    exact X.ht
  have hW' : Wo.entry = entryOf Reading.gl X.tl X.funs SD.S.v.iU3 SD.S.v.K3 Mm := by
    rw [hW, Xρ, Xv]
  refine ⟨rs, X.cl, Wo, hcl, fun R sh bl places hR hp b hb _ => ?_, fun R sh hR hsh => ?_⟩
  · obtain ⟨pans, hpan, rfl⟩ := panels_open hp
    have hR' : readsAt Q w SD.S.fo
        (tokPts SD.S.zlow (OnBytes.Desc.First.K4.Honest.bitsOf SD.S.v.y.h.lt i)) = some R := by
      have q := hR
      unfold OnBytes.Desc.First.K4.Honest.Sides.readsTok at q
      rw [eQ, ew] at q
      exact q
    exact hval_true hR' hl hf hpp hm X.hNM hC (pe := sidesEnv SD.S sh) hv hB hpan hW' b hb
  · have Xp' := Xp R sh hR hsh
    have ey : X.p.v.y = SD.S.v.y := by rw [Xv]
    obtain ⟨E1, E2, E3⟩ := l3EndShown X Wo Mm (hvOfH (hhAt SD.S i)) lE (reads_true_pub X Mm hW)
      hlE hE
    refine ⟨⟨X.h, X.pc, X.s, _, _, _, sig_of_pub X Xρ hscl Xp' Xc Wo Mm hW⟩,
      hhAt_gated h hts htu Ss Su N hlt hne hi, fun ν hν => ?_, fun l' hl' => ?_,
      fun l' e hl' he => ?_⟩
    · rw [← hsl R sh hR hsh ν, E1 ν hν]
      unfold OnBytes.Road.Rows.Pub34.rTrue OnBytes.Road.rTrueP
      rw [Xρ, Xc, ey]
    · rw [← hsl R sh hR hsh, ← ey]
      refine (E2 l' hl').trans ?_
      unfold OnBytes.Road.Rows.Pub34.rTrue OnBytes.Road.rTrueP
      rw [Xρ, Xc, ey]
    · rw [← hsl R sh hR hsh, ← ey]
      refine (E3 l' e hl' he).trans ?_
      unfold OnBytes.Road.Rows.Pub34.rTrue OnBytes.Road.rTrueP
      rw [Xρ, Xc, ey]

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.tokAll_x
