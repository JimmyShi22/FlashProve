-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/JoinRun.lean: CONDITIONAL.

What is here. `JoinWorth` at a hearing of K4's own text, in the shape in which StackWhole.lean's
`stack_whole` asks it, WITH NOTHING LEFT AT THE TOKENS: JoinHeard.lean's `joinWorth_tied` with its
hypothesis on the returns at every token's corner paid by TokRetOf.lean's `tokRet_of`, and that on
the end function's return by its `stackEnd_all`. What is asked in its place: the lookup's point is
the hearing's.

  `joinWorth_run`   **`JoinWorth` in `stack_whole`'s shape; nothing left at the tokens**

Limits. At the reading `Reading.gl`. THE FULL SIZE ALONE (X). NOTHING NEW IS SHOWN: calls. X IS A
LETTER with the letters of `HeardX` (JoinHeard.lean): the library's maker is not called here. LEFT
AS HYPOTHESES, ALL: the five ties of the honest side to the hearing (tv te tz tsh trt) and hfo; on
the world W: its entries are the true ones (hW), the claim that the lookup reads (`Join`), the slot
of the claimed sum (hσ); on the honest input: `CellsAre`, `TensorIs` twice; on X: its laying and its
sub-proof's matrices in the plan's letters (hl, hm), the honest named points are a part of its
points (hpp), the table of scales (hscl), `QKOk`; public: `GatedNums`, hdq (it follows from X's
fields and the layout, as in Johnson/Road/K4/C/WsFacts.lean's `ws_facts`; asked all the same), hTS,
hnl, hne, the two tensors are found; returns: h, hJ, hH; hom. No example of the hypotheses together
is known. WHAT THIS FILE's IMPORTS REACH, by a program's walk over import lines that stops,
unopened, at every module under Johnson/Goal/, Johnson/D/, Johnson/Bridge/, Cb/Bridge* or
ThirdParty/: it stopped at two modules under Johnson/Bridge/ and at none under the others; it saw
seven modules whose names hold RecCompile, none of them RecCompile.Honest…, RecCompile.Both… or
RecCompile.PassH…. What lies behind the two is not counted: the numbers are floors. A LAW, NOT A
PART: no file that defines a part of the proof file's description may import this one.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.JoinHeard
import Johnson.Desc.ProofFile.Honest.K4.Law.TokRetOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes (E zeroE)
open OnBytes.Model (Reading Aff World Tsc Fork)
open OnBytes.Model.Layer (Own Ten layTables tableAsks)
open OnBytes.Road (sclOf cellsAt cellsOf Mats ts_eq)
open OnBytes.Road.K4 (entryOf)
open OnBytes.Road.K4.C (stackIs_of CellsAre PtsPart TensorIs GatedNums)
open OnBytes.Desc.First.K4 (engFl hear)
open Inst.Model (Scl)
open OnBytes.Desc.First.K4.Honest

variable {Q : K4Pub} {w : K4In} {p : Pts} {shownT : Array E} {SD : StackData} {tk : Array ℕ}
  {fo : OnBytes.Model.Forest.Heard} {F G : Fork} {t u : OnBytes.K.Kc.Tape} {o : Own}
  {X : OnBytes.Road.Rows.Pub34 Cb.Gl.E}

/-- **`JoinWorth` AT A HEARING, IN `stack_whole`'s SHAPE; NOTHING LEFT AT THE TOKENS.** CONDITIONAL:
on every hypothesis named. THE FULL SIZE ALONE (X). -/
theorem joinWorth_run [scl : Scl] (h : stackData Q w p shownT = some SD) {J : Job}
    (hJ : jobTermsOn SD.S = some J)
    (hH : hear engFl { Q.P with tokv := tk } Q.hp Q.g fo F t = some (o, G, u))
    (T : HeardX X { Q.P with tokv := tk } o) (tv : SD.S.v = o.v) (te : SD.S.fo.e = o.H.fo.e)
    (tz : SD.S.zt = o.H.ztF) (tsh : X.p.shownT = shownT) (trt : p.rt = X.tT.r)
    (hscl : scl = sclOf X.h X.p.v.sc X.p.v.g X.p.v.y.Lam)
    (W : World Cb.Gl.E) (Mm : Mats Cb.Gl.E)
    (hW : W.entry = entryOf X.ρ X.tl X.funs X.p.v.iU3 X.p.v.K3 Mm)
    (hl : layTables (matsOf Q) (tableAsks Q.P.y Q.P.rd Q.g) 0 = some X.r)
    (hpp : PtsPart (namedPts Q p) X.pts)
    (hm : (X.tl.mats.map fun M => (M.m, M.k)) = matsOf Q) (hC : CellsAre Q w Mm)
    {ts tu : Ten} (hts : Q.P.y.T_ "s" = some ts) (htu : Q.P.y.T_ "u" = some tu)
    (Ss : TensorIs Q w (cellsOf X.D (cellsAt SD.S.v.y Mm)) .sl ts)
    (Su : TensorIs Q w (cellsOf X.D (cellsAt SD.S.v.y Mm)) .up tu) (N : GatedNums Q X.D)
    (hnl : X.D.nl ≤ 2 ^ X.D.lL) (hne : 2 * X.D.ne ≤ 2 ^ X.D.lL) (hdq : X.s.dq ≤ SD.S.v.y.dq)
    (hTS : SD.S.TS = [0, 1, 2, 5]) (hom : Reading.gl.val (SD.om.getD 0 zeroE) = 1)
    (hQK : X.QKOk)
    (hfo : p.fo.zx = o.H.fo.zx)
    (hJoin : X.Join W Mm (wmOf w.w))
    (hσ : W.slot X.tT.sCl = Reading.gl.val J.cube.total) :
    ∀ (weighed : Array _) (parts : List Aff) (tT' : Tsc),
      o.v.y.calls.mapM o.v.weighedOf = some weighed →
      ((o.v.y.calls.zip weighed).toList.zipIdx.mapM fun x =>
        o.v.joinPart o.H.fo.alpha o.H.fo.theta x.2 x.1.1 x.1.2) = some parts →
      o.H.tT = some tT' → JoinWorth o.H tT' parts W SD := by
  obtain ⟨Xp, _⟩ := env_tied h hH T tv te tz tsh trt
  have ey : X.p.v.y = SD.S.v.y := by rw [T.v, tv]
  obtain ⟨_, tbI, I⟩ := stackIs_of h
  have hT : SD.S.v.y.T = 2 ^ X.D.lT := by
    rw [I.y]
    exact N.T
  exact joinWorth_tied h hJ hH T tv te tz tsh trt hscl W Mm hW hl hpp hm hC hts htu Ss Su N hnl hne
    hdq hTS hom
    (stackEnd_all X Xp (by rw [hTS]; exact ts_eq X.hy X.S.p3 X.hN X.hrd X.hTS)) hQK
    (fun i hi => tokRet_of h hJ X Xp (by rw [hfo, T.H]) (by rw [hT]; exact hi)) hJoin hσ

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.joinWorth_run
