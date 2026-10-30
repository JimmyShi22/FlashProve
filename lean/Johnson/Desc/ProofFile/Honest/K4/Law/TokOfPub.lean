-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/TokOfPub.lean: CONDITIONAL.

What is here. The hypothesis `TokAll` (JoinPub.lean: what is left at one token) FROM THE ONE PUBLIC
STRUCTURE `Pub34` AT THE END POINT, and from returns. Pub34At.lean's `pub34At` moves the structure
to the token's corner; TokAtY.lean's `tokAll_y` is called there. And so `JoinWorth`
(StackStart.lean) from one structure: JoinAtX.lean's `joinWorth_x` with `TokAll` laid in at every
token.

  `TokRet`   the returns at one token
  `tokAll_pub`   **what is left at a token, from the structure at the end point**
  `joinWorth_ret`   **`JoinWorth` from one structure**

Limits. At the reading `Reading.gl`. THE FULL SIZE ALONE (X). NOTHING NEW IS SHOWN: calls. `TokRet`
IS A HYPOTHESIS AT EVERY TOKEN: that eight of the verifier's and the honest side's functions return
at the token's corner (the honest reads and end values; `pointsOf`, `funsOf`, `panelsT`,
`weightClaims`, `stackEnd`, `termsForms`), that the number of rounds is the logarithm of the panels'
places, and that the token's two points are a part of the named points: returns and public facts;
shown nowhere here: TokRetOf.lean's `tokRet_of` shows it. A token's corner: the point of zeros and
ones that spells the token's number (`bitsOf lt i`). THE OTHER HYPOTHESES OF `joinWorth_ret`, ALL
(they are `joinWorth_x`'s, but `TokAll`): on the world W: its entries are the true ones (hW), THE
CLAIM THAT THE LOOKUP READS (hJoin: the library's `Join`), the slot of the claimed sum holds the
honest job's total (hσ): these three bear what is summed; X's two environments are the honest side's
(Xp Xc), and the token point (hzt); on the honest input: `CellsAre`, `TensorIs` twice; on X: its
laying and its sub-proof's matrices in the plan's letters (hl hm), the honest named points are a
part of its points (hpp), the table of scales (hscl), `QKOk`; eight that X itself gives and that
JoinHeard.lean draws from it (hf hd hfew hfw hfef hNE hzs hB); public: `GatedNums`, hdq, hTS, the
two tensors are found; two that hold at all sizes by the library's definitions (hnl hne); the end
function returns at every shown array (hstT); returns: h, hJ; hom. No example of the hypotheses
together is known.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.JoinAtX
import Johnson.Desc.ProofFile.Honest.K4.Law.TokAtY
import Johnson.Desc.ProofFile.Honest.K4.Law.Pub34At

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes (E zeroE ceilLog2)
open OnBytes.Model (Reading Aff World WsClaim HFun)
open OnBytes.Model.Layer (ClaimEnv Panels StackEnd Ten layTables tableAsks funsOf pointsOf panelsT
  panelsA placePanels stackEnd)
open OnBytes.Road (sclOf cellsAt cellsOf zOf Mats admitted_of_layout)
open OnBytes.Road.K4 (entryOf)
open OnBytes.Road.K4.C (sidesEnv stackIs_of CellsAre PtsPart TensorIs GatedNums tokPts)
open Inst.Model (Scl)
open OnBytes.Desc.First.K4.Honest

/-- **The returns at token number i.** This defines a hypothesis; the definition claims nothing. -/
def TokRet (X : OnBytes.Road.Rows.Pub34 Cb.Gl.E) (SD : StackData) (i : ℕ) : Prop :=
  ∃ (R0 : Reads) (sh0 : Array E) (pts : List (String × Array E)) (funs : Array HFun)
    (pans : Panels) (cl : List WsClaim) (fin : StackEnd) (lE : List Aff),
    SD.S.readsTok (OnBytes.Desc.First.K4.Honest.bitsOf SD.S.v.y.h.lt i) = some R0 ∧
    endsOn SD.S R0 = some sh0 ∧
    pointsOf X.p.v.y
      { X.H with tT := some { X.tT with r := OnBytes.Desc.First.K4.Honest.bitsOf SD.S.v.y.h.lt i } }
      X.hd X.hd2 = some pts ∧
    funsOf X.p.v.y X.H.fo pts X.r.2.1 = some funs ∧
    panelsT { X.p with shownT := sh0 } X.TS (panelsA { X.p with shownT := sh0 } {}) = some pans ∧
    ({ X.c with rt := OnBytes.Desc.First.K4.Honest.bitsOf SD.S.v.y.h.lt i } :
      ClaimEnv).weightClaims X.TS = some cl ∧
    stackEnd X.p.v.y (placePanels pans.bl).1 X.c.rs X.lam X.om X.H1 X.V X.shownA X.shownB =
      some fin ∧
    (ceilLog2 (placePanels pans.bl).2 == X.lam) = true ∧
    OnBytes.Desc.First.K4.termsForms SD.S.v
      { X.H with
        tT := some { X.tT with r := OnBytes.Desc.First.K4.Honest.bitsOf SD.S.v.y.h.lt i } } =
      some lE ∧
    PtsPart (tokPts SD.S.zlow (OnBytes.Desc.First.K4.Honest.bitsOf SD.S.v.y.h.lt i)) pts

/-- **WHAT IS LEFT AT TOKEN NUMBER i, FROM THE STRUCTURE AT THE END POINT.** CONDITIONAL: on every
hypothesis named. THE FULL SIZE ALONE (X). -/
theorem tokAll_pub [scl : Scl] {Q : K4Pub} {w : K4In} {p : Pts} {shownT : Array E}
    {SD : StackData} (h : stackData Q w p shownT = some SD) {i : ℕ} {rs : Array E}
    (X : OnBytes.Road.Rows.Pub34 Cb.Gl.E) (Xρ : X.ρ = Reading.gl)
    (hscl : scl = sclOf X.h X.p.v.sc X.p.v.g X.p.v.y.Lam) (Xp : X.p = sidesEnv SD.S shownT)
    (Xc : X.c = { SD.S.ce with rs := rs, rt := p.rt }) (hTS : SD.S.TS = [0, 1, 2, 5])
    (Mm : Mats Cb.Gl.E) (hl : layTables (matsOf Q) (tableAsks Q.P.y Q.P.rd Q.g) 0 = some X.r)
    (hm : (X.tl.mats.map fun M => (M.m, M.k)) = matsOf Q) (hC : CellsAre Q w Mm) {tB0 : ℕ}
    (hB : SD.S.v.tabAt "b-bits-0" = some tB0) {ts tu : Ten} (hts : Q.P.y.T_ "s" = some ts)
    (htu : Q.P.y.T_ "u" = some tu)
    (Ss : TensorIs Q w (cellsOf X.D (cellsAt SD.S.v.y Mm)) .sl ts)
    (Su : TensorIs Q w (cellsOf X.D (cellsAt SD.S.v.y Mm)) .up tu) (N : GatedNums Q X.D)
    (hne : 2 * X.D.ne ≤ 2 ^ X.D.lL) (hi : i < 2 ^ X.D.lT) (T : TokRet X SD i) :
    TokAll SD.S X.D (cellsOf X.D (cellsAt SD.S.v.y Mm)) X.tb (SD.S.ce.v.g * SD.S.ce.v.y.Lam) X.lk
      (zOf Reading.gl X.H.fo.zx X.H.fo.zy) i := by
  obtain ⟨R0, sh0, pts, funs, pans, cl, fin, lE, hR0, hsh0, hpts, hfun, hp, hcl, hst, hlam, hlF,
    hpp⟩ := T
  have ey : X.p.v.y = SD.S.v.y := by rw [Xp]; rfl
  obtain ⟨_, tbI, I⟩ := stackIs_of h
  have hlt : X.D.lT = SD.S.v.y.h.lt := by
    rw [X.Z.lT, ← (admitted_of_layout X.hy X.S.p3).shape, ey]
  refine tokAll_y h (rs := rs)
    (pub34At X (OnBytes.Desc.First.K4.Honest.bitsOf SD.S.v.y.h.lt i) sh0 pts funs pans cl fin hpts
      hfun hp hcl hst hlam) Xρ hscl (fun R sh hR' hsh' => ?_) ?_ ?_ hTS Mm hR0 hsh0 hlF hl ?_
    hpp hm hC hB rfl rfl rfl rfl rfl rfl hts htu Ss Su N hlt hne hi
  · obtain rfl : R0 = R := Option.some.inj (hR0.symm.trans hR')
    obtain rfl : sh0 = sh := Option.some.inj (hsh0.symm.trans hsh')
    show ({ X.p with shownT := sh0 } : OnBytes.Model.Layer.PanelEnv) = _
    rw [Xp]
    rfl
  · show X.p.v = SD.S.v
    rw [Xp]
    rfl
  · show ({ X.c with rt := OnBytes.Desc.First.K4.Honest.bitsOf SD.S.v.y.h.lt i } : ClaimEnv) = _
    rw [Xc]
  · show funsOf Q.P.y X.H.fo pts X.r.2.1 = some funs
    rw [← I.y, ← ey]
    exact hfun

/-- **`JoinWorth` FROM ONE PUBLIC STRUCTURE AND RETURNS.** CONDITIONAL: on every hypothesis named.
THE FULL SIZE ALONE (X). -/
theorem joinWorth_ret [scl : Scl] {Q : K4Pub} {w : K4In} {p : Pts} {shownT : Array E}
    {SD : StackData} (h : stackData Q w p shownT = some SD) {J : Job}
    (hJ : jobTermsOn SD.S = some J) {rs : Array E}
    (X : OnBytes.Road.Rows.Pub34 Cb.Gl.E) (Xρ : X.ρ = Reading.gl)
    (hscl : scl = sclOf X.h X.p.v.sc X.p.v.g X.p.v.y.Lam) (Xp : X.p = sidesEnv SD.S shownT)
    (Xc : X.c = { SD.S.ce with rs := rs, rt := p.rt }) (hzt : SD.S.zt = X.H.ztF)
    (W : World Cb.Gl.E) (Mm : Mats Cb.Gl.E)
    (hW : W.entry = entryOf X.ρ X.tl X.funs X.p.v.iU3 X.p.v.K3 Mm)
    (hl : layTables (matsOf Q) (tableAsks Q.P.y Q.P.rd Q.g) 0 = some X.r)
    (hf : funsOf Q.P.y X.H.fo X.pts X.r.2.1 = some X.funs) (hpp : PtsPart (namedPts Q p) X.pts)
    (hm : (X.tl.mats.map fun M => (M.m, M.k)) = matsOf Q) (hC : CellsAre Q w Mm) {tB0 : ℕ}
    (hB : SD.S.v.tabAt "b-bits-0" = some tB0) {ts tu : Ten} (hts : Q.P.y.T_ "s" = some ts)
    (htu : Q.P.y.T_ "u" = some tu)
    (Ss : TensorIs Q w (cellsOf X.D (cellsAt SD.S.v.y Mm)) .sl ts)
    (Su : TensorIs Q w (cellsOf X.D (cellsAt SD.S.v.y Mm)) .up tu) (N : GatedNums Q X.D)
    (hnl : X.D.nl ≤ 2 ^ X.D.lL) (hne : 2 * X.D.ne ≤ 2 ^ X.D.lL) (hd : X.s.d = SD.S.v.y.h.d)
    (hfew : X.s.fe = SD.S.v.y.h.fe) (hdq : X.s.dq ≤ SD.S.v.y.dq) (hfw : X.s.f ≤ SD.S.v.y.h.f)
    (hfef : X.s.fe ≤ SD.S.v.y.h.f) (hNE : X.s.NE ≤ SD.S.v.y.h.NE)
    (hTS : SD.S.TS = [0, 1, 2, 5]) (hom : Reading.gl.val (SD.om.getD 0 zeroE) = 1)
    (hstT : ∀ sh bl places, SD.S.panels sh = some (bl, places) → ∃ rs om H1 V lam sA sB s',
      stackEnd SD.S.v.y bl rs lam om H1 V sA sB = some s')
    (hzs : SD.S.zt.size = SD.S.v.y.h.lt) (hQK : X.QKOk)
    (Tr : ∀ i, i < 2 ^ X.D.lT → TokRet X SD i) (hJoin : X.Join W Mm (wmOf w.w))
    (hσ : W.slot X.tT.sCl = Reading.gl.val J.cube.total) :
    JoinWorth X.H X.tT X.parts W SD :=
  joinWorth_x h hJ X Xρ hscl Xp Xc hzt W Mm hW hl hf hpp hm hC hB hts htu Ss Su N hnl hd hfew hdq
    hfw hfef hNE hTS hom hstT hzs hQK
    (fun i hi => tokAll_pub h X Xρ hscl Xp Xc hTS Mm hl hm hC hB hts htu Ss Su N hne hi (Tr i hi))
    hJoin hσ

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.tokAll_pub
#print axioms ProofFile.Honest.K4.joinWorth_ret
