-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/KeysWorth.lean: kind K5: what the key forms are worth: the twins of
Johnson/Desc/First/Att/Claims/KeysLin.lean gathered, and the four key forms as the extensions of the
calls' vectors of looked-up values.

Main names:
  `PlaneM`, `PlaneD`: the public premises at one plane claim below, on the diagonal: its flag; the
    family's region and length; piece b is pair b; the pieces' weights and the inner point are the
    library's; the table on "as" lies in the list with the point's own last coordinates as weights.
  `LinPub`: the public premises of all the twins at once: four plane claims (the two of the
    remainder-table units; the two of the softmax-table units, whose first slot is the unit's); the
    two units' row maxima; the segments wl, ix, wh.
  `LinIn`: the indices that the linear claims read lie in their tables; the heads' features are
    lawful: ten clauses in the words of Johnson/Desc/First/Att/Claims/KeysIn.lean, which draws each
    out of the return of "first".
  `keys_lin`: **under LinPub and LinIn, in a world where every table is true (AttAt) and the written
    claims are worth 0 (PlanesSay twice, UnitAt twice, Say5): EVERY NAMED SCALAR THAT THE KEY FORMS
    READ (ReadK, Cb/Pv/Att/End/Seam.lean) AND THAT ONE CLAIM TIES TO A TABLE (Linear,
    Johnson/Road/Rows/AttBetween.lean) HAS ITS RULE VALUE ON THE CELLS.**
  `ProdAt`: the four others (the two scores, the accumulator, the denominator times the output) have
    theirs. A NAMED PREMISE: their rule values are sums of products of cells: what the sumchecks
    claim. No claim ties them to a table, and "every form is worth 0" at one drawn point does not
    give them: that step has probability in it and is the law of the masked sumcheck's.
  `kf_worth`: **at ANY values v of the named scalars that are the rule values wherever the key forms
    read them: KF D C p v c = Blocks.ext (C.a c) (keyVec D tb t c) (C.zC c p.z).** No world, no
    slot: KF_congr and kfExt. The form that the chain's first joint can spend.
  `keysPort_worth`: **keys_lin's premises, ProdAt, KeyPub and the three conditions of kfExt on the
    lookup's layout ⇒ for each of the four calls c: the written sum of terms kfPort h u sd pad c
    (Johnson/Road/Rows/AttKeyPort.lean) is worth Blocks.ext (C.a c) (keyVec D tb (cellsK h.S M) c)
    (C.zC c p.z): the extension of the call's vector of looked-up values at its key point.**
Limits: AttAt's clause "every table is true" is a premise: the smallness test is there to show it.
LinPub, KeyPub and kfExt's three conditions are public facts: not shown here of what pointsOf and
tablesP make. That a run's key forms are the sums kfPort is not made here. ProdAt is a premise.
THE TWO SILLY MEMBERS: a list of claims that holds no claim (PlanesSay, UnitAt, Say5 idle) makes
keys_lin false; a world in which no table is true makes it empty: the stored proofs' worlds are for
that.
Used: KeysLin.lean; Say.lean, Say58.lean; of the library: ReadK, KF_congr (Cb/Pv/Att/End/Seam.lean),
kfPort_value, KeyPub, slotVal, Linear, Units, dimLT, kfExt (Inst/Model/Att/KeyFormsExt/All.lean).

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Road.Rows.AttKeyPort
import Cb.Pv.Att.End.Seam
import Inst.Model.Att.KeyFormsExt.All
import Johnson.Desc.First.Att.Claims.KeysLin
import Johnson.Desc.First.Att.Claims.KeysIn

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace K5Law
open Cb.Pv.Att
open Cb.Pv.Att.End (ReadK KF_congr)
open Finset
open OnBytes OnBytes.Model OnBytes.Attention OnBytes.Road OnBytes.Road.Rows
open Inst.Model (Scl)
open Inst.Model.AttSeg (Calls Pub rv wp KSc KF Fam keyVec blkRow)

variable {Kf : Type} [Field Kf]

/-! ## The public premises -/

/-- At a plane claim below the diagonal, of the family u. -/
structure PlaneM (ρ : Reading Kf) (h : Attention.Heard) (C : Calls) (p : Pub Kf) (pc : PlaneClaim)
    (u : Fam) : Prop where
  isD : pc.isD = false
  reg : u.reg = .M
  len : u.l (L5.dimOf h.S) = h.S.nM
  pairs : PiecesAll h.S pc.pw
  w : ∀ b < h.S.NP, ρ.val (pc.pw.getD b default).wp = wp (L5.dimOf h.S) C p.z u b
  z : pc.z.size = h.S.nM
  v : ∀ j < h.S.nM, pt ρ pc.z j = Inst.Model.AttSeg.inn (L5.dimOf h.S) C p.z u j
  tab : AsAt h h.t.tA (lastN pc.z h.S.cf.lmS)

/-- At a plane claim on the diagonal, of the family u. -/
structure PlaneD (ρ : Reading Kf) (h : Attention.Heard) (C : Calls) (p : Pub Kf) (pc : PlaneClaim)
    (u : Fam) : Prop where
  isD : pc.isD = true
  reg : u.reg = .D
  len : u.l (L5.dimOf h.S) = h.S.nD
  pairs : PiecesAll h.S pc.pw
  w : ∀ b < h.S.NP, ρ.val (pc.pw.getD b default).wp = wp (L5.dimOf h.S) C p.z u b
  z : pc.z.size = h.S.nD
  v : ∀ j < h.S.nD, pt ρ pc.z j = Inst.Model.AttSeg.inn (L5.dimOf h.S) C p.z u j
  tab : AsAt h h.t.tA (lastN pc.z h.S.cf.lmS)

/-- At a segment whose scalars read the high parts of the remainders: pw, zg, zi, zc: its pieces and
points; u: its family. -/
structure HighPub (ρ : Reading Kf) (tl : HTailF2) (h : Attention.Heard) (C : Calls) (p : Pub Kf)
    (pw : Array PW) (zg zi zc : Array E) (u : Fam) : Prop where
  pairs : PiecesAll h.S pw
  w : ∀ b < h.S.NP, ρ.val (pw.getD b default).wp = wp (L5.dimOf h.S) C p.z u b
  szg : zg.size = h.S.cf.lgk
  szi : zi.size = h.S.cf.lt
  szc : zc.size = h.S.cf.ldh
  g : ∀ j < h.S.cf.lgk, pt ρ zg j = Inst.Model.AttSeg.yg (L5.dimOf h.S) C p.z j
  i : ∀ j < h.S.cf.lt, pt ρ zi j = Inst.Model.AttSeg.yi (L5.dimOf h.S) C p.z j
  n : ∀ j < h.S.cf.ldh, pt ρ zc j = Inst.Model.AttSeg.yn (L5.dimOf h.S) C p.z j
  tab : TabAt tl h h.t.tO (h.S.cf.NAs + 1) (2 ^ h.S.cf.la) (blockRows (lowOf h.S zc) (eqTab zi))

/-- At a unit's scalar on the row maxima, but for the weights of the tile rows. -/
structure MaxPub (ρ : Reading Kf) (tl : HTailF2) (h : Attention.Heard) (C : Calls) (p : Pub Kf)
    (k : Score) (tM : ℕ) (u : Fam) (vg : ℕ → Kf) : Prop where
  pairs : PiecesAll h.S k.pw
  w : ∀ b < h.S.NP, ρ.val (k.pw.getD b default).wp = wp (L5.dimOf h.S) C p.z u b
  zg : k.zg.size = h.S.cf.lgk
  zi : k.zi.size = h.S.cf.lB
  g : ∀ j < h.S.cf.lgk, pt ρ k.zg j = vg j
  i : ∀ j < h.S.cf.lB, pt ρ k.zi j = Inst.Model.AttSeg.zi' (L5.dimOf h.S) C p.z j
  tab : TabAt tl h tM h.S.cf.NAs h.S.T (Attention.tok h.S k.wI k.zi)

/-- **The public premises of all the twins at once.** cM, cD: the plane claims of the two
softmax-table units. -/
structure LinPub (ρ : Reading Kf) (tl : HTailF2) (h : Attention.Heard) (u : Units)
    (cM cD : PlaneClaim) (C : Calls) (p : Pub Kf) : Prop where
  m1 : PlaneM ρ h C p u.pM .m1
  m1n : u.pM.np = 3
  d1 : PlaneD ρ h C p u.pD .d1
  d1n : u.pD.np = 3
  m2 : PlaneM ρ h C p cM .m2
  m2n : cM.np = 5
  m2s : cM.s0 = u.kM.s0
  d2 : PlaneD ρ h C p cD .d2
  d2n : cD.np = 5
  d2s : cD.s0 = u.kD.s0
  msM : MaxPub ρ tl h C p u.kM u.tM.tM .m2 (Inst.Model.AttSeg.zg (L5.dimOf h.S) C p.z)
  msMI : ∀ I < h.S.nT, ρ.val (u.kM.wI.getD I zeroE) =
    blkRow (L5.dimOf h.S) (Inst.Model.AttSeg.zP (L5.dimOf h.S) C p.z)
      (Inst.Model.AttSeg.zs (L5.dimOf h.S) C p.z) I
  msD : MaxPub ρ tl h C p u.kD u.tD.tM .d2 (Inst.Model.AttSeg.zgD (L5.dimOf h.S) C p.z)
  msDI : ∀ I < h.S.nT, ρ.val (u.kD.wI.getD I zeroE) =
    Blocks.eqN ((L5.dimOf h.S).lP + 1) 0 (Inst.Model.AttSeg.zID (L5.dimOf h.S) C p.z) I
  wl : HighPub ρ tl h C p h.d.pwW h.d.zgW h.d.ziW h.d.zcW .w3
  wlT : TabAt tl h h.t.hW h.S.cf.NAs h.S.T (eqTab h.d.ziW)
  wh : HighPub ρ tl h C p h.d.pwH h.d.zgH h.d.ziH h.d.zcH .f4
  ixP : PiecesAll h.S h.d.pwX
  ixW : ∀ b < h.S.NP, ρ.val (h.d.pwX.getD b default).wp = wp (L5.dimOf h.S) C p.z .x3 b
  ixZg : h.d.zgX.size = h.S.cf.lgk
  ixZi : h.d.ziX.size = h.S.cf.lt
  ixG : ∀ j < h.S.cf.lgk, pt ρ h.d.zgX j = Inst.Model.AttSeg.xg (L5.dimOf h.S) C p.z j
  ixI : ∀ j < h.S.cf.lt, pt ρ h.d.ziX j = Inst.Model.AttSeg.xi (L5.dimOf h.S) C p.z j
  ixT : TabAt tl h h.t.hX h.S.cf.NAs h.S.T (eqTab h.d.ziX)

/-- **What the runs' return pays** (Johnson/Desc/First/Att/Claims/KeysIn.lean): the indices that the
linear claims read lie in their tables, and the heads' features are lawful. -/
structure LinIn (h : Attention.Heard) (u : Units) (cM cD : PlaneClaim) : Prop where
  m1 : PlaneIn h u.pM
  d1 : PlaneIn h u.pD
  m2 : PlaneIn h cM
  d2 : PlaneIn h cD
  msM : MaxIn h u.kM u.tM.tM
  msD : MaxIn h u.kD u.tD.tM
  den : DenIn h
  wl : HighIn h h.d.pwW h.d.zcW
  wh : HighIn h h.d.pwH h.d.zcH
  bits : BitIn h

variable {ρ : Reading Kf} {W : World Kf} {tl : HTailF2} {K3 : ℕ} {M : Mats Kf}
  {h : Attention.Heard} {lid : ℕ} {cf : Attention.Cfg} {fs : Model.Forest.Shape} {C : Calls}
  {p : Pub Kf} {u : Units} {cM cD : PlaneClaim}

/-! ## The planes' scalars -/

theorem cellM_of (A : AttAt ρ W tl K3 M h lid cf fs) {pc : PlaneClaim} {f : Fam}
    (P : PlaneM ρ h C p pc f) (I : PlaneIn h pc) (s : PlanesSay ρ W h K3 pc) {jj : ℕ}
    (hj : jj < pc.np) :
    W.slot (pc.s0 + jj) = rv (L5.dimOf h.S) C p (cellsK h.S M) (.cell f jj) := by
  have h0 := s jj hj
  unfold Fo.planeMember at h0
  rw [P.isD] at h0
  have I' := I jj hj
  rw [P.isD] at I'
  exact linCellMF A f P.reg P.len P.pairs P.w P.z P.v P.tab pc.s0 jj
    (fun b hb => I' b (by rw [P.pairs.1]; exact hb)) h0

theorem cellD_of (A : AttAt ρ W tl K3 M h lid cf fs) {pc : PlaneClaim} {f : Fam}
    (P : PlaneD ρ h C p pc f) (I : PlaneIn h pc) (s : PlanesSay ρ W h K3 pc) {jj : ℕ}
    (hj : jj < pc.np) :
    W.slot (pc.s0 + jj) = rv (L5.dimOf h.S) C p (cellsK h.S M) (.cell f jj) := by
  have h0 := s jj hj
  unfold Fo.planeMember at h0
  rw [P.isD] at h0
  have I' := I jj hj
  rw [P.isD] at I'
  exact linCellDF A f P.reg P.len P.pairs P.w P.z P.v P.tab pc.s0 jj
    (fun b hb => I' b (by rw [P.pairs.1]; exact hb)) h0

/-! ## All that one claim ties to a table -/

/-- **Every named scalar that the key forms read and that one claim ties to a table has its rule
value on the cells.** -/
theorem keys_lin (A : AttAt ρ W tl K3 M h lid cf fs) (P : LinPub ρ tl h u cM cD C p)
    (I : LinIn h u cM cD) (s1M : PlanesSay ρ W h K3 u.pM) (s1D : PlanesSay ρ W h K3 u.pD)
    (uM : UnitAt ρ W h K3 u.kM u.tM cM) (uD : UnitAt ρ W h K3 u.kD u.tD cD)
    (s5 : Say5 ρ W h K3) :
    ∀ k, ReadK (L5.dimOf h.S) k → Linear k →
      slotVal W h u k = rv (L5.dimOf h.S) C p (cellsK h.S M) k := by
  intro k hr hl
  have hG : h.S.G = 2 ^ h.S.cf.lgk := (shapedG_of_hid A.shape).G
  match k, hr, hl with
  | .cell .m1 jj, hr, _ => exact cellM_of A P.m1 I.m1 s1M (by rw [P.m1n]; exact hr)
  | .cell .d1 jj, hr, _ => exact cellD_of A P.d1 I.d1 s1D (by rw [P.d1n]; exact hr)
  | .cell .m2 jj, hr, _ =>
    show W.slot (u.kM.s0 + jj) = _
    rw [← P.m2s]
    exact cellM_of A P.m2 I.m2 uM.planes (by rw [P.m2n]; exact hr)
  | .cell .d2 jj, hr, _ =>
    show W.slot (u.kD.s0 + jj) = _
    rw [← P.d2s]
    exact cellD_of A P.d2 I.d2 uD.planes (by rw [P.d2n]; exact hr)
  | .cell .w3 _, hr, _ => exact hr.elim
  | .cell .x3 _, hr, _ => exact hr.elim
  | .cell .f4 _, hr, _ => exact hr.elim
  | .ms .M, _, _ =>
    exact linMsMF A P.msM.pairs P.msM.w P.msM.zg P.msM.zi P.msM.g P.msMI P.msM.i P.msM.tab
      (fun b hb g hg => I.msM b (by rw [P.msM.pairs.1]; exact hb) g (by rw [hG]; exact hg))
      uM.maximum
  | .ms .D, _, _ =>
    exact linMsDF A P.msD.pairs P.msD.w P.msD.zg P.msD.zi P.msD.g P.msDI P.msD.i P.msD.tab
      (fun b hb g hg => I.msD b (by rw [P.msD.pairs.1]; exact hb) g (by rw [hG]; exact hg))
      uD.maximum
  | .ss _, _, hl => exact hl.elim
  | .acc, _, hl => exact hl.elim
  | .zo, _, hl => exact hl.elim
  | .zc, _, _ =>
    exact linZcF A P.wl.pairs P.wl.w P.wl.szg P.wl.szi P.wl.g P.wl.i P.wlT
      (fun b hb g hg => I.den b (by rw [P.wl.pairs.1]; exact hb) g (by rw [hG]; exact hg)) s5.zc
  | .rh, _, _ =>
    exact linRhF A h.d.sRH P.wl.pairs _ P.wl.w P.wl.szg P.wl.szi P.wl.szc P.wl.g P.wl.i P.wl.n
      P.wl.tab (fun b hb => (I.wl.1 b (by rw [P.wl.pairs.1]; exact hb)).long hG) s5.rh
  | .rh', _, _ =>
    exact linRhF' A h.d.sRHP P.wl.pairs _ P.wl.w P.wl.szg P.wl.szi P.wl.szc P.wl.g P.wl.i P.wl.n
      P.wl.tab (fun b hb => (I.wl.2 b (by rw [P.wl.pairs.1]; exact hb)).long hG) s5.rhp
  | .ib k, hr, _ =>
    have hk : k < h.S.cf.lt := by rw [← dimLT A]; exact hr
    exact linIbF A P.ixP P.ixW P.ixZg P.ixZi P.ixG P.ixI P.ixT k
      (fun b hb g hg => I.bits k hk b (by rw [P.ixP.1]; exact hb) g (by rw [hG]; exact hg))
      (s5.ib k hk)
  | .rg, _, _ =>
    exact linRhF A h.d.s5h P.wh.pairs _ P.wh.w P.wh.szg P.wh.szi P.wh.szc P.wh.g P.wh.i P.wh.n
      P.wh.tab (fun b hb => (I.wh.1 b (by rw [P.wh.pairs.1]; exact hb)).long hG) s5.r2
  | .rg', _, _ =>
    exact linRhF' A (h.d.s5h + 1) P.wh.pairs _ P.wh.w P.wh.szg P.wh.szi P.wh.szc P.wh.g P.wh.i
      P.wh.n P.wh.tab (fun b hb => (I.wh.2 b (by rw [P.wh.pairs.1]; exact hb)).long hG) s5.r2p

/-! ## The four that no claim ties to a table -/

/-- The two scores, the accumulator and the denominator times the output have their rule values: A
NAMED PREMISE: sums of products of cells, which the sumchecks claim. -/
def ProdAt (W : World Kf) (h : Attention.Heard) (u : Units) (M : Mats Kf) (C : Calls) (p : Pub Kf) :
    Prop :=
  ∀ k, ¬ Linear k → slotVal W h u k = rv (L5.dimOf h.S) C p (cellsK h.S M) k

/-! ## What the key forms are worth -/

/-- **At any values v of the named scalars that are the rule values wherever the key forms read
them, the library's key form is the extension of the call's vector of looked-up values at its key
point.** No world and no slot: the form in which the proved chain's first joint hands the values on
(there they are bound by "there are"). -/
theorem kf_worth [scl : Scl] (D : Inst.Model.AttSeg.Dim) (C : Calls) (tb : Inst.Model.Tables)
    (p : Pub Kf) (t : Inst.Model.AttSeg.Raw → Kf) {v : KSc → Kf}
    (hv : ∀ k, ReadK D k → v k = rv D C p t k) (hC : C.OK D) (hdeep : ∀ f : Fam, f.l D ≤ C.Dk)
    (hs : C.a 0 = C.a 1) (c : Fin 4) :
    KF D C p v c = Blocks.ext (C.a c) (keyVec D tb t c) (C.zC c p.z) := by
  rw [← Inst.Model.AttSeg.KeyFormsExt.kfExt D C tb p t hC hdeep hs c]
  exact KF_congr D C p hv c

/-- **The four written key forms are worth the extensions of the calls' vectors of looked-up values
at their key points.** -/
theorem keysPort_worth [scl : Scl] (tb : Inst.Model.Tables) (A : AttAt ρ W tl K3 M h lid cf fs)
    (P : LinPub ρ tl h u cM cD C p) (I : LinIn h u cM cD)
    (s1M : PlanesSay ρ W h K3 u.pM) (s1D : PlanesSay ρ W h K3 u.pD)
    (uM : UnitAt ρ W h K3 u.kM u.tM cM) (uD : UnitAt ρ W h K3 u.kD u.tD cD)
    (s5 : Say5 ρ W h K3) (hp : ProdAt W h u M C p) {sd : ShD} {pad : E}
    (Q : KeyPub ρ h u C p sd pad) (hC : C.OK (L5.dimOf h.S))
    (hdeep : ∀ f : Fam, f.l (L5.dimOf h.S) ≤ C.Dk) (hs : C.a 0 = C.a 1) (c : Fin 4) :
    (kfPort h u sd pad c).value ρ W =
      Blocks.ext (C.a c) (keyVec (L5.dimOf h.S) tb (cellsK h.S M) c) (C.zC c p.z) := by
  rw [kfPort_value W Q c]
  refine kf_worth (L5.dimOf h.S) C tb p (cellsK h.S M) (fun k hr => ?_) hC hdeep hs c
  by_cases hl : Linear k
  · exact keys_lin A P I s1M s1D uM uD s5 k hr hl
  · exact hp k hl

end K5Law

#print axioms K5Law.keys_lin
#print axioms K5Law.kf_worth
#print axioms K5Law.keysPort_worth
