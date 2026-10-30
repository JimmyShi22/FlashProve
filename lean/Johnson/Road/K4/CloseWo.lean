-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/CloseWo.lean: AT A YES OF THE PIECE THAT HOLDS K4's BLOCK, IN A GROUP THAT IS NOT
THE FIRST: THE NAMED SENTENCE `WoSays` (Johnson/Road/K4/OwnPending.lean) OF THE HEARING's OWN MERGE
RECORD, AT THE SEVENTH STATE READ OFF THE TAPE, AGAINST THE ROW THAT `pendingRowO` RETURNS. Five
theorems. Glue: `woSays_at_led` (WoAtLed.lean) with its premises on sizes, numberings, outputs and
the public record concluded under `Plan4.Meets`, as Johnson/Road/K4/SixK.lean and CloseRows.lean do
it for the own rows. That the public lines' number of column bits is the value's is concluded
(`PubLines`' hlw, `unitOK_of_layout`, `Meets`' wk). No draw, no count.

  `pubAtWo_of_led`: under the premises of `pubAt_of_led` (PubAt.lean): there is X with `PubAt` at
    Led7's own G2 and tc4, X.rd = Pp.rd and X.lk = lk. Bookkeeping over `pub34_of_hear_run`
    (PubOfHearTied.lean), which concludes both.
  `numK_of_num4`: if `num4` at a numbering num of the weight claims gives `numK`'s numbers, then
    claim number i of num has the number i in `numK`.
  `readsTrue_zero`: at every public record X the reads are true (`Pub34.ReadsTrue`) in the world
    `zeroW` (Johnson/Road/K4/ZeroWorld.lean), of the matrices 0. `woSays_at_led` asks true reads in
    SOME world and names none in its conclusion: so this pays that premise.
  `Plan4L.wo_led`: at a hearing, at the value with its slots and orders laid (`Plan4L`), under
    `Meets` and the premises that `Plan4L.wo_at` concludes for it or asks itself (its binders: the
    fourth claimed sum, the token point, zOf, a public record with `PubAt`, its reads' numbers and
    its number of column bits, o.v.y, the table of scales, the first layer, n4, hr, hidx): `WoSays`
    holds exactly if the row's sentence does.
  `Plan4L.wo_at`: the same at a yes, at every `Led7` and `TgRec` of that hearing. The left side is
    typed after what the field wo of `Plan4L.Owes` (Johnson/Road/K4/CloseK.lean) concludes: held by
    eye: that file is not imported.

THE ROW's SENTENCE: the sum over the cube's rows of `pendWeight gl r.g j` times the committed
matrix's row j read at the point `r.psi` turned round, plus the sum over the row's named mask
entries of the entry times its factor, is the reading of `r.target`.

Limits. PREMISES THAT STAY, in `Plan4L.wo_at`: `Plan4.Meets` and pc.ds = dsLater par · the yes · the
ledger in front has arrays of the right sizes · `PubLines`, `LookLines`, the rotary tables' fit ·
zOf and kTg at the first statement; the lookup's end form has filled slots alone · `ValueIs` (of it
the table of scales and the first layer are read), `ValueMore` (of it n4) · `Led7` and `TgRec` · hr:
`pendingRowO` returns · hidx: the index masks' entry that the row names is the typed mask entry. im,
os, claims and S are letters: that a layers' link's end calls `pendingRowO` at the index masks'
number, the statement's messages, the plan's count and this record is not said here; nor that the
letter `Lt.wo` of the law gives such a row and its sentence. The cells are the value's `Wn` at the
message of part w: that another file's cells are these is not said. Nothing shows that these can be
met together. An equivalence of two sentences on numbers. Nothing on soundness.
-/
import Johnson.Road.K4.WoAtLed
import Johnson.Road.K4.CloseRows
import Johnson.Road.K4.ZeroWorld

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Finset
open TWhole Iop Cb Cb.Sub Cb.Pv.Att Cb.Pv.Lay Cb.Pv.Lay.At Cb.Pv.Lay.End
open OnBytes OnBytes.K.Kc OnBytes.Flat OnBytes.Maker OnBytes.Road OnBytes.Road.Rows
open OnBytes.Model (Reading Fork Forest.Heard Level Tsc WsShape HTailF2)
open OnBytes.Model.Layer (Pub HPlan2 Own Heard)
open OnBytes.Desc.First.K4 (Par Seat hear engFl)
open OnBytes.Desc.First.P1 (gl NzT TailM Tg7 aS7 addsOf drawnOf tailIs_at)
open _root_.Run (ckP)
open VerifiableInference.Desc.Sound (Frame Piece)
open VerifiableInference.Desc.First.Pend (pendingRowO)
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim LW zpos)

/-- **The public record at a hearing, with its reads' numbers and its number of column bits.** -/
theorem pubAtWo_of_led {Pp : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {o : Own}
    {F G : Fork} {t0 u : Tape} {H1 : Heard} {hd2 : Level} {tT : Tsc}
    {F4 F7 F8 G1 G1' G2 G3 G3' G4 : Fork}
    (h : hear engFl Pp hp g fo F t0 = some (o, G, u))
    (Ld : Led7 Pp hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4)
    {hS : OnBytes.Model.Layer.Shape} {pc : List (List String)} {D : Dim} {tb : Tables}
    {s : WsShape} {lk : ℕ} {s0 : OnBytes.Model.Forest.Shape} {tl : HTailF2}
    (B : PubLines Pp g hS pc D tb s lk s0 tl) (K : LookLines Pp fo s0)
    (Rp : ∀ (rt : Array E) (lam : ℕ), lam < Pp.y.Lam →
      RopeFits Reading.gl
        { v := o.v, wsLay := Pp.wsLay, rope := Pp.rope, rs := o.K.rs, rt := rt } D tb
        (g * Pp.y.Lam) lam)
    (hinv : ∀ tT, o.H.tT = some tT →
      Reading.gl.val (negE (invE tT.p.eps)) * Reading.gl.val tT.p.eps = -1) :
    ∃ X : Rows.Pub34 Cb.Gl.E,
      PubAt X Pp hp fo o G2 ((ksOf Pp hp).tc4 (t0.drop 1)) D tb hS ∧ X.rd = Pp.rd ∧ X.lk = lk := by
  obtain ⟨X, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, _, a13, a14, a15, a16, _, _, a19, a20,
    _, _, a23, a24, a25, a26, _, _, H1', G1x, G2x, _, _, u1x, u2x, _, n1, n2, _, hom, hst, hsh,
    _⟩ :=
    pub34_of_hear_run Reading.gl h B.hy B.S B.hs B.hg B.hrd B.hmats B.hρ B.Z B.hc B.hN B.hfl K.hsx
      K.hsy K.hzk K.he B.hs0 K.hpt B.Zw B.hsL B.hlw B.h4 Rp B.htm B.hNM B.hpad hinv
  obtain ⟨u1, m1, m2⟩ := Ld.nt
  have e1 := Option.some.inj (n1.symm.trans m1)
  simp only [Prod.mk.injEq] at e1
  obtain ⟨rfl, rfl, rfl⟩ := e1
  have e2 := Option.some.inj (n2.symm.trans m2)
  simp only [Prod.mk.injEq, true_and] at e2
  obtain ⟨rfl, rfl⟩ := e2
  obtain ⟨_, _, _, _, _, _, _, q6⟩ := Desc.First.K4.hearNorms_public m1
  obtain ⟨kfo, _⟩ := Desc.First.K4.hearTerms_keeps m2
  exact ⟨X, ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a13, a15, a16, a20, a23, a24, a25, a26,
    hom, hst, hsh, by rw [kfo, q6]⟩, a14, a19⟩

/-- If `num4` at num gives `numK`'s numbers, claim number i of num has the number i in `numK`. -/
theorem numK_of_num4 (D : Dim) {n : ℕ} (num : Fin n ≃ Piece D)
    (h : ∀ q, num4 D num q = num4 D (numK D) q) (i : Fin n) :
    ((numK D).symm (num i)).val = i.val := by
  have q : 2 + (1 + D.ne) + (num.symm (num i)).val =
      2 + (1 + D.ne) + ((numK D).symm (num i)).val := h (Sum.inr (Sum.inr (num i)))
  rw [Equiv.symm_apply_apply] at q
  omega

/-- **Every public record's reads are true in the world in which every hidden value is 0, of the
matrices 0**: each entry of the reads is there 0, and so is each sum of entries under weights. -/
theorem readsTrue_zero {K : Type} [Field K] (X : Rows.Pub34 K) :
    X.ReadsTrue zeroW (fun _ _ _ => 0) := by
  intro Fn _ c sg pos _
  show (0 : K) = ∑ j ∈ range Fn.len, X.ρ.val (Fn.phi.getD j zeroE) * 0
  exact (sum_eq_zero fun _ _ => mul_zero _).symm

variable [scl : Scl] {Mm X T Wt Cl : Type} {Fr : Frame} {QL : Plan4L Cb.Gl.E Mm X} {par : Par}
  {hS : OnBytes.Model.Layer.Shape} {pcl : List (List String)}

/-- **The named sentence at a hearing, at the value, of the row that `pendingRowO` returns.** -/
theorem Plan4L.wo_led (A : QL.plan.Meets par hS pcl) (tk : Array Nat) {fo : Forest.Heard}
    {o : Own} {F G : Fork} {t0 u : Tape} {H1 : Heard} {hd2 : Level} {tT : Tsc}
    {F4 F7 F8 G1 G1' G2 G3 G3' G4 : Fork}
    (h : hear engFl { par.P with tokv := tk } par.hp par.g fo F t0 = some (o, G, u))
    (Ld : Led7 { par.P with tokv := tk } par.hp par.g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2
      G3 G3' G4)
    (nz : NzT QL.plan.full.own.toOwn.tail (ksOf { par.P with tokv := tk } par.hp) (t0.drop 1))
    (x : X × (Fin QL.plan.full.own.toOwn.gT → Cb.Gl.E)) (g7 : Tg7)
    (I : TgRec g7 { par.P with tokv := tk } par.hp o t0 H1 tT F4 G2 G3 G3')
    (hc4 : (k4Tail (Plan4L.wK A) { par.P with tokv := tk } par.hp t0 nz
        (addsOf (Plan4L.wK A) (ksOf { par.P with tokv := tk } par.hp)
          (t0.drop 1) nz x g7)).d4.Claim
      ((k4Tail (Plan4L.wK A) { par.P with tokv := tk } par.hp t0 nz
        (addsOf (Plan4L.wK A) (ksOf { par.P with tokv := tk } par.hp)
          (t0.drop 1) nz x g7)).y4 x))
    (hx : ∀ j : Fin QL.plan.full.own.toOwn.gT, x.2 j = gl.val ((drawnOf t0).getD j.val zeroE))
    (hz0 : QL.plan.full.zOf x.1 = zAt fo) (Xp : Rows.Pub34 Cb.Gl.E)
    (PX : PubAt Xp { par.P with tokv := tk } par.hp fo o G2
      ((ksOf { par.P with tokv := tk } par.hp).tc4 (t0.drop 1)) QL.plan.full.D QL.plan.full.tb hS)
    (Xrd : Xp.rd = par.P.rd) (Xlk : Xp.lk = QL.plan.full.kW)
    (hvy : o.v.y = par.P.y) (hscl : scl = sclOf hS o.v.sc o.v.g o.v.y.Lam)
    (hL0 : o.v.g * o.v.y.Lam = QL.plan.full.ip.L0)
    (hn4 : ∀ q, num4 QL.plan.full.D QL.plan.full.num q = num4 QL.plan.full.D (numK QL.plan.full.D)
      q)
    (claims : ℕ) (S : Params.LinShape) {im : ℕ} {os os' : Array Oracle} {r : TensorRow}
    (hr : pendingRowO par.P.wsLay im o.wo claims S os = .ok (r, os')) (idx : ℕ → Cb.Gl.E)
    (mm : Mm) (hidx : ∀ y ∈ r.masks, idx y.1.index = QL.plan.full.msg mm QL.plan.full.c7) :
    WoSays QL.plan.full
        (aS7 (Plan4L.wK A) (ksOf { par.P with tokv := tk } par.hp) (t0.drop 1) nz x g7) o.wo mm ↔
      ∑ j ∈ range (2 ^ S.kRow),
          pendWeight gl r.g j * rowAt gl par.P.wsLay.lk r.psi.reverse.toArray
            (QL.plan.full.Wn (QL.plan.full.msg mm)) j +
        (r.masks.map fun y => idx y.1.index * gl.val y.2).sum = gl.val r.target := by
  have OT := outTies_K A tk Ld.c4
  have Sz := sevenSizes_of_meets A tk
  have Nm := numTies_K QL.plan.full (tailIs_at QL.plan.full
    (OnBytes.Model.Verify.layerNumbers par.P par.hp par.g) A.dimIs A.wk A.hg) A.written.2.2
    (A.lamM tk)
  have hzp : ∀ j, j < QL.plan.full.D.lT →
      zpos QL.plan.full.D (zAt fo) j = gl.val (H1.ztF.getD j zeroE) := by
    intro j hj
    have q := zpos_pub Xp (by rw [PX.D, PX.v, hvy]; exact OT.lt) j (by rw [PX.D]; exact hj)
    rw [PX.D, PX.H, PX.fo, Ld.ztF] at q
    exact q
  obtain ⟨_, _, O3, O4, _, _, _⟩ := outs_of_led QL.plan.full (Plan4L.wK A) Ld OT nz x
    g7 I hx hz0 hzp
  have hsX : scl = sclOf Xp.h Xp.p.v.sc Xp.p.v.g Xp.p.v.y.Lam := by rw [PX.h, PX.v]; exact hscl
  have eT : Xp.tT = { tT with p := { tT.p with rowMade := true } } :=
    Option.some.inj (PX.tT.symm.trans Ld.kTT)
  have hW : QL.plan.full.nW = par.hp.NCL - (if (par.g == 0) = true then 1 else 0) :=
    OnBytes.Tie.Pv.Lay.At.nW_eq QL.plan.full _ A.dimIs
  rw [if_neg (by rw [A.hg]; exact Bool.false_ne_true)] at hW
  exact woSays_at_led QL.plan.full (Plan4L.wK A) Ld h A.hg nz x g7
    (addsOf (Plan4L.wK A) (ksOf { par.P with tokv := tk } par.hp) (t0.drop 1) nz x g7) rfl hc4
    O3 O4 Sz.k3 Sz.k4 Nm.n3 Sz.hNN Sz.hLM Sz.hNE Sz.hEnd Xp PX.ρ PX.H
    (by have q := PX.c; rw [eT] at q; exact q) Xrd
    (by have q := PX.sh; rw [eT] at q; exact q) PX.om PX.D PX.tb
    (by rw [PX.c]; exact hL0) Xlk hsX (by rw [PX.fo]; exact hz0) (by rw [PX.fo]; exact hz0) zeroW
    (fun _ _ _ => 0) (readsTrue_zero Xp) (numK_of_num4 QL.plan.full.D QL.plan.full.num hn4)
    (by omega) claims S hr idx mm hidx

/-- **The named sentence at a yes, of the row that `pendingRowO` returns.** -/
theorem Plan4L.wo_at (A : QL.plan.Meets par hS pcl) (L : Seat T) (Ex : ExtSpec)
    {pc : Piece (ckP .two) Fr T Cl Wt} (hds : pc.ds = dsLater par)
    (fa : T × Fr.E.Str → X × Ex.Str) (part : Wt → Mm) (a : T × Fr.E.Str)
    (τ : Tr (uLT (ckP .two) pc.ds)) {fo : Forest.Heard} {o : Own} {G : Fork}
    (Y : Yes L par pc a τ fo o G) (w : Wt) (hF : PscRun.Sized (L.fork a.1)) {s : WsShape}
    {lk : ℕ} {s0 : OnBytes.Model.Forest.Shape} {tl : HTailF2}
    (B : PubLines { par.P with tokv := L.tokv a.1 } par.g hS pcl QL.plan.full.D QL.plan.full.tb s
      lk s0 tl)
    (K : LookLines { par.P with tokv := L.tokv a.1 } fo s0)
    (Rp : ∀ (rt : Array E) (lam : ℕ), lam < par.P.y.Lam →
      RopeFits Reading.gl
        { v := o.v, wsLay := par.P.wsLay, rope := par.P.rope, rs := o.K.rs, rt := rt }
        QL.plan.full.D QL.plan.full.tb (par.g * par.P.y.Lam) lam)
    (lw : ℕ → LW Cb.Gl.E) (hz0 : QL.plan.full.zOf (fa a).1 = zAt fo)
    (hk0 : QL.plan.full.kTg (fa a).1 = kTgAt fo (L.fork a.1))
    (hfil : Fo.FilledA (L.fork a.1) fo.cEnd)
    (V : Plan4L.ValueIs QL par hS) (V2 : Plan4L.ValueMore QL)
    (g7 : Tg7) {H1 : Heard} {hd2 : Level} {tT : Tsc} {F4 F7 F8 G1 G1' G2 G3 G3' G4 : Fork}
    (Ld : Led7 { par.P with tokv := L.tokv a.1 } par.hp par.g fo o (L.fork a.1) G
      (tapeAt par pc τ) [] H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4)
    (I : TgRec g7 { par.P with tokv := L.tokv a.1 } par.hp o (tapeAt par pc τ) H1 tT F4 G2 G3 G3')
    (claims : ℕ) (S : Params.LinShape) {im : ℕ} {os os' : Array Oracle} {r : TensorRow}
    (hr : pendingRowO par.P.wsLay im o.wo claims S os = .ok (r, os')) (idx : ℕ → Cb.Gl.E)
    (hidx : ∀ y ∈ r.masks, idx y.1.index = QL.plan.full.msg (part w) QL.plan.full.c7) :
    WoSays QL.plan.full (aS7 (Plan4.tailMK A (numsK QL.plan.full))
        (ksOf { par.P with tokv := L.tokv a.1 } par.hp) ((tapeAt par pc τ).drop 1)
        (Plan4.nzAt A (L.tokv a.1) hds τ _) ((fa a).1, ptOf QL.plan (tapeAt par pc τ)) g7)
        o.wo (part w) ↔
      ∑ j ∈ range (2 ^ S.kRow),
          pendWeight gl r.g j * rowAt gl par.P.wsLay.lk r.psi.reverse.toArray
            (QL.plan.full.Wn (QL.plan.full.msg (part w))) j +
        (r.masks.map fun y => idx y.1.index * gl.val y.2).sum = gl.val r.target := by
  obtain ⟨hinv, hscl, hvy, hL0, _, _⟩ :=
    Plan4L.heard_K A Y.hears hF (small_of_all _ _ _ Y.small) V.scl V.L0
  have hc : Plan4.ClaimsAt A (numsK QL.plan.full) (L.tokv a.1) hds τ (fa a).1
      (addsOf (Plan4.tailMK A (numsK QL.plan.full))
        (ksOf { par.P with tokv := L.tokv a.1 } par.hp) ((tapeAt par pc τ).drop 1)
        (Plan4.nzAt A (L.tokv a.1) hds τ _) ((fa a).1, ptOf QL.plan (tapeAt par pc τ)) g7) :=
    claims_of_led (Plan4.tailMK A (numsK QL.plan.full)) Ld _ _ g7 hF A.dimIs A.hg
      (A.lamM (L.tokv a.1)) gl_half (nums4_numsK QL.plan.full) I
      (first4_full QL.plan.full (Plan4.tailMK A (numsK QL.plan.full)) Y.hears Ld A.hy B.S B.hs
        B.hg B.hrd B.hmats B.hρ A.Z B.hc B.hN B.hfl K.hsx K.hsy K.hzk K.he B.hs0 K.hpt B.Zw B.hsL
        B.hlw B.h4 Rp B.htm B.hNM B.hpad hinv hscl A.dimIs.lt hvy lw _ _ g7 I.t3 I.t4 hz0 hk0
        hfil)
  obtain ⟨Xp, PX, Xrd, Xlk⟩ := pubAtWo_of_led Y.hears Ld B K Rp hinv
  exact Plan4L.wo_led A (L.tokv a.1) Y.hears Ld _ _ g7 I hc.c4 (fun _ => rfl) hz0 Xp PX Xrd
    (Xlk.trans ((unitOK_of_layout B.hlw).1.symm.trans A.wk.symm)) hvy hscl hL0 V2.n4
    claims S hr idx (part w) hidx

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.pubAtWo_of_led
#print axioms OnBytes.Road.K4.numK_of_num4
#print axioms OnBytes.Road.K4.readsTrue_zero
#print axioms OnBytes.Road.K4.Plan4L.wo_led
#print axioms OnBytes.Road.K4.Plan4L.wo_at
