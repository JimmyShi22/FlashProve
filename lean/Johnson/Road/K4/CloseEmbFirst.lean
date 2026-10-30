-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/CloseEmbFirst.lean: AT A YES OF THE PIECE THAT HOLDS K4's BLOCK, IN THE FIRST GROUP,
AND UNDER WHAT K4's ROW OPENS: THE LIBRARY's CLAIM ON THE STREAM THAT COMES IN (`embClaim`,
Cb/Pv/Lay/End/EmbShare.lean) IS WORTH 0 AT THE ENTRIES `Plan4F.yKF` AND THE FIRST CHAIN's LAST
STATEMENT `Plan4F.eKF` (Johnson/Road/K4/CloseFirst.lean): THE PREMISE uE OF `Plan4LF.eight_at` AND
`nine_at`, THE FIELD emb OF `OwesF`, `Owes3F`, `Owes4F`. It has no model among the later groups'
files: they have no such claim. One theorem. Glue: `uE_of_front` (Johnson/Road/K4/EmbFirst.lean) at
the record `EmbAsks` that `embAsks_at_ptsT` (Johnson/Road/K4/EmbVal.lean) concludes at a hearing,
laid over `Plan4F.atYesF` (ClaimsYesFirst.lean), `pubAtMore_of_ledF` and `Plan4LF.heard_KF`
(CloseKitFirst.lean), `forms_of_behind` (CloseBehind.lean), the seventh tie of `Plan4LF.hm_ofF`
(MaskTiesHFirst.lean) and `sevenSizesF_K` (SevenPaidFirst.lean). No new argument, no draw, no count.

  `Plan4LF.emb_at`: the claim is worth 0, at a yes, under what the row opens, at every first
    statement z of the chain (a letter: the callers lay the image of the statement in front).

WHERE THE ZERO COMES FROM: K4's first run of claims holds the embedding's own form in the first
group (`embeddingForm`, group 12 of `front`, OnBytes/Desc/First/K4/Claims.lean); what the row opens
says that every form of that run is worth 0.

Limits. K04_law IS NOT PROVED BY THIS. THE CLAIM READS NO TOKEN: it ties the scalar that is sent in
the weights' round, less its mask entry, to the stream's limbs at the two further points; that this
scalar is the committed embedding's side at the request's tokens is the pending row's matter (the
field wo). PREMISES THAT STAY, in `emb_at`: those of `Plan4LF.rows_atF` (CloseRowsFirst.lean), with
the letter z for its fa a, less kIncS, «no entry» and «slots below ns + 1»: the seat's two laws ·
the ledger in front has arrays of the right sizes and its next free slot is the value's n0 ·
`ValueIs`, `ValueMoreF` (of it numI) · `PubLines`, `LookLines`, the rotary tables' fit · zOf, kTg at
the first statement; the lookup's end form names filled slots alone · the statement's mask row is
the value's at part w · matrices Mt whose reads are true in the worlds of the ledgers behind the
hearing's, and whose cells are the message's. `Plan4F.MeetsF` and pc.ds = dsFirst par. Nothing shows
that these can be met together. The first group alone. USER: `Plan4KF.owes4F_of_row`
(CloseK5First.lean).
-/
import Johnson.Road.K4.CloseRowsFirst
import Johnson.Road.K4.EmbVal

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open TWhole Iop Cb Cb.Sub Cb.Pv.Att Cb.Pv.Lay Cb.Pv.Lay.At Cb.Pv.Lay.End Cb.Pv.Lay.End.Gated
open OnBytes OnBytes.K.Kc OnBytes.Flat OnBytes.Maker
open OnBytes.Model (Reading Fork Forest.Heard WsShape HTailF2)
open OnBytes.Model.Layer (Own)
open OnBytes.Desc.First.K4 (Par Seat k0 later_fo formsFrontWith formsFrontWith_later)
open OnBytes.Desc.First.P1 (gl)
open _root_.Run (ckP)
open VerifiableInference.Desc.Sound (Frame Piece)
open VerifiableInference.Desc.Plain.K04 (Sem Letters Behind)
open Inst.Model (Scl)
open Inst.Model.FFSeg (LW)

variable [scl : Scl] {Mm X T Wt Cl : Type} {Fr : Frame} {par : Par}
  {hS : OnBytes.Model.Layer.Shape} {pcl : List (List String)}

/-- **The library's claim on the stream that comes in is worth 0, at a yes in the first group, under
what the row opens**: from `MeetsF`, the piece's rounds, the yes, what the row opens, the seat's two
laws, the sizes of the ledger in front, `PubLines`, `LookLines`, the rotary tables' fit, zOf and kTg
at the first statement z, the filled slots of the lookup's end form, matrices whose reads are true
and whose cells are the message's, `ValueIs`, `ValueMoreF`, n0 and the masks' line. -/
theorem Plan4LF.emb_at {QF : Plan4LF Cb.Gl.E Mm X} (A : QF.planF.MeetsF par hS pcl) (L : Seat T)
    (Sm : Sem Wt)
    (Lt : Letters T Wt Fr) (Ex : ExtSpec) {pc : Piece (ckP .two) Fr T Cl Wt}
    (hds : pc.ds = dsFirst par) (z : X × Ex.Str) (part : Wt → Mm)
    (a : T × Fr.E.Str) (τ : Tr (uLT (ckP .two) pc.ds)) {fo : Forest.Heard} {o : Own} {G : Fork}
    (Y : Yes L par pc a τ fo o G) (w : Wt)
    (hB : Behind L Sm Lt par (behindOf L pc a τ o G) w) (hL : SeatOk L a.1)
    (hF : PscRun.Sized (L.fork a.1)) {s : WsShape} {lk : ℕ} {s0 : OnBytes.Model.Forest.Shape}
    {tl : HTailF2}
    (B : PubLines { par.P with tokv := L.tokv a.1 } par.g hS pcl QF.planF.fullF.D
      QF.planF.fullF.tb s lk s0 tl)
    (K : LookLines { par.P with tokv := L.tokv a.1 } fo s0)
    (Rp : ∀ (rt : Array E) (lam : ℕ), lam < par.P.y.Lam →
      RopeFits Reading.gl
        { v := o.v, wsLay := par.P.wsLay, rope := par.P.rope, rs := o.K.rs, rt := rt }
        QF.planF.fullF.D QF.planF.fullF.tb (par.g * par.P.y.Lam) lam)
    (lw : ℕ → LW Cb.Gl.E) (hz0 : QF.planF.fullF.zOf z.1 = zAt fo)
    (hk0 : QF.planF.fullF.kTg z.1 = kTgAt fo (L.fork a.1))
    (hfil : Fo.FilledA (L.fork a.1) fo.cEnd) (Mt : Mats Cb.Gl.E)
    (hR : ∀ (X : Rows.Pub34 Cb.Gl.E) (G2 : Fork) (t4 : Tape),
      PubAt X { par.P with tokv := L.tokv a.1 } par.hp fo o G2 t4 QF.planF.fullF.D
        QF.planF.fullF.tb hS →
      ∀ Fl, Fo.Later G Fl → X.ReadsTrue (Fl.worldOf gl (Sm.mask w) (Sm.entryT o w)) Mt)
    (hcells : cellsOf QF.planF.fullF.D (cellsAt par.P.y Mt) =
      QF.planF.fullF.rd (QF.planF.fullF.msg (part w)))
    (V : Plan4L.ValueIs QF.toPlan4L par hS) (V2 : Plan4LF.ValueMoreF QF)
    (h0 : QF.n0 = (L.fork a.1).next) (hSm : Sm.mask w = QF.planF.maskAt (part w)) :
    Blocks.Form.val (QF.planF.yKF par hS (ztSF QF.planF.fullF)
        (Plan4F.eKF A (numsKF QF.planF.fullF) Ex hds z τ) (part w))
      (embClaim (lateF (roomKF QF.planF par hS)) Sum.inr
        (((tailW QF.planF.fullF).y7 (Plan4F.eKF A (numsKF QF.planF.fullF) Ex hds z τ)).1.2
          (0 : Fin 1))
        QF.planF.fullF.mkE QF.planF.fullF.nb QF.planF.fullF.gB
        (stF QF.planF.fullF (Plan4F.eKF A (numsKF QF.planF.fullF) Ex hds z τ)).pb) = 0 := by
  obtain ⟨hinv, hscl, hvy, _, _, _⟩ :=
    Plan4LF.heard_KF A Y.hears hF (small_of_all _ _ _ Y.small) V.scl V.L0
  obtain ⟨H1, hd2, tT, F4, F7, F8, G1, G1', G2, G3, G3', G4, G5, u5', g7, Ld, I, hc⟩ :=
    Plan4F.atYesF A (numsKF QF.planF.fullF) L hds a τ Y z.1 hF B.S B.hs B.hg B.hrd B.hmats
      B.hρ B.hc B.hN B.hfl K.hsx K.hsy K.hzk K.he B.hs0 K.hpt B.Zw B.hsL B.hlw B.h4 Rp B.htm B.hNM
      B.hpad hinv hscl hvy (A.lamM (L.tokv a.1)) gl_half
      (nums4_num4K QF.planF.fullF.toFullPar) lw hz0 hk0 hfil
  obtain ⟨Xp, PX, _, _⟩ := pubAtMore_of_ledF Y.hears Ld B K Rp hinv
  obtain ⟨_, ⟨fs₁, F₁, _, _, h1, _, z1, _⟩, _⟩ :=
    forms_of_behind L Sm Lt par pc a τ o G w hL hB
  have l1 : Fo.Later G F₁ := later_fo (formsFrontWith_later h1)
  have he : Plan4F.eKF A (numsKF QF.planF.fullF) Ex hds z τ = _ :=
    Plan4F.val_of_claimsF A (numsKF QF.planF.fullF) Ex (L.tokv a.1) hds τ z _ hc
  have Sz := sevenSizesF_K A (L.tokv a.1)
  obtain ⟨_, _, _, _, _, _, mE⟩ := Plan4LF.hm_ofF A hF Y.hears Ld (A.lamM (L.tokv a.1)) (part w)
    (Sm.mask w) ⟨h0, V.nT, V.nI, V2.numI, fun n _ => (congrFun hSm n).symm, V.room⟩
  have hB' : par.P.y.h.d / par.P.y.S2 = hS.d / par.P.y.S2 := Sz.hB
  have e2 : QF.planF.fullF.D.d = QF.planF.fullF.nb * 2 ^ par.P.y.ls := by
    have q := QF.planF.hd
    rw [A.hls] at q
    exact q
  have hnb : par.P.y.h.d / par.P.y.S2 = QF.planF.fullF.nb :=
    hB'.trans (Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos _) (Sz.nd.symm.trans e2))
  have eg : par.g = 0 := beq_iff_eq.mp A.hg
  have h1' : formsFrontWith false par.P par.g o G = some (fs₁, F₁) := h1
  rw [eg] at h1'
  have As : EmbAsks QF.planF.fullF Xp (F₁.worldOf gl (Sm.mask w) (Sm.entryT o w)) o
      (Plan4F.eKF A (numsKF QF.planF.fullF) Ex hds z τ) (part w) := by
    rw [he]
    exact embAsks_at_ptsT QF.planF.fullF (Plan4F.tailMKF A (numsKF QF.planF.fullF)) Xp Ld A.hg
      Y.hears (tb3_eq _ A.hg) _ _ z.1 (Ld.g5.trans l1) (Sm.mask w) (Sm.entryT o w) (part w)
      PX.ρ PX.H Sz.Z.2.2.2.2.1 hnb A.hls.symm A.hB.symm Sz.s2 mE
  have hsX : scl = sclOf Xp.h Xp.p.v.sc Xp.p.v.g Xp.p.v.y.Lam := by rw [PX.h, PX.v]; exact hscl
  have hcX : cellsOf QF.planF.fullF.D (cellsAt Xp.p.v.y Mt) =
      QF.planF.fullF.rd (QF.planF.fullF.msg (part w)) := by rw [PX.v, hvy]; exact hcells
  have hzX : ∀ f ∈ fs₁.toList, f.value Xp.ρ (F₁.worldOf gl (Sm.mask w) (Sm.entryT o w)) = 0 :=
    fun f hf => by rw [PX.ρ]; exact (z1 f hf).2
  exact uE_of_front QF.planF.fullF (ztSF QF.planF.fullF) (par.P.y.lPd - par.P.y.ls)
    (hS.d / par.P.y.S2) par.P.y.ls (Plan4F.eKF A (numsKF QF.planF.fullF) Ex hds z τ)
    (part w) Xp (F₁.worldOf gl (Sm.mask w) (Sm.entryT o w)) Mt (hR Xp _ _ PX F₁ l1) hsX PX.v.symm
    (PX.hd2.trans Ld.eHd2) PX.D hcX As h1' hzX

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.Plan4LF.emb_at
