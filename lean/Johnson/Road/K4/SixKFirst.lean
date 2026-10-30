-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/SixKFirst.lean: AT A HEARING OF K4's TEXT IN THE FIRST GROUP, AT THE FIRST GROUP's
VALUE WITH ITS SLOTS AND ORDERS LAID (`Plan4LF.planF`, ValueSlotsFirst.lean): THE FIVE OWN ROWS AND
THE PART merge OF THE LIBRARY's LEDGER, FROM THE TWO RUNS' ZEROS. The twin of
Johnson/Road/K4/SixK.lean. Two definitions and one theorem. Glue, and long: `six_of_ledF`
(SixLedFirst.lean) with its premises on weights, masks, incoming forms and the batched sumcheck's
end concluded: `outTies_KF`, `outs_of_ledF`, `fitsAt1F` … `fitsAt6F`, `fits4F`, `fits7F`,
`Plan4LF.hm_ofF`, `Plan4LF.hwTiesF_slots`, `Plan4LF.firsts_KF`, `Plan4LF.hkI_ofF`, `hincH1F` …
`hincO7F`, `ho_of_ledF`, `d2_fourF`, `trueAt_pub`, `d4_of_pubF`; three of its six conclusions speak
of the stages' outputs, and are carried to the last statement's parts by `o1_z7`, `o5_z7`, `o6_z7`
(OnBytes/Desc/First/P1/TailParts.lean). No draw, no count.

  `RowsSayF P e mm w`: the five own rows u1At, u2At, prodU (twice), upForm of the outputs in the
    last statement e are worth 0 at Sum.elim (P.msg mm) w, and the first group's part merge
    (`mergeLedF`, Cb/Pv/Lay/End/MergeShare.lean) holds there.
  `Plan4LF.wKF`: the ties between the typed tail and K4's written rounds, at the numbering `numsKF`.
  `Plan4LF.six_ledF`: `RowsSayF` at the last statement that the tape's data make.

What is other than in a later group. `LedG`, `TgRecF` and the tail's tape t0.drop (k0 g); the first
statement x bears three points, and zOf, kTg, kIncS are read at its first part; the merge's start
form names one slot more, the embedding's, whose mask entry is concluded (the seventh tie of
`hm_ofF`); the merge's own slots begin one slot later, so room7F asks one slot more than room7.

Limits. K04_law IS NOT PROVED BY THIS. PREMISES THAT STAY: `MeetsF` · the hearing's return, `LedG`,
`TgRecF`, the fourth claimed sum · the ledger in front has arrays of the right sizes · the token
point, zOf, kTg, kIncS at the first statement; the lookup's end form: filled slots alone, no entry,
slots below ns + 1 · a public record X with `PubAt`, its reads' numbers and its panels' environment
· o.v.y is the plan's; the table of scales; the inverse of the terms' coefficient · `MaskLetters` at
the letters that the value shares with a later group's, room for the merge's slots, the numbering of
the weight claims is `numK`'s · matrices Mt whose reads are true in the worlds of the two ledgers
behind the runs, and whose cells are the message's · the two runs' returns and their forms' zeros.
Nothing on the embedding's own claim, on the two further points, on tok. Nothing shows that these
can be met together.
-/
import Johnson.Road.K4.SixLedFirst
import Johnson.Road.K4.StackRowPubFirst
import Johnson.Road.K4.TrueAtPub
import Johnson.Road.K4.StageOutsAllFirst
import Johnson.Road.K4.StageFitsAtFirst
import Johnson.Road.K4.StageFitsRestFirst
import Johnson.Road.K4.OutTiesKFirst
import Johnson.Road.K4.SevenPaidFirst
import Johnson.Road.K4.NumTiesKFirst
import Johnson.Road.K4.IncsOutFirst
import Johnson.Road.K4.Inc4HeardFirst
import Johnson.Road.K4.KtLedFirst
import Johnson.Road.K4.MaskTiesHFirst
import Johnson.Road.K4.CloseKitFirst
import Johnson.Road.K4.CloseValFirst
import Johnson.Road.K4.Claim4FullFirst
import Johnson.Road.K4.ClaimsPaid
import OnBytes.Desc.First.K4.HearGrows
import OnBytes.Desc.First.P1.TailParts

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Iop Cb TWhole Cb.Pv.Lay Cb.Pv.Att Cb.Pv.Lay.At Cb.Pv.Lay.End Cb.Pv.Lay.End.Gated
open OnBytes OnBytes.K.Kc OnBytes.Desc.First.K4
open OnBytes.Model (Reading Fork Forest.Heard Level Tsc Aff)
open OnBytes.Model.Layer (Pub HPlan2 Own Heard nEndT stubO)
open OnBytes.Desc.First.P1 (gl NzT TailM Tg7 addsOf drawnOf tailT tailIsF_at o1_z7 o5_z7 o6_z7)
open Inst.Model (Scl)
open Inst.Model.FFSeg (LW zpos)

/-- **The five own rows are worth 0 and the first group's part merge holds**, at a last statement
e. -/
def RowsSayF [scl : Scl] {M Xs : Type} (P : FullFPar Cb.Gl.E M Xs) {J₂ : Type} [Fintype J₂]
    (e : (tailW P).s7.Nx) (mm : M) (w : J₂ → Cb.Gl.E) : Prop :=
  Blocks.Form.val (Sum.elim (P.msg mm) w) (u1At (J₂ := J₂) P.ofp.nr ((tailW P).b1 e).2) = 0 ∧
    Blocks.Form.val (Sum.elim (P.msg mm) w) (u2At (J₂ := J₂) P.ofp.nr ((tailW P).b2 e).2) = 0 ∧
    Blocks.Form.val (Sum.elim (P.msg mm) w) (prodU (J₂ := J₂) P.fp.gp ((tailW P).b5 e).2) = 0 ∧
    Blocks.Form.val (Sum.elim (P.msg mm) w) (prodU (J₂ := J₂) P.fp.rt.L ((tailW P).b6 e).2) = 0 ∧
    Blocks.Form.val (Sum.elim (P.msg mm) w)
      (upForm (J₂ := J₂) (Cb.Sub.formU P.ip.inn.toSum.T.par (fun _ b _ _ => PEmpty.elim b)
        ((tailW P).b4 e).2)) = 0 ∧
    TWhole.Ledger.Holds (mergeLedF (J₂ := J₂) P.wp0 (tenEF P) (rhsF P) P.mkE e.2)
      (Sum.elim (P.msg mm) w)

variable [scl : Scl] {Mm X : Type} {QF : Plan4LF Cb.Gl.E Mm X} {par : Par}
  {hS : OnBytes.Model.Layer.Shape} {pcl : List (List String)}

/-- The ties between the first group's typed tail and K4's written rounds, at the numbering
`numsKF`. -/
noncomputable abbrev Plan4LF.wKF (A : QF.planF.MeetsF par hS pcl) :
    TailM QF.planF.fullF.ownF.toOwn.tail (tailR (numsOf par.P par.hp par.g)) :=
  Plan4F.tailMKF A (numsKF QF.planF.fullF)

/-- **The five own rows and merge, at a hearing in the first group, from the two runs' zeros**,
under the premises that the head lists. -/
theorem Plan4LF.six_ledF (A : QF.planF.MeetsF par hS pcl) (tk : Array Nat) {fo : Forest.Heard}
    {o : Own} {F G : Fork} {t0 u : Tape} {H1 : Heard} {hd2 : Level} {tT : Tsc}
    {F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 : Fork} {u5 : Tape} (hF : PscRun.Sized F)
    (h : hear engFl { par.P with tokv := tk } par.hp par.g fo F t0 = some (o, G, u))
    (Ld : LedG { par.P with tokv := tk } par.hp par.g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2
      G3 G3' G4 G5 u5)
    (nz : NzT QF.planF.fullF.ownF.toOwn.tail (ksOf { par.P with tokv := tk } par.hp)
      (t0.drop (k0 par.g)))
    (x : QF.planF.fullF.ofp.fs.X3) (g7 : Tg7)
    (T : TgRecF g7 { par.P with tokv := tk } par.hp par.g o t0 H1 tT F4 G2 G3 G3')
    (hc4 : (tailT (Plan4LF.wKF A) (ksOf { par.P with tokv := tk } par.hp) (t0.drop (k0 par.g)) nz
        (addsOf (Plan4LF.wKF A) (ksOf { par.P with tokv := tk } par.hp) (t0.drop (k0 par.g)) nz x
          g7)).d4.Claim
      ((tailT (Plan4LF.wKF A) (ksOf { par.P with tokv := tk } par.hp) (t0.drop (k0 par.g)) nz
        (addsOf (Plan4LF.wKF A) (ksOf { par.P with tokv := tk } par.hp) (t0.drop (k0 par.g)) nz x
          g7)).y4 x))
    (hx : ∀ j : Fin QF.planF.fullF.D.lT,
      QF.planF.fullF.ofp.fs.pvF x j = gl.val ((drawnOf t0).getD j.val zeroE))
    (hz0 : QF.planF.fullF.zOf (QF.planF.fullF.ofp.fs.x0F x) = zAt fo)
    (hk0 : QF.planF.fullF.kTg (QF.planF.fullF.ofp.fs.x0F x) = kTgAt fo F)
    (hkS : ∀ s, QF.planF.kIncS (QF.planF.fullF.ofp.fs.x0F x) s = kIncAt fo F s)
    (hfil : Fo.FilledA F fo.cEnd)
    (he : fo.cEnd.ents = #[]) (hsl : ∀ y ∈ fo.cEnd.slots.toList, y.1 < QF.ns + 1)
    (Xp : Rows.Pub34 Cb.Gl.E)
    (PX : PubAt Xp { par.P with tokv := tk } par.hp fo o G2
      ((ksOf { par.P with tokv := tk } par.hp).tc4 (t0.drop (k0 par.g))) QF.planF.fullF.D
      QF.planF.fullF.tb hS)
    (Xrd : Xp.rd = par.P.rd)
    (Xe : Xp.p = { v := o.v, e := o.H.fo.e, shownT := Xp.p.shownT, zt := o.H.ztF,
                   stubO := stubO par.P.y })
    (hvy : o.v.y = par.P.y) (hscl : scl = sclOf hS o.v.sc o.v.g o.v.y.Lam)
    (hinv : ∀ tT, o.H.tT = some tT →
      Reading.gl.val (negE (invE tT.p.eps)) * Reading.gl.val tT.p.eps = -1)
    (lw : ℕ → LW Cb.Gl.E) (mm : Mm) (mask : ℕ → Cb.Gl.E) (entry : ℕ → ℕ → ℕ → Cb.Gl.E)
    (Lm : MaskLetters QF.toPlan4L mm mask F.next (nEndT par.P.y)
      (2 + (1 + par.P.y.LamM) + (par.hp.NCL - (if (par.g == 0) = true then 1 else 0))))
    (room7F : QF.toPlan4L.slots.f7 + 1 + 1 + (2 * QF.planF.kW + 1) ≤ QF.ns)
    (hn4 : ∀ q, num4 QF.planF.fullF.D QF.planF.fullF.num q =
      num4 QF.planF.fullF.D (numK QF.planF.fullF.D) q)
    (Ex : ExtSpec) (y : Ex.Str) {fs₁ fs₂ : Array Aff} {F₁ F₂ : Fork}
    (h1 : formsFrontWith false { par.P with tokv := tk } par.g o G = some (fs₁, F₁))
    (h2 : formsBack o F₁ = some (fs₂, F₂))
    (z1 : ∀ q ∈ fs₁.toList, q.value gl (F₁.worldOf gl mask entry) = 0)
    (z2 : ∀ q ∈ fs₂.toList, q.value gl (F₂.worldOf gl mask entry) = 0) (Mt : Mats Cb.Gl.E)
    (hR1 : Xp.ReadsTrue (F₁.worldOf gl mask entry) Mt)
    (hR2 : Xp.ReadsTrue (F₂.worldOf gl mask entry) Mt)
    (hcells : cellsOf QF.planF.fullF.D (cellsAt par.P.y Mt) =
      QF.planF.fullF.rd (QF.planF.fullF.msg mm))
    {J₂ : Type} [Fintype J₂] (w : J₂ → Cb.Gl.E) :
    RowsSayF QF.planF.fullF
      ((tailT (Plan4LF.wKF A) (ksOf { par.P with tokv := tk } par.hp) (t0.drop (k0 par.g)) nz
        (addsOf (Plan4LF.wKF A) (ksOf { par.P with tokv := tk } par.hp) (t0.drop (k0 par.g)) nz x
          g7)).z7 x) mm w := by
  have OT := outTies_KF A tk Ld.c4
  have Sz := sevenSizesF_K A tk
  have Nm := numTiesF_K QF.planF.fullF (tailIsF_at QF.planF.fullF
    (OnBytes.Model.Verify.layerNumbers par.P par.hp par.g) A.dimIs A.wk A.hg) A.written.2.2.2.2
    (A.lamM tk)
  have ok := Plan4F.tailMKF_ok A (numsKF QF.planF.fullF)
  have hS0 : PscRun.Sized G :=
    (hearFl_later (P := { par.P with tokv := tk }) (hp := par.hp) (g := par.g) (fo := fo)
      h).sized hF
  obtain ⟨l1, l12, _, _⟩ := runs_later hS0 h1 h2
  have l2 : Fo.Later G F₂ := l1.trans l12
  have hzp : ∀ j, j < QF.planF.fullF.D.lT →
      zpos QF.planF.fullF.D (zAt fo) j = gl.val (H1.ztF.getD j zeroE) := by
    intro j hj
    have q := zpos_pub Xp (by rw [PX.D, PX.v, hvy]; exact OT.lt) j (by rw [PX.D]; exact hj)
    rw [PX.D, PX.H, PX.fo, Ld.ztF] at q
    exact q
  obtain ⟨_, _, O3, O4, _, _, _⟩ := outs_of_ledF QF.planF.fullF (Plan4LF.wKF A) Ld OT nz x
    g7 T hx hz0 hzp
  obtain ⟨m1, m2, m3, m5, m6, m7, mE⟩ := Plan4LF.hm_ofF A hF h Ld (A.lamM tk) mm mask Lm
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, _⟩ := Plan4LF.firsts_KF A rfl hF h Ld Lm.n0 Lm.nT Lm.nI
  have Hw0 := Plan4LF.hwTiesF_slots mm mask Lm room7F
  have hsX : scl = sclOf Xp.h Xp.p.v.sc Xp.p.v.g Xp.p.v.y.Lam := by rw [PX.h, PX.v]; exact hscl
  have eT : Xp.tT = { tT with p := { tT.p with rowMade := true } } :=
    Option.some.inj (PX.tT.symm.trans Ld.kTT)
  have f3 := fitsAt3F QF.planF.fullF (Plan4LF.wKF A) Ld OT.lt nz x g7 hz0 hzp
  have ho := ho_of_ledF QF.planF.fullF (Plan4LF.wKF A) Ld nz x g7 T.t3 ok f3 Ex y l2 mask
    entry (QF.planF.fullF.msg mm) (by rw [e3]; exact Hw0.hw3)
    (hincH3F (Plan4LF.wKF A) Ld nz x g7 F₂ l2 mask entry (QF.planF.fullF.msg mm) m3)
    (hinv { tT with p := { tT.p with rowMade := true } } Ld.kTT)
  have T4 := trueAt_pub Xp (F₂.worldOf gl mask entry) Mt hR2
  rw [PX.ρ] at T4
  have d4 := d2_fourF QF.planF.fullF (Plan4LF.wKF A) Ld Xp PX.ρ PX.H PX.fo hsX PX.D PX.tb
    PX.alpha PX.theta PX.tT PX.om PX.st lw nz x g7 T.t4 O3 hz0 hk0 hfil F₂ l2 mask entry
    (QF.planF.fullF.msg mm) (cellsAt Xp.p.v.y Mt) T4 (by rw [PX.v, hvy]; exact hcells)
    (QF.ns + 1) he hsl (Plan4LF.hkI_ofF (QF.planF.fullF.ofp.fs.x0F x) mm mask Lm hkS) m3 ho
  have hD4 := d4_of_pubF QF.planF.fullF (Plan4LF.wKF A) Ld nz
    (addsOf (Plan4LF.wKF A) (ksOf { par.P with tokv := tk } par.hp) (t0.drop (k0 par.g))
      nz x g7) x hc4 O3 O4 Sz.k3 Sz.k4 Nm.n3 hn4 hvy Sz.hNN Sz.hLM Sz.hNE Sz.hEnd Xp PX.ρ Xe PX.H
    Xrd (by have q := PX.sh; rw [eT] at q; exact q) PX.D hsX (by rw [PX.fo]; exact hz0)
    (by rw [PX.fo]; exact hz0) (F₁.worldOf gl mask entry) Mt hR1
  have f1 := fitsAt1F QF.planF.fullF Ld OT.eS OT.m1 OT.lI OT.lP OT.half x
    (fun j => by rw [pv_drawnF Ld]; exact hx j)
  have f2 := fitsAt2F QF.planF.fullF (Plan4LF.wKF A) Ld OT.lt nz x g7 hx
  have f5 := fitsAt5F QF.planF.fullF (Plan4LF.wKF A) Ld OT.n5 OT.e5 OT.m5 OT.k4 OT.wD OT.le5 OT.rs
    nz x g7 O4 hz0 (fun j hj => by rw [Ld.ztF]; exact hzp j hj)
  have f6 := fitsAt6F QF.planF.fullF (Plan4LF.wKF A) Ld OT.n6 OT.e6 OT.m6 OT.k4 OT.lt OT.lfe OT.le6
    OT.rs OT.ll nz x g7 O3 O4
  have i1 := hincH1F (V := QF.planF.fullF) Ld x F₁ l1 mask entry (QF.planF.fullF.msg mm) hF
    (A.dimIsT tk) gl_half m1
  have i2 := hincH2F (Plan4LF.wKF A) Ld nz x g7 F₁ l1 mask entry (QF.planF.fullF.msg mm) m2
  have i5 := hincO5F (Plan4LF.wKF A) Ld nz x g7 F₁ l1 mask entry (QF.planF.fullF.msg mm) O4 m5
  have i6 := hincO6F (Plan4LF.wKF A) Ld nz x g7 F₁ l1 mask entry (QF.planF.fullF.msg mm) O4
    (A.dimIsT tk) (A.lamM tk) m6
  have i7 := hincO7F (Plan4LF.wKF A) Ld nz x g7 F₂ l2 mask entry (QF.planF.fullF.msg mm) O4
    (A.dimIsT tk) A.hg m7 mE
  rw [← e1, ← e2, ← e3, ← e4, ← e5, ← e6, ← e7] at Hw0
  obtain ⟨r1, r2, r5, r6, r4, rM⟩ := six_of_ledF (J₂ := J₂) QF.planF.fullF (Plan4LF.wKF A) Ld nz x
    g7 T ok Nm rfl f1 f2 (fits4F QF.planF.fullF _ par.hp.lamS OT.k4) f5 f6
    (fits7F QF.planF.fullF _ _ OT.k7) Sz.Z.2.2.2.2.2.2 Sz.hNP Sz.hNO rfl hD4 Ex y
    (Fo.Later.refl G) hS0 h1 h2 mask entry z1 z2 mm Hw0 ⟨i1, i2, d4, i5, i6, i7⟩ w
  have q1 := o1_z7 (tailW QF.planF.fullF)
    (tailT (Plan4LF.wKF A) (ksOf { par.P with tokv := tk } par.hp) (t0.drop (k0 par.g)) nz
      (addsOf (Plan4LF.wKF A) (ksOf { par.P with tokv := tk } par.hp) (t0.drop (k0 par.g)) nz x
        g7)) x
  have q5 := o5_z7 (tailW QF.planF.fullF)
    (tailT (Plan4LF.wKF A) (ksOf { par.P with tokv := tk } par.hp) (t0.drop (k0 par.g)) nz
      (addsOf (Plan4LF.wKF A) (ksOf { par.P with tokv := tk } par.hp) (t0.drop (k0 par.g)) nz x
        g7)) x
  have q6 := o6_z7 (tailW QF.planF.fullF)
    (tailT (Plan4LF.wKF A) (ksOf { par.P with tokv := tk } par.hp) (t0.drop (k0 par.g)) nz
      (addsOf (Plan4LF.wKF A) (ksOf { par.P with tokv := tk } par.hp) (t0.drop (k0 par.g)) nz x
        g7)) x
  unfold RowsSayF
  refine ⟨?_, r2, ?_, ?_, r4, rM⟩
  · refine (congrArg (fun z => Blocks.Form.val (Sum.elim (QF.planF.fullF.msg mm) w)
      (u1At (J₂ := J₂) QF.planF.fullF.ofp.nr z) = 0) q1).mpr ?_
    exact r1
  · refine (congrArg (fun z => Blocks.Form.val (Sum.elim (QF.planF.fullF.msg mm) w)
      (prodU (J₂ := J₂) QF.planF.fullF.fp.gp z) = 0) q5).mpr ?_
    exact r5
  · refine (congrArg (fun z => Blocks.Form.val (Sum.elim (QF.planF.fullF.msg mm) w)
      (prodU (J₂ := J₂) QF.planF.fullF.fp.rt.L z) = 0) q6).mpr ?_
    exact r6

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.Plan4LF.six_ledF
