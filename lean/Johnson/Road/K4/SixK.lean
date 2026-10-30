-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/SixK.lean: AT A HEARING OF K4's TEXT IN A GROUP THAT IS NOT THE FIRST, AT THE VALUE
WITH ITS SLOTS AND ORDERS LAID (`Plan4L`): THE FIVE OWN ROWS AND THE PART merge OF THE LIBRARY's
LEDGER, FROM THE TWO RUNS' ZEROS. Two definitions and one theorem. Glue, and long: `six_of_led`
(SixLed.lean) with its premises on weights, masks, incoming forms and the batched sumcheck's end
concluded: `outTies_K`, `outs_of_led`, `fitsAt1` … `fitsAt6`, `Plan4L.hm_of`, `Plan4L.hwTies_slots`,
`Plan4L.firsts_K`, `hincH1` … `hincO7`, `ho_of_led`, `d2_four`, `trueAt_pub`, `d4_of_pub`. No draw,
no count.

  `RowsSay P e mm w`: the five own rows u1At, u2At, prodU (twice), upForm of the outputs in the last
  statement e are worth 0 at Sum.elim (P.msg mm) w, and the part merge holds there.
  `Plan4L.six_led`: `RowsSay` at the last statement that the tape's data make.

Limits. PREMISES THAT STAY: `Meets` · the hearing's return, `Led7`, `TgRec`, the fourth claimed sum
· the ledger in front has arrays of the right sizes · the token point, zOf, kTg, kIncS at the first
statement; the lookup's end form: filled slots alone, no entry, slots below ns + 1 · a public record
X with `PubAt`, its reads' numbers and its panels' environment · o.v.y is the plan's; the table of
scales; the inverse of the terms' coefficient · `MaskLetters`, room for the merge's slots, the
numbering of the weight claims is `numK`'s · matrices Mt whose reads are true in the worlds of the
two ledgers behind the runs, and whose cells are the message's · the two runs' returns and their
forms' zeros. Nothing shows that these can be met together.
-/
import Johnson.Road.K4.SixLed
import Johnson.Road.K4.StackRowPub
import Johnson.Road.K4.TrueAtPub
import Johnson.Road.K4.StageOutsAll
import Johnson.Road.K4.StageFitsAt
import Johnson.Road.K4.OutTiesK
import Johnson.Road.K4.MeetsCovers
import Johnson.Road.K4.NumTiesK
import Johnson.Road.K4.IncsOut
import Johnson.Road.K4.Inc4Heard
import Johnson.Road.K4.PubAtMore
import Johnson.Road.K4.KIncTie
import Johnson.Road.K4.CloseVal
import Johnson.Road.K4.Claim4Full
import OnBytes.Desc.First.K4.HearGrows

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Iop Cb TWhole Cb.Pv.Lay Cb.Pv.Att Cb.Pv.Lay.At Cb.Pv.Lay.End Cb.Pv.Lay.End.Gated
open OnBytes OnBytes.K.Kc OnBytes.Desc.First.K4
open OnBytes.Model (Reading Fork Forest.Heard Level Tsc Aff)
open OnBytes.Model.Layer (Pub HPlan2 Own Heard nEndT stubO)
open OnBytes.Desc.First.P1 (gl NzT TailM Tg7 addsOf drawnOf tailIs_at)
open Inst.Model (Scl)
open Inst.Model.FFSeg (LW zpos)

/-- **The five own rows are worth 0 and the part merge holds**, at a last statement e. -/
def RowsSay [scl : Scl] {M Xs : Type} (P : FullPar Cb.Gl.E M Xs) {J₂ : Type} [Fintype J₂]
    (e : (tailF P).s7.Nx) (mm : M) (w : J₂ → Cb.Gl.E) : Prop :=
  Blocks.Form.val (Sum.elim (P.msg mm) w) (u1At (J₂ := J₂) P.nr ((tailF P).b1 e).2) = 0 ∧
    Blocks.Form.val (Sum.elim (P.msg mm) w) (u2At (J₂ := J₂) P.nr ((tailF P).b2 e).2) = 0 ∧
    Blocks.Form.val (Sum.elim (P.msg mm) w) (prodU (J₂ := J₂) P.fp.gp ((tailF P).b5 e).2) = 0 ∧
    Blocks.Form.val (Sum.elim (P.msg mm) w) (prodU (J₂ := J₂) P.fp.rt.L ((tailF P).b6 e).2) = 0 ∧
    Blocks.Form.val (Sum.elim (P.msg mm) w)
      (upForm (J₂ := J₂) (Cb.Sub.formU P.ip.inn.toSum.T.par (fun _ b _ _ => PEmpty.elim b)
        ((tailF P).b4 e).2)) = 0 ∧
    TWhole.Ledger.Holds (mergeLed (J₂ := J₂) P.wp0 e.2) (Sum.elim (P.msg mm) w)

variable [scl : Scl] {Mm X : Type} {QL : Plan4L Cb.Gl.E Mm X} {par : Par}
  {hS : OnBytes.Model.Layer.Shape} {pcl : List (List String)}

/-- The ties between the typed tail and K4's written rounds, at the numbering `numsK`. -/
noncomputable abbrev Plan4L.wK (A : QL.plan.Meets par hS pcl) :
    TailM QL.plan.full.own.toOwn.tail (tailR (numsOf par.P par.hp par.g)) :=
  Plan4.tailMK A (numsK QL.plan.full)

/-- **The five own rows and merge, at a hearing, from the two runs' zeros.** -/
theorem Plan4L.six_led (A : QL.plan.Meets par hS pcl) (tk : Array Nat) {fo : Forest.Heard}
    {o : Own} {F G : Fork} {t0 u : Tape} {H1 : Heard} {hd2 : Level} {tT : Tsc}
    {F4 F7 F8 G1 G1' G2 G3 G3' G4 : Fork} (hF : PscRun.Sized F)
    (h : hear engFl { par.P with tokv := tk } par.hp par.g fo F t0 = some (o, G, u))
    (Ld : Led7 { par.P with tokv := tk } par.hp par.g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2
      G3 G3' G4)
    (nz : NzT QL.plan.full.own.toOwn.tail (ksOf { par.P with tokv := tk } par.hp) (t0.drop 1))
    (x : X × (Fin QL.plan.full.own.toOwn.gT → Cb.Gl.E)) (g7 : Tg7)
    (T : TgRec g7 { par.P with tokv := tk } par.hp o t0 H1 tT F4 G2 G3 G3')
    (hc4 : (k4Tail (Plan4L.wK A) { par.P with tokv := tk } par.hp t0 nz
        (addsOf (Plan4L.wK A) (ksOf { par.P with tokv := tk } par.hp)
          (t0.drop 1) nz x g7)).d4.Claim
      ((k4Tail (Plan4L.wK A) { par.P with tokv := tk } par.hp t0 nz
        (addsOf (Plan4L.wK A) (ksOf { par.P with tokv := tk } par.hp)
          (t0.drop 1) nz x g7)).y4 x))
    (hx : ∀ j : Fin QL.plan.full.own.toOwn.gT, x.2 j = gl.val ((drawnOf t0).getD j.val zeroE))
    (hz0 : QL.plan.full.zOf x.1 = zAt fo) (hk0 : QL.plan.full.kTg x.1 = kTgAt fo F)
    (hkS : ∀ s, QL.plan.kIncS x.1 s = kIncAt fo F s) (hfil : Fo.FilledA F fo.cEnd)
    (he : fo.cEnd.ents = #[]) (hsl : ∀ y ∈ fo.cEnd.slots.toList, y.1 < QL.ns + 1)
    (Xp : Rows.Pub34 Cb.Gl.E)
    (PX : PubAt Xp { par.P with tokv := tk } par.hp fo o G2
      ((ksOf { par.P with tokv := tk } par.hp).tc4 (t0.drop 1)) QL.plan.full.D QL.plan.full.tb hS)
    (Xrd : Xp.rd = par.P.rd)
    (Xe : Xp.p = { v := o.v, e := o.H.fo.e, shownT := Xp.p.shownT, zt := o.H.ztF,
                   stubO := stubO par.P.y })
    (hvy : o.v.y = par.P.y) (hscl : scl = sclOf hS o.v.sc o.v.g o.v.y.Lam)
    (hinv : ∀ tT, o.H.tT = some tT →
      Reading.gl.val (negE (invE tT.p.eps)) * Reading.gl.val tT.p.eps = -1)
    (lw : ℕ → LW Cb.Gl.E) (mm : Mm) (mask : ℕ → Cb.Gl.E) (entry : ℕ → ℕ → ℕ → Cb.Gl.E)
    (Lm : MaskLetters QL mm mask F.next (nEndT par.P.y)
      (2 + (1 + par.P.y.LamM) + (par.hp.NCL - (if (par.g == 0) = true then 1 else 0))))
    (room7 : QL.slots.f7 + 1 + (2 * QL.plan.kW + 1) ≤ QL.ns)
    (hn4 : ∀ q, num4 QL.plan.full.D QL.plan.full.num q = num4 QL.plan.full.D (numK QL.plan.full.D)
      q)
    (Ex : ExtSpec) (y : Ex.Str) {fs₁ fs₂ : Array Aff} {F₁ F₂ : Fork}
    (h1 : formsFrontWith false { par.P with tokv := tk } par.g o G = some (fs₁, F₁))
    (h2 : formsBack o F₁ = some (fs₂, F₂))
    (z1 : ∀ q ∈ fs₁.toList, q.value gl (F₁.worldOf gl mask entry) = 0)
    (z2 : ∀ q ∈ fs₂.toList, q.value gl (F₂.worldOf gl mask entry) = 0) (Mt : Mats Cb.Gl.E)
    (hR1 : Xp.ReadsTrue (F₁.worldOf gl mask entry) Mt)
    (hR2 : Xp.ReadsTrue (F₂.worldOf gl mask entry) Mt)
    (hcells : cellsOf QL.plan.full.D (cellsAt par.P.y Mt) = QL.plan.full.rd (QL.plan.full.msg mm))
    {J₂ : Type} [Fintype J₂] (w : J₂ → Cb.Gl.E) :
    RowsSay QL.plan.full
      ((k4Tail (Plan4L.wK A) { par.P with tokv := tk } par.hp t0 nz
        (addsOf (Plan4L.wK A) (ksOf { par.P with tokv := tk } par.hp)
          (t0.drop 1) nz x g7)).z7 x) mm w := by
  have OT := outTies_K A tk Ld.c4
  have Sz := sevenSizes_of_meets A tk
  have Nm := numTies_K QL.plan.full (tailIs_at QL.plan.full
    (OnBytes.Model.Verify.layerNumbers par.P par.hp par.g) A.dimIs A.wk A.hg) A.written.2.2
    (A.lamM tk)
  have ok := Plan4.tailMK_ok A (numsK QL.plan.full)
  have hS0 : PscRun.Sized G :=
    (hearFl_later (P := { par.P with tokv := tk }) (hp := par.hp) (g := par.g) (fo := fo)
      h).sized hF
  obtain ⟨l1, l12, _, _⟩ := runs_later hS0 h1 h2
  have l2 : Fo.Later G F₂ := l1.trans l12
  have hzp : ∀ j, j < QL.plan.full.D.lT →
      zpos QL.plan.full.D (zAt fo) j = gl.val (H1.ztF.getD j zeroE) := by
    intro j hj
    have q := zpos_pub Xp (by rw [PX.D, PX.v, hvy]; exact OT.lt) j (by rw [PX.D]; exact hj)
    rw [PX.D, PX.H, PX.fo, Ld.ztF] at q
    exact q
  obtain ⟨_, _, O3, O4, _, _, _⟩ := outs_of_led QL.plan.full (Plan4L.wK A) Ld OT nz x
    g7 T hx hz0 hzp
  obtain ⟨m1, m2, m3, m5, m6, m7⟩ := Plan4L.hm_of A hF h Ld mm mask Lm
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := Plan4L.firsts_K A rfl hF h Ld Lm.n0 Lm.nT Lm.nI
  have Hw0 := Plan4L.hwTies_slots mm mask Lm room7
  have hsX : scl = sclOf Xp.h Xp.p.v.sc Xp.p.v.g Xp.p.v.y.Lam := by rw [PX.h, PX.v]; exact hscl
  have eT : Xp.tT = { tT with p := { tT.p with rowMade := true } } :=
    Option.some.inj (PX.tT.symm.trans Ld.kTT)
  have f3 := fitsAt3 QL.plan.full (Plan4L.wK A) Ld OT.lt nz x g7 hz0 hzp
  have ho := ho_of_led QL.plan.full (Plan4L.wK A) Ld nz x g7 T.t3 ok f3 Ex y l2 mask
    entry (QL.plan.full.msg mm) (by rw [e3]; exact Hw0.hw3)
    (hincH3 (Plan4L.wK A) Ld nz x g7 F₂ l2 mask entry (QL.plan.full.msg mm) m3)
    (hinv { tT with p := { tT.p with rowMade := true } } Ld.kTT)
  have T4 := trueAt_pub Xp (F₂.worldOf gl mask entry) Mt hR2
  rw [PX.ρ] at T4
  have d4 := d2_four QL.plan.full (Plan4L.wK A) Ld Xp PX.ρ PX.H PX.fo hsX PX.D PX.tb
    PX.alpha PX.theta PX.tT PX.om PX.st lw nz x g7 T.t4 O3 hz0 hk0 hfil F₂ l2 mask entry
    (QL.plan.full.msg mm) (cellsAt Xp.p.v.y Mt) T4 (by rw [PX.v, hvy]; exact hcells) (QL.ns + 1) he
      hsl
    (Plan4L.hkI_of x.1 mm mask Lm hkS) m3 ho
  have hD4 := d4_of_pub QL.plan.full (Plan4L.wK A) Ld nz
    (addsOf (Plan4L.wK A) (ksOf { par.P with tokv := tk } par.hp) (t0.drop 1)
      nz x g7) x hc4 O3 O4 Sz.k3 Sz.k4 Nm.n3 hn4 hvy Sz.hNN Sz.hLM Sz.hNE Sz.hEnd Xp PX.ρ Xe PX.H
    Xrd (by have q := PX.sh; rw [eT] at q; exact q) PX.D hsX (by rw [PX.fo]; exact hz0)
    (by rw [PX.fo]; exact hz0) (F₁.worldOf gl mask entry) Mt hR1
  exact six_of_led QL.plan.full (Plan4L.wK A) Ld nz x g7 T ok Nm rfl
    (fitsAt1 QL.plan.full Ld OT.eS OT.m1 OT.lI OT.lP OT.half x
      (fun j => by rw [pv_drawn Ld]; exact hx j))
    (fitsAt2 QL.plan.full (Plan4L.wK A) Ld OT.lt nz x g7 hx)
    (fits4 QL.plan.full _ par.hp.lamS OT.k4)
    (fitsAt5 QL.plan.full (Plan4L.wK A) Ld OT.n5 OT.e5 OT.m5 OT.k4 OT.wD OT.le5 OT.rs
      nz x g7 O4 hz0 (fun j hj => by rw [Ld.ztF]; exact hzp j hj))
    (fitsAt6 QL.plan.full (Plan4L.wK A) Ld OT.n6 OT.e6 OT.m6 OT.k4 OT.lt OT.lfe OT.le6
      OT.rs OT.ll nz x g7 O3 O4)
    OT.k7 Sz.Z.2.2.2.2.2.2 Sz.hNP Sz.hNO rfl hD4 Ex y (Fo.Later.refl G) hS0 h1 h2 mask entry z1 z2
    mm (by rw [e1, e2, e3, e4, e5, e6, e7]; exact Hw0)
    ⟨hincH1 Ld x F₁ l1 mask entry (QL.plan.full.msg mm) hF (A.dimIsT tk) gl_half m1,
      hincH2 (Plan4L.wK A) Ld nz x g7 F₁ l1 mask entry (QL.plan.full.msg mm) m2, d4,
      hincO5 (Plan4L.wK A) Ld nz x g7 F₁ l1 mask entry (QL.plan.full.msg mm) O4 m5,
      hincO6 (Plan4L.wK A) Ld nz x g7 F₁ l1 mask entry (QL.plan.full.msg mm) O4
        (A.dimIsT tk) (A.lamM tk) m6,
      hincO7 (Plan4L.wK A) Ld nz x g7 F₂ l2 mask entry (QL.plan.full.msg mm) O4
        (A.dimIsT tk) A.hg m7⟩ w

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.Plan4L.six_led
