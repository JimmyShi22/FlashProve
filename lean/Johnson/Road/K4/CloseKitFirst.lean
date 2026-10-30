-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/CloseKitFirst.lean: FIVE SHORT STATEMENTS THAT THE FIRST GROUP's CLOSING FILES
CALL, each the twin of one that stands for a later group. Nothing new is argued: each proof is its
model's, over the record `LedG` (Johnson/Road/K4/OwnLedgersG.lean) in the place of `Led7`.

  `Plan4F.MeetsF.dimIsT`, `Plan4F.MeetsF.lamM`: under `MeetsF` (PlanMapsFirst.lean): the library's
    sizes are the program's own record's, with whatever tokens laid in; LamM = ne. Models:
    `Plan4.Meets.dimIsT`, `Plan4.Meets.lamM` (ClaimsPaid.lean).
  `heard_KF`: the six facts of `heard_K` (HeardK.lean) on what K4's hearing returns, IN WHICHEVER
    GROUP the letter g names: no premise on g.
  `Plan4LF.heard_KF`: the same under `MeetsF`, at { par.P with tokv := tk } and the sizes and first
    layer of the first group's value (`Plan4LF.planF`, ValueSlotsFirst.lean).
  `pubAtMore_of_ledF`: `pubAtMore_of_led` (PubAtMore.lean) in `LedG`'s letters: there is X with
    `PubAt` at LedG's own G2 and tc4, X.rd = Pp.rd, and X.p made of what was heard.

PREMISES of `heard_KF`: the hearing's return · the ledger in front has arrays of the right sizes ·
EVERY WORD THAT THE TAPE's ROUNDS DREW IS BELOW THE PRIME (`SmallTape`) · the layout is `layout`'s;
the library's sizes agree with the shape · TWO CHOICES OF LETTERS: the section's table of scales IS
`sclOf hS P.sc g P.y.Lam`; L0 IS g * Lam. Of `pubAtMore_of_ledF`: all premises of
`pub34_of_hear_run` (PubOfHearTied.lean), as `PubLines`, `LookLines`, the rotary tables' fit and the
inverse of the terms' coefficient.

Limits. K04_law IS NOT PROVED BY THIS. One direction: from a return. Equations alone: nothing on
soundness. Behind «there is X» stay free: X.funs, X.pc, X.s, X.lk, X.s0, X.tl; the panels' next
free number; the shown values X.H1, X.V, X.shownA, X.shownB.
-/
import Johnson.Road.K4.OwnLedgersG
import Johnson.Road.K4.OwnCoin
import Johnson.Road.K4.NormWordsOfHear
import Johnson.Road.K4.PlanMapsFirst
import Johnson.Road.K4.ValueSlotsFirst
import Johnson.Road.K4.PubAt
import Johnson.Road.Rows.LayerEnds34Ref
import OnBytes.Desc.First.K4.StackPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.K.Kc OnBytes.Model
open OnBytes.Model.Layer (Pub HPlan2 Own Heard layout stubO)
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim)
open OnBytes.Desc.First.K4 (Par engFl hear hearStack_public k0)
open OnBytes.Desc.First.P1 (tapeEps tscIn_heard)
open OnBytes.Tie.Pv.Lay.At (DimIs)

section Meets
variable [scl : Scl] {M X : Type} {Q : Plan4F Cb.Gl.E M X} {p : Par} {hS : Layer.Shape}
  {pc : List (List String)}

/-- **The library's sizes are the program's own record's, with whatever tokens laid in**, under
`MeetsF`. -/
theorem Plan4F.MeetsF.dimIsT (A : Q.MeetsF p hS pc) (tk : Array Nat) :
    DimIs Q.fullF.D (Verify.layerNumbers { p.P with tokv := tk } p.hp p.g) :=
  A.dimIs

/-- **The layers with routed experts**, under `MeetsF`. -/
theorem Plan4F.MeetsF.lamM (A : Q.MeetsF p hS pc) (tk : Array Nat) :
    ({ p.P with tokv := tk } : Layer.Pub).y.LamM = Q.fullF.D.ne :=
  (laySizes_of_layout A.hy).LamM.trans (ne_tie A.Z).symm

end Meets

/-- **Six facts on what the hearing returns, in whichever group**: from a ledger with arrays of the
right sizes, on a tape whose drawn words are below the prime, at a layout that `layout` makes, sizes
that agree with the shape, the table of scales `sclOf hS P.sc g P.y.Lam` and L0 = g * Lam. -/
theorem heard_KF [scl : Scl] {P : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {F G : Fork}
    {t0 u : Tape} {o : Own} {hS : Layer.Shape} {pc : List (List String)} {D : Dim} {L0 : ℕ}
    (h : hear engFl P hp g fo F t0 = some (o, G, u)) (hF : PscRun.Sized F)
    (hs : SmallTape t0) (hy : layout hS pc = .ok P.y) (Z : Sized hS D)
    (hscl : scl = sclOf hS P.sc g P.y.Lam) (hL0 : g * P.y.Lam = L0) :
    (∀ tT, o.H.tT = some tT →
      Reading.gl.val (negE (invE tT.p.eps)) * Reading.gl.val tT.p.eps = -1) ∧
    scl = sclOf hS o.v.sc o.v.g o.v.y.Lam ∧ o.v.y = P.y ∧ o.v.g * o.v.y.Lam = L0 ∧
    NormWords o.v D ∧ o.K.sB0 = o.K.sA0 + (1 + (1 + P.y.LamM)) := by
  subst hscl
  obtain ⟨vy, vsc, vg, _⟩ := env_of_hear h
  obtain ⟨H1, hd2, tT0, F4, F7, F8, G1, G1', G2, G3, G3', G4, G5, u5, Ld⟩ := own_ledG hF h
  have L := laySizes_of_layout hy
  refine ⟨?_, by rw [vsc, vg, vy], vy, by rw [vg, vy]; exact hL0, ?_, ?_⟩
  · intro tT e
    rw [Ld.kTT] at e
    obtain rfl := Option.some.inj e
    show Reading.gl.val (negE (invE tT0.p.eps)) * Reading.gl.val tT0.p.eps = -1
    have e1 : tT0.p.eps =
        tapeEps ((((ksOf P hp).tcP (t0.drop (k0 g))).drop 1).drop (P.y.h.lt + 3)) :=
      (tscIn_heard Ld.c3).2.2.2.2.2.2.2.2.1
    have hsm : SmallTape ((((ksOf P hp).tcP (t0.drop (k0 g))).drop 1).drop (P.y.h.lt + 3)) :=
      ((((((hs.drop (k0 g)).drop 1).drop 1).drop _).drop 1).drop 1).drop _
    have hk : okE tT0.p.eps = true := by
      rw [e1]
      exact small_eps hsm
    exact Rows.hinv_of gl_numerals (gl_ne_of_word hk Ld.eps) (Rows.gl_inv _)
  · have N := normWords_of_hear h D L.NN (L.Lam.trans (nl_tie Z).symm)
    rw [L.shape] at N
    exact N
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, a1, a2, _⟩ :=
      hearStack_public Ld.c4
    rw [a2, a1]
    omega

/-- **The same under `MeetsF`**, at the first group's value with its slots and orders laid, under
the two choices of letters. -/
theorem Plan4LF.heard_KF [scl : Scl] {M X : Type} {QF : Plan4LF Cb.Gl.E M X} {par : Par}
    {hS : Layer.Shape} {pcl : List (List String)} (A : QF.planF.MeetsF par hS pcl)
    {tk : Array Nat} {fo : Forest.Heard} {F G : Fork} {t0 u : Tape} {o : Own}
    (h : hear engFl { par.P with tokv := tk } par.hp par.g fo F t0 = some (o, G, u))
    (hF : PscRun.Sized F) (hs : SmallTape t0)
    (hscl : scl = sclOf hS par.P.sc par.g par.P.y.Lam) (hL0 : par.g * par.P.y.Lam = QF.L0) :
    (∀ tT, o.H.tT = some tT →
      Reading.gl.val (negE (invE tT.p.eps)) * Reading.gl.val tT.p.eps = -1) ∧
    scl = sclOf hS o.v.sc o.v.g o.v.y.Lam ∧ o.v.y = par.P.y ∧
    o.v.g * o.v.y.Lam = QF.planF.fullF.ip.L0 ∧ NormWords o.v QF.planF.fullF.D ∧
    o.K.sB0 = o.K.sA0 + (1 + (1 + par.P.y.LamM)) := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := OnBytes.Road.K4.heard_KF (P := { par.P with tokv := tk })
    (hS := hS) (pc := pcl) (D := QF.planF.D) (L0 := QF.L0) h hF hs A.hy A.Z hscl hL0
  exact ⟨a1, a2, a3, a4, a5, a6⟩

/-- **The public record at a hearing, with its reads' numbers and its panels' environment, in
`LedG`'s letters**, under the premises of `pubAt_of_ledF` (PubAtFirst.lean). -/
theorem pubAtMore_of_ledF {Pp : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {o : Own}
    {F G : Fork} {t0 u : Tape} {H1 : Heard} {hd2 : Level} {tT : Tsc}
    {F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 : Fork} {u5 : Tape}
    (h : hear engFl Pp hp g fo F t0 = some (o, G, u))
    (Ld : LedG Pp hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 u5)
    {hS : Layer.Shape} {pc : List (List String)} {D : Dim} {tb : Tables} {s : WsShape} {lk : ℕ}
    {s0 : Forest.Shape} {tl : HTailF2} (B : PubLines Pp g hS pc D tb s lk s0 tl)
    (K : LookLines Pp fo s0)
    (Rp : ∀ (rt : Array E) (lam : ℕ), lam < Pp.y.Lam →
      RopeFits Reading.gl
        { v := o.v, wsLay := Pp.wsLay, rope := Pp.rope, rs := o.K.rs, rt := rt } D tb
        (g * Pp.y.Lam) lam)
    (hinv : ∀ tT, o.H.tT = some tT →
      Reading.gl.val (negE (invE tT.p.eps)) * Reading.gl.val tT.p.eps = -1) :
    ∃ X : Rows.Pub34 Cb.Gl.E,
      PubAt X Pp hp fo o G2 ((ksOf Pp hp).tc4 (t0.drop (k0 g))) D tb hS ∧ X.rd = Pp.rd ∧
        X.p = { v := o.v, e := o.H.fo.e, shownT := X.p.shownT, zt := o.H.ztF,
                stubO := stubO Pp.y } := by
  obtain ⟨X, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, _, a13, a14, a15, a16, _, _, _, a20, _,
    _, a23, a24, a25, a26, a27, _, H1', G1x, G2x, _, _, u1x, u2x, _, n1, n2, _, hom, hst, hsh, _⟩ :=
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
    hom, hst, hsh, by rw [kfo, q6]⟩, a14, a27⟩

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.Plan4F.MeetsF.dimIsT
#print axioms OnBytes.Road.K4.Plan4F.MeetsF.lamM
#print axioms OnBytes.Road.K4.heard_KF
#print axioms OnBytes.Road.K4.Plan4LF.heard_KF
#print axioms OnBytes.Road.K4.pubAtMore_of_ledF
