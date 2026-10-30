-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/PubAtMore.lean: TWO TIES MORE OF THE PUBLIC RECORD (`Pub34`) TO A HEARING OF K4's
TEXT, BESIDE THE TWENTY-THREE OF `PubAt` (Johnson/Road/K4/PubAt.lean), AT ONE AND THE SAME RECORD:
the reads' numbers X.rd are the plan's, and the panels' environment X.p is made of what was heard.
One theorem: bookkeeping over `pub34_of_hear_run` (PubOfHearTied.lean), which concludes both.

  `pubAtMore_of_led`: under the premises of `pubAt_of_led`: there is X with `PubAt` at Led7's own G2
  and tc4, X.rd = Pp.rd, and X.p = { v := o.v, e := o.H.fo.e, shownT := X.p.shownT, zt := o.H.ztF,
  stubO := stubO Pp.y }.

Limits. ALL PREMISES OF `pub34_of_hear_run` STAY PREMISES. STILL DROPPED, and so free behind «there
is»: X.funs, X.pc, X.s, X.lk, X.s0, X.tl; the panels' next free number; the shown values X.H1, X.V,
X.shownA, X.shownB.
-/
import Johnson.Road.K4.PubAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Model.Layer (Heard Pub Own HPlan2 stubO)
open OnBytes.Desc.First.K4 (engFl hear)
open Inst.Model (Tables)
open Inst.Model.FFSeg (Dim)

/-- **The public record at a hearing, with its reads' numbers and its panels' environment.** -/
theorem pubAtMore_of_led {Pp : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {o : Own}
    {F G : Fork} {t0 u : Tape} {H1 : Heard} {hd2 : Level} {tT : Tsc}
    {F4 F7 F8 G1 G1' G2 G3 G3' G4 : Fork}
    (h : hear engFl Pp hp g fo F t0 = some (o, G, u))
    (Ld : Led7 Pp hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4)
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
      PubAt X Pp hp fo o G2 ((ksOf Pp hp).tc4 (t0.drop 1)) D tb hS ∧ X.rd = Pp.rd ∧
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

#print axioms OnBytes.Road.K4.pubAtMore_of_led
