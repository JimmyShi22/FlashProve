-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/PubAtFirst.lean: THE FIRST GROUP's twin of Johnson/Road/K4/PubAt.lean (its part at
the typed chain): the public record at a hearing, in LedG's letters, in every group.

The statements and proofs are that file's, turned to the first group's letters by a program
(FullFPar for FullPar; the chain P.ownF.toOwn.tail; the records LedG and TgRecF, which stand in
every group, with the tail's tape t0.drop (k0 g)) and compiled; each name bears an F.

Main names: `pubAt_of_ledF`.

Limits. As that file's. Nothing on a draw, on soundness or on hiding.


-/
import Johnson.Road.K4.PubAt
import Johnson.Road.K4.OwnLedgersG

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Model.Layer (Heard Pub Own layout scalesHeld readsOf nEndT HPlan2)
open OnBytes.Desc.First.K4 (engFl hear stackStart)
open OnBytes.Desc.First.P1 (tapeEps)
open Inst.Model (Tables)
open Inst.Model.FFSeg (Dim used lut)
open OnBytes.Desc.First.K4 (k0)

/-- **The public record at a hearing, in `LedG`'s letters.** -/
theorem pubAt_of_ledF {Pp : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {o : Own} {F G : Fork}
    {t0 u : Tape} {H1 : Heard} {hd2 : Level} {tT : Tsc} {F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 : Fork} {u5
        : Tape}
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
    ∃ X : Rows.Pub34 Cb.Gl.E, PubAt X Pp hp fo o G2 ((ksOf Pp hp).tc4 (t0.drop (k0 g))) D tb hS :=
        by
  obtain ⟨X, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, _, a13, _, a15, a16, _, _, _, a20, _, _,
    a23, a24, a25, a26, _, _, H1', G1x, G2x, _, _, u1x, u2x, _, n1, n2, _, hom, hst, hsh, _⟩ :=
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
  exact ⟨X, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a13, a15, a16, a20, a23, a24, a25, a26,
    hom, hst, hsh, by rw [kfo, q6]⟩

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.pubAt_of_ledF
