-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/PubAt.lean: THE PUBLIC RECORD OF THE LAYER LAWS (`Pub34`,
Johnson/Road/Rows/LayerEnds34.lean) AT A HEARING OF K4's TEXT, WITH ITS TIES SAID ONCE, IN THE
LETTERS OF `Led7` (Johnson/Road/K4/OwnLedgers.lean). Three records and one theorem. Bookkeeping over
`pub34_of_hear_run` (PubOfHearTied.lean): its premises are gathered, and twenty-two ties of its
conclusion, with one more, are named.

  `PubLines Pp g hS pc D tb s lk s0 tl`: the plan's public lines: nineteen premises of
    `pub34_of_hear_run`, to the letter.
  `LookLines Pp fo s0`: what it asks of what the lookup heard: five, to the letter.
  `PubAt X Pp hp fo o G2 t4 D tb hS`: the ties of X to the hearing: the reading; H, v, the batched
    sumcheck's challenges and end record, four first slots, the two layers' records, lamS, D, the
    shape, the tables, alpha and theta, the terms' record, the claims' environment; the power's
    base and the start form at the ledger G2 and the tape t4 at which the batched sumcheck begins;
    the terms' shown end values at G2; and that what the lookup heard stands in o.H.
  `pubAt_of_led`: where `hear` returns, with `Led7` at that return, under `PubLines`, `LookLines`,
    the rotary tables' fit and the inverse of the terms' coefficient: there is X with `PubAt` at
    Led7's own G2 and tc4.

Limits. ALL PREMISES OF `pub34_of_hear_run` STAY PREMISES. `PubAt` HOLDS NOT ALL THAT
`pub34_of_hear_run` CONCLUDES, AND X STANDS UNDER «THERE IS»: DROPPED, and so free again for whoever
builds on `PubAt` alone: X.funs, X.rd, X.pc, X.s, X.lk, X.s0, X.tl; of X.p the fields e, zt, stubO;
the panels' next free number; the shown values X.H1, X.V, X.shownA, X.shownB (which that theorem
ties to a ledger that it does not name). Who needs one of these calls `pub34_of_hear_run` itself. By
the head of LayerEnds34.lean hfl fails at the small shipped example.
-/
import Johnson.Road.K4.PubOfHearTied
import Johnson.Road.K4.OwnLedgers

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

/-- The plan's public lines. -/
structure PubLines (Pp : Pub) (g : ℕ) (hS : Layer.Shape) (pc : List (List String)) (D : Dim)
    (tb : Tables) (s : WsShape) (lk : ℕ) (s0 : Forest.Shape) (tl : HTailF2) : Prop where
  hy : layout hS pc = .ok Pp.y
  S : Switches hS
  hs : scalesHeld hS Pp.sc = .ok ()
  hg : g < Pp.y.NGr
  hrd : readsOf Pp.y = .ok Pp.rd
  hmats : ((Pp.tails.getD g {}).mats.map fun M => (M.m, M.k)) = matsR Pp.y g
  hρ : Numerals Reading.gl
  Z : Sized hS D
  hc : D.cap = hS.lidb
  hN : LinesAre Pp.y
  hfl : ∀ k : Fin 8, hS.nmin - hS.ll - hS.lt ≤ Nat.clog 2 (used D k)
  hs0 : Forest.shape Pp.y.cl Pp.y.h.lidb = .ok s0
  Zw : SizedW s D.P
  hsL : s.L = hS.L
  hlw : wsLayOf s true lk = .ok Pp.wsLay
  h4 : hS.p4 = true
  htm : (tl.mats.map fun M => (M.m, M.k)) = matsR Pp.y g
  hNM : tl.NM = tl.mats.size
  hpad : ∀ k : Fin 8,
    Reading.gl.val (ofF ((Pp.y.cl.getD k.val {}).tauAt (Pp.y.cl.getD k.val {}).t0)) =
      (((lut tb k).pad : ℤ) : Cb.Gl.E)

/-- What is asked of what the lookup heard. -/
structure LookLines (Pp : Pub) (fo : Forest.Heard) (s0 : Forest.Shape) : Prop where
  hsx : fo.zx.size = Pp.y.fo.dT
  hsy : fo.zy.size = Pp.y.fo.rK
  hzk : fo.zk = (Array.range Pp.y.fo.NC).map fun q =>
    fo.zy.extract (Pp.y.fo.rK - Pp.y.fo.iota.getD q 0) fo.zy.size ++ fo.zx
  he : fo.e = (Array.range Pp.y.fo.NC).map (Forest.callWeight Pp.y.fo fo.zy)
  hpt : ((List.range s0.NC).all fun q =>
    (fo.zk.getD q #[]).size == ((s0.calls[q]?).map (·.n)).getD 0) = true

/-- The ties of a public record to a hearing. -/
structure PubAt (X : Rows.Pub34 Cb.Gl.E) (Pp : Pub) (hp : HPlan2) (fo : Forest.Heard) (o : Own)
    (G2 : Fork) (t4 : Tape) (D : Dim) (tb : Tables) (hS : Layer.Shape) : Prop where
  ρ : X.ρ = Reading.gl
  H : X.H = o.H
  v : X.p.v = o.v
  rs : X.c.rs = o.K.rs
  fin : X.fin = o.K.fin
  sA : X.sA0 = o.K.sA0
  sH1 : X.sH1 = o.K.sH1
  sB : X.sB0 = o.K.sB0
  sV : X.sV = o.K.sV
  hd : X.hd = o.hd
  hd2 : X.hd2 = o.hd2
  lam : X.lam = hp.lamS
  D : X.D = D
  h : X.h = hS
  tb : X.tb = tb
  alpha : X.alpha = o.H.fo.alpha
  theta : X.theta = o.H.fo.theta
  tT : o.H.tT = some X.tT
  c : X.c = { v := o.v, wsLay := Pp.wsLay, rope := Pp.rope, rs := o.K.rs, rt := X.tT.r }
  om : X.om = powers (tapeEps t4) 2
  st : stackStart o.v o.H G2 t4 = startOf X.H X.om X.parts
  sh : ((Array.range (nEndT Pp.y)).mapM fun i => G2.shown (X.tT.sEnd + i)) = some X.p.shownT
  fo : o.H.fo = fo

/-- **The public record at a hearing, in `Led7`'s letters.** -/
theorem pubAt_of_led {Pp : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {o : Own} {F G : Fork}
    {t0 u : Tape} {H1 : Heard} {hd2 : Level} {tT : Tsc} {F4 F7 F8 G1 G1' G2 G3 G3' G4 : Fork}
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
    ∃ X : Rows.Pub34 Cb.Gl.E, PubAt X Pp hp fo o G2 ((ksOf Pp hp).tc4 (t0.drop 1)) D tb hS := by
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

#print axioms OnBytes.Road.K4.pubAt_of_led
