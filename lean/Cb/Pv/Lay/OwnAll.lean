-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/Pv/Lay/OwnAll.lean: the letters of the chain of a layers' sub-proof's own rounds
(Cb/Pv/Lay/Own.lean) filled from the records of this folder's sumchecks, with the chain's laws
proved.

In Cb/Pv/Lay/Own.lean what is claimed before each drawing round, and what of each sumcheck's
output claims is owed at the end, are letters, and the laws on them are a premise. Here they are
made from the records of the seven sumchecks: the sums of squares, the products of the rows, the
terms, the batched inner products, the gated products, the routed gated products, the weights.
Each record keeps its own states and names; a map reads its state off the chain's statements,
another its entries off the messages. What ties one sumcheck to the next is a short list of
fields.

Main names:
  `Fore`: the records up to the terms; `jg`: the gap of the lookup's join as a function of the
    hidden sum of the terms; `Rd0`: what else is claimed at the start and is taken up only by the
    last stages. `Fore.Src`: what is claimed, beside the squares' identities, before the first
    stage: the rows' claim (`led` of the products' sums), that the join holds at the true sum of
    the terms, and `Rd0`. `Fore.g0`, `g1`: the two gaps before the draw that combines: the join's,
    at the sent sum less its mask; the terms' first row's, in the programs' form
    (Cb/Pv/Lay/Over.lean). `Fore.ow3`: of the terms' output claims the rows on the end values are
    owed at the end, and that the drawn coefficient is not 0.
  `Mid`: with the batched sumcheck's record, and `link`: its sum claim gives that the two gaps'
    batch is 0.
  `LayV`: with the last stages (`Foot`, Cb/Pv/Lay/OwnEnds.lean); `ow4`: what of the batched
    sumcheck's output claims is owed at the end; `seam`: that, with the input claims of the gated
    products, the routed ones and the weights, gives its output claims; `rides`: the weights'
    claims give `Rd0` back. `LayVF`: the same for the first sub-proof, in whose weights' round one
    scalar is sent (`FootFirst`, Cb/Pv/Lay/OwnEndsFirst.lean).
  `LayV.toTail`, `LayV.laws`, `LayVF.toTail`, `LayVF.laws`: the letters of Cb/Pv/Lay/Own.lean;
    `LayTail.Laws` of them: no premise is left but the fields of the records.
  `LayVO`: with the token point: before it a family of vectors on the cube of the positions
    vanishes, and Q; `atPt`: what is claimed behind the point gives that their extensions vanish
    at it, and Q. `LayVOF`: the first sub-proof's, with its two further points
    (Cb/Pv/Lay/Emb.lean) and `atTwo`: what is claimed behind the three points gives that the
    identities' extension over both indices vanishes at the two.
  `LayVO.knowAt`, `LayVOF.knowAt`: knowledge soundness of the whole chain: no premise is left but
    the fields of the records.

Limits: `link`, `seam`, `rides`, `atPt` and `atTwo` are fields, and so are the conditions inside
the seven records: whoever gives a value proves them. No value is built here: that the records,
the maps, `jg` and the families at a value are the programs' is not said. `link` is asked also
where the coefficient drawn in the sumcheck of the terms is 0. There `g1` is read with 1 / 0 = 0;
a batched sumcheck whose target and incoming form are written as `overAt` is meets `link` as an
identity, but the programs' own expression differs from it at the coefficient 0, on transcripts
that the programs refuse. In `LayV` the letter `Rd0` can carry nothing: `rides` is asked at every
statement, and the weights' claims there name scalars that the prover has sent; it is meant to be
"True". In `LayVF` it carries the embedding's identity. "The drawn coefficient is not 0" stands in
the last claim: whoever follows must test it (`knowAt_test`, Cb/Pv/Lay/OwnMid.lean;
`knowAt_tested`, Cb/Pv/Lay/OwnTest.lean). The limits of Cb/Pv/Lay/Own.lean hold here too. Nothing
is said on the honest prover, on completeness or on zero knowledge.
-/
import Cb.Pv.Lay.OwnEnds
import Cb.Pv.Lay.OwnEndsFirst
import Cb.Pv.Lay.OwnMid
import Cb.Pv.Lay.Emb
import Cb.Pv.Lay.Inner

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Lay
open Iop Prob Cb IOR Finset TWhole Johnson.L5.Layers Cb.Pv.Att

noncomputable section

variable {E : Type} [Field E] [Fintype E]

/-! ### The stages up to the terms -/

/-- The parameters of the stages up to the sumcheck of the terms, at first statements X. Each record
keeps its own states and names: a map reads its state off the first statement, another its entries
off the messages. -/
structure Fore (E : Type) [Field E] [Fintype E] (M X : Type) where
  /-- the sums of squares -/
  G : SquaresL E
  st0 : X → G.St
  rd0 : M → G.J → E
  /-- the products of the rows -/
  Rw : RowsL E
  st2 : X → Rw.St
  rd2 : M → Rw.J → E
  /-- the terms -/
  Tm : TokL E
  st3 : X → Tm.St
  rd3 : M → Tm.J → E
  /-- the gap of the lookup's join, as a function of the hidden sum of the terms -/
  jg : X → E → M → E
  /-- what else is claimed at the start and is taken up only by the last stages -/
  Rd0 : X → M → Prop

namespace Fore
variable {M X : Type} (V : Fore E M X)

/-- The join holds at the true sum of the terms. -/
def Jn (x : X) (m : M) : Prop :=
  V.jg x (tsum V.Tm.toSum.T.par (V.st3 x) (V.rd3 m) - V.rd3 m V.Tm.rJ) m = 0

/-- What is claimed, beside the squares' identities, before the first stage. -/
def Src (x : X) (m : M) : Prop := V.Rw.Idn (V.st2 x) (V.rd2 m) ∧ V.Jn x m ∧ V.Rd0 x m

/-- The first stages. -/
@[reducible] def H : Head E M X := ⟨V.G, V.st0, V.rd0, V.Src⟩

/-- The statements before the products' scalars; the first statement inside one. -/
abbrev X1 : Type := V.H.s1.Nx × E
def x0 (y : V.X1) : X := y.1.1.1.1.1.1

/-- The products of the rows. -/
@[reducible] def s2 : Stg E M (V.Rw.XP V.X1) :=
  V.Rw.stg2 V.rd2 (fun y => V.st2 (V.x0 y)) (F₀ V.Rw.tok.toSum.T.par)

/-- The terms: one further scalar, the claimed sum itself; nothing is claimed of it here. -/
@[reducible] def s3 : Stg E M V.s2.Nx where
  L := V.Tm.toSum
  n := 1
  F := F₀ V.Tm.toSum.T.par
  cl := fun b r => (r 0, V.st3 (V.x0 b.1.1.1.1))
  msg := V.rd3
  Lc := fun _ _ _ => True

/-- The two gaps before the draw that combines: the join's, at the sent sum less its mask; and the
terms' first row's, in the programs' form. -/
def g0 (b : V.s3.Nx) (m : M) : E :=
  V.jg (V.x0 b.1.1.1.1.1.1) ((b.1.2 : Fin 1 → E) 0 - V.rd3 m V.Tm.rJ) m
def g1 (b : V.s3.Nx) (m : M) : E :=
  keptAt V.Tm.toSum.T.par b.2 (V.rd3 m) - overAt V.Tm.toSum.T.par b.2 (V.rd3 m)
def gap (b : V.s3.Nx) (m : M) : Fin 2 → E := Fin.cases (V.g0 b m) fun _ => V.g1 b m

/-- the first statement inside a statement behind the terms -/
def x3 (b : V.s3.Nx) : X := V.x0 b.1.1.1.1.1.1

def p4 (b : V.s3.Nx) (m : M) : Prop := (∀ i, V.gap b m i = 0) ∧ V.Rd0 (V.x3 b) m

def ow3 (b : V.s3.Nx) (m : M) : Prop :=
  b.2.eps ≠ 0 ∧ ∀ a, V.Tm.toSum.T.par.EHolds b.2 (V.rd3 m) a

end Fore

/-! ### The batched sumcheck -/

/-- The parameters up to the batched sumcheck of the inner products. -/
structure Mid (E : Type) [Field E] [Fintype E] (M X : Type) extends Fore E M X where
  In : InnL E
  st4 : toFore.s3.Nx × E → In.St
  rd4 : M → In.J → E
  F4 : ∀ st, HFixs (In.toSum.T.par.vars st)
  /-- its sum claim gives that the two gaps' batch is 0 -/
  link : ∀ b β m, In.toSum.T.par.SumHolds (In.tg (st4 (b, β)), st4 (b, β)) (rd4 m) →
    toFore.g0 b m + β * toFore.g1 b m = 0

namespace Mid
variable {M X : Type} (W : Mid E M X)

@[reducible] def s4 : Stg E M (W.s3.Nx × E) where
  L := W.In.toSum
  n := 0
  F := W.F4
  cl := fun x _ => (W.In.tg (W.st4 x), W.st4 x)
  msg := W.rd4
  Lc := fun _ _ _ => True

end Mid

/-! ### The whole -/

/-- The parameters of all stages from the limbs' scalars on. -/
structure LayV (E : Type) [Field E] [Fintype E] (M X : Type) extends Mid E M X where
  /-- the last stages -/
  Ft : Foot E M toMid.s4.Nx
  /-- what of the batched sumcheck's output claims is owed at the end -/
  ow4 : toMid.s4.Nx → M → Prop
  /-- that, with the input claims of the three kinds of later stages, gives its output claims -/
  seam : ∀ b m, ow4 b m → Ft.Gp.Sg (Ft.st5 b) (Ft.rd5 m) → Ft.C6 b m → Ft.C7 b m →
    toMid.s4.Out b m
  /-- the weights' claims give back what was carried from the start -/
  rides : ∀ b m, Ft.C7 b m → toMid.Rd0 (toMid.x3 b.1.1.1) m

namespace LayV
variable {M X : Type} (V : LayV E M X)

/-- The letters of Cb/Pv/Lay/Own.lean. -/
def toTail : LayTail E M X where
  nL := V.H.nL
  eL := V.G.ns - 1
  pL := V.H.pL
  lL := V.H.lL
  gN := V.G.g
  eN := V.G.g * Fintype.card E ^ (V.G.g - 1)
  pN := V.H.pN
  s1 := V.H.s1
  ow1 := V.H.s1.Out
  p1 := V.H.p1
  nP := V.Rw.np
  eP := V.Rw.np - 1
  pP := fun y m => V.Src (V.x0 y) m
  lP := V.Rw.lP V.rd2 fun y => V.st2 (V.x0 y)
  s2 := V.s2
  ow2 := V.s2.Out
  s3 := V.s3
  ow3 := V.ow3
  n4 := 2
  p4 := V.p4
  s4 := V.s4
  ow4 := V.ow4
  s5 := V.Ft.s5
  ow5 := V.Ft.s5.Out
  p5 := V.Ft.p5
  gR := V.Ft.Rt.g
  eR := V.Ft.Rt.g * Fintype.card E ^ (V.Ft.Rt.g - 1)
  pR := V.Ft.pR
  s6 := V.Ft.s6
  ow6 := V.Ft.s6.Out
  p6 := V.Ft.p6
  nW := 0
  eW := V.Ft.Wt.n - 1
  pW := V.Ft.pW
  lW := fun _ _ _ => True
  s7 := V.Ft.s7

/-- The laws. What a user pays are the fields of the records. -/
theorem laws : V.toTail.Laws where
  cL := V.H.cL
  cN := V.H.cN V.H.p1 fun _ _ h => h
  o1 := fun _ _ h _ => h
  c1 := V.H.c1 (fun y m => V.Src (V.x0 y) m) fun _ _ _ h => h
  cP := V.Rw.cP V.rd2 (fun y => V.st2 (V.x0 y)) (F₀ V.Rw.tok.toSum.T.par) V.s2.Out
    (V.s3.stage V.ow3 V.toTail.ch4) (fun y m => V.Jn (V.x0 y) m ∧ V.Rd0 (V.x0 y) m) fun b m h =>
      terms_gives V.s3 rfl (fun b => V.st3 (V.x0 b.1.1.1.1)) (fun _ _ => rfl)
        (fun _ m => V.rd3 m V.Tm.rJ)
        (fun b z m => V.jg (V.x0 b.1.1.1.1) z m = 0 ∧ V.Rd0 (V.x0 b.1.1.1.1) m) V.ow3
        V.toTail.ch4 (fun c m hc => ⟨hc.1 0, hc.2⟩) b m h
  o2 := fun _ _ h _ => h
  o3 := o3_over V.s3 V.p4 fun b m h => sub_eq_zero.1 (h.1 1)
  c4 := c4 V.s4 V.ow4 V.toTail.ch5 2 V.gap (fun b m => V.Rd0 (V.x3 b) m)
    (fun b β _ m _ h => by
      rw [Fin.sum_univ_two]
      simpa [Fore.gap] using V.link b β m h)
    fun c m h => V.rides c m (V.Ft.todo5_gives c m h).2.2
  o4 := V.Ft.o4 V.ow4 V.s4.Out V.seam
  o5 := fun _ _ h _ => h
  c5 := V.Ft.c5
  cR := V.Ft.cR V.Ft.p6 fun _ _ h => h
  o6 := fun _ _ h _ => h
  c6 := V.Ft.c6
  cW := fun x m h s _ => V.Ft.cW (fun _ _ => True) x m h s

end LayV

/-! ### The first sub-proof's stages -/

/-- The same for the first sub-proof: in the weights' round one scalar is sent. -/
structure LayVF (E : Type) [Field E] [Fintype E] (M X : Type) extends Mid E M X where
  Ft : FootFirst E M toMid.s4.Nx
  ow4 : toMid.s4.Nx → M → Prop
  seam : ∀ b m, ow4 b m → Ft.Gp.Sg (Ft.st5 b) (Ft.rd5 m) → Ft.C6 b m → Ft.C7 b m →
    toMid.s4.Out b m
  rides : ∀ b m, Ft.C7 b m → toMid.Rd0 (toMid.x3 b.1.1.1) m

namespace LayVF
variable {M X : Type} (V : LayVF E M X)

/-- The letters of Cb/Pv/Lay/Own.lean. -/
def toTail : LayTail E M X where
  nL := V.H.nL
  eL := V.G.ns - 1
  pL := V.H.pL
  lL := V.H.lL
  gN := V.G.g
  eN := V.G.g * Fintype.card E ^ (V.G.g - 1)
  pN := V.H.pN
  s1 := V.H.s1
  ow1 := V.H.s1.Out
  p1 := V.H.p1
  nP := V.Rw.np
  eP := V.Rw.np - 1
  pP := fun y m => V.Src (V.x0 y) m
  lP := V.Rw.lP V.rd2 fun y => V.st2 (V.x0 y)
  s2 := V.s2
  ow2 := V.s2.Out
  s3 := V.s3
  ow3 := V.ow3
  n4 := 2
  p4 := V.p4
  s4 := V.s4
  ow4 := V.ow4
  s5 := V.Ft.s5
  ow5 := V.Ft.s5.Out
  p5 := V.Ft.p5
  gR := V.Ft.Rt.g
  eR := V.Ft.Rt.g * Fintype.card E ^ (V.Ft.Rt.g - 1)
  pR := V.Ft.pR
  s6 := V.Ft.s6
  ow6 := V.Ft.s6.Out
  p6 := V.Ft.p6
  nW := 1
  eW := V.Ft.Wf.n
  pW := V.Ft.pW
  lW := V.Ft.lW
  s7 := V.Ft.s7

/-- The laws. What a user pays are the fields of the records. -/
theorem laws : V.toTail.Laws where
  cL := V.H.cL
  cN := V.H.cN V.H.p1 fun _ _ h => h
  o1 := fun _ _ h _ => h
  c1 := V.H.c1 (fun y m => V.Src (V.x0 y) m) fun _ _ _ h => h
  cP := V.Rw.cP V.rd2 (fun y => V.st2 (V.x0 y)) (F₀ V.Rw.tok.toSum.T.par) V.s2.Out
    (V.s3.stage V.ow3 V.toTail.ch4) (fun y m => V.Jn (V.x0 y) m ∧ V.Rd0 (V.x0 y) m) fun b m h =>
      terms_gives V.s3 rfl (fun b => V.st3 (V.x0 b.1.1.1.1)) (fun _ _ => rfl)
        (fun _ m => V.rd3 m V.Tm.rJ)
        (fun b z m => V.jg (V.x0 b.1.1.1.1) z m = 0 ∧ V.Rd0 (V.x0 b.1.1.1.1) m) V.ow3
        V.toTail.ch4 (fun c m hc => ⟨hc.1 0, hc.2⟩) b m h
  o2 := fun _ _ h _ => h
  o3 := o3_over V.s3 V.p4 fun b m h => sub_eq_zero.1 (h.1 1)
  c4 := c4 V.s4 V.ow4 V.toTail.ch5 2 V.gap (fun b m => V.Rd0 (V.x3 b) m)
    (fun b β _ m _ h => by
      rw [Fin.sum_univ_two]
      simpa [Fore.gap] using V.link b β m h)
    fun c m h => V.rides c m (V.Ft.todo5_gives c m h).2.2
  o4 := V.Ft.o4 V.ow4 V.s4.Out V.seam
  o5 := fun _ _ h _ => h
  c5 := V.Ft.c5
  cR := V.Ft.cR V.Ft.p6 fun _ _ h => h
  o6 := fun _ _ h _ => h
  c6 := V.Ft.c6
  cW := V.Ft.cW fun _ _ => True

end LayVF

/-! ### With the token point -/

/-- The parameters of the own rounds of a sub-proof that is not the first. Before the token point a
family of vectors on the cube of the positions is claimed to vanish, and Q. -/
structure LayVO (E : Type) [Field E] [Fintype E] (M X : Type) where
  /-- the number of bits of a position -/
  gT : ℕ
  /-- the family of gaps, by a name and a position -/
  K : Type
  d : X → M → K → ℕ → E
  Q : X → M → Prop
  /-- the stages behind the point -/
  V : LayV E M (X × (Fin gT → E))
  /-- what is claimed behind the point gives that the extensions vanish at it, and Q -/
  atPt : ∀ x p m, V.H.pL (x, p) m →
    (∀ k, Blocks.ext gT (d x m k) (Blocks.nat p) = 0) ∧ Q x m

namespace LayVO
variable {M X : Type} (A : LayVO E M X)

/-- What is claimed before the first round. -/
def pT (x : X) (m : M) : Prop := (∀ k, ∀ Y < 2 ^ A.gT, A.d x m k Y = 0) ∧ A.Q x m

/-- The letters of Cb/Pv/Lay/Own.lean. -/
def toOwn : LayOwn E M X where
  gT := A.gT
  eT := A.gT * Fintype.card E ^ (A.gT - 1)
  pT := A.pT
  tail := A.V.toTail

theorem laws : A.toOwn.Laws where
  cT := law_pt A.gT A.d A.Q A.pT (fun y m => A.V.H.pL y m) (fun _ _ h1 h2 => ⟨h1, h2⟩) A.atPt
  tail := A.V.laws

/-- Knowledge soundness of the own rounds. The chain's laws are no premise any more: what a user
pays are the fields of the records. -/
theorem knowAt {Kc X0 Wp : Type} (Ex : ExtSpec) (A0 : Rels Kc X0 Ex (M × Wp)) (pr : X → X0)
    (Dn : X → M → Prop) :
    KnowAt (A.toOwn.ch.R Ex) (jt A0 pr fun x m => Dn x m ∧ A.pT x m)
      (jt A0 (fun e => pr (A.toOwn.ch.back e)) (A.toOwn.ch.Last Dn)) (fun _ _ _ wp => wp)
      (A.toOwn.ch.eps Ex) :=
  A.toOwn.knowAt A.laws Ex A0 pr Dn

end LayVO

/-- The parameters of the own rounds of the first sub-proof: the token point, then two further
points that test a family of identities with two indices (Cb/Pv/Lay/Emb.lean). -/
structure LayVOF (E : Type) [Field E] [Fintype E] (M X : Type) where
  gT : ℕ
  K : Type
  d : X → M → K → ℕ → E
  Q0 : X → M → Prop
  /-- the two further points' coordinates; the identities' gaps; what is carried along -/
  gA : ℕ
  gB : ℕ
  e : X × (Fin gT → E) → M → ℕ → ℕ → E
  Q : X × (Fin gT → E) → M → Prop
  /-- the stages behind the three points -/
  V : LayVF E M (((X × (Fin gT → E)) × (Fin gA → E)) × (Fin gB → E))
  /-- what is claimed behind the token point gives that the extensions vanish at it, and Q0 -/
  atPt : ∀ x p m, ((∀ V < 2 ^ gB, ∀ U < 2 ^ gA, e (x, p) m U V = 0) ∧ Q (x, p) m) →
    (∀ k, Blocks.ext gT (d x m k) (Blocks.nat p) = 0) ∧ Q0 x m
  /-- what is claimed behind the three points gives that the identities' extension over both
  indices vanishes at the two points, and Q -/
  atTwo : ∀ z m, V.H.pL z m →
    Blocks.ext gB (fun V => Blocks.ext gA (fun U => e z.1.1 m U V) (Blocks.nat z.1.2))
      (Blocks.nat z.2) = 0 ∧ Q z.1.1 m

namespace LayVOF
variable {M X : Type} (A : LayVOF E M X)

/-- What is claimed before the first round. -/
def pT (x : X) (m : M) : Prop := (∀ k, ∀ Y < 2 ^ A.gT, A.d x m k Y = 0) ∧ A.Q0 x m

/-- The letters of Cb/Pv/Lay/Own.lean. -/
def toOwn : LayOwnFirst E M X :=
  embFirst A.gT (A.gT * Fintype.card E ^ (A.gT - 1)) A.pT A.gA A.gB A.e A.Q A.V.toTail

theorem laws : A.toOwn.Laws :=
  emb_laws A.gT _ A.pT A.gA A.gB A.e A.Q A.V.toTail
    (law_pt A.gT A.d A.Q0 A.pT _ (fun _ _ h1 h2 => ⟨h1, h2⟩) A.atPt) A.atTwo A.V.laws

/-- Knowledge soundness of the first sub-proof's own rounds. What a user pays are the fields of
the records. -/
theorem knowAt {Kc X0 Wp : Type} (Ex : ExtSpec) (A0 : Rels Kc X0 Ex (M × Wp)) (pr : X → X0)
    (Dn : X → M → Prop) :
    KnowAt (A.toOwn.ch.R Ex) (jt A0 pr fun x m => Dn x m ∧ A.pT x m)
      (jt A0 (fun e => pr (A.toOwn.ch.back e)) (A.toOwn.ch.Last Dn)) (fun _ _ _ wp => wp)
      (A.toOwn.ch.eps Ex) :=
  A.toOwn.knowAt A.laws Ex A0 pr Dn

end LayVOF
end
end Cb.Pv.Lay

#print axioms Cb.Pv.Lay.LayV.laws
#print axioms Cb.Pv.Lay.LayVO.laws
#print axioms Cb.Pv.Lay.LayVO.knowAt
#print axioms Cb.Pv.Lay.LayVF.laws
#print axioms Cb.Pv.Lay.LayVOF.knowAt
