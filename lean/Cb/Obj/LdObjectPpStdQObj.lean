-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectPpStdQObj.lean: assembly of the holographic IOP from its sub-protocols: the object on
data at the plan of this protocol's technical report (lean/CREDITS.md), both plans with standard
groups that have their own long positions (`StdPq`), the eight whole tests given by towers that are
parameters (no value is fixed):
the data, and the clause "choices of the plans and numbers" from a short list.

Definitions, one theorem and its proof. Generic. A tool: for guards, and for whoever puts towers
with stages at these groups.
`StdPq`: Cb/Obj/LdObjectPpStdQ.lean. The object on data: `LdObjZp` (Cb/Obj/LdObjectPpData.lean,
which also says what a tower is); the clause is `pl₁ : Z.R.HypPl₁` of its record `Z.HypRefPJ`
(`HypPl₁`: Cb/Obj/LdObjectPpRefPlan.lean).

Main names:
  `LdObjStQ F E`: data only, but for the proofs inside its fields' types (among them `StdPq`'s
    `neO`, `four`, `cov`): `D : LdObjD`; Y; nAt, `DO₀ : StdPq D.W.O`, n₀; offline four evaders zO₁
    .. zO₄ and four towers within a third wO₁ .. wO₄ (`LdTowG3` of the four joints) with distances;
    `DB : StdPq D.on.ol`, n₀B, baB; online four evaders zB₁ .. and four towers below the Johnson
    radius wB₁ .. (`LdTowGJ`) with distances; Zw, δ, the link's tower and distance. The fixed values
    are a record of their own, `S.Fx`.
  `S.XO`, `S.TO`, `S.XB`, `S.TB`: the tests' data; bounds on lists: 1 offline; listMax |P| d e
    online.
  `S.toRp v : LdObjRp`, `S.toZp v : LdObjZp`, for `v : S.Fx`.
  `ldObjStQ_pl₁`: `(S.toRp v).HypPl₁` from: q₀ is "nothing"; `EntAt`; the senders' places (twice);
    each plan's mask entry is the senders' free entry; the places of the offline mask part lie in
    messages of inG, those of the filed rows in messages of kpA; the demand on what is left; 1 ≤ N;
    ten inequalities in the towers' numbers of positions.

By construction the first three clauses of `LdRunD.Pre3` / `LdRunD.PreJ` (`RunGlAt` / `RunGlJAt`,
Cb/Gl/GlObjMix.lean) hold by definition at `S.toZp v` for the eight tests on the plans' groups; not
for the link's.

Notation: `dK`, `dO₁` .. `dO₄`, `dB₁` .. `dB₄`: natural numbers (in `LdRunD.Pre3`,
Cb/Obj/LdObjectTowers.lean, and `LdRunD.PreJ`, Cb/Obj/LdObjectTowerJohn.lean, the field `dist`: a
distance of the members' codes, one for each test).

Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectPpStdQ
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- the standard groups over what weights-formedness leaves -/
@[reducible] def LdOWf.pqO {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E]
    [Algebra F E] (W : LdOWf F E) (nAt : W.P.N → W.P.S.Ent) (D₀ : StdPq W.O) : StdPq W.O :=
  { D₀ with
    slR := W.restF nAt, BM := W.RB, finBM := inferInstance, rowsA := W.rowsA nAt, tgA := W.tgA }

/-- The data. -/
structure LdObjStQ (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] where
  D    : LdObjD F E
  Y    : D.StdS
  /-- offline -/
  nAt  : D.W.P.N → D.W.P.S.Ent
  DO₀  : StdPq D.W.O
  n₀   : Σ a, Y.TS.YO.Fr a
  zO₁  : Evader E ((D.W.pqO nAt DO₀).pl.GU.Row (D.W.O.toC.Brc ⊕ Unit))
  wO₁  : LdTowG3 (D.W.pqO nAt DO₀).pl.GU (fun _ => D.W.O.toC.Sh6) (D.W.pqO nAt DO₀).pl.r₁ zO₁
  zO₂  : Evader E ((D.W.pqO nAt DO₀).pl.G₂.Row Unit)
  wO₂  : LdTowG3 (D.W.pqO nAt DO₀).pl.G₂ (fun _ => D.W.O.toC.Sh6) (D.W.pqO nAt DO₀).pl.r₂ zO₂
  zO₃  : Evader E ((D.W.pqO nAt DO₀).pl.Gc.Row LinB₂)
  wO₃  : LdTowG3 (D.W.pqO nAt DO₀).pl.Gc (fun _ => D.W.O.toC.St6) (D.W.pqO nAt DO₀).pl.r₃ zO₃
  zO₄  : Evader E ((D.W.pqO nAt DO₀).G₄.Row {_b : (D.W.pqO nAt DO₀).BM // True})
  wO₄  : LdTowG3 (D.W.pqO nAt DO₀).G₄ (fun _ => D.W.O.Cl)
    (fun b : {_b : (D.W.pqO nAt DO₀).BM // True} =>
      ((D.W.pqO nAt DO₀).pl.rowsL (D.W.pqO nAt DO₀).rowsA b.1).onG (D.W.pqO nAt DO₀).G₄) zO₄
  dO₁  : ℕ
  dO₂  : ℕ
  dO₃  : ℕ
  dO₄  : ℕ
  /-- online -/
  DB   : StdPq D.on.ol
  n₀B  : Σ a, Y.TB.YO.Fr a
  baB  : D.on.ol.toC.Sa.O → ℕ
  zB₁  : Evader E (DB.pl.GU.Row (D.on.ol.toC.Brc ⊕ Unit))
  wB₁  : LdTowGJ DB.pl.GU (fun _ => D.on.ol.toC.Sh6) DB.pl.r₁ zB₁
  zB₂  : Evader E (DB.pl.G₂.Row Unit)
  wB₂  : LdTowGJ DB.pl.G₂ (fun _ => D.on.ol.toC.Sh6) DB.pl.r₂ zB₂
  zB₃  : Evader E (DB.pl.Gc.Row LinB₂)
  wB₃  : LdTowGJ DB.pl.Gc (fun _ => D.on.ol.toC.St6) DB.pl.r₃ zB₃
  zB₄  : Evader E (DB.G₄.Row {_b : DB.BM // True})
  wB₄  : LdTowGJ DB.G₄ (fun _ => D.on.ol.Cl)
    (fun b : {_b : DB.BM // True} => (DB.pl.rowsL DB.rowsA b.1).onG DB.G₄) zB₄
  dB₁  : ℕ
  dB₂  : ℕ
  dB₃  : ℕ
  dB₄  : ℕ
  /-- weights-formedness, distances, the link's tower -/
  Zw   : LdWfE F E
  δ    : D.Dst Zw
  twK  : D.Kc.run.Tow3
  dK   : ℕ

namespace LdObjStQ
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (S : LdObjStQ F E)

/-- the offline plan's data -/
@[reducible] def DO : StdPq S.D.W.O := S.D.W.pqO S.nAt S.DO₀

/-- the tests' data: each whole test is its tower's -/
@[reducible] def XO :
    LdRowsD S.DO.pl.S₃ S.D.W.O.toC.E₀ S.D.W.O.toC.Wpa (S.DO.pl.rowsL S.DO.rowsA) :=
  S.DO.mkX S.zO₄ S.wO₄.toG.toEnd 1 S.wO₄.toG.q
@[reducible] def TO : LdLinPpT S.DO.pl :=
  S.DO.mkT S.zO₁ S.wO₁.toG.toEnd 1 S.wO₁.toG.q S.zO₂ S.wO₂.toG.toEnd 1 S.wO₂.toG.q S.zO₃
    S.wO₃.toG.toEnd 1 S.wO₃.toG.q S.XO (fun a => a.2.elim, ())
@[reducible] def XB :
    LdRowsD S.DB.pl.S₃ S.D.on.ol.toC.E₀ S.D.on.ol.toC.Wpa (S.DB.pl.rowsL S.DB.rowsA) :=
  S.DB.mkX S.zB₄ S.wB₄.toG.toEnd (listMax (Fintype.card S.DB.P4) S.dB₄ S.DB.e4) S.wB₄.toG.q
@[reducible] def TB : LdLinPpT S.DB.pl :=
  S.DB.mkT S.zB₁ S.wB₁.toG.toEnd (listMax (Fintype.card S.DB.PU) S.dB₁ S.DB.eU) S.wB₁.toG.q S.zB₂
    S.wB₂.toG.toEnd (listMax (Fintype.card S.DB.PO) S.dB₂ S.DB.eO) S.wB₂.toG.q S.zB₃ S.wB₃.toG.toEnd
    (listMax (Fintype.card S.DB.PC) S.dB₃ S.DB.eC) S.wB₃.toG.q S.XB (fun a => a.2.elim, ())

/-- The fixed values. -/
structure Fx where
  x₀   : S.D.on.ol.toC.S.Smp
  y₀   : S.D.on.ol.toC.S.ext.Str
  xB   : S.TB.StB
  xC   : S.TB.StC
  yE   : S.D.on.ol.toC.E₀.Str
  sh₀  : S.D.on.ol.toC.Sh6
  x₄   : S.D.on.ol.toC.P.X4
  y₄   : S.D.on.ol.toC.P.E4.Str

variable (v : S.Fx)

def toRp : LdObjRp F E :=
  { S.D with
    Y := S.Y
    p := S.DO.pl
    TP₀ := S.TO
    nAt := S.nAt
    X := S.XO
    wX := (fun a => a.2.elim, ())
    n₀ := S.n₀
    pB := S.DB.pl
    TB₀ := S.TB
    RwB := S.DB.BM
    finRwB := S.DB.finBM
    rowsB := S.DB.rowsA
    tgB := S.DB.tgA
    slB := S.DB.slR
    XB := S.XB
    wXB := (fun a => a.2.elim, ())
    n₀B := S.n₀B
    q₀B := fun U => U = ∅
    baB := S.baB
    x₀ := v.x₀
    y₀ := v.y₀
    xB := v.xB
    xC := v.xC
    yE := v.yE
    sh₀ := v.sh₀
    x₄ := v.x₄
    y₄ := v.y₄ }

def toZp : LdObjZp F E :=
  { R := S.toRp v, Zw := S.Zw, δ := S.δ, twK := S.twK, tw₁ := S.wO₁, tw₂ := S.wO₂,
    tw₃ := S.wO₃, tw₄ := S.wO₄
    tw₁B := S.wB₁, tw₂B := S.wB₂, tw₃B := S.wB₃, tw₄B := S.wB₄
    dK := S.dK, d₁ := S.dO₁, d₂ := S.dO₂, d₃ := S.dO₃, d₄ := S.dO₄, d₁B := S.dB₁, d₂B := S.dB₂,
      d₃B := S.dB₃, d₄B := S.dB₄ }

/-- finiteness of the tables of weights-formedness, given at S.Zw, read at (S.toZp v).Zw: the same
type by definition -/
@[reducible] def finWfI (i : ∀ b, Fintype (S.Zw.K.wfI S.Zw.Rl b → E)) :
    ∀ b, Fintype ((S.toZp v).Zw.K.wfI (S.toZp v).Zw.Rl b → E) := i

end LdObjStQ

theorem ldObjStQ_pl₁ {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
    (S : LdObjStQ F E) (v : S.Fx) (q₀is : S.D.q₀ = fun U => U = ∅)
    (entAt : S.D.W.P.EntAt S.nAt) (plS : S.Y.TS.Places) (plB : S.Y.TB.Places)
    (nIs : S.DO₀.n₀ = S.Y.TS.YO.entF S.n₀) (nIsB : S.DB.n₀ = S.Y.TB.YO.entF S.n₀B)
    (inW : ∀ i,
      S.DO₀.inG
        (S.nAt (S.D.W.P.wAt (pIx S.D.W.P.bt.fmt (pdPlains E S.D.W.P.bt.n S.D.W.P.bt.k) i))).1)
    (inC : ∀ (q : Fin (S.D.W.P.n + 1)) n, S.D.W.P.gC q n → S.DO₀.inG (S.nAt n).1)
    (kpR : ∀ (r : S.D.W.RB) n, S.D.W.P.gR r.1.1 r.2 n → S.DO₀.kpA (S.nAt n).1)
    (qaOK : ∀ W,
      S.D.on.ol.toC.Sa.qFam (E₀ := S.D.on.ol.toC.E₀) (fun U => U = ∅) S.baB W → S.D.qaB W)
    (oneN : 1 ≤ S.D.N)
    (nA : ∀ a, (if S.DO₀.inG a then S.wO₃.toG.q else 0) + (if S.DO₀.kpA a then S.wO₄.toG.q else 0) ≤
      S.D.Bw.t a)
    (nW : S.wO₃.toG.q ≤ S.Y.tW S.D.W.O.toC.iW) (nU : S.wO₁.toG.q ≤ S.Y.tU S.D.W.O.toC.iU)
    (nO : S.wO₂.toG.q + S.wO₃.toG.q ≤ S.Y.tO S.D.W.O.toC.iO)
    (nS : S.wO₁.toG.q + S.wO₂.toG.q ≤ S.Y.tO S.DO₀.n₀.1)
    (nAB : ∀ a,
      (if S.DB.inG a then S.wB₃.toG.q else 0) + (if S.DB.kpA a then S.wB₄.toG.q else 0) ≤ S.baB a)
    (nWB : S.wB₃.toG.q ≤ S.Y.tWB S.D.on.ol.toC.iW) (nUB : S.wB₁.toG.q ≤ S.Y.tUB S.D.on.ol.toC.iU)
    (nOB : S.wB₂.toG.q + S.D.N * S.wB₃.toG.q ≤ S.Y.tOB S.D.on.ol.toC.iO)
    (nSB : S.wB₁.toG.q + S.wB₂.toG.q ≤ S.Y.tOB S.DB.n₀.1) : (S.toRp v).HypPl₁ := by
  obtain ⟨mK, mP⟩ := stdPq_mask S.DO S.Y.TS S.n₀ plS nIs
  obtain ⟨mKB, mPB⟩ := stdPq_mask S.DB S.Y.TB S.n₀B plB nIsB
  obtain ⟨o1, o2, o3, o4⟩ :=
    stdPq_needOff S.DO S.TO S.wO₄.toG.q S.D.Bw.t S.Y.tW S.Y.tU S.Y.tO nA nW nU nO nS
  obtain ⟨b1, b2, b3, b4⟩ := stdPq_needN S.DB S.TB S.XB (fun _ => trivial) (fun _ hh => hh)
    S.D.N S.baB S.Y.tWB S.Y.tUB S.Y.tOB nAB nWB nUB nOB nSB
  exact
    { q₀is := q₀is, entAt := entAt, plain := stdPq_plain S.DO, kept := stdPq_kept S.DO, kIs := mK,
      noPad := mP, restIs := rfl
      plW := fun i => ⟨(stdPq_k12 S.DO _).1, (stdPq_k12 S.DO _).2.1, inW i⟩
      plC := fun q n hg => ⟨(stdPq_k12 S.DO _).1, (stdPq_k12 S.DO _).2.1, inC q n hg⟩
      plR := fun r n hg => ⟨(stdPq_k12 S.DO _).1, (stdPq_k12 S.DO _).2.1, kpR r n hg⟩
      nowX := fun _ => trivial, kpX := fun _ hh => hh
      needA := o1, needW := o2, needU := o3, needO := o4
      shared := stdPq_shared S.DB, plainB := stdPq_plain S.DB, keptB := stdPq_kept S.DB,
        kIsB := mKB, noPadB := mPB
      nowXB := fun _ => trivial, kpXB := fun _ hh => hh, q₀Be := rfl, qaOK := qaOK, oneN := oneN
      needNA := b1, needNW := b2, needNU := b3, needNO := b4 }

end Cb
