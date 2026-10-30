-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/RuleAll.lean: CONDITIONAL: the honest prover's side of an attention
segment's own rounds: EVERY NAMED SCALAR THAT THE KEY FORMS READ: THE PROVER's VALUE, READ IN A
FIELD, IS THE LIBRARY's RULE VALUE (`rv`, Inst/Model/Att/KeyForms.lean), in one statement over the
library's names. Definitions, and statements with their proofs. No algebra is in this file: it
gathers Johnson/Desc/K5/Honest/Law/RuleValues.lean and two statements of Law/Starts.lean.

What it is for. The tree has: at any values of the named scalars that are the rule values wherever
the key forms read them, a key form is the multilinear extension of its call's vector of looked-up
values (`kf_worth`, Johnson/Desc/First/Att/Claims/KeysWorth.lean). Law/Keys.lean asks for "under
each slot lies the rule value" (`RuleAt`). What is meant to lie under a slot is the prover's scalar:
that it lies there is not shown here. This file says that that scalar, read, is the rule value.

Main names:
  `PlaneReads`, `MaxReads`, `LoneReads`   the premises: at a plane claim; at a unit's maximum; all
  `scalarOf`         the prover's value, read, under each of the library's names
  `scalar_rule`      the scalars that one claim ties to a table
  `scalar_rule_all`  all that the key forms read, the four sums of products among them
  `piecesRead_of_all`, `loneReads_of_linPub`   `LoneReads` from the tree's own bundle of public
                                               premises

EVERY STATEMENT IS CONDITIONAL. `Sized`: public. `StepReads`: the files on the three summands. The
accumulator's scalar comes by `acc_reads` (Law/Starts.lean) under the clause `wl`. `LoneReads` has
clauses of three sorts: lengths of points, and "piece b is pair b": public, or tests of the
verifier's function of the points; that a plane claim's flag is its family's region: public; that
points and pieces' weights, read, are the library's: these hang on what the lookup hands on.
TWO SOURCES OF `LoneReads`. The main one is Johnson/Desc/K5/Honest/Law/LoneUnits.lean: from the
lookup's key points, the place's seven units and the text of the verifier's function of the points;
its public premises say yes together, by evaluation, at three small places (Law/LoneUnitsToy.lean).
The other is `loneReads_of_linPub` here: from `LinPub` (Claims/KeysWorth.lean), which the tree draws
(Claims/KeysPubAll.lean) from a bundle that holds the public test `CallsFit` whole.
Limits. `CallsFit` SAYS NO AT ALL THREE SMALL MADE-UP PLANS of
Johnson/Desc/K5/Honest/ProductsToy.lean, and yes at a small place of the library's own;
Law/PremisesToy.lean holds both by lines. So at these three plans `loneReads_of_linPub` has no
member by evaluation. A plan in which the layers of the group have more than one shift is not
reached. Nothing here says that a premise holds at any place. No property is claimed by a
definition.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.RuleValues
import Johnson.Desc.K5.Honest.Law.EndsMeet
import Johnson.Desc.First.Att.Claims.KeysPubAll
import Cb.Pv.Att.End.Seam

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes (E addE subE mulE zeroE oneE)
open OnBytes.Model (Reading)
open OnBytes.Road (pt)
open OnBytes.Road.Rows (Linear)
open Cb.Pv.Att.End (ReadK)
open VerifiableInference.Desc.First.Att.P (Geo W1 RemP ScoreP DivP geoOf)
open Inst.Model.AttSeg hiding ibV
open Finset

variable {K : Type} [Field K]

/-! ## The premises, list by list -/

/-- **The premises at a plane claim** of the family fam: its region and the length of its inner
point are the family's; the inner point and the pieces' weights read as the library's. -/
structure PlaneReads (ρ : Reading K) (P : Pub5) (C : Calls) (z : ℕ → K) (fam : Fam) (u : RemP) :
    Prop where
  reg : regOf u.isD = fam.reg
  size : u.z.size = fam.l P.D
  reads : ∀ j < fam.l P.D, pt ρ u.z j = inn P.D C z fam j
  pieces : PiecesRead ρ P C z fam u.pw

/-- **The premises at a softmax-table unit's maximum**: vg: what the head point reads as; wt: what
the tile rows' weights read as. -/
structure MaxReads (ρ : Reading K) (P : Pub5) (C : Calls) (z : ℕ → K) (fam : Fam) (k : ScoreP)
    (vg wt : ℕ → K) : Prop where
  pieces : PiecesRead ρ P C z fam k.pw
  sg : k.zg.size = P.D.lg
  g : ∀ j < P.D.lg, pt ρ k.zg j = vg j
  wI : ∀ I < P.D.nBlk, ρ.val (k.wI.getD I zeroE) = wt I
  si : k.zi.size = P.D.lB
  i : ∀ j < P.D.lB, pt ρ k.zi j = zi' P.D C z j

/-- **The premises of all the scalars that are sent by themselves and that the key forms read.** pM,
pD: the plane claims of the two remainder-table units; cM, cD: those of the two softmax-table units
kM, kD; d: the division's points. -/
structure LoneReads (ρ : Reading K) (P : Pub5) (C : Calls) (p : Pub K) (pM pD cM cD : RemP)
    (kM kD : ScoreP) (d : DivP) : Prop where
  m1 : PlaneReads ρ P C p.z .m1 pM
  d1 : PlaneReads ρ P C p.z .d1 pD
  m2 : PlaneReads ρ P C p.z .m2 cM
  d2 : PlaneReads ρ P C p.z .d2 cD
  msM : MaxReads ρ P C p.z .m2 kM (zg P.D C p.z) (blkRow P.D (zP P.D C p.z) (zs P.D C p.z))
  msD : MaxReads ρ P C p.z .d2 kD (zgD P.D C p.z) (Blocks.eqN (P.D.lP + 1) 0 (zID P.D C p.z))
  wl : LonePts ρ P C p d
  ixP : PiecesRead ρ P C p.z .x3 d.pwX
  ixSg : d.zgX.size = P.D.lg
  ixG : ∀ j < P.D.lg, pt ρ d.zgX j = xg P.D C p.z j
  ixSi : d.ziX.size = P.D.lT
  ixI : ∀ j < P.D.lT, pt ρ d.ziX j = xi P.D C p.z j
  whP : PiecesRead ρ P C p.z .f4 d.pwH
  whY : YReads ρ P C p.z d.zgH d.ziH d.zcH

/-! ## The prover's scalars by the library's names -/

/-- **The prover's value, read, under each name of a scalar of the key forms.** sM, sD, zo: the
three that are sums over cubes, handed in. The cases follow the tree's table of slots (`slotOf`,
Johnson/Road/Rows/AttBetween.lean). A name that the library's list does not hold gets 0. That a
value lies under the slot of its name is not said here; in that table the planes' scalars of a
softmax-table unit have the unit's slots, while their values are taken at the unit's plane claim. -/
def scalarOf (ρ : Reading K) (g : Geo) (w : K5In) (pM pD cM cD : RemP) (kM kD : ScoreP) (d : DivP)
    (sM sD zo : E) : KSc → K
  | .cell .m1 x => ρ.val (planeOf g w pM x)
  | .cell .d1 x => ρ.val (planeOf g w pD x)
  | .cell .m2 x => ρ.val (planeOf g w cM x)
  | .cell .d2 x => ρ.val (planeOf g w cD x)
  | .cell _ _ => 0
  | .ms .M => ρ.val (maxAt g w kM)
  | .ms .D => ρ.val (maxAt g w kD)
  | .ss .M => ρ.val sM
  | .ss .D => ρ.val sD
  | .acc => ρ.val (accAt g w d)
  | .zo => ρ.val zo
  | .zc => ρ.val (zcAt g w d)
  | .rh => ρ.val (rhAt g w d)
  | .rh' => ρ.val (rhpAt g w d)
  | .ib k => ρ.val ((ibAt g w d).getD k zeroE)
  | .rg => ρ.val (rh2At g w d)
  | .rg' => ρ.val (rhp2At g w d)

variable {ρ : Reading K} {P : Pub5} {C : Calls} {p : Pub K} {pM pD cM cD : RemP} {kM kD : ScoreP}
  {d : DivP}

/-- **Every scalar that the key forms read and that one claim ties to a table: the prover's value,
read, is the library's rule value.** CONDITIONAL on `Sized` (public) and `LoneReads`. -/
theorem scalar_rule (H : Sized P) (w : K5In) (R : LoneReads ρ P C p pM pD cM cD kM kD d)
    (sM sD zo : E) : ∀ k, ReadK P.D k → Linear k →
      scalarOf ρ P.g w pM pD cM cD kM kD d sM sD zo k = rv P.D C p (tOf ρ w) k := by
  intro k hr hl
  match k, hr, hl with
  | .cell .m1 x, _, _ => exact planeOf_rule ρ w C p R.m1.reg R.m1.size R.m1.reads R.m1.pieces x
  | .cell .d1 x, _, _ => exact planeOf_rule ρ w C p R.d1.reg R.d1.size R.d1.reads R.d1.pieces x
  | .cell .m2 x, _, _ => exact planeOf_rule ρ w C p R.m2.reg R.m2.size R.m2.reads R.m2.pieces x
  | .cell .d2 x, _, _ => exact planeOf_rule ρ w C p R.d2.reg R.d2.size R.d2.reads R.d2.pieces x
  | .cell .w3 _, hr, _ => exact hr.elim
  | .cell .x3 _, hr, _ => exact hr.elim
  | .cell .f4 _, hr, _ => exact hr.elim
  | .ms .M, _, _ =>
    exact maxAt_rule_below ρ w C p H R.msM.pieces R.msM.sg R.msM.g R.msM.wI R.msM.si R.msM.i
  | .ms .D, _, _ =>
    exact maxAt_rule_on ρ w C p H R.msD.pieces R.msD.sg R.msD.g R.msD.wI R.msD.si R.msD.i
  | .ss _, _, hl => exact hl.elim
  | .acc, _, hl => exact hl.elim
  | .zo, _, hl => exact hl.elim
  | .zc, _, _ => exact zc_reads ρ w R.wl
  | .rh, _, _ =>
    exact rhAt_rule ρ w C p ((lonePts_iff ρ C p).1 R.wl).1 ((lonePts_iff ρ C p).1 R.wl).2
  | .rh', _, _ =>
    exact rhpAt_rule ρ w C p ((lonePts_iff ρ C p).1 R.wl).1 ((lonePts_iff ρ C p).1 R.wl).2
  | .ib k, hr, _ => exact ibAt_rule ρ w C p H R.ixP R.ixSg R.ixG R.ixSi R.ixI hr
  | .rg, _, _ => exact rh2At_rule ρ w C p R.whP R.whY
  | .rg', _, _ => exact rhp2At_rule ρ w C p R.whP R.whY

/-- **Every scalar that the key forms read**, where moreover the three sums that are handed in are
those of summands that read as the library's steps s6b, s6d and s8. CONDITIONAL as `scalar_rule`,
and on the three `StepReads` (Law/ProductsLaw.lean). -/
theorem scalar_rule_all (H : Sized P) (w : K5In) (R : LoneReads ρ P C p pM pD cM cD kM kD d)
    {SM SD SE : Summand} (RM : StepReads ρ SM P.D C p (tOf ρ w) .s6b)
    (RD : StepReads ρ SD P.D C p (tOf ρ w) .s6d) (RE : StepReads ρ SE P.D C p (tOf ρ w) .s8) :
    ∀ k, ReadK P.D k → scalarOf ρ P.g w pM pD cM cD kM kD d SM.total SD.total SE.total k =
      rv P.D C p (tOf ρ w) k := by
  intro k hr
  by_cases hl : Linear k
  · exact scalar_rule H w R _ _ _ k hr hl
  · match k, hl with
    | .ss .M, _ => exact RM.total
    | .ss .D, _ => exact RD.total
    | .zo, _ => exact RE.total
    | .acc, _ => exact acc_reads ρ H w R.wl
    | .cell _ _, hl => exact absurd trivial hl
    | .ms _, hl => exact absurd trivial hl
    | .zc, hl => exact absurd trivial hl
    | .rh, hl => exact absurd trivial hl
    | .rh', hl => exact absurd trivial hl
    | .ib _, hl => exact absurd trivial hl
    | .rg, hl => exact absurd trivial hl
    | .rg', hl => exact absurd trivial hl

/-! ## The premises, from the tree's own bundle of public premises -/

section Lin
open OnBytes OnBytes.Model OnBytes.Attention OnBytes.Road.Rows
open K5Law (LinPub unitsOf oldOf remBack pwBack)

/-- The tree's premise on a list of pieces, said of the kind's own pieces. -/
theorem piecesRead_of_all {ρ : Reading K} {S : Attention.Shape} {x : Params.AttentionRounds}
    {C : Calls} {z : ℕ → K} {fam : Fam} {pw : Array W1} (A : PiecesAll S (pwBack pw))
    (hw : ∀ b < S.NP,
      ρ.val ((pwBack pw).getD b default).wp = wp (OnBytes.Road.L5.dimOf S) C z fam b) :
    PiecesRead ρ ⟨S, x⟩ C z fam pw := by
  have hs : pw.size = S.NP := by
    have h1 := A.1
    unfold K5Law.pwBack at h1
    rwa [Array.size_map] at h1
  refine ⟨hs, fun b hb => ?_, fun b hb => ?_⟩
  · have h1 := hw b hb
    rw [pwBack_getD pw (lt_of_lt_of_eq hb hs.symm)] at h1
    exact h1
  · have hb' : b < pw.size := lt_of_lt_of_eq hb hs.symm
    have e1 : (pwBack pw)[b]? = some ((pwBack pw).getD b default) := by
      have h2 : b < (pwBack pw).size := lt_of_lt_of_eq hb A.1.symm
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h2]
      rfl
    have e2 := A.2 b hb _ e1
    rw [pwBack_getD pw hb'] at e2
    exact e2

/-- **`LoneReads` at the division's points of any values i of the claims, and at any plane claims
and units**, from the tree's bundle of the public premises of its statements on the same scalars
(`LinPub`, Johnson/Desc/First/Att/Claims/KeysWorth.lean; Claims/KeysPubAll.lean draws it from the
planner's shape, the lookup's key points and the tables' list). Nothing here says that i holds what
the verifier's function of the points makes: the bundle alone ties the letters. CONDITIONAL on that
bundle and on `Sized`. -/
theorem loneReads_of_linPub {ρ : Reading K} {S : Attention.Shape} {x : Params.AttentionRounds}
    {tl : HTailF2} {gL : Forest.Heard} {i : VerifiableInference.Desc.First.Att.P.Runs.In}
    {C : Calls} {p : Pub K} {pM pD cM cD : RemP} {kM kD : ScoreP} {tM tD : ScoreTables}
    (H : Sized ⟨S, x⟩)
    (Lp : LinPub ρ tl (oldOf S gL i) (unitsOf pM pD kM kD tM tD) (remBack cM) (remBack cD) C p) :
    LoneReads ρ ⟨S, x⟩ C p pM pD cM cD kM kD i.p.d := by
  have hlt : S.cf.lt = (OnBytes.Road.L5.dimOf S).lT := H.lt
  have hnB : S.nT = (OnBytes.Road.L5.dimOf S).nBlk := OnBytes.Road.Rows.dim_nBlk H.Z
  have yr : ∀ {pw : Array PW} {zg zi zc : Array E} {f : Fam},
      K5Law.HighPub ρ tl (oldOf S gL i) C p pw zg zi zc f → YReads ρ ⟨S, x⟩ C p.z zg zi zc :=
    fun X => ⟨X.szg, X.g, X.szi.trans hlt, fun j hj => X.i j (lt_of_lt_of_eq hj hlt.symm), X.szc,
      X.n⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, piecesRead_of_all Lp.ixP Lp.ixW, Lp.ixZg, Lp.ixG,
    Lp.ixZi.trans hlt, fun j hj => Lp.ixI j (lt_of_lt_of_eq hj hlt.symm),
    piecesRead_of_all Lp.wh.pairs Lp.wh.w, yr Lp.wh⟩
  · exact ⟨by rw [show pM.isD = false from Lp.m1.isD]; exact Lp.m1.reg.symm,
      Lp.m1.z.trans Lp.m1.len.symm, fun j hj => Lp.m1.v j (lt_of_lt_of_eq hj Lp.m1.len),
      piecesRead_of_all Lp.m1.pairs Lp.m1.w⟩
  · exact ⟨by rw [show pD.isD = true from Lp.d1.isD]; exact Lp.d1.reg.symm,
      Lp.d1.z.trans Lp.d1.len.symm, fun j hj => Lp.d1.v j (lt_of_lt_of_eq hj Lp.d1.len),
      piecesRead_of_all Lp.d1.pairs Lp.d1.w⟩
  · exact ⟨by rw [show cM.isD = false from Lp.m2.isD]; exact Lp.m2.reg.symm,
      Lp.m2.z.trans Lp.m2.len.symm, fun j hj => Lp.m2.v j (lt_of_lt_of_eq hj Lp.m2.len),
      piecesRead_of_all Lp.m2.pairs Lp.m2.w⟩
  · exact ⟨by rw [show cD.isD = true from Lp.d2.isD]; exact Lp.d2.reg.symm,
      Lp.d2.z.trans Lp.d2.len.symm, fun j hj => Lp.d2.v j (lt_of_lt_of_eq hj Lp.d2.len),
      piecesRead_of_all Lp.d2.pairs Lp.d2.w⟩
  · exact ⟨piecesRead_of_all Lp.msM.pairs Lp.msM.w, Lp.msM.zg, Lp.msM.g,
      fun I hI => Lp.msMI I (lt_of_lt_of_eq hI hnB.symm), Lp.msM.zi, Lp.msM.i⟩
  · exact ⟨piecesRead_of_all Lp.msD.pairs Lp.msD.w, Lp.msD.zg, Lp.msD.g,
      fun I hI => Lp.msDI I (lt_of_lt_of_eq hI hnB.symm), Lp.msD.zi, Lp.msD.i⟩
  · exact (lonePts_iff ρ C p).2 ⟨piecesRead_of_all Lp.wl.pairs Lp.wl.w, yr Lp.wl⟩

end Lin

end H2K5.Honest

#print axioms H2K5.Honest.scalar_rule
#print axioms H2K5.Honest.scalar_rule_all
#print axioms H2K5.Honest.piecesRead_of_all
#print axioms H2K5.Honest.loneReads_of_linPub
