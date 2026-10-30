-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05GatheredForms.lean: kind K5: what the kind's law asks of the relation
behind the kind (`GatheredAllJ`, Johnson/Desc/First/Att/K05GatheredJ.lean) WITHOUT its two last
conjuncts ("the tables are true of matrices M": AttAt; "M's entries are the committed message's cell
entries": CellsTie), at the entries that read each table as its stated sum.

Main names:
  `GatheredFormsJ … tl Kc funs …`: GatheredAllJ's text, to the letter, with the smallness test's
    record tl, the number of columns Kc and the list of tables funs fixed in front, the matrices
    gone, and in the place of the two last conjuncts: the record's list of tables is funs.
  `gatheredAllJ_of_forms`: the return of shapeHid, MatsFit, `Apart tl funs`
    (Johnson/Desc/First/Att/Claims/TabsByChoice.lean), CellsTie at M, and GatheredFormsJ at the
    entries `entryOf Reading.gl tl Kc M funs` give GatheredAllJ at these entries.
  `gatheredAllJ_att_of_forms`: at the letters beside the lookup's closed caller on an attention link
    (`attBase`, `attLin`, `cellAtt`) and M := `matsOfMsg` (the committed message's own cells;
    Johnson/Desc/First/Att/K05CellsTie.lean): CellsTie is no premise.
What it is worth: NOTHING IS PAID. AttAt holds at these entries because they are chosen so; in the
last theorem CellsTie holds at its M by unfolding. What GatheredAllJ says through its two last
conjuncts now stands in ONE sentence of GatheredFormsJ: every gathered form, and the join's form, is
worth 0 in the world whose entry at a table's position is that table's weighted sum of M's entries:
in the first theorem of any M with CellsTie; in the last OF THE COMMITTED CELLS. That the array which
the prover commits later holds these sums (the reads' truth) is not said and not used.
Limits: GatheredFormsJ, Apart, MatsFit and the return of shapeHid are shown of no record here. The
record tl of the caller's letters and the tl of GatheredFormsJ are one letter in the last theorem.

No soundness of the protocol is claimed. Nothing is claimed on completeness or hiding.

-/
import Johnson.Desc.First.Att.K05CellsTie
import Johnson.Desc.First.Att.Claims.AttAtByChoice

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb TWhole IOR OnBytes OnBytes.Model OnBytes.Model.Road Johnson.L5.Layers Cb.Pv.Att Inst.Model
open OnBytes.Tie.Pv.Att (PscH SumH TailH UnitsH UnitsClaims seenAfter recOf)
open VerifiableInference.Desc.Part
open K5Law (oldOf PlanLaw AllZero Apart entryOf)
open Cb.Pv.Att.End (EndLay JoinLay NameJ)

variable {M0 Mg X : Type}

/-- **GatheredAllJ without its two last conjuncts**, at a fixed record, width and list of tables. -/
def GatheredFormsJ (P0 : OwnPar Cb.Gl.E M0 X) (Λ : Lin P0 Mg) (ns : ℕ) (N : Nums) (rows : ℕ) (S : Attention.Shape)
    (tl : HTailF2) (Kc : ℕ) (funs : List HFun)
    (Jn : X → Forest.Heard → World Cb.Gl.E → Mg → Prop) (zx : Array E)
    (zk : Array (Array E)) (entry : ℕ → ℕ → ℕ → Cb.Gl.E) (G : Fork) (h : Heard) (L : Lists) (x0 : X) (m : Mg) : Prop :=
  ∀ (nz : BetasNz Reading.gl L) (du : UnitsH Reading.gl ((closedOf P0 Λ ns N).own (theMeans Cb.Gl.E _ _ _)).units) (dt : TailH Reading.gl ((closedOf P0 Λ ns N).own (theMeans Cb.Gl.E _ _ _)).tail),
    UnitsOfP ((closedOf P0 Λ ns N).own (theMeans Cb.Gl.E _ _ _)).units du (recOf (closedOf P0 Λ ns N) rows).score h.scores.toList L.planes.flatten L.units →
    TailOfP dt (recOf (closedOf P0 Λ ns N) rows) h L →
    UnitsVals ((closedOf P0 Λ ns N).own (theMeans Cb.Gl.E _ _ _)).units du
      (unitsAdd (ρ := Reading.gl) ((closedOf P0 Λ ns N).own (theMeans Cb.Gl.E _ _ _)).units (landedUnits _ _) L.planes.flatten L.units (x0, [])) →
    TailVals dt (tailAdd ((closedOf P0 Λ ns N).own (theMeans Cb.Gl.E _ _ _)).tail L h nz (landedTail _ _) (seenAfter ((closedOf P0 Λ ns N).own (theMeans Cb.Gl.E _ _ _)).units du (x0, []))) →
    ∃ (l : Left) (A : Attention.Plan) (gL : Forest.Heard) (i : Runs.In) (l₁ l₂ : List Aff) (jn : Runs.JoinsP)
      (k3 : Runs.PadIn) (kf : Array Aff) (Fj : Fork) (tj : OnBytes.K.Kc.Tape) (xj : Aff × Fork × OnBytes.K.Kc.Tape)
      (nW : ℕ) (lk : LookIn),
      LeftIs (geoOf S) zk h G l ∧ i.g = geoOf S ∧ i.zk = gL.zk ∧ gL.zk = zk ∧ A.NC = S.calls.size ∧
      pointsOf i.g zk h l = some i.p ∧ Runs.firstRun i Kc = some (l₁, jn) ∧ Runs.secondRun i Kc = some l₂ ∧
      AllZero Reading.gl (G.worldOf Reading.gl (Λ.maskOf m) entry) (l₁ ++ l₂) ∧
      Runs.keysRun i k3 jn = some kf ∧ VerifiableInference.Desc.First.Look.joinF gL kf Fj tj = some xj ∧
      xj.1.value Reading.gl (G.worldOf Reading.gl (Λ.maskOf m) entry) = 0 ∧
      Jn x0 gL (G.worldOf Reading.gl (Λ.maskOf m) entry) m ∧
      tablesP i.g (K5Law.matsOf tl.mats) nW lk i.p = some i.t ∧ lk.zx = zx ∧
      (oldOf S gL i).t.funs.toList = funs

/-- **At the chosen entries GatheredAllJ asks no more than GatheredFormsJ**, three facts and CellsTie. -/
theorem gatheredAllJ_of_forms (P0 : OwnPar Cb.Gl.E M0 X) (Λ : Lin P0 Mg) (ns : ℕ) (N : Nums) (rows : ℕ)
    (S : Attention.Shape) (lid : ℕ) (cf : Attention.Cfg) (fs : Model.Forest.Shape) {J₂ : Type} [Fintype J₂]
    [DecidableEq J₂] (Ly : EndLay (closedOf P0 Λ ns N) J₂) (Jn : X → Forest.Heard → World Cb.Gl.E → Mg → Prop)
    {zx : Array E} {zk : Array (Array E)} {G : Fork} {h : Heard} {L : Lists} {x0 : X} {m : Mg}
    (tl : HTailF2) (Kc : ℕ) (funs : List HFun) (M : OnBytes.Road.Mats Cb.Gl.E)
    (hid : Attention.shapeHid lid cf = .ok (S, fs)) (hm : OnBytes.Road.Rows.MatsFit S tl) (hA : Apart tl funs)
    (hC : ∀ gL i, K5Law.CellsTie (oldOf S gL i) M Ly.cellJ ((closedOf P0 Λ ns N).msg m))
    (H : GatheredFormsJ P0 Λ ns N rows S tl Kc funs Jn zx zk (entryOf Reading.gl tl Kc M funs) G h L x0 m) :
    GatheredAllJ P0 Λ ns N rows S lid cf fs Ly Jn zx zk (entryOf Reading.gl tl Kc M funs) G h L x0 m := by
  intro nz du dt d1 d2 d3 d4
  obtain ⟨l, A, gL, i, l₁, l₂, jn, k3, kf, Fj, tj, xj, nW, lk, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12,
    c13, c14, c15, hf⟩ := H nz du dt d1 d2 d3 d4
  have at0 := K5Law.attAt_entryOf_gl tl Kc M (oldOf S gL i) lid cf fs hid hm (hf ▸ hA) G (Λ.maskOf m)
  rw [hf] at at0
  exact ⟨l, A, gL, i, Kc, l₁, l₂, jn, k3, kf, Fj, tj, xj, tl, nW, lk, M, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10,
    c11, c12, c13, c14, c15, at0, hC gL i⟩

section AtTheCaller
open Cb.Fo Cb.LdLkp Cb.Pv.Att.End Inst.Model.AttSeg
open VerifiableInference.Desc.First.Look (Sent attSg JAtt)

/-- **At the letters beside the lookup's closed caller, and at the committed message's own cells**:
CellsTie is no premise. -/
theorem gatheredAllJ_att_of_forms (x : VerifiableInference.Desc.First.Look.Place) (S : Attention.Shape)
    (tl : HTailF2) (D : Sent) (rad : OracleShape → Nat) (Ex : Iop.ExtSpec) (Wp : Type)
    (α : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl)) → Cb.Gl.E) (ns : ℕ) (N : Nums) (rows : ℕ)
    (lid : ℕ) (cf : Attention.Cfg) (fs : Model.Forest.Shape)
    (j0 : NameJ (attBase x S tl D rad).D S.ls S.cf.lmS)
    (Jn : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl)) → Forest.Heard → World Cb.Gl.E →
      (attSg x D rad).Msg → Prop)
    {zx : Array E} {zk : Array (Array E)} {G : Fork} {h : Heard} {L : Lists}
    {x0 : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl))} {m : (attSg x D rad).Msg}
    (Kc : ℕ) (funs : List HFun)
    (hid : Attention.shapeHid lid cf = .ok (S, fs)) (hm : OnBytes.Road.Rows.MatsFit S tl) (hA : Apart tl funs)
    (H : GatheredFormsJ (attBase x S tl D rad) (attLin x S tl D rad Ex Wp α ns N) ns N rows S tl Kc funs Jn zx zk
      (entryOf Reading.gl tl Kc (matsOfMsg x tl D rad m) funs) G h L x0 m) :
    GatheredAllJ (attBase x S tl D rad) (attLin x S tl D rad Ex Wp α ns N) ns N rows S lid cf fs
      (endLay (attBase x S tl D rad) (attLin x S tl D rad Ex Wp α ns N) ns N (cellAtt x S tl) S.ls S.cf.lmS j0)
      Jn zx zk (entryOf Reading.gl tl Kc (matsOfMsg x tl D rad m) funs) G h L x0 m :=
  gatheredAllJ_of_forms _ _ ns N rows S lid cf fs _ Jn tl Kc funs (matsOfMsg x tl D rad m) hid hm hA
    (fun gL i => cellsTie_att x S tl D rad Ex Wp α ns N j0 m gL i) H

end AtTheCaller

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.gatheredAllJ_of_forms
#print axioms VerifiableInference.Desc.First.Att.P.gatheredAllJ_att_of_forms
