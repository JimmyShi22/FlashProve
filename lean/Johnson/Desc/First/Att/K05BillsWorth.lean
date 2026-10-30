-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05BillsWorth.lean: kind K5: of what the kind's law asks of the relation behind
the kind (`BillsFormsJ`, Johnson/Desc/First/Att/K05BillsForms.lean) THE RETURNS ARE PAID: they follow
from what was heard (Said) and tests on public data (`returns_at_lk`,
Johnson/Desc/First/Att/K05ReturnsLk.lean), AT THE RECORD FOR THE LOOKUP's TABLES THAT THE PAYER NAMES (lk0). What stays asked of the relation is the forms' worth.

Main names:
  `gatheredFormsJ_of_returns`: `Returns` (Johnson/Desc/First/Att/K05GatheredZero.lean), "every gathered
    form is worth 0", "the join's form is worth 0" and the join's tie give `GatheredFormsJ`
    (Johnson/Desc/First/Att/K05GatheredForms.lean) at the returns' own list of tables.
  `BillsWorthJ`: BillsFormsJ's text with, in the place of "there are a later ledger, a width and a list
    … GatheredFormsJ": at every tuple with Returns AT lk0 a the gathered forms and the join's form are
    worth 0, each entry read as its table's stated sum (`entryOf` of `matsOfMsg`). BY READING, NOT
    TYPED: the other letters of such a tuple are returns of functions at lk0 a and what was heard (of
    l Returns has a relation, LeftIs): so "at every" should ask no more than "at one".
  `billsFormsJ_of_worths`: public: a yes of planOkAll, the return of shapeHid, MatsFit, a yes of
    claimsOk; AT "on", OF THE LOOKUP's KIND's PROMISE, NOT PUBLIC: hK (K3Pts at its heard record; four
    key points, calls and values e) and hlk (lk0 a has that record's point, and planesOk); hSz (the
    ledger behind the hearing is Sized); and BillsWorthJ: these give BillsFormsJ, with the join's tie
    "gL = gOf a".
What it is worth: thirteen returns and equations, Apart and the later ledger leave what is asked of
the relation behind. NOTHING OF THE FORMS' WORTH IS PAID. That lk0 a is the record that the seat hands
in is not asked here: a payer who names another pays at that other's entries. (A form that
runs over every record with the point is harder to pay, perhaps never at an honest run.)
Limits: those of the files named. The width Kc, the padding's record k3, the number nW, the plan
record A0 and the tape tj are letters; claimsOk's yes is evaluated in no file of this library. "The
stated sum" is over the library's reading of the committed symbols, which is 0 where a column is no
packing of small integers. No member is shown.

No soundness of the protocol is claimed. Nothing is claimed on completeness or hiding.

-/
import Johnson.Desc.First.Att.K05BillsForms
import Johnson.Desc.First.Att.K05ReturnsLk
import Johnson.Desc.First.Att.Claims.ReadsApart

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb IOR TWhole Cb.Fo Cb.LdLkp Cb.Pv.Att Cb.Pv.Att.End Inst.Model Inst.Model.AttSeg
open OnBytes OnBytes.Model OnBytes.Model.Road
open OnBytes.Tie.Pv.Att (recOf)
open OnBytes.Slice OnBytes.Flat OnBytes.Maker Run Fo.Peel
open VerifiableInference.Desc.First.Look (Sent attCaller attSg JAtt AttOK enMask)
open K5Law (Apart entryOf oldOf AllZero)

/-- Returns and the two worths give GatheredFormsJ at the returns' own list. -/
theorem gatheredFormsJ_of_returns {M0 Mg X : Type} (P0 : OwnPar Cb.Gl.E M0 X) (Λ : Lin P0 Mg) (ns : ℕ) (N : Nums)
    (rows : ℕ) {S : Attention.Shape} {tl : HTailF2} {Kc : ℕ}
    (Jn : X → Forest.Heard → World Cb.Gl.E → Mg → Prop) {zx : Array E} {zk : Array (Array E)}
    (entry : ℕ → ℕ → ℕ → Cb.Gl.E) {G : Fork} {h : Heard} (L : Lists) (x0 : X) (m : Mg)
    {l : Left} {A : Attention.Plan} {gL : Forest.Heard} {i : Runs.In} {l₁ l₂ : List Aff} {jn : Runs.JoinsP}
    {k3 : Runs.PadIn} {kf : Array Aff} {Fj : Fork} {tj : OnBytes.K.Kc.Tape} {xj : Aff × Fork × OnBytes.K.Kc.Tape}
    {nW : ℕ} {lk : LookIn} (Rt : Returns S zx zk G h l A gL i Kc l₁ l₂ jn k3 kf Fj tj xj tl nW lk)
    (hZ : AllZero Reading.gl (G.worldOf Reading.gl (Λ.maskOf m) entry) (l₁ ++ l₂))
    (hv : xj.1.value Reading.gl (G.worldOf Reading.gl (Λ.maskOf m) entry) = 0)
    (hJ : Jn x0 gL (G.worldOf Reading.gl (Λ.maskOf m) entry) m) :
    GatheredFormsJ P0 Λ ns N rows S tl Kc (oldOf S gL i).t.funs.toList Jn zx zk entry G h L x0 m :=
  fun _ _ _ _ _ _ _ => ⟨l, A, gL, i, l₁, l₂, jn, k3, kf, Fj, tj, xj, nW, lk, Rt.left, Rt.geo, Rt.zkI, Rt.zkL, Rt.nc,
    Rt.points, Rt.first, Rt.second, hZ, Rt.keys, Rt.join, hv, hJ, Rt.tables, Rt.zx, rfl⟩

section BillsWorth
variable (x : VerifiableInference.Desc.First.Look.Place) (tl : HTailF2) (D : Sent)
  (rad : OracleShape → Nat) (Ex : Iop.ExtSpec) (Wp : Type)
  (α : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl)) → Cb.Gl.E)

/-- **What stays asked of the relation behind the kind: the forms' worth.** -/
def BillsWorthJ {St Aa Bb W : Type} (S : Attention.Shape) (ns : ℕ) (N : Nums) (A0 : Attention.Plan) (Kc : ℕ)
    (k3 : Runs.PadIn) (nW : ℕ) (tj : OnBytes.K.Kc.Tape) (gOf : Aa → Forest.Heard) (lk0 : Aa → LookIn)
    (seat : Seat St) (xr : Params.AttentionRounds) (recA : Aa → St) (recB : Bb → St) (on : Aa → Prop)
    (part : W → (attSg x D rad).Msg) (R' : Bb → W → Prop) : Prop :=
  ∀ (a : Aa) (b : Bb) (w : W), on a → R' b w → ∀ (F G : Fork) (h : Heard) (L : Lists),
    seat.ledger (recA a) = some F → seat.lay (recA a) h G = some (recB b) → Said xr h G L →
    Stays F G → G.ns = F.ns →
    ∀ (l : Left) (i : Runs.In) (l₁ l₂ : List Aff) (jn : Runs.JoinsP) (kf : Array Aff)
      (xj : Aff × Fork × OnBytes.K.Kc.Tape),
      Returns S (gOf a).zx (gOf a).zk G h l A0 (gOf a) i Kc l₁ l₂ jn k3 kf G tj xj tl nW (lk0 a) →
      AllZero Reading.gl (G.worldOf Reading.gl ((attLin x S tl D rad Ex Wp α ns N).maskOf (part w))
        (entryOf Reading.gl tl Kc (matsOfMsg x tl D rad (part w)) (oldOf S (gOf a) i).t.funs.toList)) (l₁ ++ l₂) ∧
      xj.1.value Reading.gl (G.worldOf Reading.gl ((attLin x S tl D rad Ex Wp α ns N).maskOf (part w))
        (entryOf Reading.gl tl Kc (matsOfMsg x tl D rad (part w)) (oldOf S (gOf a) i).t.funs.toList)) = 0

/-- **The returns are paid.** -/
theorem billsFormsJ_of_worths {St Aa Bb W : Type} {S : Attention.Shape} {lid : ℕ} {cf : Attention.Cfg}
    (hid : Attention.shapeHid lid cf = Except.ok (S, x.fs)) (hok : planOkAll cf S x.fs = true)
    (hmf : OnBytes.Road.Rows.MatsFit S tl) (ns : ℕ) (N : Nums) (rows : ℕ) (A0 : Attention.Plan)
    (hN : A0.NC = S.calls.size) (iU3 nW : ℕ) (hu : iU3 = A0.iU3) {Kc : ℕ} {k3 : Runs.PadIn} {nzx : ℕ}
    (hd : claimsOk ⟨geoOf S, iU3, nW, K5Law.matsOf tl.mats⟩ Kc k3 true nzx = true) (tj : OnBytes.K.Kc.Tape)
    (gOf : Aa → Forest.Heard) (lk0 : Aa → LookIn) (seat : Seat St) (recA : Aa → St) (recB : Bb → St)
    (x0 : Aa → TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl))) (on : Aa → Prop)
    (hK : ∀ a, on a → (∃ zy z, K3Pts x.fs (gOf a).zx zy (gOf a).zk z) ∧ (gOf a).zk.size = 4 ∧
      (gOf a).shape.calls.size = 4 ∧ (gOf a).e.size = 4)
    (hlk : ∀ a, on a → (lk0 a).zx = (gOf a).zx ∧ (lk0 a).planesOk = true)
    (part : W → (attSg x D rad).Msg) (R' : Bb → W → Prop)
    (hSz : ∀ (a : Aa) (b : Bb) (w : W), on a → R' b w → ∀ (F G : Fork) (h : Heard) (L : Lists),
      seat.ledger (recA a) = some F → seat.lay (recA a) h G = some (recB b) →
      Said (recOf (closedOf (attBase x S tl D rad) (attLin x S tl D rad Ex Wp α ns N) ns N) rows) h G L →
      Stays F G → G.ns = F.ns → Sized G)
    (H : BillsWorthJ x tl D rad Ex Wp α S ns N A0 Kc k3 nW tj gOf lk0 seat
      (recOf (closedOf (attBase x S tl D rad) (attLin x S tl D rad Ex Wp α ns N) ns N) rows) recA recB on part R') :
    BillsFormsJ x tl D rad Ex Wp α S ns N rows (fun a _ gL _ _ => gL = gOf a) seat
      (recOf (closedOf (attBase x S tl D rad) (attLin x S tl D rad Ex Wp α ns N) ns N) rows) recA recB x0
      (fun a => (gOf a).zx) (fun a => (gOf a).zk) on part R' := by
  intro a b w ha hR F G h L h1 h2 h3 h4 h5
  have zG := hSz a b w ha hR F G h L h1 h2 h3 h4 h5
  have hW := H a b w ha hR F G h L h1 h2 h3 h4 h5
  obtain ⟨hlz, hlp⟩ := hlk a ha
  obtain ⟨⟨zy, z, H3⟩, hz4, hsh, he⟩ := hK a ha
  have PA := plan_all hid hok
  obtain ⟨r1, r2, u1, u2, wl, ix, wh, U⟩ := PA.units
  have B := baseIs_att x S tl D rad
  obtain ⟨_, _, s3, _, _, _, _⟩ := seven_of B hid PA.law.fit
  obtain ⟨l, i, l₁, l₂, jn, kf, xj, Rt⟩ := returns_at_lk hid PA.law U tl hmf iU3 nW hd H3 hz4
    (fun f hf => by have := s3 f hf; rw [B.D] at this; exact this)
    (closedOf (attBase x S tl D rad) (attLin x S tl D rad Ex Wp α ns N) ns N) B.D B.npl rows h3 zG A0 hN hu (gOf a) rfl
    hsh he G tj (lk0 a) hlz hlp
  obtain ⟨hZ, hv⟩ := hW l i l₁ l₂ jn kf xj Rt
  refine ⟨G, Kc, (oldOf S (gOf a) i).t.funs.toList, Stays.refl G, zG, rfl, ?_,
    gatheredFormsJ_of_returns _ _ ns N rows _ _ L (x0 a) (part w) Rt hZ hv rfl⟩
  show Apart tl (i.t.funs.map K5Law.funBack).toList
  rw [Array.toList_map]
  exact K5Law.apart_tablesP Rt.tables

end BillsWorth

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.gatheredFormsJ_of_returns
#print axioms VerifiableInference.Desc.First.Att.P.billsFormsJ_of_worths
