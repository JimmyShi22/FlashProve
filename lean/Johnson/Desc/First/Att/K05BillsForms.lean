-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05BillsForms.lean: kind K5: the kind's law at the letters beside the lookup's
closed caller (`K05_keepsW_all_left`, Johnson/Desc/First/Att/K05KeepsLeft.lean) with what it asks of
the relation behind the kind in the form "the runs return, and the forms are worth 0 with each entry
read as its table's stated sum of the committed cells".

Main names:
  `BillsFormsJ`: `BillsLaterJ`'s text (Johnson/Desc/First/Att/K05KeepsLater.lean) at these letters,
    with "there are a later ledger, a number of columns and a list of tables that is `Apart`" in the
    place of "there are a later ledger and entries", and `GatheredFormsJ`
    (Johnson/Desc/First/Att/K05GatheredForms.lean) at the entries `entryOf` of `matsOfMsg` in the
    place of `GatheredAllJ`.
  `billsLaterJ_of_forms`: the return of shapeHid, MatsFit and BillsFormsJ give BillsLaterJ.
  `K05_keepsW_forms_left`: K05_keepsW_all_left's statement, to the letter, with MatsFit and
    BillsFormsJ in the place of BillsLaterJ.
What it is worth: NOTHING IS PAID. AttAt and CellsTie are not among what is asked because the entries
and the matrices are picked so that they hold (by choice; by unfolding). What they say of the
committed message is said by the one sentence on the forms' worth at these entries. The reads'
truth (that the array which the prover commits later holds these sums) is not said and not used.
Limits: those of K05KeepsLeft.lean and K05GatheredForms.lean. BillsFormsJ, MatsFit, the seam, pin and
the entry's record are premises; no member is shown.

No soundness of the protocol is claimed. Nothing is claimed on completeness or hiding.

-/
import Johnson.Desc.First.Att.K05GatheredForms
import Johnson.Desc.First.Att.K05KeepsLeft

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb IOR TWhole Cb.Fo Cb.LdLkp Cb.Pv.Att Cb.Pv.Att.End Inst.Model Inst.Model.AttSeg
open OnBytes OnBytes.Model OnBytes.Model.Road
open OnBytes.Tie.Pv.Att (recOf)
open OnBytes.Slice OnBytes.Flat OnBytes.Maker Run Fo.Peel
open VerifiableInference.Desc.First.Look (Sent attCaller attSg JAtt AttOK enMask)
open K5Law (Apart entryOf)

section BillsForms
variable (x : VerifiableInference.Desc.First.Look.Place) (tl : HTailF2) (D : Sent)
  (rad : OracleShape → Nat) (Ex : Iop.ExtSpec) (Wp : Type)
  (α : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl)) → Cb.Gl.E)

/-- **What is asked of the relation behind the kind, in the forms' own words.** -/
def BillsFormsJ {St Aa Bb W : Type} (S : Attention.Shape) (ns : ℕ) (N : Nums) (rows : ℕ)
    (Jn : Aa → TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl)) → Forest.Heard → World Cb.Gl.E → (attSg x D rad).Msg → Prop)
    (seat : Seat St) (xr : Params.AttentionRounds) (recA : Aa → St) (recB : Bb → St)
    (x0 : Aa → TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl))) (zx : Aa → Array E) (zk : Aa → Array (Array E)) (on : Aa → Prop)
    (part : W → (attSg x D rad).Msg) (R' : Bb → W → Prop) : Prop :=
  ∀ (a : Aa) (b : Bb) (w : W), on a → R' b w → ∀ (F G : Fork) (h : Heard) (L : Lists),
    seat.ledger (recA a) = some F → seat.lay (recA a) h G = some (recB b) → Said xr h G L →
    Stays F G → G.ns = F.ns →
    ∃ (G' : Fork) (Kc : ℕ) (funs : List HFun), Stays G G' ∧ Sized G' ∧ G'.ns = G.ns ∧ Apart tl funs ∧
      GatheredFormsJ (attBase x S tl D rad) (attLin x S tl D rad Ex Wp α ns N) ns N rows S tl Kc funs (Jn a) (zx a)
        (zk a) (entryOf Reading.gl tl Kc (matsOfMsg x tl D rad (part w)) funs) G' h L (x0 a) (part w)

theorem billsLaterJ_of_forms {St Aa Bb W : Type} (S : Attention.Shape) (ns : ℕ) (N : Nums) (rows : ℕ)
    (lid : ℕ) (cf : Attention.Cfg) (fs : Model.Forest.Shape) (j0 : NameJ (attBase x S tl D rad).D S.ls S.cf.lmS)
    (Jn : Aa → TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl)) → Forest.Heard → World Cb.Gl.E → (attSg x D rad).Msg → Prop)
    (seat : Seat St) (xr : Params.AttentionRounds) (recA : Aa → St) (recB : Bb → St)
    (x0 : Aa → TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl))) (zx : Aa → Array E) (zk : Aa → Array (Array E)) (on : Aa → Prop)
    (part : W → (attSg x D rad).Msg) (R' : Bb → W → Prop)
    (hid : Attention.shapeHid lid cf = .ok (S, fs)) (hm : OnBytes.Road.Rows.MatsFit S tl)
    (H : BillsFormsJ x tl D rad Ex Wp α S ns N rows Jn seat xr recA recB x0 zx zk on part R') :
    BillsLaterJ (attBase x S tl D rad) (attLin x S tl D rad Ex Wp α ns N) ns N rows S lid cf fs
      (endLay (attBase x S tl D rad) (attLin x S tl D rad Ex Wp α ns N) ns N (cellAtt x S tl) S.ls S.cf.lmS j0)
      Jn seat xr recA recB x0 zx zk on part R' := by
  intro a b w ha hR F G h L h1 h2 h3 h4 h5
  obtain ⟨G', Kc, funs, s1, s2, s3, hA, hg⟩ := H a b w ha hR F G h L h1 h2 h3 h4 h5
  exact ⟨G', _, s1, s2, s3,
    gatheredAllJ_att_of_forms x S tl D rad Ex Wp α ns N rows lid cf fs j0 (Jn a) Kc funs hid hm hA hg⟩

open Classical in
/-- **The kind's law, what stands behind the kind being asked in the forms' own words.** -/
theorem K05_keepsW_forms_left {St Aa Bb W : Type} {set : Params.Setting}
    {settings : Model.Settings} {i : Attention.In} {cf : Attention.Cfg} {A : Attention.Plan}
    (hA : Attention.plan settings i cf = Except.ok A) (H : AttOK set x A.S tl D rad) (hfs : x.fs = A.fs)
    (hok : planOkAll cf A.S A.fs = true) (seat : Seat St) (hlb : LaysBack seat) (p : Par) (hp : p.own = A.own)
    (ns nx k : ℕ) (j0 : NameJ (OnBytes.Road.L5.dimOf A.S) A.S.ls A.S.cf.lmS)
    (ds : List RDT) (out : Aa → Tr (uLT (ckP .two) ds) → Option Bb) (recA : Aa → St) (recB : Bb → St)
    (x0 : Aa → TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl))) (yOf : Aa → Ex.Str) (on : Aa → Prop)
    (fork : St → Option Fork) (heard : St → Option Forest.Heard) (gOf : Aa → Forest.Heard)
    (pl : ℕ → ℕ → JAtt x.ns tl)
    (hent : ∀ a, on a → ∃ (F F' : Fork) (rs : TwV.Rounds Cb.Gl.E),
      K5Entry seat fork heard x p.own (recA a) ns nx k F F' (gOf a) rs ∧
        OutTies (x0 a) (Fo.endsOf x.fs x.lm F.next rs) (Cb.Fo.NumsEq.placeOf (enMask x.ns tl) pl))
    (hyes : ∀ a τ b, on a → out a τ = some b →
      decide seat p (recA a) ((rvT (ckP .two) ds τ).map noDigest) = .ok (recB b) ∧
        roundsFit (rounds p) ((rvT (ckP .two) ds τ).map noDigest) = true ∧
        ∀ r ∈ (rvT (ckP .two) ds τ).map noDigest, ∀ x ∈ r.drawn.elems, Fmt.Fld.two.okE x = true)
    (hpass : ∀ a τ b, out a τ = some b → passT (ckP .two) ds (rhoT (ckP .two) ds τ) = true)
    (hd : ∀ d ∈ ds, Plain (toRD d)) (he : ds.map (·.entry) = (rounds p).map (·.entry))
    (part : W → (attSg x D rad).Msg) (mOf : Aa → (attSg x D rad).Msg) (on' : Bb → Prop) (R' : Bb → W → Prop)
    (hon' : ∀ a τ b, on a → out a τ = some b → on' b)
    (hm : OnBytes.Road.Rows.MatsFit A.S tl)
    (hb : BillsFormsJ x tl D rad Ex Wp α A.S ns (numsPlan p.own (nx + Forest.elems x.fs)) A.own.rows
      (fun a _ gL _ _ => gL = gOf a)
      seat p.own recA recB x0 (fun a => (gOf a).zx) (fun a => (gOf a).zk) on part R')
    (pin : ∀ a τ b w, on a → out a τ = some b → R' b w → part w = mOf a) :
    (⟨uLT (ckP .two) ds, out⟩ : Reduction Aa Bb).KeepsW on on'
      (fun a w => ((closedOf (attBase x A.S tl D rad) (attLin x A.S tl D rad Ex Wp α ns (numsPlan p.own (nx + Forest.elems x.fs))) ns (numsPlan p.own (nx + Forest.elems x.fs))).own (theMeans Cb.Gl.E _ _ _)).ch.Todo (x0 a) (part w)) R'
      (bearErr ds _ (((closedOf (attBase x A.S tl D rad) (attLin x A.S tl D rad Ex Wp α ns (numsPlan p.own (nx + Forest.elems x.fs))) ns (numsPlan p.own (nx + Forest.elems x.fs))).own (theMeans Cb.Gl.E _ _ _)).ch.eps Ex)) :=
  K05_keepsW_all_left x tl D rad Ex Wp α hA H hfs hok seat hlb p hp ns nx k j0 ds out recA recB x0 yOf on fork heard
    gOf pl hent hyes hpass hd he part mOf on' R' hon'
    (billsLaterJ_of_forms x tl D rad Ex Wp α A.S ns (numsPlan p.own (nx + Forest.elems x.fs)) A.own.rows settings.lidb cf A.fs j0
      (fun a _ gL _ _ => gL = gOf a) seat p.own recA recB x0 (fun a => (gOf a).zx) (fun a => (gOf a).zk) on part R'
      (OnBytes.Road.L5.plan_shape hA).1 hm hb)
    pin

end BillsForms

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.billsLaterJ_of_forms
#print axioms VerifiableInference.Desc.First.Att.P.K05_keepsW_forms_left
