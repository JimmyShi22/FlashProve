-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05KeepsLeft.lean: the law of the kind K5 at the parameters beside the closed
caller of the lookup on an attention link's calls, where all that it takes of the lookup's kind is
one record at the entry of the kind and the four ties of the out-statement. The join's tie `K3Join`
is not asked of the relation behind the kind.

Statement and proof. Main name:
  `K05_keepsW_all_left`: `K05_keepsW_later_any` (Johnson/Desc/First/Att/K05KeepsLater.lean) at
    `attBase`, `attLin0` and `attQ0` (Johnson/Desc/First/Att/K05AtCaller.lean). At each statement
    with "on" there are F, F' and rs with `K5Entry` seat fork heard x p.own (recA a) ns nx k F F'
    (gOf a) rs (Johnson/Desc/First/Att/K05Entry.lean) and `OutTies` (x0 a) (endsOf x.fs x.lm F.next
    rs) (placeOf (enMask x.ns tl) pl) (Johnson/Desc/First/Att/K05Left.lean). From these come `Room`
    (`hroom_of_entry`), `K3Pts` (`hk3_of_entry`) and `K3Join` at every ledger in which what lay at
    the entry stays (`k3join_of_entry`), and from it the join's worth (`hjv_att`,
    Johnson/Desc/First/Att/K05RowAtt.lean).
In `BillsLaterJ` the tie is "gL = gOf a": the heard record that the runs of claims read is the one
that lay at the entry of the kind. This is a fact on the carried record; it holds no equation in the
field.
Premises: the return of `Attention.plan` at A; `AttOK` at (x, A.S); x.fs = A.fs; a yes of
`planOkAll`; p.own = A.own; `LaysBack` seat; the record and the ties at "on"; the seam (hyes, hpass,
hd, he); hon'; `BillsLaterJ`; pin.
Limits: no premise is shown in this file or in what it imports, and no member is shown. The
statement holds for nothing where "on" holds of no statement, where R' holds of no witness or where
out returns nothing. The letter yOf stands in no premise and not in the conclusion. The record tl of
`attBase` and the tl that `GatheredAllJ` says there is are two letters, not tied. No soundness of
the protocol is claimed. Nothing on completeness or hiding.

-/
import Johnson.Desc.First.Att.K05KeepsLater
import Johnson.Desc.First.Att.K05RowAtt
import Johnson.Desc.First.Att.K05Entry

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb IOR TWhole Cb.Fo Cb.LdLkp Cb.Pv.Att Cb.Pv.Att.End Inst.Model Inst.Model.AttSeg
open OnBytes OnBytes.Model OnBytes.Model.Road
open OnBytes.Tie.Pv.Att (recOf)
open OnBytes.Slice OnBytes.Flat OnBytes.Maker Run Fo.Peel
open VerifiableInference.Desc.First.Look (Sent attCaller attSg JAtt AttOK enMask)

section KeepsLeft
variable (x : VerifiableInference.Desc.First.Look.Place) (tl : HTailF2) (D : Sent)
  (rad : OracleShape → Nat) (Ex : Iop.ExtSpec) (Wp : Type)
  (α : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl)) → Cb.Gl.E)

open Classical in
/-- **The kind's law, all that it takes of the lookup's kind being the record at the kind's entry and
the out-statement's four ties.** -/
theorem K05_keepsW_all_left {St Aa Bb W : Type} {set : Params.Setting}
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
    (hb : BillsLaterJ (attBase x A.S tl D rad) (attLin x A.S tl D rad Ex Wp α ns (numsPlan p.own (nx + Forest.elems x.fs))) ns (numsPlan p.own (nx + Forest.elems x.fs)) A.own.rows A.S settings.lidb cf A.fs (endLay (attBase x A.S tl D rad) (attLin x A.S tl D rad Ex Wp α ns (numsPlan p.own (nx + Forest.elems x.fs))) ns (numsPlan p.own (nx + Forest.elems x.fs)) (cellAtt x A.S tl) A.S.ls A.S.cf.lmS j0)
      (fun a _ gL _ _ => gL = gOf a)
      seat p.own recA recB x0 (fun a => (gOf a).zx) (fun a => (gOf a).zk) on part R')
    (pin : ∀ a τ b w, on a → out a τ = some b → R' b w → part w = mOf a) :
    (⟨uLT (ckP .two) ds, out⟩ : Reduction Aa Bb).KeepsW on on'
      (fun a w => ((closedOf (attBase x A.S tl D rad) (attLin x A.S tl D rad Ex Wp α ns (numsPlan p.own (nx + Forest.elems x.fs))) ns (numsPlan p.own (nx + Forest.elems x.fs))).own (theMeans Cb.Gl.E _ _ _)).ch.Todo (x0 a) (part w)) R'
      (bearErr ds _ (((closedOf (attBase x A.S tl D rad) (attLin x A.S tl D rad Ex Wp α ns (numsPlan p.own (nx + Forest.elems x.fs))) ns (numsPlan p.own (nx + Forest.elems x.fs))).own (theMeans Cb.Gl.E _ _ _)).ch.eps Ex)) :=
  K05_keepsW_later_any hA (hfs ▸ baseIs_att x A.S tl D rad) hok (attLin0 x A.S tl D rad) seat hlb p hp ns
    (nx + Forest.elems x.fs) (attQ0 x A.S tl D rad Ex Wp α ns (numsPlan p.own (nx + Forest.elems x.fs))) j0 (fun a _ gL _ _ => gL = gOf a) Ex ds out recA recB
    x0 yOf (fun a => (gOf a).zx) (fun a => (gOf a).zy) (fun a => (gOf a).zk) on
    (fun a ha F1 G' entry m gL hl hs hn e kv => by
      subst e
      obtain ⟨F, F', rs, N, T⟩ := hent a ha
      have eF : F1 = F' := N.ledger hl
      subst eF
      exact hjv_att x A.S tl D rad Ex Wp α ns (numsPlan p.own (nx + Forest.elems x.fs)) H (k3join_of_entry N Ex Wp H pl T hs hn entry m) kv)
    k
    (fun a ha G hG => by
      obtain ⟨F, F', rs, N, _⟩ := hent a ha
      exact hroom_of_entry N G hG)
    (fun a ha => by
      obtain ⟨F, F', rs, N, T⟩ := hent a ha
      exact hfs ▸ hk3_of_entry N H T.pt)
    hyes hpass hd he rfl part mOf on' R' hon' hb pin

end KeepsLeft

end VerifiableInference.Desc.First.Att.P
