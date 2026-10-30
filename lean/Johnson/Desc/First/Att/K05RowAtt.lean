-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05RowAtt.lean: the forms of Johnson/Desc/First/Att/K05RowAny.lean at
`attBase` (Johnson/Desc/First/Att/K05AtCaller.lean), the parameters beside the closed caller of the
lookup on an attention link's calls: so that these forms and `whole_row_att`, `whole_row_plan` speak
of one set of letters: c := attCaller, P0 := attBase, Λ := attLin, Q := meantQ … attQ0 (`joinLayOf`
at the scales sclOf S).

Definitions, statements and proofs.
Main names:
  `hjv_att`: the equality of worths that `GatheredTop` (Johnson/Desc/First/Att/K05RowTop.lean) holds
    for the join, at these letters, from `AttOK` and `K3Join`
    (Johnson/Desc/First/Att/K05JoinMeets.lean), by `join_meets`.
  `hscl_att`: the first shift of these letters' table of scales is the group's.
  `cellAtt`, `baseIs_att`: `attBase` is a base (`BaseIs`); its cells lie at `enCell` of `addrA`.
  `K05_row_att`, `K05_row_att_plan`: `K05_row_any` and `K05_row_any_plan` there.
  `K05_keepsW_att`: `K05_keepsW_any_one` there, at a plan A that `Attention.plan` returns, with S :=
    A.S and x.fs = A.fs.
Why `attBase` and not `baseOf` at that caller: `attCaller` reads a cell by `enCell` (0 where a name
has no cell); `attBase` reads so by definition; `baseOf`, with its total map of places, would want a
cell at every name, valid or not. The three laws take no `AttOK`: `hjv_att` and `whole_row_att` do.
Public premises of `K05_keepsW_att`: the return of `Attention.plan`; x.fs = A.fs; a yes of
`planOkAll`; p.own = A.own. At each statement with "on": `Room` at the ledger in front; `K3Pts` at
the end point. The seam (hyes, hpass, hd, he), `BillsTop` and pin.
Used: `K05_row_any`, `K05_row_any_plan`, `K05_keepsW_any_one`, `join_meets`, `att_ok`,
`attLin`, `attLin0`, `attQ0`, `meantQ`, `endLay`; no routine in a context.
Limits: those of Johnson/Desc/First/Att/K05RowTop.lean (`GatheredTop` is shown to be met at no view)
and of Johnson/Desc/First/Att/K05AtCaller.lean (the silent 0; x.ns stands untied beside ns0). In
`GatheredTop` the equality of worths stands inside an existence statement: `K3Join` does not yet
stand in its place. No soundness of the protocol is claimed: the seam and the premises named are not
shown. Nothing is claimed on completeness or hiding.

-/
import Johnson.Desc.First.Att.K05AtCaller
import Johnson.Desc.First.Att.K05JoinMeets
import Johnson.Desc.First.Att.K05RowAny

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb IOR TWhole Cb.Fo Cb.LdLkp Cb.Pv.Att Cb.Pv.Att.End Inst.Model Inst.Model.AttSeg
open OnBytes OnBytes.Model OnBytes.Model.Road
open OnBytes.Road.L5 (sclOf)
open OnBytes.Tie.Pv.Att (recOf)
open K5Law (PlanLaw)
open OnBytes.Slice OnBytes.Flat OnBytes.Maker Run Fo.Peel
open VerifiableInference.Desc.First.Look (Sent attCaller attSg JAtt AttOK att_ok)

section RowAtt
variable (x : VerifiableInference.Desc.First.Look.Place) (S : Attention.Shape) (tl : HTailF2) (D : Sent)
  (rad : OracleShape → Nat) (Ex : Iop.ExtSpec) (Wp : Type)
  (α : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl)) → Cb.Gl.E) (ns : ℕ) (N : Nums)

local notation "cA" => attCaller x S tl D rad Ex Wp
local notation "P0A" => attBase x S tl D rad
local notation "ΛA" => attLin x S tl D rad Ex Wp α ns N
local notation "QA" => meantQ P0A (attLin0 x S tl D rad) ns N (attQ0 x S tl D rad Ex Wp α ns N)

/-- **The one equality of worths, at the letters beside the closed caller, from the lookup's kind's
record.** -/
theorem hjv_att {set : Params.Setting} (H : AttOK set x S tl D rad) {gL : Forest.Heard} {W : World Cb.Gl.E}
    {x0 : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl))} {m : (attSg x D rad).Msg}
    (J : K3Join cA gL W x0 m) (kv : Fin 4 → Cb.Gl.E) :
    joinVal (K5Law.qAt Reading.gl gL) kv (gL.cEnd.value Reading.gl W) =
      joinVal ((QA).q x0) kv (((QA).ce x0).val ((closedOf P0A ΛA ns N).msg m)) :=
  join_meets (c := cA) (P := closedOf P0A ΛA ns N) (att_ok Ex Wp H cA (List.mem_singleton.2 rfl)) H.four (sclOf S)
    α Sum.inr (fun _ _ => rfl) J kv

/-- The first shift of these letters' table of scales is the group's. -/
theorem hscl_att : ((QA).scl.κ 0).sh = S.cf.sh.getD 0 0 := rfl

end RowAtt

section Tower
variable (x : VerifiableInference.Desc.First.Look.Place) (S : Attention.Shape) (tl : HTailF2) (D : Sent)
  (rad : OracleShape → Nat) (Ex : Iop.ExtSpec) (Wp : Type)
  (α : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl)) → Cb.Gl.E)

local notation "P0A" => attBase x S tl D rad

/-- The place of a cell among the entries of attBase. -/
def cellAtt (c : AttSeg.Raw) : JAtt x.ns tl :=
  VerifiableInference.Desc.First.Look.enCell x.ns tl (OnBytes.Road.L5.addrA S c).1 (OnBytes.Road.L5.addrA S c).2.1
    (OnBytes.Road.L5.addrA S c).2.2

/-- attBase is a base. -/
theorem baseIs_att : BaseIs P0A S x.fs (cellAtt x S tl) := ⟨rfl, rfl, rfl, rfl, fun _ => rfl⟩

open Classical in
/-- **K05_row_top at the parameters beside the closed caller.** -/
theorem K05_row_att {St Aa Bb : Type} {lid : ℕ} {cf : Attention.Cfg}
    (hid : Attention.shapeHid lid cf = Except.ok (S, x.fs)) (PL : PlanLaw cf S x.fs) (seat : Seat St) (p : Par)
    (ns0 k0 : ℕ) (j0 : NameJ (OnBytes.Road.L5.dimOf S) S.ls S.cf.lmS) (rows : ℕ) {qW qM qD : Fin 4}
    (UW : ∀ wl, (geoOf S).single .wl = some wl →
      UnitIs (OnBytes.Road.L5.dimOf S) (OnBytes.Road.L5.callsOf x.fs) .w3 qW wl)
    (UM : UnitIs (OnBytes.Road.L5.dimOf S) (OnBytes.Road.L5.callsOf x.fs) .m1 qM
      ((geoOf S).unitAt 1 (callOf (OnBytes.Road.L5.callAt S 1)) .fm))
    (UD : UnitIs (OnBytes.Road.L5.dimOf S) (OnBytes.Road.L5.callsOf x.fs) .d1 qD
      ((geoOf S).unitAt 1 (callOf (OnBytes.Road.L5.callAt S 1)) .fd))
    (hrec : p.own = recOf (closedOf P0A (attLin x S tl D rad Ex Wp α ns0 (numsPlan p.own k0)) ns0
      (numsPlan p.own k0)) rows) (ds : List RDT)
    (out : Aa → Tr (uLT (ckP .two) ds) → Option Bb) (recA : Aa → St) (recB : Bb → St)
    (x0 : Aa → TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl))) (yOf : Aa → Ex.Str)
    (mOf : Aa → (attSg x D rad).Msg) (zx zy : Aa → Array E) (zk : Aa → Array (Array E)) (on : Aa → Prop)
    (hon : ∀ a, on a → ∀ F, seat.ledger (recA a) = some F → Sized F ∧ F.ns = ns0 ∧ F.next = k0)
    (hk3 : ∀ a, on a → K3Pts x.fs (zx a) (zy a) (zk a) (x0 a).2.1.pt)
    (hyes : ∀ a τ b, on a → out a τ = some b →
      decide seat p (recA a) ((rvT (ckP .two) ds τ).map noDigest) = .ok (recB b) ∧
        roundsFit (rounds p) ((rvT (ckP .two) ds τ).map noDigest) = true ∧
        ∀ r ∈ (rvT (ckP .two) ds τ).map noDigest, ∀ x ∈ r.drawn.elems, Fmt.Fld.two.okE x = true)
    (hpass : ∀ a τ b, out a τ = some b → passT (ckP .two) ds (rhoT (ckP .two) ds τ) = true)
    (hd : ∀ d ∈ ds, Plain (toRD d)) (he : ds.map (·.entry) = (rounds p).map (·.entry)) :
    (⟨uLT (ckP .two) ds, out⟩ : Reduction Aa Bb).Leads on
      (RowTopSays P0A (attLin x S tl D rad Ex Wp α ns0 (numsPlan p.own k0)) ns0 (numsPlan p.own k0) rows S
        (endLay P0A (attLin x S tl D rad Ex Wp α ns0 (numsPlan p.own k0)) ns0 (numsPlan p.own k0)
          (cellAtt x S tl) S.ls S.cf.lmS j0)
        (meantQ P0A (attLin0 x S tl D rad) ns0 (numsPlan p.own k0)
          (attQ0 x S tl D rad Ex Wp α ns0 (numsPlan p.own k0)))
        seat p.own recA recB x0 mOf zk)
      (bearErr ds _ (((closedOf P0A (attLin x S tl D rad Ex Wp α ns0 (numsPlan p.own k0)) ns0
        (numsPlan p.own k0)).own (theMeans Cb.Gl.E _ _ _)).ch.eps Ex)) :=
  K05_row_any (baseIs_att x S tl D rad) hid PL (attLin0 x S tl D rad) seat p ns0 k0
    (attQ0 x S tl D rad Ex Wp α ns0 (numsPlan p.own k0)) j0 rows UW UM UD hrec Ex ds out recA recB x0 yOf mOf zx zy zk on
    hon hk3 hyes hpass hd he rfl

open Classical in
/-- **The same from one Boolean test on the plan**: planOkAll pays PlanLaw and the three public
records on units. -/
theorem K05_row_att_plan {St Aa Bb : Type} {lid : ℕ} {cf : Attention.Cfg}
    (hid : Attention.shapeHid lid cf = Except.ok (S, x.fs)) (hp : planOkAll cf S x.fs = true) (seat : Seat St) (p : Par)
    (ns0 k0 : ℕ) (j0 : NameJ (OnBytes.Road.L5.dimOf S) S.ls S.cf.lmS) (rows : ℕ)
    (hrec : p.own = recOf (closedOf P0A (attLin x S tl D rad Ex Wp α ns0 (numsPlan p.own k0)) ns0
      (numsPlan p.own k0)) rows) (ds : List RDT)
    (out : Aa → Tr (uLT (ckP .two) ds) → Option Bb) (recA : Aa → St) (recB : Bb → St)
    (x0 : Aa → TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl))) (yOf : Aa → Ex.Str)
    (mOf : Aa → (attSg x D rad).Msg) (zx zy : Aa → Array E) (zk : Aa → Array (Array E)) (on : Aa → Prop)
    (hon : ∀ a, on a → ∀ F, seat.ledger (recA a) = some F → Sized F ∧ F.ns = ns0 ∧ F.next = k0)
    (hk3 : ∀ a, on a → K3Pts x.fs (zx a) (zy a) (zk a) (x0 a).2.1.pt)
    (hyes : ∀ a τ b, on a → out a τ = some b →
      decide seat p (recA a) ((rvT (ckP .two) ds τ).map noDigest) = .ok (recB b) ∧
        roundsFit (rounds p) ((rvT (ckP .two) ds τ).map noDigest) = true ∧
        ∀ r ∈ (rvT (ckP .two) ds τ).map noDigest, ∀ x ∈ r.drawn.elems, Fmt.Fld.two.okE x = true)
    (hpass : ∀ a τ b, out a τ = some b → passT (ckP .two) ds (rhoT (ckP .two) ds τ) = true)
    (hd : ∀ d ∈ ds, Plain (toRD d)) (he : ds.map (·.entry) = (rounds p).map (·.entry)) :
    (⟨uLT (ckP .two) ds, out⟩ : Reduction Aa Bb).Leads on
      (RowTopSays P0A (attLin x S tl D rad Ex Wp α ns0 (numsPlan p.own k0)) ns0 (numsPlan p.own k0) rows S
        (endLay P0A (attLin x S tl D rad Ex Wp α ns0 (numsPlan p.own k0)) ns0 (numsPlan p.own k0)
          (cellAtt x S tl) S.ls S.cf.lmS j0)
        (meantQ P0A (attLin0 x S tl D rad) ns0 (numsPlan p.own k0)
          (attQ0 x S tl D rad Ex Wp α ns0 (numsPlan p.own k0)))
        seat p.own recA recB x0 mOf zk)
      (bearErr ds _ (((closedOf P0A (attLin x S tl D rad Ex Wp α ns0 (numsPlan p.own k0)) ns0
        (numsPlan p.own k0)).own (theMeans Cb.Gl.E _ _ _)).ch.eps Ex)) :=
  K05_row_any_plan (baseIs_att x S tl D rad) hid hp (attLin0 x S tl D rad) seat p ns0 k0
    (attQ0 x S tl D rad Ex Wp α ns0 (numsPlan p.own k0)) j0 rows hrec Ex ds out recA recB x0 yOf mOf zx zy zk on hon hk3
    hyes hpass hd he rfl

end Tower

section Planned
variable (x : VerifiableInference.Desc.First.Look.Place) (tl : HTailF2) (D : Sent)
  (rad : OracleShape → Nat) (Ex : Iop.ExtSpec) (Wp : Type)
  (α : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl)) → Cb.Gl.E)

open Classical in
/-- **The kind's law in the form for the table of joints, at the parameters beside the closed
caller**, at a plan that the planner returns: K05_keepsW_any_one there, in one line. -/
theorem K05_keepsW_att {St Aa Bb W : Type} {settings : Model.Settings} {i : Attention.In}
    {cf : Attention.Cfg} {A : Attention.Plan} (hA : Attention.plan settings i cf = Except.ok A)
    (hfs : x.fs = A.fs) (hok : planOkAll cf A.S A.fs = true)
    (seat : Seat St) (p : Par) (hp : p.own = A.own) (ns0 k0 : ℕ)
    (j0 : NameJ (OnBytes.Road.L5.dimOf A.S) A.S.ls A.S.cf.lmS)
    (ds : List RDT) (out : Aa → Tr (uLT (ckP .two) ds) → Option Bb) (recA : Aa → St) (recB : Bb → St)
    (x0 : Aa → TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl))) (yOf : Aa → Ex.Str) (zx zy : Aa → Array E) (zk : Aa → Array (Array E)) (on : Aa → Prop)
    (kr : ℕ) (hroom : ∀ a, on a → ∀ F, seat.ledger (recA a) = some F → Room F ns0 k0 kr)
    (hk3 : ∀ a, on a → K3Pts A.fs (zx a) (zy a) (zk a) (x0 a).2.1.pt)
    (hyes : ∀ a τ b, on a → out a τ = some b →
      decide seat p (recA a) ((rvT (ckP .two) ds τ).map noDigest) = .ok (recB b) ∧
        roundsFit (rounds p) ((rvT (ckP .two) ds τ).map noDigest) = true ∧
        ∀ r ∈ (rvT (ckP .two) ds τ).map noDigest, ∀ x ∈ r.drawn.elems, Fmt.Fld.two.okE x = true)
    (hpass : ∀ a τ b, out a τ = some b → passT (ckP .two) ds (rhoT (ckP .two) ds τ) = true)
    (hd : ∀ d ∈ ds, Plain (toRD d)) (he : ds.map (·.entry) = (rounds p).map (·.entry))
    (part : W → (attSg x D rad).Msg) (mOf : Aa → (attSg x D rad).Msg) (on' : Bb → Prop) (R' : Bb → W → Prop)
    (hon' : ∀ a τ b, on a → out a τ = some b → on' b)
    (hb : BillsTop (attBase x A.S tl D rad) (attLin x A.S tl D rad Ex Wp α ns0 (numsPlan p.own k0)) ns0 (numsPlan p.own k0) A.own.rows A.S
      (endLay (attBase x A.S tl D rad) (attLin x A.S tl D rad Ex Wp α ns0 (numsPlan p.own k0)) ns0 (numsPlan p.own k0) (cellAtt x A.S tl) A.S.ls A.S.cf.lmS j0) (meantQ (attBase x A.S tl D rad) (attLin0 x A.S tl D rad) ns0 (numsPlan p.own k0)
        (attQ0 x A.S tl D rad Ex Wp α ns0 (numsPlan p.own k0)))
      seat p.own recA recB x0 zk part R')
    (pin : ∀ a τ b w, on a → out a τ = some b → R' b w → part w = mOf a) :
    (⟨uLT (ckP .two) ds, out⟩ : Reduction Aa Bb).KeepsW on on'
      (fun a w => ((closedOf (attBase x A.S tl D rad) (attLin x A.S tl D rad Ex Wp α ns0 (numsPlan p.own k0)) ns0 (numsPlan p.own k0)).own (theMeans Cb.Gl.E _ _ _)).ch.Todo (x0 a) (part w)) R'
      (bearErr ds _ (((closedOf (attBase x A.S tl D rad) (attLin x A.S tl D rad Ex Wp α ns0 (numsPlan p.own k0)) ns0 (numsPlan p.own k0)).own (theMeans Cb.Gl.E _ _ _)).ch.eps Ex)) :=
  K05_keepsW_any_one hA (hfs ▸ baseIs_att x A.S tl D rad) hok (attLin0 x A.S tl D rad) seat p hp ns0 k0
    (attQ0 x A.S tl D rad Ex Wp α ns0 (numsPlan p.own k0)) j0 Ex ds out recA recB x0 yOf zx zy zk on kr hroom hk3 hyes
    hpass hd he rfl part mOf on' R' hon' hb pin

end Planned

end VerifiableInference.Desc.First.Att.P
