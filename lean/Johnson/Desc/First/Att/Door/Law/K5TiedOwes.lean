-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/K5TiedOwes.lean: kind K5: **ONE THEOREM FROM K5Owes TO THE TIE IN
THE TABLE's SECOND FORM AT THE NARROWER FILLING**: the chain K5Owes → K5Left → K5AtMg → SeatLaws →
TiedAt at the wider filling → TiedAtR at Mg, joined: k5AtMg_plus
(Johnson/Desc/First/Att/Door/Law/K5AtMgPaid.lean) handed to k5_tiedAtR_plus
(Johnson/Desc/First/Att/Door/Law/K5TiedPlus.lean), at one place of the kind.

IS IT EMPTY HERE? AN IMPLICATION. NO MEMBER OF ITS PREMISES IS SHOWN: whether they can be met
together, at the composed meaning's term (mgAll, Sound/MgAll.lean) or anywhere, is shown nowhere.
The conclusion is the sentence that KindTiedR (Sound/TiedR.lean) asks at one place of the kind.

Main name: `k5_tiedAtR_owes`.
ITS PREMISES, BY SORT: (1) four structures of equations AT THE WIDER FILLING mgPlus Mg Mg0.more D Ld
Ms Mg0.pub Dn.codes (Mg0: the composed filling's base: one pair of letters):
MgIs · MgGains · DataIs · DataSent · (2) on the plan: PlanIs · profile 4 · Wv.A[g] · two
returns of lookAt · K5Plan · (3) on the table: K5Place · ps[k], ps[k + 1] · K5Book · the row's asks
are open · readsOpen · rowsApart · ridersB · (4) K5Owes, at O, Q := what is open at border k (Q: at
the wider list) and at the base of the piece · (5) on the description's piece q: q.back = [] · q.err
· RoundAsG · SeatOf · hq · an extractor that lays nothing · the seats lie below q.base · (6) the
bridge's: hpub · Facts5 · the sixth and the seventh fact at border k, under the narrower promise ·
the test on the two lists at k and k + 1 · hopen' · HandsOn. Nothing is claimed on
soundness, completeness or hiding.
-/
import Johnson.Desc.First.Att.Door.Law.K5AtMgPaid
import Johnson.Desc.First.Att.Door.Law.K5TiedPlus

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Door
open Cb Cb.Fo Cb.LdLkp OnBytes OnBytes.Model OnBytes.Model.Road OnBytes.Maker OnBytes.Flat Johnson.Pack Run
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look (Sent JAtt lookAt sigListCalls)
open VerifiableInference.Desc.K13.Law (DataK13)
open VerifiableInference.Desc.First.Att.P
open VerifiableInference.Desc.K12.Door (Laid)
open OnBytes.Road.L5 (Zs)

open Classical in
/-- **From K5Owes to the tie in the second form, at one place of the kind.** -/
theorem k5_tiedAtR_owes {Pp Xi Cells Tok Cl Ix : Type} [Nonempty Pp] {nR : ℕ} {Fr : Frame}
    (Mg Mg0 : Meaning Pp (Wit Cells Tok MsgT)) (D : PubData) (Dn : Sent)
    (G0 : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
    (smp : Pp × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf Dn.codes s.l).om i).Smp) (ms : List Mem)
    (decT : (ℕ → Option (ℕ × List UInt64)) → Pp × S → Option Cells) (in0 : Pp × S → Bool) (c5 : Pp → Bool)
    (Ld : Laid) (Ms : List OracleShape) (D13 : DataK13 Pp (Wit Cells Tok MsgT) nR)
    (E : MgIs (mgPlus Mg Mg0.more D Ld Ms Mg0.pub Dn.codes) Mg0 D Dn.codes G0 arr smp ms decT in0 c5 Ld Ms D13)
    (q : Piece (ckP .two) Fr (Pp × S) Claim (Wit Cells Tok MsgT)) (hback : q.back = [])
    (herr : q.err = Iop.Err.cap 128 (uLT (ckP .two) q.ds))
    (claim : Aff → Cl) (Wv : Verify.Public) (g : ℕ) (before : List (ℕ × ℕ)) (a : Attention.Plan) (x xd : Look.Place)
    (links : List ModelPart) (T : DataIs D Wv links (2 * g + 1)) (Sn : DataSent D Dn.codes Dn)
    (hP : PlanIs Wv) (h4 : Wv.p4 = true) (ha : Wv.A[g]? = some a) (hx : lookAt Wv (2 * g + 1) false = some x)
    (hxd : lookAt Wv (2 * g + 1) true = some xd)
    (pl pl' : VerifiableInference.Desc.Place) (Ix5 : K5Place links (2 * g + 1) pl pl')
    (rad : OracleShape → Nat) (Ex : Iop.ExtSpec) (Wp : Type)
    (α : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns a.seam.tl)) → Cb.Gl.E) (plJ : ℕ → ℕ → JAtt x.ns a.seam.tl)
    (yOf : S × Fr.E.Str → Ex.Str)
    (uL uH : ℕ → UFn) (wt : ℕ → Pp × S → Strs → Wit Cells Tok MsgT → Prop)
    (seat : Fin (sigListCalls Dn rad x.link).length → ℕ × ℕ)
    (G : MgGains (mgPlus Mg Mg0.more D Ld Ms Mg0.pub Dn.codes) Dn.codes arr ms D.Rd D.runs (Stated.of (uBySort uL (uArm Wv) uH)) D.N wt (2 * g + 1) x
      a.S a.seam.tl Dn rad seat arr)
    (ps : List VerifiableInference.Desc.Place) (k : ℕ) (hk : ps[k]? = some pl) (hk' : ps[k + 1]? = some pl')
    (smpR : Array OnBytes.Oracle × OnBytes.TreeBook → (i : Fin (sigListCalls Dn rad x.link).length) →
      Option ((sigOf Dn.codes (sigListCalls Dn rad x.link)).om i).Smp)
    (hlow : ∀ i, (seat i).1 < q.base)
    (lk : ℕ → Option (Link S Claim)) (Lk : Link S Claim) (same : S → S → Bool) (blk : Block S Claim)
    (claimC : Aff → Claim) (nm : String)
    (Hd : Cells → Ix → Prop) (bsW : ℕ → Wit Cells Tok MsgT → Prop)
    (dP : ℕ → Pp × S → Strs → Wit Cells Tok MsgT → Prop) (body : ℕ → First.Part → Ix → Pp × S → Strs → Wit Cells Tok MsgT → Prop)
    (Zof : Wit Cells Tok MsgT → Zs)
    (Ow : K5Owes (Fr := Fr) (mgPlus Mg Mg0.more D Ld Ms Mg0.pub Dn.codes) Mg0 D Dn arr smp ms decT in0 Ld Ms D13 q.base Wv g before a x links pl
      rad ((openSets links ps (start links))[k]?.getD []) ((pubSets (morePlus Mg0.more) links ps)[k]?.getD [])
      seat smpR lk Lk same blk claimC nm Hd bsW dP body Zof)
    (hds : List.Forall₂ RoundAsG q.ds (rounds (parO Wv (2 * g + 1) a before)))
    (hS : Forest.Shape) (kr : ℕ) (Bk : K5Book D.N pl pl')
    (Pn : K5Plan (parO Wv (2 * g + 1) a before).own (2 * g + 1) (Look.P.ofPlace (Params.settingOf Wv.P.frame) false x)
      (Look.P.ofPlace (Params.settingOf Wv.P.frame) true xd) hS (Forest.elems a.fs) kr a.ns)
    (hQ : ∀ t ∈ (pubRowOf links pl).asks, t ∈ ((pubSets (morePlus Mg0.more) links ps)[k]?.getD []))
    (hr : readsOpen links ps (start links) = true) (hap : rowsApart links ps = true) (hB : ridersB links ps k (2 * g + 1) = true)
    (B : Block S Claim) (hSeat : SeatOf blk B) (hq : q.b = (below B).lift Prod.snd fun t s => (t.1, s))
    (Ee : (Pp × S) × Fr.E.Str → (Pp × S) × Fr.E.Str → Wit Cells Tok MsgT → Wit Cells Tok MsgT) (hEe : ∀ u v w, Ee u v w = w)
    (Rch : ℕ → (Pp × S) × Fr.E.Str → Prop) (hpub : Mg.pub = pubAll D Mg0.pub)
    (F : Facts5 (fun u : Pp × S => u) D Ld Ms Dn.codes Rch)
    (hbare : ∀ u, Rch k u → onQ D.N Mg links ps (fun u => u) k u → u.1.2.failed = none → bareAttB u.1.2 = true)
    (hleft : ∀ u, Rch k u → onQ D.N Mg links ps (fun u => u) k u → u.1.2.failed = none → leftAttB u.1.2 = true)
    (hD : doorsFitB Mg.more (morePlus Mg0.more) isWideQ links ps k = true)
    (hD' : doorsFitB Mg.more (morePlus Mg0.more) isWideQ links ps (k + 1) = true)
    (hopen' : ∀ t ∈ (pubSets (morePlus Mg0.more) links ps)[k + 1]?.getD [],
      t ∈ (pubSets Mg.more links ps)[k + 1]?.getD [] ∨ isThreeQ t = true)
    (hs : HandsOn Rch k q) :
    TiedAtR D.N Mg links ps (fun u => u) Rch k (q.withMap Ee) := by
  obtain ⟨x0, gOf, H⟩ := k5AtMg_plus (mgPlus Mg Mg0.more D Ld Ms Mg0.pub Dn.codes) Mg0 D Dn G0 arr smp ms decT in0 c5 Ld Ms D13 E q.base claim Wv g before a x
    links T Sn hP h4 ha hx Ix5 rad Ex Wp α plJ _ _ uL uH wt seat G ps k hk smpR hlow lk Lk same blk claimC nm Hd bsW dP body Zof Ow xd hxd
  exact k5_tiedAtR_plus q hback herr claim hP h4 g (2 * g + 1) rfl before blk Ow.seated Ow.seatedOk Ow.guard ha hx Dn rad Ex Wp α a.ns hds []
    x0 yOf gOf plJ (k5Pin (Cells := Cells) (Tok := Tok) G0 x Dn rad seat smpR arr Fr q.base hlow)
    (fun π => relAt (meansQ (Fr := Fr) D.N (mgPlus Mg Mg0.more D Ld Ms Mg0.pub Dn.codes) fun s => (π, s)) (outsQ links ps k)) D.N Mg Mg0.more D Ld Ms Mg0.pub Dn.codes
    links pl pl' _ _ _ _ hS _ _ kr _ Ix5 Bk Pn hQ ps k hk hk' rfl rfl (fun _ => rfl) hr hap hB H B hSeat hq Ee hEe Rch hpub F hbare hleft hD
    hD' hopen' hs

end H2K5.Door

#print axioms H2K5.Door.k5_tiedAtR_owes
