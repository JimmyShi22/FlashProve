-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/K05LawPin.lean: KIND K5's LAW IN ONE STATEMENT AT THE SEATED BLOCK, WITH THE
PIN FILLED: the item that pins the world's part is the rule of composition's pin by a decoder with a
sample (pinItemOf, Johnson/Desc/Sound/PinItemFill.lean).

Main names:
  `k5Pin`: pinItemOf at the codes D.codes, the list sigListCalls D rad x.link (the kept oracle
    messages that are sent anew in the link's first message, then the link's own of moment 0, each
    with its radius) and the hearing's seat seatSO. Its type is PinItemP … (attSg x D rad).Msg by
    unfolding: attSg is Johnson.Pack.sigOf at these two. Its field "lay" is
    seatSO_keeps_oracles_book (Att/K05SeatKeepsPin.lean).
  `K05_law_one_pin`: **K05_law_one_guard (Att/K05LawGuard.lean) at I := k5Pin …**, with K5AtOn and
    K5Behind opened into what is left: FOUR PREMISES: left · promise · worth · pinned.
WHAT FELL: K5AtOn's "ok": the pin fixes outright (pinItemOf_ok). WHAT K5Behind's "item" BECAME:
"pinned": behind the kind's rounds every member of that list is pinned at the record's oracle
messages and book and the frame's strings. LETTERS THAT STAY FREE: Gd (a description), seat, smp,
arr; D and rad (see Att/K05LawGuard.lean's head). SILLY FILLINGS ARE NOT SHUT OUT BY THE FORM: at
smp := none nothing is pinned: then "pinned" is false wherever R' has a witness, and the law is to
be had at R' := False alone. That sigListCalls D rad x.link with its seats is an entry of a border's
own lists of members is tied by nobody: rad is a function of the shape; the library's radii hang on
a message's group. All that Att/K05LawGuard.lean's head says of what is left on the public side, of
the bare block and of emptiness holds here.
No soundness of the protocol is claimed: the premises named are not shown.
Nothing is claimed on completeness or hiding.

-/
import Johnson.Desc.First.Att.K05LawGuard
import Johnson.Desc.First.Att.K05SeatKeepsPin
import Johnson.Desc.Sound.PinItemFill

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb IOR TWhole Cb.Fo Cb.LdLkp Cb.Pv.Att Cb.Pv.Att.End Inst.Model Inst.Model.AttSeg
open OnBytes OnBytes.Model OnBytes.Model.Road
open OnBytes.Slice OnBytes.Flat OnBytes.Maker Run Fo.Peel
open VerifiableInference.Desc.First.Look (Sent attCaller attSg JAtt AttOK enMask lookAt
  sigListCalls)
open VerifiableInference.Desc.Sound (Frame Piece pinItemOf PinAt MsgT strsOf)
open VerifiableInference.Desc (Claim RoundAsG FileDescription Wit)

/-- **The pin at K5's place.** -/
def k5Pin {Xi : Type} (Gd : FileDescription Xi) (x : VerifiableInference.Desc.First.Look.Place) (D : Sent)
    (rad : OracleShape → Nat) (seat : Fin (sigListCalls D rad x.link).length → ℕ × ℕ)
    {Cells Tok : Type}
    (smp : Array OnBytes.Oracle × OnBytes.TreeBook → (i : Fin (sigListCalls D rad x.link).length) →
      Option ((Johnson.Pack.sigOf D.codes (sigListCalls D rad x.link)).om i).Smp)
    (arr : ℕ → ℕ → ℕ) (Fr : Frame) (base : ℕ) (hlow : ∀ i, (seat i).1 < base) :
    PinItemP Fr seatSO base (Wit Cells Tok MsgT) (attSg x D rad).Msg :=
  pinItemOf Gd D.codes (sigListCalls D rad x.link) seat smp arr Fr seatSO base hlow
    seatSO_keeps_oracles_book

open Classical in
/-- **KIND K5's LAW AT THE SEATED BLOCK, WITH THE PIN FILLED.** -/
theorem K05_law_one_pin {Cl Xi Cells Tok : Type} {Fr : Frame} (claim : Aff → Cl) (Gd : FileDescription Xi) {Wv : Verify.Public}
    (hP : PlanIs Wv) (h4 : Wv.p4 = true) (g : ℕ) (before : List (ℕ × ℕ))
    (blk : VerifiableInference.Desc.Block First.S Claim)
    (hblk : k5AtN Wv (2 * g + 1) g before = some blk) (hok : blk.planOk = true)
    (hG : k5GuardN Wv (2 * g + 1) g = true) {a : Attention.Plan} (ha : Wv.A[g]? = some a)
    {x : VerifiableInference.Desc.First.Look.Place} (hx : lookAt Wv (2 * g + 1) false = some x) (D : Sent)
    (rad : OracleShape → Nat) (Ex : Iop.ExtSpec) (Wp : Type)
    (α : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns a.seam.tl)) → Cb.Gl.E) (ns base : ℕ)
    (ds : List RDT) (hds : List.Forall₂ RoundAsG ds (rounds (parO Wv (2 * g + 1) a before)))
    (tj : OnBytes.K.Kc.Tape)
    (x0 : First.S × Fr.E.Str → TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns a.seam.tl)))
    (yOf : First.S × Fr.E.Str → Ex.Str) (gOf : First.S × Fr.E.Str → Forest.Heard)
    (pl : ℕ → ℕ → JAtt x.ns a.seam.tl) (on : First.S × Fr.E.Str → Prop)
    (seat : Fin (sigListCalls D rad x.link).length → ℕ × ℕ)
    (smp : Array OnBytes.Oracle × OnBytes.TreeBook → (i : Fin (sigListCalls D rad x.link).length) →
      Option ((Johnson.Pack.sigOf D.codes (sigListCalls D rad x.link)).om i).Smp)
    (arr : ℕ → ℕ → ℕ) (hlow : ∀ i, (seat i).1 < base) (Rd : Rides Fr base)
    (R' : First.S × Fr.E.Str → Wit Cells Tok MsgT → Prop)
    (left : ∀ a', on a' → K3LeftOutIs (VerifiableInference.Desc.K3.seatCalls claim).fork
      (VerifiableInference.Desc.K3.seatCalls claim).heard x.fs x.lm x.F.next
      (Cb.Fo.NumsEq.placeOf (enMask x.ns a.seam.tl) pl)
      (fun F => Room F ns x.F.next
        (Forest.elems x.fs + (slotsOf (script (parO Wv (2 * g + 1) a before).own) + 0)))
      (x0 a') (gOf a') a'.1)
    (promise : ∀ a', on a' → Rd.q (Rd.rq a'.1) a'.2)
    (worth : BillsWorthJ x a.seam.tl D rad Ex Wp α a.S ns
      (numsPlan (parO Wv (2 * g + 1) a before).own (x.F.next + Forest.elems x.fs))
      { a with NC := a.S.calls.size } (plannedK a) (padOfO a.fs) a.nW tj gOf
      (fun a' => lookOfO (parCOf a).geo.lmb (gOf a')) seatSO (parO Wv (2 * g + 1) a before).own
      (fun a' : First.S × Fr.E.Str => a'.1) (fun a' : First.S × Fr.E.Str => a'.1) on
      (k5Pin Gd x D rad seat smp arr Fr base hlow).part
      (fun b w => LaidBehind Fr seatSO (parO Wv (2 * g + 1) a before) base on b ∧ R' b w))
    (pinned : ∀ b w, LaidBehind Fr seatSO (parO Wv (2 * g + 1) a before) base on b → R' b w →
      ∀ i, PinAt Gd D.codes (sigListCalls D rad x.link) seat smp arr i (b.1.st.oracles, b.1.book)
        (strsOf Fr b.2) w) :
    (⟨blk, base, ds, [], fun _ _ w => w, Err.cap 128 (uLT (ckP .two) ds)⟩ :
        Piece (ckP .two) Fr First.S Claim (Wit Cells Tok MsgT)).GoodIn
      on (fun b => LaidBehind Fr seatSO (parO Wv (2 * g + 1) a before) base on b ∧
        Rd.q (Rd.rq b.1) b.2)
      (fun a' w => ((closedOf (attBase x a.S a.seam.tl D rad)
          (attLin x a.S a.seam.tl D rad Ex Wp α ns
            (numsPlan (parO Wv (2 * g + 1) a before).own (x.F.next + Forest.elems x.fs))) ns
          (numsPlan (parO Wv (2 * g + 1) a before).own (x.F.next + Forest.elems x.fs))).own
          (theMeans Cb.Gl.E _ _ _)).ch.Todo (x0 a') ((k5Pin Gd x D rad seat smp arr Fr base hlow).part w)) R' :=
  K05_law_one_guard claim hP h4 g before blk hblk hok hG ha hx D rad Ex Wp α ns base ds hds tj x0 yOf
    gOf pl on (k5Pin Gd x D rad seat smp arr Fr base hlow) Rd R'
    ⟨left, fun _ _ => trivial, promise⟩ ⟨worth, pinned⟩

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.k5Pin
#print axioms VerifiableInference.Desc.First.Att.P.K05_law_one_pin
