-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/TailPlaces.lean: the law that ties a run of the Lean verifier's routine to the typed
block, at three places of a link of the first proof chain: the sending of the reads, the draw of the
matrix of the smallness test, the sending of the digits.

Johnson/Top/H/RowMeet.lean states what is asked at one block and one written stretch (`PlaceAt`):
where the stretch's tests of work pass and the rounds that the run has still to take begin with the
stretch's, the stretch has an image under the block's maps, the block's verifier puts out a named
statement on it, and the rest is still to be taken. Here that law is shown at the two kinds of block
of the smallness test's first three places, from a success of the verifier's own routine on a view.
Definitions, statements and proofs.

Main names:
  `rngCarS d dR ho`: the maps from the written round of the draw to the round of `KTailRngOn`'s
    block; `rngCarS_fits`: the written round's error count bears the typed one's if it is at least
    the typed count times the sampler's own bound.
  `rngPlace`: the law at the draw, from a success of drawMatrixF. The statement behind is the
    statement before with the typed challenge of the written verifier message.
  `rngPlace_record`: the list that the routine has laid into its record is the list of that typed
    challenge.
  `sendCarS d₂ Q`, `sendCarS_fits`: the like for the two written rounds of a sending and the block
    of `kSendInto`.
  `sendPlace_of`: the law at a sending, from the fact that a run has taken just two rounds. The
    statement behind is the statement before with, for each member, its seed and answers as the
    readings Q give them; the implicit instance gets the words.
  `sendPlace`, `sendPlaceV`: so from a success of rootInH, and from a success of the sending block
    sendVerify itself.
  `fivePlace4`, `fivePlace5`, `fivePlace6`: the three laws at the callers of the record `Five`
    (Johnson/Top/H/TailFive.lean).

Limits: those of OnBytes/Tie/Pv/Tail/RngView.lean, SendRoot.lean and SendCarry.lean: the three
readings of a sending are letters; that a run reaches a routine with just these rounds still to be
taken is a premise of the law's own form. Nothing on the lookups or on the batching draw.
-/
import Johnson.Top.H.RowMeet
import Johnson.Top.H.TailFive
import OnBytes.Tie.Pv.Row.ViewT
import OnBytes.Tie.Pv.Tail.SendRoot
import OnBytes.Tie.Pv.Tail.SendCarry

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace KObj.TailRow
open KObj KObj.RowCar Iop Prob Cb IOR VerifiableInference.OnPublicFiles OnBytes OnBytes.Model
  OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.Tie.Pv.Row OnBytes.Tie.Pv.Tail Cb.Pv.Tail

section Rng
variable (d : TailCallerOn) (dR : RDT) (ho : OnlyTrits (rdOf dR) (d.c.s.columns * d.c.s.tau))

/-- The maps from the written round of the draw to the typed round. -/
noncomputable def rngCarS : CarryS (uLT (Run.ckP .two) [dR]) (KTailRngOn.blk d).R.shape :=
  (CarryS.step (fun _ => ((), ())) (fun _ c => chalTo (rdOf dR) (matOf d.c.s (rdOf dR) ho) c)
    (fun _ _ => CarryS.nil) :
      CarryS [(roundT (Run.ckP .two) dR).up] [IOR.drawRound (Dr d.c.s)])

/-- The written round's error count bears the typed one's. -/
theorem rngCarS_fits (hlog : dR.entry.logN ≤ 64) (e e' : ℕ)
    (h : e * (Run.bsRound .two dR.entry dR.kind).w ≤ e') :
    (rngCarS d dR ho).Fits ((e, ()) : ℕ × Unit) ((e', ()) : ℕ × Unit) :=
  ⟨⟨_, fun _ c' => chalTo_fib (rdOf dR) (matOf d.c.s (rdOf dR) ho)
    (matOf_inj d.c.s (rdOf dR) ho) hlog c', h⟩, fun _ _ => trivial⟩

/-- The law at the draw of the matrix. -/
theorem rngPlace (tl tl' : HTailF2) (F F' : Fork) (x x' : Ctx) (hc : PscRun.Clean x)
    (hr : tl.drawMatrixF F x = .ok ((tl', F'), x')) (m : (roundT (Run.ckP .two) dR).up.Msg)
    (c : (roundT (Run.ckP .two) dR).up.Chal)
    (a : (KTailRngOn.src d).X × (KTailRngOn.src d).E.Str) :
    PlaceAt (vT [dR]) (okT [dR]) (KTailRngOn.blk d) (rngCarS d dR ho)
      ((m, c, ()) : Tr (uLT (Run.ckP .two) [dR])) x.ch.left a x'.ch.left
      (((a.1.1, matOf d.c.s (rdOf dR) ho (valsOf (rdOf dR) c)), a.1.2), a.2) := by
  intro rest hok hp
  have hpass : GChal.pass (b := dR.entry.work) c = true := (okT_one dR m c).1 hok
  obtain ⟨-, rv, hR, -, -⟩ := drawMatrix_view tl tl' F F' x x' hc hr
  have e : rv :: x'.ch.left = rvOne dR m c :: rest := hR.2.2.symm.trans hp
  have e1 : chalTo (rdOf dR) (matOf d.c.s (rdOf dR) ho) c =
      some (matOf d.c.s (rdOf dR) ho (valsOf (rdOf dR) c)) := if_pos hpass
  refine ⟨((((), ()), matOf d.c.s (rdOf dR) ho (valsOf (rdOf dR) c), ()) :
    Tr [IOR.drawRound (Dr d.c.s)]), ?_, rfl, (List.cons.inj e).2⟩
  show (chalTo (rdOf dR) (matOf d.c.s (rdOf dR) ho) c).bind _ = _
  rw [e1]
  rfl

/-- The routine's own record holds the list of that typed challenge. -/
theorem rngPlace_record (tl tl' : HTailF2) (F F' : Fork) (x x' : Ctx) (hc : PscRun.Clean x)
    (hr : tl.drawMatrixF F x = .ok ((tl', F'), x')) (m : (roundT (Run.ckP .two) dR).up.Msg)
    (c : (roundT (Run.ckP .two) dR).up.Chal) (rest : List Fmt.RoundView)
    (hp : x.ch.left = vT [dR] ((m, c, ()) : Tr (uLT (Run.ckP .two) [dR])) ++ rest) :
    tl'.cfF = listOf (matOf d.c.s (rdOf dR) ho (valsOf (rdOf dR) c)) := by
  obtain ⟨-, rv, hR, -, rfl⟩ := drawMatrix_view tl tl' F F' x x' hc hr
  have e : rv :: x'.ch.left = rvOne dR m c :: rest := hR.2.2.symm.trans hp
  obtain rfl := (List.cons.inj e).1
  exact drawn_view d.c.s (rdOf dR) ho c

end Rng

section Send
variable (cS : SendCaller GE) {d₁ : RDT} (d₂ : RDT) (Q : SendRead d₁ cS.s)

/-- The maps from the two written rounds of a sending to the two typed rounds. -/
noncomputable def sendCarS :
    CarryS (uLT (Run.ckP .two) [d₁, d₂]) ((kSendInto [cS]).block cS).R.shape :=
  (CarryS.step (fun m => (Q.words m, ())) (fun _ c => chalTo (rdOf d₁) Q.seed c) (fun _ _ =>
    CarryS.step (fun m₂ => ((), Q.anOf (ansT d₂ m₂)))
      (fun _ c₂ => chalTo (rdOf d₂) (fun _ => ()) c₂) (fun _ _ => CarryS.nil)) :
      CarryS [(roundT (Run.ckP .two) d₁).up, (roundT (Run.ckP .two) d₂).up] (cS.s.N.sh cS.s.Sd))

/-- The written rounds' error counts bear the typed ones'. -/
theorem sendCarS_fits (hinj : Function.Injective Q.seed) (h₂ : OnlyTrits (rdOf d₂) 0)
    (hl₁ : d₁.entry.logN ≤ 64) (hl₂ : d₂.entry.logN ≤ 64) (e₁ e₂ e₁' e₂' : ℕ)
    (g₁ : e₁ * (Run.bsRound .two d₁.entry d₁.kind).w ≤ e₁')
    (g₂ : e₂ * (Run.bsRound .two d₂.entry d₂.kind).w ≤ e₂') :
    (sendCarS cS d₂ Q).Fits ((e₁, e₂, ()) : ℕ × ℕ × Unit) ((e₁', e₂', ()) : ℕ × ℕ × Unit) :=
  ⟨⟨_, fun _ c' => chalTo_fib (rdOf d₁) Q.seed hinj hl₁ c', g₁⟩, fun _ _ =>
    ⟨⟨_, fun _ c' => chalTo_fib (rdOf d₂) (fun _ => ())
      (fun _ _ _ => bitsL_inj h₂ (funext fun i => i.elim0)) hl₂ c', g₂⟩, fun _ _ => trivial⟩⟩

/-- The law at a sending, from the fact that a run has taken just two rounds. -/
theorem sendPlace_of (x x' : Ctx) (r₁ r₂ : Fmt.RoundView) (hT : x.ch.left = r₁ :: r₂ :: x'.ch.left)
    (m₁ : (roundT (Run.ckP .two) d₁).up.Msg) (w₁ : (roundT (Run.ckP .two) d₁).up.Chal)
    (m₂ : (roundT (Run.ckP .two) d₂).up.Msg) (w₂ : (roundT (Run.ckP .two) d₂).up.Chal)
    (a : cS.X × cS.E₀.Str) :
    PlaceAt (vT [d₁, d₂]) (okT [d₁, d₂]) ((kSendInto [cS]).block cS) (sendCarS cS d₂ Q)
      ((m₁, w₁, m₂, w₂, ()) : Tr (uLT (Run.ckP .two) [d₁, d₂])) x.ch.left a x'.ch.left
      ((a.1, fun i => (cS.s.Sd.sd i (Q.seed (valsOf (rdOf d₁) w₁)), Q.anOf (ansT d₂ m₂) i)),
        (a.2, Q.words m₁)) := by
  intro rest hok hp
  obtain ⟨p₁, p₂⟩ := (okT_two d₁ d₂ m₁ w₁ m₂ w₂).1 hok
  have e : r₁ :: r₂ :: x'.ch.left = rvOne d₁ m₁ w₁ :: rvOne d₂ m₂ w₂ :: rest :=
    hT.symm.trans hp
  have e₁ : chalTo (rdOf d₁) Q.seed w₁ = some (Q.seed (valsOf (rdOf d₁) w₁)) := if_pos p₁
  have e₂ : chalTo (rdOf d₂) (fun _ => ()) w₂ = some () := if_pos p₂
  refine ⟨(((Q.words m₁, ()), Q.seed (valsOf (rdOf d₁) w₁), ((), Q.anOf (ansT d₂ m₂)), (), ()) :
    Tr (cS.s.N.sh cS.s.Sd)), ?_, rfl, (List.cons.inj (List.cons.inj e).2).2⟩
  show (chalTo (rdOf d₁) Q.seed w₁).bind (fun c' =>
    ((chalTo (rdOf d₂) (fun _ => ()) w₂).bind fun c'' => (some ()).map fun τ' =>
      (((), Q.anOf (ansT d₂ m₂)), c'', τ')).map fun τ' => ((Q.words m₁, ()), c', τ')) = _
  rw [e₁, e₂]
  rfl

/-- The law at a sending of a later moment of a link, from a success of rootInH. -/
theorem sendPlace (trees : List Nat) (L L' : LinkCtx) (F F' : Fork) (x x' : Ctx)
    (hc : PscRun.Clean x) (hr : rootInH trees L F x = .ok ((((), L'), F'), x'))
    (m₁ : (roundT (Run.ckP .two) d₁).up.Msg) (w₁ : (roundT (Run.ckP .two) d₁).up.Chal)
    (m₂ : (roundT (Run.ckP .two) d₂).up.Msg) (w₂ : (roundT (Run.ckP .two) d₂).up.Chal)
    (a : cS.X × cS.E₀.Str) :
    PlaceAt (vT [d₁, d₂]) (okT [d₁, d₂]) ((kSendInto [cS]).block cS) (sendCarS cS d₂ Q)
      ((m₁, w₁, m₂, w₂, ()) : Tr (uLT (Run.ckP .two) [d₁, d₂])) x.ch.left a x'.ch.left
      ((a.1, fun i => (cS.s.Sd.sd i (Q.seed (valsOf (rdOf d₁) w₁)), Q.anOf (ansT d₂ m₂) i)),
        (a.2, Q.words m₁)) := by
  obtain ⟨ids, r₁, r₂, shapes, seeds, ans, T⟩ := rootInH_view trees L L' F F' x x' hc hr
  exact sendPlace_of cS d₂ Q x x' r₁ r₂ T.left m₁ w₁ m₂ w₂ a

/-- The same law from a success of the sending block itself, with a round of its own for the
answers: for a sending that no link's routine calls. -/
theorem sendPlaceV (notices : Array OracleNotice) (ids : Array Nat) (x x' : Ctx)
    (hc : PscRun.Clean x) (hr : (sendVerify notices true).Yields x ids x')
    (m₁ : (roundT (Run.ckP .two) d₁).up.Msg) (w₁ : (roundT (Run.ckP .two) d₁).up.Chal)
    (m₂ : (roundT (Run.ckP .two) d₂).up.Msg) (w₂ : (roundT (Run.ckP .two) d₂).up.Chal)
    (a : cS.X × cS.E₀.Str) :
    PlaceAt (vT [d₁, d₂]) (okT [d₁, d₂]) ((kSendInto [cS]).block cS) (sendCarS cS d₂ Q)
      ((m₁, w₁, m₂, w₂, ()) : Tr (uLT (Run.ckP .two) [d₁, d₂])) x.ch.left a x'.ch.left
      ((a.1, fun i => (cS.s.Sd.sd i (Q.seed (valsOf (rdOf d₁) w₁)), Q.anOf (ansT d₂ m₂) i)),
        (a.2, Q.words m₁)) := by
  obtain ⟨r₁, r₂, shapes, seeds, ans, T⟩ := sendVerify_view notices ids x x' hc hr
  exact sendPlace_of cS d₂ Q x x' r₁ r₂ T.left m₁ w₁ m₂ w₂ a

end Send

section AtFive
variable {κ7 κ8 : KFam.{1}} (n : Five κ7 κ8)

/-- Place 4 at the record of Johnson/Top/H/TailFive.lean: the sending of the reads. -/
theorem fivePlace4 {d₁ : RDT} (d₂ : RDT) (Q : SendRead d₁ n.c4.s) (trees : List Nat)
    (L L' : LinkCtx) (F F' : Fork) (x x' : Ctx) (hc : PscRun.Clean x)
    (hr : rootInH trees L F x = .ok ((((), L'), F'), x'))
    (m₁ : (roundT (Run.ckP .two) d₁).up.Msg) (w₁ : (roundT (Run.ckP .two) d₁).up.Chal)
    (m₂ : (roundT (Run.ckP .two) d₂).up.Msg) (w₂ : (roundT (Run.ckP .two) d₂).up.Chal)
    (a : n.c4.X × n.c4.E₀.Str) :
    PlaceAt (vT [d₁, d₂]) (okT [d₁, d₂]) ((kSendInto [n.c4]).block n.c4) (sendCarS n.c4 d₂ Q)
      ((m₁, w₁, m₂, w₂, ()) : Tr (uLT (Run.ckP .two) [d₁, d₂])) x.ch.left a x'.ch.left
      ((a.1, fun i => (n.c4.s.Sd.sd i (Q.seed (valsOf (rdOf d₁) w₁)), Q.anOf (ansT d₂ m₂) i)),
        (a.2, Q.words m₁)) :=
  sendPlace n.c4 d₂ Q trees L L' F F' x x' hc hr m₁ w₁ m₂ w₂ a

/-- Place 5: the draw of the matrix. -/
theorem fivePlace5 (dR : RDT) (ho : OnlyTrits (rdOf dR) (n.c5.c.s.columns * n.c5.c.s.tau))
    (tl tl' : HTailF2) (F F' : Fork) (x x' : Ctx) (hc : PscRun.Clean x)
    (hr : tl.drawMatrixF F x = .ok ((tl', F'), x')) (m : (roundT (Run.ckP .two) dR).up.Msg)
    (c : (roundT (Run.ckP .two) dR).up.Chal)
    (a : (KTailRngOn.src n.c5).X × (KTailRngOn.src n.c5).E.Str) :
    PlaceAt (vT [dR]) (okT [dR]) (KTailRngOn.blk n.c5) (rngCarS n.c5 dR ho)
      ((m, c, ()) : Tr (uLT (Run.ckP .two) [dR])) x.ch.left a x'.ch.left
      (((a.1.1, matOf n.c5.c.s (rdOf dR) ho (valsOf (rdOf dR) c)), a.1.2), a.2) :=
  rngPlace n.c5 dR ho tl tl' F F' x x' hc hr m c a

/-- Place 6: the sending of the digits. -/
theorem fivePlace6 {d₁ : RDT} (d₂ : RDT) (Q : SendRead d₁ n.c6.s) (trees : List Nat)
    (L L' : LinkCtx) (F F' : Fork) (x x' : Ctx) (hc : PscRun.Clean x)
    (hr : rootInH trees L F x = .ok ((((), L'), F'), x'))
    (m₁ : (roundT (Run.ckP .two) d₁).up.Msg) (w₁ : (roundT (Run.ckP .two) d₁).up.Chal)
    (m₂ : (roundT (Run.ckP .two) d₂).up.Msg) (w₂ : (roundT (Run.ckP .two) d₂).up.Chal)
    (a : n.c6.X × n.c6.E₀.Str) :
    PlaceAt (vT [d₁, d₂]) (okT [d₁, d₂]) ((kSendInto [n.c6]).block n.c6) (sendCarS n.c6 d₂ Q)
      ((m₁, w₁, m₂, w₂, ()) : Tr (uLT (Run.ckP .two) [d₁, d₂])) x.ch.left a x'.ch.left
      ((a.1, fun i => (n.c6.s.Sd.sd i (Q.seed (valsOf (rdOf d₁) w₁)), Q.anOf (ansT d₂ m₂) i)),
        (a.2, Q.words m₁)) :=
  sendPlace n.c6 d₂ Q trees L L' F F' x x' hc hr m₁ w₁ m₂ w₂ a

end AtFive

end KObj.TailRow

#print axioms KObj.TailRow.rngCarS_fits
#print axioms KObj.TailRow.rngPlace
#print axioms KObj.TailRow.rngPlace_record
#print axioms KObj.TailRow.sendCarS_fits
#print axioms KObj.TailRow.sendPlace
#print axioms KObj.TailRow.sendPlaceV
#print axioms KObj.TailRow.fivePlace4
#print axioms KObj.TailRow.fivePlace5
#print axioms KObj.TailRow.fivePlace6
