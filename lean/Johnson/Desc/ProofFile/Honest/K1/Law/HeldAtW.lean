-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/HeldAtW.lean: the kind K1's sending of W (number 356 of the
first chain's flat list), under the library's head: if the samples' test holds at the state in
front, it holds at border 357 behind an accepting step, at a state in front that is reached and
passes the test on the book, at a meaning whose held is smpHeld. Beside the step no premise speaks
of the state behind.

What this file proves. Let h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x (the library's head,
Johnson/P5J/MgAtAll.lean), blk whatever stands at number 356 in the first chain's flat list, and s,
s' the states in front of and behind an accepting step of blk (IM.Yes).
  - samples_W_head: samplesHeld (Johnson/Desc/First/Borders.lean) at the numbers P5J.At.N Zp cF and
    the written lists IM.linksW and IM.placesW goes from border 356 at s to border 357 at s'. Its
    premises beside the step and the test in front: the meaning's held is smpHeld (hH); s is reached
    at number 356 of the flat list (hreach); the test on the book at s (hbk). The form is
    samples_later_head's (Johnson/Desc/ProofFile/Honest/K1/Law/HeldAtFifty.lean).
  - held_behind_send: for any sub-protocol that is a sending of the parameters P (IsSend) and leaves
    the book as a sending does (Booked): behind a yes of its decision the sample of each message
    with an out-of-domain (OOD) sample is held at the seat that the place makes, if the book in
    front fits (BookFits), has as many places as the statement has messages, and P passes PlanOwn.
  - Two facts on the written parameters parWF, by evaluation in Lean's kernel, with no premise.
    sampled_W: the message number 0 of W's sending has an OOD sample. sampled_W_first: not every
    message of that sending has one: so sampled_W's premise on the number is needed.
No thread, no prover and no proof file's bytes occur. No definition. Statements and proofs.

How it fits. A seat with a sample that is open at border 357 is the index masks' or W's (the field
two of the table's row: rowM4_head, Johnson/Desc/ProofFile/Honest/K1/Law/WAtHead.lean). The index
masks': their pin is open at border 356 (the field pinIn), so their sample is held in front, and it
stays (held4). W's: held_behind_send at the bare sub-protocol atM4 (whereOf Zp) (sendAtS (parWZ Zp
wMsgFull)), at message number 0, whose seat is the numbers' w (W_sits_atAll's second half).
held_W_at (Johnson/Desc/ProofFile/Honest/K1/Law/FormBehindTwo.lean) has the same first step; it is
not called, because it asks the row at the meaning's own extra rows, and no equation on these is
wanted here. That the book fits at a state reached at number 356: atFirstFits_all, which holds at
every border; bookFits_reached, which served the fifty, stops at number 353.

Proof that this file follows: held_new_later
(Johnson/Desc/ProofFile/Honest/K1/Law/HeldAtFifty.lean) in held_behind_send: its lines from the
sixth on, with the later places' two facts (IsSend, Booked) as premises. The two are one proof in
two places.

Kin on the seal. The same end, from other premises: smpHeld_of_sealed
(Johnson/Desc/K1/Law/HeldAtSending.lean), from Sealed at a string; held_new
(Johnson/Top/H0/Tw/K2C/HeldAtYes.lean), for the sending of the kind K2's switch. Of sampled_W_first:
sam_bites (Johnson/Desc/K1/Law/TiesWritten.lean), which names the seat of the mask's message.

Lemmas used beside these: msg_behind_send (Johnson/Desc/ProofFile/Honest/K1/Law/HeldAtFifty.lean);
size_behind (Johnson/Desc/K1/Law/GoodSend3.lean), oracleNoNew
(Johnson/Desc/K1/Law/OracleNoNew.lean), placed_of_fits (Johnson/Desc/Book/BookFits.lean), smpHeld_of
(Johnson/Top/H0/Tw/K2C/HeldAtYes.lean), seedReadsBack (Johnson/Desc/K1/Law/SeedReadsBack.lean);
k13_sits_flat (Johnson/Desc/AtSeats/K13SitsJoin.lean), Yes.under (Johnson/IMR/HandsDef.lean),
StepM4.decide, isSend_atM4, atM4_booked (Johnson/Desc/K13/Law/AtRecord.lean), held4
(Johnson/Desc/K13/Law/Others4AtSig.lean), planSitsB_iff (Johnson/Desc/K13/Law/SitsMade.lean),
PlanSits.pos (Johnson/Desc/K13/Law/SeatMade.lean); W_hm_atAll, W_sits_atAll, eW_atAll
(Johnson/Desc/K1/Law/TiesAtAll.lean), hOk_atAll (Johnson/Desc/K1/Law/TestsAtAll.lean), pin1_atAll,
pin2_atAll (Johnson/Desc/K1/Law/PinsAtHead.lean), planOwn_w (Johnson/Desc/K1/Law/PlanOwn.lean);
atFirstFits_all (Johnson/IMR/AtReach.lean), bookFitsB_iff (Johnson/Desc/Sound/BookTestsLaw.lean);
linksW_full, placesW_full (Johnson/IMR/K8Owed.lean); head_N_is
(Johnson/Desc/ProofFile/Honest/K1/Law/FiftyAtHead.lean); the opening from the head (LaidAt.opened,
Johnson/P5J/LaidOpens.lean).

Limits, the weightiest first.
  1. This file shows no value of the head h, and no state at which the premises of samples_W_head
    hold. That blk accepts anywhere is not shown here.
  2. hH, hreach and hbk are premises, the last two at the state in front. This file does not prove
    them.
  3. "Held" is a test on the verifier's state: sample rows lie in the statement, and a seed can be
    read back off the first. It does not say that the seed reads in the field (msg_behind_send's own
    limit).
  4. The meaning's field pubP at border 357 is not touched here. Nothing on the samples' test at
    number 2.
  5. At the full size's written lists and under IM.Open at the earlier hash OnBytes.secondHashFunction alone.
  6. The two closed facts are evaluations in Lean's kernel (decide +kernel) over the written
    parameters.
  7. Nothing on soundness, on completeness or on any other property.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.ProofFile.Honest.K1.Law.HeldAtFifty
import Johnson.Desc.ProofFile.Honest.K1.Law.WAtHead
import Johnson.Desc.K13.Law.Others4AtSig
import Johnson.Desc.Sound.BookTestsLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Block Chain Place smpHeld)
open VerifiableInference.Desc.First (S Numbers Meaning flatPlacesOf samplesHeld)
open VerifiableInference.Desc.Sound (linksFull moreAll)
open VerifiableInference.Desc.Book (BookFits placed_of_fits)
open VerifiableInference.Desc.K13 (whereOf atM4)
open VerifiableInference.Desc.K13.Law (wMsgFull StepM4)
open VerifiableInference.Desc.K1
open OnBytes.Maker (WholeD)
open Johnson.Desc.First.Walk.Tied (Reach)
open _root_.Desc.Plain

/-! ## 1 Two facts on the written parameters -/

/-- The message number 0 of W's sending has an OOD sample. -/
theorem sampled_W : ∀ j : Fin (shapesOf parWF).length, j.val = 0 → sampledAt parWF j := by
  decide +kernel

/-- **Not every message of that sending has one.** -/
theorem sampled_W_first : ¬ ∀ j : Fin (shapesOf parWF).length, sampledAt parWF j := by
  decide +kernel

/-! ## 2 Behind a sending -/

/-- **Behind a yes of a sending's decision the sample of each message with an OOD sample is held at
the seat that the place makes.** -/
theorem held_behind_send (P : K1.Par) {b : Block S ProofFile.Cl}
    (hS : IsSend P (fun s : S => s.st) b) {s s' : S} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (hd : b.decide s [r₁, r₂] gs = .ok s')
    (hB : Booked P s.book s.st.oracles.size s'.book s'.st.oracles.size)
    (hfull : s.book.place.size = s.st.oracles.size) (hfit : BookFits s.book) (hO : PlanOwn P)
    (j : Fin (shapesOf P).length) (hj : sampledAt P j) :
    smpHeld s'.st s'.book (s.book.trees.size + (layOf P).tree.getD j.val 0)
      ((layOf P).part.getD j.val 0) = true := by
  obtain ⟨L, dd, dd', owed, ids, hyes, hsame, hsize⟩ := hS _ _ _ _ _ hd
  obtain ⟨hc, y, zz, β, t, hy, e1, e2, e3⟩ :=
    msg_behind_send P owed dd dd' r₁ r₂ ids hyes j hj (hO.one j hj)
  have hl : (shapesOf P).length = P.sent.size := by simp [shapesOf]
  have hjlt : j.val < P.sent.size := hl ▸ j.isLt
  have hn : dd.st.oracles.size = s.st.oracles.size := by
    have a := size_behind P owed dd dd' r₁ r₂ ids hyes
    have a' := hB.msgs
    have c : s'.st.oracles.size = dd'.st.oracles.size := hsize
    rw [hl] at a
    omega
  have ho := oracleNoNew P _ _ _ _ hB hfull (placed_of_fits hfit) hO.part j.val hjlt
  have e := hsame.2 (dd.st.oracles.size + j.val)
  rw [hy] at e
  obtain ⟨y', hy', e⟩ := Option.map_eq_some_iff.1 e
  obtain ⟨f1, f23⟩ := Prod.mk.inj e
  obtain ⟨f2, f3⟩ := Prod.mk.inj f23
  rw [hn] at hy'
  refine First.K2.smpHeld_of ho hy' (f2.trans e2) (by rw [f1, e1, hO.one j hj]; exact Nat.one_pos)
    (by rw [f3, e3, f1, e1, hO.one j hj]; rfl) (by rw [f3, e3]; rfl) ?_
  rw [hsame.1, hc, f1, e1]
  exact seedReadsBack _ _ _ _ _ _ (by rw [hO.one j hj]; exact Nat.one_pos) (hO.pad j hj)
    (hO.row j hj)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place}

/-! ## 3 Under the head -/

/-- **The samples' test at border 357, behind an accepting step of what stands at number 356**,
under the head: from the samples' test and the test on the book in front, at a state that is reached
there, at a meaning whose held is smpHeld. Beside the step no premise speaks of the state behind. -/
theorem samples_W_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {blk : Block S ProofFile.Cl}
    (hb : cF.blocksInOrder[356]? = some blk) {W : Type} (Mg : Meaning ProofFile.InstPub W)
    (hH : Mg.held = fun j t (a : ProofFile.InstPub × S) => smpHeld a.2.st a.2.book j t)
    (z : ProofFile.InstPub) (ft : ℕ) {s s' : S}
    (hreach : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 356 (z, s))
    (hbk : First.bookAt (P5J.At.N Zp cF) IM.placesW[356]? s = true) (hy : IM.Yes ft blk s s')
    (hs : samplesHeld (P5J.At.N Zp cF) Mg (IM.openAt IM.linksW IM.placesW 356) (z, s) = true) :
    samplesHeld (P5J.At.N Zp cF) Mg (IM.openAt IM.linksW IM.placesW (356 + 1)) (z, s') = true := by
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  obtain ⟨-, e, msg, he, -, hm, hu⟩ := K13.Law.k13_sits_flat h.scope h.reads O
  obtain rfl : e = blk := Option.some.inj (he.symm.trans hb)
  obtain rfl : msg = wMsgFull := Option.some.inj
    (hm.symm.trans (K1.W_hm_atAll h O (K1.pin1_atAll h)))
  have hT := rowM4_head h O
  rw [IM.placesW_full, IM.linksW_full, ← head_N_is h] at hs ⊢
  rw [IM.placesW_full, ← head_N_is h] at hbk
  obtain ⟨rs, cols, n, e'⟩ := hy.under hu
  have hst : StepM4 ProofFile.Cl (whereOf Zp) (parWZ Zp wMsgFull) (z, s) (z, s') :=
    ⟨rfl, ft, rs, cols, n, e'⟩
  obtain ⟨r₁, r₂, gs, hd⟩ := hst.decide
  unfold samplesHeld at hs ⊢
  refine List.all_eq_true.2 fun u hu' => ?_
  rw [hH]
  rcases hT.two u hu' with rfl | rfl
  · have h0 := List.all_eq_true.1 hs h.𝔇.N.index
      (List.mem_flatMap.2 ⟨.pinI, hT.pinIn, List.mem_singleton.2 rfl⟩)
    rw [hH] at h0
    exact K13.Law.held4 hst _ _ h0
  · obtain ⟨p1, p2⟩ := K1.W_sits_atAll h O (K1.pin1_atAll h) (K1.pin2_atAll h)
    have hp1 := (K13.Law.planSitsB_iff (whereOf Zp) (parWZ Zp wMsgFull)).1 p1
    have hw : h.𝔇.N.w = _ := eq_of_beq p2
    unfold First.bookAt at hbk
    simp only [Bool.and_eq_true, beq_iff_eq] at hbk
    have hfit : BookFits s.book := (Sound.bookFitsB_iff _).1
      (Meaning.K2.atFirstFits_all O (fun b hb' => (K1.hOk_atAll h O b hb').1) hreach)
    have hO : PlanOwn (parWZ Zp wMsgFull) :=
      planOwn_w (K13.Law.likeFull_in_scope h.scope h.laid.pub (K1.pin1_atAll h))
        (K13.Law.gpOf_in_scope h.scope h.laid.pub (K1.pin1_atAll h))
        (K1.W_hm_atAll h O (K1.pin1_atAll h))
    have hall : ∀ j : Fin (shapesOf (parWZ Zp wMsgFull)).length, j.val = 0 →
        sampledAt (parWZ Zp wMsgFull) j := by
      rw [K1.eW_atAll h O (K1.pin1_atAll h)]
      exact sampled_W
    have hl : (shapesOf (parWZ Zp wMsgFull)).length = (parWZ Zp wMsgFull).sent.size := by
      simp [shapesOf]
    have hq := held_behind_send (parWZ Zp wMsgFull) (K13.Law.isSend_atM4 _ _) hd
      (K13.Law.atM4_booked hd) hbk.1.2 hfit hO ⟨0, hl ▸ hp1.pos⟩ (hall _ rfl)
    have hw1 : h.𝔇.N.w.1 = s.book.trees.size + (layOf (parWZ Zp wMsgFull)).tree.getD 0 0 := by
      rw [hw, hbk.1.1]
    have hw2 : h.𝔇.N.w.2 = (layOf (parWZ Zp wMsgFull)).part.getD 0 0 := by rw [hw]
    show smpHeld s'.st s'.book h.𝔇.N.w.1 h.𝔇.N.w.2 = true
    rw [hw1, hw2]
    exact hq

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.sampled_W
#print axioms ProofFile.Honest.K1.sampled_W_first
#print axioms ProofFile.Honest.K1.held_behind_send
#print axioms ProofFile.Honest.K1.samples_W_head
