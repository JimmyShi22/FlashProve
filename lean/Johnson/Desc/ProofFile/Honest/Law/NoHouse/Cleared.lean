-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Law/NoHouse/Cleared.lean: THE RECORD `NoHouse`
(Honest/Law/NoHouse/Bare.lean) AT «link l: cleared», AT EACH OF THE 25 LINKS (number `P1L20.clearIx
l` of the 358; place `P1L20.clearPlace l`): at the first chain's thread at the library's head
(`lettersHead`, Honest/Thread/FirstHead.lean), GENERAL IN l, under named premises. A member without
a round WHOSE YES TURNS THE STATE: what it leaves and turns is the library's `Tied.ClearedRec`
(Johnson/Top/H0/Walk/FrameGives.lean; `clearedGives`, FrameTiedRec.lean).

WHAT THIS IS. Conditional lemmas on definitions of ours and on the library's own texts. None of the
library's goals.

  1  GENERAL IN THE FIRST CHAIN's LETTERS: `form_shape`, `noHouse_first_turn`   the record at a
     member without a round whose yes is a step f's, with no mark behind it and the reply as it was:
     (P) one border on by `form_next_letters` (Honest/Law/NoHouse/FormNext.lean)
  2  `row_cleared_att`   at an attention segment the table's row at the place owes nothing (that the
     row closes and opens no class of rows and no pin: the library's `P1L20.quiet_at`)
  3  AT THE HEAD: `ride_cleared` (THE LIBRARY's `LettersRide` AT THE HONEST LETTERS: A MEMBER) ·
     `noHouse_cleared`

WHICH FIELDS FALL OUT OF THE LIBRARY's OWN LAWS, AND WHICH ARE CONTENT (at `noHouse_cleared`).
  seat     A CALL: `IM.frame_of` at the head's own opening.
  bare     no round, no oracle message: calls; the place: `IM.place_at`; noHalf: a premise on the
           prover.
  behind   (P) ONE BORDER ON: PAID WHOLE. From `ClearedRec` and one house's laws at the head: the
           mark, the statement's groups and the book's places as they were · the book-keeping's Bool
           behind (`Tied.shape_across`; `P1L20.places_full`) · where the book stands
           (`Tied.book_across`; `P1L20.still_atAll`). The library's `Tied.LettersRide` at the honest
           letters, at the step's own yes, from OUR promise in front: `ride_cleared`: the four
           fields that are spent read what «honest» does not turn, and their proofs spend
of the promise in front no more than ours holds. The reply's rider: PAID
           (`ClearedRec`: the reply as it was; b₀ ≠ the border behind). The other riders and the
           place's clause of «keeps»: premises on letters, AT A STEP OF THE BLOCK's (hRd, hKp).
  owes     AT AN ATTENTION SEGMENT NOTHING IS OWED (`row_cleared_att`). **AT A LAYERS' OR THE HEAD's
           SEGMENT: CONTENT: owes: THE ROW's CONTEXT [pile, pinW, pinI] AT THE STATE BEHIND**: there
           the block has laid one pending row more: that the pile with that row holds is to come of
           the claim on the weights, which the row shuts.
  yes      **CONTENT: asks: THE STEP SAYS YES AT THE THREAD's STATE** (`∃ t, f.clear s = .ok t`).
           ITS GUARDS, ONE BY ONE, by the library's `Props.clearWith_iff`
           (Johnson/Top/H0/Walk/FrameProps.lean) and the texts' own refusals
           (Johnson/Desc/First/Walk/Frame.lean). [N] a link with its fork is open in the record. THE
           KIND's OWN COUNTS: at a layers' link (`CountsLay`): such a link is open · C0 the
           smallness test's record has the plan's number of matrices · C1 the claims added are as
           many as the plan's · C2 every claim's weight has been handed out · C3 every matrix has
           had its call of the fold's sums; at an attention link (`CountsAtt`): such a link is open
           · C1 · C2 · C3 · C4 the claims added are attention's number · C5 just one matrix was
           drawn · C6 the lookup on the digits has run; at the head's link the step is another
           text's (`Close.tailHead`): its counts are not read by us. `Back` [W3 W4 W5]: the link is
           handed and done · `SamePlan` · the check that is handed back is the link's · where the
           flag says «no row» none is left; where it says «a row», what the sub-proof left is there.
           [ROW] where a row is left the pending row's function says yes: what that asks is not read
           by us. Last, the leaving's own form says yes. NONE OF THESE IS TAKEN OFF asks HERE. No
           mark behind the yes and the reply as it was: paid from `ClearedRec`.
  said, rides   PREMISES, as the record has them.

MET FOR NOTHING. As `NoHouse`. Limits. THE FULL SIZE ALONE, and the format's second hash function alone, as
the head. The library's head has a member at the name under four premises on the public files (the
seal's `P5J.head_exists_at_name`, Johnson/P5J/HeadExistsAtName.lean); none of our files calls it; no
member of the head TOGETHER WITH the thread's sentence is shown. Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.FirstStill
import Johnson.Top.H0.Walk.FrameTiedCleared
import Johnson.Top.H0.Walk.FrameRows
import Johnson.P1L20R.FrameJoin9
import Johnson.Desc.SmpRowsLay

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Block Chain Place Strs Wit KindName)
open VerifiableInference.Desc.First (S ModelPart Item Pub Numbers Meaning onAt openSets pubSets start
  rowOf segRow shift quietRow shapeAt standAt Stand mayWait bookAt flatPlacesOf sampledIn
  openSets_succ sampledIn_step)
open VerifiableInference.Desc.Sound (MsgT mgAll mgBase mgAll_pub mgAll_pubP_said linksFull)
open Johnson.Desc.First.Walk.Tied (NoneBetween DoorIdle LettersRide FrontAt ClearedRec
  clearedGives shape_across book_across front_parts pub_of_kept)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

/-! ## 1 General in the first chain's letters -/

section
variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr X P Cells Tok M : Type}
  {L : Letters Bk Cl W₀ Rc Xi Tr X P Cells Tok M}

/-- (P) holds the book-keeping's Bool at its border. -/
theorem form_shape {b : Nat} {k : Coins Bk} {s : S} {m : Mid (Local W₀ Rc Xi Tr) X}
    (hF : L.thread.Form b k s m) : s.failed = none ∧ shapeAt L.links L.ps[b]? s = true := by
  have hfail : s.failed = none := by
    have h1 : s.failed.isNone = true := hF.1
    exact Option.isNone_iff_eq_none.1 h1
  have hon : onAt L.N L.mgP L.links L.ps[b]?
      (((openSets L.links L.ps (start L.links))[b]?).getD [])
      (((pubSets L.mgP.more L.links L.ps)[b]?).getD []) (L.pubOf m.st.input.x, s) noStrs := hF.2
  obtain ⟨-, hr⟩ := hon
  obtain ⟨hB, -⟩ := hr.resolve_left (fun h => h hfail)
  simp only [Bool.and_eq_true] at hB
  exact ⟨hfail, hB.1.1.1.1.1⟩

/-- **THE RECORD AT A MEMBER OF THE FIRST CHAIN WITHOUT A ROUND AND WITHOUT A HOUSE WHOSE YES IS A
STEP f's**, with no mark behind it and the reply as it was. -/
theorem noHouse_first_turn {Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop}
    {fall : Nat → S → List Fmt.Drawn → Option String} {b : Nat} {p : Place} {blk : Block S Cl}
    {f : S → Except String S} {base : Nat} {Op : Item → Prop} (seat : L.bs[b]? = some blk)
    (hr : blk.rounds = []) (hor : blk.oracles = []) (hpl : blk.place = p)
    (hkf : p.kind = KindName.frame) (noHalf : ∀ g ∈ L.hs, g.place.kind ≠ KindName.frame)
    (hd : ∀ s t, blk.decide s [] [] = .ok t ↔
      f s = .ok t ∧ t.failed = none ∧ ProofFile.sameReply s t = true)
    (hp : L.ps[b]? = some p) (hq : quietRow (rowOf L.links p) = true)
    (hfail : ∀ s t, f s = .ok t → t.failed = s.failed)
    (hrep : ∀ s t, f s = .ok t → t.out.reply = s.out.reply)
    (hG : ∀ s t, f s = .ok t → t.st.groups = s.st.groups)
    (hB : ∀ s t, f s = .ok t → t.book.place = s.book.place)
    (hshape : ∀ s t, f s = .ok t → shapeAt L.links L.ps[b]? s = true →
      shapeAt L.links L.ps[b + 1]? t = true)
    (hbook : ∀ s t, f s = .ok t → bookAt L.N L.ps[b]? s = true →
      bookAt L.N L.ps[b + 1]? t = true)
    (hL : LettersRide L.N L.mgP (Johnson.Desc.First.Walk.Tied.Yes f) base
      (FrontAt L.N L.mgP L.links L.ps b)
      ((openSets L.links L.ps (start L.links))[b + 1]?.getD [])
      ((pubSets L.mgP.more L.links L.ps)[b + 1]?.getD []) Op)
    (said : ∀ k m, Said b k m → Said (b + 1) k m)
    (hrd : ∀ v s t, f s = .ok t → L.rides b v s → L.rides (b + 1) v t)
    (hkp : ∀ s t, f s = .ok t → t.failed = none → L.keeps b s t)
    (owes : ∀ k s m E t, ThrS L.thread Said b k s m E → f s = .ok t →
      L.thread.Items (L.thread.row b).owes k t m E)
    (asks : ∀ k s m E, ThrS L.thread Said b k s m E → fall b s [] = none → ∃ t, f s = .ok t)
    (rides : RidesPastS L.thread Said b) : NoHouse L.thread Said fall b blk :=
  NoHouse.ofDecide seat hr (by rw [hr, hor]; rfl)
    (noHalf_of_kind fun g hg => by
      rw [hpl, hkf]
      exact noHalf g hg)
    said
    (fun k s m E s' hA hs => by
      have hf := ((hd s s').1 hs).1
      exact ⟨form_next_letters L hp hq hA.1.2.2.1 (hfail s s' hf) (hG s s' hf) (hB s s' hf)
        (hshape s s' hf (form_shape hA.1.2.2.1).2) (hbook s s' hf) hL hf,
        hrd _ s s' hf hA.1.2.2.2.2.2.1, hkp s s' hf ((hd s s').1 hs).2.1⟩)
    (fun k s m E s' hA hs => owes k s m E s' hA ((hd s s').1 hs).1)
    (fun k s m E hA hfl => by
      obtain ⟨t, ht⟩ := asks k s m E hA hfl
      refine ⟨t, (hd s t).2 ⟨ht, (hfail s t ht).trans (form_shape hA.1.2.2.1).1, ?_⟩⟩
      unfold ProofFile.sameReply
      rw [hrep s t ht]
      exact beq_self_eq_true _)
    rides

end

/-! ## 2 The table's row at the place -/

/-- At an attention segment the row at «cleared» is empty. -/
theorem row_cleared_att {links : List ModelPart} {m : Nat} (hsub : links[m]? = some ModelPart.attention) :
    (rowOf links ⟨1, some m, 13, KindName.frame⟩).ins = [] ∧
      (rowOf links ⟨1, some m, 13, KindName.frame⟩).outs = [] ∧
      (rowOf links ⟨1, some m, 13, KindName.frame⟩).ctx = [] := by
  simp [rowOf, hsub, segRow, shift]

/-! ## 3 At the head -/

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
  {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **THE LIBRARY's `LettersRide` AT «CLEARED», AT THE HONEST LETTERS OVER THE LIBRARY's CONSTANT**:
at whatever numbers, at whatever two honest letters ans and test, at no item that rides back. The
four fields that read what «honest» does not turn, as they are paid at the library's own meaning
(`P1L20.ride_clear9`): in order: `inOrder9` · the public items' Bools: `pub_of_kept`, at OUR
promise in front, then `pub_clear9`'s own three cases · what they say beside: `q_behind9` · held:
`held_clear9`, `smpHeld_lay`. The three that read the strings are true by the honest letters' text.
-/
theorem ride_cleared (N : Numbers) (ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (tst : Nat → TS → Option String) {l : Nat} (hl : l < 25)
    {fs : List Johnson.Desc.First.Walk.Seat.LinkFrame}
    {f : Johnson.Desc.First.Walk.Seat.LinkFrame}
    (hfs : Johnson.Desc.First.Walk.Seat.framesOf Zp.p.built.links Zp.first Zp.p.X = .ok fs)
    (hf : fs[l]? = some f) (base : Nat) :
    LettersRide N (honest (P5J.mgAtAll h) ans tst) (Johnson.Desc.First.Walk.Tied.Yes f.clear) base
      (FrontAt N (honest (P5J.mgAtAll h) ans tst) linksFull (flatPlacesOf linksFull true)
        (P1L20.clearIx l))
      ((openSets linksFull (flatPlacesOf linksFull true)
        (start linksFull))[P1L20.clearIx l + 1]?.getD [])
      ((pubSets (honest (P5J.mgAtAll h) ans tst).more linksFull
        (flatPlacesOf linksFull true))[P1L20.clearIx l + 1]?.getD [])
      (fun _ => False) := by
  obtain ⟨-, Xl, counts, left, e, -⟩ :=
    Johnson.Desc.First.Walk.Seat.framesOf_row hfs (List.mem_of_getElem? hf)
  obtain ⟨pk, hk, hm, ho⟩ := P1L20.door_idle9 h.𝔇 (P1L20.mem_our_clear hl)
  have eS : sampledIn N ((openSets linksFull (flatPlacesOf linksFull true)
      (start linksFull))[P1L20.clearIx l + 1]?.getD []) =
      sampledIn N ((openSets linksFull (flatPlacesOf linksFull true)
        (start linksFull))[P1L20.clearIx l]?.getD []) := by
    rw [openSets_succ linksFull (flatPlacesOf linksFull true) (start linksFull)
      (P1L20.clearIx l) pk hk]
    exact sampledIn_step N _ _ (P1L20.quiet_at (P1L20.mem_our_clear hl) hk)
  refine ⟨fun _ _ _ _ _ _ _ _ => trivial, ?_, ?_, ?_, ?_,
    fun _ _ _ _ _ _ _ _ _ _ _ => trivial, fun _ _ _ _ _ _ _ _ _ _ _ => trivial,
    fun _ _ _ _ _ _ _ _ _ _ _ hO => hO.elim⟩
  · intro p s t y _ hu hF
    exact P1L20.inOrder9 h.𝔇 p s t (front_parts hu hF).1
  · intro p s t y q hy hu hF hq
    have hy' : f.clear s = .ok t := hy
    rw [e] at hy'
    have hm' : DoorIdle (honest (P5J.mgAtAll h) ans tst) linksFull pk := hm
    have hs0 : (honest (P5J.mgAtAll h) ans tst).pub q (p, s) = true :=
      pub_of_kept hk ho hm' hu hF hq
    have hs : (mgAll h.𝔇 mgBase).pub q (p, s) = true := hs0
    obtain ⟨g1, g2, g3⟩ := P1L20.cleared_out hy'
    show (mgAll h.𝔇 mgBase).pub q (p, t) = true
    rw [mgAll_pub] at hs ⊢
    rcases P1L20.pub_behind9 h.𝔇 hl hq with rfl | rfl | rfl
    · rw [VerifiableInference.Desc.First.pubAll_unheard] at hs ⊢
      unfold VerifiableInference.Desc.First.unheardB at hs ⊢
      rw [g1]
      exact hs
    · rw [VerifiableInference.Desc.First.pubAll_indexIs] at hs ⊢
      unfold VerifiableInference.Desc.K13.indexIsC at hs ⊢
      rw [g2]
      exact hs
    · rw [VerifiableInference.Desc.First.pubAll_indexThere] at hs ⊢
      unfold VerifiableInference.Desc.K13.indexThereC at hs ⊢
      exact g3 hs
  · intro p s t y q _ _ _ hq
    rw [P1L20.q_behind9 h.𝔇 hl hq]
    exact mgAll_pubP_said h.𝔇 Pub.unheard _ rfl
  · intro p s t y x hy hu hF hx
    have hy' : f.clear s = .ok t := hy
    rw [e] at hy'
    rw [eS] at hx
    show (mgAll h.𝔇 mgBase).held x.1 x.2 (p, t) = true
    rw [P1L20.held_clear9 h.𝔇 VerifiableInference.Desc.smpHeld_lay hy']
    exact ((front_parts hu hF).2.1 x hx).1

/-- **`NoHouse` AT «LINK l: CLEARED»**, at each of the 25 links. fs, f: the frame's rows, and link
l's. hRd, hKp: the other riders and the place's clause of «keeps», at a step of the block's.
**owes, asks: THE CONTENT.** -/
theorem noHouse_cleared {Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop}
    {fall : Nat → TS → List Fmt.Drawn → Option String} {l : Nat} (hl : l < 25)
    {fs : List Johnson.Desc.First.Walk.Seat.LinkFrame}
    {f : Johnson.Desc.First.Walk.Seat.LinkFrame}
    (hfs : Johnson.Desc.First.Walk.Seat.framesOf Zp.p.built.links Zp.first Zp.p.X = .ok fs)
    (hf : fs[l]? = some f) (noHalf : ∀ g ∈ H.first, g.place.kind ≠ KindName.frame)
    (said : ∀ k m, Said (P1L20.clearIx l) k m → Said (P1L20.clearIx l + 1) k m)
    (hb₀ : b₀ ≠ P1L20.clearIx l + 1)
    (hRd : ∀ v s t, f.clear s = .ok t → Rd (P1L20.clearIx l) v s → Rd (P1L20.clearIx l + 1) v t)
    (hKp : ∀ s t, f.clear s = .ok t → t.failed = none → Kp (P1L20.clearPlace l) s t)
    (owes : ∀ k s m E t, ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      (P1L20.clearIx l) k s m E → f.clear s = .ok t →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Items
        ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.row
          (P1L20.clearIx l)).owes k t m E)
    (asks : ∀ k s m E, ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      (P1L20.clearIx l) k s m E → fall (P1L20.clearIx l) s [] = none → ∃ t, f.clear s = .ok t)
    (rides : RidesPastS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      (P1L20.clearIx l)) :
    ∃ blk, cF.blocksInOrder[P1L20.clearIx l]? = some blk ∧
      NoHouse (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said fall
        (P1L20.clearIx l) blk := by
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  obtain ⟨-, fs', hfs', hall⟩ := IM.frame_of h.scope h.reads O
  obtain rfl := Except.ok.inj (hfs.symm.trans hfs')
  obtain ⟨Lk, f', bL, bB, bC, -, hn, hf', -, -, -, hClear, -, -, -, -, -, -, iC, rC, dC⟩ :=
    hall l hl
  obtain rfl := Option.some.inj (hf.symm.trans hf')
  obtain ⟨Lk', bL', bB', bC', -, hn', -, -, -, -, iC', oC⟩ :=
    IM.frame_oracles h.scope h.reads O l hl
  rw [hn] at iC
  rw [hn'] at iC'
  obtain rfl := Option.some.inj (iC.symm.trans iC')
  obtain ⟨-, -, -, hp, hmw, p', hp', hst⟩ := P1L20.places_full hl
  have hpl : bC.place = P1L20.clearPlace l := by
    have e := IM.place_at h.scope h.reads O iC
    rw [P1L20.placesW_eq] at e
    exact Option.some.inj (e.symm.trans hp)
  obtain ⟨-, Xl, counts, left, hcl, -⟩ :=
    Johnson.Desc.First.Walk.Seat.framesOf_row hfs (List.mem_of_getElem? hf)
  have hrec : ∀ s t, f.clear s = .ok t → ClearedRec Xl left _ _ s t := fun s t e => by
    rw [hcl] at e
    exact clearedGives Xl counts left _ _ s t e
  refine ⟨bC, iC, noHouse_first_turn (f := f.clear) iC rC oC hpl rfl noHalf
    (fun s t => by rw [dC, hClear]) hp (P1L20.quiet_at (P1L20.mem_our_clear hl) hp)
    (fun s t e => (hrec s t e).2.2.2.2.2.2.1)
    (fun s t e => (hrec s t e).2.2.2.2.2.2.2.2.2.2.2.2.1)
    (fun s t e => (hrec s t e).2.2.2.2.2.2.2.2.2.1)
    (fun s t e => by rw [(hrec s t e).2.2.2.1])
    (fun s t e hs => by
      have hs' : shapeAt linksFull (flatPlacesOf linksFull true)[P1L20.clearIx l]? s = true := hs
      rw [hp] at hs'
      show shapeAt linksFull (flatPlacesOf linksFull true)[P1L20.clearIx l + 1]? t = true
      rw [hp']
      exact shape_across hmw hst (hrec s t e).1 (hrec s t e).2.2.2.2.2.1 hs')
    (fun s t e hb => book_across ((P1L20.still_atAll h).2.2 l hl) (hrec s t e).2.2.2.1
      (hrec s t e).2.2.2.2.2.2.2.2.2.2.1 hb)
    (ride_cleared h _ _ _ hl hfs hf 0) said
    (fun v s t e hv => ⟨fun hb => by
      rw [(hrec s t e).2.2.2.2.2.2.2.2.2.2.2.2.1]
      exact hv.1 (by omega), hRd v s t e hv.2⟩)
    (fun s t e h0 =>
      (head_keeps h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hp s t).2 (hKp s t e h0))
    owes asks rides⟩

end

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.form_shape
#print axioms ProofFile.Honest.FirstThread.noHouse_first_turn
#print axioms ProofFile.Honest.FirstThread.row_cleared_att
#print axioms ProofFile.Honest.FirstThread.ride_cleared
#print axioms ProofFile.Honest.FirstThread.noHouse_cleared
