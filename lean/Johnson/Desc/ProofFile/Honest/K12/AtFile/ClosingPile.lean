-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/ClosingPile.lean: the pending rows go past the first chain's
closing proximity test. At a stand of the library's own thread, across an accept of the test, what the
pile says of a witness in front it says behind: the rows stay, and the reader of the rows reads one
message, whose codes, shape and seat the test leaves.

  `K12Step`          an accept of the test at the finish
  `index_facts`      at a stand: the index masks' message is there, has its seat, and the pending rows
                     name it alone
  `pile_past`        the sentence of the pile goes on
  `pin_past`         the index masks' pin goes on: it reads the message's sample alone

By what. `promise_index` (Johnson/Desc/K13/Law/AtTable.lean); `foldFacts_thr` (Honest/Thread/ReachFacts.lean);
`indexSeat_of_carried`; `four_of_yes` (Johnson/Desc/K12/Honest/Shape/TestKeepsPile.lean); `agree_across`
(Johnson/Loose/H2K12/Rides354.lean); `holds_congr` (Johnson/Desc/K13/Law/Agree.lean). For the pin: `k12_smp`
(Johnson/Desc/K12/Coin/SamplesThrough.lean), `smpAt_congr`; `smp_listed`, `sampled_of_held`, `sampled_no_mask`,
`pinI_open_written`, `places_of`, `placesOnce_of` (Johnson/Loose/H2K12/).

Hypotheses. hT: the stand. hL: the places listed have the index masks' seat at the table's own number:
`indexListed_at` (Johnson/Loose/H2K12/ClosedAtHead354.lean) pays it under the written values. Y: the
accept.

Limits. Y is the accept itself, not the weaker `K12KeepsFirst`. Nothing on completeness of the chain, soundness or hiding.

NOT IN FRONT OF A LAW OVER COINS: `index_facts`, `pile_past`, `pin_past` bear this label; the rule is at its home,
the head of Johnson/Bind/ForProver/FiveFieldsAt.lean. Their ground: the thread from `Thr` as a premise.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.ClosingHead
import Johnson.Desc.ProofFile.Honest.Thread.ReachFacts
import Johnson.Desc.K12.Honest.Shape.TestKeepsPile
import Johnson.Desc.K13.Law.AtTable
import Johnson.Loose.H2K12.Rides354
import Johnson.Loose.H2K12.AcrossOfSits
import Johnson.Loose.H2K12.Owed354AtMg
import Johnson.Loose.H2K12.ClosedOfPins354
import Johnson.P5J.ReadsTestsAtHead
import Johnson.P5T.FenceAtMg
import AtFullSide.K12.FirstAnyAtHeadL

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open VerifiableInference.Desc (Chain Place Strs)
open VerifiableInference.Desc.K12 (T12 P12 atFinish)
open VerifiableInference.Desc.First (S Item)
open VerifiableInference.Desc.Sound (MsgT seatBy noFirst)
open VerifiableInference.Desc.K13.Law (RowsTrue rwBook OnLedger holds_congr ρg LFull)
open ProofFile.Honest.FirstThread (lettersHead Script WtF noStrs foldFacts_thr)
open P5J (AtMgA CellsM TS)

/-- An accept of the test at the finish. -/
def K12Step (q : P12) (s s' : S) : Prop :=
  ∃ rs gs, (atFinish q).decide s rs gs = .ok s'

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

section
variable (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x) {Bk : ProverCoinCounts}
  {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **At a stand the index masks' message is there, has its seat, and the pending rows name it.** -/
theorem index_facts {k : Coins Bk} {s : S} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 354 k s m E)
    (hL : LFull.places[(P5J.At.N Zp cF).indexNo]? = some (P5J.At.N Zp cF).index) :
    s.out.indexMasks < s.st.oracles.size ∧
      (seatBy noFirst s.book s.out.indexMasks).isSome = true ∧
      ∀ r ∈ s.rows, OnLedger s.out.indexMasks r := by
  have h' := hT
  unfold Thr at h'
  obtain ⟨-, -, hF, -, -, -, -⟩ := h'
  obtain ⟨hf, hon⟩ := hF
  have hfail : s.failed = none :=
    Option.isNone_iff_eq_none.1 (show s.failed.isNone = true from hf)
  have hlen : 354 ≤ cF.blocksInOrder.length := by
    obtain ⟨nm, hm⟩ := member_354 h
    exact Nat.le_of_lt (List.getElem?_eq_some_iff.1 hm).1
  have FF := foldFacts_thr h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w (X := X)
  have hr : (fun b (a : ProofFile.InstPub × TS) => b ≤ cF.blocksInOrder.length ∧
      ∃ (k : Coins Bk) (m : Mid (Local W₀ Rc ProofFile.Inst Tr) X) (E : Env),
        Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b k a.2 m E ∧
          m.st.input.x.pub = a.1) 354 (m.st.input.x.pub, s) := ⟨hlen, k, m, E, hT, rfl⟩
  have fSeats := FF.seatsCarried 354 _ hr hfail
  have fFits := FF.bookFits 354 _ hr hfail
  have fMasks := FF.pileMasks 354 _ hr hfail
  obtain ⟨hii, hit, hbk, -⟩ := VerifiableInference.Desc.K13.Law.promise_index
    (Fr := ⟨0, [], fun _ => 0, 0⟩) (P5J.At.N Zp cF)
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP P5J.fullLinks P5J.At.ps
    (fun a : ProofFile.InstPub × TS => a) 354 H2K12.pinI_open_written
    ((m.st.input.x.pub, s), (fun _ => (0, []), fun _ => [])) hon hfail
  have hI : VerifiableInference.Desc.K1.indexIsB (P5J.At.N Zp cF).indexNo s = true := by
    rw [← VerifiableInference.Desc.K13.Law.indexIsC_eq]
    exact hii
  have hTh : VerifiableInference.Desc.K1.indexThereB s = true := by
    rw [← VerifiableInference.Desc.K13.Law.indexThereC_eq]
    exact hit
  have hbk' := hbk
  unfold VerifiableInference.Desc.First.bookAt at hbk'
  simp only [Bool.and_eq_true, beq_iff_eq] at hbk'
  have hseat : s.book.place[s.out.indexMasks]? = some (P5J.At.N Zp cF).index :=
    eq_of_beq (VerifiableInference.Desc.K1.indexSeat_of_carried
      ((VerifiableInference.Desc.K12.Coin.seatsPrefix_iff
        (VerifiableInference.Desc.K12.Door.toTree LFull) _).1 fSeats) hbk'.1.2 hTh hI hL)
  have hthere : s.out.indexMasks < s.st.oracles.size := by
    have e : (s.st.oracles[s.out.indexMasks]?).isSome = true := hTh
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 e
    exact (Array.getElem?_eq_some_iff.1 hy).1
  have hBF := (VerifiableInference.Desc.Sound.bookFitsB_iff s.book).1 fFits
  obtain ⟨T, hTr, -⟩ := hBF _ _ hseat
  refine ⟨hthere, ?_, (VerifiableInference.Desc.K13.Law.pileMasksC_iff s).1 fMasks⟩
  rw [VerifiableInference.Desc.Sound.seatBy_some _ s.book _ (P5J.At.N Zp cF).index T hseat hTr]
  rfl

/-- **The sentence of the pile goes on across an accept of the test.** -/
theorem pile_past {k : Coins Bk} {s s' : S} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 354 k s m E)
    (hL : LFull.places[(P5J.At.N Zp cF).indexNo]? = some (P5J.At.N Zp cF).index)
    (Y : K12Step (H2U.p12OfMade Zp.made) s s') (π : ProofFile.InstPub) (u : VerifiableInference.Desc.Wit (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (hm : RowsTrue (rwBook (P5J.At.arr Zp) h.𝔇.mat13 (π, s)) s u) :
    RowsTrue (rwBook (P5J.At.arr Zp) h.𝔇.mat13 (π, s')) s' u := by
  obtain ⟨rs, gs, hd⟩ := Y
  obtain ⟨hi, hs, hled⟩ := index_facts h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hT hL
  obtain ⟨e1, e2, e3, e4⟩ := ProofFile.Honest.Sh.four_of_yes _ s s' rs gs
    (ProofFile.Honest.Sh.answers_at_head h.toAtMg) hd _ hi hs
  intro r' hr'
  have hrs : r' ∈ s.rows := by
    rw [← e1]
    exact hr'
  exact (holds_congr ρg (hled r' hrs)
    (H2K12.Rid354.agree_across (P5J.At.arr Zp) h.𝔇.mat13 (π, s') (π, s) s.out.indexMasks u u e2.symm
      e3.symm e4.symm rfl fun _ _ => ⟨rfl, rfl⟩)).1 (hm r' hrs)

set_option maxHeartbeats 4000000 in
/-- **The index masks' pin goes on across an accept of the test.** -/
theorem pin_past {k : Coins Bk} {s s' : S} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 354 k s m E)
    (hL : LFull.places[(P5J.At.N Zp cF).indexNo]? = some (P5J.At.N Zp cF).index)
    (Y : K12Step (H2U.p12OfMade Zp.made) s s') (π : ProofFile.InstPub) (y y' : Strs)
    (u : VerifiableInference.Desc.Wit (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (hm : ansJT (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.smp Zp) (P5J.At.ms Zp Z.lay)
      (P5J.At.N Zp cF).index.1 (P5J.At.N Zp cF).index.2 (π, s) y u) :
    ansJT (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.smp Zp) (P5J.At.ms Zp Z.lay)
      (P5J.At.N Zp cF).index.1 (P5J.At.N Zp cF).index.2 (π, s') y' u := by
  obtain ⟨rs, gs, hd⟩ := Y
  obtain ⟨o, t', -, -, -, hdk, e⟩ := VerifiableInference.Desc.K12.Seat.atFinish_ok _ s s' rs gs hd
  have est : s'.st = t'.st := by rw [e]
  have h' := hT
  unfold Thr at h'
  obtain ⟨-, -, hF, -, -, -, -⟩ := h'
  obtain ⟨hf, hon⟩ := hF
  have hfail : s.failed = none :=
    Option.isNone_iff_eq_none.1 (show s.failed.isNone = true from hf)
  have hlen : 354 ≤ cF.blocksInOrder.length := by
    obtain ⟨nm, hm'⟩ := member_354 h
    exact Nat.le_of_lt (List.getElem?_eq_some_iff.1 hm').1
  have FF := foldFacts_thr h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w (X := X)
  have hr : (fun b (a : ProofFile.InstPub × TS) => b ≤ cF.blocksInOrder.length ∧
      ∃ (k : Coins Bk) (m : Mid (Local W₀ Rc ProofFile.Inst Tr) X) (E : Env),
        Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b k a.2 m E ∧
          m.st.input.x.pub = a.1) 354 (m.st.input.x.pub, s) := ⟨hlen, k, m, E, hT, rfl⟩
  have fSeats := FF.seatsCarried 354 _ hr hfail
  have fFits := FF.bookFits 354 _ hr hfail
  obtain ⟨hii, hit, hbk, -⟩ := VerifiableInference.Desc.K13.Law.promise_index
    (Fr := ⟨0, [], fun _ => 0, 0⟩) (P5J.At.N Zp cF)
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP P5J.fullLinks P5J.At.ps
    (fun a : ProofFile.InstPub × TS => a) 354 H2K12.pinI_open_written
    ((m.st.input.x.pub, s), (fun _ => (0, []), fun _ => [])) hon hfail
  have hI : VerifiableInference.Desc.K1.indexIsB (P5J.At.N Zp cF).indexNo s = true := by
    rw [← VerifiableInference.Desc.K13.Law.indexIsC_eq]
    exact hii
  have hTh : VerifiableInference.Desc.K1.indexThereB s = true := by
    rw [← VerifiableInference.Desc.K13.Law.indexThereC_eq]
    exact hit
  have hbk' := hbk
  unfold VerifiableInference.Desc.First.bookAt at hbk'
  simp only [Bool.and_eq_true, beq_iff_eq] at hbk'
  have hseat : s.book.place[s.out.indexMasks]? = some (P5J.At.N Zp cF).index :=
    eq_of_beq (VerifiableInference.Desc.K1.indexSeat_of_carried
      ((VerifiableInference.Desc.K12.Coin.seatsPrefix_iff
        (VerifiableInference.Desc.K12.Door.toTree LFull) _).1 fSeats) hbk'.1.2 hTh hI hL)
  have hthere : s.out.indexMasks < s.st.oracles.size := by
    have e' : (s.st.oracles[s.out.indexMasks]?).isSome = true := hTh
    obtain ⟨y₀, hy⟩ := Option.isSome_iff_exists.1 e'
    exact (Array.getElem?_eq_some_iff.1 hy).1
  have hBF := (VerifiableInference.Desc.Sound.bookFitsB_iff s.book).1 fFits
  have hSH : VerifiableInference.Desc.First.samplesHeld (P5J.At.N Zp cF)
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP
      (VerifiableInference.Desc.K13.Law.openAt P5J.fullLinks P5J.At.ps 354)
      (m.st.input.x.pub, s) = true := ((hon.2.resolve_left fun q => q hfail).2).1
  have hHeld : VerifiableInference.Desc.smpHeld s.st s.book (P5J.At.N Zp cF).index.1
      (P5J.At.N Zp cF).index.2 = true :=
    List.all_eq_true.1 hSH (P5J.At.N Zp cF).index
      (List.mem_flatMap.2 ⟨.pinI, H2K12.pinI_open_written, by simp⟩)
  have hmk : o.mask ≠ some s.out.indexMasks := by
    intro hmask
    obtain ⟨x₁, hx, hs⟩ := H2K12.sampled_of_held hBF hHeld hseat
    exact H2K12.sampled_no_mask
      (VerifiableInference.Desc.K12.Seat.block_front_holds _ _ t' _ gs hdk).2.1 hx hs hmask
  have hq := ProofFile.Honest.K12.AtProof.numbersL_at_head h.toAtMg
  have hplan : (VerifiableInference.Desc.K12.proximityTestKind VerifiableInference.Desc.K12.guardedProximityTestParts
      (H2U.p12OfMade Zp.made) : VerifiableInference.Desc.Block T12 Unit).planOk = true := by
    rw [hq]
    exact (ProofFile.Honest.K12.Light.facts_head_L h.toAtMg).plan
  have hsp := VerifiableInference.Desc.K12.Coin.k12_smp _ (H2K.JointK.early_of_planOk _ hplan)
    (ProofFile.Honest.Sh.answers_at_head h.toAtMg) _ t' _ gs hdk s.out.indexMasks hthere hmk
  have W4 := H2K12.written354_of_pins h.scope h.laid.pub h.pins.1 h.laid.laidPOf
  have hLd := P5J.laid_at_head h.toAtMg
  have hpl : LFull.places = P5J.At.seats Zp := H2K12.places_of W4 LFull hLd
  have hno : (P5J.At.seats Zp).Nodup := hpl ▸ H2K12.placesOnce_of W4 LFull hLd
  have eo : s.out.indexMasks = (P5J.At.N Zp cF).indexNo := eq_of_beq hI
  refine ansJT_congr (P5J.At.cs Zp) (P5J.At.arr Zp) (fun z _ hs => ?_) hm
  have es : z.1.seat z.2 = ((P5J.At.N Zp cF).index.1, (P5J.At.N Zp cF).index.2) := hs
  have hsl : (P5J.At.seats Zp)[s.out.indexMasks]? = some (P5J.At.N Zp cF).index := by
    rw [← hpl, eo]
    exact hL
  have hsl' := hsl.trans (congrArg some es.symm)
  have a1 := H2K12.smp_listed (P5J.At.cs Zp) (P5J.At.seats Zp) hno (π, s') _ z hsl'
  have a2 := H2K12.smp_listed (P5J.At.cs Zp) (P5J.At.seats Zp) hno (π, s) _ z hsl'
  exact a1.trans ((VerifiableInference.Desc.Sound.smpAt_congr _ _ _ s.st s'.st _
    (by rw [est]; exact hsp)).trans a2.symm)

end

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.K12Step
#print axioms ProofFile.Honest.K12.index_facts
#print axioms ProofFile.Honest.K12.pile_past
#print axioms ProofFile.Honest.K12.pin_past
