-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/HeldAtFifty.lean: the kind K1's fifty later sendings (every
link's reads and digits), under the library's head: if the samples' test and the test on the book
hold at a reached state in front, the samples' test holds at the next border behind an accepting
step of what stands at the place's number, at a meaning whose held is smpHeld. Beside the step no
premise speaks of the state behind.

What this file proves. Let h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x (the library's head,
Johnson/P5J/MgAtAll.lean), l < 25, d a Boolean (false: the reads; true: the digits), blk whatever
stands at the number noL l d in the first chain's flat list, and s, s' the states in front of and
behind an accepting step of blk (IM.Yes).
  - samples_later_head: samplesHeld (Johnson/Desc/First/Borders.lean) at the numbers P5J.At.N Zp cF
    and the written lists IM.linksW and IM.placesW goes from border noL l d at (z, s) to border noL
    l d + 1 at (z, s'). Its premises beside the step and the test in front: the meaning's held is
    smpHeld (hH); the test on the book at s (hbk, one of the table's six tests); s is reached at the
    number noL l d of the flat list (hreach).
  - held_old_later: what is held in front of an accept of the lot's own sub-protocol blkL is held
    behind, under hH.
  - held_new_later: the place's own tenants are held behind such an accept: from the test on the
    book and BookFits of the book in front, and from three premises on the plan (the seats' test
    laterSeatsB; every message of the place has a sample; PlanOwn).
  - msg_behind_send: behind a yes of the kind's decision decideSend, a message of the place that has
    a sample, with one answer, stands in the statement at its number, with its shape, marked as
    sampled, with one sample row.
No thread, no prover and no file's bytes occur. No definition. Statements and proofs.

How it fits. held_later (Johnson/Desc/ProofFile/Honest/K1/Law/FormBehind.lean) gives the samples'
test behind from the test in front and two premises, old and new; new stands at the state behind.
Both are proved here. For new: a tenant is a message's seat (seats_of_later,
Johnson/Desc/AtSeats/PlanRestAtCut.lean); a yes of blkL holds a yes of decideSend and leaves its
messages (isSend_laterAt, Johnson/Desc/K1/Law/GoodSendPlaces.lean; isSend_k1Reads,
Johnson/Desc/K1/Law/BlocksAtLater.lean); the message's number is the number of messages in front
plus its place (size_behind, Johnson/Desc/K1/Law/GoodSend3.lean; booked_blkL,
Johnson/Desc/K1/Law/K01Law.lean); the book's reader finds it at its seat (oracleNoNew,
Johnson/Desc/K1/Law/OracleNoNew.lean); a seed can be read back off its row (seedReadsBack,
Johnson/Desc/K1/Law/SeedReadsBack.lean); these make smpHeld (smpHeld_of,
Johnson/Top/H0/Tw/K2C/HeldAtYes.lean).

Proofs that this file follows: fill_held (Johnson/Desc/K1/Law/MgK1.lean) in held_old_later: its
premise MgK1, five equations on the meaning, is replaced by the one that its proof uses.
seedIs_behind (Johnson/Desc/K1/Law/SeedIs.lean) in msg_behind_send: the statement is SeedIs without
its last two clauses (that the seed reads in the field; the answer's value), and the premises that
served these alone are gone: the test condPort (of it answers = 1 stays, as a premise), that the
rounds fit, and joint seeds ρ of the field as which the first round's seeds read (the first seed's
pair, which they also handed over, now comes of the list's length).

Lemmas used beside these: laterFacts_blkL (Johnson/Desc/K1/Law/K01Law.lean), smpHeldStays
(Johnson/Desc/K1/Law/SmpHeldStays.lean), decideSend_iff and cutSeeds_length
(Johnson/Desc/K1/Law/Writes3.lean), outs_spec (Johnson/Desc/K1/Law/Joined2.lean), one_le_seeds
(Johnson/Desc/K1/Law/Port6.lean), rowsOf_one (Johnson/Desc/K1/Law/SeedIs.lean), placed_of_fits
(Johnson/Desc/Book/BookFits.lean); under the head k01_flat
(Johnson/Desc/K1/Law/LettersAtFifty.lean), planK1_head
(Johnson/Desc/ProofFile/Honest/K1/Law/FiftyAtHead.lean) with hinj_of, trees_of, msgs_of and hP_of
(Johnson/Desc/K1/Law/CallsC.lean), bookFits_reached (Johnson/IMR/AtReach.lean) with front_len
(Johnson/IMR/FinPin.lean), parL_place (Johnson/Desc/AtSeats/FromTheCut.lean), sampled_at
(Johnson/Desc/AtSeats/PlanRestAtCut.lean), own_fifty and planOwn_of
(Johnson/Desc/K1/Law/PlanOwn.lean).

Names (namespace ProofFile.Honest.K1): held_old_later, msg_behind_send, held_new_later,
samples_later_head, as above.

Limits, the weightiest first.
  1. This file shows no value of the head h, and no state at which the premises of
    samples_later_head hold. That blk accepts anywhere is not shown here.
  2. "Held" is a test on the verifier's state: the sample's rows lie in the statement, and a seed
    can be read back off the first (smpHeld, Johnson/Desc/SmpRows.lean). It does not say that the
    seed reads in the field: a factor 0 is not excluded here.
  3. hH, hbk and hreach are premises. This file does not prove them.
  4. At the numbers P5J.At.N Zp cF: held_later reads the table's row at them.
  5. At the written list linksFull. Nothing on the first segment's opening (number 2) or on W's
    sending (number 356).
  6. Nothing on soundness, on completeness or on any other property.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.ProofFile.Honest.K1.Law.FiftyAtHead
import Johnson.Desc.K1.Law.MgK1
import Johnson.Desc.K1.Law.K01Law
import Johnson.Desc.K1.Law.BlocksAtLater
import Johnson.Desc.K1.Law.GoodSendPlaces
import Johnson.Desc.K1.Law.OracleNoNew
import Johnson.Desc.K1.Law.SeedReadsBack
import Johnson.Desc.K1.Law.PlanOwn
import Johnson.Desc.AtSeats.PlanRestAtCut
import Johnson.Desc.AtSeats.FromTheCut
import Johnson.IMR.AtReach
import Johnson.IMR.FinPin
import Johnson.Top.H0.Tw.K2C.HeldAtYes

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Block Chain Place smpHeld)
open VerifiableInference.Desc.First (S Numbers Meaning flatPlacesOf samplesHeld)
open VerifiableInference.Desc.Sound (linksFull)
open VerifiableInference.Desc.Book (BookFits placed_of_fits)
open VerifiableInference.Desc.K1
open OnBytes.Model.Stages (LinkH)
open OnBytes.Maker (WholeD)
open Johnson.Desc.First.Walk.Tied (Reach)
open _root_.Desc.Plain

/-- **What is held in front of an accept of the sub-protocol is held behind**, at a meaning whose
held is smpHeld. -/
theorem held_old_later {Pp W : Type} (Mg : Meaning Pp W)
    (hH : Mg.held = fun j t (a : Pp × S) => smpHeld a.2.st a.2.book j t) (Z : ProofFile.Pub)
    (G : ProofFile.Ground) (l : ℕ) (d : Bool) (X : LinkH) (arrs : Option (List ℕ)) (x x' : Pp × S)
    (hY : YesOf (blkL Z G l d X arrs) x x') (u : ℕ × ℕ) (h0 : Mg.held u.1 u.2 x = true) :
    Mg.held u.1 u.2 x' = true := by
  rw [hH] at h0 ⊢
  have hB := laterFacts_blkL Z G l d X arrs
  obtain ⟨r₁, r₂, gs, hd⟩ := hY.two hB.rounds
  obtain ⟨more, hm⟩ := hB.grows _ _ _ _ _ hd
  exact (smpHeldStays _ _ _ _ more u.1 u.2 (hB.smpStay _ _ _ _ _ hd) hm h0).2.2.2

/-- **Behind a yes of the sending's decision**: a message of the place that has a sample, with one
answer, stands at its number with its shape, marked as sampled, with one sample row; and the
statement's codes are the place's. -/
theorem msg_behind_send {L : Type} (P : K1.Par) (owed : Option Nat) (d d' : DState L)
    (r₁ r₂ : Fmt.RoundView) (ids : Array Nat) (hyes : decideSend P owed d [r₁, r₂] = .ok (ids, d'))
    (k : Fin (shapesOf P).length) (hk : sampledAt P k) (h1 : (shapeAt P k).answers = 1) :
    d'.st.codes = P.codes ∧ ∃ x z β t, d'.st.oracles[d.st.oracles.size + k.val]? = some x ∧
      x.shape = shapeAt P k ∧ x.sampled = true ∧
      x.sampleRows = #[sampleRow (Msg.of P.codes (shapeAt P k)) (d.st.oracles.size + k.val) z β 0
        t] := by
  have h0 : 0 < P.seeds := one_le_seeds P k hk
  have hlen : (seedsOf P r₁).length = P.seeds := cutSeeds_length _ _ _
  obtain ⟨sd, hsd⟩ : ∃ sd, (seedsOf P r₁)[0]? = some sd :=
    ⟨(seedsOf P r₁)[0]'(by rw [hlen]; exact h0), List.getElem?_eq_getElem _⟩
  obtain ⟨⟨_, hc, _, _, hf⟩, _, rfl⟩ := (decideSend_iff P owed d d' r₁ r₂ ids).1 hyes
  obtain ⟨ys', hy, hget⟩ := outs_spec P.codes (seedsOf P r₁) P.seeds (shapesOf P)
    d.st.oracles.size (answersIn r₂) hf k.val k.isLt
  have hk' : (shapesOf P)[k.val].answers ≠ 0 := hk
  have hx : (behind P d (seedsOf P r₁) (answersIn r₂)).st.oracles[d.st.oracles.size + k.val]? =
      some (wr P.codes (seedsOf P r₁) (d.st.oracles.size + k.val) (shapesOf P)[k.val] ys') := by
    show (d.st.oracles.toList ++ outs P.codes (seedsOf P r₁) d.st.oracles.size (shapesOf P)
      (answersIn r₂)).toArray[d.st.oracles.size + k.val]? = _
    rw [List.getElem?_toArray, List.getElem?_append_right (by simp)]
    simpa using hget
  obtain ⟨t, ht⟩ : ∃ t, ys'[0]? = some t :=
    ⟨ys'[0]'(Nat.lt_of_lt_of_le (Nat.pos_of_ne_zero hk') hy), List.getElem?_eq_getElem _⟩
  refine ⟨hc, _, sd.1, sd.2, t, hx, ?_, by simp [wr, hk'], ?_⟩
  · unfold wr
    split <;> rfl
  · have hrows : (wr P.codes (seedsOf P r₁) (d.st.oracles.size + k.val) (shapesOf P)[k.val]
        ys').sampleRows = rowsOf P.codes (seedsOf P r₁) (d.st.oracles.size + k.val)
          (shapesOf P)[k.val] ys' := by simp [wr, hk']
    rw [hrows]
    exact rowsOf_one _ _ _ _ _ h1 sd t hsd ht

/-- **The place's own tenants are held behind an accept of the sub-protocol**, if the test on the
book holds in front and the book there fits (BookFits), under three premises on the plan (hP, hsam,
hO). -/
theorem held_new_later (N : Numbers) (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : ℕ) (d : Bool)
    (X : LinkH) (arrs : Option (List ℕ)) {Pp : Type} (x x' : Pp × S)
    (hY : YesOf (blkL Z G l d X arrs) x x')
    (hbk : First.bookAt N (flatPlacesOf linksFull true)[noL l d]? x.2 = true)
    (hfit : BookFits x.2.book)
    (hP : laterSeatsB N (parL Z G l d) l (momL d)
      (N.treesAt (flatPlacesOf linksFull true)[noL l d]?) = true)
    (hsam : ∀ j : Fin (shapesOf (parL Z G l d)).length, sampledAt (parL Z G l d) j)
    (hO : PlanOwn (parL Z G l d)) :
    ∀ u ∈ N.sent l (momL d), smpHeld x'.2.st x'.2.book u.1 u.2 = true := by
  intro u hu
  obtain ⟨j, hj, rfl⟩ := seats_of_later hP hsam u hu
  obtain ⟨r₁, r₂, gs, hd⟩ := hY.two (laterFacts_blkL Z G l d X arrs).rounds
  have hB := booked_blkL Z G l d X arrs _ _ _ _ _ hd
  have hS : IsSend (parL Z G l d) (fun s : S => s.st) (blkL Z G l d X arrs) := by
    cases d with
    | true => exact isSend_laterAt _ _ _ _ _ _
    | false => exact isSend_k1Reads _ _ _ _ _ _
  obtain ⟨L, dd, dd', owed, ids, hyes, hsame, hsize⟩ := hS _ _ _ _ _ hd
  obtain ⟨hc, y, zz, β, t, hy, e1, e2, e3⟩ :=
    msg_behind_send (parL Z G l d) owed dd dd' r₁ r₂ ids hyes j hj (hO.one j hj)
  unfold First.bookAt at hbk
  simp only [Bool.and_eq_true, beq_iff_eq] at hbk
  have hl : (shapesOf (parL Z G l d)).length = (parL Z G l d).sent.size := by simp [shapesOf]
  have hjlt : j.val < (parL Z G l d).sent.size := hl ▸ j.isLt
  have hn : dd.st.oracles.size = x.2.st.oracles.size := by
    have a := size_behind (parL Z G l d) owed dd dd' r₁ r₂ ids hyes
    have b := hB.msgs
    have c : x'.2.st.oracles.size = dd'.st.oracles.size := hsize
    rw [hl] at a
    omega
  have ho := oracleNoNew (parL Z G l d) _ _ _ _ hB hbk.1.2 (placed_of_fits hfit) hO.part j.val hjlt
  have e := hsame.2 (dd.st.oracles.size + j.val)
  rw [hy] at e
  obtain ⟨y', hy', e⟩ := Option.map_eq_some_iff.1 e
  obtain ⟨f1, f23⟩ := Prod.mk.inj e
  obtain ⟨f2, f3⟩ := Prod.mk.inj f23
  rw [hn] at hy'
  rw [← hbk.1.1]
  refine First.K2.smpHeld_of ho hy' (f2.trans e2) (by rw [f1, e1, hO.one j hj]; exact Nat.one_pos)
    (by rw [f3, e3, f1, e1, hO.one j hj]; rfl) (by rw [f3, e3]; rfl) ?_
  rw [hsame.1, hc, f1, e1]
  exact seedReadsBack _ _ _ _ _ _ (by rw [hO.one j hj]; exact Nat.one_pos) (hO.pad j hj)
    (hO.row j hj)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place}

/-- **The samples' test at the next border, behind an accepting step of what stands at the place's
number**, under the head: from the samples' test and the test on the book in front, at a state that
is reached there, at a meaning whose held is smpHeld. Beside the step no premise speaks of the state
behind. -/
theorem samples_later_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : ℕ} (hl : l < 25)
    (d : Bool) {blk : Block S ProofFile.Cl} (hb : cF.blocksInOrder[noL l d]? = some blk) {W : Type}
    (Mg : Meaning ProofFile.InstPub W)
    (hH : Mg.held = fun j t (a : ProofFile.InstPub × S) => smpHeld a.2.st a.2.book j t)
    (z : ProofFile.InstPub) (ft : ℕ) {s s' : S}
    (hreach : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (noL l d) (z, s))
    (hbk : First.bookAt (P5J.At.N Zp cF) IM.placesW[noL l d]? s = true)
    (hy : IM.Yes ft blk s s')
    (hs : samplesHeld (P5J.At.N Zp cF) Mg (IM.openAt IM.linksW IM.placesW (noL l d)) (z, s) =
      true) :
    samplesHeld (P5J.At.N Zp cF) Mg (IM.openAt IM.linksW IM.placesW (noL l d + 1)) (z, s') =
      true := by
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  obtain ⟨e, X, arrs, he, hu⟩ := K1.k01_flat h.scope h.reads O l hl d
  obtain rfl : e = blk := Option.some.inj (he.symm.trans hb)
  have H := planK1_head h O
  have hs' := K1.hs_atAll h O (K1.pin1_atAll h)
  have eP : parL Zp Bs.G₀ l d = placeL l d :=
    parL_place (K1.hc_atAll h O (K1.pin1_atAll h)) hs'
      (K13.Law.gpOf_in_scope h.scope h.laid.pub (K1.pin1_atAll h)) l d
  have hO : PlanOwn (parL Zp Bs.G₀ l d) := by
    rw [eP]
    have h2 := List.all_eq_true.1 own_fifty l (List.mem_range.2 hl)
    rw [Bool.and_eq_true] at h2
    cases d with
    | false => exact planOwn_of h2.2
    | true => exact planOwn_of h2.1
  have hsam : ∀ j : Fin (shapesOf (parL Zp Bs.G₀ l d)).length, sampledAt (parL Zp Bs.G₀ l d) j := by
    rw [eP]
    exact sampled_at l hl d
  have hfit : BookFits s.book := Meaning.K2.bookFits_reached O hreach (by
    rw [Meaning.K2.front_len h.scope h.reads O]
    have h6 : IM.k1Ix l d ≤ 6 := by unfold IM.k1Ix; split <;> split <;> omega
    show 14 * l + IM.k1Ix l d + 2 ≤ 353
    omega)
  rw [IM.placesW_full, IM.linksW_full, ← head_N_is h] at hs ⊢
  rw [IM.placesW_full, ← head_N_is h] at hbk
  have hY := K1.yesOf_of_yes hu hy z
  refine held_later h.𝔇.N Mg z l hl d _ _ (K1.hinj_of H l hl d) (K1.trees_of H l hl d)
    (K1.msgs_of H l hl d) s s' hs
    (fun u _ h0 => held_old_later Mg hH Zp Bs.G₀ l d X arrs (z, s) (z, s') hY u h0) fun u hu' => ?_
  rw [hH]
  exact held_new_later h.𝔇.N Zp Bs.G₀ l d X arrs (z, s) (z, s') hY hbk hfit
    (K1.hP_of H hs' l hl d) hsam hO u hu'

end ProofFile.Honest.K1
