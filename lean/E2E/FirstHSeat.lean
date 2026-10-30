-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/FirstHSeat.lean: the debts at a sending of the key file's first chain, at the thread `T₁`
(E2E/FirstHFill.lean), under one record of what is public at that sending, and what rides past a
member that keeps the older messages.

  `SendSeat`: the record: the member is a sending of the job; the half stands at its place; the job
    fits; the job's data read what was heard alone; the numbers of the message.
  `seat_step`: the member's step, unpacked, at the thread.
  `wit_msg`: the message that the witness holds is the words that the part lays.
  `seat_srow`, `seat_pin`: the two items that the sending owes.
  `ride_*`, `rides_past`: what is open stays, behind a step that keeps the older messages.

Limits. Conditional on the record and on the thread in front. `told` (the description tells the tree)
is a field. Nothing on the batching, on W's row (Eval) or on any property.
-/
import E2E.FirstHSends
import E2E.KeyBehind
import Johnson.Desc.Key.RowsCarry

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace AtPublicFiles.FirstH
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Means
open VerifiableInference.Desc (Block Place OpenedColumn)
open VerifiableInference.Desc.Key (Xi FirstState Claim KItem Source LaterPlaces KPlan KReaders
  KBook sentB shape₁ start₁ RowHolds valOf TensorRowHolds matOf mkOf)
open Johnson.RunOne.KeyRows1 (plan₁ readers₁ book₁ slots₁)
open Johnson.RunOne.KeyRows23 (atSix)
open Johnson.Prover.Send (answers held)
open AtPublicFiles.KeyThread (KeyFill laid₁ D one₀ rowsFirst)
open AtPublicFiles.KeyFile (KeyParts keyProver In1)
open ProofFile.Honest
open ProofFile.Honest.K1 (SendJob proverSideOfSending sendFits stAt rowsLaid lentCut dueR)

/-- The book-keeping at border b. -/
abbrev ShapeAt (Xs : Source) (b : Nat) (s : FirstState) : Bool :=
  shape₁ (plan₁ (one₀ Xs)) (readers₁ (one₀ Xs)) (book₁ (one₀ Xs)) 2 (slots₁ (one₀ Xs)) b s

/-- What the book-keeping's Bool says of a message. -/
theorem of_sentB {S : Type} {K : KPlan} {X : KReaders S} {s : S} {n o : Nat}
    (ho : K.orc n = some o) (h : sentB K X s n = true) :
    ∃ x : OnBytes.Oracle, (X.st s).oracles[o]? = some x ∧ x.sampled = true ∧
      x.sampleRows.size ≠ 0 := by
  unfold sentB at h
  rw [ho, Option.bind_some] at h
  cases hx : (X.st s).oracles[o]? with
  | none =>
    rw [hx] at h
    cases h
  | some x =>
    rw [hx] at h
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    exact ⟨x, rfl, h.1, h.2⟩

section
variable {Bk : ProverCoinCounts} {W₀ Rc X₀ X' Wk : Type} (Xs : Source) (N : H2U.PlaceNums) (Pl : LaterPlaces)
  (K : KeyParts W₀ Rc X₀ X' Wk) (f : W₀ → Weights) (Q : LaterFill Bk W₀ Rc) (w₀ : W₀) (rc : Rc)
  (x : Xi)

/-- The thread at these letters. -/
abbrev Th : Thread Bk (D Xs N Pl).S₁ (D Xs N Pl).Cl (In1 W₀ Rc) (In1 W₀ Rc) X' Xi :=
  T₁ Xs N Pl K f Q w₀ rc x

/-- The filling at these letters. -/
abbrev Fl : KeyFill Bk W₀ Rc HCells HTab Unit Unit := fillH Xs N Pl K f Q x

/-- **What is public at a sending**: number b of the chain sends message n of the witness by the job
J. -/
structure SendSeat (b n : Nat) (J : SendJob (In1 W₀ Rc) X') : Prop where
  member : ∃ blk, (Th Xs N Pl K f Q w₀ rc x).bs[b]? = some blk ∧
    (blk.place = J.P.place ∧ blk.rounds = VerifiableInference.Desc.K1.rounds J.P ∧
      blk.oracles = VerifiableInference.Desc.K1.oracles J.P) ∧
    ∀ {s s' : FirstState} {r₁ r₂ : Fmt.RoundView} {gs : List (List (Nat × List UInt64))},
      blk.decide s [r₁, r₂] gs = .ok s' → SendYes J.P s s' r₁ r₂
  half : ((Th Xs N Pl K f Q w₀ rc x).hs.find? fun g => g.place == J.P.place) = some (proverSideOfSending J)
  fits : sendFits J.P J.ride = true
  data : ∀ w (fr fr' : Front X'), fr.heard = fr'.heard → J.data w fr = J.data w fr'
  sent : 0 < J.P.sent.size
  number : ∀ s, ShapeAt Xs b s = true → s.d.st.oracles.size = J.first
  sampled : ∀ s, ShapeAt Xs (b + 1) s = true →
    sentB (plan₁ (one₀ Xs)) (readers₁ (one₀ Xs)) s n = true
  orc : (plan₁ (one₀ Xs)).orc n = some J.first
  num : (plan₁ (one₀ Xs)).num J.first = some n
  small : n < 3
  msg : ∀ k h, (Fl Xs N Pl K f Q x).msg n k w₀ rc h =
    msgRun J K.own₀ k (⟨w₀, rc, x, ()⟩ : In1 W₀ Rc) h
  fixed : (Fl Xs N Pl K f Q x).fixedMsg n = roundsTo (D Xs N Pl).first.blocksInOrder b
  told : ∃ o, (D Xs N Pl).oracleAt (atSix n).1 = some o
  seat : arrH (atSix n).1 (atSix n).2 = n
  table : ∀ τ, τ < J.P.trees.length → ∀ k w h,
    (Th Xs N Pl K f Q w₀ rc x).table (.own (treesTo (Th Xs N Pl K f Q w₀ rc x).bs b + τ)) k w h =
      ProofFile.Honest.K1.treeTbl (Th Xs N Pl K f Q w₀ rc x).chain id J K.own₀ τ k w h
  fixedTree : ∀ τ, τ < J.P.trees.length →
    (Th Xs N Pl K f Q w₀ rc x).fixed (.own (treesTo (Th Xs N Pl K f Q w₀ rc x).bs b + τ)) =
      (Th Xs N Pl K f Q w₀ rc x).front + roundsTo (Th Xs N Pl K f Q w₀ rc x).bs b

variable {Xs N Pl K f Q w₀ rc x} {b n : Nat} {J : SendJob (In1 W₀ Rc) X'}

/-- **The member's step, unpacked, at the thread.** -/
theorem seat_step (h : SendSeat Xs N Pl K f Q w₀ rc x b n J)
    {blk : Block (D Xs N Pl).S₁ (D Xs N Pl).Cl} (hb : (Th Xs N Pl K f Q w₀ rc x).bs[b]? = some blk)
    {k : Coins Bk} {s s' : FirstState} {m : Mid (In1 W₀ Rc) X'} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (In1 W₀ Rc) X'} {cols : List OpenedColumn}
    (hT : Thr (Th Xs N Pl K f Q w₀ rc x) b k s m E) (hd : drawsFit blk.rounds ds = true)
    (hS : (Th Xs N Pl K f Q w₀ rc x).Stepped blk k s m E ds y cols s') :
    ∃ (c : Cs (dueR J.P J.ride)) (r₁ r₂ : Fmt.RoundView),
      lentCut k 0 ⟨J.P.place, 0⟩ (dueR J.P J.ride) = some c ∧ SendYes J.P s s' r₁ r₂ ∧
      r₂.vals = (answers J.P (stAt J.P s.d.st.oracles.size) s.d.st.oracles.size
        (held (fun _ _ _ => 0) s.d.st.oracles.size J.P
          (rowsLaid J K.own₀ c m.st.input m.st.heard))
        (VerifiableInference.Desc.K1.seedsOf J.P r₁)).map .answer ∧
      y.2.st.input = m.st.input ∧ y.2.st.heard = m.st.heard ++ ds := by
  obtain ⟨blk₀, hb₀, hsh, hyes⟩ := h.member
  rw [hb] at hb₀
  obtain rfl : blk = blk₀ := Option.some.inj hb₀
  obtain ⟨c, r₁, r₂, gs, hc, hdec, hans, hin, hheard⟩ :=
    step_send (Th Xs N Pl K f Q w₀ rc x) blk J K.own₀ (fun z : FirstState => z.d.st) hsh h.half
      h.fits rfl h.data (h.number s hT.2.2.1.1) hd hS
  exact ⟨c, r₁, r₂, hc, hyes hdec, hans, hin, hheard⟩

/-- **The witness's message is the words that the part lays.** -/
theorem wit_msg (h : SendSeat Xs N Pl K f Q w₀ rc x b n J) {k : Coins Bk}
    {c : Cs (dueR J.P J.ride)} (hc : lentCut k 0 ⟨J.P.place, 0⟩ (dueR J.P J.ride) = some c)
    (hd : List Fmt.Drawn) (hl : hd.length = roundsTo (D Xs N Pl).first.blocksInOrder b)
    (tail : List Fmt.Drawn) :
    ((Fl Xs N Pl K f Q x).wit k w₀ rc (hd ++ tail) []).msg n = fun part i =>
      held (fun _ _ _ => 0) J.first J.P
        (rowsLaid J K.own₀ c (⟨w₀, rc, x, ()⟩ : In1 W₀ Rc) hd) J.first part i := by
  show (Fl Xs N Pl K f Q x).msg n k w₀ rc
    ((if n < 3 then hd ++ tail else []).take ((Fl Xs N Pl K f Q x).fixedMsg n)) = _
  rw [if_pos h.small, h.fixed, ← hl, List.take_left, h.msg]
  unfold msgRun
  rw [hc]

/-- The reading of the statement's message at the witness. -/
theorem val_first (h : SendSeat Xs N Pl K f Q w₀ rc x b n J) (v : VerifiableInference.Desc.Wit HCells Unit HTab)
    (part : Part) (i : Nat) :
    readE (valOf (plan₁ (one₀ Xs)) readH v J.first part i) = v.msg n part i := by
  unfold valOf
  rw [h.num]
  exact toE_ofE _

/-- **The sample rows of the message hold at the witness.** -/
theorem seat_srow (h : SendSeat Xs N Pl K f Q w₀ rc x b n J)
    {blk : Block (D Xs N Pl).S₁ (D Xs N Pl).Cl} (hb : (Th Xs N Pl K f Q w₀ rc x).bs[b]? = some blk)
    {k : Coins Bk} {s s' : FirstState} {m : Mid (In1 W₀ Rc) X'} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (In1 W₀ Rc) X'} {cols : List OpenedColumn}
    (hT : Thr (Th Xs N Pl K f Q w₀ rc x) b k s m E) (hd : drawsFit blk.rounds ds = true)
    (hS : (Th Xs N Pl K f Q w₀ rc x).Stepped blk k s m E ds y cols s')
    (hF : (Th Xs N Pl K f Q w₀ rc x).Form (b + 1) k s' y.2)
    (hord : InOrder s'.d.st) :
    (Th Xs N Pl K f Q w₀ rc x).Items [.srow n] k s' y.2 (E.add y.1) := by
  obtain ⟨c, r₁, r₂, hc, hy, hans, hin, hheard⟩ := seat_step h hb hT hd hS
  have hv : m.st.input = ⟨w₀, rc, x, ()⟩ := hT.2.2.2.2.2.2.1
  have hn := h.number s hT.2.2.1.1
  have hlen : m.st.heard.length = roundsTo (D Xs N Pl).first.blocksInOrder b := by
    have e := drawsFit_length _ _ hT.2.1
    rw [List.length_append] at e
    exact e.trans (Nat.zero_add _)
  intro ds' i hi
  obtain rfl := List.mem_singleton.1 hi
  obtain ⟨x', hx', hsam, hrows⟩ := of_sentB h.orc (h.sampled s' hF.1)
  have hx₀ : s'.d.st.oracles[s.d.st.oracles.size + 0]? = some x' := by
    rw [hn, Nat.add_zero]
    exact hx'
  have hw : (Th Xs N Pl K f Q w₀ rc x).wit k y.2.st.input (y.2.st.heard ++ ds') =
      (Fl Xs N Pl K f Q x).wit k w₀ rc (m.st.heard ++ (ds ++ ds')) [] := by
    show (Fl Xs N Pl K f Q x).wit k y.2.st.input.w₀ y.2.st.input.rc (y.2.st.heard ++ ds') [] = _
    rw [hin, hv, hheard, List.append_assoc]
  have hm := wit_msg h hc m.st.heard hlen (ds ++ ds')
  show ∃ (o : Nat) (z : OnBytes.Oracle), (plan₁ (one₀ Xs)).orc n = some o ∧
    s'.d.st.oracles[o]? = some z ∧ z.sampled = true ∧ z.sampleRows.size ≠ 0 ∧
    ∀ r ∈ z.sampleRows.toList, RowHolds readH.same s'.d.st
      (valOf (plan₁ (one₀ Xs)) readH ((Th Xs N Pl K f Q w₀ rc x).wit k y.2.st.input
        (y.2.st.heard ++ ds'))) r
  rw [hw]
  refine ⟨J.first, x', h.orc, hx', hsam, hrows, ?_⟩
  refine rows_hold_at_yes hy _ hans 0 h.sent x' hx₀ hord _ fun part i => ?_
  rw [hn, Nat.add_zero, val_first h, hm, hv]

/-- **The pin of the message.** -/
theorem seat_pin (h : SendSeat Xs N Pl K f Q w₀ rc x b n J)
    {k : Coins Bk} {s' : FirstState} {m : Mid (In1 W₀ Rc) X'} {E : Env}
    (hF : (Th Xs N Pl K f Q w₀ rc x).Form (b + 1) k s' m) :
    (Th Xs N Pl K f Q w₀ rc x).Items [.pin n] k s' m E := by
  intro ds' i hi
  obtain rfl := List.mem_singleton.1 hi
  obtain ⟨o, ho⟩ := h.told
  obtain ⟨x', hx', hsam, -⟩ := of_sentB h.orc (h.sampled s' hF.1)
  refine ⟨o, (), ho, ?_, trivial⟩
  show ((plan₁ (one₀ Xs)).orc (arrH (atSix n).1 (atSix n).2)).bind
    (fun q => (s'.d.st.oracles[q]?).bind fun z => if z.sampled = true then some () else none) =
      some ()
  rw [h.seat, h.orc]
  show (s'.d.st.oracles[J.first]?).bind _ = _
  have hx₂ : s'.d.st.oracles[J.first]? = some x' := hx'
  rw [hx₂]
  simp [hsam]

/-- **It plays**, from the thread alone. -/
theorem seat_plays (h : SendSeat Xs N Pl K f Q w₀ rc x b n J) :
    Plays (Th Xs N Pl K f Q w₀ rc x) b := by
  obtain ⟨blk, hb, hsh, -⟩ := h.member
  exact plays_send _ b blk J K.own₀ hb hsh h.half h.fits h.data h.table h.fixedTree

/-- **What the step of a sending keeps.** -/
theorem seat_stays (h : SendSeat Xs N Pl K f Q w₀ rc x b n J)
    {blk : Block (D Xs N Pl).S₁ (D Xs N Pl).Cl} (hb : (Th Xs N Pl K f Q w₀ rc x).bs[b]? = some blk)
    {k : Coins Bk} {s s' : FirstState} {m : Mid (In1 W₀ Rc) X'} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (In1 W₀ Rc) X'} {cols : List OpenedColumn}
    (hT : Thr (Th Xs N Pl K f Q w₀ rc x) b k s m E) (hd : drawsFit blk.rounds ds = true)
    (hS : (Th Xs N Pl K f Q w₀ rc x).Stepped blk k s m E ds y cols s') : StaysK s s' := by
  obtain ⟨c, r₁, r₂, -, hy, -⟩ := seat_step h hb hT hd hS
  exact stays_of_yes hy

/-! ## What rides past a member that keeps the older messages -/

/-- "Unmarked" says nothing of the state. -/
theorem ride_unmarked {k : Coins Bk} {m : Mid (In1 W₀ Rc) X'} {s s' : FirstState}
    {y y' : VerifiableInference.Desc.Strs} {v} :
    (Th Xs N Pl K f Q w₀ rc x).means m.st.input .unmarked ((Th Xs N Pl K f Q w₀ rc x).seat k m s) y v →
    (Th Xs N Pl K f Q w₀ rc x).means m.st.input .unmarked ((Th Xs N Pl K f Q w₀ rc x).seat k m s') y' v :=
  fun _ => rfl

/-- The stored table's pin reads what the chain was handed. -/
theorem ride_pinT {k : Coins Bk} {m : Mid (In1 W₀ Rc) X'} {s s' : FirstState}
    {y y' : VerifiableInference.Desc.Strs} {v} :
    (Th Xs N Pl K f Q w₀ rc x).means m.st.input .pinT ((Th Xs N Pl K f Q w₀ rc x).seat k m s) y v →
    (Th Xs N Pl K f Q w₀ rc x).means m.st.input .pinT ((Th Xs N Pl K f Q w₀ rc x).seat k m s') y' v :=
  id

/-- "In range" reads the witness alone. -/
theorem ride_range {l : Nat} {k : Coins Bk} {m : Mid (In1 W₀ Rc) X'} {s s' : FirstState}
    {y y' : VerifiableInference.Desc.Strs} {v} :
    (Th Xs N Pl K f Q w₀ rc x).means m.st.input (.inRange l) ((Th Xs N Pl K f Q w₀ rc x).seat k m s) y v →
    (Th Xs N Pl K f Q w₀ rc x).means m.st.input (.inRange l) ((Th Xs N Pl K f Q w₀ rc x).seat k m s') y' v :=
  id

/-- **A pin rides** over a step that keeps the older messages. -/
theorem ride_pin {i : Nat} {k : Coins Bk} {m : Mid (In1 W₀ Rc) X'} {s s' : FirstState}
    {y y' : VerifiableInference.Desc.Strs} {v} (hs : StaysK s s') :
    (Th Xs N Pl K f Q w₀ rc x).means m.st.input (.pin i) ((Th Xs N Pl K f Q w₀ rc x).seat k m s) y v →
    (Th Xs N Pl K f Q w₀ rc x).means m.st.input (.pin i) ((Th Xs N Pl K f Q w₀ rc x).seat k m s') y' v := by
  rintro ⟨o, z, ho, hz, -⟩
  refine ⟨o, (), ho, ?_, trivial⟩
  change ((plan₁ (one₀ Xs)).orc (arrH (atSix i).1 (atSix i).2)).bind
    (fun q => (s.d.st.oracles[q]?).bind fun z => if z.sampled = true then some () else none) =
      some z at hz
  show ((plan₁ (one₀ Xs)).orc (arrH (atSix i).1 (atSix i).2)).bind
    (fun q => (s'.d.st.oracles[q]?).bind fun z => if z.sampled = true then some () else none) =
      some ()
  obtain ⟨q, hq, hz⟩ := Option.bind_eq_some_iff.1 hz
  obtain ⟨a, ha, hz⟩ := Option.bind_eq_some_iff.1 hz
  obtain ⟨a', ha', -, es, -⟩ := hs.2 q a ha
  rw [hq, Option.bind_some, ha', Option.bind_some, es]
  by_cases e : a.sampled = true
  · rw [if_pos e]
  · rw [if_neg e] at hz
    cases hz

/-- **The sample rows ride**, where the statement in front is in order. -/
theorem ride_srow {i : Nat} {k : Coins Bk} {m : Mid (In1 W₀ Rc) X'} {s s' : FirstState}
    {y y' : VerifiableInference.Desc.Strs} {v} (hs : StaysK s s') (hord : InOrder s.d.st) :
    (Th Xs N Pl K f Q w₀ rc x).means m.st.input (.srow i) ((Th Xs N Pl K f Q w₀ rc x).seat k m s) y v →
    (Th Xs N Pl K f Q w₀ rc x).means m.st.input (.srow i) ((Th Xs N Pl K f Q w₀ rc x).seat k m s') y' v := by
  rintro ⟨o, z, ho, hz, hsam, hsz, hrows⟩
  obtain ⟨z', hz', esh, esam, erows⟩ := hs.2 o z hz
  have hE : Extends s.d.st s'.d.st :=
    ⟨hs.1, fun q a ha => (hs.2 q a ha).imp fun _ h => ⟨h.1, h.2.1⟩⟩
  refine ⟨o, z', ho, hz', by rw [esam]; exact hsam, by rw [erows]; exact hsz, fun r hr => ?_⟩
  rw [erows] at hr
  exact (VerifiableInference.Desc.Key.rowHolds_extends rdE hE (hord.samples o z hz r hr) _).2
    (hrows r hr)

end

end AtPublicFiles.FirstH

#print axioms AtPublicFiles.FirstH.seat_plays
#print axioms AtPublicFiles.FirstH.seat_stays
#print axioms AtPublicFiles.FirstH.ride_pin
#print axioms AtPublicFiles.FirstH.ride_srow
#print axioms AtPublicFiles.FirstH.of_sentB
#print axioms AtPublicFiles.FirstH.seat_step
#print axioms AtPublicFiles.FirstH.wit_msg
#print axioms AtPublicFiles.FirstH.seat_srow
#print axioms AtPublicFiles.FirstH.seat_pin
