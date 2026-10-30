-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/ExchangeAtPin.lean: the kind "the code switch" (K2): THE KIND's
SHARE OF "THE EXCHANGE" (`ExchangeAtS`, Honest/Thread/SharesS.lean) AT THE ITEM "pin seg 0": behind
a switch's step, at every continuation of the challenges heard, each seat that the table's numbers
pin there answers: UNDER THE RECORD AT A SWITCH (`K2SeatedL`, Honest/K2/SeatedL.lean), WHICH IS A
BUNDLE OF PREMISES. Three statements with their proofs; no definition.

  `pin_entry_switch`     one pinned seat, at an entry whose shape is the message's
  `pins_behind_switch`   all seats of "pin seg 0", behind the member's step
  `exchange_pin_switch`  THE END

AFTER THE FORM OF the shared sending's `pin_entry`, `pins_behind`, `exchange_pin`
(Honest/K1/Law/ExchangeAtPins.lean, of other authors): the three proofs here go as those, step by
step, with the switch's own pieces in the sending's stead: `step_at_switch`
(Honest/K2/Law/StepAtSwitch.lean) for the member's step · `ans_at_cut`, `fit_trimmed`
(Honest/K2/Law/AnsAtCut.lean) for the law on a sample's answers: a switch's second round also draws
positions · `tab_rows_off` (Honest/K2/Law/TabRowsOff.lean) for the witness's table: the tie on the
Script's message is asked off the pad alone. Called as they stand: `first_at_border`, `shapeAt_fin`,
`held_at_main`, `held_at_mask` (of the same authors). `sendingPar_sent`, `sendingPar_shape`
(Honest/K2/Law/Counts.lean): two spellings of the switch's messages and their shapes.

Limits. EVERYTHING STANDS UNDER THE RECORD: thirty premises, none shown here at any letters; that
they can hold together is shown nowhere. OF THE THIRTY, TWENTY-FOUR ARE SPENT FOR THIS ITEM: here:
member · placeAt · sends · books · port · seedsNo · nonZeroNo · answersNo · firstNo · noWord · msgs
· pads · seats · ans · numbered · sits · in `step_at_switch`: shape · half · serves · roomy ·
placeOk · trees · closes · publicAt, and answersNo again. SIX ARE NOT: decides · treesNo · rowM ·
later · asks · carryM: they stand in the binder and are read by no step of these proofs. `msgs` AND
`pads` ARE TIES TO A SCRIPT: no Script is laid. At a kept copy `msgs` asks that the copy's entries
off the pad are what the Script's message holds at the original's number: no law pays that yet.
UNDER "Stepped": where the book does not cover the part's count no step is there, and the end holds
of nothing. IT SPEAKS OF ANSWERS, and these hang on the pads. It says that a pinned seat answers:
nothing on what an answer shows. Nothing on the item "row seg (sample 0)". Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.StepAtSwitch
import Johnson.Desc.ProofFile.Honest.K2.Law.AnsAtCut
import Johnson.Desc.ProofFile.Honest.K2.Law.TabRowsOff

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open OnBytes OnBytes.Slice OnBytes.Means Cb Cb.Ood Johnson.Pack VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2 rounds)
open VerifiableInference.Desc.Sound (MsgT Mem SitsAt smpNamed smpNamed_at numAt msgsOf)
open VerifiableInference.Desc.K1 (sampledAt shapesOf smpAt)
open ProofFile.Honest.FirstThread (Letters)
open ProofFile.Honest.K1 (seatAtMember)
open Johnson.Prover.Send (answers shapeAt)

variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr X P Cells Tok : Type}
variable {L : Letters Bk Cl W₀ Rc Xi Tr X P Cells Tok MsgT} {b : Nat} {blk : Block S Cl}
  {D : RowDataOf Xi} {readers : Local W₀ Rc Xi Tr → Readers} {lay : OnBytes.Params.ReqLayout}
  {segs : List SegmentPub} {p : SwitchPlace} {q : P2} {before : S → Except String S}
  {after : S → S → Except String S} {seg first : Nat} {Zp : ProofFile.Pub} {arr : ℕ → ℕ → ℕ}
  {seats₀ : List (ℕ × ℕ)} {ms : List Mem} {rad : ℕ → ℕ}

/-- **ONE PINNED SEAT**, at an entry e (shape and radius) whose shape is the message's. T: any table
that is the rows that the switch lays. Behind a yes of the member (hdec) at a state of the thread in
front of the member (hThr). NOT IN FRONT OF A LAW OVER COINS. -/
theorem pin_entry_switch
    (R : K2SeatedL L b blk D readers lay segs p q before after seg first Zp arr seats₀ ms rad)
    {k : Coins Bk} {s s' : S} {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env}
    (hThr : Thr L.thread b k s m E) {r₁ r₂ : Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (hdec : blk.decide s [r₁, r₂] gs = .ok s') (hfit : roundsFit (rounds q) [r₁, r₂] = true)
    (hok : (r₁.drawn.elems.all fun x =>
      x.1 < fieldPrimeWord && x.2.1 < fieldPrimeWord && x.2.2 < fieldPrimeWord) = true)
    (V : ℕ → Johnson.Prover.Send.Rows)
    (hans : r₂.vals = (answers (switchPar p) (K1.stAt (switchPar p) s.st.oracles.size)
      s.st.oracles.size
      (Johnson.Prover.Send.held (fun _ _ _ => 0) s.st.oracles.size (switchPar p) V)
      (VerifiableInference.Desc.K1.seedsOf (switchPar p) r₁)).map .answer)
    (n : ℕ) (hn : n < (switchPar p).sent.size) (ha : (shapeAt (switchPar p) n).answers ≠ 0)
    (T : MsgT) (hT : T = K1.rowsMsg (shapeAt (switchPar p) n) (V n)) (e : OracleShape × ℕ)
    (he : e.1 = shapeAt (switchPar p) n) :
    ∃ z : (portOmZ (switchPar p).codes e.1 e.2).Smp,
      smpAt (switchPar p).codes e.1 e.2 s'.st (s.st.oracles.size + n) = some z ∧
        (portOmZ (switchPar p).codes e.1 e.2).Z.val z.1
          (fun j => match (j : (Fin e.1.mainRows × Fin (pMain (switchPar p).codes e.1).ell) ⊕
              (Fin e.1.maskRows × Fin (pMask (switchPar p).codes e.1).ell)) with
            | .inl x => T false x.1.val x.2.val
            | .inr x => T true x.1.val x.2.val) = z.2 := by
  obtain ⟨hf', hl'⟩ := fit_trimmed (switchPar p) q R.seedsNo R.nonZeroNo R.answersNo hfit
  have hl : (shapesOf (switchPar p)).length = (switchPar p).sent.size := by simp [shapesOf]
  have hsh := K1.shapeAt_fin (switchPar p) ⟨n, hl ▸ hn⟩
  have hk : sampledAt (switchPar p) ⟨n, hl ▸ hn⟩ := by
    show (VerifiableInference.Desc.K1.shapeAt (switchPar p) ⟨n, hl ▸ hn⟩).answers ≠ 0
    rw [hsh]
    exact ha
  obtain ⟨z, hz, hv⟩ := ans_at_cut (switchPar p) rad R.port
    (fun t a₁ a₂ g hy => R.sends k s m E t a₁ a₂ g hThr hy) hdec
    (R.books k s m E _ _ _ _ hThr hdec) hf' hl' hok V hans ⟨n, hl ▸ hn⟩ hk e (he.trans hsh.symm)
  refine ⟨z, hz, ?_⟩
  rw [← hv]
  congr 1
  funext j
  obtain ⟨sh, ee⟩ := e
  obtain rfl : sh = shapeAt (switchPar p) n := he
  subst hT
  rcases j with x | x
  · exact (K1.held_at_main (switchPar p) _ _ V n hn x.1.val x.2.val x.1.isLt).symm
  · exact (K1.held_at_mask (switchPar p) _ _ V n hn x.1.val x.2.val x.1.isLt).symm

/-- **THE PINS**: behind the member's step, at every continuation of the challenges heard, each seat
of "pin seg 0" answers. It speaks of answers, and these hang on the pads. In front stand hA (the
thread's stand, `ThrS`) and hS ("Stepped", which holds that the member said yes at this run).
NOT IN FRONT OF A LAW OVER COINS. -/
theorem pins_behind_switch
    (R : K2SeatedL L b blk D readers lay segs p q before after seg first Zp arr seats₀ ms rad)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop) {k : Coins Bk} {s s' : S}
    {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc Xi Tr) X} {cols : List OpenedColumn}
    (hA : ThrS L.thread Said b k s m E) (hd : drawsFit blk.rounds ds = true)
    (hS : L.thread.Stepped blk k s m E ds y cols s') (x : ℕ × ℕ) (hx : x ∈ L.N.sent seg 0)
    (pp : P) (yy : Strs) (ds' : List Fmt.Drawn) :
    L.ans x.1 x.2 (pp, s') yy (L.Q.wit k y.2.st.input (y.2.st.heard ++ ds')) := by
  obtain ⟨n, hn, ha, rfl⟩ := (R.seats x).1 hx
  obtain ⟨c, V, r₁, r₂, gs, hc, hV, hdec, hfit, hok, hans, hin, hheard⟩ :=
    step_at_switch R Said hA hd hS
  have hf : s.st.oracles.size = first := K1.first_at_border L Said hA R.placeAt R.firstNo
  have hlen : m.st.heard.length = L.thread.front + roundsTo L.bs b := by
    have e := drawsFit_length _ _ hA.1.2.1
    rw [e, List.length_append]
    rfl
  have htk : (m.st.heard ++ ds ++ ds').take (L.thread.front + roundsTo L.bs b) = m.st.heard := by
    rw [List.append_assoc, ← hlen, List.take_left]
  have hn' : n < (switchSent p.sizes p.others).size := by
    have e : n < (sendingPar p.sizes.codes (switchSent p.sizes p.others)).sent.size := hn
    rwa [sendingPar_sent] at e
  have hT := tab_rows_off L.Q L.valid _ 0 D readers (lotClosingAt lay segs) p _ n _ _ _
    (R.msgs n hn) (R.pads n hn) R.noWord hn' k hc m.st.input hA.1.2.2.2.2.2.2
    (m.st.heard ++ ds ++ ds')
    (by rw [List.length_append, List.length_append, hlen]; omega) (by rw [htk]; exact hV)
  rw [← sendingPar_shape p.sizes.codes (switchSent p.sizes p.others) n] at hT
  rw [R.ans]
  refine ⟨(R.sits n hn ha).1, fun μ hμ hs => ?_⟩
  have hsh : (μ.1.l.get μ.2).1 = shapeAt (switchPar p) n := (R.sits n hn ha).2 μ hμ hs
  obtain ⟨z, hz, hv⟩ :=
    pin_entry_switch R hA.1 hdec hfit hok _ hans n hn ha _ hT (μ.1.l.get μ.2) hsh
  have hseat : μ.1.seat μ.2 = seatAtMember L.bs b (switchPar p) n := hs
  have hq : μ.1.seat μ.2 ∈ seats₀ := by rw [hseat]; exact (R.numbered n hn ha).1
  have hnum : numAt seats₀ μ = s.st.oracles.size + n := by
    show seats₀.idxOf (μ.1.seat μ.2) = _
    rw [hseat, (R.numbered n hn ha).2, hf]
  refine ⟨z, ?_, ?_⟩
  · show smpNamed (switchPar p).codes seats₀ _ μ.1 μ.2 = some z
    rw [smpNamed_at (switchPar p).codes seats₀ _ μ.1 μ.2 hq]
    show smpAt (switchPar p).codes _ _ s'.st (numAt seats₀ μ) = some z
    rw [hnum]
    exact hz
  · rw [← hv, hin, hheard]
    congr 1
    funext j
    show msgsOf (switchPar p).codes μ.1.l μ.1.seat arr _ μ.2 j = _
    unfold msgsOf
    rw [hseat]
    rcases j with x | x
    · exact congrArg (fun sh => (L.Q.wit k m.st.input (m.st.heard ++ ds ++ ds')).tab
        (switchPar p).codes sh _ _ _ false x.1.val x.2.val) hsh
    · exact congrArg (fun sh => (L.Q.wit k m.st.input (m.st.heard ++ ds ++ ds')).tab
        (switchPar p).codes sh _ _ _ true x.1.val x.2.val) hsh

/-- **THE KIND's SHARE AT "pin seg 0".** It speaks of answers, and these hang on the pads.
`ExchangeAtS` itself asks the same two in front: the thread's stand and a step in which the member
said yes. NOT IN FRONT OF A LAW OVER COINS. FREE LETTERS, bound by the record alone:
D, the filling · readers, a function of all of `Local W₀ Rc Xi Tr` · rad, the radii · before and
after, the place's own steps · and, inside the field `sends`, under "there is": the type Lt and the
start d, which stands in no equation with the record s. -/
theorem exchange_pin_switch
    (R : K2SeatedL L b blk D readers lay segs p q before after seg first Zp arr seats₀ ms rad)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop) :
    ExchangeAtS L.thread Said b (.pin seg 0) := by
  intro blk' hblk k s m E ds y cols s' hA hd hS ds' i hi
  obtain rfl := List.mem_singleton.1 hi
  obtain rfl : blk' = blk := Option.some.inj (hblk.symm.trans R.member)
  intro x hx
  exact pins_behind_switch R Said hA hd hS x hx _ _ ds'

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.pin_entry_switch
#print axioms ProofFile.Honest.K2.Law.pins_behind_switch
#print axioms ProofFile.Honest.K2.Law.exchange_pin_switch
