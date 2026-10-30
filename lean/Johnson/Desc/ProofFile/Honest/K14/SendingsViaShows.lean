-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/SendingsViaShows.lean: ShowsU and ShowsO
(Honest/K14/Exchange2.lean) WHERE THE TWO SENDINGS ARE CALLS OF THE SHARED SENDING's PART
(Honest/K14/SendingsVia.lean): what the calls show in their second rounds is what the honest tables'
out-of-domain (OOD) answers are, at what an honest prover holds as Honest/K14/Holds2.lean lays it
(holds2), UNDER Plan2, SendShapes, sendFits AT THE CALL AND HalfVia. Every statement on a call
stands at the public data ⟨Q, 0, n⟩: "LIN point" is the chain's round number 0, typed.

  firstMask_noAnswer   the first mask has no OOD answer, where withU returns the notices
  point_front     the challenge number 0 is the same with one more challenge behind: a fact on lists
  viaU_same, viaOmega_same   below the tables' sizes (viaU_same: at a sampled message;
                  viaOmega_same: at both messages): the calls' rows are the tables that this kind's
                  own text lays of the same input, challenges and coins, read; under Plan2,
                  SendShapes, sendFits and one challenge heard in front
  HalfVia, viaDeclared_like   the first half at a call's place among O.hs has one part, the call's
                  lifted part (the like of HalfIn, Honest/K14/SendingsShows.lean, for the other
                  part); what via_moved asks of a sub-protocol reads its rounds and oracle messages
                  alone
  showsU_via, showsO_via   **ShowsU and ShowsO at the calls**, each under Plan2, HalfVia, sendFits,
                  O.holds = holds2 and SendShapes
  exchange_via    so Exchange at both sendings, with no premise on what is shown, under these at
                  both calls and: no two messages have one tenant

What is assumed. The plan's public facts (Plan2). SendShapes. sendFits: the shared part's own public
test, at the call. HalfVia. In exchange_via: no two messages have one tenant. What the prover holds
is holds2, as for this kind's own text. A REMARK, WHICH NO STATEMENT BEARS: the OOD answers that
ShowsU compares hang, of holds2, on none but Rw and cU.pad, those that ShowsO compares on none but
Rw, cOmega.pad and cSp.mask: so both would stand at any other first mask and any other tails. What
speaks for it: the first mask has no OOD answer (firstMask_noAnswer), and the answers do not hang on
the words in front (Honest/K14/AnswersAny.lean: answersAt_any). BY TYPE the two sentences name more:
ShowsU the field w₀ and the rows rowsU, which take Rw, cU and cMask whole; ShowsO the words in front
(words1, made of w₀ and rowsU) and rowsO, which take Rw, cOmega and cSp whole
(Johnson/Desc/K14/Honest/ChainHolds.lean). That the other fields are what the calls lay is
Honest/K14/SendingsViaHolds.lean's. In viaU_same and
viaOmega_same: at least one challenge has been heard in front of the sending (at the thread: from
Thr, which also has that the first is the point). No premise on n, the number that o_u gets among
the statement's messages ("send o_u" is told n for its first message, "send o_omega" n and the count
of o_u's sending): the answers do not hang on it.
What is not claimed. Nothing on a message that is not sampled, on tails or on symbols. That the book
lends to a call's part. Nothing on a verifier's decision, on soundness or on hiding.
-/
import Johnson.Desc.ProofFile.Honest.K14.SendingsViaAnswers
import Johnson.Desc.ProofFile.Honest.K14.SendingsViaRows
import Johnson.Desc.ProofFile.Honest.K14.SendingsShows
import Johnson.Desc.ProofFile.Honest.K1.PadLaw
import Johnson.Desc.K14.Law.PlanShapes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes OnBytes.Params
open OnBytes.Slice (rdE)
open VerifiableInference.Desc (K1.Msg.of)
open Desc.K14 (P14 first)
open Desc.K14.Honest
open Desc.K14.Law (parU parO)
open Johnson.Prover.Send (shapeAt)
open ProofFile.Honest.K1 (sendPart sendFits dueR startR ce)

variable {Bk : ProverCoinCounts} {W₀ Rc X₀ P₁ Wt : Type} {Q : P14} {sentU : Array OracleNotice} {layO : TreeLay}

/-- The first mask has no OOD answer. (The library has the fact in another form:
Desc.K14.Law.mask_unsampled, Johnson/Desc/K14/Law/LedgerMembersAt.lean. Where no mask is sent ahead
there is no message number 1, and this speaks of the default notice.) -/
theorem firstMask_noAnswer (hU : Desc.K14.withU Q.S = some sentU) :
    (sentU.getD 1 default).shape.answers = 0 := by
  obtain ⟨rest, hr, rfl⟩ := Desc.K14.Law.withU_cut hU
  unfold linWithU at hr
  by_cases hm : Q.S.masksAhead = true
  · rw [if_pos hm] at hr
    cases hn : linMaskNotice Q.S.testU Q.S.fold.leafClass with
    | none =>
      rw [hn] at hr
      cases hr
    | some n =>
      rw [hn] at hr
      obtain rfl : #[n] = rest := Option.some.inj hr
      unfold linMaskNotice at hn
      obtain ⟨s, -, rfl⟩ := Option.map_eq_some_iff.1 hn
      rfl
  · rw [if_neg hm] at hr
    obtain rfl : #[] = rest := Option.some.inj hr
    rfl

/-- The challenge number 0 is the same with one more challenge behind, where there is one. -/
theorem point_front (h : List Fmt.Drawn) (x : Fmt.Drawn) (hne : h ≠ []) :
    ((h ++ [x]).drop 0).take 1 = (h.drop 0).take 1 := by
  cases h with
  | nil => exact absurd rfl hne
  | cons a l => rfl

/-- **"send o_u": the call's rows are the tables of this kind's own text, read**, at a sampled
message (ha), under Plan2, SendShapes and sendFits at the call (hf), where at least one challenge
has been heard in front (hne), at a message's number below the count sent (hk) and an index below
the table's size (hj). -/
theorem viaU_same (hQ : Plan2 Q sentU layO) (hSh : SendShapes Q) (n : Nat)
    (hf : sendFits (viaU ⟨Q, 0, n⟩).P (viaU ⟨Q, 0, n⟩).ride = true)
    (own : Cs (dueR (viaU ⟨Q, 0, n⟩).P (viaU ⟨Q, 0, n⟩).ride)) (a : Ask) (h : List Fmt.Drawn)
    (x₀ : Fmt.Drawn) (sn : Seen) (hne : h ≠ []) (k : Nat)
    (hk : k < (viaU ⟨Q, 0, n⟩).P.sent.size) (ha : (shapeAt (viaU ⟨Q, 0, n⟩).P k).answers ≠ 0)
    (part : OnBytes.Part) (j : Nat)
    (hj : j < (K1.Msg.of (viaU ⟨Q, 0, n⟩).P.codes (shapeAt (viaU ⟨Q, 0, n⟩).P k)).size part) :
    ((viaU ⟨Q, 0, n⟩).rows own sn { input := a, heard := h ++ [x₀], own := () } 1
        k).word (shapeAt (viaU ⟨Q, 0, n⟩).P k) part j =
      rdE.val (wordsOf (jobU ⟨Q, 0⟩).Q.sent
        ((jobU ⟨Q, 0⟩).rows { input := a, heard := h ++ [x₀], own := () } (coinsE own).toArray) k
        part j) := by
  have eQ := jobU_par (Q := Q) hQ.facts.goes 0
  have hs0 : shapeAt (viaU ⟨Q, 0, n⟩).P 0 = Q.par.S.fold.u := by
    show ((jobU ⟨Q, 0⟩).Q.sent.getD 0 default).shape = _
    rw [eQ]
    exact (shapeAt_of_get (parU Q sentU) 0 ⟨Q.par.S.fold.u, Q.par.S.fold.leafClass⟩
      (by rw [Desc.K14.Law.parK1_sent]; exact withU_zero hQ.facts.goes)).1
  have hsz : (viaU ⟨Q, 0, n⟩).P.sent.size = 2 := by
    show (jobU ⟨Q, 0⟩).Q.sent.size = 2
    rw [eQ, Desc.K14.Law.parK1_sent, hQ.facts.goesTwo]
  have h1 : (shapeAt (viaU ⟨Q, 0, n⟩).P 1).answers = 0 := by
    show ((jobU ⟨Q, 0⟩).Q.sent.getD 1 default).shape.answers = 0
    rw [eQ, Desc.K14.Law.parK1_sent]
    exact firstMask_noAnswer hQ.facts.goes
  obtain rfl : k = 0 := by
    rcases Nat.lt_or_ge k 1 with hlt | hge
    · omega
    · have : k = 1 := by omega
      subst this
      exact absurd h1 ha
  have hz : (shapeAt (viaU ⟨Q, 0, n⟩).P 0).maskRows = 0 := by rw [hs0]; exact hSh.u.noMask
  cases part with
  | mask => exact word_none_same _ _ _ own 0 _ j hz
  | main =>
    have hm : (shapeAt (viaU ⟨Q, 0, n⟩).P 0).mainRows ≠ 0 := by
      rw [hs0]
      exact Nat.pos_iff_ne_zero.1 hSh.u.main
    refine word_main_same (viaU ⟨Q, 0, n⟩).P (viaU ⟨Q, 0, n⟩).ride _ own 0
      ((jobU ⟨Q, 0⟩).rows { input := a, heard := h ++ [x₀], own := () } (coinsE own).toArray)
      Q.S.fold.rowsHigh
      (Desc.K14.Honest.uAtE Q.S (elems (heardFrom
        ({ input := a, heard := h ++ [x₀], own := () } : State Ask Unit) 0 1)) a.rows)
      (msgCoins (jobU ⟨Q, 0⟩) (coinsE own).toArray 0) rfl (by rw [hs0]; exact hSh.u.overE) hz ha
      (by rw [hs0]; exact hSh.u.room)
      (ProofFile.Honest.K1.two_logEll_base _ _ (ProofFile.Honest.K1.fits_lengths _ _ hf)
        (ProofFile.Honest.K1.fits_code _ _ 0 hf hk hm)) (fun r i => ?_) (fun i => ?_) j hj
    · show vectorData Q.codes Q.S.fold.u Q.S.fold.rowsHigh (Desc.K14.Honest.uAtE Q.S
        (elems ((((h ++ [x₀]).take ((h ++ [x₀]).length - 1)).drop 0).take 1)) a.rows) r i = _
      rw [hs0, List.length_append, List.length_singleton, Nat.add_sub_cancel, List.take_left']
      · show _ = vectorData Q.codes Q.S.fold.u Q.S.fold.rowsHigh (Desc.K14.Honest.uAtE Q.S
          (elems (((h ++ [x₀]).drop 0).take 1)) a.rows) r i
        rw [point_front h x₀ hne]
      · rfl
    · show rdE.val ((coinsE own).toArray.getD (0 + i) zeroE) = ce own (0 + i)
      exact val_coinsE own (0 + i)

/-- **"send o_omega": the call's rows are the tables of this kind's own text, read**, at both
messages, under Plan2, SendShapes and sendFits at the call (hf), where at least one challenge has
been heard in front (hne), at a message's number below the count sent (hk) and an index below the
table's size (hj). -/
theorem viaOmega_same (hQ : Plan2 Q sentU layO) (hSh : SendShapes Q) (n : Nat)
    (hf : sendFits (viaOmega ⟨Q, 0, n⟩).P (viaOmega ⟨Q, 0, n⟩).ride = true)
    (own : Cs (dueR (viaOmega ⟨Q, 0, n⟩).P (viaOmega ⟨Q, 0, n⟩).ride)) (a : Ask)
    (h : List Fmt.Drawn) (x₀ : Fmt.Drawn) (sn : Seen) (hne : h ≠ []) (k : Nat)
    (hk : k < (viaOmega ⟨Q, 0, n⟩).P.sent.size) (part : OnBytes.Part) (j : Nat)
    (hj : j < (K1.Msg.of (viaOmega ⟨Q, 0, n⟩).P.codes
      (shapeAt (viaOmega ⟨Q, 0, n⟩).P k)).size part) :
    ((viaOmega ⟨Q, 0, n⟩).rows own sn
        { input := a, heard := h ++ [x₀], own := () } 1 k).word
        (shapeAt (viaOmega ⟨Q, 0, n⟩).P k) part j =
      rdE.val (wordsOf (jobOmega ⟨Q, 0⟩).Q.sent
        ((jobOmega ⟨Q, 0⟩).rows { input := a, heard := h ++ [x₀], own := () }
          (coinsE own).toArray) k part j) := by
  obtain ⟨w2, w0, w1⟩ := withOmega_two hQ.facts.two
  have sO : (viaOmega ⟨Q, 0, n⟩).P.sent = Desc.K14.withOmega Q.S :=
    Desc.K14.Law.parK1_sent Q 5 _ _
  have hs0 : shapeAt (viaOmega ⟨Q, 0, n⟩).P 0 = Q.par.S.omega :=
    (shapeAt_of_get (viaOmega ⟨Q, 0, n⟩).P 0 ⟨Q.par.S.omega, Q.par.S.omegaLeafClass⟩
      (by rw [sO]; exact w0)).1
  have hs1 : shapeAt (viaOmega ⟨Q, 0, n⟩).P 1 = Q.par.S.sharedSplit :=
    (shapeAt_of_get (viaOmega ⟨Q, 0, n⟩).P 1 ⟨Q.par.S.sharedSplit, Q.par.S.sharedSplitLeafClass⟩
      (by rw [sO]; exact w1)).1
  have hsz : (viaOmega ⟨Q, 0, n⟩).P.sent.size = 2 := by rw [sO]; exact w2
  have hlin := (VerifiableInference.Desc.Own.linFits_iff Q.codes Q.par.S).1 hQ.facts.lin
  have ha0 : (shapeAt (viaOmega ⟨Q, 0, n⟩).P 0).answers ≠ 0 := by
    rw [hs0]
    have := hlin.1.2.2.2.2.2.2.1.2.2.2
    omega
  have hz0 : (shapeAt (viaOmega ⟨Q, 0, n⟩).P 0).maskRows = 0 := by
    rw [hs0]
    exact hSh.omega.noMask
  have h30 : (shapeAt (viaOmega ⟨Q, 0, n⟩).P 0).mainDeg = 3 := by
    rw [hs0]
    exact hSh.omega.overE
  have hk2 : k = 0 ∨ k = 1 := by omega
  rcases hk2 with rfl | rfl
  · cases part with
    | mask => exact word_none_same _ _ _ own 0 _ j hz0
    | main =>
      have hm : (shapeAt (viaOmega ⟨Q, 0, n⟩).P 0).mainRows ≠ 0 := by
        rw [hs0]
        exact Nat.pos_iff_ne_zero.1 hSh.omega.main
      refine word_main_same (viaOmega ⟨Q, 0, n⟩).P (viaOmega ⟨Q, 0, n⟩).ride _ own 0
        ((jobOmega ⟨Q, 0⟩).rows { input := a, heard := h ++ [x₀], own := () }
          (coinsE own).toArray) Q.S.omegaRowsHigh
        (Desc.K14.Honest.omegaAtE Q.S (elems (heardFrom
          ({ input := a, heard := h ++ [x₀], own := () } : State Ask Unit) 0 1)) a.rows)
        (msgCoins (jobOmega ⟨Q, 0⟩) (coinsE own).toArray 0) rfl h30 hz0 ha0
        (by rw [hs0]; exact hSh.omega.room)
        (ProofFile.Honest.K1.two_logEll_base _ _ (ProofFile.Honest.K1.fits_lengths _ _ hf)
          (ProofFile.Honest.K1.fits_code _ _ 0 hf hk hm)) (fun r i => ?_) (fun i => ?_) j hj
      · show vectorData Q.codes Q.S.omega Q.S.omegaRowsHigh (Desc.K14.Honest.omegaAtE Q.S
          (elems ((((h ++ [x₀]).take ((h ++ [x₀]).length - 1)).drop 0).take 1)) a.rows) r i = _
        rw [hs0, List.length_append, List.length_singleton, Nat.add_sub_cancel, List.take_left']
        · show _ = vectorData Q.codes Q.S.omega Q.S.omegaRowsHigh (Desc.K14.Honest.omegaAtE Q.S
            (elems (((h ++ [x₀]).drop 0).take 1)) a.rows) r i
          rw [point_front h x₀ hne]
        · rfl
      · show rdE.val ((coinsE own).toArray.getD (0 + i) zeroE) = ce own (0 + i)
        exact val_coinsE own (0 + i)
  · have hm1 : (shapeAt (viaOmega ⟨Q, 0, n⟩).P 1).mainRows = 0 := by
      rw [hs1]
      exact sp_noMain hQ
    cases part with
    | main => exact word_noMain_same _ _ _ own 1 _ j hm1
    | mask =>
      have hz1 : (shapeAt (viaOmega ⟨Q, 0, n⟩).P 1).maskRows ≠ 0 := by
        intro h0
        have hs : (K1.Msg.of (viaOmega ⟨Q, 0, n⟩).P.codes
            (shapeAt (viaOmega ⟨Q, 0, n⟩).P 1)).size .mask = 0 := by
          show (if ((shapeAt (viaOmega ⟨Q, 0, n⟩).P 1).maskRows != 0) = true then _ else 0) = 0
          rw [h0]
          rfl
        rw [hs] at hj
        exact Nat.not_lt_zero _ hj
      refine word_mask_same (viaOmega ⟨Q, 0, n⟩).P (viaOmega ⟨Q, 0, n⟩).ride _ own 1
        ((jobOmega ⟨Q, 0⟩).rows { input := a, heard := h ++ [x₀], own := () }
          (coinsE own).toArray) Q.S.omegaRowsHigh
        (Desc.K14.Honest.omegaAtE Q.S (elems (heardFrom
          ({ input := a, heard := h ++ [x₀], own := () } : State Ask Unit) 0 1)) a.rows)
        (msgCoins (jobOmega ⟨Q, 0⟩) (coinsE own).toArray 1) rfl hm1 rfl
        (ProofFile.Honest.K1.two_logEll_mask _ _ (ProofFile.Honest.K1.fits_lengths _ _ hf)
          (ProofFile.Honest.K1.fits_maskCode _ _ 1 hf hk hz1)) (fun i => ?_) j hj
      rw [start_one (viaOmega ⟨Q, 0, n⟩).P (viaOmega ⟨Q, 0, n⟩).ride (jobOmega ⟨Q, 0⟩).sort
        Q.S.omegaRowsHigh (by omega) rfl rfl h30 hz0 ha0]
      exact val_coinsE own _

/-- The first half at the place pl among the halves O.hs (find? sees no later one) has one part, the
call's lifted part. The like of HalfIn (Honest/K14/SendingsShows.lean), but for the part. -/
def HalfVia (O : Others Bk W₀ Rc X₀ P₁ Wt) (pl : VerifiableInference.Desc.Place)
    (J : ProofFile.Honest.K1.SendJob Ask Unit) (wit : Common W₀ Rc TableKey → Ask) : Prop :=
  (O.hs.find? fun g => g.place == pl) = some { place := pl, parts := [liftSend wit (sendPart J)] }

/-- ViaDeclared reads the declared rounds and the stated oracle messages alone. -/
theorem viaDeclared_like {S S' Cl Cl' : Type} {b : VerifiableInference.Desc.Block S Cl}
    {c : VerifiableInference.Desc.Block S' Cl'} {J : ProofFile.Honest.K1.SendJob Ask Unit}
    (hr : b.rounds = c.rounds) (ho : b.oracles = c.oracles) (h : ViaDeclared c J) :
    ViaDeclared b J := by
  obtain ⟨d₀, d₁, os, r, o, rest⟩ := h.rounds
  exact ⟨d₀, d₁, os, hr.trans r, ho.trans o, rest⟩

/-- **ShowsU, where "send o_u" is a call of the shared part**: under Plan2, HalfVia at the sending's
place, sendFits at the call, O.holds = holds2 and SendShapes. n: the number that the call is told
for its first message; no premise on it. -/
theorem showsU_via (hQ : Plan2 Q sentU layO) (O : Others Bk W₀ Rc X₀ P₁ Wt) (Cl : Type)
    (weights : W₀ → Weights) (rand : Rc → TableRand) (n : Nat)
    (hh : HalfVia O (sendPlace 2) (viaU ⟨Q, 0, n⟩) (witOf Q weights rand))
    (hf : sendFits (viaU ⟨Q, 0, n⟩).P (viaU ⟨Q, 0, n⟩).ride = true)
    (hO : O.holds = holds2 Q weights rand) (hSh : SendShapes Q) : ShowsU Q sentU O Cl := by
  obtain ⟨B⟩ := hQ.eight
  intro blk k s m E ds y cols Ra Rb hblk hd hA hMv hrs
  have F := flatOf_carried (Cl := Cl) O.c Q B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 O.tests O.last
    B.made
  have L := F.at2 hblk
  obtain ⟨-, pU, -, pO⟩ := send_declares Q 0 B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 B.made
  obtain ⟨dU, -, dO, -⟩ := via_declares ⟨Q, 0, n⟩ B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 B.made
  have hpl : blk.place = sendPlace 2 := L.place.trans pU
  have hhalf : ((letters2 Q sentU O Cl).thread.hs.find? fun g => g.place == blk.place) =
      some { place := blk.place
             parts := [liftSend (witOf Q weights rand) (sendPart (viaU ⟨Q, 0, n⟩))] } := by
    rw [hpl]
    exact hh
  obtain ⟨-, -, -, -, hM, -, -⟩ := hA
  obtain ⟨hsm, -, -, -, s₀, c₀, hbeg, -, hfold⟩ := hM
  obtain rfl : s₀ = first Q.codes m.st.input.key := hbeg
  obtain ⟨⟨l, hl, hy⟩, -⟩ := hMv
  obtain ⟨x₀, x₁, c, -, hc, hp, -⟩ := via_moved (viaU ⟨Q, 0, n⟩) (witOf Q weights rand) hf blk
    (viaDeclared_like L.rounds L.oracles dU) hhalf hl m ds hd
  obtain rfl := Except.ok.inj (hy.symm.trans hp)
  obtain ⟨rfl, rfl⟩ : (⟨[], x₀⟩ : Fmt.RoundView) = Ra ∧
      (⟨viaShownAt (viaU ⟨Q, 0, n⟩) c.1.1 (witOf Q weights rand m.st.input) (m.st.heard ++ [x₀])
        (m.shown.plus [⟨[], x₀⟩]), x₁⟩ : Fmt.RoundView) = Rb := by
    simpa [roundsOf, playedBy] using hrs
  obtain ⟨W, D, hseen, -, hd1, u⟩ := FlatAt.stepTo1 (B := B) F hQ.facts.goes 0 _ s _ [] c₀ [] hfold
  have S := hQ.pub m.st.input.key
  have t := S.to1 u
  have hT : s.st.codes = Q.codes := by
    rw [← hd1]
    exact (S.at1 t).carried.codes
  have hseen' : m.seen = [W.R1] := hseen
  have hh' : m.st.heard = [W.R1].map (·.drawn) := by rw [← hsm, hseen']
  have hne : m.st.heard ≠ [] := by rw [hh']; exact List.cons_ne_nil _ _
  have e1 : firstRv m.st.heard = rvOf W.R1.drawn := by rw [hh']; rfl
  have eQ := jobU_par (Q := Q) hQ.facts.goes 0
  have eV : (viaU ⟨Q, 0, n⟩).P = parU Q sentU := eQ
  rw [hpl] at hc
  have hs0 : ((jobU ⟨Q, 0⟩).Q.sent.getD 0 default).shape = Q.par.S.fold.u := by
    rw [eQ]
    exact (shapeAt_of_get (parU Q sentU) 0 ⟨Q.par.S.fold.u, Q.par.S.fold.leafClass⟩
      (by rw [Desc.K14.Law.parK1_sent]; exact withU_zero hQ.facts.goes)).1
  have hsz : (jobU ⟨Q, 0⟩).Q.sent.size ≤ 2 := by
    rw [eQ, Desc.K14.Law.parK1_sent, hQ.facts.goesTwo]
  show viaShownAt (viaU ⟨Q, 0, n⟩) c.1.1 (witOf Q weights rand m.st.input) (m.st.heard ++ [x₀])
    (m.shown.plus [⟨[], x₀⟩]) = _
  rw [e1, hO, via_shown (viaU ⟨Q, 0, n⟩) c.1.1 (witOf Q weights rand m.st.input) m.st.heard x₀
    (m.shown.plus [⟨[], x₀⟩]) [] s.st (by rw [hT, eV]; rfl)
    (rowsU Q (first Q.codes m.st.input.key) (rvOf W.R1.drawn) (holds2 Q weights rand k m.st.input))
    (holds2 Q weights rand k m.st.input).w₀ fun kk hkk ha part j hj =>
      (viaU_same hQ hSh n hf c.1.1 (witOf Q weights rand m.st.input) m.st.heard x₀
        (m.shown.plus [⟨[], x₀⟩]) hne kk hkk ha part j hj).trans
      (rowsU_read Q (first Q.codes m.st.input.key) (rvOf W.R1.drawn)
        (holds2 Q weights rand k m.st.input) (witOf Q weights rand m.st.input)
        (m.st.heard ++ [x₀]) (coinsE c.1.1).toArray hsz hs0 hSh.u hSh.mask
        (by
          rw [← elems_one]
          show elems (((m.st.heard ++ [x₀]).drop 0).take 1) = _
          rw [hh']
          rfl)
        t.point (fun _ _ => rfl)
        (by
          show readCoins Q.codes ((jobU ⟨Q, 0⟩).Q.sent.getD 0 default).shape _ = _
          rw [hs0, coins_msg k (jobU ⟨Q, 0⟩) (sendPlace 2) hc 0])
        (by
          rw [← coins_msg k (jobU ⟨Q, 0⟩) (sendPlace 2) hc 1]
          show (holds2 Q weights rand k m.st.input).cMask = _
          unfold holds2
          cases Q.S.testU.head? <;> rfl)
        kk hkk part j), eV]

/-- **ShowsO, where "send o_omega" is a call of the shared part**: under Plan2, HalfVia at the
sending's place, sendFits at the call, O.holds = holds2 and SendShapes. n: the number that o_u gets;
the call is told, for its first message, n and the count of o_u's sending; no premise on n. -/
theorem showsO_via (hQ : Plan2 Q sentU layO) (O : Others Bk W₀ Rc X₀ P₁ Wt) (Cl : Type)
    (weights : W₀ → Weights) (rand : Rc → TableRand) (n : Nat)
    (hh : HalfVia O (sendPlace 5) (viaOmega ⟨Q, 0, n⟩) (witOf Q weights rand))
    (hf : sendFits (viaOmega ⟨Q, 0, n⟩).P (viaOmega ⟨Q, 0, n⟩).ride = true)
    (hO : O.holds = holds2 Q weights rand) (hSh : SendShapes Q) : ShowsO Q sentU O Cl := by
  obtain ⟨B⟩ := hQ.eight
  intro blk k s m E ds y cols Ra Rb hblk hd hA hMv hrs
  have F := flatOf_carried (Cl := Cl) O.c Q B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 O.tests O.last
    B.made
  have L := F.at5 hblk
  obtain ⟨-, pU, -, pO⟩ := send_declares Q 0 B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 B.made
  obtain ⟨dU, -, dO, -⟩ := via_declares ⟨Q, 0, n⟩ B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 B.made
  have hpl : blk.place = sendPlace 5 := L.place.trans pO
  have hhalf : ((letters2 Q sentU O Cl).thread.hs.find? fun g => g.place == blk.place) =
      some { place := blk.place
             parts := [liftSend (witOf Q weights rand) (sendPart (viaOmega ⟨Q, 0, n⟩))] } := by
    rw [hpl]
    exact hh
  obtain ⟨-, -, -, -, hM, -, -⟩ := hA
  obtain ⟨hsm, -, -, -, s₀, c₀, hbeg, -, hfold⟩ := hM
  obtain rfl : s₀ = first Q.codes m.st.input.key := hbeg
  obtain ⟨⟨l, hl, hy⟩, -⟩ := hMv
  obtain ⟨x₀, x₁, c, -, hc, hp, -⟩ := via_moved (viaOmega ⟨Q, 0, n⟩) (witOf Q weights rand) hf blk
    (viaDeclared_like L.rounds L.oracles dO) hhalf hl m ds hd
  obtain rfl := Except.ok.inj (hy.symm.trans hp)
  obtain ⟨rfl, rfl⟩ : (⟨[], x₀⟩ : Fmt.RoundView) = Ra ∧
      (⟨viaShownAt (viaOmega ⟨Q, 0, n⟩) c.1.1 (witOf Q weights rand m.st.input) (m.st.heard ++ [x₀])
        (m.shown.plus [⟨[], x₀⟩]), x₁⟩ : Fmt.RoundView) = Rb := by
    simpa [roundsOf, playedBy] using hrs
  obtain ⟨W, D, hseen, -, hd4, u⟩ := FlatAt.stepTo4 (B := B) F hQ.facts.goes 0 _ s _ [] c₀ [] hfold
  have S := hQ.pub m.st.input.key
  obtain ⟨x2, ids2, t⟩ := S.to4 u
  have hT : s.st.codes = Q.codes := by
    rw [← hd4]
    exact (S.at4 t).carried.codes
  have hseen' : m.seen = [W.R1, W.R2a, W.R2b, W.R4] := hseen
  have hh' : m.st.heard = [W.R1, W.R2a, W.R2b, W.R4].map (·.drawn) := by rw [← hsm, hseen']
  have hne : m.st.heard ≠ [] := by rw [hh']; exact List.cons_ne_nil _ _
  have e1 : firstRv m.st.heard = rvOf W.R1.drawn := by rw [hh']; rfl
  rw [hpl] at hc
  obtain ⟨w2, w0, w1⟩ := withOmega_two hQ.facts.two
  have sO : (jobOmega ⟨Q, 0⟩).Q.sent = Desc.K14.withOmega Q.S := Desc.K14.Law.parK1_sent Q 5 _ _
  have hs0 : ((jobOmega ⟨Q, 0⟩).Q.sent.getD 0 default).shape = Q.par.S.omega :=
    (shapeAt_of_get (jobOmega ⟨Q, 0⟩).Q 0 ⟨Q.par.S.omega, Q.par.S.omegaLeafClass⟩
      (by rw [sO]; exact w0)).1
  have hs1 : ((jobOmega ⟨Q, 0⟩).Q.sent.getD 1 default).shape = Q.par.S.sharedSplit :=
    (shapeAt_of_get (jobOmega ⟨Q, 0⟩).Q 1 ⟨Q.par.S.sharedSplit, Q.par.S.sharedSplitLeafClass⟩
      (by rw [sO]; exact w1)).1
  have hsz : (jobOmega ⟨Q, 0⟩).Q.sent.size ≤ 2 := by
    rw [sO]
    exact Nat.le_of_eq w2
  show viaShownAt (viaOmega ⟨Q, 0, n⟩) c.1.1 (witOf Q weights rand m.st.input)
    (m.st.heard ++ [x₀]) (m.shown.plus [⟨[], x₀⟩]) = _
  rw [e1, hO, via_shown (viaOmega ⟨Q, 0, n⟩) c.1.1 (witOf Q weights rand m.st.input) m.st.heard x₀
    (m.shown.plus [⟨[], x₀⟩]) [] s.st hT
    (rowsO Q (first Q.codes m.st.input.key) (rvOf W.R1.drawn) (holds2 Q weights rand k m.st.input))
    (words1 Q sentU (first Q.codes m.st.input.key) (rvOf W.R1.drawn)
      (holds2 Q weights rand k m.st.input)) fun kk hkk _ part j hj =>
      (viaOmega_same hQ hSh n hf c.1.1 (witOf Q weights rand m.st.input) m.st.heard x₀
        (m.shown.plus [⟨[], x₀⟩]) hne kk hkk part j hj).trans
      (rowsO_read Q (first Q.codes m.st.input.key) (rvOf W.R1.drawn)
        (holds2 Q weights rand k m.st.input) (witOf Q weights rand m.st.input)
        (m.st.heard ++ [x₀]) (coinsE c.1.1).toArray hsz hs0 hs1 hSh.omega (sp_noMain hQ)
        (by
          rw [← elems_one]
          show elems (((m.st.heard ++ [x₀]).drop 0).take 1) = _
          rw [hh']
          rfl)
        t.front.front.front.point (fun _ _ => rfl)
        (by
          show readCoins Q.codes Q.S.omega _ = _
          rw [coins_msg k (jobOmega ⟨Q, 0⟩) (sendPlace 5) hc 0]
          rfl)
        (by
          show readCoins Q.codes Q.S.sharedSplit _ = _
          rw [coins_msg k (jobOmega ⟨Q, 0⟩) (sendPlace 5) hc 1]
          rfl)
        kk hkk part j)]
  rfl

/-- **«Exchange» at both sendings, where they are calls of the shared part**, under eight premises:
Plan2 · no two messages have one tenant (hN) · HalfVia at both places · sendFits at both calls ·
O.holds = holds2 · SendShapes. The thread's sentence Thr is no premise of this statement: it is a
premise inside Exchange. -/
theorem exchange_via (hQ : Plan2 Q sentU layO) (O : Others Bk W₀ Rc X₀ P₁ Wt) (Cl : Type)
    (hN : Function.Injective O.N.tenant) (weights : W₀ → Weights) (rand : Rc → TableRand)
    (n n' : Nat) (hU : HalfVia O (sendPlace 2) (viaU ⟨Q, 0, n⟩) (witOf Q weights rand))
    (hOm : HalfVia O (sendPlace 5) (viaOmega ⟨Q, 0, n'⟩) (witOf Q weights rand))
    (hfU : sendFits (viaU ⟨Q, 0, n⟩).P (viaU ⟨Q, 0, n⟩).ride = true)
    (hfO : sendFits (viaOmega ⟨Q, 0, n'⟩).P (viaOmega ⟨Q, 0, n'⟩).ride = true)
    (hO : O.holds = holds2 Q weights rand) (hSh : SendShapes Q) :
    Exchange (letters2 Q sentU O Cl).thread 2 ∧ Exchange (letters2 Q sentU O Cl).thread 5 :=
  ⟨exchange2 hQ O Cl hN (showsU_via hQ O Cl weights rand n hU hfU hO hSh),
    exchange5 hQ O Cl hN (showsO_via hQ O Cl weights rand n' hOm hfO hO hSh)⟩

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.firstMask_noAnswer
#print axioms ProofFile.Honest.K14.point_front
#print axioms ProofFile.Honest.K14.viaU_same
#print axioms ProofFile.Honest.K14.viaOmega_same
#print axioms ProofFile.Honest.K14.viaDeclared_like
#print axioms ProofFile.Honest.K14.showsU_via
#print axioms ProofFile.Honest.K14.showsO_via
#print axioms ProofFile.Honest.K14.exchange_via
#print axioms ProofFile.Honest.K14.HalfVia
