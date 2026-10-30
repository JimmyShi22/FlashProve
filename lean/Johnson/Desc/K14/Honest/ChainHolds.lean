--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Honest/ChainHolds.lean: the eight sub-protocols of the linear claim's shared
rounds: where their functions have returned one behind the other, and under the premises hRec and
hCol on the committed table (no committer is in Lean), the statement behind the eighth is in order,
and every open row and every sample row in it holds of an honest prover's tables, if the values
shown are the honest ones.

Two lines of files meet here. That the eight return: Johnson/Desc/K14/Honest/YesChain.lean
(Returned, eight_return): THAT HALF IS TRUE OF EVERY PROVER, whatever values of the right form are
sent, since the eight test no equation. So for these eight the weight of "an honest prover is
accepted" lies in the second half: what the statement claims is kept from place to place:
Johnson/Desc/K14/Honest/PlacesHold.lean (the kind's six places) and SendKept.lean, SendPaid.lean
(the two sendings).

The proposition that is kept is AllMet (Johnson/Desc/Means/Forth/AllMet.lean): the statement is in
order (InOrder), and every open row of every group and every sample row of every oracle message
holds of the words (Holds). The proximity tests behind the eight take these rows in.

What of AllMet behind the eighth rests on what, family by family:
  the sample rows of o_u, o_omega, o_sp: on the law of the shared sending (sendSays), at answers
      that are by their making the sample rows' left sides at the held words
  (rec_gamma)'s rows: on hRec, multiplied by the weights and summed: hRec is these rows' claim, row
      by row of the committed table
  (loc_x)'s rows: on hCol, likewise
  the two rows of "SPLIT": proved from the definitions of the honest values
  InOrder: proved

Main names:
  Inputs              what an honest prover holds: the words in front of the eight; the committed
                      table's rows before encoding; the random values of the four messages
  wRun, psiLoRun, rowsU, rowsO, words1, words2, muRun   what it lays and sends, off Inputs and the
                      challenges heard: the rows' weights; the low part of the shared point; the
                      rows of the two sendings' messages; the words behind each sending; the scalar
  returned_holds      **under hRec and hCol: where the eight have returned and the values shown are
                      the honest ones, AllMet holds behind the eighth at the honest words**
  eight_hold          **the eight return; and there returned_holds applies**: in terms of the
                      functions. In terms of the format's own step, which is the form to be cited:
                      eight_steps_hold (Johnson/Desc/K14/Honest/ChainSteps.lean)

What is assumed, as premises (eight_hold).
  Public: PlanFacts (met at the two typed shapes: Johnson/Desc/K14/Honest/YesAt.lean); the two
      sendings pass their kind's test on the plan (hBU, hBO).
  On the first state: its codes are the plan's (hc); statement and book are in step (hstep); AllMet
      holds there at the words in front (hK0). All three are met at the chain's own first state
      (first_kept: PlacesHold.lean).
  On the instance's key: its sizes fit (hkey); no seed has the factor 0 (hbeta): no choice of an
      honest committer's, since a key's seeds follow from the table's name by the hash; EACH ANSWER
      OF THE KEY IS ITS ROW's OWN (hRec).
  On the view: the two sendings' rounds have the stated form (hfU, hfO); the two points have the
      planned numbers of coordinates; each sampled location has its column; "SPLIT"'s round holds
      one scalar; EACH OPENED COLUMN HOLDS THE ROWS' OWN SYMBOLS (hCol).
  On what is shown, inside the conclusion: the OOD answers are the sample rows' left sides at the
      held words, at the states that the run reaches; the scalar is muRun.

What is not claimed. That a decision accepts. That a committer's key and columns meet hRec and hCol.
That any program writes these values. That the honest tables are what lies beneath the roots that
the verifier is sent. Nothing on the two proximity tests. Nothing on how the random values are
distributed, on soundness or on hiding. This is not completeness of the protocol or of a program.

-/
import Johnson.Desc.K14.Honest.YesRounds
import Johnson.Desc.K14.Honest.PlacesHold
import Johnson.Desc.K14.Honest.SplitValue
import Johnson.Desc.K14.Honest.SendPaid
import Johnson.Desc.K14.Law.Shapes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Honest
open OnBytes OnBytes.Params Desc.Plain
open OnBytes.Means (Words)
open OnBytes.Slice (rdE)
open Johnson.Prover.Send (Rows held shapeAt)
open VerifiableInference.Desc (Grows roundsFit)
open VerifiableInference.Desc.Own (keyFits allZero)
open Desc.K14.Law (locations genK uOf Seated placed_of_seated seatedUB seatedUB_iff on4_of_seatedUB
  parK1_sent size_grows parU parO)

/-- What an honest prover holds in front of the eight. -/
structure Inputs where
  /-- the words in front -/
  w₀ : Words Cb.Gl.E
  /-- the committed table's rows before encoding: message, then tail, as a folded row lays them.
  Between a row's message and its tail a folded row has free entries: an honest prover's are 0
  there, so these tables are an honest prover's only for rows that are 0 there. No row of this kind
  reads these entries. The type is wider than a committer's rows, which are over the base field:
  hCol, which sets a column's word beside a row's code symbol, can hold only where that symbol lies
  in the base field -/
  Rw : ℕ → ℕ → Cb.Gl.E
  /-- the random values of o_u -/
  cU : MsgCoins
  /-- the entries of the first mask, which goes out with o_u. They are free here: what form an
  honest prover's first mask has is the proximity test's to say, not this file's -/
  cMask : MsgCoins
  /-- the random values of o_omega -/
  cOmega : MsgCoins
  /-- the random values of o_sp -/
  cSp : MsgCoins

/-- The rows' weights, off the shared point. -/
noncomputable def wRun (P : P14) (d0 : St) (r1 : Fmt.RoundView) : ℕ → Cb.Gl.E :=
  wOf rdE P.par.S (locU P.par P.codes d0.loc d0.st.groups.size d0.st.oracles.size r1)

/-- The low part of the shared point. -/
noncomputable def psiLoRun (P : P14) (r1 : Fmt.RoundView) : List Cb.Gl.E :=
  ((drawn r1).take P.par.S.kLo).map rdE.val

/-- The rows of the messages of o_u's sending. -/
noncomputable def rowsU (P : P14) (d0 : St) (r1 : Fmt.RoundView) (H : Inputs) : ℕ → Rows :=
  sendsU P.codes P.par.S (wRun P d0 r1) H.Rw H.cU H.cMask

/-- The rows of the messages of o_omega's sending. -/
noncomputable def rowsO (P : P14) (d0 : St) (r1 : Fmt.RoundView) (H : Inputs) : ℕ → Rows :=
  sendsOmega P.codes P.par.S (psiLoRun P r1) (uHon P.par.S.fold (wRun P d0 r1) H.Rw) H.cOmega H.cSp

/-- The words behind o_u's sending. -/
noncomputable def words1 (P : P14) (sentU : Array OracleNotice) (d0 : St) (r1 : Fmt.RoundView)
    (H : Inputs) : Words Cb.Gl.E :=
  held H.w₀ d0.st.oracles.size (parU P sentU) (rowsU P d0 r1 H)

/-- The words behind o_omega's sending. -/
noncomputable def words2 (P : P14) (sentU : Array OracleNotice) (d0 : St) (r1 : Fmt.RoundView)
    (H : Inputs) : Words Cb.Gl.E :=
  chainWords H.w₀ d0.st.oracles.size (d0.st.oracles.size + 2) (parU P sentU) (parO P)
    (rowsU P d0 r1 H) (rowsO P d0 r1 H)

/-- The scalar sent at "SPLIT". -/
noncomputable def muRun (P : P14) (d0 : St) (r1 r7 : Fmt.RoundView) (H : Inputs) : Cb.Gl.E :=
  muSent P.par.S (psiLoRun P r1) ((drawn r7).map rdE.val) (uHon P.par.S.fold (wRun P d0 r1) H.Rw)
    H.cSp 0

/-- **Under hRec and hCol (the committed table's two laws: premises): where the eight have returned
and the values shown are the honest ones, the statement behind the eighth is in order and all that
it claims holds of the honest words.** -/
theorem returned_holds (P : P14) (sentU : Array OracleNotice) (layO : TreeLay)
    (hP : PlanFacts P.par P.codes sentU layO) (d0 : St) (r1 r2a r2b r4 r5a r5b r7 r8 : Fmt.RoundView)
    (cols : List (Nat × List UInt64)) (rs3 rs6 : List Fmt.RoundView) (d1 d2 d3 d4 d5 d6 d7 d8 : St)
    (x2 x5 : DState (Array Nat)) (ids2 ids5 : Array Nat)
    (h : Returned P sentU d0 r1 r2a r2b r4 r5a r5b r7 r8 cols rs3 rs6 d1 d2 d3 d4 d5 d6 d7 d8 x2 x5
      ids2 ids5) (H : Inputs)
    (hBU : VerifiableInference.Desc.K1.planOkOwn (parU P sentU) = true)
    (hBO : VerifiableInference.Desc.K1.planOkOwn (parO P) = true)
    (hfU : roundsFit (VerifiableInference.Desc.K1.rounds (parU P sentU)) [r2a, r2b] = true)
    (hfO : roundsFit (VerifiableInference.Desc.K1.rounds (parO P)) [r5a, r5b] = true)
    (hK0 : Means.AllMet rdE d0.st H.w₀)
    (hRec : ∀ x ∈ d0.loc.key.seeds.zipIdx, ∀ r < P.par.S.fold.index.rows,
      RowAnswer P.par.S.fold.index (x.1.z.map rdE.val) (rdE.val x.1.beta)
        (fun t => rdE.val (thetaE t)) x.2 (H.Rw r)
        (rdE.val (d0.loc.key.record.getD (r * P.par.S.fold.index.answers + x.2) zeroE)))
    (hCol : ∀ x ∈ locations P.par r4, ∀ col, cols.lookup x = some col →
      ∀ q < P.par.S.fold.index.rows,
        rdE.val (ofF (col.toArray.getD q 0)) = genK rdE P.par.S.fold x (H.Rw q))
    (ha2 : r2b.vals = answersAt (parU P sentU) d1.st r2a H.w₀ (rowsU P d0 r1 H))
    (ha5 : r5b.vals = answersAt (parO P) d4.st r5a (words1 P sentU d0 r1 H) (rowsO P d0 r1 H))
    (hmu : r8.vals = [.e (Slice.ofE (muRun P d0 r1 r7 H))]) :
    Means.AllMet rdE d8.st (words2 P sentU d0 r1 H) := by
  have hlin := hP.lin
  have hok : linOk P.codes P.par.S = true :=
    (VerifiableInference.Desc.Own.linFits_eq _ _).symm.trans hlin
  obtain ⟨w2, w0, w1⟩ := withOmega_two hP.two
  have sU : (parU P sentU).sent = sentU := parK1_sent P 2 _ sentU
  have sO : (parO P).sent = withOmega P.par.S := parK1_sent P 5 _ _
  have hszU : 0 < (parU P sentU).sent.size := by rw [sU, hP.goesTwo]; omega
  have hshU : shapeAt (parU P sentU) 0 = P.par.S.fold.u :=
    (shapeAt_of_get (parU P sentU) 0 ⟨P.par.S.fold.u, P.par.S.fold.leafClass⟩
      (by rw [sU]; exact withU_zero hP.goes)).1
  have hszO : 1 < (parO P).sent.size := by rw [sO, w2]; omega
  have hshO0 : shapeAt (parO P) 0 = P.par.S.omega :=
    (shapeAt_of_get (parO P) 0 ⟨P.par.S.omega, P.par.S.omegaLeafClass⟩ (by rw [sO]; exact w0)).1
  have hshO1 : shapeAt (parO P) 1 = P.par.S.sharedSplit :=
    (shapeAt_of_get (parO P) 1 ⟨P.par.S.sharedSplit, P.par.S.sharedSplitLeafClass⟩
      (by rw [sO]; exact w1)).1
  -- "LIN point" and the sending of o_u
  have K1 := linPoint_kept rdE P.par d0 d1 [r1] H.w₀ h.k1 hK0
  have K2' := sendU_kept P "send o_u" (parU P sentU) none [] d1 d2 r2a r2b [] H.w₀ (rowsU P d0 r1 H)
    (sendSays _) hBU hfU (h.s2.decides P "send o_u" none [] []) ha2 K1.1 K1.2
  rw [h.n1] at K2'
  have K2 : Means.AllMet rdE d2.st (words1 P sentU d0 r1 H) := K2'
  -- "(rec_gamma)"
  have at2 : seatedUB P.par d2 = true := by
    obtain ⟨x, hx, hs, _⟩ := h.u2.u
    exact (seatedUB_iff P.par d2).2 ⟨⟨x, hx, hs⟩, h.u2.lay, by rw [h.c2]; exact hok⟩
  obtain ⟨hi, hP2⟩ := on4_of_seatedUB P.par d2 at2
  have fold2 : ∀ l : Lin,
      l = locU P.par P.codes d0.loc d0.st.groups.size d0.st.oracles.size r1 →
      IsFold P.par.S.fold (wOf rdE P.par.S l) H.Rw (uOf l (words1 P sentU d0 r1 H)) := by
    intro l hl
    subst hl
    exact isFold_held H.w₀ d0.st.oracles.size (parU P sentU) P.codes P.par.S (wRun P d0 r1) H.Rw
      H.cU H.cMask _ hlin hszU hshU rfl
  have key2 : d2.loc.key = d0.loc.key := by rw [h.l2]; rfl
  have K3 := laysRec_kept rdE P.par d2 d3 rs3 (words1 P sentU d0 r1 H) H.Rw h.k3 hi hP2
    (fold2 _ h.l2) (by rw [key2]; exact hRec) K2
  -- "LOC"
  have at3 : seatedUB P.par d3 = true := by
    obtain ⟨x, hx, hs, _⟩ := h.u3.u
    exact (seatedUB_iff P.par d3).2 ⟨⟨x, hx, hs⟩, h.u3.lay, by rw [h.c3]; exact hok⟩
  have K4 := loc_kept rdE P.par d3 d4 r4 cols (words1 P sentU d0 r1 H) H.Rw h.k4 hi
    (on4_of_seatedUB P.par d3 at3).2 (fold2 _ h.l3) (weights_size P.par d3 h.f3.psi) hCol K3
  -- the sending of o_omega and o_sp
  have K5' := sendOmega_kept P "send o_omega" (parO P) none [] d4 d5 r5a r5b []
    (words1 P sentU d0 r1 H) (rowsO P d0 r1 H) (sendSays _) hBO hfO
    (h.s5.decides P "send o_omega" none [] []) ha5 K4.1 K4.2
  rw [h.n4] at K5'
  have K5 : Means.AllMet rdE d5.st (words2 P sentU d0 r1 H) := K5'
  -- the joinings and "LIN zeta"
  have K6 := joins_kept rdE P.par d5 d6 rs6 _ h.k6 K5
  have K7 := linZeta_kept rdE d6 d7 r7 _ h.k7 K6
  -- "SPLIT"
  have at7 : Seated d7.st P.codes P.par.S d7.loc := by
    obtain ⟨x, hx, hs, _⟩ := h.o7.omega
    obtain ⟨y, hy, hs', _⟩ := h.u7.u
    exact ⟨h.c7, h.o7.apartOU, ⟨x, hx, hs⟩, ⟨y, hy, hs'⟩, by rw [← h.c7]; exact h.u7.lay⟩
  have hP7 : ∀ T, Grows d7.st T →
      Law.Placed T P.par.S d7.loc (linLayOmega d7.st.codes P.par.S) := fun T g => by
    rw [h.c7]
    exact placed_of_seated (at7.grows g) hok
  have lU7 : d7.loc.oU = ⟨d0.st.oracles.size,
      vectorLay P.codes P.par.S.fold.u P.par.S.fold.rowsHigh⟩ := by rw [h.l7]; rfl
  have lO7 : d7.loc.oOmega = d0.st.oracles.size + 2 := by rw [h.l7]; rfl
  have lS7 : d7.loc.oSp = d0.st.oracles.size + 2 + 1 := by rw [h.l7]; rfl
  have lP7 : d7.loc.psiSh = drawn r1 := by rw [h.l7]; rfl
  have lZ7 : d7.loc.zFd = drawn r7 := by rw [h.l7]; rfl
  have hle : d0.st.oracles.size + (parU P sentU).sent.size ≤ d0.st.oracles.size + 2 := by
    rw [sU, hP.goesTwo]
  refine split_kept rdE P.par d7 d8 r8 _ hP.two h.k8 hP7 ?_ ?_ K7
  · intro j hj
    rw [h.c7, lP7]
    exact col_chain H.w₀ d0.st.oracles.size (d0.st.oracles.size + 2) (parU P sentU) (parO P) P.codes
      P.par.S (psiLoRun P r1) (wRun P d0 r1) H.Rw H.cU H.cMask H.cOmega H.cSp d7.loc hlin hle hszU
      hshU lU7 (Nat.lt_trans Nat.zero_lt_one hszO) hshO0 lO7 j hj
  · intro row x G kappa d₁ hf hx hG hk
    obtain ⟨d₁', hk', hA, _⟩ := take_first P.par d7 hP.two h.f8
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hk.symm.trans hk'))
    obtain ⟨GO, hGO, _, _, _, hmem⟩ := h.f8.gO
    obtain rfl : G = GO := Option.some.inj (hG.symm.trans hGO)
    obtain ⟨xS, hxS, hsS, _, hpS⟩ := h.f8.sp
    obtain ⟨ms1, _⟩ := mask_first d7.st d7.loc.oSp xS P.par.S.sharedSplit hxS hsS hpS h.f8.free
    have g1 := VerifiableInference.Desc.Ground.takeMaskP_grows d7 d₁ _ _ hk
    have hx' : x = Slice.ofE (muRun P d0 r1 r7 H) := by
      have e := hx.symm.trans hmu
      simpa using e
    have hsh := (VerifiableInference.Desc.Own.linFits_iff P.codes P.par.S).1 hlin
    have hSp : VerifiableInference.Desc.Own.SplitMessageFits P.par.S.sharedSplit
        P.par.S.sharedMaskCode := by
      rcases hsh.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with e | e
      · rw [hP.two] at e
        cases e
      · exact e
    rw [muVal_formula rdE d₁.st P.par.S d7.loc _ row G.members 0 _ hf (hP7 _ g1)
      (contains_of hmem _ (by simp))
      (not_contains_of hmem _ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨Ne.symm h.f8.apartOU, Ne.symm h.f8.apartU⟩))
      (Nat.lt_of_lt_of_le h.f8.sp.lt (size_grows _ _ g1))
      (by
        unfold Means.tableSize
        rw [hA.has_eq, ms1, if_pos rfl]
        exact Nat.two_pow_pos _)]
    rw [h.c7, lZ7, hx']
    have e := mu_chain H.w₀ d0.st.oracles.size (d0.st.oracles.size + 2) (parU P sentU) (parO P)
      (rowsU P d0 r1 H) P.codes P.par.S (psiLoRun P r1) ((drawn r7).map rdE.val)
      (uHon P.par.S.fold (wRun P d0 r1) H.Rw) H.cOmega H.cSp d7.loc hlin hszO hshO0 hshO1 lO7 lS7 0
      (by rw [Nat.zero_mod]; exact Nat.pos_of_ne_zero hSp.2.1)
    refine Eq.trans ?_ e.symm
    show Slice.readE (E.ofTriple (Slice.ofE (muRun P d0 r1 r7 H))) = _
    rw [Slice.readE_ofTriple, Slice.toE_ofE]
    rfl

/-- **The eight return, whatever values of the right form are sent; and, under hRec and hCol, if the
values shown are the honest ones at the states that the run reaches, the statement behind the eighth
is in order and all that it claims holds of the honest words.** -/
theorem eight_hold (P : P14) (sentU : Array OracleNotice) (layO : TreeLay)
    (hP : PlanFacts P.par P.codes sentU layO) (d0 : St) (hc : d0.st.codes = P.codes)
    (hstep : d0.st.oracles.size = d0.book.place.size)
    (hkey : keyFits d0.loc.key P.par.S.fold.index = true)
    (hbeta : (d0.loc.key.seeds.all (!allZero ·.beta)) = true)
    (r1 r2a r2b r4 r5a r5b r7 r8 : Fmt.RoundView) (cols : List (Nat × List UInt64))
    (hBU : VerifiableInference.Desc.K1.planOkOwn (parU P sentU) = true)
    (hBO : VerifiableInference.Desc.K1.planOkOwn (parO P) = true)
    (hfU : roundsFit (VerifiableInference.Desc.K1.rounds (parU P sentU)) [r2a, r2b] = true)
    (hfO : roundsFit (VerifiableInference.Desc.K1.rounds (parO P)) [r5a, r5b] = true)
    (hpt : (drawn r1).length = P.par.S.kCol) (hz : (drawn r7).length = P.par.S.kRow)
    (hcols : ∀ x ∈ r4.drawn.poss, ∃ col,
      cols.lookup (x % 2 ^ P.par.S.fold.index.code.logN) = some col ∧
        col.length = P.par.S.fold.index.rows)
    (hx : ∃ x, r8.vals = [.e x]) (rs3 rs6 : List Fmt.RoundView) (H : Inputs)
    (hK0 : Means.AllMet rdE d0.st H.w₀)
    (hRec : ∀ x ∈ d0.loc.key.seeds.zipIdx, ∀ r < P.par.S.fold.index.rows,
      RowAnswer P.par.S.fold.index (x.1.z.map rdE.val) (rdE.val x.1.beta)
        (fun t => rdE.val (thetaE t)) x.2 (H.Rw r)
        (rdE.val (d0.loc.key.record.getD (r * P.par.S.fold.index.answers + x.2) zeroE)))
    (hCol : ∀ x ∈ locations P.par r4, ∀ col, cols.lookup x = some col →
      ∀ q < P.par.S.fold.index.rows,
        rdE.val (ofF (col.toArray.getD q 0)) = genK rdE P.par.S.fold x (H.Rw q)) :
    ∃ d1 d2 d3 d4 d5 d6 d7 d8 x2 x5 ids2 ids5,
      Returned P sentU d0 r1 r2a r2b r4 r5a r5b r7 r8 cols rs3 rs6 d1 d2 d3 d4 d5 d6 d7 d8 x2 x5
        ids2 ids5 ∧
      (r2b.vals = answersAt (parU P sentU) d1.st r2a H.w₀ (rowsU P d0 r1 H) →
        r5b.vals = answersAt (parO P) d4.st r5a (words1 P sentU d0 r1 H) (rowsO P d0 r1 H) →
        r8.vals = [.e (Slice.ofE (muRun P d0 r1 r7 H))] →
        Means.AllMet rdE d8.st (words2 P sentU d0 r1 H)) := by
  have hlen : P.codes.lengthsOk = true := hP.lengths
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, x2, x5, ids2, ids5, h⟩ := eight_return P sentU layO hP d0
    hc hstep hkey hbeta r1 r2a r2b r4 r5a r5b r7 r8 cols
    ⟨hpt, seeds_nz _ _ _ hfU, fitB_of_rounds _ _ _ hBU hlen hfU, hcols, seeds_nz _ _ _ hfO,
      fitB_of_rounds _ _ _ hBO hlen hfO, hz, hx⟩ rs3 rs6
  exact ⟨d1, d2, d3, d4, d5, d6, d7, d8, x2, x5, ids2, ids5, h, fun ha2 ha5 hmu =>
    returned_holds P sentU layO hP d0 r1 r2a r2b r4 r5a r5b r7 r8 cols rs3 rs6 d1 d2 d3 d4 d5 d6 d7
      d8 x2 x5 ids2 ids5 h H hBU hBO hfU hfO hK0 hRec hCol ha2 ha5 hmu⟩

end Desc.K14.Honest

#print axioms Desc.K14.Honest.returned_holds
#print axioms Desc.K14.Honest.eight_hold
