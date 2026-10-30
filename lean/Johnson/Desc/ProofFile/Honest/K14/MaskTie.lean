-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/MaskTie.lean: kind K14: THE TIE AT TWO DATA, AND WHAT THE SECOND
ROUND OF "send o_u" HANGS ON: under the test on the shapes; with no premise on what was heard.
Statements with their proofs. Equations at each value of the coins: no distribution occurs; no
property is claimed.

Why. The tie (shows_tie, Honest/K14/TieShown.lean) stands where the job's vectors are the same in
both of the part's rounds (SameData). The owner's sentence (the field fresh of Good) has no sentence
at entry: it is asked at every stand, also where the two rounds read two vectors.

  answers_tie_behind   the second round's items are the shared text's answers at the rows laid at
                  the stand BEHIND the part's first challenge: no premise on what was heard
  shows_tie_two   **the tie at two data**: the first round as the shared sending's first move,
                  written out (shownR's first half), has it at the data in front of the part; the
                  second as its second move, written out, has it at the data behind the part's first
                  challenge; at the same coins, number by number. Called by
                  Honest/K14/FreshAtPure.lean, for "some …" at all coins; the proof of the owner's
                  sentence goes by shows_first
  shows_first     the same with the second round left in this kind's own text: THE FORM THAT THE
                  PROOF OF THE OWNER's SENTENCE CALLS (Honest/K14/MaskOfRows.lean)
  u_sent, u_two, u_shape0, u_sort0, u_sort1   "send o_u" where masks are sent ahead and the test on
                  G_u has a first stage: two messages: o_u, laid plainly; a fold's fresh table
  cut_coins       two values of the coins with the same cut of the first n coins have the same first
                  n coins as the program's elements
  cutAll_single   the runs that one entry cuts off
  u_noMask, maskFirst_at   o_u has no mask row; the first mask's first coin is the number of o_u's
                  coins
  u_answers_below **at "send o_u" the second round hangs on o_u's own coins alone**: two values of
                  the coins with the same cut below the first mask's first coin show the same items

What is assumed. sendShapeFits (in the general statements), sendingsFit with "masks are sent ahead"
and "the test has a first stage" (at "send o_u"); SendDeclared where the frame's play is named.
Limits. THE RIGHT SIDES ARE TEXTS: shownR is the shared part's two moves WRITTEN OUT; that that
part, played, shows it: play_send (Johnson/SendSim/At/Shows.lean), where its test accepts (fits_tie,
Honest/K14/TieCounts.lean) and the first challenge holds just the seeds; at another challenge that
part stops, and this kind's does not. Nothing on a distribution or a book of coins. Nothing on any
property.
-/
import Johnson.Desc.ProofFile.Honest.K14.TieShown
import Johnson.Desc.ProofFile.Honest.K14.ExactOfRows
import Johnson.Desc.ProofFile.Honest.K14.MaskOwner
import Johnson.Desc.K14.Law.PlanShapes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes (E zeroE OracleNotice linWithU linMaskNotice)
open OnBytes.Slice (GE GF rdE ofE toE)
open Johnson.Prover.Send (shapeAt answers)
open ProofFile.Honest.K1 (rowsR stAt seedsAt ce)
open OnBytes.SendSim.At (shownR asked)

variable {S Cl X Pb W : Type}

/-- **The second round's items, with no premise on what was heard**: the shared text's answers at
the rows laid at the stand behind the part's first challenge. -/
theorem answers_tie_behind (J : SendJob) (hfit : sendShapeFits J = true)
    (c : Cs (sendingPart J).takes) (a : Ask) (h : List Fmt.Drawn) (x₀ x₁ : Fmt.Drawn) :
    sendShownAt J c a (h ++ [x₀]) =
      (answers J.Q (stAt J.Q 0) 0
        (Johnson.Prover.Send.held (fun _ _ _ => 0) 0 J.Q (rowsR J.Q (rideBySort J)
          (vecData J { input := a, heard := h ++ [x₀], own := () }) (recount (due_tie J hfit) c)))
        (seedsAt J.Q [x₀, x₁])).map fun y => (Said.answer (toE y)).got := by
  obtain ⟨hlen, hsh⟩ := shapes_of_fit J hfit
  obtain ⟨e1, e2⟩ := stAt_front J.Q 0
  rw [shown_read J c a h x₀ [] (stFront J.Q 0) rfl
    (rowsR J.Q (rideBySort J) (vecData J { input := a, heard := h ++ [x₀], own := () })
      (recount (due_tie J hfit) c)) (fun _ _ _ => 0)
    (fun k hk part j hj => words_tie J.Q _ _ (rows_tie J hfit c _) hlen hsh k hk part j hj)]
  unfold Desc.K14.Honest.answersAt
  rw [e2, ← e1]
  show (answers J.Q (stAt J.Q 0) 0 _ (seedsAt J.Q [x₀, x₁])).map Fmt.ItemValue.answer = _
  rw [← answers_round J.Q (stAt J.Q 0), List.map_map, List.map_map]
  refine List.map_congr_left fun y _ => ?_
  show Fmt.ItemValue.answer (ofE (toE y)) = Fmt.ItemValue.answer (ofE (toE (ofE (toE y))))
  rw [OnBytes.Slice.toE_ofE]

/-- The first round as the shared sending's first move shows it at the data in front of the part;
the second round in this kind's own text. -/
theorem shows_first (J : SendJob) (hfit : sendShapeFits J = true) (wit : W → Ask)
    (φ : Face Empty W Pb) (σ : Side S Cl Empty W X Pb) (sim : Sim Pb)
    (hd : SendDeclared σ.block J) (m : Mid W X) (x₀ x₁ : Fmt.Drawn)
    (asks : List (List (List Nat))) (c : Cs (sendingPart J).takes) :
    σ.shows φ (sendingMember σ J wit sim) (c, (), ()) m [x₀, x₁] asks =
      some ((shownR J.Q 0 (rideBySort J)
          (vecData J { input := wit m.st.input, heard := m.st.heard, own := () }) [x₀, x₁] asks
          (recount (due_tie J hfit) c)).take 1 ++
        [{ vals := sendShownAt J c (wit m.st.input) (m.st.heard ++ [x₀]), cols := [] }]) := by
  have h := shows_send J wit σ sim hd φ (c, (), ()) m x₀ x₁ asks
  refine h.trans (congrArg some ?_)
  unfold shownR sendTablesAt
  rw [sentTables_tie J.Q _ _ (rows_tie J hfit c
    { input := wit m.st.input, heard := m.st.heard, own := () })]
  simp only [List.zipIdx_map, List.map_map, asked, Function.comp_def]
  rfl

/-- **THE TIE AT TWO DATA.** With no premise on what was heard: the first round shows the columns
that the shared sending's first move, written out, has at the data made of the job's vectors IN
FRONT of the part; the second round shows the answers that its second move, written out, has at the
data made of the vectors BEHIND the part's first challenge: at the same coins, number by number.
That the shared part, played, shows these: play_send, only where the first challenge holds just the
seeds. -/
theorem shows_tie_two (J : SendJob) (hfit : sendShapeFits J = true) (wit : W → Ask)
    (φ : Face Empty W Pb) (σ : Side S Cl Empty W X Pb) (sim : Sim Pb)
    (hd : SendDeclared σ.block J) (m : Mid W X) (x₀ x₁ : Fmt.Drawn)
    (asks : List (List (List Nat))) (c : Cs (sendingPart J).takes) :
    σ.shows φ (sendingMember σ J wit sim) (c, (), ()) m [x₀, x₁] asks =
      some ((shownR J.Q 0 (rideBySort J)
          (vecData J { input := wit m.st.input, heard := m.st.heard, own := () }) [x₀, x₁] asks
          (recount (due_tie J hfit) c)).take 1 ++
        (shownR J.Q 0 (rideBySort J)
          (vecData J { input := wit m.st.input, heard := m.st.heard ++ [x₀], own := () })
          [x₀, x₁] asks (recount (due_tie J hfit) c)).drop 1) := by
  rw [shows_first J hfit wit φ σ sim hd m x₀ x₁ asks c,
    answers_tie_behind J hfit c (wit m.st.input) m.st.heard x₀ x₁]
  rfl

/-! ## "send o_u" -/

/-- Where masks are sent ahead, "send o_u" has two messages, the first o_u. -/
theorem u_sent (A : SendPub) (hfit : sendingsFit A.P = true) (hm : A.P.S.masksAhead = true) :
    ∃ n : OracleNotice,
      (jobU A).Q.sent = #[(⟨A.P.S.fold.u, A.P.S.fold.leafClass⟩ : OracleNotice)] ++ #[n] := by
  unfold sendingsFit at hfit
  simp only [Bool.and_eq_true] at hfit
  obtain ⟨sentU, hU⟩ := Option.isSome_iff_exists.1 hfit.1.1.1.1
  obtain ⟨rest, hr, rfl⟩ := Desc.K14.Law.withU_cut hU
  unfold linWithU at hr
  rw [if_pos hm] at hr
  have e : (jobU A).Q.sent =
      #[(⟨A.P.S.fold.u, A.P.S.fold.leafClass⟩ : OracleNotice)] ++ rest := by
    show (Desc.K14.parK1 A.P 2 "o_u and the first mask"
      ((Desc.K14.withU A.P.S).getD #[])).sent = _
    rw [Desc.K14.Law.parK1_sent, hU]
    rfl
  cases hn : linMaskNotice A.P.S.testU A.P.S.fold.leafClass with
  | none =>
    rw [hn] at hr
    cases hr
  | some n =>
    rw [hn] at hr
    obtain rfl : #[n] = rest := Option.some.inj hr
    exact ⟨n, e⟩

/-- It has two messages. -/
theorem u_two (A : SendPub) (hfit : sendingsFit A.P = true) (hm : A.P.S.masksAhead = true) :
    (jobU A).Q.sent.size = 2 := by
  obtain ⟨n, e⟩ := u_sent A hfit hm
  rw [e]
  rfl

/-- Its first message's shape is o_u's. -/
theorem u_shape0 (A : SendPub) (hfit : sendingsFit A.P = true) (hm : A.P.S.masksAhead = true) :
    shapeAt (jobU A).Q 0 = A.P.S.fold.u := by
  obtain ⟨n, e⟩ := u_sent A hfit hm
  show ((jobU A).Q.sent.getD 0 default).shape = _
  rw [e]
  rfl

/-- o_u is laid plainly. -/
theorem u_sort0 (A : SendPub) : (jobU A).sort 0 = .plain A.P.S.fold.rowsHigh := rfl

/-- Every message behind o_u is laid as the fresh table of the test's first stage. -/
theorem u_sort1 (A : SendPub) (s : OnBytes.Params.IoppStage) (hs : A.P.S.testU.head? = some s)
    (k : Nat) : (jobU A).sort (k + 1) = .fresh s.k s.h := by
  show (if (k + 1 == 0) = true then MsgSort.plain A.P.S.fold.rowsHigh else
    match A.P.S.testU.head? with
    | some s => MsgSort.fresh s.k s.h
    | none => MsgSort.plain false) = _
  rw [hs]
  rfl

/-- **Two values of the coins with the same cut of the first n coins have the same first n
coins.** -/
theorem cut_coins {d : Due} (n : Nat) (hn : n ≤ d.e) (c c' : Cs d)
    (h : c.cut ⟨0, 0⟩ ⟨0, n⟩ = c'.cut ⟨0, 0⟩ ⟨0, n⟩) (i : Nat) (hi : i < n) :
    (coinsE c).toArray.getD i zeroE = (coinsE c').toArray.getD i zeroE := by
  have hc : (⟨0, 0⟩ : Due).f + (⟨0, n⟩ : Due).f ≤ d.f ∧
      (⟨0, 0⟩ : Due).e + (⟨0, n⟩ : Due).e ≤ d.e :=
    ⟨Nat.zero_le _, by show 0 + n ≤ d.e; omega⟩
  unfold Cs.cut at h
  rw [dif_pos hc, dif_pos hc] at h
  have h1 := congrFun (congrArg Cs.e (Option.some.inj h)) ⟨i, hi⟩
  have e1 : ∀ hlt : 0 + i < d.e, (⟨0 + i, hlt⟩ : Fin d.e) = ⟨i, by omega⟩ :=
    fun _ => Fin.ext (Nat.zero_add _)
  have h2 : c.e ⟨0 + i, by omega⟩ = c'.e ⟨0 + i, by omega⟩ := h1
  rw [e1] at h2
  rw [coded_coin c i (by omega), coded_coin c' i (by omega),
    ProofFile.Honest.K1.ce_eq d c i (by omega), ProofFile.Honest.K1.ce_eq d c' i (by omega), h2]

/-- The runs that one entry cuts off. -/
theorem cutAll_single {d : Due} (c : Cs d) (e : Ahead) :
    cutAll c [e] = (c.cut e.start e.count).map fun x => (x, ()) := by
  show ((c.cut e.start e.count).bind fun x => (cutAll c []).map fun y => (x, y)) = _
  cases c.cut e.start e.count <;> rfl

/-- o_u has no mask row. -/
theorem u_noMask (A : SendPub) (hfit : sendingsFit A.P = true) (hm : A.P.S.masksAhead = true) :
    (shapeAt (jobU A).Q 0).maskRows = 0 := by
  rw [u_shape0 A hfit hm]
  unfold sendingsFit at hfit
  simp only [Bool.and_eq_true] at hfit
  have h := hfit.1.2
  simp only [carriersFit, vecShapeFits, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1.1.1.1.1.1

/-- The first mask's first coin is the number of o_u's coins; it lies within the part's count. -/
theorem maskFirst_at (A : SendPub) (hfit : sendingsFit A.P = true) (hm : A.P.S.masksAhead = true) :
    maskFirstCoin A = dueOf (jobU A).Q.codes (shapeAt (jobU A).Q 0) ((jobU A).sort 0) ∧
      maskFirstCoin A ≤ (sendingPart (jobU A)).takes.e := by
  have h2 := u_two A hfit hm
  refine ⟨?_, offset_mono _ _ _ _ 1 (by omega) (Nat.le_refl _)⟩
  unfold maskFirstCoin
  rw [offset_succ _ _ _ 0 (by omega)]
  exact Nat.zero_add _

/-- **At "send o_u" the second round hangs on o_u's own coins alone**: two values of the coins with
the same cut below the first mask's first coin show the same items. (The first mask has no
answer.) -/
theorem u_answers_below (A : SendPub) (s : OnBytes.Params.IoppStage)
    (hfit : sendingsFit A.P = true) (hm : A.P.S.masksAhead = true)
    (hs : A.P.S.testU.head? = some s) (a : Ask) (h : List Fmt.Drawn) (x₀ : Fmt.Drawn)
    (c c' : Cs (sendingPart (jobU A)).takes)
    (hcut : c.cut ⟨0, 0⟩ ⟨0, maskFirstCoin A⟩ = c'.cut ⟨0, 0⟩ ⟨0, maskFirstCoin A⟩) :
    sendShownAt (jobU A) c a (h ++ [x₀]) = sendShownAt (jobU A) c' a (h ++ [x₀]) := by
  have hJ := fit_u A hfit
  obtain ⟨hlen, hsh⟩ := shapes_of_fit (jobU A) hJ
  obtain ⟨e1, e2⟩ := stAt_front (jobU A).Q 0
  obtain ⟨hf1, hf2⟩ := maskFirst_at A hfit hm
  have hz := u_noMask A hfit hm
  rw [answers_tie_behind (jobU A) hJ c a h x₀ x₀, answers_tie_behind (jobU A) hJ c' a h x₀ x₀]
  have key := answers_same (jobU A).Q (stFront (jobU A).Q 0) (stFront (jobU A).Q 0) rfl rfl
    (rowsR (jobU A).Q (rideBySort (jobU A))
      (vecData (jobU A) { input := a, heard := h ++ [x₀], own := () }) (recount (due_tie _ hJ) c))
    (rowsR (jobU A).Q (rideBySort (jobU A))
      (vecData (jobU A) { input := a, heard := h ++ [x₀], own := () }) (recount (due_tie _ hJ) c'))
    (fun _ _ _ => 0) (fun _ _ _ => 0) (seedsAt (jobU A).Q [x₀, x₀]) (fun k hk ha part j hj => by
      rw [← words_tie (jobU A).Q _ _ (rows_tie (jobU A) hJ c _) hlen hsh k hk part j hj,
        ← words_tie (jobU A).Q _ _ (rows_tie (jobU A) hJ c' _) hlen hsh k hk part j hj]
      refine congrArg rdE.val ?_
      match k, hk, ha with
      | 0, _, _ =>
        have hmain : ∀ r i, ((jobU A).rows { input := a, heard := h ++ [x₀], own := () }
            (coinsE c).toArray 0).main r i =
            ((jobU A).rows { input := a, heard := h ++ [x₀], own := () }
              (coinsE c').toArray 0).main r i := fun r i => by
          rw [sendRows_at (jobU A) _ _ 0 _ (u_sort0 A), sendRows_at (jobU A) _ _ 0 _ (u_sort0 A)]
          refine laid_main_congr _ _ _ _ _ _ hz (fun n hn => ?_) r i
          refine cut_coins (maskFirstCoin A) hf2 c c' hcut _ ?_
          rw [hf1]
          show 0 + n < _
          rw [Nat.zero_add]
          exact hn
        cases part with
        | main =>
          show (if _ then ((jobU A).rows _ (coinsE c).toArray 0).main _ _ else zeroE) =
            (if _ then ((jobU A).rows _ (coinsE c').toArray 0).main _ _ else zeroE)
          rw [hmain]
        | mask =>
          show (if j % 2 ^ OnBytes.ceilLog2 (shapeAt (jobU A).Q 0).maskRows <
              (shapeAt (jobU A).Q 0).maskRows then _ else zeroE) =
            (if j % 2 ^ OnBytes.ceilLog2 (shapeAt (jobU A).Q 0).maskRows <
              (shapeAt (jobU A).Q 0).maskRows then _ else zeroE)
          rw [hz, if_neg (Nat.not_lt_zero _), if_neg (Nat.not_lt_zero _)]
      | k + 1, hk, ha =>
        have hf := msg_fits (jobU A) hJ (k + 1) hk
        rw [u_sort1 A s hs k] at hf
        simp only [msgShapeFits, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hf
        exact absurd hf.1.1.1.1.1.2 ha)
  rw [e2, ← e1] at key
  rw [key]

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.answers_tie_behind
#print axioms ProofFile.Honest.K14.shows_first
#print axioms ProofFile.Honest.K14.shows_tie_two
#print axioms ProofFile.Honest.K14.u_sent
#print axioms ProofFile.Honest.K14.u_two
#print axioms ProofFile.Honest.K14.u_shape0
#print axioms ProofFile.Honest.K14.u_sort0
#print axioms ProofFile.Honest.K14.u_sort1
#print axioms ProofFile.Honest.K14.cut_coins
#print axioms ProofFile.Honest.K14.cutAll_single
#print axioms ProofFile.Honest.K14.u_noMask
#print axioms ProofFile.Honest.K14.maskFirst_at
#print axioms ProofFile.Honest.K14.u_answers_below
