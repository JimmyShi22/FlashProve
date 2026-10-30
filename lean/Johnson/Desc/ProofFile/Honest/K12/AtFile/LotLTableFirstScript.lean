-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LotLTableFirstScript.lean

It states no goal. No property of the protocol is claimed.

AT THE FIRST CHAIN's SCRIPT AT THE
BASE PROVER (`firstScriptAt`, AtFullSide/K1/FirstScript.lean): WHAT `plays_head_L`
(K12/AtFile/ClosingAtHead.lean) ASKS OF THE SCRIPT's TABLES AT THE CLOSING PROXIMITY TEST: htable,
hfixed outright; hold from one premise on a stand; and the table and fixed number at own 76,
the tree that the test opens.

  `record_at_finish`      where the finish is found, the record of the other senders is the sum of the
                          code switch's share and the test's share at that finish
  `numbers_apart_first`   354 is no number of the shared sending's jobs and none of the code switch's;
                          no number of the code switch's is a job's of the shared sending; none stands
                          twice
  `testLot_at_first`      the record holds at 354 the test's lot of trees
  `finishPlace_written`   by Lean's kernel: the written finish stands at ⟨1, none, 1, .K2⟩
  `finishNumber_at_base`  so the finish's member's number is 353
  `finishLot_at_first`    the record holds at 353 the finish's own table
  `finishNumber_apart`    353 is no number of the shared sending's jobs
  `fitsL_at_base`         the lot's public test says yes at the finish
  `closingTestTable_at_firstScript`, `closingTestFixed_at_firstScript`   htable, hfixed, to the letter
  `finishTable_at_firstScript`   the thread's table at own 76 is the finish's table number 0, as a
                          function; its fixed number is `roundsTo cF.blocksInOrder 353` = 48235
  `closingTestOldOpenings_at_firstScript`   hold, to the letter, from hready
  `closingTestPlays_at_firstScript`   `plays_head_L` called at these: `Plays` at member 354

The letters of `plays_head_L` at which all this stands: H := A.H · Q := firstScriptAt I Sz Op A cF ·
D := widerRows Sz A.Z A.G · readers := readersB I A.Z · closing := closingB A.Z A.G · pl := the finish
(hf) · own₀ := (). At other letters nothing is said.

By what. LotLTableHead.lean, LotLTableHold.lean; `joinFit_first`, `switch_in_first`, `testShareAt_some`
(AtFullSide/K1/FirstScript.lean); `share_in_add` (K12/JoinShare.lean); `share_tl_at`
(K2/JoinShare.lean); `borderNo_at` (Honest/Thread/Rows.lean); `places_head`, `fitsL_head_L`, `finishW`
(AtFullSide/K12/FitsAtHeadL.lean).

Hypotheses. h: the head. hA: the maker returns A at the filling. hf: the finish. hready (the last two):
AT EACH STAND in front of the test the frame hands the finish's part coins and at them its rows are
laid, at the stand's input and the challenges in front of member 353. The last also: hh, hT:
`plays_head_L`'s own, handed through.

Limits.
- hready IS A PREMISE ON EVERY STAND; where one stand fails it the last two say nothing.
- That a stand is reached is not said.
- FirstScript.lean's head's limits bind here.
- Full size, the format's second hash function alone.
- At the base prover's filling's return, at its own type of random values: NOT AT THE ONLINE PROVER,
  whose filling reads this one through the coins' map.
- The statements at the maker's return are typed at `OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit`: they cannot
  even be written at the online prover's return (`OnlineProverWithDescription FullSizeMatrix (protocolAtFiles files).EncodingRandomness Cells Unit Unit`,
  E2E/TheHonestProver.lean): no law through `OnlineProverParts.through` is made here.
- Nothing on completeness of the chain, soundness or hiding.

NOT IN FRONT OF A LAW OVER COINS: `closingTestOldOpenings_at_firstScript` and
`closingTestPlays_at_firstScript` bear this label; the rule is at its home, the head of
Johnson/Bind/ForProver/FiveFieldsAt.lean.
This file's own ground, in the rule's terms.
- h and hA speak of the public files, of the letters I and Op (how an index, an instance and the
  challenges are read, and one named member of the index's type) and of what the maker returns at
  the filling made of them. By their text they name no coin, no run's input (its index, its trace)
  and no Script: of neither kind.
- hf, hh and hT speak of the finish, of the prover's side that the search finds at the test's place
  and of the book's entries: they name no coin.
- hready is itself bound over all coins and every stand: by itself it picks among no coins.
- w, the run's input, is a letter under no premise in front. It holds the committer's coins (its
  field rc) and the hidden input (its fields w₀ and trace).
- A run's coins k are bound inside each end. Beside k the first binds the letters st, m and E (the
  verifier's state, the state of the prover's side, the available tables) under `Thr … 354 k st m
  E`, and the second, through `Plays`, s, m and E under the same: a premise of the first kind: it
  names k; by its text, at a fixed state, m and E it can hold at some values of the coins and fail
  at others.
- `Plays` | `PlaysS` binds besides l under `chainSteps … (k.look T.chain) … = .ok l`: of the first
  kind.
- ds, the challenges, stands under `drawsFit` (no coin) and under `chainStopAt (T.φ.sees m.st.input)
  …`: no run's coin is among its arguments (`Part.stopAt`, Honest/Side.lean), but in the first chain
  the face shows a part's second stop the whole input of m (`Face.sees`, Honest/Frame.lean), which
  holds rc and the hidden input: of the first kind as far as such a stop reads rc, of the second as
  far as it reads the index or the trace; what the parts at 354 read is not fixed here.
- One clause of the invariant says that the input of m is w and meets Vd, a letter for a predicate
  on the input: what it reads of the input is not fixed here.
- The thread's other letters (test, carryX, item, n₁, n₂, b₀, Vd, Rd, Kp) stand under no premise in
  front that names a coin; the invariant reads them. The Script is no letter: it is the term
  `firstScriptAt`.
- The other theorems of this file tie no letter to a coin: where k stands in them it is bound inside
  an equation of functions. They bear none.
- What lifts the bar: for the state, m, E and l the made terms would be those of the honest run at
  the border, as terms of w, k and the challenges, and the lemma would show the premises at them at
  every value of the coins. For ds, which no term of the prover's makes, the lemma would show that
  at each ds `chainStopAt … = none` holds at every value of rc or at none. None is known to this
  file: the bar is flat.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLTableHold
import Johnson.Desc.ProofFile.Honest.K12.AtFile.ClosingAtHead
import AtFullSide.K1.FirstScript

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open VerifiableInference.Desc (Block Chain Place Strs)
open VerifiableInference.Desc.K12 (T12 proximityTestKind guardedProximityTestParts)
open OnBytes.Maker (WholeD)
open ProofFile.Honest.FirstThread (lettersHead WtF)
open ProofFile.Honest.K1 (LocB witB jobTwoAt jobLaterAt jobWAt k1MembersW firstScriptAt otherSendersAt
  switchShareB testShareOf testShareAt_some testJobAt testOk readersB closingB cellsB tokB noTree
  joinFit_first switch_in_first)
open ProofFile.Honest.K12.AtProof (jobL doorAtL fitsL finishAt finishW places_head fitsL_head_L places_at_L)
open ProofFile.Honest.K2.Law (SwitchCoins)
open P5J (AtMgA TS)

variable {W₀ : Type} {Z : VerifierAndGoals.PublicFiles} {I : WiderIn W₀} {Sz : OnBytes.HonestTrace.Sz} {Op : OnlineProverArguments}
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit} {D : WholeD} {r : LPFD.Full.RunPF} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {pl : K2.SwitchPlace}

/-! ## 1 The record -/

/-- Where the finish is found, the record is the sum of the two shares. -/
theorem record_at_finish (hf : finishAt A.Z A.G = some pl) :
    otherSendersAt I Sz A cF = (switchShareB I Sz A cF).add (testShareOf I Sz A cF pl) :=
  congrArg (switchShareB I Sz A cF).add (testShareAt_some hf)

/-- **The members' numbers stand apart.** -/
theorem numbers_apart_first (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction Sz Op) = .ok A)
    (hf : finishAt A.Z A.G = some pl) :
    354 ∉ (k1MembersW (jobTwoAt Sz A.Z A.G) (jobLaterAt Sz A.Z A.G) (jobWAt Op A.Z A.G)).map (·.1) ∧
      354 ∉ (switchShareB I Sz A cF).tn ∧
      (∀ b ∈ (switchShareB I Sz A cF).tn, b ∉ (k1MembersW (jobTwoAt Sz A.Z A.G)
        (jobLaterAt Sz A.Z A.G) (jobWAt Op A.Z A.G)).map (·.1)) ∧
      (switchShareB I Sz A cF).tn.Nodup := by
  have F := (joinFit_first (I := I) (S := Sz) (Op := Op) h hA).nums
  rw [record_at_finish hf] at F
  have hT : ((switchShareB I Sz A cF).tn ++ [354]).Nodup := F.of_append_right
  have h354 : 354 ∈ ((switchShareB I Sz A cF).add (testShareOf I Sz A cF pl)).tn :=
    List.mem_append_right (switchShareB I Sz A cF).tn (List.mem_singleton.2 rfl)
  exact ⟨fun hj => List.disjoint_of_nodup_append F hj h354,
    fun ht => List.disjoint_of_nodup_append hT ht (List.mem_singleton.2 rfl),
    fun b hb hj => List.disjoint_of_nodup_append F hj (List.mem_append_left [354] hb),
    hT.of_append_left⟩

/-- **The record holds at 354 the test's lot of trees**, at the job at the filled door, at "always
yes", at the rounds in front of the member. -/
theorem testLot_at_first (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction Sz Op) = .ok A)
    (hf : finishAt A.Z A.G = some pl) :
    (otherSendersAt I Sz A cF).tl 354 =
      testTreeLot 0 (jobL (H2U.p12OfMade A.Z.made) (doorAtL A.Z) (widerRows Sz A.Z A.G) (readersB I A.Z)
            (closingB A.Z A.G) pl)
        () (roundsTo cF.blocksInOrder 354) (fun _ _ _ => true) := by
  rw [record_at_finish hf]
  exact (share_in_add (switchShareB I Sz A cF) 0 (testJobAt I Sz A.Z A.G pl) ()
    (roundsTo cF.blocksInOrder 354) 77 (P5J.At.arr A.Z) testOk pl.sizes.codes _ _ 354 noTree
    (Bool.eq_false_iff.2 fun hc =>
      (numbers_apart_first h hA hf).2.1 (List.contains_iff_mem.1 hc))).2.2.2

set_option maxRecDepth 1000000 in
/-- By the kernel: the written finish's place. An equation of values: no control. -/
theorem finishPlace_written : finishW.map (·.place) = some ⟨1, none, 1, .K2⟩ := by
  decide +kernel

/-- **The finish's member's number is 353.** -/
theorem finishNumber_at_base (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction Sz Op) = .ok A)
    (hf : finishAt A.Z A.G = some pl) : borderNo cF.blocksInOrder pl.place = 353 := by
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  obtain ⟨-, eG, -⟩ := atPure_at_laid_ground h.laid O.blank hA
  have e : finishAt A.Z A.G = finishW := by
    unfold finishAt finishW
    rw [places_head h.toAtMg (G := A.G) (by rw [eG]; exact O.blank)]
  have hp : pl.place = ⟨1, none, 1, .K2⟩ := by
    have t := finishPlace_written
    rw [← e, hf] at t
    exact Option.some.inj t
  obtain ⟨⟨b, hb, hbp⟩, -⟩ := places_at_L h.toAtMg
  rw [hp, ← hbp]
  exact borderNo_at cF.blocksInOrder 353 b (ProofFile.Honest.FirstThread.places_at_head h) hb

/-- **The record holds at 353 the finish's own table.** -/
theorem finishLot_at_first (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction Sz Op) = .ok A)
    (hf : finishAt A.Z A.G = some pl) :
    (otherSendersAt I Sz A cF).tl 353 =
      ⟨fun j k v hd => (pl.place, K2.switchTableAt A.B 0 (K2.coreSender K2.freshTable)
          (widerRows Sz A.Z A.G) (readersB I A.Z) (closingB A.Z A.G) pl k v hd j), fun _ => 0⟩ := by
  have hno := finishNumber_at_base (I := I) (Sz := Sz) (Op := Op) h hA hf
  have hp : pl ∈ K2.switchPlaces A.Z A.G := List.mem_of_find?_eq_some hf
  have hm : 353 ∈ (switchShareB I Sz A cF).tn := by
    rw [← hno]
    exact List.mem_map.2 ⟨pl, hp, rfl⟩
  have hnd : ((K2.switchPlaces A.Z A.G).map fun p => borderNo cF.blocksInOrder p.place).Nodup :=
    (numbers_apart_first (I := I) h hA hf).2.2.2
  have t : (switchShareB I Sz A cF).tl (borderNo cF.blocksInOrder pl.place) =
      ⟨fun j k v hd => (pl.place, K2.switchTableAt A.B 0 (K2.coreSender K2.freshTable)
          (widerRows Sz A.Z A.G) (readersB I A.Z) (closingB A.Z A.G) pl k v hd j), fun _ => 0⟩ :=
    K2.Law.share_tl_at 0 _ _ _ _ (fun p => borderNo cF.blocksInOrder p.place) _ _ _ _ _ _ hnd hp
  rw [hno] at t
  rw [(switch_in_first (I := I) (S := Sz) (A := A) (cF := cF)).tl 353 hm]
  exact t

/-! ## 2 What `plays_head_L` asks of the tables -/

/-- **htable at the first chain's Script.** -/
theorem closingTestTable_at_firstScript (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction Sz Op) = .ok A)
    (hf : finishAt A.Z A.G = some pl) (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : LocB W₀ → Prop) (Rd : Nat → LocB W₀ → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : LocB W₀) :
    ∀ τ, τ + 1 < (H2U.p12OfMade A.Z.made).nums.stages.length →
      (lettersHead h A.H (firstScriptAt I Sz Op A cF) test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.table
          (.own (treesTo cF.blocksInOrder 354 + τ)) =
        testTbl (lettersHead h A.H (firstScriptAt I Sz Op A cF) test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.chain
          (jobL (H2U.p12OfMade A.Z.made) (doorAtL A.Z) (widerRows Sz A.Z A.G) (readersB I A.Z)
            (closingB A.Z A.G) pl) ()
          ((lettersHead h A.H (firstScriptAt I Sz Op A cF) test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.front +
            roundsTo cF.blocksInOrder 354) (fun _ _ _ => true) τ :=
  closingTestTable_at_joinedScript h A.H (cellsB I A.Z) tokB (P5J.At.arr A.Z) (witB I A.Z) ()
    (k1MembersW (jobTwoAt Sz A.Z A.G) (jobLaterAt Sz A.Z A.G) (jobWAt Op A.Z A.G))
    (otherSendersAt I Sz A cF) test carryX item n₁ n₂ b₀ Vd Rd Kp w (widerRows Sz A.Z A.G) (readersB I A.Z)
    (closingB A.Z A.G) pl
    (numbers_apart_first h hA hf).1 () rfl (testLot_at_first h hA hf)

/-- **hfixed at the first chain's Script.** -/
theorem closingTestFixed_at_firstScript (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction Sz Op) = .ok A)
    (hf : finishAt A.Z A.G = some pl) (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : LocB W₀ → Prop) (Rd : Nat → LocB W₀ → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : LocB W₀) :
    ∀ τ, τ + 1 < (H2U.p12OfMade A.Z.made).nums.stages.length →
      (lettersHead h A.H (firstScriptAt I Sz Op A cF) test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.fixed
          (.own (treesTo cF.blocksInOrder 354 + τ)) =
        (lettersHead h A.H (firstScriptAt I Sz Op A cF) test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.front +
            roundsTo cF.blocksInOrder 354 +
          seedRound (H2U.p12OfMade A.Z.made).nums.stages τ :=
  closingTestFixed_at_joinedScript h A.H (cellsB I A.Z) tokB (P5J.At.arr A.Z) (witB I A.Z) ()
    (k1MembersW (jobTwoAt Sz A.Z A.G) (jobLaterAt Sz A.Z A.G) (jobWAt Op A.Z A.G))
    (otherSendersAt I Sz A cF) test carryX item n₁ n₂ b₀ Vd Rd Kp w (widerRows Sz A.Z A.G) (readersB I A.Z)
    (closingB A.Z A.G) pl
    (numbers_apart_first h hA hf).1 () _ (testLot_at_first h hA hf)

/-- 353 is no number of the shared sending's jobs. -/
theorem finishNumber_apart (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction Sz Op) = .ok A)
    (hf : finishAt A.Z A.G = some pl) :
    353 ∉ (k1MembersW (jobTwoAt Sz A.Z A.G) (jobLaterAt Sz A.Z A.G) (jobWAt Op A.Z A.G)).map
      (·.1) := by
  refine (numbers_apart_first (I := I) h hA hf).2.2.1 353 ?_
  rw [← finishNumber_at_base (I := I) (Sz := Sz) (Op := Op) h hA hf]
  exact List.mem_map.2 ⟨pl, List.mem_of_find?_eq_some hf, rfl⟩

/-- **The tree that the test opens, own 76, at the first chain's Script.** -/
theorem finishTable_at_firstScript (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction Sz Op) = .ok A)
    (hf : finishAt A.Z A.G = some pl) (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : LocB W₀ → Prop) (Rd : Nat → LocB W₀ → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : LocB W₀) :
    (lettersHead h A.H (firstScriptAt I Sz Op A cF) test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.table
        (.own 76) =
      (fun k v hd => (pl.place, K2.switchTableAt A.B 0 (K2.coreSender K2.freshTable)
        (widerRows Sz A.Z A.G) (readersB I A.Z) (closingB A.Z A.G) pl k v hd 0)) ∧
    (lettersHead h A.H (firstScriptAt I Sz Op A cF) test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.fixed
        (.own 76) = roundsTo cF.blocksInOrder 353 ∧
    roundsTo cF.blocksInOrder 353 = 48235 :=
  finishTable_at_joinedScript h A.H (cellsB I A.Z) tokB (P5J.At.arr A.Z) (witB I A.Z) ()
    (k1MembersW (jobTwoAt Sz A.Z A.G) (jobLaterAt Sz A.Z A.G) (jobWAt Op A.Z A.G))
    (otherSendersAt I Sz A cF) test carryX item n₁ n₂ b₀ Vd Rd Kp w (widerRows Sz A.Z A.G) (readersB I A.Z)
    (closingB A.Z A.G) pl
    (finishNumber_apart h hA hf) _ (finishLot_at_first h hA hf)

/-- The lot's public test says yes at the finish. -/
theorem fitsL_at_base (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction Sz Op) = .ok A)
    (hf : finishAt A.Z A.G = some pl) : fitsL (H2U.p12OfMade A.Z.made) pl = true := by
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  obtain ⟨-, eG, -⟩ := atPure_at_laid_ground h.laid O.blank hA
  obtain ⟨pl', hf', hfit⟩ := fitsL_head_L h.toAtMg (G := A.G) (by rw [eG]; exact O.blank)
  obtain rfl : pl' = pl := Option.some.inj (hf'.symm.trans hf)
  exact hfit

/-- **hold at the first chain's Script**, from hready. -/
theorem closingTestOldOpenings_at_firstScript (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction Sz Op) = .ok A)
    (hf : finishAt A.Z A.G = some pl) (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : LocB W₀ → Prop) (Rd : Nat → LocB W₀ → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : LocB W₀)
    (hready : ∀ k st m E, Thr (lettersHead h A.H (firstScriptAt I Sz Op A cF) test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 354 k st m E →
      ∃ c : SwitchCoins pl.sizes pl.others pl.foldVars pl.carries, K2.handed 0 pl k = some c ∧
        ∃ V : ℕ → Johnson.Prover.Send.Rows, K2.switchRowsLaid (widerRows Sz A.Z A.G) (readersB I A.Z)
          (closingB A.Z A.G) pl c m.st.input (m.st.heard.take (roundsTo cF.blocksInOrder 353)) = .ok V) :
    ∀ k st m E, Thr (lettersHead h A.H (firstScriptAt I Sz Op A cF) test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 354 k st
        m E → ∀ d ∈ (proximityTestKind guardedProximityTestParts (H2U.p12OfMade A.Z.made) : Block T12 Unit).rounds,
        ∀ o ∈ d.opens, oldSrc E.sent o.2 = true → ∃ pt, E.tree o.2 = some pt ∧ pt.2.words = o.1.W :=
  closingTestOldOpenings_at_joinedScript h A.H (cellsB I A.Z) tokB (P5J.At.arr A.Z) (witB I A.Z) ()
    (k1MembersW (jobTwoAt Sz A.Z A.G) (jobLaterAt Sz A.Z A.G) (jobWAt Op A.Z A.G))
    (otherSendersAt I Sz A cF) test carryX item n₁ n₂ b₀ Vd Rd Kp w (widerRows Sz A.Z A.G) (readersB I A.Z)
    (closingB A.Z A.G) pl
    (finishNumber_apart h hA hf) (finishLot_at_first h hA hf) (fitsL_at_base h hA hf) hready

/-! ## 3 The call -/

/-- **`Plays` at the closing test, at the first chain's Script**: `plays_head_L` with hold, htable and
hfixed paid. -/
theorem closingTestPlays_at_firstScript (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction Sz Op) = .ok A)
    (hf : finishAt A.Z A.G = some pl) (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : LocB W₀ → Prop) (Rd : Nat → LocB W₀ → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : LocB W₀)
    (hh : (A.H.first.find? fun g => g.place == (H2U.p12OfMade A.Z.made).place) =
      some (proverSideOfProximityTest (jobL (H2U.p12OfMade A.Z.made) (doorAtL A.Z) (widerRows Sz A.Z A.G) (readersB I A.Z)
                             (closingB A.Z A.G) pl)))
    (hT : tiesB A.B (H2U.p12OfMade A.Z.made).place (AtProof.membersL pl).length = true)
    (hready : ∀ k st m E, Thr (lettersHead h A.H (firstScriptAt I Sz Op A cF) test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 354 k st m E →
      ∃ c : SwitchCoins pl.sizes pl.others pl.foldVars pl.carries, K2.handed 0 pl k = some c ∧
        ∃ V : ℕ → Johnson.Prover.Send.Rows, K2.switchRowsLaid (widerRows Sz A.Z A.G) (readersB I A.Z)
          (closingB A.Z A.G) pl c m.st.input (m.st.heard.take (roundsTo cF.blocksInOrder 353)) = .ok V) :
    Plays (lettersHead h A.H (firstScriptAt I Sz Op A cF) test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 354 :=
  plays_head_L h A.H (firstScriptAt I Sz Op A cF) test carryX item n₁ n₂ b₀ Vd Rd Kp w
    (widerRows Sz A.Z A.G) (readersB I A.Z) (closingB A.Z A.G) pl hh hT
    (closingTestOldOpenings_at_firstScript h hA hf test carryX item n₁ n₂ b₀ Vd Rd Kp w hready) ()
    (closingTestTable_at_firstScript h hA hf test carryX item n₁ n₂ b₀ Vd Rd Kp w)
    (closingTestFixed_at_firstScript h hA hf test carryX item n₁ n₂ b₀ Vd Rd Kp w)

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.record_at_finish
#print axioms ProofFile.Honest.K12.numbers_apart_first
#print axioms ProofFile.Honest.K12.testLot_at_first
#print axioms ProofFile.Honest.K12.finishPlace_written
#print axioms ProofFile.Honest.K12.finishNumber_at_base
#print axioms ProofFile.Honest.K12.finishLot_at_first
#print axioms ProofFile.Honest.K12.closingTestTable_at_firstScript
#print axioms ProofFile.Honest.K12.closingTestFixed_at_firstScript
#print axioms ProofFile.Honest.K12.finishNumber_apart
#print axioms ProofFile.Honest.K12.finishTable_at_firstScript
#print axioms ProofFile.Honest.K12.fitsL_at_base
#print axioms ProofFile.Honest.K12.closingTestOldOpenings_at_firstScript
#print axioms ProofFile.Honest.K12.closingTestPlays_at_firstScript
