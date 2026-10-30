-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LotLTableHold.lean

It states no goal. No property of the protocol is claimed.

`plays_head_L`'s PREMISE hold
(K12/AtFile/ClosingAtHead.lean), TO THE LETTER, AT THE JOINED SCRIPT: at a stand in front of the first
chain's closing proximity test, every old tree that the test's rounds open is at hand with the width
that the round declares. There is one such tree, own 76, the last code switch's, of nine words.

  `oldOpenings_at_stand`   general in the thread: `old_of_hand` (not beneath this file) with the
                           width asked of the thread's table AT THE STAND ALONE
  `switchTable_shape`      where the frame hands the switch's part its coins and its rows are laid,
                           the switch's table number j has the depth and width of the sending's tree j
  `firstOfMap`             a helper on lists
  `finishTree_of_fitsL`    where the lot's public test `fitsL` says yes, the finish's sending has a
                           tree number 0 with the depth and width of the test's one first tree
  `oldOpeningsAre`         A PUBLIC TEST: every old opening of a list of rounds has one source and
                           one width
  `oldOpenings_written`    by Lean's kernel, at the written place: own 76, nine words. THREE CONTROLS:
                           at eight words no; at own 75 no; and there is an old opening
  `rounds_head_L`          under the head the seated place's rounds are the written place's
  `closingTestOldOpenings_at_joinedScript`   hold

WHY NOT `old_of_hand`. Its premise asks the width of the thread's table at every coin, input and list
of challenges. At the joined Script the table at own 76 is `switchTableAt`, which is the table without
a word wherever the frame hands the part nothing or its rows refuse: there the width is 0, not 9. So
that premise is false at the joined Script at every book at which some coins are refused, and hold
itself needs what hready says.

Hypotheses of the last. h: the head. hb, htl: as in `finishTable_at_joinedScript` (LotLTableHead.lean),
at the sender `coreSender freshTable`. hfit: the lot's public test at the finish
(`fitsL_head_L`, AtFullSide/K12/FitsAtHeadL.lean, has it under the head). hready: AT EACH STAND the
frame hands the switch's part coins, and at them the switch's rows are laid at the stand's input and
the challenges in front of member 353.

Limits.
- hready IS A PREMISE ON EVERY STAND. Where one stand fails it, nothing is said of any.
- That a stand is reached is not said.
- Widths and sources alone: nothing on what a column holds.
- Full size, the format's second hash function alone.
- Nothing on completeness, soundness or hiding.

NOT IN FRONT OF A LAW OVER COINS: `oldOpenings_at_stand`, `switchTable_shape` and
`closingTestOldOpenings_at_joinedScript` bear this label; the rule is at its home, the head of
Johnson/Bind/ForProver/FiveFieldsAt.lean.
This file's own ground, in the rule's terms.
- In `oldOpenings_at_stand`, at any thread T, k, s, m and E are the theorem's own binders. The
  letters s, m and E (the verifier's state, the state of the prover's side, the available tables)
  stand under u : `Thr T b k s m E`, and m besides under hw, which reads `T.tableAt o.2 k m`:
  premises of the first kind: they name k; by their text, at fixed s, m and E they can hold at some
  values of the coins and fail at others.
- In `closingTestOldOpenings_at_joinedScript` k is bound inside the end, with the letters st, m and
  E under `Thr … 354 k st m E`: of the first kind. h, hb, htl and hfit speak of the public files, of
  the lots from which the Script is joined and of the lot's public test: they name no coin (htl is
  an equation of functions of k: it holds or fails at all k alike); hb and htl are of the second
  kind: they read the Script's make. hready is itself bound over all coins and every stand: by
  itself it picks among no coins. w, the run's input, is a letter under no premise in front; it
  holds the committer's coins (its field rc) and the hidden input.
- In `switchTable_shape` k is the theorem's own binder. The letter c stands under hH : `K2.handed ch
  p k = some c`, which names k, and the letter V under hV : `K2.switchRowsLaid … c w … = .ok V`,
  which names c, a cut of k, and w, whose rc holds the committer's coins: premises of the first
  kind: by their text, at a fixed c (a fixed V) they can hold at some values of the coins and fail
  at others. ht speaks of the sending's public sizes: it names no coin.
- The other theorems of this file name no coin: they bear none.
- What lifts the bar. For c and V the made terms are what `K2.handed` and `K2.switchRowsLaid`
  return. At the closing place, at the lot's own closing, `switch_lot_returns_at_closing_place`
  (LotLOwedAtHead.lean), from h, hB, hG, hf and hok (the public files, the book, the ground, the
  finish, the closing's public test: no coin), shows, at every k, every list of challenges and every
  w whose instance passes `K2.publicOk`, that both return; `finishIsHanded_at_base`
  (LotLAcceptedFields.lean) shows the first at every k. For the states, m and E under a stand none
  is known to this file: there the bar is flat.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLTableHead
import Johnson.Desc.ProofFile.Honest.K12.ColsReturn
import Johnson.Desc.ProofFile.Honest.K2.Law.RowsTie
import Johnson.Desc.ProofFile.Honest.Thread.Sent
import Johnson.Desc.ProofFile.Honest.K1.TableShape
import AtFullSide.K12.OpenTiesAtHeadWL
import AtFullSide.K12.FirstAnyAtHeadL

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open VerifiableInference.Desc (Block Chain Place Strs)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT)
open H2K.Member (piLFull)
open ProofFile.Honest.FirstThread (lettersHead Script WtF Others joinQ)
open ProofFile.Honest.K1 (SendJob PlaceIn)
open ProofFile.Honest.K12.AtProof (jobL doorAtL numbersL_at_head fitsL fitsLs sentL fourOf)
open ProofFile.Honest.K2.Law (SwitchCoins)
open P5J (AtMg AtMgA CellsM TS)

/-! ## 1 At a stand -/

/-- **`RunPlays.old` at a stand**, where each old opening is in hand at the border and the thread's
table AT THE STAND has the declared width. -/
theorem oldOpenings_at_stand {St Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk St Cl V W X Pb)
    {b : ℕ} (decls : List Fmt.DeclaredRound) {k : Coins Bk} {s : St} {m : Mid W X} {E : Env}
    (u : Thr T b k s m E)
    (hw : ∀ d ∈ decls, ∀ o ∈ d.opens, oldSrc (treesTo T.bs b) o.2 = true →
      o.2 ∈ T.hand b ∧ (T.tableAt o.2 k m).2.words = o.1.W) :
    ∀ d ∈ decls, ∀ o ∈ d.opens, oldSrc E.sent o.2 = true →
      ∃ pt, E.tree o.2 = some pt ∧ pt.2.words = o.1.W := by
  obtain ⟨⟨-, hH⟩, -, -, -, ⟨-, -, hsent, -⟩, -, -⟩ := u
  intro d hd o ho hO
  rw [hsent] at hO
  obtain ⟨hin, hwd⟩ := hw d hd o ho hO
  obtain ⟨pt, hE, -, hs⟩ := T.handAt_elim (hH _ hin)
  unfold Table.same at hs
  rw [Bool.and_eq_true, Bool.and_eq_true] at hs
  exact ⟨pt, hE, (beq_iff_eq.1 hs.1.2).trans hwd⟩

/-! ## 2 The switch's table's two numbers -/

/-- **Where the part is handed its coins and its rows are laid, the switch's table number j has the
depth and the width of the sending's tree number j.** -/
theorem switchTable_shape {W₀ Rc Xi Tr : Type} {Bk : ProverCoinCounts} (ch : ℕ) (D : RowDataOf Xi)
    (readers : Local W₀ Rc Xi Tr → Readers) (closing : K2.Closing) (p : K2.SwitchPlace)
    (k : Coins Bk) (w : Local W₀ Rc Xi Tr) (hd : List Fmt.Drawn) (j : ℕ)
    {c : SwitchCoins p.sizes p.others p.foldVars p.carries} (hH : K2.handed ch p k = some c)
    {V : ℕ → Johnson.Prover.Send.Rows} (hV : K2.switchRowsLaid D readers closing p c w hd = .ok V)
    {a width : ℕ}
    (ht : ∃ t, (K2.sendingPar p.sizes.codes (K2.switchSent p.sizes p.others)).trees[j]? = some t ∧
      t.logN = a ∧ t.mainWidth + t.maskWidth = width) :
    (K2.switchTableAt Bk ch (K2.coreSender K2.freshTable) D readers closing p k w hd j).logLength =
        a ∧
      (K2.switchTableAt Bk ch (K2.coreSender K2.freshTable) D readers closing p k w hd j).words =
        width := by
  obtain ⟨t, ht, ha, hwd⟩ := ht
  obtain ⟨T, hT, hl, hw⟩ := K1.treeTables_at _ V j t ht
  have e : K2.switchTableAt Bk ch (K2.coreSender K2.freshTable) D readers closing p k w hd j = T := by
    rw [K2.Law.table_of_rows, hH]
    show (((K2.switchRowsLaid D readers closing p c w hd).toOption).bind _).getD K2.noTable = T
    rw [hV]
    show ((K1.treeTables (K2.sendingPar p.sizes.codes (K2.switchSent p.sizes p.others)) V)[j]?).getD
      K2.noTable = T
    rw [hT]
    rfl
  rw [e]
  exact ⟨hl.trans ha, hw.trans hwd⟩

/-- A list whose image is one value has a first entry with that image. -/
theorem firstOfMap {α β : Type} (g : α → β) (y : β) : ∀ L : List α, [y] = L.map g →
    ∃ t, L[0]? = some t ∧ g t = y
  | [], h => by simp at h
  | t :: _, h => ⟨t, rfl, ((List.cons.inj h).1).symm⟩

/-- **Where the lot's public test says yes, the finish's sending has a tree number 0 with the depth
and width of the test's one first tree.** -/
theorem finishTree_of_fitsL {q : P12} {p : K2.SwitchPlace} (h : fitsL q p = true) {a width : ℕ}
    (hq : q.nums.first.map (fun y => (y.1.a, y.1.W)) = [(a, width)]) :
    ∃ t, (K2.sendingPar p.sizes.codes (K2.switchSent p.sizes p.others)).trees[0]? = some t ∧
      t.logN = a ∧ t.mainWidth + t.maskWidth = width := by
  simp only [fitsL, fitsLs, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    beq_iff_eq] at h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, h15, -⟩ := h
  rw [hq] at h15
  have et : (K2.sendingPar p.sizes.codes (K2.switchSent p.sizes p.others)).trees =
      ((VerifiableInference.Desc.Own.treesMade p.sizes.codes (sentL p)).getD {}).shapes.toList := by
    unfold VerifiableInference.Desc.K1.Par.trees
    rw [show (K2.sendingPar p.sizes.codes (K2.switchSent p.sizes p.others)).codes = p.sizes.codes
      from rfl, K2.sendingPar_sent]
    show _ = ((VerifiableInference.Desc.Own.treesMade p.sizes.codes
      (K2.switchSent p.sizes p.others)).getD {}).shapes.toList
    cases VerifiableInference.Desc.Own.treesMade p.sizes.codes (K2.switchSent p.sizes p.others) <;>
      rfl
  rw [et]
  obtain ⟨t, h0, hg⟩ := firstOfMap _ _ _ h15
  exact ⟨t, h0, congrArg Prod.fst hg, congrArg Prod.snd hg⟩

/-! ## 3 Which old trees the test opens -/

/-- **A public test**: every opening of these rounds whose source is old (`oldSrc`) has the source
source and declares the width width. -/
def oldOpeningsAre (decls : List Fmt.DeclaredRound) (sent : ℕ) (source : Fmt.TreeSource) (width : ℕ) :
    Bool :=
  decls.all fun d => d.opens.all fun o =>
    !oldSrc sent o.2 || (decide (o.2 = source) && decide (o.1.W = width))

set_option maxRecDepth 1000000 in
/-- **At the written place**: own 76, nine words. Three controls: at eight words the test says no; at
own 75 it says no; and an old opening is there. -/
theorem oldOpenings_written :
    oldOpeningsAre (proximityTestKind guardedProximityTestParts piLFull : Block T12 Unit).rounds 77 (.own 76) 9 = true ∧
      oldOpeningsAre (proximityTestKind guardedProximityTestParts piLFull : Block T12 Unit).rounds 77 (.own 76) 8 = false ∧
      oldOpeningsAre (proximityTestKind guardedProximityTestParts piLFull : Block T12 Unit).rounds 77 (.own 75) 9 = false ∧
      ((proximityTestKind guardedProximityTestParts piLFull : Block T12 Unit).rounds.any fun d =>
        d.opens.any fun o => oldSrc 77 o.2) = true := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- Under the head the seated place's rounds are the written place's. -/
theorem rounds_head_L {o : ProofFile.SecondHashFunctionArgument} (h : AtMg o Z D₀ r Zp Np cF) :
    (proximityTestKind guardedProximityTestParts (fourOf Np).L : Block T12 Unit).rounds =
      (proximityTestKind guardedProximityTestParts piLFull : Block T12 Unit).rounds := by
  refine Option.some.inj ?_
  rw [← VerifiableInference.Desc.K12.k12_rounds guardedProximityTestParts _ (Light.reads_head_L h).2.2.2,
    ← VerifiableInference.Desc.K12.k12_rounds guardedProximityTestParts _ Light.facts_LFull.plan,
    Light.nums_head_L h]

/-! ## 4 hold -/

section
variable (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X Xj Xk : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (cells : Local W₀ Rc ProofFile.Inst Tr → CellsM OnBytes.Flat.numsFull)
  (tok : Local W₀ Rc ProofFile.Inst Tr → P5J.At.Tok) (arr : ℕ → ℕ → ℕ)
  (wit : Local W₀ Rc ProofFile.Inst Tr → PlaceIn Xj) (ownK : Xk)
  (jobs : List (ℕ × SendJob (PlaceIn Xj) Xk)) (O : Others Bk (Local W₀ Rc ProofFile.Inst Tr))
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)
  (D : RowDataOf ProofFile.Inst) (readers : Local W₀ Rc ProofFile.Inst Tr → Readers)
  (closing : K2.Closing) (pl : K2.SwitchPlace)

/-- **`plays_head_L`'s premise hold, at the joined Script.** -/
theorem closingTestOldOpenings_at_joinedScript (hb : 353 ∉ jobs.map (·.1))
    (htl : O.tl 353 =
      ⟨fun j k v hd => (pl.place,
          K2.switchTableAt Bk 0 (K2.coreSender K2.freshTable) D readers closing pl k v hd j),
        fun _ => 0⟩)
    (hfit : fitsL (H2U.p12OfMade Zp.made) pl = true)
    (hready : ∀ k st m E, Thr (lettersHead h H (joinQ cF.blocksInOrder 0 cells tok arr wit ownK jobs O) test
        carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 354 k st m E →
      ∃ c : SwitchCoins pl.sizes pl.others pl.foldVars pl.carries, K2.handed 0 pl k = some c ∧
        ∃ V : ℕ → Johnson.Prover.Send.Rows, K2.switchRowsLaid D readers closing pl c m.st.input
          (m.st.heard.take (roundsTo cF.blocksInOrder 353)) = .ok V) :
    ∀ k st m E, Thr (lettersHead h H (joinQ cF.blocksInOrder 0 cells tok arr wit ownK jobs O) test carryX item
        n₁ n₂ b₀ Vd Rd Kp w).thread 354 k st m E →
      ∀ d ∈ (proximityTestKind guardedProximityTestParts (H2U.p12OfMade Zp.made) : Block T12 Unit).rounds,
        ∀ o ∈ d.opens, oldSrc E.sent o.2 = true →
          ∃ pt, E.tree o.2 = some pt ∧ pt.2.words = o.1.W := by
  intro k st m E u
  obtain ⟨c, hH, V, hV⟩ := hready k st m E u
  obtain ⟨et, ef, -⟩ := finishTable_at_joinedScript h H cells tok arr wit ownK jobs O test carryX item
    n₁ n₂ b₀ Vd Rd Kp w D readers closing pl hb (K2.coreSender K2.freshTable) htl
  have hq : (H2U.p12OfMade Zp.made).nums.first.map (fun y => (y.1.a, y.1.W)) = [(23, 9)] := by
    rw [numbersL_at_head h.toAtMg, Light.first_head_L h.toAtMg]
    rfl
  have h77 : treesTo (lettersHead h H (joinQ cF.blocksInOrder 0 cells tok arr wit ownK jobs O) test carryX
      item n₁ n₂ b₀ Vd Rd Kp w).thread.bs 354 = 77 := treesTo_354 h.toAtMg
  refine oldOpenings_at_stand _ _ u (fun d hd o ho hO => ?_)
  rw [h77] at hO
  rw [numbersL_at_head h.toAtMg, rounds_head_L h.toAtMg] at hd
  have a := List.all_eq_true.1 (List.all_eq_true.1 oldOpenings_written.1 d hd) o ho
  rw [hO, Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq,
    decide_eq_true_eq] at a
  obtain ⟨e1, e2⟩ := a
  rw [e1, e2]
  refine ⟨?_, ?_⟩
  · refine List.mem_append_right _ (List.mem_map.2 ⟨76, List.mem_range.2 ?_, rfl⟩)
    rw [h77]
    omega
  · show ((lettersHead h H (joinQ cF.blocksInOrder 0 cells tok arr wit ownK jobs O) test carryX item n₁ n₂ b₀
      Vd Rd Kp w).thread.table (.own 76) k m.st.input (m.st.heard.take
        ((lettersHead h H (joinQ cF.blocksInOrder 0 cells tok arr wit ownK jobs O) test carryX item n₁ n₂ b₀
          Vd Rd Kp w).thread.fixed (.own 76)))).2.words = 9
    rw [et, ef]
    exact (switchTable_shape 0 D readers closing pl k m.st.input _ 0 hH hV
      (finishTree_of_fitsL hfit hq)).2

end

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.oldOpenings_at_stand
#print axioms ProofFile.Honest.K12.switchTable_shape
#print axioms ProofFile.Honest.K12.firstOfMap
#print axioms ProofFile.Honest.K12.finishTree_of_fitsL
#print axioms ProofFile.Honest.K12.oldOpeningsAre
#print axioms ProofFile.Honest.K12.oldOpenings_written
#print axioms ProofFile.Honest.K12.rounds_head_L
#print axioms ProofFile.Honest.K12.closingTestOldOpenings_at_joinedScript
