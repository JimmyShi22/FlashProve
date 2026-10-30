-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/LotsLaid.lean: the proximity test (the kind K12) in the frame for
the honest side: WHAT `Script.ofLots` (Honest/Thread/ScriptLots.lean) GIVES AT K12's LOTS. In its
Lean it is modelled on Honest/K1/LotsLaid.lean, of other authors. One definition, twelve theorems.

  `fenceB`, `stageMsg_isSome`, `testMsgTxt_isSome`   when does a message's text return a value: a
                 Boolean that mentions neither switch, tenant nor entry (the frame lends the second
                 part its coins, and ok accepts), and with it a test on public numbers, the fence.
                 Hence: at each entry within the fence, or at no entry
  `mem_testMsgLots`, `mem_testPl`   membership of a switch's two lots in `testMsgLots`, of its two
                 lots of pads in `testPl`
  `test_msgs_of_lots`, `test_pads_of_lots`, `test_trees_of_lots`   THE TIES, under hin: `OwnMsgs`
                 and `OwnPads` (first and second tenant) at our texts; `OwnTrees` under htl
  `hin_test_msgs_of_agree`, `hin_test_pads_of_agree`   hin, from two simpler hypotheses on the whole
                 laid list
  `test_fx_fits`, `seedRound_le_LFull`   arithmetic toward the frame's tests on fixedMsg and fixed
  `fenceB_bite_LFull`   a control on the fence

By what. Each tie calls one law (the tie on pads calls its law twice, once a tenant):
`ofLots_ownMsgs`, `ofLots_ownPads`, `ofLots_ownTrees`, all three the frame's authors'. At those
authors' own joined Script (`joinQ`, Honest/Thread/Join.lean)
the ties are better had from their `join_msgs_other`, `join_pads_other`,
`join_trees_other`, which call the same three laws under one hypothesis and need from a sender only
the two membership laws here and `testTl_at`.

Limits.
- What ScriptLots.lean's head says a law over coins has to mind holds for this file. The three ties
  tie a text to the laid Script (`Script.ofLots`), not to a run. No statement here is a measure over
  coins or ties a text to a run. `runs_L_at_laid` (AtFullSide/K12/RunsAtLaidL.lean) is not imported
  here and occurs in no statement here.
  
- Only for a job with `J.fresh` = some …: ScriptLots.lean's first limit.
- Nothing is laid and no list is exhibited. Membership in ml or pl, and agreement there, come in as
  the hypothesis hin; this file discharges neither.
- FOUR PARAMETERS ARE INDEPENDENT HERE THAT ARE MEANT TO BE LINKED: bs and front belong to the
  laying, n₀ and t₀ to our lots. Intended: n₀ = front + roundsTo bs b, t₀ = treesTo bs b. Away from
  that n₀ the field fixed in `test_trees_of_lots` is no bound on the challenges that `testTbl`
  reads.
- VACUITY. `OwnMsgs` and `OwnPads` speak only of entries at which a text returns a value. If the
  frame lends nothing, or ok rejects, none of our texts returns one, and the ties then assert
  nothing. No theorem here exhibits coins, an input and challenges at which that Boolean is true. At
  a job of fewer than two stages no τ lies below length - 1, and the ties on messages and on pads
  say nothing. The two pads' texts have their counterparts of `testMsgTxt_isSome` in
  LotsAnswer.lean.
- Owed still: that this Boolean depends on public data only (what is had of that, and for which
  texts it is still owed: ScriptLots.lean's limit on «answers or not»; LotsAnswer.lean); that each
  text depends on a run's coins only through the shares it reads.
- `test_trees_of_lots` takes its count of trees from blk; nothing compares that count with the job's
  number of switches. The law that it calls is true of any lots whatever.
- `fenceB` has five arms; the control tries one.
- It moves no count. Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.ScriptLotsPads
import Johnson.Desc.ProofFile.Honest.K12.ScriptLotsNumbersL

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Slice Cb
open VerifiableInference.Desc (Block)
open Johnson.Prover.Link (PS)
open ProofFile.Honest.FirstThread

variable {Bk : ProverCoinCounts} {W X S Cl Cells Tok : Type}

/-- **The public fence of message (τ, t)'s entries**: `stageMsg`'s own four conditions, as a test.
-/
def fenceB (s : Fmt.M1.Stage) (last : Bool) (t : ℕ) (mask : Bool) (b q : ℕ) : Bool :=
  match t, mask with
  | 0, false => decide (b < 2 ^ s.k ∧ q < s.C.l)
  | 0, true => decide (b < 2 ^ s.h ∧ q < s.Z.l)
  | 1, true => decide ((if last then b = 0 else b < 2 ^ s.h) ∧ q < s.Z.l)
  | 1, false => decide (last = true ∧ b = 0 ∧ q < s.C.l)
  | _, _ => false

/-- `stageMsg` answers just inside the fence, whatever the state. -/
theorem stageMsg_isSome (s : Fmt.M1.Stage) (last : Bool) (Q : PS) (t : ℕ) (mask : Bool) (b q : ℕ) :
    (stageMsg s last Q t mask b q).isSome = fenceB s last t mask b q := by
  have key : ∀ (p : Prop) [Decidable p] (a : GE),
      (if p then some a else none).isSome = decide p := fun p _ a => by
    by_cases h : p <;> simp [h]
  match t, mask with
  | 0, false => exact key _ _
  | 0, true => exact key _ _
  | 1, true => exact key _ _
  | 1, false => exact key _ _
  | _ + 2, false => rfl
  | _ + 2, true => rfl

/-- **When a message's text returns a value**: a Boolean free of τ, t and the entry, and the fence.
-/
theorem testMsgTxt_isSome (ch : ℕ) (J : TestJob W X) (own₀ : X) (n₀ : ℕ)
    (ok : W → List Fmt.Drawn → (ℕ → Stretch) → Bool) (τ t : ℕ) (k : Coins Bk) (w : W)
    (h : List Fmt.Drawn) (mask : Bool) (b q : ℕ) :
    (testMsgTxt ch J own₀ n₀ ok τ t k w h mask b q).isSome =
      (((handedRest ch J k).any fun c => ok w (h.take n₀) (restCoins J c).mem) &&
        fenceB (J.p.nums.stages.getD (τ + 1) default) (τ + 2 == J.p.nums.stages.length) t mask b
          q) := by
  unfold testMsgTxt
  cases handedRest ch J k with
  | none => rfl
  | some c =>
    show (if ok w (h.take n₀) (restCoins J c).mem = true then _ else none).isSome =
      (ok w (h.take n₀) (restCoins J c).mem && _)
    cases ok w (h.take n₀) (restCoins J c).mem with
    | false => rfl
    | true =>
      rw [if_pos rfl, Bool.true_and]
      exact stageMsg_isSome _ _ _ _ _ _ _

/-- A switch's two lots lie in the list. -/
theorem mem_testMsgLots (ch : ℕ) (J : TestJob W X) (own₀ : X) (n₀ t₀ : ℕ) (arr : ℕ → ℕ → ℕ)
    (ok : W → List Fmt.Drawn → (ℕ → Stretch) → Bool) {τ t : ℕ} (hτ : τ < J.p.nums.stages.length - 1)
    (ht : t < 2) :
    (⟨arr (t₀ + τ) t, n₀ + seedRound J.p.nums.stages τ, testMsgTxt ch J own₀ n₀ ok τ t⟩ : MsgLot Bk
      W) ∈
      testMsgLots ch J own₀ n₀ t₀ arr ok := by
  unfold testMsgLots
  refine List.mem_flatMap.2 ⟨τ, List.mem_range.2 hτ, List.mem_map.2 ⟨t, ?_, rfl⟩⟩
  rcases t with _ | _ | t
  · simp
  · simp
  · omega

/-- Membership of a switch's two lots of pads in `testPl`. -/
theorem mem_testPl (ch : ℕ) (J : TestJob W X) (codes : OnBytes.Codes)
    (sh sh₁ : ℕ → OnBytes.OracleShape) (t₀ : ℕ) {τ : ℕ} (hτ : τ < J.p.nums.stages.length - 1) :
    (⟨t₀ + τ, 0, fun k _ => testPadTxt ch J codes sh τ k⟩ : PadLot Bk W) ∈ testPl ch J codes sh sh₁
      t₀ ∧
      (⟨t₀ + τ, 1, fun k _ => testPadTxtB ch J codes sh₁ τ k⟩ : PadLot Bk W) ∈ testPl ch J codes sh
        sh₁ t₀ :=
  ⟨List.mem_append_left _ (List.mem_map.2 ⟨τ, List.mem_range.2 hτ, rfl⟩),
    List.mem_append_right _ (List.mem_map.2 ⟨τ, List.mem_range.2 hτ, rfl⟩)⟩

/-- **THE TIE ON MESSAGES**, at a Script built by `Script.ofLots`, under hin. -/
theorem test_msgs_of_lots (bs : List (Block S Cl)) (front : ℕ) (cells : W → Cells) (tok : W → Tok)
    (pl : List (PadLot Bk W)) (tl : ℕ → TreeLot Bk W) (ml : List (MsgLot Bk W)) (ch : ℕ)
    (J : TestJob W X) (own₀ : X) (n₀ t₀ : ℕ) (arr : ℕ → ℕ → ℕ)
    (ok : W → List Fmt.Drawn → (ℕ → Stretch) → Bool)
    (hin : ∀ L ∈ testMsgLots ch J own₀ n₀ t₀ arr ok, L ∈ ml ∧ LotsAgree ml L) (Vd : W → Prop)
    (N : ℕ) :
    ∀ τ, τ < J.p.nums.stages.length - 1 → ∀ t, t < 2 →
      OwnMsgs (Script.ofLots bs front cells tok pl tl ml) Vd N (arr (t₀ + τ) t)
        (n₀ + seedRound J.p.nums.stages τ) (testMsgTxt ch J own₀ n₀ ok τ t) := by
  intro τ hτ t ht
  have hL := hin _ (mem_testMsgLots ch J own₀ n₀ t₀ arr ok hτ ht)
  exact ofLots_ownMsgs bs front cells tok pl tl ml hL.1 hL.2 Vd N

/-- **THE TIE ON PADS**, both tenants'. -/
theorem test_pads_of_lots (bs : List (Block S Cl)) (front : ℕ) (cells : W → Cells) (tok : W → Tok)
    (pl : List (PadLot Bk W)) (tl : ℕ → TreeLot Bk W) (ml : List (MsgLot Bk W)) (ch : ℕ)
    (J : TestJob W X) (codes : OnBytes.Codes) (sh sh₁ : ℕ → OnBytes.OracleShape) (t₀ : ℕ)
    (hin : ∀ L ∈ testPl ch J codes sh sh₁ t₀, L ∈ pl ∧ PadLotsAgree pl L) (Vd : W → Prop) :
    ∀ τ, τ < J.p.nums.stages.length - 1 →
      OwnPads (Script.ofLots bs front cells tok pl tl ml) Vd (t₀ + τ) 0 (fun k _ => testPadTxt ch J
        codes sh τ k) ∧
      OwnPads (Script.ofLots bs front cells tok pl tl ml) Vd (t₀ + τ) 1 (fun k _ => testPadTxtB ch J
        codes sh₁ τ k) := by
  intro τ hτ
  have h0 := hin ⟨t₀ + τ, 0, fun k _ => testPadTxt ch J codes sh τ k⟩
    (List.mem_append_left _ (List.mem_map.2 ⟨τ, List.mem_range.2 hτ, rfl⟩))
  have h1 := hin ⟨t₀ + τ, 1, fun k _ => testPadTxtB ch J codes sh₁ τ k⟩
    (List.mem_append_right _ (List.mem_map.2 ⟨τ, List.mem_range.2 hτ, rfl⟩))
  exact ⟨ofLots_ownPads bs front cells tok pl tl ml h0.1 h0.2 Vd,
    ofLots_ownPads bs front cells tok pl tl ml h1.1 h1.2 Vd⟩

/-- hin for the messages, from two hypotheses on the whole laid list: it contains `testMsgLots`, and
`MsgsAgree` holds of it. -/
theorem hin_test_msgs_of_agree {ch : ℕ} {J : TestJob W X} {own₀ : X} {n₀ t₀ : ℕ} {arr : ℕ → ℕ → ℕ}
    {ok : W → List Fmt.Drawn → (ℕ → Stretch) → Bool} {ml : List (MsgLot Bk W)}
    (hsub : ∀ L ∈ testMsgLots ch J own₀ n₀ t₀ arr ok, L ∈ ml) (hag : MsgsAgree ml) :
    ∀ L ∈ testMsgLots ch J own₀ n₀ t₀ arr ok, L ∈ ml ∧ LotsAgree ml L :=
  fun L hL => ⟨hsub L hL, hag L (hsub L hL)⟩

/-- hin for the pads, likewise: the laid list contains `testPl`, and `PadsAgree` holds of it. -/
theorem hin_test_pads_of_agree {ch : ℕ} {J : TestJob W X} {codes : OnBytes.Codes}
    {sh sh₁ : ℕ → OnBytes.OracleShape} {t₀ : ℕ} {pl : List (PadLot Bk W)}
    (hsub : ∀ L ∈ testPl ch J codes sh sh₁ t₀, L ∈ pl) (hag : PadsAgree pl) :
    ∀ L ∈ testPl ch J codes sh sh₁ t₀, L ∈ pl ∧ PadLotsAgree pl L :=
  fun L hL => ⟨hsub L hL, hag L (hsub L hL)⟩

/-- **THE TIE ON TREES**, under hbs, hfr, htab, hfix (four fields of the thread T are the laying's)
and htl (the laying's lot at b is ours). -/
theorem test_trees_of_lots {V Pb : Type} (bs : List (Block S Cl)) (front : ℕ) (cells : W → Cells)
    (tok : W → Tok) (pl : List (PadLot Bk W)) (tl : ℕ → TreeLot Bk W) (ml : List (MsgLot Bk W))
    (T : Thread Bk S Cl V W X Pb) (hbs : T.bs = bs) (hfr : T.front = front)
    (htab : T.table = (Script.ofLots bs front cells tok pl tl ml).table)
    (hfix : T.fixed = (Script.ofLots bs front cells tok pl tl ml).fixed) (ch : ℕ) (J : TestJob W X)
    (own₀ : X) (n₀ : ℕ) (ok : W → List Fmt.Drawn → (ℕ → Stretch) → Bool) {b : ℕ} {blk : Block S Cl}
    (hblk : bs[b]? = some blk) (htl : tl b = testTreeLot ch J own₀ n₀ ok) :
    OwnTrees T b (blk.oracles.flatMap id).length (testTbl ch J own₀ n₀ ok) (seedRound
      J.p.nums.stages) := by
  have h := ofLots_ownTrees bs front cells tok pl tl ml T hbs hfr htab hfix hblk
  rw [htl] at h
  exact h

/-- Arithmetic on `roundsTo`: if the sub-protocol at b has no fewer rounds than `seedRound stages
τ`, then front + roundsTo bs b + that number does not pass front + roundsTo bs (b + 1). Of our
definitions it mentions `seedRound` alone. hr is also the shape of `ofLots_hfix`'s premise hoff. -/
theorem test_fx_fits (bs : List (Block S Cl)) (front b : ℕ) {blk : Block S Cl}
    (hblk : bs[b]? = some blk) (stages : List Fmt.M1.Stage) (τ : ℕ)
    (hr : seedRound stages τ ≤ blk.rounds.length) :
    front + roundsTo bs b + seedRound stages τ ≤ front + roundsTo bs (b + 1) := by
  rw [roundsTo_succ hblk]
  omega

/-- At the written record each sending round's number is at most 33. 33 is how many lists of oracle
messages the record has (`oracles_len_LFull`); nothing here counts the rounds of a sub-protocol. -/
theorem seedRound_le_LFull : ∀ τ < 5, seedRound H2K.Member.piLFull.nums.stages τ ≤ 33 := by
  decide +kernel

/-- A control on the fence: at the written record's second stage, the first tenant's main rows: row
15, place 262143 lies inside; row 16 and place 262144 lie outside. -/
theorem fenceB_bite_LFull :
    fenceB (H2K.Member.piLFull.nums.stages.getD 1 default) false 0 false 15 262143 = true ∧
    fenceB (H2K.Member.piLFull.nums.stages.getD 1 default) false 0 false 16 0 = false ∧
    fenceB (H2K.Member.piLFull.nums.stages.getD 1 default) false 0 false 0 262144 = false := by
  decide +kernel

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.fenceB
#print axioms ProofFile.Honest.K12.stageMsg_isSome
#print axioms ProofFile.Honest.K12.testMsgTxt_isSome
#print axioms ProofFile.Honest.K12.mem_testMsgLots
#print axioms ProofFile.Honest.K12.mem_testPl
#print axioms ProofFile.Honest.K12.test_msgs_of_lots
#print axioms ProofFile.Honest.K12.test_pads_of_lots
#print axioms ProofFile.Honest.K12.hin_test_msgs_of_agree
#print axioms ProofFile.Honest.K12.hin_test_pads_of_agree
#print axioms ProofFile.Honest.K12.test_trees_of_lots
#print axioms ProofFile.Honest.K12.test_fx_fits
#print axioms ProofFile.Honest.K12.seedRound_le_LFull
#print axioms ProofFile.Honest.K12.fenceB_bite_LFull
