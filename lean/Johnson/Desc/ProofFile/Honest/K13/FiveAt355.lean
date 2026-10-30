-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K13/FiveAt355.lean: kind K13, the members' batching: THE FIVE
STATEMENTS AT THE KIND's BORDER IN THE PROOF FILE's FIRST CHAIN, NUMBER 355 (`PlaysS`, `BehindS`,
`ExchangeS`, `RidesPastS`, `AcceptedS`: Honest/Thread/PaysS.lean), AT THE FRAME's OWN LAYING OF
THAT CHAIN's THREAD (`lettersHead`, Honest/Thread/FirstHead.lean), AT THE WRITTEN FILLER OF THE PILE
(`pileAnyK3`, PileOfAnySize.lean of this folder). Two structures; statements with their proofs:
calls. THE FULL SIZE ALONE, AT THE FORMAT's SECOND HASH FUNCTION ALONE: all under the library's one
hypothesis h (`P5J.AtMgA`).

In what it is general. The prover H, with the type of its index and of its stored randomness; the
book; the Script Q; Said; fall; the list cs of the thread's other clauses; the clause Kp of what a
member's step keeps; the input w. The sender is named by what a search of H.first finds at the
member's place.

WHICH STATEMENT ASKS WHAT, beside h.
  `PlaysS`      which sender is found (hH), at every filler.
  `AcceptedS`   hH at the written filler; a base; b₀ ≤ 355 (`k13_accepted_at_anyK3`,
               AcceptedAtAnyK3.lean of this folder).
  `BehindS`, `RidesPastS`, and of `ExchangeS` the item "pinI": the structure `K13Left`. NOTHING OF
               THE SENDER, THE SCRIPT OR THE BOOK.
  of `ExchangeS` the item "pinW": nothing: no work of the kind's: it holds by the frame's own
               parameters.
  of `ExchangeS` the item "pileOne": b₀ ≤ 355, a base, and the structure `K13Ties`.
`K13Left`, five fields; the structure is filled here at no value of Kp or cs.
  reply    the thread's clause on the reply has begun: b₀ ≤ 355. A number.
  keepsTo  Kp at the kind's place gives `K13KeepsAll` (Johnson/Desc/K13/Honest/KeepsAllM3.lean).
  keepsOf  Kp at the kind's place holds behind the member's accepted step: THE THIRD PART OF
           `BehindS` ITSELF, AS A PREMISE (asked from the thread alone, without what is said).
           What this file has towards it is its core: `K13KeepsAll` holds there, under h alone
           (`k13_keepsAll_behind`): so where Kp at that place is `K13KeepsAll`, keepsTo and keepsOf
           hold.
  stays, none   the clauses of cs in force across the member stay; none begins behind it. At the
           written list `csHead` (Honest/Thread/CsHead.lean) no clause reaches 355: both hold for
           want of a case (`csHead_none_at_355`).
`K13Ties`, three fields; none is shown here at a prover, a Script or a book.
  half     hH at the written filler. At the prover that the maker returns: `k13_half_of_lots`
           (AcceptedAtAnyK3.lean).
  mat      `MatTie` (ExchangeAtM3.lean): ON THE SCRIPT, THE ONE INPUT w AND THE INDEX's READER: the
           Script's cells at w are the matrix that the reader gives. Its exact form:
           `matTie_iff_at_head` (MatTieAtHead.lean).
  coins    `CoinsTie`: ON THE SCRIPT, THE BOOK AND KIND K1's SENDER OF THE INDEX MASKS' MESSAGE: the
           mask entries under the slots that the verifier takes are the coins that the book lends
           the sumcheck's part. From kind K1's record at the opening, the job's plan and ride, and
           that the book is the maker's: `k13_coinsTie_of_five` (AtFullSide/K13/CoinsTieFive.lean).
Further names:
  `k13_keepsAll_behind`, `k13_reply_behind_355`: behind the member's accepted step: what the kind's
    step leaves of the state; the reply is the one asked. Under h (and b₀ ≤ 355) alone. The thread's
    form behind: `k13_form_behind` (FormBehind.lean).
  `k13_rowsTie_anyK3`: `RowsTie` (the filler's rows are the state's in g and psi) at the written
    filler.
  `rowAt₀_of_keepsAll`: the member's step leaves every message's first sample row.
  `pileAnyK3_at_head`, `k13_pile_made_at_355`: the written filler's two arms without a row are not
    taken: the first under h; the second at every stand of the thread in front of the member, at a
    base's ground, where b₀ ≤ 355.
  `k13_five_at_355`: **the five, from h, a base, `K13Left` and `K13Ties`.**

What the five say: each is a premise's form, from "the thread and what is said stand in front of the
member": where the thread stands nowhere they speak of nothing.

What is not claimed. Any field of the two structures at a prover, a Script, a book or a value of Kp.
That h holds at any public files. Anything at number 356, in the other two chains or at the key
file. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K13.AcceptedAtAnyK3
import Johnson.Desc.ProofFile.Honest.K13.FormBehind
import Johnson.Desc.ProofFile.Honest.K13.KindAt355
import Johnson.Desc.ProofFile.Honest.K13.DefaultsIdle
import Johnson.Desc.ProofFile.Honest.K13.SeatedHead
import Johnson.Desc.ProofFile.Honest.K13.SeatedPair
import Johnson.Desc.ProofFile.Honest.Thread.PinForward
import Johnson.Desc.ProofFile.Honest.Thread.CsHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K13
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Chain Strs Place KindName)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.K13.Law (SameAll sampleOf)
open VerifiableInference.Desc.K13.Honest (K13KeepsAll withClaim_keepsAll roundsAhead)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersHead head_keeps head_rides_and head_reply Script WtF
  exchangeAtS_pinI_older)

/-! ## What the kind's step leaves of a message's sample rows -/

/-- The kind's step leaves every message's first sample row. -/
theorem rowAt₀_of_keepsAll {P : VerifiableInference.Desc.K13.Where} {s s' : TS}
    (hk : K13KeepsAll P s s') (o : ℕ) : rowAt₀ s'.st o = rowAt₀ s.st o := by
  have e : sampleOf s'.st o = sampleOf s.st o := hk.1.2.2.2.2.2.2.1.2 o
  refine rowAt₀_same ?_
  have q := congrArg (Option.map fun y : OracleShape × Bool × Array OnBytes.Row ×
    List (OnBytes.Part × ℕ) => y.2.2.1) e
  unfold sampleOf at q
  rw [Option.map_map, Option.map_map] at q
  exact q

/-! ## The written list of the thread's other clauses -/

/-- No clause of the written list reaches the border 355: none is in force across the member, and
none begins behind it. -/
theorem csHead_none_at_355 {W : Type} {ν : Nat} {st : Nat → TS → Prop}
    {R : Nat → Option OnBytes.Model.Forest.Heard → Prop} {c : RiderCl W TS}
    (hc : c ∈ csHead ν st R) : c.hi < 355 + 1 ∧ c.lo ≠ 355 + 1 := by
  rcases (csHead_mem ν st R c).1 hc with
    ((((rfl | rfl | rfl | rfl | rfl | rfl | rfl) | ⟨l, hl, rfl⟩) | ⟨g, hg, rfl⟩) | ⟨g, hg, rfl⟩)
  all_goals (refine ⟨?_, ?_⟩ <;> dsimp only [riderHead, riderAtt] <;> omega)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
  (cs : List (RiderCl (Local W₀ Rc ProofFile.Inst Tr) TS)) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-! ## Behind the member's accepted step: what asks nothing of the sender -/

/-- **Behind the member's accepted step: what the kind's step leaves of the state.** Under h alone.
-/
theorem k13_keepsAll_behind :
    ∀ blk, cF.blocksInOrder[355]? = some blk → ∀ k s m E ds y cols s',
      Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 355 k s m E →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y cols
        s' → K13KeepsAll h.𝔇.P13 s s' := by
  intro blk hb k s m E ds y cols s' hT hS
  obtain ⟨-, t, msg, row, ht, -, rfl, -⟩ :=
    k13_from_step (T := (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread)
      (k13_memberIs_at h) hb hS
  exact withClaim_keepsAll
    (k13_form_front (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) m3_place
      hT.2.2.1).1 ht msg row

/-- **Behind it the reply that the state holds is the one asked**, where the thread's clause on the
reply has begun. -/
theorem k13_reply_behind_355 (hb₀ : b₀ ≤ 355) :
    ∀ blk, cF.blocksInOrder[355]? = some blk → ∀ k s m E ds y cols s',
      Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 355 k s m E →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y cols
        s' → s'.out.reply = some m.st.input.x.asked := by
  intro blk hb k s m E ds y cols s' hT hS
  have hk := k13_keepsAll_behind h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w blk hb k s m E ds y
    cols s' hT hS
  have e : s'.out = s.out := hk.1.2.2.2.2.1
  rw [e]
  exact k13_replyRides_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb₀ k s m E hT

/-! ## The filler's rows are the state's -/

/-- **`RowsTie` AT THE WRITTEN FILLER OF THE PILE**, at a base's ground. -/
theorem k13_rowsTie_anyK3 (Bs : ProofFile.PureBase)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) :
    RowsTie (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) 355 (pileAnyK3 Zp Bs.G₀)
      ProofFile.Inst.asked := by
  have e : pileAnyK3 Zp Bs.G₀ = _ := pileOfAnySize_at h q0Idle Bs
  rw [e]
  exact rowsTie_of_pileIs _ 355 _ _ (k13_pileIs_at_head h Bs hB _)

/-! ## The filler's arms without a row -/

include h in
/-- **Under h the chain is made**: the written filler is the filler over the first chain, at every
ground: the arm "no row where the chain cannot be made" is not taken. -/
theorem pileAnyK3_at_head (G : ProofFile.Ground) :
    pileAnyK3 Zp G = pileAtChain cF Zp (headArmOfSeg cF Zp G) (q0Idle Zp) :=
  pileOfAnySize_of_chain headArmOfSeg q0Idle h.laid.chain G

/-- **AT A STAND OF THE THREAD IN FRONT OF THE MEMBER THE WRITTEN FILLER YIELDS THE PLAN's NUMBER OF
ROWS**, thirteen, at what was heard and any challenge more: so there the arm "no row where one
site's row cannot be made" is not taken either. From h, a base, the thread, and that its clause on
the reply has begun. -/
theorem k13_pile_made_at_355 (hb₀ : b₀ ≤ 355) (Bs : ProofFile.PureBase)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) {k : Coins Bk} {s : TS}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 355 k s m E)
    (d : Fmt.Drawn) :
    (pileAnyK3 Zp Bs.G₀ m.st.input.x (m.st.heard ++ [d])).length = 13 := by
  have q := congrArg List.length
    (k13_rowsTie_anyK3 h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Bs hB k s m E hT
      (k13_replyRides_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb₀ k s m E hT) d)
  rw [List.length_map, List.length_map] at q
  rw [q, k13_count_at h H.first Q _ _ test carryX item n₁ n₂ _ _ _ hT, m3_rows h]

/-! ## What is left -/

/-- **What `BehindS`, `RidesPastS` and the share of `ExchangeS` at "pinI" still ask at 355**: a
number, two sentences on the clause Kp at the kind's place, two on the list cs. -/
structure K13Left : Prop where
  reply : b₀ ≤ 355
  keepsTo : ∀ s s', Kp ⟨1, none, 3, .K13⟩ s s' → K13KeepsAll h.𝔇.P13 s s'
  keepsOf : ∀ blk, cF.blocksInOrder[355]? = some blk → ∀ k s m E ds y cols s',
    Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) Kp w).thread 355 k s m
      E →
    drawsFit blk.rounds ds = true →
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) Kp w).thread.Stepped blk k s
      m E ds y cols s' →
    Kp ⟨1, none, 3, .K13⟩ s s'
  stays : ∀ c ∈ cs, c.lo ≤ 355 → 355 + 1 ≤ c.hi →
    StaysBy (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) Kp w).thread 355 c
  none : ∀ c ∈ cs, c.lo ≠ 355 + 1

/-- **What the share of `ExchangeS` at "pileOne" asks beside**, at the written filler of the pile.
G: the ground at which the filler stands. -/
structure K13Ties (weights : W₀ → Weights) (G : ProofFile.Ground) : Prop where
  half : ∀ blk, cF.blocksInOrder[355]? = some blk →
    (H.first.find? fun g => g.place == blk.place) =
      some (proverSideOfClaimCombination weights (pileAnyK3 Zp G) h.𝔇.P13)
  mat : MatTie (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) Kp w) weights
    (pileAnyK3 Zp G) h.𝔇.P13 (k13ReaderAt h)
  coins : CoinsTie (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) Kp w) 355
    weights (pileAnyK3 Zp G) h.𝔇.P13 (k13ReaderAt h)

variable {weights : W₀ → Weights} {G : ProofFile.Ground}

/-! ## The five -/

/-- **`PlaysS` AT 355**: from which sender is found, at every filler of the pile. -/
theorem k13_playsS_at_355 (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    {pile : PileOf ProofFile.Inst}
    (hH : ∀ blk, cF.blocksInOrder[355]? = some blk →
      (H.first.find? fun g => g.place == blk.place) = some (proverSideOfClaimCombination weights pile h.𝔇.P13)) :
    PlaysS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 355 :=
  playsS_of _ Said (k13_thread_plays (k13_atK13_at h H.first Q _ _ test carryX item n₁ n₂ _ _ _ hH))

/-- **`BehindS` AT 355.** It asks nothing of the sender. -/
theorem k13_behindS_at_355 (L : K13Left h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) :
    BehindS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) Kp w).thread Said 355 :=
  behindS_of_keeps_and _ Said
    (head_rides_and h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w)
    (fun blk hb k s m E ds y cols s' hA hd hS =>
      ⟨k13_form_behind h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) Kp w blk hb k s m E ds y
          cols s' hA.1 hS,
        (head_keeps h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) Kp w m3_place s s').2
          (L.keepsOf blk hb k s m E ds y cols s' hA.1 hd hS)⟩)
    (fun blk hb k s m E ds y cols s' hA _ hS _ =>
      k13_reply_behind_355 h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) Kp w L.reply blk hb k
        s m E ds y cols s' hA.1 hS)
    L.stays (fun c hc e => absurd e (L.none c hc))

/-- **The share of `ExchangeS` at the item "pinI"**: the pin of the index masks' message, which is
open in front of the member and owed again behind it. It asks nothing of the sender. -/
theorem k13_pinI_at_355 (L : K13Left h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) :
    ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) Kp w).thread Said
      355 Item.pinI :=
  exchangeAtS_pinI_older h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) Kp w Said
    (fun _ s _ _ s' _ hK o q hq => by
      rw [rowAt₀_of_keepsAll (L.keepsTo s s'
        ((head_keeps h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) Kp w m3_place s s').1 hK)) o]
      exact hq)
    m3_pinI_open (k13_behindS_at_355 h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w L Said)

/-- The share at the item "pinW". No work of the kind's: at the frame's own laying of the thread
that item holds of the thread's witness at every state (`m3_pinW_at`, FromThreadAt.lean). -/
theorem k13_pinW_at_355 (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) :
    ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 355
      Item.pinW :=
  exchangeAtS_of _ Said ((exchangeAt_iff
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 355 Item.pinW).1
    (k13_pinW_at h H.first Q _ _ test carryX item n₁ n₂ _ _ _ 355))

/-- **The share at the item "pileOne"**: the one row that the batching leaves is true of the
thread's witness. THE ONE STATEMENT AT THIS BORDER THAT READS WHAT THE SENDER SENDS. hG: the ground
is a base's. -/
theorem k13_pileOne_at_355 (hb₀ : b₀ ≤ 355)
    (T : K13Ties h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w weights G)
    {Bs : ProofFile.PureBase} (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)
    (hG : Bs.G₀ = G) (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) :
    ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) Kp w).thread Said
      355 Item.pileOne := by
  subst hG
  exact exchangeAtS_of _ Said ((exchangeAt_iff
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) Kp w).thread 355 Item.pileOne).1
    (k13_pileOne_at h H.first Q _ _ test carryX item n₁ n₂ _ _ _ T.half T.mat T.coins
      (k13_rowsTie_anyK3 h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) Kp w Bs hB)
      (k13_replyRides_head h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) Kp w hb₀)))

/-- **`ExchangeS` AT 355**: the three items that the row owes: "pileOne", "pinW", "pinI". -/
theorem k13_exchangeS_at_355 (L : K13Left h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w)
    (T : K13Ties h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w weights G)
    {Bs : ProofFile.PureBase} (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)
    (hG : Bs.G₀ = G) (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) :
    ExchangeS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs)
      Kp w).thread Said 355 := by
  refine (exchangeS_iff _ Said).2 fun i hi => ?_
  have hi' : i ∈ [Item.pileOne, Item.pinW, Item.pinI] := by
    rw [← k13_owes (L := lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) Kp w)
      m3_place]
    exact hi
  rcases List.mem_cons.1 hi' with rfl | h2
  · exact k13_pileOne_at_355 h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w L.reply T hB hG Said
  rcases List.mem_cons.1 h2 with rfl | h3
  · exact k13_pinW_at_355 h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) Kp w Said
  obtain rfl := List.mem_singleton.1 h3
  exact k13_pinI_at_355 h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w L Said

/-- **`RidesPastS` AT 355**: "unmarked" alone goes past the member, and what the step keeps says
outright that the state behind bears no mark. It asks nothing of the sender. -/
theorem k13_ridesPastS_at_355 (L : K13Left h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) :
    RidesPastS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs)
      Kp w).thread Said 355 :=
  ridesPastS_of _ Said
    (k13_thread_rides_at h H.first Q _ _ test carryX item n₁ n₂ _ _ _ fun _ s _ _ s' _ hK =>
      (L.keepsTo s s'
        ((head_keeps h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) Kp w m3_place s s').1
          hK)).1.1)

/-- **THE FIVE STATEMENTS AT 355**, at every Said and every fall: from h, a base whose ground is G,
and what is left. -/
theorem k13_five_at_355 (L : K13Left h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w)
    (T : K13Ties h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w weights G)
    {Bs : ProofFile.PureBase} (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)
    (hG : Bs.G₀ = G) (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (fall : Nat → TS → List Fmt.Drawn → Option String) :
    PlaysS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) Kp w).thread Said 355 ∧
      BehindS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) Kp w).thread Said 355 ∧
      ExchangeS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs)
        Kp w).thread Said 355 ∧
      RidesPastS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) Kp w).thread Said
        355 ∧
      AcceptedS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) Kp w).thread Said fall
        355 :=
  ⟨k13_playsS_at_355 h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) Kp w Said T.half,
    k13_behindS_at_355 h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w L Said,
    k13_exchangeS_at_355 h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w L T hB hG Said,
    k13_ridesPastS_at_355 h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w L Said,
    k13_accepted_at_anyK3 h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) Kp w Said L.reply Bs hB
      (by rw [hG]; exact T.half) fall⟩

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.rowAt₀_of_keepsAll
#print axioms ProofFile.Honest.K13.csHead_none_at_355
#print axioms ProofFile.Honest.K13.k13_keepsAll_behind
#print axioms ProofFile.Honest.K13.k13_reply_behind_355
#print axioms ProofFile.Honest.K13.k13_rowsTie_anyK3
#print axioms ProofFile.Honest.K13.pileAnyK3_at_head
#print axioms ProofFile.Honest.K13.k13_pile_made_at_355
#print axioms ProofFile.Honest.K13.k13_playsS_at_355
#print axioms ProofFile.Honest.K13.k13_behindS_at_355
#print axioms ProofFile.Honest.K13.k13_pinI_at_355
#print axioms ProofFile.Honest.K13.k13_pinW_at_355
#print axioms ProofFile.Honest.K13.k13_pileOne_at_355
#print axioms ProofFile.Honest.K13.k13_exchangeS_at_355
#print axioms ProofFile.Honest.K13.k13_ridesPastS_at_355
#print axioms ProofFile.Honest.K13.k13_five_at_355
