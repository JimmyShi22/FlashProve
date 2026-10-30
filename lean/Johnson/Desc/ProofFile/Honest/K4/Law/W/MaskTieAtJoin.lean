-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/MaskTieAtJoin.lean: CONDITIONAL. Four
statements with their proofs; no definition.

What turned against the first form. Each statement takes what its proof spends, as a
proposition and not as a test that says true. "Agree" is hm, `MsgsAgree` of the joined list of
messages' lots (it was `agreeB … = true`, of which the half on pads was idle). "Owned" is, in
`k4MaskTie_at_joinQ`, hown, the one instance that is spent (it was `ownedB … = true` at a list of
seats that holds K4's seat); in `k4MaskTie_at_joinQ_k1`, where it was idle, it has fallen. New:
`k4MaskTie_at_joinQ_fit` and `k4MaskTie_at_joinQ_k1_fit`. The ends of the two elder statements are
unturned.

What is here. THE TIE ON THE MASK ROW OF THE MEMBER OF THE FEED-FORWARD LAYERS' OWN ROUNDS
(sub-protocol K4), `K4MaskTieAt` (Law/ScriptAt.lean), AT THE JOINED SCRIPT `joinQ`
(Honest/Thread/Join.lean, of other writers; no part of the library yet) AND AT THE BOOK A.B THAT
`onlineProverFromPublicFiles` RETURNS. `k4MaskTie_at_joinQ`: at every group g: hown hands a lot Ls of the joined list
that bears the message's number: SO NO LOT AND NO SENDER IS NAMED; hm gives that the other lots
agree with it; the lock at A.B comes of `k4Book_at_atPure` (Law/W/BookAtPure.lean), at the owner
and start row that the maker finds (hrow); then `k4MaskOwn_ofLots` (Law/W/MaskCovers.lean) with no
fence on the input and none on the challenges, and `k4MaskTie_of_ownMsgsG`
(Law/W/MaskTieOfLot.lean). hA and hE speak of every lot of the list that bears the number. Where no
lot of the list bears it, hown is false and the statement says nothing.
`k4MaskTie_at_joinQ_fit`: the same from the one premise F, `JoinFit` (Honest/Thread/JoinFit.lean,
of other writers; no part of the library yet), at a list of seats that holds K4's seat (hs): of F's
seven fields two are spent, five are idle there: see its docstring.
`k4MaskTie_at_joinQ_k1`: the lot is the shared sending's (K1's) for message n of a job y of the
list: hA is had from hC, the book's count at that one job (`msgTxt_answers`,
Honest/K1/LotsLaid.lean); hn and hE stay. `k4MaskTie_at_joinQ_k1_fit`: the same from F: one field,
msgs, is spent, six are idle there, and the list of seats is a free letter.
The types of hm and hown are those of `JoinFit.msgs` and of the first half of `JoinFit.owned` at
K4's seat (`k4MaskNum` unfolded), and of what `agree_of_test` and `owned_gives` (Join.lean) hand.

Not shown here. THAT hE HOLDS OF ANY SENDER's TEXT; that hA holds beside K1's; that hn holds at any
n; that hC holds at A.B; that hm or hown holds at any list; that any list is fit; that K4's seat is
among any list of seats; that `onlineProverFromPublicFiles` returns; that the thread stands anywhere: where it stands at
no state all four are empty. n, y and g are letters: that K1 sends the message at g = 0 alone is
not said here. Each statement is an equation at the stand's own coins, entry by entry: nothing is
said on how an element of the coins is sampled. The full size and the format's second hash function alone.
The limits of the files named hold here too. Nothing on soundness, on completeness or on any other
property.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.MaskTieOfLot
import Johnson.Desc.ProofFile.Honest.K4.Law.W.BookAtPure
import Johnson.Desc.ProofFile.Honest.Thread.JoinFit

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no standing table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Desc.First.K4.Rt (k4Takes)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs Block)
open VerifiableInference.Desc.Sound (MsgT seatTab)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead OwnMsgs MsgLot Others joinQ joinMl joinPl joinTl
  MsgsAgree JoinFit)
open ProofFile.Honest.K1 (SendJob PlaceIn seatAtMember msgTxt msgTxt_answers k1MsgLotsAt mem_k1MsgLots
  dueR)
open ProofFile.Honest.K4.SeatedHead (LaidK4)
open ProofFile.Honest.K4.Lot (k4MaskLotG k4MaskNum k4MaskSeat k4PubG)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

variable {W₀ Rc Ky Tr X₀ X' Xi Xj : Type} {Wa Rca Tra Xa₀ Xa : Type}
  {P : OnlineProverParts Wa Rca Tra Xa₀ Xa} {A : OnlineProverWithDescription Wa Rca Tra Xa₀ Xa}

variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh)
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X') (front : ℕ)
  (cellsQ : Local W₀ Rc ProofFile.Inst Tr → CellsM OnBytes.Flat.numsFull)
  (tok : Local W₀ Rc ProofFile.Inst Tr → P5J.At.Tok) (wit : Local W₀ Rc ProofFile.Inst Tr → PlaceIn Xi)
  (own₀ : Xj) (jobs : List (ℕ × SendJob (PlaceIn Xi) Xj))
  (O : Others A.B (Local W₀ Rc ProofFile.Inst Tr))
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)

/-- CONDITIONAL on h, hAP, hm, Lh, hown, hQ, hrow, hA, hE, hL and hT. **THE TIE ON THE MASK ROW
AT THE JOINED SCRIPT AND THE BOOK A.B, AT EVERY GROUP.** hown ("owned", the one instance that is
spent) hands the lot and its number; hm ("agree") that the other lots agree with it. -/
theorem k4MaskTie_at_joinQ (hAP : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (hm : MsgsAgree (joinMl cF.blocksInOrder front (P5J.At.arr Zp) wit own₀ jobs O))
    {k m g : ℕ} {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀)
    (hown : ∃ Ls ∈ joinMl cF.blocksInOrder front (P5J.At.arr Zp) wit own₀ jobs O,
      Ls.n = k4MaskNum Zp (2 * g))
    {cells : Tr → Cells} {weights : W₀ → Weights}
    {tokens : ProofFile.Inst → Array Nat} {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Qp : K4Pub}
    (hQ : k4PubOf Zp x.2 = some Qp) {row : MsgAt}
    (hrow : ownerOf maskRowRun cF.blocksInOrder Zp.made.proof.1
      ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder.flatMap (·.rounds))
      s!"link {2 * g}, moment 0" isMaskRowMsg = some row)
    (hA : ∀ Ls ∈ joinMl cF.blocksInOrder front (P5J.At.arr Zp) wit own₀ jobs O,
      Ls.n = k4MaskNum Zp (2 * g) → ∀ k w (hd : List Fmt.Drawn) ν,
      Forest.elems (P5J.At.X Zp).y.fo ≤ ν →
      ν + 1 < Forest.elems (P5J.At.X Zp).y.fo + k4Takes Qp.P Qp.hp Qp.g →
      (Ls.txt k w (hd.take Ls.fx) true 0 ν).isSome = true)
    {L : ℕ}
    (hE : ∀ Ls ∈ joinMl cF.blocksInOrder front (P5J.At.arr Zp) wit own₀ jobs O,
      Ls.n = k4MaskNum Zp (2 * g) → ∀ k w hd ν y', ν < L → Ls.txt k w hd true 0 ν = some y' →
      (k.look 0 row.owner).2.eAt (row.base.e + ν) = .ok y')
    (hL : Forest.elems (P5J.At.X Zp).y.fo + k4Takes Qp.P Qp.hp Qp.g ≤ L + 1)
    {c : Coins A.B} {s : TS} {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E : Env}
    (hT : Thr (lettersHead h H (joinQ cF.blocksInOrder front cellsQ tok (P5J.At.arr Zp) wit own₀ jobs O)
      test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k c s mm E) :
    K4MaskTieAt (lettersHead h H (joinQ cF.blocksInOrder front cellsQ tok (P5J.At.arr Zp) wit own₀ jobs O)
      test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread cells weights tokens look Qp
      (h.𝔇.N.sent m 0) (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms) c s mm := by
  obtain ⟨Ls, hLs, hn⟩ := hown
  have hP := k4PubG_of Lh hQ
  obtain ⟨-, -, row', idx, hr', -, J, -⟩ := k4Book_at_atPure h hAP (Rc := Rc) (X := X') cells
    weights tokens (look Qp) g Lh.lt Qp hP
  obtain rfl : row' = row := Option.some.inj (hr'.symm.trans hrow)
  have Ow := k4MaskOwn_ofLots (X := X') (cells := cells) (weights := weights) (tokens := tokens)
    (look := look) cF.blocksInOrder front cellsQ tok (joinPl cF.blocksInOrder jobs O) (joinTl wit own₀ jobs O)
    (joinMl cF.blocksInOrder front (P5J.At.arr Zp) wit own₀ jobs O) hLs (hm Ls hLs) hP J
    hn (Vq := fun _ => True) (N := 0) (fun k w hd ν _ _ h1 h2 => hA Ls hLs hn k w hd ν h1 h2)
    (hE Ls hLs hn) hL
  exact k4MaskTie_of_ownMsgsG h H (joinQ cF.blocksInOrder front cellsQ tok (P5J.At.arr Zp) wit own₀ jobs O)
    test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Lh hQ Ow hT trivial (Nat.zero_le _)

/-- CONDITIONAL on h, hAP, F, Lh, hs, hQ, hrow, hA, hE, hL and hT. **THE SAME AT A FIT LIST WHOSE
LIST OF SEATS HOLDS K4's SEAT.** Of F's seven fields two are spent: msgs, and of owned the half on
the message's lot, at K4's seat alone. The half of owned on the pad's lot and the five fields pads,
nums, trees, found and fits are idle here: the statement above asks less. -/
theorem k4MaskTie_at_joinQ_fit (hAP : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    {seats : List (ℕ × ℕ)}
    (F : JoinFit cF.blocksInOrder front (P5J.At.arr Zp) seats wit own₀ jobs O)
    {k m g : ℕ} {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀)
    (hs : k4MaskSeat Zp (2 * g) ∈ seats) {cells : Tr → Cells} {weights : W₀ → Weights}
    {tokens : ProofFile.Inst → Array Nat} {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Qp : K4Pub}
    (hQ : k4PubOf Zp x.2 = some Qp) {row : MsgAt}
    (hrow : ownerOf maskRowRun cF.blocksInOrder Zp.made.proof.1
      ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder.flatMap (·.rounds))
      s!"link {2 * g}, moment 0" isMaskRowMsg = some row)
    (hA : ∀ Ls ∈ joinMl cF.blocksInOrder front (P5J.At.arr Zp) wit own₀ jobs O,
      Ls.n = k4MaskNum Zp (2 * g) → ∀ k w (hd : List Fmt.Drawn) ν,
      Forest.elems (P5J.At.X Zp).y.fo ≤ ν →
      ν + 1 < Forest.elems (P5J.At.X Zp).y.fo + k4Takes Qp.P Qp.hp Qp.g →
      (Ls.txt k w (hd.take Ls.fx) true 0 ν).isSome = true)
    {L : ℕ}
    (hE : ∀ Ls ∈ joinMl cF.blocksInOrder front (P5J.At.arr Zp) wit own₀ jobs O,
      Ls.n = k4MaskNum Zp (2 * g) → ∀ k w hd ν y', ν < L → Ls.txt k w hd true 0 ν = some y' →
      (k.look 0 row.owner).2.eAt (row.base.e + ν) = .ok y')
    (hL : Forest.elems (P5J.At.X Zp).y.fo + k4Takes Qp.P Qp.hp Qp.g ≤ L + 1)
    {c : Coins A.B} {s : TS} {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E : Env}
    (hT : Thr (lettersHead h H (joinQ cF.blocksInOrder front cellsQ tok (P5J.At.arr Zp) wit own₀ jobs O)
      test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k c s mm E) :
    K4MaskTieAt (lettersHead h H (joinQ cF.blocksInOrder front cellsQ tok (P5J.At.arr Zp) wit own₀ jobs O)
      test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread cells weights tokens look Qp
      (h.𝔇.N.sent m 0) (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms) c s mm :=
  k4MaskTie_at_joinQ h H front cellsQ tok wit own₀ jobs O test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ hAP
    F.msgs Lh (F.owned _ hs).1 hQ hrow hA hE hL hT

/-- CONDITIONAL on h, hAP, hm, hx, hlt, hn, hC, Lh, hQ, hrow, hE, hL and hT. **THE SAME AT K1's LOT
FOR MESSAGE n OF THE JOB y.** hC: the book's count at that one job is the part's due. -/
theorem k4MaskTie_at_joinQ_k1 (hAP : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (hm : MsgsAgree (joinMl cF.blocksInOrder front (P5J.At.arr Zp) wit own₀ jobs O))
    {y : ℕ × SendJob (PlaceIn Xi) Xj} (hx : y ∈ jobs) {n : ℕ} (hlt : n < y.2.P.sent.size)
    {k m g : ℕ} {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀)
    (hn : P5J.At.arr Zp (seatAtMember cF.blocksInOrder y.1 y.2.P n).1 (seatAtMember cF.blocksInOrder y.1 y.2.P n).2 =
      k4MaskNum Zp (2 * g))
    (hC : dueAt (A.B.rowsOf 0) ⟨y.2.P.place, 0⟩ = dueR y.2.P y.2.ride)
    {cells : Tr → Cells} {weights : W₀ → Weights}
    {tokens : ProofFile.Inst → Array Nat} {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Qp : K4Pub}
    (hQ : k4PubOf Zp x.2 = some Qp) {row : MsgAt}
    (hrow : ownerOf maskRowRun cF.blocksInOrder Zp.made.proof.1
      ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder.flatMap (·.rounds))
      s!"link {2 * g}, moment 0" isMaskRowMsg = some row)
    {L : ℕ}
    (hE : ∀ (k : Coins A.B) w hd ν y', ν < L → msgTxt 0 wit y.2 own₀ n k w hd true 0 ν = some y' →
      (k.look 0 row.owner).2.eAt (row.base.e + ν) = .ok y')
    (hL : Forest.elems (P5J.At.X Zp).y.fo + k4Takes Qp.P Qp.hp Qp.g ≤ L + 1)
    {c : Coins A.B} {s : TS} {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E : Env}
    (hT : Thr (lettersHead h H (joinQ cF.blocksInOrder front cellsQ tok (P5J.At.arr Zp) wit own₀ jobs O)
      test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k c s mm E) :
    K4MaskTieAt (lettersHead h H (joinQ cF.blocksInOrder front cellsQ tok (P5J.At.arr Zp) wit own₀ jobs O)
      test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread cells weights tokens look Qp
      (h.𝔇.N.sent m 0) (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms) c s mm := by
  have hP := k4PubG_of Lh hQ
  obtain ⟨-, -, row', idx, hr', -, J, -⟩ := k4Book_at_atPure h hAP (Rc := Rc) (X := X') cells
    weights tokens (look Qp) g Lh.lt Qp hP
  obtain rfl : row' = row := Option.some.inj (hr'.symm.trans hrow)
  have hLs : (⟨P5J.At.arr Zp (seatAtMember cF.blocksInOrder y.1 y.2.P n).1
      (seatAtMember cF.blocksInOrder y.1 y.2.P n).2, front + roundsTo cF.blocksInOrder y.1,
      msgTxt 0 wit y.2 own₀ n⟩ : MsgLot A.B (Local W₀ Rc ProofFile.Inst Tr)) ∈
      joinMl cF.blocksInOrder front (P5J.At.arr Zp) wit own₀ jobs O :=
    List.mem_append.2 (Or.inl (mem_k1MsgLots hx
      (List.mem_map.2 ⟨n, List.mem_range.2 hlt, rfl⟩)))
  have Ow := k4MaskOwn_ofLots (X := X') (cells := cells) (weights := weights) (tokens := tokens)
    (look := look) cF.blocksInOrder front cellsQ tok (joinPl cF.blocksInOrder jobs O) (joinTl wit own₀ jobs O)
    (joinMl cF.blocksInOrder front (P5J.At.arr Zp) wit own₀ jobs O) hLs (hm _ hLs) hP J
    hn (Vq := fun _ => True) (N := 0)
    (fun k w hd ν _ _ _ _ => by
      obtain ⟨v, hv⟩ := msgTxt_answers hC wit own₀ n k w
        (hd.take (front + roundsTo cF.blocksInOrder y.1)) true 0 ν
      exact Option.isSome_iff_exists.2 ⟨v, hv⟩)
    hE hL
  exact k4MaskTie_of_ownMsgsG h H (joinQ cF.blocksInOrder front cellsQ tok (P5J.At.arr Zp) wit own₀ jobs O)
    test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Lh hQ Ow hT trivial (Nat.zero_le _)

/-- CONDITIONAL on h, hAP, F, hx, hlt, hn, hC, Lh, hQ, hrow, hE, hL and hT. **THE SAME AT A FIT
LIST.** Of F's seven fields one is spent: msgs. The six fields pads, owned, nums, trees, found and
fits are idle here, and the list of seats is a free letter: the statement above asks less. -/
theorem k4MaskTie_at_joinQ_k1_fit (hAP : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    {seats : List (ℕ × ℕ)}
    (F : JoinFit cF.blocksInOrder front (P5J.At.arr Zp) seats wit own₀ jobs O)
    {y : ℕ × SendJob (PlaceIn Xi) Xj} (hx : y ∈ jobs) {n : ℕ} (hlt : n < y.2.P.sent.size)
    {k m g : ℕ} {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀)
    (hn : P5J.At.arr Zp (seatAtMember cF.blocksInOrder y.1 y.2.P n).1 (seatAtMember cF.blocksInOrder y.1 y.2.P n).2 =
      k4MaskNum Zp (2 * g))
    (hC : dueAt (A.B.rowsOf 0) ⟨y.2.P.place, 0⟩ = dueR y.2.P y.2.ride)
    {cells : Tr → Cells} {weights : W₀ → Weights}
    {tokens : ProofFile.Inst → Array Nat} {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Qp : K4Pub}
    (hQ : k4PubOf Zp x.2 = some Qp) {row : MsgAt}
    (hrow : ownerOf maskRowRun cF.blocksInOrder Zp.made.proof.1
      ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder.flatMap (·.rounds))
      s!"link {2 * g}, moment 0" isMaskRowMsg = some row)
    {L : ℕ}
    (hE : ∀ (k : Coins A.B) w hd ν y', ν < L → msgTxt 0 wit y.2 own₀ n k w hd true 0 ν = some y' →
      (k.look 0 row.owner).2.eAt (row.base.e + ν) = .ok y')
    (hL : Forest.elems (P5J.At.X Zp).y.fo + k4Takes Qp.P Qp.hp Qp.g ≤ L + 1)
    {c : Coins A.B} {s : TS} {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E : Env}
    (hT : Thr (lettersHead h H (joinQ cF.blocksInOrder front cellsQ tok (P5J.At.arr Zp) wit own₀ jobs O)
      test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k c s mm E) :
    K4MaskTieAt (lettersHead h H (joinQ cF.blocksInOrder front cellsQ tok (P5J.At.arr Zp) wit own₀ jobs O)
      test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread cells weights tokens look Qp
      (h.𝔇.N.sent m 0) (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms) c s mm :=
  k4MaskTie_at_joinQ_k1 h H front cellsQ tok wit own₀ jobs O test carryX item n₁ n₂ b₀ Vd Rd Kp w₁
    hAP F.msgs hx hlt Lh hn hC hQ hrow hE hL hT

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.k4MaskTie_at_joinQ
#print axioms ProofFile.Honest.K4.W.k4MaskTie_at_joinQ_fit
#print axioms ProofFile.Honest.K4.W.k4MaskTie_at_joinQ_k1
#print axioms ProofFile.Honest.K4.W.k4MaskTie_at_joinQ_k1_fit
