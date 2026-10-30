-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K7/AtExchange.lean: the one item that the row of the next token's member
(kind K7, number 338 of the first chain) owes. The row closes `constr 24 lookCalls`, the head's keys at
the witness's token, and opens `constr 24 lookCallsHeard`, the same keys at the reply that the state has
heard. So the item holds behind the member where the witness's token is the reply heard.

  `constr_heard_of_calls`   the item's statement behind, from the statement in front, at the head's own
                   segment: general in its letters
  `headPartK6_heard`   the head's part behind, from the part in front, at one request and one token
  `k7_exchange`   `ExchangeAtS` at the member
  `hw_of_script`   the premise below from one clause on the script
  `k7_row_owes`, `k7_front_open`, `k7_places`, `k7_place_number`   closed tests on the written lists
  `k7_exchange_cell`   at every number of the kind, each item that the row owes

The premise `hw`: at an input that the thread lets through, the witness's token is the token that a state
holding the asked reply has heard. It is a premise on the script. This file proves nothing about soundness, completeness,
hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.K7.AtSeat
import Johnson.Desc.ProofFile.Honest.K7.Behind
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead
import Johnson.Desc.ProofFile.Honest.Thread.SharesS
import Johnson.Desc.ProofFile.Honest.Thread.PaysLaw
import Johnson.Desc.ProofFile.Honest.Thread.FirstRows
import Johnson.Desc.Kinds.Law.HeadCutsK6
import Johnson.P5J.RowsAtMg

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Block Chain Strs Wit Place)
open VerifiableInference.Desc.First (Item Numbers)
open VerifiableInference.Desc.Sound (MsgT Mem oneDec)
open VerifiableInference.Desc.Kinds.Head.Law (headPartK6 partsAtX)
open VerifiableInference.OnPublicFiles (headLink)
open VerifiableInference.OnPublicFiles.Flat (GE)
open Inst.Model (ppref)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)

/-- **The item's statement behind, from the statement in front**, at the head's own segment. -/
theorem constr_heard_of_calls {X : OnBytes.Model.Verify.Public} {P W : Type} {rows cols : Nat}
    (hd : Nat) (put : P5J.TReq → Fin ppref.V → P5J.TReq) (H : P5J.HidAt X P W rows cols)
    (headPart : P5J.TPart → Cm.Idx → P × TS → Strs → W → Prop)
    (digitsPart : Nat → P × TS → Strs → W → Prop) (k : Nat) (hk : k = hd) (a a' : P × TS)
    (y y' : Strs) (w : W) (hdec : H.dec a' y' = H.dec a y)
    (hhead : ∀ i, headPart .lookCalls i a y w → headPart .lookCallsHeard i a' y' w)
    (h : P5J.constrQAt hd put H headPart digitsPart k .lookCalls a y w) :
    P5J.constrQAt hd put H headPart digitsPart k .lookCallsHeard a' y' w := by
  subst hk
  unfold P5J.constrQAt at h ⊢
  rw [if_neg (by decide)] at h ⊢
  refine ⟨fun e => (by cases e), fun M i hM hi => ?_⟩
  have h2 := h.2 M i (by rw [← hdec]; exact hM) hi
  rw [if_pos rfl] at h2 ⊢
  exact hhead i h2

/-- **The head's part behind, from the part in front.** -/
theorem headPartK6_heard {rows cols : Nat} (cs : OnBytes.Codes) {Tok : Type}
    (arr : Nat → Nat → Nat) (msR : List Mem) (N : Numbers) (s : Nat → Cb.Pv.Tail.Size)
    (seat : ∀ k, Fin (s k).NM → Nat → Nat → Nat × Nat × Nat) (Wp : OnBytes.Model.Verify.Public)
    (pl : Nat → Nat × Bool × Nat × Nat) {P : Type} (tab : Nat → Nat)
    (put : P5J.TReq → Fin ppref.V → P5J.TReq)
    (H : P5J.HidAt Wp P (Wit (Fin rows → Fin cols → GE) Tok MsgT) rows cols)
    (tokH : P × P5J.TS → Fin ppref.V) (i : Cm.Idx) (a a' : P × P5J.TS) (y y' : Strs)
    (w : Wit (Fin rows → Fin cols → GE) Tok MsgT) (hr : H.req a' = H.req a)
    (ht : tokH a' = (H.hid w).tok)
    (h0 : headPartK6 cs arr msR N s seat Wp pl tab put H tokH .lookCalls i a y w) :
    headPartK6 cs arr msR N s seat Wp pl tab put H tokH .lookCallsHeard i a' y' w := by
  show partsAtX cs arr msR N s seat Wp pl tab i (put (H.req a') (tokH a')).val w .lookCalls
  rw [hr, ht]
  exact h0

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **`ExchangeAtS` at the member.** -/
theorem k7_exchange (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    {V : Nat} {blk : Block TS ProofFile.Cl} {G : ProofFile.Ground} {x₀ : Block TS Unit} {a : Place}
    {fs : List Johnson.Desc.First.Walk.Seat.LinkFrame}
    {f : Johnson.Desc.First.Walk.Seat.LinkFrame}
    (K : K7Stands (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 338 24 V blk)
    (Dm : K7Made Zp G 24 blk x₀ a fs f)
    (hop : Item.constr 24 .lookCalls ∈
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.opened 338)
    (hw : ∀ (k : Coins Bk) (v : Local W₀ Rc ProofFile.Inst Tr) (ds : List Fmt.Drawn) (s : TS),
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.valid v → s.out.reply = some v.x.asked →
      (h.𝔇.H.hid ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.wit k v ds)).tok =
        P5J.tokVOf ((s.replyTok?).getD 0)) :
    ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 338
      (Item.constr 24 .lookCallsHeard) := by
  intro blk' hblk k s mm E ds y cols s' hA hd hS ds' j hj
  obtain rfl := List.mem_singleton.1 hj
  obtain rfl : blk = blk' := Option.some.inj (K.member.symm.trans hblk)
  have hr : s'.out.reply = some mm.st.input.x.asked :=
    k7_laysS Said K Dm 0 0 blk hblk k s mm E ds y cols s' hA hd hS
  have hM := hS.1
  have hpl := hM.1.choose_spec.2
  have hin : y.2.st.input = mm.st.input := (play_mid _ _ _ _ _ hpl).1
  have hheard : y.2.st.heard = mm.st.heard ++ ds := play_heard _ _ _ _ _ hpl
  have hseat := seat_moved hA.1.2.1 hM
  have hI := hA.1.2.2.2.1 (ds ++ ds') _ hop
  have h24 : headLink (P5J.At.X Zp) = 24 := P5J.headLink_in_scope h.scope h.reads h.pubOne
  rw [hin, hseat s s', hheard, List.append_assoc]
  have hval := hA.1.2.2.2.2.2.2
  exact constr_heard_of_calls (headLink (P5J.At.X Zp)) h.𝔇.put
    (oneDec (fun _ _ => some (Q.cells mm.st.input)) h.𝔇.H) h.𝔇.headPart h.𝔇.digitsPart 24 h24.symm
    ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.seat k mm s)
    (((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.seat k mm s).1, s')
    ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs E)
    ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs (E.add y.1))
    ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.wit k mm.st.input
      (mm.st.heard ++ (ds ++ ds'))) rfl
    (fun i hi => headPartK6_heard _ _ _ _ _ _ _ _ _ _ _ _ i _ _
      ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs E)
      ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs (E.add y.1)) _ rfl
      (hw k mm.st.input _ s' hval hr).symm hi) hI

/-- **The premise `hw` from one clause on the script**: at a valid input the script's token is the number
of the asked reply, and the reply is of the form that the state's reader reads. -/
theorem hw_of_script
    (hq : ∀ v : Local W₀ Rc ProofFile.Inst Tr, (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.valid v →
      Q.tok v = v.x.asked.c0.toNat ∧ OnBytes.Model.ofNat v.x.asked.c0.toNat = v.x.asked) :
    ∀ (k : Coins Bk) (v : Local W₀ Rc ProofFile.Inst Tr) (ds : List Fmt.Drawn) (s : TS),
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.valid v → s.out.reply = some v.x.asked →
      (h.𝔇.H.hid ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.wit k v ds)).tok =
        P5J.tokVOf ((s.replyTok?).getD 0) := by
  intro k v ds s hv hs
  obtain ⟨h1, h2⟩ := hq v hv
  have e : s.replyTok? = some v.x.asked.c0.toNat := by
    unfold VerifiableInference.Desc.First.S.replyTok?
    rw [hs]
    simp [h2]
  rw [e]
  show P5J.tokVOf (Q.tok v) = _
  rw [h1]
  rfl

set_option maxRecDepth 1000000 in
/-- The row at the member owes the one item. -/
theorem k7_row_owes : (FirstRows.rows P5J.At.links P5J.At.ps 338).owes =
    [Item.constr 24 .lookCallsHeard] := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The item in front is open at the border. -/
theorem k7_front_open : Item.constr 24 .lookCalls ∈
    fwdOpen (VerifiableInference.Desc.First.start P5J.At.links)
      (FirstRows.rows P5J.At.links P5J.At.ps) 338 := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- Of the written list of places only number 338 is of the kind. -/
theorem k7_places : ((List.range P5J.At.ps.length).all fun b =>
    (P5J.At.ps[b]?).all fun p => !(p.kind == .K7) || b == 338) = true := by
  decide +kernel

/-- **A number whose place is of the kind is 338.** -/
theorem k7_place_number {b : Nat} {p : Place} (hp : P5J.At.ps[b]? = some p)
    (hk : p.kind = .K7) : b = 338 := by
  have hb : b < P5J.At.ps.length := (List.getElem?_eq_some_iff.1 hp).1
  have h1 := List.all_eq_true.1 k7_places b (List.mem_range.2 hb)
  rw [hp] at h1
  simpa [hk] using h1

/-- **THE CELL OF THE GATHER AT THE KIND**: at every number whose place is of the kind, `ExchangeAtS` at
each item that the row owes. `hhalf`: the prover's look-up at the place finds the kind's half. `hw`: as
in `k7_exchange`. -/
theorem k7_exchange_cell (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) {Vh : Nat}
    (hhalf : H.first.find? (fun g => g.place == IM.k7Place) = some (replyHalf 24 1 Vh))
    (hw : ∀ (k : Coins Bk) (v : Local W₀ Rc ProofFile.Inst Tr) (ds : List Fmt.Drawn) (s : TS),
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.valid v → s.out.reply = some v.x.asked →
      (h.𝔇.H.hid ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.wit k v ds)).tok =
        P5J.tokVOf ((s.replyTok?).getD 0)) :
    ∀ b p, P5J.At.ps[b]? = some p → p.kind = .K7 →
      ∀ j ∈ ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.row b).owes,
        ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said b j := by
  intro b p hp hk j hj
  obtain rfl := k7_place_number hp hk
  have hrow : ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.row 338).owes =
      [Item.constr 24 .lookCallsHeard] := k7_row_owes
  rw [hrow] at hj
  obtain rfl := List.mem_singleton.1 hj
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨blk, x₀, fs, f, K, Dm⟩ := k7_stands_of_open h.scope h.reads O
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread rfl hhalf
  exact k7_exchange h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said K Dm k7_front_open hw

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.constr_heard_of_calls
#print axioms ProofFile.Honest.FirstThread.headPartK6_heard
#print axioms ProofFile.Honest.FirstThread.k7_exchange
#print axioms ProofFile.Honest.FirstThread.hw_of_script
#print axioms ProofFile.Honest.FirstThread.k7_row_owes
#print axioms ProofFile.Honest.FirstThread.k7_front_open
#print axioms ProofFile.Honest.FirstThread.k7_places
#print axioms ProofFile.Honest.FirstThread.k7_place_number
#print axioms ProofFile.Honest.FirstThread.k7_exchange_cell
