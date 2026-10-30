-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K8/ZzAtJoin.lean: the honest side of the smallness test (K8): the
field zz of `K8TwoAt` (Johnson/Desc/ProofFile/Honest/K8/ExchangeByKind.lean), in its own form, at
letters whose Script is the joined one (`joinQ`, Johnson/Desc/ProofFile/Honest/Thread/Join.lean).
Five statements with their proofs; no definition.

`K8TwoAt.zz` is exchanged here for hSt and hR, each proved nowhere, and for public premises. It is
not paid. Behind a yes at which the second stop is silent. An equation on the Script.
NOT IN FRONT OF A LAW OVER COINS. At the digits' message's first sending alone: of a copy that a
later member keeps or sends again nothing is said. Whoever quotes either statement at a book names
hasCoins at that book beside it: hbook is asked here.

  **`zz_at_join`**   `zz_under_thread` (Johnson/Desc/ProofFile/Honest/K8/ZzUnderThread.lean) with
                  its premise hm on the Script laid in by `join_tie_k1_fit`
                  (Johnson/Desc/ProofFile/Honest/Thread/JoinFit.lean). The kind sends nothing and
                  has no text of its own: the text is the sender's own, `K1.msgTxt` at the chain 0.
                  In that law the bound on what was heard and the cut of the text are one number,
                  the rounds in front of the sender; `zz_under_thread` asks the first at most, the
                  second at least, one more than the rounds in front of the draw: so hnext is asked:
                  the two numbers are equal
  **`zz_at_join_head`**   the same at the first chain's letters at the library's head
                  (`lettersHead`, Johnson/Desc/ProofFile/Honest/Thread/FirstHead.lean), at the
                  kind's number of segment l, the sender one number on: hnext and hrng are laid in
                  (`next_at_head`, `hrng_at_head`,
                  Johnson/Desc/ProofFile/Honest/K8/RngAtHead.lean); that the letters' Script is the
                  joined one holds by unfolding
  `arr_at_head`   the head's data's function from seats to messages' numbers is the written one at
                  the public part, by unfolding: so a `JoinFit` stated at `P5J.At.arr Zp` serves as
                  F
  `readers_one`   what meets hR: where the reader of the input is written with the cells of the
                  input's trace as its first reader, hR holds by unfolding, at every input
  `hbook_of_test`   what meets hbook: where the join's test on the book (`coinsB`) passes at a list
                  of jobs, the book covers the due of each job in it: the test has an equation
                  where hbook asks no more than the book's count
What meets hx and hJ of the second: `zz_job_in_list`
(Johnson/Desc/ProofFile/Honest/K8/ZzJobInList.lean).
The premises, sorted. On the joined lists: F (the one premise `JoinFit`: the lots agree, each listed
seat is owned, and four clauses on numbers, trees and places), hx (the job stands in the list with
its number), hn. On the prover's text: hJ. On the book: hbook. On two readers of the hidden input:
hR, not public. On the thread's states: hSt: on the verifier's state alone, asked at every reached
state behind the member's step. On public data: all others.
`Sound.seatOf` is written with its namespace: a second constant of that name is in reach here.
No option is raised; one instance is taken away, as in the files beneath. No tactic that searches.
The sign 𝔇 is the name of a field of the library's head, as
the library writes it.
Limits. Implications. No letters are given at which the premises hold together. Counted nowhere. At
an empty record O, or where the list holds the shared sending's jobs alone, the joined Script is
still one that no run has. F's list of seats may be any list, the empty one too, and then its field
owned is void. Neither long statement leans on that field: each reads one message, sent by the job
J, whose lots stand in the joined lists by hx. Where no state of the thread stands at the number, or
blk takes no step there, both long statements hold emptily. The field tie is not touched. That
`JoinFit` or the test on the book holds at the full size is shown nowhere here. `readers_one` speaks
of a written reader, at no filling: that any filling lays that reader is not said.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.ZzUnderThread
import Johnson.Desc.ProofFile.Honest.K8.RngAtHead
import Johnson.Desc.ProofFile.Honest.Thread.JoinFit
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Slice VerifiableInference.Desc VerifiableInference.Desc.Sound
open OnBytes.Params (ReqArray)
open OnBytes.Model (HTailF2)
open OnBytes.HonestTrace (pairOf seatsOf seatAt)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc.First (S Numbers)
open VerifiableInference.Desc.First.K8 (cellsAhead)
open VerifiableInference.Desc.First.K8.Honest (allRows)
open VerifiableInference.Desc.K9 (rowBitsOf placeBitsOf)
open ProofFile.Honest.K2 (drawnAt)
open ProofFile.Honest.FirstThread (Letters OwnMsgs Others joinQ JoinFit join_tie_k1_fit lettersHead WtF
  coinsB coins_gives)
open Johnson.Prover.Send (shapeAt)
open P5J (AtMgA CellsM TS)

/-- **The field zz at the joined Script, exchanged for hSt and hR, each proved nowhere, and public
premises.** hSt: on the verifier's state alone, asked at every reached state behind the member's
step. hR: on two readers of the hidden input. Behind a yes at which the second stop is silent. At
the digits' message's first sending alone. An equation on the Script.
NOT IN FRONT OF A LAW OVER COINS. Whoever quotes it at a book names hasCoins there beside it. -/
theorem zz_at_join {Bk : ProverCoinCounts} {Cl W₀ Rc Tr X Pz Cw Tok : Type}
    (L : Letters Bk Cl W₀ Rc ProofFile.Inst Tr X Pz Cw Tok MsgT)
    (Said : ℕ → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) (b : ℕ) (blk : Block S Cl)
    (cells : Tr → Cells) (cellsQ : Local W₀ Rc ProofFile.Inst Tr → Cw)
    (tokQ : Local W₀ Rc ProofFile.Inst Tr → Tok)
    (arr : ℕ → ℕ → ℕ) (wit : Local W₀ Rc ProofFile.Inst Tr → K1.PlaceIn ProofFile.Inst) (own₀ : X)
    (jobs : List (ℕ × K1.SendJob (K1.PlaceIn ProofFile.Inst) X))
    (O : Others Bk (Local W₀ Rc ProofFile.Inst Tr))
    (hQ : L.Q = joinQ L.bs 0 cellsQ tokQ arr wit own₀ jobs O)
    {seats : List (ℕ × ℕ)} (F : JoinFit L.bs 0 arr seats wit own₀ jobs O)
    {no : ℕ} {J : K1.SendJob (K1.PlaceIn ProofFile.Inst) X} (hx : (no, J) ∈ jobs) {n : ℕ}
    (hn : n < J.P.sent.size) (hnext : roundsTo L.bs no = roundsTo L.bs b + 1)
    (S₀ : OnBytes.HonestTrace.Sz) (Z : Pub)
    (G : Ground) (gp : _root_.Desc.Plain.GPar) (lk piece first : ℕ)
    (hJ : J = K1.laterJobAt G.first gp lk piece 2 first (K1.lotData S₀ Z G))
    (cs : OnBytes.Codes) (ms : List Mem) (Nn : Numbers) {l : ℕ} {nm : String} {a : ReqArray}
    (hbook : K1.bookCovers Bk 0 ⟨J.P.place, 0⟩ (K1.dueR J.P J.ride) = true)
    (ok : reqLayoutOk G.first.codes G.first.shape G.first.layout = true)
    (ha : arrayOf G.first.layout l nm = some a) (hname : a.name = "ZZ") {M : Params.ReqMessage}
    (hM : Meaning.messageAt G.first.shape l a.message = some M) (hans : M.shape.answers ≠ 0)
    (hlen : G.first.codes.lengthsOk = true) (hne : (⟨J.P.place, 0⟩ : Addr) ≠ K1.firstAddr)
    (hmom : ∀ t, (seatAt (seatsOf Z G "BZ") ⟨⟨J.P.place, 0⟩, n⟩ = some t ∨
      seatAt (seatsOf Z G "U3") ⟨⟨J.P.place, 0⟩, n⟩ = some t) → K1.momentIs t 2 = true)
    (hB : bearsZz G.first.layout (pairOf (seatsOf Z G "BZ")) ⟨⟨J.P.place, 0⟩, n⟩ =
      some (l, a.message))
    {tl₀ : HTailF2} (htl : (zzPubOf G Z.D.1 (K3.matsOwn G.W)).tl l = some tl₀)
    (hrng : (zzPubOf G Z.D.1 (K3.matsOwn G.W)).rng[l]? = some (roundsTo L.bs b))
    (hcs : cs = J.P.codes) (hsI : tl₀.tau ≤ a.sizeI)
    (hsC : 2 * allRows (parOfTail tl₀) ≤ a.sizeC)
    (hR : ∀ w, L.valid w → (wit w).R.cells = cells w.trace)
    (hSt : ∀ k s m E ds pl cols s' tl', ThrS L.thread Said b k s m E →
      drawsFit blk.rounds ds = true → L.thread.Stepped blk k s m E ds pl cols s' →
      L.thread.Form (b + 1) k s' pl.2 → s'.tl? = some tl' →
      ∃ (q : K9.Part) (x : ℕ × String) (h : K9.Ahead) (y : Mem), K9.segAt? s' = some q ∧
        q.L.arrayOf[tl'.ix.ZZ]? = some x ∧
        K9.aheadIn (Nn.sent l) (Nn.group l) q (x.1, x.2) = some h ∧ h.A = a ∧
        laidMatrixOk h.A (rowBitsOf h.shape .main) (placeBitsOf q.d.st.codes h.shape .main) =
          true ∧
        ms.find? (fun y => decide (Sound.seatOf y = h.seat)) = some y ∧ numOf arr y =
          arr (K1.seatAtMember L.bs no J.P n).1 (K1.seatAtMember L.bs no J.P n).2 ∧
        (y.1.l.get y.2).1 = shapeAt J.P n ∧ parOfTail tl₀ = parOfTail tl' ∧
        2 * tl'.mz ≤ 2 * allRows (parOfTail tl₀)) :
    ∀ k s m E ds y cols s' tl' (d : Fmt.Drawn) e (z : Pz), ThrS L.thread Said b k s m E →
      drawsFit blk.rounds ds = true → L.thread.Stepped blk k s m E ds y cols s' →
      L.thread.Form (b + 1) k s' y.2 → s'.tl? = some tl' → tl'.cfF = d.trits.toArray →
      ZzBy tl'
        (cellsAhead cs arr ms Nn l (z, s') (L.thread.wit k m.st.input (m.st.heard ++ d :: e)))
        (cellsAtOf (cells m.st.input.trace) (K3.matsOwn G.W l)) := by
  have hm := (join_tie_k1_fit F cellsQ tokQ L.valid hx).1 n hn
  rw [← hQ] at hm
  exact zz_under_thread L Said b blk cells L.valid (0 + roundsTo L.bs no) 0 (Nat.zero_le 1) wit S₀ Z
    G gp lk piece first hJ own₀ (0 + roundsTo L.bs no) n _ (K1.msgTxt 0 wit J own₀ n) cs arr ms Nn
    hm (fun _ _ _ _ _ _ _ _ hv => hv) hbook (fun _ hw => hw) ok ha hname hM hans hlen hne hmom hB
    htl hrng (Nat.le_of_eq (by rw [Nat.zero_add, hnext])) (Nat.le_of_eq (by rw [Nat.zero_add,
    hnext])) hcs hsI hsC hR hSt

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **The same at the head's letters, at the kind's number of segment l.** Exchanged for hSt and hR,
each proved nowhere, and public premises. Behind a yes at which the second stop is silent. At the
digits' message's first sending alone. An equation on the Script. NOT IN FRONT OF A LAW OVER COINS.
Whoever quotes it at a book names hasCoins at that book beside it. -/
theorem zz_at_join_head (Said : ℕ → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (blk : Block S ProofFile.Cl) (cells : Tr → Cells)
    (cellsQ : Local W₀ Rc ProofFile.Inst Tr → CellsM OnBytes.Flat.numsFull)
    (tokQ : Local W₀ Rc ProofFile.Inst Tr → P5J.At.Tok)
    (wit : Local W₀ Rc ProofFile.Inst Tr → K1.PlaceIn ProofFile.Inst) (own₀ : X)
    (jobs : List (ℕ × K1.SendJob (K1.PlaceIn ProofFile.Inst) X))
    (O : Others Bk (Local W₀ Rc ProofFile.Inst Tr))
    {seats : List (ℕ × ℕ)} (F : JoinFit cF.blocksInOrder 0 h.𝔇.arr seats wit own₀ jobs O)
    {l : ℕ} (hl : l < 25) {J : K1.SendJob (K1.PlaceIn ProofFile.Inst) X}
    (hx : (14 * l + (if l = 24 then 5 else 4) + 2 + 1, J) ∈ jobs) {n : ℕ}
    (hn : n < J.P.sent.size) (S₀ : OnBytes.HonestTrace.Sz)
    (G : Ground) (gp : _root_.Desc.Plain.GPar) (lk piece first : ℕ)
    (hJ : J = K1.laterJobAt G.first gp lk piece 2 first (K1.lotData S₀ Zp G))
    {nm : String} {a : ReqArray}
    (hbook : K1.bookCovers Bk 0 ⟨J.P.place, 0⟩ (K1.dueR J.P J.ride) = true)
    (ok : reqLayoutOk G.first.codes G.first.shape G.first.layout = true)
    (ha : arrayOf G.first.layout l nm = some a) (hname : a.name = "ZZ") {M : Params.ReqMessage}
    (hM : Meaning.messageAt G.first.shape l a.message = some M) (hans : M.shape.answers ≠ 0)
    (hlen : G.first.codes.lengthsOk = true) (hne : (⟨J.P.place, 0⟩ : Addr) ≠ K1.firstAddr)
    (hmom : ∀ t, (seatAt (seatsOf Zp G "BZ") ⟨⟨J.P.place, 0⟩, n⟩ = some t ∨
      seatAt (seatsOf Zp G "U3") ⟨⟨J.P.place, 0⟩, n⟩ = some t) → K1.momentIs t 2 = true)
    (hB : bearsZz G.first.layout (pairOf (seatsOf Zp G "BZ")) ⟨⟨J.P.place, 0⟩, n⟩ =
      some (l, a.message))
    {tl₀ : HTailF2} (htl : (zzPubOf G Zp.D.1 (K3.matsOwn G.W)).tl l = some tl₀)
    (hcs : h.𝔇.cs = J.P.codes) (hsI : tl₀.tau ≤ a.sizeI)
    (hsC : 2 * allRows (parOfTail tl₀) ≤ a.sizeC)
    (hR : ∀ v, v = w ∧ Vd v → (wit v).R.cells = cells v.trace)
    (hSt : ∀ k s m E ds pl cols s' tl',
      ThrS (lettersHead h H (joinQ cF.blocksInOrder 0 cellsQ tokQ h.𝔇.arr wit own₀ jobs O) test carryX item
        n₁ n₂ b₀ Vd Rd Kp w).thread Said (14 * l + (if l = 24 then 5 else 4) + 2) k s m E →
      drawsFit blk.rounds ds = true →
      (lettersHead h H (joinQ cF.blocksInOrder 0 cellsQ tokQ h.𝔇.arr wit own₀ jobs O) test carryX item
        n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds pl cols s' →
      (lettersHead h H (joinQ cF.blocksInOrder 0 cellsQ tokQ h.𝔇.arr wit own₀ jobs O) test carryX item
        n₁ n₂ b₀ Vd Rd Kp w).thread.Form (14 * l + (if l = 24 then 5 else 4) + 2 + 1) k s' pl.2 →
      s'.tl? = some tl' →
      ∃ (q : K9.Part) (x : ℕ × String) (g : K9.Ahead) (y : Mem), K9.segAt? s' = some q ∧
        q.L.arrayOf[tl'.ix.ZZ]? = some x ∧
        K9.aheadIn (h.𝔇.N.sent l) (h.𝔇.N.group l) q (x.1, x.2) = some g ∧ g.A = a ∧
        laidMatrixOk g.A (rowBitsOf g.shape .main) (placeBitsOf q.d.st.codes g.shape .main) =
          true ∧
        h.𝔇.ms.find? (fun y => decide (Sound.seatOf y = g.seat)) = some y ∧ numOf h.𝔇.arr y =
          h.𝔇.arr
            (K1.seatAtMember cF.blocksInOrder (14 * l + (if l = 24 then 5 else 4) + 2 + 1) J.P n).1
            (K1.seatAtMember cF.blocksInOrder (14 * l + (if l = 24 then 5 else 4) + 2 + 1) J.P n).2 ∧
        (y.1.l.get y.2).1 = shapeAt J.P n ∧ parOfTail tl₀ = parOfTail tl' ∧
        2 * tl'.mz ≤ 2 * allRows (parOfTail tl₀)) :
    ∀ k s m E ds y cols s' tl' (d : Fmt.Drawn) e (z : ProofFile.InstPub),
      ThrS (lettersHead h H (joinQ cF.blocksInOrder 0 cellsQ tokQ h.𝔇.arr wit own₀ jobs O) test carryX item
        n₁ n₂ b₀ Vd Rd Kp w).thread Said (14 * l + (if l = 24 then 5 else 4) + 2) k s m E →
      drawsFit blk.rounds ds = true →
      (lettersHead h H (joinQ cF.blocksInOrder 0 cellsQ tokQ h.𝔇.arr wit own₀ jobs O) test carryX item
        n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y cols s' →
      (lettersHead h H (joinQ cF.blocksInOrder 0 cellsQ tokQ h.𝔇.arr wit own₀ jobs O) test carryX item
        n₁ n₂ b₀ Vd Rd Kp w).thread.Form (14 * l + (if l = 24 then 5 else 4) + 2 + 1) k s' y.2 →
      s'.tl? = some tl' → tl'.cfF = d.trits.toArray →
      ZzBy tl'
        (cellsAhead h.𝔇.cs h.𝔇.arr h.𝔇.ms h.𝔇.N l (z, s')
          ((lettersHead h H (joinQ cF.blocksInOrder 0 cellsQ tokQ h.𝔇.arr wit own₀ jobs O) test carryX item
            n₁ n₂ b₀ Vd Rd Kp w).thread.wit k m.st.input (m.st.heard ++ d :: e)))
        (cellsAtOf (cells m.st.input.trace) (K3.matsOwn G.W l)) :=
  zz_at_join (lettersHead h H (joinQ cF.blocksInOrder 0 cellsQ tokQ h.𝔇.arr wit own₀ jobs O) test carryX item
    n₁ n₂ b₀ Vd Rd Kp w) Said (14 * l + (if l = 24 then 5 else 4) + 2) blk cells cellsQ tokQ h.𝔇.arr
    wit own₀ jobs O rfl F hx hn (next_at_head h hl) S₀ Zp G gp lk piece first hJ h.𝔇.cs h.𝔇.ms h.𝔇.N
    hbook ok ha hname hM hans hlen hne hmom hB htl (hrng_at_head h G _ hl) hcs hsI hsC hR hSt

/-- The head's data's numbers of messages are the written function at the public part. -/
theorem arr_at_head : h.𝔇.arr = P5J.At.arr Zp := rfl

/-- **Where the join's test on the book passes, hbook holds at each job of the list.** On the book's
counts and the plans alone. -/
theorem hbook_of_test {Bk : ProverCoinCounts} {Xi X : Type} {jobs : List (ℕ × K1.SendJob (K1.PlaceIn Xi) X)}
    (hc : coinsB Bk jobs = true) {no : ℕ} {J : K1.SendJob (K1.PlaceIn Xi) X}
    (hx : (no, J) ∈ jobs) :
    K1.bookCovers Bk 0 ⟨J.P.place, 0⟩ (K1.dueR J.P J.ride) = true := by
  have e : dueAt (Bk.rowsOf 0) ⟨J.P.place, 0⟩ = K1.dueR J.P J.ride := coins_gives hc (no, J) hx
  unfold K1.bookCovers
  rw [e]
  exact decide_eq_true ⟨Nat.le_refl _, Nat.le_refl _⟩

/-- **Where the reader is written over the cells of the input's trace, hR holds by unfolding.** At a
written reader; at no filling. -/
theorem readers_one {W₀ Rc Tr : Type} (cells : Tr → Cells)
    (wts : Local W₀ Rc ProofFile.Inst Tr → Weights) (rnd : Local W₀ Rc ProofFile.Inst Tr → Nat → TableRand)
    (v : Local W₀ Rc ProofFile.Inst Tr) :
    ((fun u : Local W₀ Rc ProofFile.Inst Tr =>
      (⟨u.x, ⟨cells u.trace, wts u, rnd u⟩⟩ : K1.PlaceIn ProofFile.Inst)) v).R.cells =
      cells v.trace := rfl

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.zz_at_join
#print axioms ProofFile.Honest.K8.zz_at_join_head
#print axioms ProofFile.Honest.K8.arr_at_head
#print axioms ProofFile.Honest.K8.hbook_of_test
#print axioms ProofFile.Honest.K8.readers_one
