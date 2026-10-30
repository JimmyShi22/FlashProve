-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K8/ZzPublicAtHead.lean: the honest side of the smallness test (K8):
THE SEVENTEEN PUBLIC PREMISES OF `zz_at_join_laid`
(Johnson/Desc/ProofFile/Honest/K8/ZzAtJoinLaid.lean) ARE MET UNDER THE HEAD AND AN OPENING, at the
array named "ZZ" of the written layout and the sender's message number 0. Three definitions; six
closed tests by the kernel, five of them controls that say no; one lemma; one theorem.

`K8TwoAt.zz` is exchanged here for hR, proved nowhere, for F and hc on the joined lists and the
book, for `K8Seated` and the opening. It is not paid. Behind a yes at which the second stop is
silent. An equation on the Script. NOT IN FRONT OF A LAW OVER COINS. At the digits'
message's first sending alone. Whoever quotes it at a book names hasCoins at that book beside it: hc
is asked here.

  `seatsU3W`       the written seats of the arrays named "U3"
  `zzAddrW`        the address of the written second later place's message number n
  `zzWrittenAt`    ONE TEST ON WRITTEN LISTS, at a segment l, with five letters for the controls
                  (the array's name nm, the rows asked tau, add, dt, the message's number n): the
                  written layout has an array of the name nm, and its name is "ZZ"; its message is
                  in the written shape and is sampled; the written plan of the shared sending's
                  second later place has a message number n, sampled; at that address the written
                  seats of "BZ" bear the digits' array, in that message; a seat of "BZ" or "U3" that
                  stands there has moment 2; the plan of seats gives the message the seat of the
                  sender's message number n behind the written count of trees and dt; the array has
                  tau rows at least, and at least twice the sum of the written matrices' rows, and
                  add, columns; the sender's address is not the first sender's
  `zzWritten_all`  it passes at all 25, at "ZZ", 128, 0, 0, 0, and the written codes' lengths fit
  `zzWritten_name`, `_rows`, `_cols`, `_tree`, `_msg`   CONTROLS: at another name, at 129 rows,
                  at one column more, one tree further, at message number 1: NO AT EACH OF THE 25
  `allRows_view`   the sum of a record's matrices' rows, off the library's view of it
  **`zz_at_join_public`**   one call of `zz_at_join_laid`
How each is met. ok: `Q38.lawful_at_head`. ha, hname, hM, hans, hlen, hne, hmom, hB, hn, hansJ: the
closed test, with the ground's first parameters and seats as written (`first_at_head`,
Johnson/Desc/ProofFile/Honest/K2/Law/LightAtHead.lean; `seats_at_head`,
Johnson/Desc/ProofFile/Honest/K2/Law/DigitsLightAtHead.lean) and the job's plan as written
(`later_plan_head`, `parL_written`). hcs: by unfolding. hsI: `IM.k8_tau_128` and the closed test's
clause on rows. hsC: the library's view of the built record is the written one (`xShape_in_scope`,
`tail_of_is`, `built_tl_head`), and the closed test's clause on columns. haA: `IM.Own.zz_at_ground`
and the closed test's array. hseat: `nums_fifty`, `behind_closed`, the head's written plan of seats,
and the closed test's clause on the seat. hmz: `mz_at_built`
(Johnson/Desc/ProofFile/Honest/K8/ColsFitAtBuilt.lean).
The premises that stay. The head h, an opening O₁ and the built segment e3. On the joined lists: F.
On the book: hc. On two readers of the hidden input: hR, not public. On what is said: hOk. On the
prover's list and the thread: hK. l below 25.
Options are raised at the six closed tests (maxRecDepth, maxHeartbeats) and for the file
(maxHeartbeats); one instance is taken away, as in the files beneath. Tactics that search: `omega`
on one line, on l; `simp only` with a closed list on one line.
The sign 𝔇 is the name of a field of the library's head, as the library writes it.
Limits. An implication. No letters are given at which the premises that stay hold together. Counted
nowhere. The Limits of ZzAtJoin.lean, ZzStateAtHead.lean and ZzAtJoinLaid.lean are its own too. The
field tie is not touched. The full size alone.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.ZzAtJoinLaid
import Johnson.Desc.ProofFile.Honest.K8.ColsFitAtBuilt
import Johnson.Desc.ProofFile.Honest.K2.Law.DigitsLightAtHead
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.DigitsF9Reach
import Johnson.Desc.Ok.PlanWritten.XShapeLaws
import Johnson.IMR.ZzNamed

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Slice VerifiableInference.Desc VerifiableInference.Desc.Sound
open OnBytes.Params (ReqArray)
open OnBytes.Model (HTailF2)
open OnBytes.Model.Stages (LinkH)
open OnBytes.HonestTrace (Seat pairOf seatsOf seatAt)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc.First (S Numbers)
open VerifiableInference.Desc.First.K8 (cellsAhead)
open VerifiableInference.Desc.First.K8.Honest (allRows)
open VerifiableInference.PlanWritten (proofSizedFull tailView)
open Johnson.G (layoutFull xShapeFull)
open Johnson.AtFull.Desc (spotsWritten)
open ProofFile.Honest.K2.Law (seatsBZW)
open OnBytes.HonestTrace.U3.Fit (seatsW)
open ProofFile.Honest.FirstThread (Others joinQ JoinFit lettersHead WtF coinsB byNo)
open OnBytes.SendSim.Seat (wJobs)
open Johnson.Prover.Send (shapeAt)
open _root_.Desc.K14.Law (seatZ secondAt)
open P5J (AtMgA CellsM TS)
open P5T (psFull)

/-- The written seats of the arrays named "U3". -/
def seatsU3W : List Seat :=
  seatsW "U3"

/-- The address of the written second later place's message number n. -/
def zzAddrW (l n : ℕ) : MsgAddr := ⟨⟨(K1.placeL l true).place, 0⟩, n⟩

/-- **The one test on written lists.** nm, tau, add, dt, n: letters for the controls. -/
def zzWrittenAt (nm : String) (tau add dt n l : ℕ) : Bool :=
  (arrayOf layoutFull l nm).any fun a =>
    (Meaning.messageAt proofSizedFull.request l a.message).any fun M =>
      decide (a.name = "ZZ") && decide (M.shape.answers ≠ 0) &&
      decide (n < (K1.placeL l true).sent.size) &&
      decide ((shapeAt (K1.placeL l true) n).answers ≠ 0) &&
      decide (bearsZz layoutFull (pairOf seatsBZW) (zzAddrW l n) = some (l, a.message)) &&
      (seatAt seatsBZW (zzAddrW l n)).all (K1.momentIs · 2) &&
      (seatAt seatsU3W (zzAddrW l n)).all (K1.momentIs · 2) &&
      decide (P6T.seatT psFull l a.message =
        K1.seatOfMsg (K1.placeL l true) (K1.baseL3 l true + dt) n) &&
      decide (tau ≤ a.sizeI) &&
      (xShapeFull.1[l]?).any (·.any fun v =>
        decide (2 * (v.2.1.map (·.2.1)).foldl (· + ·) 0 + add ≤ a.sizeC)) &&
      decide ((⟨(K1.placeL l true).place, 0⟩ : Addr) ≠ K1.firstAddr)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- It passes at all 25; and the written codes' lengths fit. -/
theorem zzWritten_all : (proofSizedFull.codes.lengthsOk &&
    (List.range 25).all (zzWrittenAt "ZZ" 128 0 0 0)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- A control: at another name it says no at each of the 25. An array of that name is there at each:
the written seats of "BZ" have the segments 0 to 24 (`seatsBZW_all`,
Johnson/Desc/ProofFile/Honest/K2/Law/DigitsWritten.lean), and a seat is made of an array of its name
(by the texts of `arraySeatBy` there and of `arrayOf`). -/
theorem zzWritten_name : (List.range 25).any (zzWrittenAt "BZ" 128 0 0 0) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- A control: at one row more it says no at each of the 25. -/
theorem zzWritten_rows : (List.range 25).any (zzWrittenAt "ZZ" 129 0 0 0) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- A control: at one column more it says no at each of the 25. -/
theorem zzWritten_cols : (List.range 25).any (zzWrittenAt "ZZ" 128 1 0 0) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- A control: one tree further it says no at each of the 25. -/
theorem zzWritten_tree : (List.range 25).any (zzWrittenAt "ZZ" 128 0 1 0) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- A control: at message number 1 it says no at each of the 25. -/
theorem zzWritten_msg : (List.range 25).any (zzWrittenAt "ZZ" 128 0 0 1) = false := by
  decide +kernel

/-- The sum of a record's matrices' rows, off the library's view of the record. -/
theorem allRows_view (tl : HTailF2) :
    allRows (parOfTail tl) = ((tailView tl).2.1.map (·.2.1)).foldl (· + ·) 0 := by
  show (tl.mats.toList.map (·.m)).foldl (· + ·) 0 =
    ((tl.mats.toList.map fun x => (x.aId, x.m, x.k)).map (·.2.1)).foldl (· + ·) 0
  rw [List.map_map]
  rfl

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **The field zz at the head's letters and the joined Script, with no public premise left but l
below 25.** Exchanged, not paid: for hR, proved nowhere, F, hc, `K8Seated`, hOk, the opening and the
built segment. Behind a yes at which the second stop is silent. At the digits' message's first
sending alone. An equation on the Script. NOT IN FRONT OF A LAW OVER COINS. Whoever
quotes it at a book names hasCoins at that book beside it. -/
theorem zz_at_join_public {Said : ℕ → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop}
    (hOk : ∀ b k m, Said b k m → SaidOk b k m) {Bs : ProofFile.PureBase}
    {base₀ : List (Block S ProofFile.Cl)}
    (O₁ : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np))
    (no : Place → Nat) (S₀ : OnBytes.HonestTrace.Sz)
    (Dd : ProofFile.Pub → ProofFile.Ground → RowDataOf ProofFile.Inst) (blk : Block S ProofFile.Cl) (cells : Tr → Cells)
    (cellsQ : Local W₀ Rc ProofFile.Inst Tr → CellsM OnBytes.Flat.numsFull)
    (tokQ : Local W₀ Rc ProofFile.Inst Tr → P5J.At.Tok)
    (wit : Local W₀ Rc ProofFile.Inst Tr → K1.PlaceIn ProofFile.Inst) (own₀ : X)
    (O : Others Bk (Local W₀ Rc ProofFile.Inst Tr)) {seats : List (ℕ × ℕ)}
    (F : JoinFit cF.blocksInOrder 0 h.𝔇.arr seats wit own₀
      (byNo cF.blocksInOrder (K1.lotJobs (X := X) no (K1.lotData S₀) Zp Bs.G₀ ++
                 wJobs (X := X) no Dd Zp Bs.G₀)) O)
    (hc : coinsB Bk (byNo cF.blocksInOrder (K1.lotJobs (X := X) no (K1.lotData S₀) Zp Bs.G₀ ++
               wJobs (X := X) no Dd Zp Bs.G₀)) = true)
    {l : ℕ} (hl : l < 25) {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl)
    {matsK : List (Nat × String × Nat)}
    (hK : K8Seated (lettersHead h H (joinQ cF.blocksInOrder 0 cellsQ tokQ h.𝔇.arr wit own₀
        (byNo cF.blocksInOrder (K1.lotJobs (X := X) no (K1.lotData S₀) Zp Bs.G₀ ++
                   wJobs (X := X) no Dd Zp Bs.G₀)) O) test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (14 * l + (if l = 24 then 5 else 4) + 2) blk cells (ProofFile.k8Par Zp Bs.G₀ Xl l, matsK))
    (hR : ∀ v, v = w ∧ Vd v → (wit v).R.cells = cells v.trace) :
    ∀ k s m E ds y cols s' tl' (d : Fmt.Drawn) e (z : ProofFile.InstPub),
      ThrS (lettersHead h H (joinQ cF.blocksInOrder 0 cellsQ tokQ h.𝔇.arr wit own₀
          (byNo cF.blocksInOrder (K1.lotJobs (X := X) no (K1.lotData S₀) Zp Bs.G₀ ++
                     wJobs (X := X) no Dd Zp Bs.G₀)) O) test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
        (14 * l + (if l = 24 then 5 else 4) + 2) k s m E →
      drawsFit blk.rounds ds = true →
      (lettersHead h H (joinQ cF.blocksInOrder 0 cellsQ tokQ h.𝔇.arr wit own₀
          (byNo cF.blocksInOrder (K1.lotJobs (X := X) no (K1.lotData S₀) Zp Bs.G₀ ++
                     wJobs (X := X) no Dd Zp Bs.G₀)) O) test carryX item n₁ n₂ b₀ Vd Rd Kp
        w).thread.Stepped blk k s m E ds y cols s' →
      (lettersHead h H (joinQ cF.blocksInOrder 0 cellsQ tokQ h.𝔇.arr wit own₀
          (byNo cF.blocksInOrder (K1.lotJobs (X := X) no (K1.lotData S₀) Zp Bs.G₀ ++
                     wJobs (X := X) no Dd Zp Bs.G₀)) O) test carryX item n₁ n₂ b₀ Vd Rd Kp
        w).thread.Form (14 * l + (if l = 24 then 5 else 4) + 2 + 1) k s' y.2 →
      s'.tl? = some tl' → tl'.cfF = d.trits.toArray →
      ZzBy tl'
        (cellsAhead h.𝔇.cs h.𝔇.arr h.𝔇.ms h.𝔇.N l (z, s')
          ((lettersHead h H (joinQ cF.blocksInOrder 0 cellsQ tokQ h.𝔇.arr wit own₀
              (byNo cF.blocksInOrder (K1.lotJobs (X := X) no (K1.lotData S₀) Zp Bs.G₀ ++
                         wJobs (X := X) no Dd Zp Bs.G₀)) O) test carryX item n₁ n₂ b₀ Vd Rd Kp
            w).thread.wit k m.st.input (m.st.heard ++ d :: e)))
        (cellsAtOf (cells m.st.input.trace) (K3.matsOwn Bs.G₀.W l)) := by
  obtain ⟨fc, fs, fl⟩ := K2.Law.first_at_head h O₁
  have hl' : l ≤ 24 := by omega
  have hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some Bs.G₀ := O₁.blank
  obtain ⟨hlenW, hallW⟩ := Eq.mp (Bool.and_eq_true _ _) zzWritten_all
  have hW := List.all_eq_true.1 hallW l (List.mem_range.2 hl)
  have eP : (zzJob (X := X) Zp Bs.G₀ no S₀ l).P = K1.placeL l true :=
    (K1.later_plan_head Zp Bs.G₀ l true _ _).trans (K1.parL_written h O₁ l true)
  unfold zzWrittenAt at hW
  cases ha : arrayOf layoutFull l "ZZ" with
  | none =>
    rw [ha] at hW
    cases hW
  | some a =>
    rw [ha] at hW
    have hW1 : ((Meaning.messageAt proofSizedFull.request l a.message).any _) = true := hW
    cases hM : Meaning.messageAt proofSizedFull.request l a.message with
    | none =>
      rw [hM] at hW1
      cases hW1
    | some M =>
      rw [hM] at hW1
      have hW2 := hW1
      simp only [Option.any_some, Bool.and_eq_true, decide_eq_true_eq] at hW2
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩, c7⟩, c8⟩, c9⟩, c10⟩, c11⟩ := hW2
      have eTl := K3.Law.AtThr.built_tl_head h l hl O₁ e3
      have eV : xShapeFull.1[l]? = some (some (tailView Xl.tl)) := by
        rw [VerifiableInference.PlanWritten.tail_of_is
          (VerifiableInference.PlanWritten.xShapeIs_of
            (VerifiableInference.PlanWritten.Joined.xShape_in_scope h.scope h.laid.pub
              (K1.pin1_atAll h))) hl, eTl]
        rfl
      rw [eV] at c10
      have c10' : 2 * ((tailView Xl.tl).2.1.map (·.2.1)).foldl (· + ·) 0 + 0 ≤ a.sizeC :=
        of_decide_eq_true c10
      have eNo := beq_iff_eq.1 (List.all_eq_true.1 behind_closed l (List.mem_range.2 hl))
      exact zz_at_join_laid h H test carryX item n₁ n₂ b₀ Vd Rd Kp w hOk O₁ no S₀ Dd blk cells
        cellsQ tokQ wit own₀ O F hc hl e3 hK (n := 0) (nm := "ZZ") (a := a) (M := M)
        (by rw [eP]; exact c3)
        (by rw [Meaning.K2.blank_first hG]; exact Q38.lawful_at_head h)
        (by rw [fl]; exact ha) c1 (by rw [fs]; exact hM) c2 (by rw [fc]; exact hlenW)
        (by rw [eP]; exact c11)
        (by
          intro t ht
          rw [eP, OnBytes.HonestTrace.U3.Fit.seats_at_head h O₁.blank "BZ",
            OnBytes.HonestTrace.U3.Fit.seats_at_head h O₁.blank "U3"] at ht
          rcases ht with h1 | h1
          · have e6 : (seatAt seatsBZW (zzAddrW l 0)).all (K1.momentIs · 2) = true := c6
            rw [show seatAt seatsBZW (zzAddrW l 0) = some t from h1] at e6
            exact e6
          · have e7 : (seatAt seatsU3W (zzAddrW l 0)).all (K1.momentIs · 2) = true := c7
            rw [show seatAt seatsU3W (zzAddrW l 0) = some t from h1] at e7
            exact e7)
        (by rw [fl, K2.Law.seatsBZ_at_head h O₁, eP]; exact c5)
        (by
          show h.𝔇.cs = Bs.G₀.first.codes
          rw [Meaning.K2.blank_first hG]
          rfl)
        (by
          rw [show Xl.tl.tau = 128 from IM.k8_tau_128 h.scope h.reads O₁ hl' e3]
          exact c9)
        (by rw [allRows_view]; exact c10')
        hR
        (by
          intro bn hbn
          obtain rfl : (l, "ZZ") = bn :=
            Option.some.inj ((IM.Own.zz_at_ground h.laid.pub hG e3).symm.trans hbn)
          rw [fl]
          exact ha)
        (by rw [eP]; exact c4)
        (by
          rw [eP, ← eNo]
          show P6T.seatT (P5J.At.pseats Zp) l a.message =
            K1.seatOfMsg (K1.placeL l true) (treesTo cF.blocksInOrder (K1.noL l true)) 0
          rw [show P5J.At.pseats Zp = psFull from h.toAtMg.seats, (K1.nums_fifty h O₁ hl true).2]
          exact c8)
        (Nat.le_of_eq (mz_at_built h.scope h.reads O₁ h.laid.planOk hl e3))

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.seatsU3W
#print axioms ProofFile.Honest.K8.zzAddrW
#print axioms ProofFile.Honest.K8.zzWrittenAt
#print axioms ProofFile.Honest.K8.zzWritten_all
#print axioms ProofFile.Honest.K8.zzWritten_name
#print axioms ProofFile.Honest.K8.zzWritten_rows
#print axioms ProofFile.Honest.K8.zzWritten_cols
#print axioms ProofFile.Honest.K8.zzWritten_tree
#print axioms ProofFile.Honest.K8.zzWritten_msg
#print axioms ProofFile.Honest.K8.allRows_view
#print axioms ProofFile.Honest.K8.zz_at_join_public
