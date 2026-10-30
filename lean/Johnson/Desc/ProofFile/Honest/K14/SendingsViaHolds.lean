-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/SendingsViaHolds.lean: what Honest/K14/SendingsViaRows.lean leaves
open between the two texts of a sending: THE TAILS AND THE RIDING TABLE. The rows that the shared
sending's part lays (rowsR, Honest/K1/Coins.lean) have the tails, and at a fold's fresh table the
entries, that this kind's own text lays (laid, Honest/K14/Sendings.lean) of the same coins, read.

  coded_coin      a part's coin below its count, as the program's element
  freshRow_same   where its h is at most its k: the format's packing of a fold's fresh table
                  (Fmt/M1Fold.lean: freshRow) reads of the coefficients none but those of the
                  variables 1 to k at the degrees 1 and 2, and the constant: two families of
                  coefficients that agree on these give the same row
  tail_same       the main rows' tails, over the extension field
  pad_same        the pad of a message that carries a vector and has no mask row
  maskTail_same   the mask rows' tails of a message of mask rows alone on which no table rides
  maskStart_ride  at a message without main rows and without an answer, maskStart
                  (Honest/K1/MaskLaw.lean) is the number at which the message's coins of the
                  extension field begin; spent at a riding table
  ride_same       **the entries of a riding table**, where its h is at most its k: AN EQUATION
                  BETWEEN TWO TEXTS THAT CALL ONE PACKING: no law on how the coins of a table of
                  more than one row are laid
  rideTail_same   its rows' tails
  holds_u_via, holds_omega_via   **at the two calls: the fields of holds2**
                  (Honest/K14/Holds2.lean) **that the honest rows read** (sendsU and sendsOmega,
                  Johnson/Desc/K14/Honest/SendMoves.lean) **are the entries of the term rowsR at
                  the call**, at the coins that the book lends it, BELOW THE ROWS' COUNTS AND THE
                  CODES' LENGTHS (beyond them the two sides part, and nothing reads there): o_u's
                  tails and pad, the first mask's entries and tails; o_omega's tails and pad,
                  o_sp's entries and tails. (Two remarks by reading, which no statement bears. What
                  ShowsU and ShowsO (Honest/K14/Exchange2.lean) say hangs, of these, on the two pads
                  and o_sp's entries alone, though by type both are handed whole what the prover
                  holds. The fields pad and tail of what is held for the first mask and for o_sp
                  (cMask, cSp) are read by no honest row. Of these four fields nothing is said here;
                  nor of the fields mask and maskTail of what is held for o_u and o_omega (cU,
                  cOmega), which under SendShapes have no mask row.)

What is assumed. In the general statements: the message's coins in the two texts are the same by
number, as in SendingsViaRows.lean; for ride_same in the coded form, at the 2 k + 1 first of them.
On the shape: as each statement names it. At the calls: Plan2, SendShapes, that the book lends to
the call's lifted part, and for "send o_u" sendFits (for h ≤ k). The calls stand at ⟨Q, 0, n⟩
(ViaPub, Honest/K14/SendingsVia.lean): 0: "LIN point" is the chain's round number 0; n: the number
that o_u gets among the statement's messages: no premise on it.
What is not claimed. No law of a distribution. That a call returns: where sendFits rejects, the part
returns an error and lays nothing; these are sentences on the term rowsR. That a number lies below
the count, but for the riding table's 2 k + 1. Nothing on symbols or columns. Nothing on a
verifier's decision, on soundness or on hiding.
-/
import Johnson.Desc.ProofFile.Honest.K14.SendingsViaCounts
import Johnson.Desc.ProofFile.Honest.K1.RideLaw
import Johnson.Desc.ProofFile.Honest.K1.RideOne

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes (E zeroE Codes OracleShape OracleNotice)
open OnBytes.Slice (GE GF rdE rdE_val readE readE_ofTriple toE toE_ofE ofE)
open VerifiableInference.Desc (K1.Par)
open Johnson.Prover.Send (Rows shapeAt)
open ProofFile.Honest.K1 (Ride rowsR startR dueR ce maskStart)

/-- A part's coin below its count, as the program's element. -/
theorem coded_coin {d : Due} (c : Cs d) (j : Nat) (hj : j < d.e) :
    (coinsE c).toArray.getD j zeroE = E.ofTriple (ofE (ce c j)) := by
  unfold coinsE ce
  rw [dif_pos hj]
  simp [Array.getD_eq_getD_getElem?, hj]

/-- **What the packing reads of the coefficients, where h ≤ k (hh)**: two families of coefficients
that agree at the variables 1 to k at the degrees 1 and 2 (hw) and in the constant (h0) give the
same row number b. -/
theorem freshRow_same (f : Fmt.Fld) (k h : Nat) (U U' : Fmt.M1.FoldOwn.Hide) (b : Nat)
    (hh : h ≤ k) (hw : ∀ l, 1 ≤ l → l ≤ k → ∀ t, t = 1 ∨ t = 2 → U.w l t = U'.w l t)
    (h0 : U.w0 = U'.w0) :
    Fmt.M1.FoldOwn.freshRow f k h U b = Fmt.M1.FoldOwn.freshRow f k h U' b := by
  have e1 : ∀ (n : Nat), n ≤ h → ∀ s : Fmt.Ext3,
      (List.range n).foldl (fun s i => if Fmt.M1.FoldOwn.reaches h b (i + 1) then
        f.addE s (U.w (i + 1) 1) else s) s =
      (List.range n).foldl (fun s i => if Fmt.M1.FoldOwn.reaches h b (i + 1) then
        f.addE s (U'.w (i + 1) 1) else s) s := by
    intro n
    induction n with
    | zero => intro _ _; rfl
    | succ n ih =>
      intro hn s
      rw [List.range_succ, List.foldl_append, List.foldl_append, ih (by omega) s]
      show (if _ then f.addE _ (U.w (n + 1) 1) else _) =
        (if _ then f.addE _ (U'.w (n + 1) 1) else _)
      rw [hw (n + 1) (by omega) (by omega) 1 (Or.inl rfl)]
  have e2 : ((List.range h).map fun i => if Fmt.M1.FoldOwn.reaches h b (i + 1) then U.w (i + 1) 2
      else Fmt.Fld.zeroE) = (List.range h).map fun i =>
        if Fmt.M1.FoldOwn.reaches h b (i + 1) then U'.w (i + 1) 2 else Fmt.Fld.zeroE :=
    List.map_congr_left fun i hi => by
      rw [hw (i + 1) (by omega) (by have := List.mem_range.1 hi; omega) 2 (Or.inr rfl)]
  have e3 : ((List.range (k - h - 1)).flatMap fun i => [U.w (h + 2 + i) 1, U.w (h + 2 + i) 2]) =
      (List.range (k - h - 1)).flatMap fun i => [U'.w (h + 2 + i) 1, U'.w (h + 2 + i) 2] :=
    List.flatMap_congr fun i hi => by
      have := List.mem_range.1 hi
      rw [hw (h + 2 + i) (by omega) (by omega) 1 (Or.inl rfl),
        hw (h + 2 + i) (by omega) (by omega) 2 (Or.inr rfl)]
  unfold Fmt.M1.FoldOwn.freshRow
  rw [e1 h (Nat.le_refl h), e2, e3, h0]
  by_cases hk : h < k
  · rw [if_pos hk, if_pos hk, if_pos hk, if_pos hk, hw (h + 1) (by omega) (by omega) 1 (Or.inl rfl),
      hw (h + 1) (by omega) (by omega) 2 (Or.inr rfl)]
  · rw [if_neg hk, if_neg hk, if_neg hk, if_neg hk]

variable (P : K1.Par) (ride : Nat → Option Ride)
  (data : Nat → Nat → Nat → Option (GF ⊕ GE)) (c : Cs (dueR P ride)) (k : Nat)

/-- **The main rows' tails**, over the extension field. -/
theorem tail_same (high : Bool) (v cs : Nat → E) (h3 : (shapeAt P k).mainDeg = 3)
    (hcs : ∀ i, rdE.val (cs i) = ce c ((startR P ride k).e + i)) (r q : Nat)
    (hr : r < (shapeAt P k).mainRows)
    (hq : q < (P.codes.base.getD (shapeAt P k).code default).r) :
    (rowsR P ride data c k).mainTlE r q =
      rdE.val ((laid P.codes (shapeAt P k) v cs (.plain high)).mainTail r q) := by
  rw [ProofFile.Honest.K1.tail_coin_e P ride data c k r q (by rw [h3]; rfl) hr hq]
  show _ = rdE.val (cs (r * (P.codes.base.getD (shapeAt P k).code default).r + q))
  rw [hcs, Nat.add_assoc]

/-- **The pad** of a message that carries a vector and has no mask row: the place of the answer
number i, whatever the data. -/
theorem pad_same (cs : Nat → E) (h3 : (shapeAt P k).mainDeg = 3)
    (hz : (shapeAt P k).maskRows = 0) (hm : 0 < (shapeAt P k).mainRows)
    (hlen : (shapeAt P k).answers ≤ (P.codes.base.getD (shapeAt P k).code default).ell)
    (hcs : ∀ i, rdE.val (cs i) = ce c ((startR P ride k).e + i)) (i : Nat)
    (hi : i < (shapeAt P k).answers) :
    (rowsR P ride data c k).mainE ((shapeAt P k).mainRows - 1)
        ((P.codes.base.getD (shapeAt P k).code default).ell - (shapeAt P k).answers + i) =
      (readCoins P.codes (shapeAt P k) cs).pad i := by
  have ha : (shapeAt P k).answers ≠ 0 := by omega
  have hpad := pad_count P.codes (shapeAt P k) (ride k) h3 hz ha
  have e := ProofFile.Honest.K1.pad_coin_e P ride data c k i (by rw [h3]; rfl) ha hm
    (by rw [hpad]; exact hlen) (by rw [hpad]; exact hi)
  rw [hpad] at e
  rw [e]
  show _ = rdE.val (cs ((shapeAt P k).mainRows *
    (P.codes.base.getD (shapeAt P k).code default).r + i))
  rw [hcs]
  rfl

/-- **The mask rows' tails** of a message of mask rows alone, on which no table rides. -/
theorem maskTail_same (high : Bool) (v cs : Nat → E) (hm : (shapeAt P k).mainRows = 0)
    (hz : (shapeAt P k).maskRows ≠ 0) (hride : ride k = none)
    (hcs : ∀ i, rdE.val (cs i) = ce c ((startR P ride k).e + i)) (r q : Nat)
    (hr : r < (shapeAt P k).maskRows)
    (hq : q < (P.codes.mask.getD (shapeAt P k).maskCode default).r) :
    (rowsR P ride data c k).maskTl r q =
      rdE.val ((laid P.codes (shapeAt P k) v cs (.plain high)).maskTail r q) := by
  rw [ProofFile.Honest.K1.maskTail_coin P ride data c k r q hr hq, maskStart_noMain P ride k hm hz]
  have hzb : ((shapeAt P k).maskRows == 0) = false := beq_eq_false_iff_ne.2 hz
  show _ = rdE.val (cs ((shapeAt P k).mainRows * _ +
    (if (shapeAt P k).maskRows == 0 then _ else 0) +
    (shapeAt P k).maskRows * (P.codes.mask.getD (shapeAt P k).maskCode default).ell +
    r * (P.codes.mask.getD (shapeAt P k).maskCode default).r + q))
  rw [hcs, hm, hzb]
  congr 1
  simp [ProofFile.Honest.K1.stepsOf, hride, Nat.add_assoc]

/-- Where a table rides on a message without main rows and without an answer, its coins begin where
the message's coins begin. -/
theorem maskStart_ride (hm : (shapeAt P k).mainRows = 0) (ha : (shapeAt P k).answers = 0) :
    maskStart P ride k = (startR P ride k).e := by
  simp [maskStart, ProofFile.Honest.K1.Steps.main, ProofFile.Honest.K1.stepsOf, hm, ha]

/-- **The entries of a riding table** of k' variables in 2 ^ h rows, h ≤ k'. (k is the message's
number.) -/
theorem ride_same (k' h : Nat) (v cs : Nat → E) (hride : ride k = some ⟨k', h⟩) (hh : h ≤ k')
    (hm : (shapeAt P k).mainRows = 0) (ha : (shapeAt P k).answers = 0)
    (hcs : ∀ i, i < 2 * k' + 1 → cs i = E.ofTriple (ofE (ce c ((startR P ride k).e + i))))
    (r j : Nat) (hr : r < (shapeAt P k).maskRows)
    (hj : j < (P.codes.mask.getD (shapeAt P k).maskCode default).ell) :
    (rowsR P ride data c k).mask r j =
      rdE.val ((laid P.codes (shapeAt P k) v cs (.fresh k' h)).mask r j) := by
  rw [ProofFile.Honest.K1.ride_coin P ride data c k r j ⟨k', h⟩ hride hr hj,
    maskStart_ride P ride k hm ha]
  show toE ((Fmt.M1.FoldOwn.freshRow .two k' h _ r).getD j Fmt.Fld.zeroE) =
    rdE.val (E.ofTriple ((Fmt.M1.FoldOwn.freshRow .two k' h _ r).getD j Fmt.Fld.zeroE))
  rw [rdE_val, readE_ofTriple]
  congr 2
  refine freshRow_same .two k' h _ _ r hh (fun l h1 hl t ht => ?_) ?_
  · have hi : (if l < k' then 2 * (l - 1) + (t - 1) else 2 * (k' - 1) + t) < 2 * k' + 1 := by
      split <;> rcases ht with rfl | rfl <;> omega
    show ofE (if (if l < k' then 2 * (l - 1) + (t - 1) else 2 * (k' - 1) + t) < 2 * k' + 1 then
        ce c ((startR P ride k).e + (if l < k' then 2 * (l - 1) + (t - 1) else 2 * (k' - 1) + t))
      else 0) = (cs (if l < k' then 2 * (l - 1) + (t - 1) else 2 * (k' - 1) + t)).triple
    rw [if_pos hi, hcs _ hi]
    rfl
  · have hi : 2 * (k' - 1) < 2 * k' + 1 := by omega
    show ofE (if 2 * (k' - 1) < 2 * k' + 1 then ce c ((startR P ride k).e + 2 * (k' - 1)) else 0) =
      (cs (2 * (k' - 1))).triple
    rw [if_pos hi, hcs _ hi]
    rfl

/-- **A riding table's rows' tails.** -/
theorem rideTail_same (k' h : Nat) (v cs : Nat → E) (hride : ride k = some ⟨k', h⟩)
    (hm : (shapeAt P k).mainRows = 0) (ha : (shapeAt P k).answers = 0)
    (hcs : ∀ i, rdE.val (cs i) = ce c ((startR P ride k).e + i)) (r q : Nat)
    (hr : r < (shapeAt P k).maskRows)
    (hq : q < (P.codes.mask.getD (shapeAt P k).maskCode default).r) :
    (rowsR P ride data c k).maskTl r q =
      rdE.val ((laid P.codes (shapeAt P k) v cs (.fresh k' h)).maskTail r q) := by
  rw [ProofFile.Honest.K1.maskTail_coin P ride data c k r q hr hq, maskStart_ride P ride k hm ha]
  show _ = rdE.val (cs (2 * k' + 1 +
    r * (P.codes.mask.getD (shapeAt P k).maskCode default).r + q))
  rw [hcs]
  congr 1
  simp [ProofFile.Honest.K1.stepsOf, ProofFile.Honest.K1.Ride.count, hride, Nat.add_assoc]

/-! ## At the two calls: the fields of holds2 -/

section AtCalls
open OnBytes.Params
open Desc.K14 (P14)
open Desc.K14.Honest

variable {Bk : ProverCoinCounts} {W₀ Rc W X : Type} {Q : P14} {sentU : Array OracleNotice}
  {layO : OnBytes.TreeLay}

/-- **"send o_u": what holds2 says of o_u's tails and pad, and of the first mask's entries and
tails, are the entries of the term rowsR at the call**, at the coins that the book lends it;
whatever the data. (The proof treats both cases, with and without a first fold of the test on G_u.
By reading, the second cannot occur under Plan2: masks are sent ahead, and withU then returns only
where there is a first fold; no theorem is cited for it.) -/
theorem holds_u_via (hQ : Plan2 Q sentU layO) (hSh : SendShapes Q) (n : Nat)
    (hf : ProofFile.Honest.K1.sendFits (viaU ⟨Q, 0, n⟩).P (viaU ⟨Q, 0, n⟩).ride = true)
    (weights : W₀ → Weights) (rand : Rc → TableRand) (κ : Coins Bk)
    (w : Common W₀ Rc OnBytes.TableKey) (wit : W → Ask)
    {c : RowCoins [(liftSend wit (ProofFile.Honest.K1.sendPart (viaU ⟨Q, 0, n⟩)) : Part Empty W X)]}
    (hc : lendRow Bk (Bk.rowsOf 1) (κ.look 1) (sendPlace 2)
      [(liftSend wit (ProofFile.Honest.K1.sendPart (viaU ⟨Q, 0, n⟩)) : Part Empty W X)] 0 = .ok c)
    (data : Nat → Nat → Nat → Option (GF ⊕ GE)) :
    (∀ r q, r < (shapeAt (viaU ⟨Q, 0, n⟩).P 0).mainRows →
      q < (Q.codes.base.getD (shapeAt (viaU ⟨Q, 0, n⟩).P 0).code default).r →
      (rowsR (viaU ⟨Q, 0, n⟩).P (viaU ⟨Q, 0, n⟩).ride data c.1.1 0).mainTlE r q =
        (holds2 Q weights rand κ w).cU.tail r q) ∧
    (∀ i, i < (shapeAt (viaU ⟨Q, 0, n⟩).P 0).answers →
      (rowsR (viaU ⟨Q, 0, n⟩).P (viaU ⟨Q, 0, n⟩).ride data c.1.1 0).mainE
          ((shapeAt (viaU ⟨Q, 0, n⟩).P 0).mainRows - 1)
          ((Q.codes.base.getD (shapeAt (viaU ⟨Q, 0, n⟩).P 0).code default).ell -
            (shapeAt (viaU ⟨Q, 0, n⟩).P 0).answers + i) =
        (holds2 Q weights rand κ w).cU.pad i) ∧
    (∀ r j, r < (shapeAt (viaU ⟨Q, 0, n⟩).P 1).maskRows →
      j < (Q.codes.mask.getD (shapeAt (viaU ⟨Q, 0, n⟩).P 1).maskCode default).ell →
      (rowsR (viaU ⟨Q, 0, n⟩).P (viaU ⟨Q, 0, n⟩).ride data c.1.1 1).mask r j =
        (holds2 Q weights rand κ w).cMask.mask r j) ∧
    ∀ r q, r < (shapeAt (viaU ⟨Q, 0, n⟩).P 1).maskRows →
      q < (Q.codes.mask.getD (shapeAt (viaU ⟨Q, 0, n⟩).P 1).maskCode default).r →
      (rowsR (viaU ⟨Q, 0, n⟩).P (viaU ⟨Q, 0, n⟩).ride data c.1.1 1).maskTl r q =
        (holds2 Q weights rand κ w).cMask.maskTail r q := by
  have gU : Desc.K14.withU Q.S = some sentU := hQ.facts.goes
  have sU : (viaU ⟨Q, 0, n⟩).P.sent = sentU := by
    have e : (viaU ⟨Q, 0, n⟩).P.sent = (Desc.K14.withU Q.S).getD #[] :=
      Desc.K14.Law.parK1_sent Q 2 _ _
    rw [e, gU, Option.getD_some]
  have hsz : (viaU ⟨Q, 0, n⟩).P.sent.size = 2 := by rw [sU]; exact hQ.facts.goesTwo
  have hs0 : shapeAt (viaU ⟨Q, 0, n⟩).P 0 = Q.S.fold.u := u_first Q 0 gU
  have hm1 : (shapeAt (viaU ⟨Q, 0, n⟩).P 1).mainRows = 0 := hSh.mask
  have ha1 : (shapeAt (viaU ⟨Q, 0, n⟩).P 1).answers = 0 := by
    show ((viaU ⟨Q, 0, n⟩).P.sent.getD 1 default).shape.answers = 0
    rw [sU]
    exact firstMask_noAnswer gU
  have hlin := (VerifiableInference.Desc.Own.linFits_iff Q.codes Q.S).1 hQ.facts.lin
  have ha0 : (shapeAt (viaU ⟨Q, 0, n⟩).P 0).answers ≠ 0 := by
    rw [hs0]
    have h1 : 1 ≤ Q.S.fold.u.answers := hlin.1.1.2.2.2.2.1
    omega
  have h30 : (shapeAt (viaU ⟨Q, 0, n⟩).P 0).mainDeg = 3 := by rw [hs0]; exact hSh.u.overE
  have hz0 : (shapeAt (viaU ⟨Q, 0, n⟩).P 0).maskRows = 0 := by rw [hs0]; exact hSh.u.noMask
  have hcm := coins_msg κ (jobU ⟨Q, 0⟩) (sendPlace 2) hc
  have st1 : (startR (viaU ⟨Q, 0, n⟩).P (viaU ⟨Q, 0, n⟩).ride 1).e =
      offsetOf (jobU ⟨Q, 0⟩).Q.codes (jobU ⟨Q, 0⟩).Q.sent (jobU ⟨Q, 0⟩).sort 1 :=
    start_one (viaU ⟨Q, 0, n⟩).P (viaU ⟨Q, 0, n⟩).ride (jobU ⟨Q, 0⟩).sort Q.S.fold.rowsHigh
      (by omega) rfl rfl h30 hz0 ha0
  have r0 : ∀ i, rdE.val (msgCoins (jobU ⟨Q, 0⟩) (coinsE c.1.1).toArray 0 i) =
      ce c.1.1 ((startR (viaU ⟨Q, 0, n⟩).P (viaU ⟨Q, 0, n⟩).ride 0).e + i) := fun i =>
    val_coinsE c.1.1 (0 + i)
  have r1 : ∀ i, rdE.val (msgCoins (jobU ⟨Q, 0⟩) (coinsE c.1.1).toArray 1 i) =
      ce c.1.1 ((startR (viaU ⟨Q, 0, n⟩).P (viaU ⟨Q, 0, n⟩).ride 1).e + i) := fun i => by
    rw [st1]
    exact val_coinsE c.1.1 _
  refine ⟨fun r q hr hq => ?_, fun i hi => ?_, ?_⟩
  · rw [tail_same (viaU ⟨Q, 0, n⟩).P (viaU ⟨Q, 0, n⟩).ride data c.1.1 0 false (fun _ => zeroE)
      (msgCoins (jobU ⟨Q, 0⟩) (coinsE c.1.1).toArray 0) h30 r0 r q hr hq, ← hcm 0]
    rfl
  · have e := pad_same (viaU ⟨Q, 0, n⟩).P (viaU ⟨Q, 0, n⟩).ride data c.1.1 0
      (msgCoins (jobU ⟨Q, 0⟩) (coinsE c.1.1).toArray 0) h30 hz0 (by rw [hs0]; exact hSh.u.main)
      (by rw [hs0]; exact hSh.u.room) r0 i hi
    rw [← hcm 0] at e
    exact e
  · cases hh : Q.S.testU.head? with
    | none =>
      have hride : (viaU ⟨Q, 0, n⟩).ride 1 = none := by
        show (Q.S.testU.head?.map fun s => ({ k := s.k, h := s.h } : Ride)) = none
        rw [hh]
        rfl
      have hM : (holds2 Q weights rand κ w).cMask =
          readCoins Q.codes ((jobU ⟨Q, 0⟩).Q.sent.getD 1 default).shape
            (coinsOfMsg κ (jobU ⟨Q, 0⟩) (sendPlace 2) 1) := by
        unfold holds2
        simp only [hh]
      refine ⟨fun r j hr hj => ?_, fun r q hr hq => ?_⟩
      · rw [mask_same (viaU ⟨Q, 0, n⟩).P (viaU ⟨Q, 0, n⟩).ride data c.1.1 1 false
          (fun _ => zeroE) (msgCoins (jobU ⟨Q, 0⟩) (coinsE c.1.1).toArray 1) hm1 (by omega) hride
          r1 r j hr hj, ← hcm 1, hM]
        rfl
      · rw [maskTail_same (viaU ⟨Q, 0, n⟩).P (viaU ⟨Q, 0, n⟩).ride data c.1.1 1 false
          (fun _ => zeroE) (msgCoins (jobU ⟨Q, 0⟩) (coinsE c.1.1).toArray 1) hm1 (by omega) hride
          r1 r q hr hq, ← hcm 1, hM]
        rfl
    | some s =>
      have hride : (viaU ⟨Q, 0, n⟩).ride 1 = some ⟨s.k, s.h⟩ := by
        show (Q.S.testU.head?.map fun s => ({ k := s.k, h := s.h } : Ride)) = _
        rw [hh]
        rfl
      have hM : (holds2 Q weights rand κ w).cMask =
          readFresh Q.codes ((jobU ⟨Q, 0⟩).Q.sent.getD 1 default).shape
            (coinsOfMsg κ (jobU ⟨Q, 0⟩) (sendPlace 2) 1) s.k s.h := by
        unfold holds2
        simp only [hh]
      have hfit := ProofFile.Honest.K1.fits_ride (viaU ⟨Q, 0, n⟩).P (viaU ⟨Q, 0, n⟩).ride 1 ⟨s.k, s.h⟩ hf
        (by omega) hride
      have hle : s.h ≤ s.k := by
        simp only [ProofFile.Honest.K1.rideFits, Bool.and_eq_true, decide_eq_true_eq] at hfit
        exact hfit.1.1.2
      have hroom : ∀ i, i < 2 * s.k + 1 →
          (startR (viaU ⟨Q, 0, n⟩).P (viaU ⟨Q, 0, n⟩).ride 1).e + i <
            (dueR (viaU ⟨Q, 0, n⟩).P (viaU ⟨Q, 0, n⟩).ride).e := fun i hi => by
        have e : dueR (viaU ⟨Q, 0, n⟩).P (viaU ⟨Q, 0, n⟩).ride =
            (startR (viaU ⟨Q, 0, n⟩).P (viaU ⟨Q, 0, n⟩).ride 1).plus
              (ProofFile.Honest.K1.dueMsg (viaU ⟨Q, 0, n⟩).P.codes (shapeAt (viaU ⟨Q, 0, n⟩).P 1)
                ((viaU ⟨Q, 0, n⟩).ride 1)) := by
          unfold dueR
          rw [hsz]
          exact ProofFile.Honest.K1.startR_succ _ _ 1
        rw [e, hride, due_ride _ _ s.k s.h hm1 ha1]
        show _ < _ + (2 * s.k + 1 + _)
        omega
      refine ⟨fun r j hr hj => ?_, fun r q hr hq => ?_⟩
      · rw [ride_same (viaU ⟨Q, 0, n⟩).P (viaU ⟨Q, 0, n⟩).ride data c.1.1 1 s.k s.h
          (fun _ => zeroE) (msgCoins (jobU ⟨Q, 0⟩) (coinsE c.1.1).toArray 1) hride hle hm1 ha1
          (fun i hi => by
            have hb := hroom i hi
            rw [st1] at hb ⊢
            exact coded_coin c.1.1 _ hb) r j hr hj, ← hcm 1, hM]
        rfl
      · rw [rideTail_same (viaU ⟨Q, 0, n⟩).P (viaU ⟨Q, 0, n⟩).ride data c.1.1 1 s.k s.h
          (fun _ => zeroE) (msgCoins (jobU ⟨Q, 0⟩) (coinsE c.1.1).toArray 1) hride hm1 ha1 r1 r q
          hr hq, ← hcm 1, hM]
        rfl

/-- **"send o_omega": what holds2 says of o_omega's tails and pad, and of o_sp's entries and tails,
are the entries of the term rowsR at the call**, at the coins that the book lends it; whatever the
data. -/
theorem holds_omega_via (hQ : Plan2 Q sentU layO) (hSh : SendShapes Q) (n : Nat)
    (weights : W₀ → Weights) (rand : Rc → TableRand) (κ : Coins Bk)
    (w : Common W₀ Rc OnBytes.TableKey) (wit : W → Ask)
    {c : RowCoins [(liftSend wit (ProofFile.Honest.K1.sendPart (viaOmega ⟨Q, 0, n⟩)) : Part Empty W X)]}
    (hc : lendRow Bk (Bk.rowsOf 1) (κ.look 1) (sendPlace 5)
      [(liftSend wit (ProofFile.Honest.K1.sendPart (viaOmega ⟨Q, 0, n⟩)) : Part Empty W X)] 0 = .ok c)
    (data : Nat → Nat → Nat → Option (GF ⊕ GE)) :
    (∀ r q, r < Q.S.omega.mainRows → q < (Q.codes.base.getD Q.S.omega.code default).r →
      (rowsR (viaOmega ⟨Q, 0, n⟩).P (viaOmega ⟨Q, 0, n⟩).ride data c.1.1 0).mainTlE r q =
        (holds2 Q weights rand κ w).cOmega.tail r q) ∧
    (∀ i, i < Q.S.omega.answers →
      (rowsR (viaOmega ⟨Q, 0, n⟩).P (viaOmega ⟨Q, 0, n⟩).ride data c.1.1 0).mainE
          (Q.S.omega.mainRows - 1)
          ((Q.codes.base.getD Q.S.omega.code default).ell - Q.S.omega.answers + i) =
        (holds2 Q weights rand κ w).cOmega.pad i) ∧
    (∀ r j, r < Q.S.sharedSplit.maskRows →
      j < (Q.codes.mask.getD Q.S.sharedSplit.maskCode default).ell →
      (rowsR (viaOmega ⟨Q, 0, n⟩).P (viaOmega ⟨Q, 0, n⟩).ride data c.1.1 1).mask r j =
        (holds2 Q weights rand κ w).cSp.mask r j) ∧
    ∀ r q, r < Q.S.sharedSplit.maskRows →
      q < (Q.codes.mask.getD Q.S.sharedSplit.maskCode default).r →
      (rowsR (viaOmega ⟨Q, 0, n⟩).P (viaOmega ⟨Q, 0, n⟩).ride data c.1.1 1).maskTl r q =
        (holds2 Q weights rand κ w).cSp.maskTail r q := by
  obtain ⟨w2, w0, w1⟩ := withOmega_two hQ.facts.two
  have sO : (viaOmega ⟨Q, 0, n⟩).P.sent = Desc.K14.withOmega Q.S :=
    Desc.K14.Law.parK1_sent Q 5 _ _
  have w2' : (Desc.K14.withOmega Q.S).size = 2 := w2
  have hs0 : shapeAt (viaOmega ⟨Q, 0, n⟩).P 0 = Q.S.omega := omega_first Q 0
  have hs1 : shapeAt (viaOmega ⟨Q, 0, n⟩).P 1 = Q.S.sharedSplit :=
    (shapeAt_of_get (viaOmega ⟨Q, 0, n⟩).P 1 ⟨Q.par.S.sharedSplit, Q.par.S.sharedSplitLeafClass⟩
      (by rw [sO]; exact w1)).1
  have hlin := (VerifiableInference.Desc.Own.linFits_iff Q.codes Q.S).1 hQ.facts.lin
  have ha0 : (shapeAt (viaOmega ⟨Q, 0, n⟩).P 0).answers ≠ 0 := by
    rw [hs0]
    have h1 : 1 ≤ Q.S.omega.answers := hlin.1.2.2.2.2.2.2.1.2.2.2
    omega
  have h30 : (shapeAt (viaOmega ⟨Q, 0, n⟩).P 0).mainDeg = 3 := by rw [hs0]; exact hSh.omega.overE
  have hz0 : (shapeAt (viaOmega ⟨Q, 0, n⟩).P 0).maskRows = 0 := by
    rw [hs0]
    exact hSh.omega.noMask
  have hm1 : (shapeAt (viaOmega ⟨Q, 0, n⟩).P 1).mainRows = 0 := by rw [hs1]; exact sp_noMain hQ
  have hcm := coins_msg κ (jobOmega ⟨Q, 0⟩) (sendPlace 5) hc
  have st1 : (startR (viaOmega ⟨Q, 0, n⟩).P (viaOmega ⟨Q, 0, n⟩).ride 1).e =
      offsetOf (jobOmega ⟨Q, 0⟩).Q.codes (jobOmega ⟨Q, 0⟩).Q.sent (jobOmega ⟨Q, 0⟩).sort 1 :=
    start_one (viaOmega ⟨Q, 0, n⟩).P (viaOmega ⟨Q, 0, n⟩).ride (jobOmega ⟨Q, 0⟩).sort
      Q.S.omegaRowsHigh (by rw [sO, w2']; exact Nat.zero_lt_two) rfl rfl h30 hz0 ha0
  have r0 : ∀ i, rdE.val (msgCoins (jobOmega ⟨Q, 0⟩) (coinsE c.1.1).toArray 0 i) =
      ce c.1.1 ((startR (viaOmega ⟨Q, 0, n⟩).P (viaOmega ⟨Q, 0, n⟩).ride 0).e + i) := fun i =>
    val_coinsE c.1.1 (0 + i)
  have r1 : ∀ i, rdE.val (msgCoins (jobOmega ⟨Q, 0⟩) (coinsE c.1.1).toArray 1 i) =
      ce c.1.1 ((startR (viaOmega ⟨Q, 0, n⟩).P (viaOmega ⟨Q, 0, n⟩).ride 1).e + i) := fun i => by
    rw [st1]
    exact val_coinsE c.1.1 _
  refine ⟨fun r q hr hq => ?_, fun i hi => ?_, fun r j hr hj => ?_, fun r q hr hq => ?_⟩
  · rw [tail_same (viaOmega ⟨Q, 0, n⟩).P (viaOmega ⟨Q, 0, n⟩).ride data c.1.1 0 false
      (fun _ => zeroE) (msgCoins (jobOmega ⟨Q, 0⟩) (coinsE c.1.1).toArray 0) h30 r0 r q
      (by rw [hs0]; exact hr) (by rw [hs0]; exact hq), ← hcm 0, hs0]
    rfl
  · have e := pad_same (viaOmega ⟨Q, 0, n⟩).P (viaOmega ⟨Q, 0, n⟩).ride data c.1.1 0
      (msgCoins (jobOmega ⟨Q, 0⟩) (coinsE c.1.1).toArray 0) h30 hz0
      (by rw [hs0]; exact hSh.omega.main) (by rw [hs0]; exact hSh.omega.room) r0 i
      (by rw [hs0]; exact hi)
    rw [hs0, ← hcm 0] at e
    exact e
  · rw [mask_same (viaOmega ⟨Q, 0, n⟩).P (viaOmega ⟨Q, 0, n⟩).ride data c.1.1 1 false
      (fun _ => zeroE) (msgCoins (jobOmega ⟨Q, 0⟩) (coinsE c.1.1).toArray 1) hm1
      (by rw [hs1]; omega) rfl r1 r j (by rw [hs1]; exact hr) (by rw [hs1]; exact hj), ← hcm 1,
      hs1]
    rfl
  · rw [maskTail_same (viaOmega ⟨Q, 0, n⟩).P (viaOmega ⟨Q, 0, n⟩).ride data c.1.1 1 false
      (fun _ => zeroE) (msgCoins (jobOmega ⟨Q, 0⟩) (coinsE c.1.1).toArray 1) hm1
      (by rw [hs1]; omega) rfl r1 r q (by rw [hs1]; exact hr) (by rw [hs1]; exact hq), ← hcm 1,
      hs1]
    rfl

end AtCalls

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.coded_coin
#print axioms ProofFile.Honest.K14.freshRow_same
#print axioms ProofFile.Honest.K14.tail_same
#print axioms ProofFile.Honest.K14.pad_same
#print axioms ProofFile.Honest.K14.maskTail_same
#print axioms ProofFile.Honest.K14.maskStart_ride
#print axioms ProofFile.Honest.K14.ride_same
#print axioms ProofFile.Honest.K14.rideTail_same
#print axioms ProofFile.Honest.K14.holds_u_via
#print axioms ProofFile.Honest.K14.holds_omega_via
