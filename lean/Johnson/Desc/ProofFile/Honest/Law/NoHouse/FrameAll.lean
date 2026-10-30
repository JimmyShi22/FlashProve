-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Law/NoHouse/FrameAll.lean: the four conditions that the first chain's
invariant has to meet at a sub-protocol (`PlaysS`, `BehindS`, `ExchangeS`, `RidesPastS`,
Thread/PaysS.lean), at each of the 77 sub-protocols of the kind `frame` at the full size. The
invariant is `lettersHead` (Thread/FirstHead.lean) with the rider clauses `csHead`
(Thread/CsHead.lean), `keeps` given kind by kind (`kpBy f`, Thread/KeepsBy.lean) and the condition
`SaidOk` (Thread/SaidOk.lean). It is named `L`, under an equation `hL`, as in `owesS_head_form`
(Thread/GatherHeadForm.lean). The file joins the lemmas of FrameOwes.lean, PileCleared.lean,
FrameRiders.lean, FrameCells.lean and RideOkFrame.lean. No definition.

  1  `frame_rides`   `RidesPastS` at a sub-protocol whose place is of the kind `frame`, for every
     `Rd` and `Said`
  2  `frame_all_front`, `frame_all_laid`, `frame_all_behind`, `frame_all_cleared`,
     `frame_all_seal`   **the four conditions** at the numbers 0, `14 * l + 1`,
     `14 * l + IM.nAt l + 3`, `P1L20.clearIx l` (which is `14 * l + IM.nAt l + 7`) and 357

What stays a hypothesis.
  * `hfF`: the clause of the kind `frame` is `keepsFrame P5J.At.links P1L20.bearing`. `fHead_frame`
    (Thread/FHead.lean) proves it for `fHead` at `take := P1L20.bearing`. That file is not used
    here.
  * `noHalf`: the prover has no side at a place of the kind `frame`.
  * `hb₀`: the border after the sub-protocol that hears the reply is 339.
  * `hcarry`: the invariant's argument `carryX` passes over these sub-protocols, at any strings.
    `carryX` has no text yet.
  * `htst`, after a batching: where the step accepts, the invariant's argument `test` does not fire.

Limits.
  * Nothing shows that the invariant holds at any state.
  * That any of these sub-protocols accepts is not shown here.
  * About the list `csHead` alone. A longer list of rider clauses needs FrameRiders.lean anew.
  * Full size only, under the library's `AtMgA` at the hash function `secondHashFunction`.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.PileCleared
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.FrameRiders
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.FrameCells
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.KeepsFrameStep

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place KindName)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.ChainEnd (sealRound)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)

section
variable (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
  (f : KindName → Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
  (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)

/-- `RidesPastS` at a sub-protocol whose place is of the kind `frame`. -/
theorem frame_rides (hfF : f KindName.frame = keepsFrame P5J.At.links P1L20.bearing)
    (hcarry : ∀ b p, P5J.At.ps[b]? = some p → p.kind = KindName.frame → ∀ m s s',
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread.keeps b s s' →
      ∀ (z : ProofFile.InstPub) (y y' : Strs) (v : WtF), carryX m (z, s) y v → carryX m (z, s') y' v)
    {b : Nat} {blk : VerifiableInference.Desc.Block TS ProofFile.Cl} (hblk : cF.blocksInOrder[b]? = some blk)
    (hk : blk.place.kind = KindName.frame) :
    RidesPastS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread Said b := by
  have hp := head_place h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w (b := b) (blk := blk) hblk
  exact ridesPastS_shares _ _ fun i hi h1 h2 =>
    frame_cellsS h H Q test carryX item n₁ n₂ b₀ Vd Rd f w Said hfF hcarry b _ i hp hk
      (head_ok_at h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w rideOkF rideOkF_onePass hp hi h1
        h2)

end

variable (ν : Nat) (st : Nat → TS → Prop) (R : Nat → Option OnBytes.Model.Forest.Heard → Prop)
  (f : KindName → Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)

include h in
/-- A sub-protocol stands at every number below 358. -/
theorem flat_at {b : Nat} (hb : b < 358) : ∃ blk, cF.blocksInOrder[b]? = some blk := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have e : cF.blocksInOrder.length = 358 := Meaning.Carry.flat_len h.scope h.reads O
  exact ⟨_, List.getElem?_eq_getElem (by omega)⟩

/-- **At number 0.** -/
theorem frame_all_front
    {L : Letters Bk ProofFile.Cl W₀ Rc ProofFile.Inst Tr X ProofFile.InstPub (CellsM OnBytes.Flat.numsFull)
      P5J.At.Tok MsgT}
    (hL : L = lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf (csHead ν st R)) (kpBy f) w)
    (hfF : f KindName.frame = keepsFrame P5J.At.links P1L20.bearing)
    (noHalf : ∀ g ∈ H.first, g.place.kind ≠ KindName.frame) (hb₀ : b₀ = 339)
    (hcarry : ∀ b p, P5J.At.ps[b]? = some p → p.kind = KindName.frame → ∀ m s s',
      L.thread.keeps b s s' →
      ∀ (z : ProofFile.InstPub) (y y' : Strs) (v : WtF), carryX m (z, s) y v → carryX m (z, s') y' v) :
    PlaysS L.thread SaidOk 0 ∧ BehindS L.thread SaidOk 0 ∧
      ExchangeS L.thread SaidOk 0 ∧ RidesPastS L.thread SaidOk 0 := by
  subst hL
  obtain ⟨blk, hblk⟩ := flat_at h (b := 0) (by omega)
  have hR := frame_rides h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf (csHead ν st R)) f w
    SaidOk hfF hcarry hblk ((frame_keeps_front h (take := P1L20.bearing) blk hblk).1)
  obtain ⟨a1, a2, a3⟩ := frame_owes_front h H Q test carryX item n₁ n₂ b₀ Vd
    (ridersOf (csHead ν st R)) f w SaidOk P1L20.bearing hfF noHalf (fun _ _ hS => hS)
    (by omega) riders_front hR
  exact ⟨a1, a2, a3, hR⟩

/-- **At the frame's step "laid" of segment `l`.** -/
theorem frame_all_laid
    {L : Letters Bk ProofFile.Cl W₀ Rc ProofFile.Inst Tr X ProofFile.InstPub (CellsM OnBytes.Flat.numsFull)
      P5J.At.Tok MsgT}
    (hL : L = lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf (csHead ν st R)) (kpBy f) w)
    (hfF : f KindName.frame = keepsFrame P5J.At.links P1L20.bearing)
    (noHalf : ∀ g ∈ H.first, g.place.kind ≠ KindName.frame) (hb₀ : b₀ = 339)
    (hcarry : ∀ b p, P5J.At.ps[b]? = some p → p.kind = KindName.frame → ∀ m s s',
      L.thread.keeps b s s' →
      ∀ (z : ProofFile.InstPub) (y y' : Strs) (v : WtF), carryX m (z, s) y v → carryX m (z, s') y' v)
    {l : Nat} (hl : l < 25) :
    PlaysS L.thread SaidOk (14 * l + 1) ∧ BehindS L.thread SaidOk (14 * l + 1) ∧
      ExchangeS L.thread SaidOk (14 * l + 1) ∧ RidesPastS L.thread SaidOk (14 * l + 1) := by
  subst hL
  obtain ⟨blk, hblk⟩ := flat_at h (b := 14 * l + 1) (by omega)
  have hR := frame_rides h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf (csHead ν st R)) f w
    SaidOk hfF hcarry hblk ((frame_keeps_laid h (take := P1L20.bearing) hl blk hblk).1)
  obtain ⟨a1, a2, a3⟩ := frame_owes_laid h H Q test carryX item n₁ n₂ b₀ Vd
    (ridersOf (csHead ν st R)) f w SaidOk P1L20.bearing hfF hl noHalf (fun _ _ hS => hS)
    (by omega) (riders_laid hl) hR
  exact ⟨a1, a2, a3, hR⟩

/-- **At the frame's step after the batching of segment `l`.** -/
theorem frame_all_behind
    {L : Letters Bk ProofFile.Cl W₀ Rc ProofFile.Inst Tr X ProofFile.InstPub (CellsM OnBytes.Flat.numsFull)
      P5J.At.Tok MsgT}
    (hL : L = lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf (csHead ν st R)) (kpBy f) w)
    (hfF : f KindName.frame = keepsFrame P5J.At.links P1L20.bearing)
    (noHalf : ∀ g ∈ H.first, g.place.kind ≠ KindName.frame) (hb₀ : b₀ = 339)
    (hcarry : ∀ b p, P5J.At.ps[b]? = some p → p.kind = KindName.frame → ∀ m s s',
      L.thread.keeps b s s' →
      ∀ (z : ProofFile.InstPub) (y y' : Strs) (v : WtF), carryX m (z, s) y v → carryX m (z, s') y' v)
    {l : Nat} (hl : l < 25)
    (htst : ∀ blk, cF.blocksInOrder[14 * l + IM.nAt l + 3]? = some blk → ∀ s rs cols s' n,
      blk.step 0 s rs cols = .ok (s', n) → test l s = none) :
    PlaysS L.thread SaidOk (14 * l + IM.nAt l + 3) ∧
      BehindS L.thread SaidOk (14 * l + IM.nAt l + 3) ∧
      ExchangeS L.thread SaidOk (14 * l + IM.nAt l + 3) ∧
      RidesPastS L.thread SaidOk (14 * l + IM.nAt l + 3) := by
  subst hL
  have hn' : l = 24 → IM.nAt l = 9 := fun e => by
    subst e
    exact nAt_head
  have hn'' : l < 24 → IM.nAt l = 7 := fun e => nAt_lt e
  obtain ⟨blk, hblk⟩ := flat_at h (b := 14 * l + IM.nAt l + 3) (by
    rcases Nat.lt_or_ge l 24 with e | e
    · have := hn'' e
      omega
    · have := hn' (by omega)
      omega)
  have hR := frame_rides h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf (csHead ν st R)) f w
    SaidOk hfF hcarry hblk ((frame_keeps_behind h (take := P1L20.bearing) hl blk hblk).1)
  obtain ⟨a1, a2, a3⟩ := frame_owes_behind h H Q test carryX item n₁ n₂ b₀ Vd
    (ridersOf (csHead ν st R)) f w SaidOk P1L20.bearing hfF hl noHalf htst (fun _ _ hS => hS)
    (by
      rcases Nat.lt_or_ge l 24 with e | e
      · have := hn'' e
        omega
      · have := hn' (by omega)
        omega) (riders_behind hl) hR
  exact ⟨a1, a2, a3, hR⟩

/-- **At the frame's step "cleared" of segment `l`.** -/
theorem frame_all_cleared
    {L : Letters Bk ProofFile.Cl W₀ Rc ProofFile.Inst Tr X ProofFile.InstPub (CellsM OnBytes.Flat.numsFull)
      P5J.At.Tok MsgT}
    (hL : L = lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf (csHead ν st R)) (kpBy f) w)
    (hfF : f KindName.frame = keepsFrame P5J.At.links P1L20.bearing)
    (noHalf : ∀ g ∈ H.first, g.place.kind ≠ KindName.frame) (hb₀ : b₀ = 339)
    (hcarry : ∀ b p, P5J.At.ps[b]? = some p → p.kind = KindName.frame → ∀ m s s',
      L.thread.keeps b s s' →
      ∀ (z : ProofFile.InstPub) (y y' : Strs) (v : WtF), carryX m (z, s) y v → carryX m (z, s') y' v)
    {l : Nat} (hl : l < 25) :
    PlaysS L.thread SaidOk (P1L20.clearIx l) ∧ BehindS L.thread SaidOk (P1L20.clearIx l) ∧
      ExchangeS L.thread SaidOk (P1L20.clearIx l) ∧
      RidesPastS L.thread SaidOk (P1L20.clearIx l) := by
  subst hL
  have hbd := clearIx_bounds hl
  have ei := clearIx_is l
  obtain ⟨blk, hblk⟩ := flat_at h (b := P1L20.clearIx l) (by omega)
  have hblk' : cF.blocksInOrder[14 * l + IM.nAt l + 7]? = some blk := hblk
  have hR := frame_rides h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf (csHead ν st R)) f w
    SaidOk hfF hcarry hblk ((frame_keeps_cleared h hl blk hblk').1)
  obtain ⟨a1, a2, a3⟩ := frame_owes_cleared_all h H Q test carryX item n₁ n₂ b₀ Vd
    (ridersOf (csHead ν st R)) f w SaidOk hfF hl noHalf (fun _ _ hS => hS)
    (by
      rcases Nat.lt_or_ge l 24 with e | e
      · have := nAt_lt e
        omega
      · have e24 : l = 24 := by omega
        subst e24
        have := nAt_head
        omega)
    (fun v s t _ hv => riders_cleared hl v s t hv) hR
  exact ⟨a1, a2, a3, hR⟩

/-- **At the chain's end, number 357.** -/
theorem frame_all_seal
    {L : Letters Bk ProofFile.Cl W₀ Rc ProofFile.Inst Tr X ProofFile.InstPub (CellsM OnBytes.Flat.numsFull)
      P5J.At.Tok MsgT}
    (hL : L = lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf (csHead ν st R)) (kpBy f) w)
    (hfF : f KindName.frame = keepsFrame P5J.At.links P1L20.bearing)
    (noHalf : ∀ g ∈ H.first, g.place.kind ≠ KindName.frame) (hb₀ : b₀ = 339)
    (hcarry : ∀ b p, P5J.At.ps[b]? = some p → p.kind = KindName.frame → ∀ m s s',
      L.thread.keeps b s s' →
      ∀ (z : ProofFile.InstPub) (y y' : Strs) (v : WtF), carryX m (z, s) y v → carryX m (z, s') y' v) :
    PlaysS L.thread SaidOk 357 ∧ BehindS L.thread SaidOk 357 ∧
      ExchangeS L.thread SaidOk 357 ∧ RidesPastS L.thread SaidOk 357 := by
  subst hL
  obtain ⟨blk, hblk⟩ := flat_at h (b := 357) (by omega)
  have hR := frame_rides h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf (csHead ν st R)) f w
    SaidOk hfF hcarry hblk ((frame_keeps_seal h (take := P1L20.bearing) blk hblk).1)
  obtain ⟨a1, a2, a3⟩ := frame_owes_seal h H Q test carryX item n₁ n₂ b₀ Vd
    (ridersOf (csHead ν st R)) f w SaidOk P1L20.bearing hfF noHalf
    (fun _ m ds hS hd => saidOk_past [sealRound] ds m hd hS) (by omega) riders_seal hR
  exact ⟨a1, a2, a3, hR⟩

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.frame_rides
#print axioms ProofFile.Honest.FirstThread.flat_at
#print axioms ProofFile.Honest.FirstThread.frame_all_front
#print axioms ProofFile.Honest.FirstThread.frame_all_laid
#print axioms ProofFile.Honest.FirstThread.frame_all_behind
#print axioms ProofFile.Honest.FirstThread.frame_all_cleared
#print axioms ProofFile.Honest.FirstThread.frame_all_seal
