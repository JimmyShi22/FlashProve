-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/BatPlays.lean: "IT PLAYS" (`Plays`, Honest/Thread/Pays.lean; `PlaysS`, Honest/Thread/PaysS.lean) AT THE
BATCHING, AT ANY THREAD in whose list of prover's sides the search at the batching's place finds none; and so at all three
sub-protocols of this kind in each of the 25 segments, at the first chain's thread under the library's hypothesis `AtMgA`.

Why it holds. The batching declares one round, in which nothing is sent, and no oracle message. Where no side stands at
its place the frame lays one step without a move (`steps_noSide`, Honest/K9/BatNoSide.lean). Played at the one challenge that
the round can draw, that step shows a round without an item; the round reads no column (`bat_reads`); and no tree is new.

  **`plays_noSide`**      `Plays T b` from: the segment's seat · the block at b · the search finds none. T is any thread
  `plays_of_hno`          that from "no side of this kind stands in the list"
  **`playsS_k9_at_head`**   under the hypothesis, l < 25, no side of this kind in the prover's first list: `PlaysS` at the
                          numbers 14 l + `IM.nAt l` + 2, + 4 and + 6, at every Said

Limits. Of a list in which a side does stand at the batching's place nothing is said. It is not proved that the invariant
holds at any run. `Plays` is one of the hypotheses on one sub-protocol; this file proves no property of a prover or a
protocol.
-/
import Johnson.Desc.ProofFile.Honest.K9.BatNoSide
import Johnson.Desc.ProofFile.Honest.K9.ShutAccepted
import Johnson.Desc.ProofFile.Honest.Thread.QuietLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread

variable {V W X Pb : Type} {Bk : ProverCoinCounts}

/-- **"It plays" at the batching, where the search at its place finds no side.** -/
theorem plays_noSide {c : Chain S Claim} {Z : ProofFile.Pub} {l k : ℕ} {Lk : Link S Claim} {p : Desc.K9.Where}
    {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (T : Thread Bk S Claim V W X Pb) {b : ℕ}
    (Sd : SeatedFree c Z l k Lk p w)
    (hblk : T.bs[b]? = some (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)))
    (hn : (T.hs.find? fun h => h.place == (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)).place) = none) :
    Plays T b := by
  intro blk hblk' κ s m En ds st _ hd _ hl
  rw [hblk] at hblk'
  cases hblk'
  obtain ⟨h1, h2, _⟩ := Sd.shape
  rw [h1] at hd
  obtain ⟨tr, rfl⟩ := draws_one p ds hd
  obtain rfl := steps_noSide p _ _ _ _ T.hs st h1 h2 hn hl
  refine ⟨([⟨(Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)).name,
      (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)).place, 0, false, [], [], ⟨[tr], [], [], none⟩⟩],
    ⟨m.st.hears ⟨[tr], [], [], none⟩, m.loc ++ [⟨[tr], [], [], none⟩], m.seen ++ [⟨[], ⟨[tr], [], [], none⟩⟩],
      m.opened⟩), [], ?_, ?_⟩
  · unfold Thread.Moved
    refine ⟨⟨_, hl, rfl⟩, ?_⟩
    rw [h1, bat_reads]
    rfl
  · intro σ hσ
    have e : T.hand (b + 1) = T.hand b := by
      unfold Thread.hand
      rw [treesTo_succ hblk, h2]
      rfl
    obtain ⟨g1, g2⟩ := List.mem_filter.1 hσ
    rw [e] at g1
    simp [g1] at g2

/-- The same from "no side of this kind stands in the thread's list". -/
theorem plays_of_hno {c : Chain S Claim} {Z : ProofFile.Pub} {l k : ℕ} {Lk : Link S Claim} {p : Desc.K9.Where}
    {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (T : Thread Bk S Claim V W X Pb) {b : ℕ}
    (Sd : SeatedFree c Z l k Lk p w)
    (hblk : T.bs[b]? = some (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)))
    (hno : ∀ g ∈ T.hs, g.place.kind ≠ KindName.K9) : Plays T b :=
  plays_noSide T Sd hblk (none_at_batching Sd T.hs hno)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {W₀ Rc Ky Tr X₀ Y : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ Y)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₀ : Local W₀ Rc ProofFile.Inst Tr)

/-- **`PlaysS` at this kind's three sub-protocols of each segment.** -/
theorem playsS_k9_at_head (l : ℕ) (hl : l < 25) (hno : ∀ g ∈ H.first, g.place.kind ≠ KindName.K9)
    (Said : ℕ → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) Y → Prop) :
    PlaysS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₀).thread Said (14 * l + IM.nAt l + 2) ∧
      PlaysS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₀).thread Said (14 * l + IM.nAt l + 4) ∧
      PlaysS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₀).thread Said (14 * l + IM.nAt l + 6) := by
  obtain ⟨Lk, p, w, Sd⟩ := seated_at_head h l hl
  obtain ⟨Lk', p', Qc, bE, bS, He⟩ := k9Ends_at_thread h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₀ l hl
  refine ⟨playsS_of _ Said (plays_of_hno _ Sd ?_ hno), playsS_of _ Said He.playsE, playsS_of _ Said He.playsS⟩
  exact Sd.batching

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.plays_noSide
#print axioms ProofFile.Honest.K9.plays_of_hno
#print axioms ProofFile.Honest.K9.playsS_k9_at_head
