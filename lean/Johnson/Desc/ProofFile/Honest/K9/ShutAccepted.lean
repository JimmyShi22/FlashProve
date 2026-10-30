-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/ShutAccepted.lean: the verifier accepts at the sub-protocol "the segment is shut", in
all 25 segments of the first chain, at the first chain's thread under the library's hypothesis `AtMgA`
(`lettersHead`, Honest/Thread/FirstHead.lean). The prover, the script and the other parameters of that thread are
variables, and so are the second condition `Said` and the table of falls: no fall is needed at this sub-protocol.

Why it holds. The sub-protocol has no round. Its decision accepts at a state without a mark of failure at which a
segment's book-keeping is open (`shut_yes`, Honest/K9/CloseYes.lean). The thread's invariant says both of the state in
front: "no mark" is its clause `form`; its clause `formP` contains the Bool `shapeAt`, which compares where the state
stands with where the written list of places says that it should stand; and at each of the 25 numbers that list says
"inside an open segment" (`standShut_all`, by Lean's kernel).

  `standShutB`, `standShut_all`, `stand_shut`   the test on the written list of places, and what it gives at one segment
  `link_of_stand`        a state that stands inside an open segment has a segment's book-keeping
  `k9Ends_at_thread`     the two sub-protocols without a round stand at the numbers 14 l + `IM.nAt l` + 4 and + 6
  `open_at_shut`         where the invariant holds in front of "the segment is shut", a segment's book-keeping is open
  **`accepted_shut`**    `AcceptedS` at 14 l + `IM.nAt l` + 6, for l < 25

Limits. The full size and the hash function `secondHashFunction` alone: the hypothesis's. It is not proved here that the invariant
holds at any run. `AcceptedS` is one of the hypotheses on one sub-protocol (Honest/Thread/PaysS.lean); this file proves
no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K9.CloseYes
import Johnson.Desc.ProofFile.Honest.K9.AtHead
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead
import Johnson.Desc.First.Att.K05T2
import Johnson.IMR.WrittenList

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread

/-- The test on the written list of places: at each number 14 l + `IM.nAt l` + 6 the list says "inside an open
segment". -/
def standShutB : Bool :=
  (List.range 25).all fun l =>
    match P5J.At.ps[14 * l + IM.nAt l + 6]? with
    | some p =>
      match standAt P5J.At.links p with
      | .link _ => true
      | _ => false
    | none => false

/-- It accepts: by Lean's kernel. -/
theorem standShut_all : standShutB = true := by decide +kernel

theorem stand_shut {l : ℕ} (hl : l < 25) :
    ∃ p sub, P5J.At.ps[14 * l + IM.nAt l + 6]? = some p ∧ standAt P5J.At.links p = .link sub := by
  have k := List.all_eq_true.1 standShut_all l (List.mem_range.2 hl)
  cases hp : P5J.At.ps[14 * l + IM.nAt l + 6]? with
  | none =>
    rw [hp] at k
    cases k
  | some p =>
    rw [hp] at k
    have k' : (match standAt P5J.At.links p with
      | .link _ => true
      | _ => false) = true := k
    cases hs : standAt P5J.At.links p with
    | link sub => exact ⟨p, sub, rfl, hs⟩
    | between => rw [hs] at k'; cases k'
    | headFront => rw [hs] at k'; cases k'
    | fin => rw [hs] at k'; cases k'
    | mem => rw [hs] at k'; cases k'

/-- A state that stands inside an open segment has a segment's book-keeping. -/
theorem link_of_stand {s : S} {sub : ModelPart} (h : standOf s = .link sub) : ∃ L, s.link? = some L := by
  unfold standOf at h
  cases hh : s.here with
  | between => rw [hh] at h; cases h
  | lay a => exact ⟨a.L, by simp [S.link?, hh]⟩
  | att a => exact ⟨a.L, by simp [S.link?, hh]⟩
  | head a =>
    rw [hh] at h
    cases hi : s.inLink with
    | false =>
      rw [hi] at h
      cases h
    | true =>
      have ho : a.opened = true := by
        by_contra ho
        simp [S.inLink, S.fork?, hh, ho] at hi
      exact ⟨a.L, by simp [S.link?, hh, ho]⟩
  | fin a => rw [hh] at h; cases h
  | mem a => rw [hh] at h; cases h

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- The two sub-protocols without a round, at their numbers in the thread's list. -/
theorem k9Ends_at_thread (l : ℕ) (hl : l < 25) :
    ∃ Lk p Qc bE bS, K9Ends (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (14 * l + IM.nAt l + 4) (14 * l + IM.nAt l + 6) cF Zp l Lk p Qc bE bS := by
  obtain ⟨Lk, p, Qc, bE, bS, Hc⟩ := close_at_head h l hl
  obtain ⟨Lk', p', w', Sd⟩ := seated_at_head h l hl
  obtain rfl : Lk' = Lk := Option.some.inj (Sd.link.symm.trans Hc.link)
  have e : Lk'.hear.length = IM.nAt l := Sd.hears
  refine ⟨Lk', p, Qc, bE, bS, Hc, ?_, ?_⟩
  · rw [← e]
    exact Hc.atE
  · rw [← e]
    exact Hc.atS

/-- Where the invariant holds in front of "the segment is shut", a segment's book-keeping is open. -/
theorem open_at_shut {l : ℕ} (hl : l < 25) {k : Coins Bk} {s : TS}
    {μ : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {En : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (14 * l + IM.nAt l + 6) k s μ En) : ∃ L, s.link? = some L := by
  obtain ⟨p, sub, hp, hs⟩ := stand_shut hl
  unfold Thr at hT
  obtain ⟨-, -, ⟨hf, hP⟩, -, -, -, -⟩ := hT
  have hf' : s.failed.isNone = true := hf
  have hn : s.failed = none := Option.isNone_iff_eq_none.1 hf'
  have hP' : onAt (P5J.At.N Zp cF) (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP P5J.At.links
      P5J.At.ps[14 * l + IM.nAt l + 6]?
      (((openSets P5J.At.links P5J.At.ps (start P5J.At.links))[14 * l + IM.nAt l + 6]?).getD [])
      (((pubSets (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP.more P5J.At.links
        P5J.At.ps)[14 * l + IM.nAt l + 6]?).getD []) (μ.st.input.x.pub, s) noStrs := hP
  rw [hp] at hP'
  have hsh := Att.P.onAt_shape hP' hn
  unfold shapeAt at hsh
  simp only [Bool.and_eq_true, beq_iff_eq] at hsh
  exact link_of_stand (hsh.1.1.trans hs)

/-- **The verifier accepts at "the segment is shut", in all 25 segments.** -/
theorem accepted_shut (l : ℕ) (hl : l < 25)
    (Said : ℕ → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (fall : ℕ → TS → List Fmt.Drawn → Option String) :
    AcceptedS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said fall
      (14 * l + IM.nAt l + 6) := by
  obtain ⟨Lk, p, Qc, bE, bS, He⟩ := k9Ends_at_thread h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w l hl
  exact He.acceptedS fall (fun _ _ hf => Option.isNone_iff_eq_none.1 hf)
    (fun _ _ _ _ hT _ => open_at_shut h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hl hT.1)

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.standShut_all
#print axioms ProofFile.Honest.K9.stand_shut
#print axioms ProofFile.Honest.K9.link_of_stand
#print axioms ProofFile.Honest.K9.k9Ends_at_thread
#print axioms ProofFile.Honest.K9.open_at_shut
#print axioms ProofFile.Honest.K9.accepted_shut
