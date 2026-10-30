-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/ToldDescR/SmpWalk.lean: no soundness is claimed.
sampleTwoB's walk: every sub-protocol of the proof file's first chain leaves the elder messages' sample rows. A joining: the relation and the walk lay.
The relation: SmpStay A B (Johnson/Desc/K1/Law/SmpStay.lean): the codes stay, and every message that is sampled stands behind at its number, with its shape, its mark and its sample rows.
The walk: descPure_fits (Johnson/Desc/AtSeats/Fit/TidySeat.lean), general in the relation: it asks StQuiet R · K1.AdmitOn R · kind K2's sub-protocol with rounds (below: by K2.yes_keeps_whole, Johnson/Top/H0/Tw/K2C/KeepsWhole.lean) · the first chain's last proximity test.
  stQuiet_smpStay · admitOn_smpStay    by groundKeeps_smpStay · stKeeps_grows.begun with kept_begun · row_of_quiet
  k2_smpStay                           K2.yes_keeps_whole at groundKeeps_smpStay
  call_smpStay · atFinish_smpStay      K12's files' run of calls (k12_calls, Johnson/Desc/K12/Law/Calls.lean · Calls.keeps, CallsDef.lean there): each call is a plain function of the ground or the beginning of a proximity test
  **descPure_smpStay**                 onlineDescription o pol lay KL = .ok F ⇒ F is fileDescBy … c and ∀ b ∈ c.blocksInOrder, b.planOk = true → Fits (ByS SmpStay) b
  **back_smpStay**                     along any family that hands back (HandsBack bs Rc, OwnSitsLast.lean): what is reached at border n + m comes from something reached at border n, with SmpStay between the two statements
  **sampleAtB_stay**                   sampleAtB cs sh A i = true · SmpStay A B ⇒ sampleAtB cs sh B i = true (the test reads the message's shape, its mark and its sample rows alone)
Does not show. That the test accepts behind the sending (the earning: left to other files). No member. Nothing on soundness.
-/
import Johnson.Desc.AtSeats.Fit.TidySeat
import Johnson.Desc.K1.Law.SmpStay
import Johnson.Desc.K13.Law.StatementGrows
import Johnson.Top.H0.Tw.K2C.KeepsWhole
import Johnson.Desc.K12.Law.Calls
import Johnson.Desc.K12.SeatLaws
import Johnson.ToldDescR.OwnSitsLast
import Johnson.ToldDescR.RcLastCode

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ToldDesc

open Meaning.K2
open OnBytes OnBytes.Model OnBytes.Params
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl WholeF Fits Steps steps_of_fits)
open VerifiableInference.Desc.Ground (GroundQuiet GroundKeeps groundKeeps_grows kept_begun)
open VerifiableInference.Desc.K1 (SmpStay smpStay_of groundKeeps_smpStay beginRun_smpStay)
open VerifiableInference.Desc.K13.Law (StQuiet row_of_quiet stKeeps_grows)

theorem stQuiet_smpStay : StQuiet SmpStay where
  quiet := groundKeeps_smpStay.quiet
  begun := fun T g G _ => smpStay_of (stKeeps_grows.begun T g G) (kept_begun T g G)
  row := fun lay im o n lin T r os' h =>
    row_of_quiet groundKeeps_smpStay.quiet lay im o n lin T r os' h

theorem admitOn_smpStay : K1.AdmitOn SmpStay :=
  fun d d' o rows h _ => groundKeeps_smpStay.admit d d' o rows h

/-- Kind K2's sub-protocol with rounds. -/
theorem k2_smpStay (p : K2.P2) (_ : p.firstTree = 0) :
    Fits (ByS SmpStay) (K2.codeSwitchKind p : Block S Unit) :=
  fun _ _ _ _ _ _ h => K2.yes_keeps_whole groundKeeps_smpStay h

/-- One call of the proximity test's run. -/
theorem call_smpStay {ft : ℕ} {a b : H2K.Out.DS} (h : H2K.Out.Call ft a b) :
    SmpStay a.st b.st := by
  cases h with
  | newGroup h => exact groundKeeps_smpStay.newGroup _ _ _ _ _ h
  | recv h => exact groundKeeps_smpStay.recv _ _ _ _ _ h
  | admit _ _ _ _ h => exact groundKeeps_smpStay.admit _ _ _ _ h
  | join h => exact groundKeeps_smpStay.join _ _ _ _ _ h
  | addRow h => exact groundKeeps_smpStay.addRow _ _ _ _ h
  | closeLedger h => exact groundKeeps_smpStay.closeLedger _ _ _ h
  | spend h => exact groundKeeps_smpStay.spendAsMask _ _ _ h
  | begin h => exact beginRun_smpStay _ _ _ _ h
  | count t => exact SmpStay.refl _
  | cols l => exact SmpStay.refl _

/-- **The first chain's last proximity test.** -/
theorem atFinish_smpStay (p : K12.P12) : Decides (ByS SmpStay) (K12.atFinish p) := by
  intro s rs gs s' h
  obtain ⟨o, t', -, -, -, hk, rfl⟩ := K12.Seat.atFinish_ok p s _ rs gs h
  exact H2K.Out.Calls.keeps (R := fun a b => SmpStay a.st b.st) (fun _ => SmpStay.refl _)
    (fun _ _ _ x y => x.trans y) (fun _ _ c => call_smpStay c)
    (H2K.Out.k12_calls p _ t' rs gs hk [] [])

/-- **AT THE PROOF FILE's SEAT: EVERY SUB-PROTOCOL OF THE FIRST CHAIN.** -/
theorem descPure_smpStay {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    (h : ProofFile.onlineDescription o pol lay KL = .ok F) :
    ∃ (Z : ProofFile.Pub) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (c : Chain S ProofFile.Cl),
      ProofFile.pureRoad.pub o pol lay KL = .ok Z ∧
      F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧
        ∀ b ∈ c.blocksInOrder, b.planOk = true → Fits (ByS SmpStay) b :=
  descPure_fits stQuiet_smpStay admitOn_smpStay k2_smpStay atFinish_smpStay h

/-- **Back along a family that hands back.** -/
theorem back_smpStay {Cl Pp : Type} {bs : List (Block S Cl)} {Rc : ℕ → Pp × S → Prop}
    (hb : HandsBack bs Rc) (hf : ∀ b ∈ bs, b.planOk = true → Fits (ByS SmpStay) b)
    (hp : ∀ b ∈ bs, b.planOk = true) (n : ℕ) {z : Pp} :
    ∀ (m : ℕ) (s : S), Rc (n + m) (z, s) → ∃ s₀, Rc n (z, s₀) ∧ SmpStay s₀.st s.st
  | 0, s, h => ⟨s, h, SmpStay.refl _⟩
  | m + 1, s, h => by
    obtain ⟨s₁, b, ft, rs, cols, k, r1, hk, hy⟩ := hb (n + m) z s h
    have hm := List.mem_of_getElem? hk
    have w : SmpStay s₁.st s.st := steps_of_fits (hf b hm (hp b hm)) (hp b hm) ft s₁ rs cols s _ hy
    obtain ⟨s₀, r0, w0⟩ := back_smpStay hb hf hp n m s₁ r1
    exact ⟨s₀, r0, w0.trans w⟩

open H2K.First (ok)
open H2K.Pin (sampleL)

/-- **The test goes along.** -/
theorem sampleAtB_stay {cs : Codes} {sh : OracleShape} {A B : Statement} {i : ℕ}
    (h : sampleAtB cs sh A i = true) (w : SmpStay A B) : sampleAtB cs sh B i = true := by
  unfold sampleAtB at h ⊢
  cases hx : A.oracles[i]? with
  | none => rw [hx] at h; cases h
  | some x =>
    rw [hx] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨e, k⟩ := h
    have hs : x.sampled = true := by
      have := k
      unfold ok sampleL at this
      simp only [List.all_cons, Bool.and_eq_true] at this
      exact this.1
    obtain ⟨x', hx', a1, a2, a3⟩ := w.2 i x hx hs
    rw [hx']
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨a1.trans e, ?_⟩
    have e2 : sampleL cs ⟨i, sh, 0, 0, default, 0⟩ x' = sampleL cs ⟨i, sh, 0, 0, default, 0⟩ x := by
      unfold sampleL
      rw [a2, a3, hs]
    rw [e2]
    exact k

end ToldDesc

#print axioms ToldDesc.stQuiet_smpStay
#print axioms ToldDesc.atFinish_smpStay
#print axioms ToldDesc.descPure_smpStay
#print axioms ToldDesc.back_smpStay
#print axioms ToldDesc.sampleAtB_stay
