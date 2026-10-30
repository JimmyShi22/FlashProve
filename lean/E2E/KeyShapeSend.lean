-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyShapeSend.lean: THE SEAT OF A SENDING (the kind K1) IN THE KEY FILE's FIRST CHAIN, CUT IN
TWO: STRUCTURE | VALUES (the cut: Johnson/Desc/ProofFile/Honest/Thread/Shape.lean), ON THE CHAIN's
SHAPE (E2E/KeyShapeFirst.lean), general in the sending's numbers and in the shape's back part: for
the chain's three sendings. BOTH DIRECTIONS. Definitions, statements and proofs. A sub-protocol of
the verifier's: NOTHING IS SHOWN OF ANY PROVER.

The sending on the shape of statement, book and roots (one Bool `sendB`, one update `sendCore`, and
the laws
`send_core`, `send_returns` on the kind's own decision) is Johnson/Desc/First/Shape/SendCore.lean's:
CALLED. Here it is seated at the chain's state, and the mark on the statement is carried.

  `sendSeat_inv`: the seat's accept, read back.
  **`gSend`**: the seat on the shape: the mark on the statement; `sendB`. Behind: `sendCore`; no
    count of rows waits; the new messages' numbers.
  **`send_carries`**: (B1r) at rounds that fit. The mark is kept by the library's `K1.sendOwn_rel`
    at `groundQuiet_tidy` and `admitOn_tidy`.
  `vSend`: two tests on the two rounds: no OOD seed's factor is 0; the second round holds as many
    answers as the place counts. **`vSend_fit`**: ROUNDS THAT FIT THE DECLARED ONES PASS BOTH:
    Johnson/Prover/Send/Form.lean's `factors_of_fit` and the library's `K1.answers_len`: CALLED: so
    a sending has no named test on values.
  **`send_returns₁`**: (B2r), at whatever rounds pass the two tests.

Limits.
- Enough, not needed.
- The files that are called, Johnson/Desc/First/Shape/SendCore.lean and
  Johnson/Prover/Send/Form.lean, are not reviewed.


-/
import E2E.KeyShapeFirst
import Johnson.Desc.First.Shape.SendCore
import Johnson.Desc.K1.Quiet
import Johnson.Desc.Tidy.Stay
import Johnson.Top.H0.StepLaws.StepLaws
import Johnson.Prover.Send.Form

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.AtFiles
open OnBytes OnBytes.Params
open ProofFile.Honest (Shape Carries Returns CarriesR ReturnsR)
open VerifiableInference.Desc (Block roundsFit noDigest step_iff)
open VerifiableInference.Desc.Ground.Sh
open VerifiableInference.Desc.Key (FirstState sendingSeat withLoc)
open VerifiableInference.Desc.First.Shape (sendCore sendB idsAt send_core send_returns)
open AtPublicFiles.KeyShape (Sh₁ sh₁ Pub1 BackOf)

/-! ## The seat -/

variable {Bk Cl : Type} (Q : Pub1) (bk : BackOf → Bk)

/-- The seat's accept, read back. -/
theorem sendSeat_inv (name : String) (P : VerifiableInference.Desc.K1.Par) (s s' : FirstState)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (sendingSeat (Cl := Cl) name P).decide s rs gs = .ok s') :
    ∃ x, VerifiableInference.Desc.K1.decideSend P s.debt (withLoc s.d (#[] : Array Nat)) rs =
        .ok x ∧ s' = { s with d := withLoc x.2 (), owed := none, sent := x.1 } := by
  have h' : ((VerifiableInference.Desc.K1.decideSend P s.debt (withLoc s.d (#[] : Array Nat))
      rs).map fun x => ({ owed := none, held := { x.2 with loc := x.1 } } :
        VerifiableInference.Desc.K1.Owing (_root_.Desc.Plain.DState (Array Nat)))).map
      (fun y => { s with d := withLoc y.held (), owed := y.owed, sent := y.held.loc }) =
      .ok s' := h
  cases hx : VerifiableInference.Desc.K1.decideSend P s.debt (withLoc s.d (#[] : Array Nat))
      rs with
  | error e =>
    rw [hx] at h'
    cases h'
  | ok x =>
    rw [hx] at h'
    exact ⟨x, rfl, (Except.ok.inj h').symm⟩

/-- **The seat of a sending, on the shape.** -/
def gSend (P : VerifiableInference.Desc.K1.Par) (a : Sh₁ Bk) : Except String (Sh₁ Bk) :=
  if a.2.tidy && sendB P a.2.owed a.1 then
    .ok (sendCore P a.1,
      { a.2 with owed := none, sent := (idsAt P a.1.st.oracles.length).toList })
  else .error "a sending: the mark on the statement, or a guard on the shape"

/-- **(B1r), at rounds that fit the sending's declared ones.** -/
theorem send_carries (name : String) (P : VerifiableInference.Desc.K1.Par) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (hfit : roundsFit (VerifiableInference.Desc.K1.rounds P) rs = true) :
    CarriesR (sh₁ Q bk)
      (fun s => (sendingSeat (Cl := Cl) name P).decide s (rs.map noDigest) gs) (gSend P) := by
  intro s s' t hf hg
  unfold gSend at hg
  split at hg
  · rename_i hm
    rw [Bool.and_eq_true] at hm
    have hT : stTidyB s.d.st = true := hm.1
    have hB : VerifiableInference.Desc.K1.planOkOwn P = true := by
      have := hm.2
      simp only [sendB, Bool.and_eq_true] at this
      exact this.1.1.2
    obtain rfl := Except.ok.inj hg
    obtain ⟨x, hx, rfl⟩ := sendSeat_inv (Cl := Cl) name P s s' _ gs hf
    obtain ⟨e1, e2, -, -⟩ := send_core hx
    have hT' : stTidyB x.2.st = true := by
      have hs : (VerifiableInference.Desc.K1.sendOwn (Cl := Cl) P).decide
          { owed := s.debt, held := withLoc s.d (#[] : Array Nat) } (rs.map noDigest) gs =
          .ok { owed := none, held := { x.2 with loc := x.1 } } := by
        show (VerifiableInference.Desc.K1.decideSend P s.debt (withLoc s.d (#[] : Array Nat))
          (rs.map noDigest)).map _ = _
        rw [hx]
        rfl
      exact tidy_mark (VerifiableInference.Desc.K1.sendOwn_rel
        VerifiableInference.Desc.Ground.groundQuiet_tidy
        VerifiableInference.Desc.Ground.admitOn_tidy P hB _ _ rs gs hfit hs (tidy_of hT))
    have e2' : shD (withLoc x.2 ()) = sendCore P (shD s.d) := e2
    have e1' : x.1 = idsAt P (shD s.d).st.oracles.length := by
      rw [e1]
      show idsAt P s.d.st.oracles.size = idsAt P (stSh s.d.st).oracles.length
      rw [orc_size]
    refine Prod.ext e2'.symm ?_
    show ({ AtPublicFiles.KeyShape.locSh Q bk s with
        owed := none, sent := (idsAt P (shD s.d).st.oracles.length).toList } :
          AtPublicFiles.KeyShape.LocSh Bk) =
      AtPublicFiles.KeyShape.locSh Q bk { s with d := withLoc x.2 (), owed := none, sent := x.1 }
    unfold AtPublicFiles.KeyShape.locSh
    have hT'' : stTidyB (withLoc x.2 ()).st = true := hT'
    rw [hT, hT'', ← e1']
    rfl
  · cases hg

/-- **The two named tests** on the sending's two rounds. -/
def vSend (P : VerifiableInference.Desc.K1.Par) (rs : List Fmt.RoundView) : Bool :=
  match rs with
  | [r₁, r₂] =>
    ((VerifiableInference.Desc.K1.seedsOf P r₁).all fun x => !isZeroE x.2) &&
      (VerifiableInference.Desc.K1.answersIn r₂).length == P.answers
  | _ => false

/-- **Rounds that fit the sending's declared ones pass both**: the first by
Johnson/Prover/Send/Form.lean's `factors_of_fit`, the second by the library's `K1.answers_len`. -/
theorem vSend_fit (P : VerifiableInference.Desc.K1.Par) (rs : List Fmt.RoundView)
    (h : roundsFit (VerifiableInference.Desc.K1.rounds P) rs = true) :
    vSend P (rs.map noDigest) = true := by
  match rs, h with
  | [r₁, r₂], h =>
    show (((VerifiableInference.Desc.K1.seedsOf P r₁).all fun x => !isZeroE x.2) &&
      (VerifiableInference.Desc.K1.answersIn r₂).length == P.answers) = true
    rw [VerifiableInference.Desc.K1.answers_len P r₁ r₂ h, beq_self_eq_true, Bool.and_true,
      List.all_eq_true]
    intro x hx
    rw [Johnson.Prover.Send.factors_of_fit P r₁ r₂ h x hx]
    rfl
  | [], h => simp [VerifiableInference.Desc.K1.rounds, roundsFit] at h
  | [_], h => simp [VerifiableInference.Desc.K1.rounds, roundsFit] at h
  | _ :: _ :: _ :: _, h => simp [VerifiableInference.Desc.K1.rounds, roundsFit] at h

/-- **(B2r).** -/
theorem send_returns₁ (name : String) (P : VerifiableInference.Desc.K1.Par) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) :
    ReturnsR (sh₁ Q bk) (fun s => (sendingSeat (Cl := Cl) name P).decide s rs gs) (gSend P)
      (fun _ => vSend P rs) := by
  intro s t hg hv
  unfold gSend at hg
  split at hg
  · rename_i hm
    rw [Bool.and_eq_true] at hm
    match rs, hv with
    | [r₁, r₂], hv =>
      have hv' : (((VerifiableInference.Desc.K1.seedsOf P r₁).all fun x => !isZeroE x.2) &&
        (VerifiableInference.Desc.K1.answersIn r₂).length == P.answers) = true := hv
      rw [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hv'
      obtain ⟨x, hx⟩ := send_returns P s.owed (withLoc s.d (#[] : Array Nat)) r₁ r₂ hm.2
        (fun y hy => by
          have := hv'.1 y hy
          cases e : isZeroE y.2 with
          | false => rfl
          | true => rw [e] at this; cases this) hv'.2
      refine ⟨{ s with d := withLoc x.2 (), owed := none, sent := x.1 }, ?_⟩
      show ((VerifiableInference.Desc.K1.decideSend P s.debt (withLoc s.d (#[] : Array Nat))
        [r₁, r₂]).map _).map _ = _
      have hx' : VerifiableInference.Desc.K1.decideSend P s.debt
          (withLoc s.d (#[] : Array Nat)) [r₁, r₂] = .ok x := hx
      rw [hx']
      rfl
  · cases hg

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.sendSeat_inv
#print axioms AtPublicFiles.AtFiles.send_carries
#print axioms AtPublicFiles.AtFiles.vSend_fit
#print axioms AtPublicFiles.AtFiles.send_returns₁
