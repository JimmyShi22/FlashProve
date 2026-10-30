-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/K3DigitsStep.lean: the lookup on the digits of a segment's approximate range
proof: WHAT AN ACCEPT OF THE WHOLE SEATED SUB-PROTOCOL (K3.theStated's value at the digits' address:
the lookup's own rounds and the step without a round behind them) LEAVES AND MAKES, AS FACTS ON TWO
STATES OF THE VERIFIER: at the sub-protocol's own decide, WHATEVER THE ROUNDS' WORDS: no piece, no
transcript, no premise that the words are canonical. Statements and proofs. NO SOUNDNESS IS CLAIMED.

Why. The same four facts lie at a piece's accept (K3DigitsSeatedYes.lean, K3DigitsSeatedLeaves.lean,
K3DigitsHeadStays.lean), where the rounds are a typed transcript's. The fold along the verifier's
states speaks of the sub-protocol's step on a state, at any rounds.

Main names.
  k3_digits_lookOut_any: k3_digits_lookOut (K3DigitsLookOut.lean) without its premise okRoundsE: by
    decide_left_some (Johnson/Top/H/Keep/K3LeftAnyWords.lean).
  k3_digits_step_turns: SameBut s s₂, and k3OnIn p s = true → k3OnOut p s₂ = true.
    k3_digits_step_leaves: DigLeft s s₂. k3_digits_step_headStays: HeadStays s s₂.
  step_gives_decide: an .ok of Block.step is an .ok of decide at some rounds and groups
    (step_ok_iff, Johnson/Desc/Sound/RunIsDecide.lean).
HOW. The three proofs are the seated theorems' own, laid by program with the piece's first line
struck.
OBJECT. Desc.K3.theStated's value at the digits' address; Desc.Block.step.
USER. K3DigitsOwnStays.lean and Johnson/Desc/Sound/MgAt/K3RidesDigStep.lean, among others.
LETTERS. Those of k3_digits_seated_turns, less the piece's; s, s₂, rs, gs.
IS IT EMPTY? The premise is an .ok of decide: what an accepted proof gives.



Compiled with the whole library.
Limits. Nothing where decide rejects. Nothing on hiding.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3DigitsSeatedLeaves
import Johnson.Desc.First.Look.K3DigitsHeadStays
import Johnson.Top.H.Keep.K3LeftAnyWords
import Johnson.Desc.Sound.RunIsDecide

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open OnBytes.PscRun
open VerifiableInference.Desc.K3 (sizedB freeB heardAt k3OnIn k3OnOut)

/-- **From the promise in front and an accept to the promise behind, whatever the words.** -/
theorem k3_digits_lookOut_any {Cl : Type} (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (p : Desc.First.Look.P)
    (guests : List (Desc.First.Look.Guest Desc.First.S Cl)) {h : Forest.Shape}
    (hs : p.shape = some h) (hdg : p.digits = true) (s s' : Desc.First.S) (rs : List Fmt.RoundView)
    (cols : List (List (ℕ × List UInt64)))
    (hd : (Desc.K3.block (Desc.K3.seatDigits claim) piece laid before p guests).decide s rs cols =
      .ok s') (hIn : k3OnIn p s = true) : k3OnOut p s' = true := by
  obtain ⟨Fk, hf, hz, hn, hfree⟩ := k3OnIn_free hs hIn
  obtain ⟨F0, x, hF0, hn0, e0, hL⟩ :=
    decide_left_some (Desc.K3.seatDigits claim) piece laid before p guests
      (Desc.K3.seatDigits_reads claim) h hs Reading.gl p.lm s s' rs cols hd
  obtain rfl : Fk = F0 := Option.some.inj (hf.symm.trans hF0)
  obtain ⟨F1, y, hF1, hn1, e1, hE⟩ :=
    decide_exact (Desc.K3.seatDigits claim) piece laid before p guests s s' rs cols hd
  obtain rfl : Fk = F1 := Option.some.inj (hf.symm.trans hF1)
  have hsome : ((Desc.K3.seatDigits claim).fork s).isSome = true := by
    rw [hF1]
    rfl
  have hgx : (Desc.K3.seatDigits claim).heard s' = some x.1 := by
    rw [e0]
    exact Desc.K3.seatDigits_reads claim _ _ _ hsome hn0
  have hgy : (Desc.K3.seatDigits claim).heard s' = some y.1 := by
    rw [e1]
    exact Desc.K3.seatDigits_reads claim _ _ _ hsome hn1
  have hFx : (Desc.K3.seatDigits claim).fork s' = some x.2 := by
    rw [e0]
    exact seatDigits_keeps claim _ _ _ hsome hn0
  have hFy : (Desc.K3.seatDigits claim).fork s' = some y.2 := by
    rw [e1]
    exact seatDigits_keeps claim _ _ _ hsome hn1
  have eg : y.1 = x.1 := Option.some.inj (hgy.symm.trans hgx)
  have eF : y.2 = x.2 := Option.some.inj (hFy.symm.trans hFx)
  obtain ⟨rs', L⟩ := hL hz
  have E := (hE hz).1
  rw [eg, eF, L.shape] at E
  refine k3OnOut_of_left p s' hs ?_ hFx L E hn hfree (_root_.Fo.Pay.shapeOf_ok (shape_some p h hs))
  rw [hdg]
  exact hgx

/-- An .ok of the step is an .ok of decide. -/
theorem step_gives_decide {S Cl : Type} (ft : ℕ) (b : Desc.Block S Cl) (s s' : S)
    (R : List Fmt.RoundView) (c : List Desc.OpenedColumn) (k : ℕ) (h : b.step ft s R c = .ok (s', k)) :
    ∃ rs gs, b.decide s rs gs = .ok s' :=
  ⟨_, _, ((step_ok_iff ft b s s' R c k).1 h).2.2.2⟩

section
variable {Cl : Type}

/-- **Nothing else turns; the promise behind holds.** -/
theorem k3_digits_step_turns (claim : Aff → Cl)
    (readers : ℕ → Option (Desc.K3.Readers Desc.First.S)) (X : Verify.Public) (codes : Codes)
    (shape : Params.ReqShape) (a : Desc.Place) (B : Desc.Block Desc.First.S Cl)
    (h : Desc.K3.theStated claim readers X codes shape a = some B) (hOk : B.planOk = true)
    (i : ℕ) (hi : a.link = some i) (hpc : a.piece = Desc.K3.pieceAt X i true)
    {x : Desc.First.Look.Place} (hlook : lookAt X i true = some x) {hs : Forest.Shape}
    (hsh : (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) true x).shape = some hs)
    (s s₂ : Desc.First.S) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64)))
    (hd : B.decide s rs gs = .ok s₂) :
    SameBut s s₂ ∧
      (Desc.K3.k3OnIn (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) true x) s = true →
        Desc.K3.k3OnOut (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) true x) s₂ =
          true) := by
  obtain ⟨P', sent, laid, n, gs', s', hP, hyes, hstep⟩ :=
    theStated_yes_digits claim readers X codes shape a B h hOk i hi hpc s s₂ rs gs hd
  have eP : P' = (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) true x) := by
    unfold placeAt at hP
    rw [hlook] at hP
    exact (Option.some.inj hP).symm
  subst eP
  have hS := k3_digits_sameBut claim a.piece laid sent _ [] s s' _ gs' hyes
  have hO : Desc.K3.k3OnIn (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) true x) s =
      true →
      Desc.K3.k3OnOut (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) true x) s' = true :=
    fun hIn => k3_digits_lookOut_any claim a.piece laid sent _ [] hsh rfl s s' _ gs' hyes hIn
  rcases hstep with e | ⟨f, hf, hfs⟩
  · rw [e]
    exact ⟨hS, hO⟩
  · unfold Desc.K3.quietAt at hf
    simp only [if_true] at hf
    split at hf
    · obtain rfl := Option.some.inj hf
      obtain ⟨ah, c, ha, ho, e⟩ := Desc.K3.quietHead_ok X s' s₂ hfs
      rw [e]
      exact ⟨hS.trans (headClaim_sameBut s' ah c ha ho),
        fun hIn => k3OnOut_headClaim _ rfl s' ah c ha (hO hIn)⟩
    · split at hf <;> split at hf <;>
        (obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.1 hf
         obtain ⟨F, hF, -, e⟩ := Desc.K3.quietDigits_ok _ _ s' s₂ hfs
         obtain ⟨F₂, hF₂, hG₂⟩ := Desc.K3.quietDigits_fork _ _ s' s₂ hfs
         obtain rfl : F = F₂ := Option.some.inj (hF.symm.trans hF₂)
         have hh : Desc.K3.heardAt true s₂ = Desc.K3.heardAt true s' := by
           rw [e]
           simp [Desc.K3.heardAt, tl_putFork]
         exact ⟨hS.trans (e ▸ putFork_sameBut s' F _ hF),
           fun hIn => k3OnOut_planClaims _ s' s₂ F _ hF hG₂ hh (hO hIn)⟩)

/-- **What else it leaves.** -/
theorem k3_digits_step_leaves (claim : Aff → Cl)
    (readers : ℕ → Option (Desc.K3.Readers Desc.First.S)) (X : Verify.Public) (codes : Codes)
    (shape : Params.ReqShape) (a : Desc.Place) (B : Desc.Block Desc.First.S Cl)
    (h : Desc.K3.theStated claim readers X codes shape a = some B) (hOk : B.planOk = true)
    (i : ℕ) (hi : a.link = some i) (hpc : a.piece = Desc.K3.pieceAt X i true)
    (s s₂ : Desc.First.S) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64)))
    (hd : B.decide s rs gs = .ok s₂) : DigLeft s s₂ := by
  unfold DigLeft
  obtain ⟨P', sent, laid, n, gs', s', -, hyes, hstep⟩ :=
    theStated_yes_digits claim readers X codes shape a B h hOk i hi hpc s s₂ rs gs hd
  obtain ⟨F, y, hF, hn, e, hE⟩ :=
    decide_exact (Desc.K3.seatDigits claim) a.piece laid sent P' [] s s' _ gs' hyes
  have hF0 : s.fork? = some F := hF
  have hsome : ((Desc.K3.seatDigits claim).fork s).isSome = true := by
    rw [hF]
    rfl
  have hF' : s'.fork? = some y.2 := by
    rw [e]
    exact seatDigits_keeps claim _ _ _ hsome hn
  have hL : s'.lookHeard? = s.lookHeard? := by
    rw [e]
    exact putDigits_look claim s y.1 F y.2 hF
  have hO : ∀ pc : Desc.First.Look.P, pc.digits = false → Desc.K3.k3OnOut pc s = true →
      Desc.K3.k3OnOut pc s' = true :=
    fun pc hdc hIn => k3OnOut_other_rides claim a.piece laid sent P' [] pc hdc s s' _ gs' hyes hIn
  have hZ : OnBytes.PscRun.Sized F → _root_.Fo.Later F y.2 ∧ OnBytes.PscRun.Sized y.2 ∧
      (((List.range (F.ns - F.next)).all fun j => !F.gotF.getD (F.next + j) true) = true →
        ((List.range (y.2.ns - y.2.next)).all fun j => !y.2.gotF.getD (y.2.next + j) true) =
          true) := by
    intro hz
    obtain ⟨E, hLat⟩ := hE hz
    exact ⟨⟨hLat.next, hLat.ns, hLat.keep⟩, hLat.sized hz,
      freeAbove_hearing E hLat.ns (hLat.sized hz)⟩
  rcases hstep with e' | ⟨f, hf, hfs⟩
  · rw [e']
    refine ⟨F, y.2, hF0, hF', hL, fun hz => ⟨(hZ hz).1, (hZ hz).2.1, fun hfr => ?_⟩, hO⟩
    unfold freeAboveB at hfr ⊢
    rw [hF0] at hfr
    rw [hF']
    exact (hZ hz).2.2 hfr
  · obtain ⟨F₂, c, hF₂, hG₂, hL₂⟩ := quietAt_ledger X i f hf s' s₂ hfs
    obtain rfl : y.2 = F₂ := Option.some.inj (hF'.symm.trans hF₂)
    refine ⟨F, _, hF0, hG₂, hL₂.trans hL, fun hz => ⟨?_, ?_, fun hfr => ?_⟩, fun pc hdc hIn => ?_⟩
    · exact (hZ hz).1.trans (later_planClaims y.2 c)
    · exact (hZ hz).2.1
    · unfold freeAboveB at hfr ⊢
      rw [hF0] at hfr
      rw [hG₂]
      exact (hZ hz).2.2 hfr
    · refine k3OnOut_planClaims pc s' s₂ y.2 c hF' hG₂ ?_ (hO pc hdc hIn)
      rw [hdc]
      exact hL₂

/-- **At the output head's segment: all but tl, F, claim.** -/
theorem k3_digits_step_headStays (claim : Aff → Cl)
    (readers : ℕ → Option (Desc.K3.Readers Desc.First.S)) (X : Verify.Public) (codes : Codes)
    (shape : Params.ReqShape) (a : Desc.Place) (B : Desc.Block Desc.First.S Cl)
    (h : Desc.K3.theStated claim readers X codes shape a = some B) (hOk : B.planOk = true)
    (i : ℕ) (hi : a.link = some i) (hpc : a.piece = Desc.K3.pieceAt X i true)
    (s s₂ : Desc.First.S) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64)))
    (hd : B.decide s rs gs = .ok s₂) : HeadStays s s₂ := by
  obtain ⟨P', sent, laid, n, gs', s', -, hyes, hstep⟩ :=
    theStated_yes_digits claim readers X codes shape a B h hOk i hi hpc s s₂ rs gs hd
  have hS := k3_digits_headStays claim a.piece laid sent _ [] s s' _ gs' hyes
  rcases hstep with e | ⟨f, hf, hfs⟩
  · rw [e]
    exact hS
  · unfold Desc.K3.quietAt at hf
    simp only [if_true] at hf
    split at hf
    · obtain rfl := Option.some.inj hf
      obtain ⟨ah, c, ha, -, e⟩ := Desc.K3.quietHead_ok X s' s₂ hfs
      rw [e]
      exact hS.trans (headClaim_headStays s' ah c ha)
    · split at hf <;> split at hf <;>
        (obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.1 hf
         obtain ⟨F, -, -, e⟩ := Desc.K3.quietDigits_ok _ _ s' s₂ hfs
         exact hS.trans (e ▸ putFork_headStays s' _))

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.k3_digits_lookOut_any
#print axioms VerifiableInference.OnPublicFiles.step_gives_decide
#print axioms VerifiableInference.OnPublicFiles.k3_digits_step_turns
#print axioms VerifiableInference.OnPublicFiles.k3_digits_step_leaves
#print axioms VerifiableInference.OnPublicFiles.k3_digits_step_headStays
