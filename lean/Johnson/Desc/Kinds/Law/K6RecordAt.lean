-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6RecordAt.lean (the ledger's length is not in RecordRest:
Law/K6LedgerAt.lean pays it; the stated data are a letter; in the place of DataSeated,
eight clauses an element, stands MatsSeated, five facts a matrix): FOUR OF THE ELEVEN CLAUSES
THAT Law/K6OpenedCut.lean ASKS OF
THE VERIFIER'S STATE BEHIND THE SUB-PROTOCOL AT THE OUTPUT HEAD (RecordDue), AT THE DESCRIPTION'S
OWN PIECE: from an accept of the piece that holds the seated constant, K6's condition in
front, and two tests with code on
the verifier's state in front.

A joining. Law/HeadRidesSays.lean (four_behind) has the four behind an accept of the
STRICT reading of blockOf's value, under K6On in front.
Johnson/Desc/Sound/K6Tied.lean has the road from the piece to the seated constant (Seated,
seated_across) and from K6Left to K6On (inside k6_carry_left). Here the two are put end to end.

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable).
  below_yes_seated: an accept of the piece is an accept of the strict reading of blockOf's value, at
      the
      carried states of the verifier.
  k6On_front: K6Left in front, the plan's test and an accept of the piece give K6On in front (the
      clause
      on the request: where it fails the seated sub-protocol rejects).
  RecordRest: what is left of RecordDue (the open segment's part; its layout; MatsSeated:
      Law/DataSeatedOfLaid.lean; the mask row's message; the reads' array's name; StatedAt; the
          lookup's last claim names no entry).
  recordDue_at_piece: RecordDue behind an accept of the piece, from RecordRest there, K6Left and the
      two
      tests noTablesB, readsWideB in front, the test laidThere and PlanK6's clause named, at
          the readers and the runs of a link Lk.

Every letter under "there is": none in the tops' conclusions but below_yes_seated's b6 (pinned by
blockOf), rs, gs (the yes's own).
What it does not say. THAT THE TWO TESTS ACCEPT IN FRONT OF THE SUB-PROTOCOL: no item of the table's
promise says either yet (two items of the door are asked for). RecordRest: nobody's. Nothing on
soundness.
-/
import Johnson.Desc.Kinds.Law.HeadRidesSays
import Johnson.Desc.Kinds.Law.K6OpenedCut
import Johnson.Desc.Kinds.Law.DataSeatedOfLaid

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes.Params (ReqLayout)
open VerifiableInference.Desc.First (S Numbers)

/-- **RecordDue's other clauses.** -/
def RecordRest (arr : Nat → Nat → Nat) (N : Numbers) (Wp : OnBytes.Model.Verify.Public)
    (layout : ReqLayout) (num : Nat → Nat → Nat) (n rb : Nat) (P8 : K8.ReadsQuiet.PH)
    (St : Sound.Stated) (s : S) (aK : K9.Part) (cU : Nat × String) : Prop :=
  K9.segAt? s = some aK ∧ aK.L.check.rows.layout = layout ∧
    MatsSeated (ColFour Wp.hS Wp.HLy (OnBytes.Model.Verify.borderOf Wp.y)) arr N Wp (N.sent 24 0) aK
        num
      layout ∧
    (∃ (o : Nat) (x : Nat × Nat), K9L.maskOracle aK.L.check.frame = some o ∧
      K9.seatAt (N.sent 24 0) aK.d.book o = some x ∧ x ∈ N.group 24 ∧ arr x.1 x.2 = n ∧
      aK.d.st.rowBits o .mask = rb) ∧
    aK.L.arrayOf[readsOf Wp]? = some cU ∧
    StatedAt Wp P8 St s cU ∧
    ∀ gk, s.lookHeard? = some gk → gk.cEnd.ents = #[]

namespace AtTable

open OnBytes.Maker OnBytes.Flat Johnson.Pack
open VerifiableInference.Desc.Sound (Piece Frame MsgT out_yes)

variable {P Cells Tok : Type} {Wp : OnBytes.Model.Verify.Public} {fld : Fmt.Fld} {Fr : Frame}
  {q : Piece (_root_.Run.ckP fld) Fr (P × S) Claim (Wit Cells Tok MsgT)} {l : ℕ}
  {bef : List (ℕ × ℕ)} {B bS : Block S Claim}

/-- **A yes of the piece is an accept of the strict reading of blockOf's value.** -/
theorem below_yes_seated (H : Seated Wp fld Fr q l bef B bS) (a b : (P × S) × Fr.E.Str)
    (τ : Iop.Tr (uLT (_root_.Run.ckP fld) q.ds)) (h : q.ior.red.out a τ = some b) :
    ∃ (b6 : Block S Unit) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64))),
      blockOf Wp l = some b6 ∧ (Sound.below b6).decide a.1.2 rs gs = .ok b.1.2 := by
  obtain ⟨rs, gs, hd⟩ := out_yes q a b τ h
  rw [H.piece] at hd
  have e' : ((Sound.below B).decide a.1.2 rs gs).map (fun s => (a.1.1, s)) = .ok b.1 := hd
  obtain ⟨b6, b0, h6, hY, hN0⟩ := seated_across H.lot
  cases hb : (Sound.below B).decide a.1.2 rs gs with
  | error m =>
    rw [hb] at e'
    cases e'
  | ok s' =>
    rw [hb] at e'
    have e2 : (a.1.1, s') = b.1 := Except.ok.inj e'
    rw [← e2]
    exact ⟨b6, rs, gs, h6, (hY.below.2 _ _ _ _).2 ((H.narrows.trans hN0).below.2 _ _ _ _ hb)⟩

/-- **The kind's whole condition in front of a yes.** -/
theorem k6On_front (H : Seated Wp fld Fr q l bef B bS) (hplan : planB Wp = true)
    (a b : (P × S) × Fr.E.Str) (τ : Iop.Tr (uLT (_root_.Run.ckP fld) q.ds))
    (h : q.ior.red.out a τ = some b) (hL : K6Left Wp a.1.2) : K6On Wp a.1.2 := by
  obtain ⟨⟨rs, gs, hd⟩, _⟩ := Sound.yes_of_part q B H.piece a b τ h
  have hst := startB_yes H.lot (H.narrows.2 _ _ _ _ hd)
  rw [Came.k6On_iff]
  refine ⟨hplan, ?_⟩
  unfold K6OnB
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨(Came.wellLaidB_iff _).2 hL.1, hst⟩, (Came.tokenB_iff _ _).2 hL.2.1⟩,
    (Came.cEndB_iff _ _).2 hL.2.2⟩

/-- **RecordDue behind an accept of the piece.** -/
theorem recordDue_at_piece (H : Seated Wp fld Fr q l bef B bS) (hplan : planB Wp = true)
    (arr : ℕ → ℕ → ℕ) (N : Numbers) (layout : ReqLayout) (num : ℕ → ℕ → ℕ) (n rb : ℕ)
    (P8 : K8.ReadsQuiet.PH) (St : Sound.Stated) (l' piece : ℕ) (Lk : Link S Claim)
    (KS : K6States Wp.hS (readsOf Wp) (parOf Wp.hS (workOf Wp)) l' piece (K9.statesOfLink Lk) 3)
    (small : S → Option K9.Read) (a b : (P × S) × Fr.E.Str)
    (τ : Iop.Tr (uLT (_root_.Run.ckP fld) q.ds)) (h : q.ior.red.out a τ = some b)
    (hL : K6Left Wp a.1.2) (Z1 : noTablesB a.1.2 = true)
    (Z2 : readsWideB (readsOf Wp) (P8.hp.nU.getD 2 0) a.1.2 = true) (aK : K9.Part)
    (cU : ℕ × String) (T : Meaning.laidThere Wp (Meaning.sizesOf Wp) layout = true)
    (p1 : ∀ (μ : Fin (Meaning.sizesOf Wp 24).NM) (r c : Nat),
      r < Alg.symRows ((Meaning.sizesOf Wp 24).m μ) → c < (Meaning.sizesOf Wp 24).k μ →
      ColFour Wp.hS Wp.HLy (OnBytes.Model.Verify.borderOf Wp.y) μ.val c →
      Sound.namedOnce arr N 24 (seatLay Wp layout num 24 μ r c).1 = true)
    (hmf : aK.F.mf.size ≤ Wp.H.ns) (R : RecordRest arr N Wp layout num n rb P8 St b.1.2 aK cU) :
    RecordDue arr N Wp layout num n rb P8 St (K9.statesOfLink Lk)
      (K9.readersOfLink ⟨small, k6Silent P8 (K9.statesOfLink Lk)⟩ Lk) b.1.2 aK cU := by
  obtain ⟨b6, rs, gs, h6, hd⟩ := below_yes_seated H a b τ h
  obtain ⟨f1, f2, f3, f4⟩ := four_behind Wp l b6 h6 a.1.2 b.1.2 rs gs hd
    (k6On_front H hplan a b τ h hL) P8 Z1 Z2 l' piece 3 Lk KS small
  obtain ⟨r1, r2, r3, r4, r6, r7, r8⟩ := R
  exact ⟨r1, r2, dataSeated_of_laid arr N Wp (N.sent 24 0) aK num layout T r2 p1 r3, r4, hmf, f1,
      f2,
    r6, r7, f3, f4, r8⟩

end AtTable

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.below_yes_seated
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6On_front
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.recordDue_at_piece
