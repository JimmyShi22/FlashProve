-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Goal/Numbers/K14Radii.lean: the three radii that K14's files' ledger writes as rad2 0, rad5 0, rad5 1 (the
radii at which K1's law is called for o_u, o_omega and the split's mask message, and which another
file's list of the shared chain's members takes as its three letters) ARE NUMBERS: a proof file:
8342416, 3131972, 6117; a key file: 8342420, 3138896, 6130. SeatBinders.lean hands the two
functions rad2, rad5 behind an "there is": here they come with these three values, so that the
comparison "the radius fits" (Johnson/Goal/Numbers/K12Fit.lean) is had at the ledger's own letters.
  ours_at_x: K14OwnAt.lean's ours_at with its witnesses in the open: rad2 and rad5 are radFrom
      of the two places at the pairs of the shared chain's first two written rows of sendings
  radiiB, radii_real, radii_key: the three values: a test with code; its yes by Lean's kernel
  SeatRadii: SeatBinders with the three equations
  binders_radii_typed, seat_binders_radii, binders_radii_key: at the typed parameters, at the seat
      (from Written Z x), at a key file
  pairs_at_letters: so that list's three pairs at these letters are K1's written pairs
  fit_at_letters_real, fit_at_letters_key: and fitB says yes at them, at both proximity tests

So one number stands on all three sides for each message: in the comparison "the radius fits", in
K1's condition (condPort: inside the Johnson range), and in the list's bound of the error that the
ledger charges for that message's out-of-domain sample (errPort reads lOf at rad k).

What is not claimed. Written Z x. What the heads of the files named do not claim. Nothing on
soundness, on an honest prover or on hiding.

-/
import Johnson.Goal.Numbers.SeatBinders
import Johnson.Goal.Numbers.K12Members

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open OnBytes.Params.Prices (AtRecord)
open Johnson.G (dryProofFull dryKeyFull codesFull2 sendsFullLit packFullLit)
open Iop Run OnBytes.Maker OnBytes.Flat
open VerifiableInference.Desc (Block Wit)
open VerifiableInference.Desc.K1 (seedMaps seedMaps_ok condPort errPort seedEntry seed_draws radFrom
  realSized litAt powB powB_cmp nVals_seed seeds_pos PlaceOk)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared
open H2K.Member (setAt szUFull szOFull)
open Lk6.AtPlan (keyFull)
open scoped ENNReal

/-- **ours_at with its witnesses in the open.** -/
theorem ours_at_x {fl work : ℕ} {set : Setting} {scope : Scope} {codes : Codes} {S : LinShape}
    {Wr : Rounds} (item : ℕ) (bp : List (ℕ × ℕ))
    (hc : K14Cond fl ⟨set, scope, codes, S, item, bp⟩ Wr)
    (hR : k14RB S Wr recordRadius cMax work = true)
    (hs : sendsLB fl ⟨set, scope, codes, S, 0, [(1, 0)]⟩ Wr = true) :
    ∃ (sentU : Array OracleNotice) (yU yO : ℕ × VerifiableInference.Desc.K1.SendRow),
      (litAt sendsFullLit packFullLit fl 1)[0]? = some yU ∧
      (litAt sendsFullLit packFullLit fl 1)[1]? = some yO ∧ withU S = some sentU ∧
      condPort (parU ⟨set, scope, codes, S, item, bp⟩ sentU)
        (radFrom (parU ⟨set, scope, codes, S, item, bp⟩ sentU) yU.2.l) = true ∧
      condPort (parO ⟨set, scope, codes, S, item, bp⟩)
        (radFrom (parO ⟨set, scope, codes, S, item, bp⟩) yO.2.l) = true ∧
      OursBelow ⟨set, scope, codes, S, item, bp⟩ Wr sentU
        (radFrom (parU ⟨set, scope, codes, S, item, bp⟩ sentU) yU.2.l)
        (radFrom (parO ⟨set, scope, codes, S, item, bp⟩) yO.2.l) := by
  obtain ⟨sentU, hU, ⟨yU, hrU, -, hCU⟩, h1U⟩ := hc.sendU
  obtain ⟨⟨yO, hrO, -, hCO⟩, h1O⟩ := hc.sendO
  have hU' : withU S = some sentU := hU
  unfold sendsLB at hs
  simp only [Bool.and_eq_true] at hs
  obtain ⟨⟨⟨s1, s2⟩, s3⟩, s4⟩ := hs
  rw [hU', Option.all_some] at s1
  rw [hrU, Option.all_some, hU', Option.all_some] at s3
  rw [hrO, Option.all_some] at s4
  have s1' := of_decide_eq_true s1
  have s2' := of_decide_eq_true s2
  unfold k14RB at hR
  simp only [Bool.and_eq_true] at hR
  obtain ⟨⟨-, r3⟩, r6⟩ := hR
  refine ⟨sentU, yU, yO, hrU, hrO, hU', hCU, hCO, ?_⟩
  intro P₁ Cl Cells Tok Fr rest k x hk ht
  refine ownK_below _ _ _ _ _ _ _ _ _ rest _ k x hk (ownDs_below _ _ _ _ _ _ _ _ _ _ k x.ds
    (fun d₁ d₂ e1 e2 => ?_) (fun d e1 e2 => ?_) (fun d₁ d₂ e1 e2 => ?_) (fun d e1 e2 => ?_))
  · have e := Option.some.inj ((ht.1 d₁ d₂ e1 e2).symm.trans s1')
    rw [parU_free set scope codes S item bp sentU]
    exact seed_brick _ h1U _ s3 d₁ d₂ (congrArg Prod.fst e) (congrArg Prod.snd e)
  · have w := ht.2.1 d e1 e2
    rw [w] at r3
    simp only [Option.any_some, Bool.and_eq_true, decide_eq_true_eq] at r3
    obtain ⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, -⟩, a6⟩ := r3
    have sd := sends_of d a1
    rw [a2, a3, a4] at sd
    exact pos_brick d _ _ _ sd a6
  · have e := Option.some.inj ((ht.2.2.1 d₁ d₂ e1 e2).symm.trans s2')
    rw [parO_free set scope codes S item bp]
    exact seed_brick _ h1O _ s4 d₁ d₂ (congrArg Prod.fst e) (congrArg Prod.snd e)
  · have w := ht.2.2.2 d e1 e2
    rw [w] at r6
    simp only [Option.any_some, Bool.and_eq_true, decide_eq_true_eq] at r6
    obtain ⟨⟨⟨⟨a1, a2⟩, a3⟩, -⟩, a5⟩ := r6
    have sd := sends_of d a1
    rw [a2, a3] at sd
    refine vec_brick d _ _ sd ?_
    rw [card_GE_num]
    exact a5

/-- **The three values**, as a test. -/
def radiiB (fl : ℕ) (Q : P14) (rU rO rSp : ℕ) : Bool :=
  ((litAt sendsFullLit packFullLit fl 1)[0]?).all (fun y => (withU Q.S).all fun s =>
    decide (radFrom (parU Q s) y.2.l 0 = rU)) &&
  ((litAt sendsFullLit packFullLit fl 1)[1]?).all fun y =>
    decide (radFrom (parO Q) y.2.l 0 = rO) && decide (radFrom (parO Q) y.2.l 1 = rSp)

theorem radii_real : (realSized.any fun p =>
    radiiB 2 ⟨recordSet, .shared, p.2, p.1.shape, 0, [(1, 0)]⟩ 8342416 3131972 6117) = true := by
  decide +kernel

theorem radii_key :
    radiiB 0 ⟨recordSet, .once, keyFull.codes, keyFull.once.shape, 0, [(1, 0)]⟩
      8342420 3138896 6130 = true := by
  decide +kernel

/-- SeatBinders with the three radii's values. -/
structure SeatRadii (fl work : ℕ) (Q : P14) (Wr : Rounds) (sentU : Array OracleNotice)
    (rad2 rad5 : ℕ → ℕ) (rU rO rSp : ℕ) : Prop where
  binders : SeatBinders fl work Q Wr sentU rad2 rad5
  hrU : rad2 0 = rU
  hrO : rad5 0 = rO
  hrSp : rad5 1 = rSp

/-- From the pieces. -/
theorem radii_of {fl work : ℕ} {set : Setting} {scope : Scope} {codes : Codes} {S : LinShape}
    {Wr : Rounds} {item : ℕ} {bp : List (ℕ × ℕ)} {rU rO rSp : ℕ}
    (hc : K14Cond fl ⟨set, scope, codes, S, item, bp⟩ Wr)
    (hR : k14RB S Wr recordRadius cMax work = true) (hi : indexB S = true)
    (hr : K14Rounds S Wr recordRadius cMax work) (h64 : pointNB S Wr cMax64 64 = true)
    (hs : sendsLB fl ⟨set, scope, codes, S, 0, [(1, 0)]⟩ Wr = true)
    (hp : fourB codes S = true)
    (hq : radiiB fl ⟨set, scope, codes, S, 0, [(1, 0)]⟩ rU rO rSp = true) :
    ∃ sentU rad2 rad5,
      SeatRadii fl work ⟨set, scope, codes, S, item, bp⟩ Wr sentU rad2 rad5 rU rO rSp := by
  obtain ⟨sentU, yU, yO, e1, e2, a1, a2, a3, a4⟩ := ours_at_x item bp hc hR hs
  unfold fourB at hp
  simp only [Bool.and_eq_true] at hp
  obtain ⟨⟨⟨p1, p2⟩, p3⟩, p4⟩ := hp
  unfold radiiB at hq
  have a1' : withU (⟨set, scope, codes, S, 0, [(1, 0)]⟩ : P14).S = some sentU := a1
  rw [e1, e2, Option.all_some, Option.all_some, a1', Option.all_some] at hq
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hq
  exact ⟨sentU, _, _, ⟨a1, a2, a3, hi, hr, h64, a4, hs, p1, p2, p3, p4, hc.ha, hc.hi, hc.hroom⟩,
    hq.1, hq.2.1, hq.2.2⟩

/-- **At the typed parameters of a proof file.** -/
theorem binders_radii_typed : ∃ x : LinSized, realSized = some (x, codesFull2) ∧
    ∀ (item : ℕ) (bp : List (ℕ × ℕ)), bp ≠ [] → ∃ sentU rad2 rad5,
      SeatRadii 2 28 ⟨recordSet, .shared, codesFull2, x.shape, item, bp⟩ dryProofFull.2.1
        sentU rad2 rad5 8342416 3131972 6117 := by
  obtain ⟨x, a1, -, a3⟩ := k14_real
  obtain ⟨x2, c1, -, -, c4⟩ := k14_rounds_real
  obtain rfl := sized_one a1 c1
  have hR := real_testR
  have hi := index_real
  have h64 := real_test64
  have hs := real_testL
  have hp := four_real
  have hq := radii_real
  rw [a1, Option.any_some] at hR hi h64 hs hp hq
  exact ⟨x, a1, fun item bp hbp => radii_of (a3 item bp hbp) hR hi c4 h64 hs hp hq⟩

/-- **At the seat.** -/
theorem seat_binders_radii {Z : ProofFile.Pub} {x : LinSized} (hx : realSized = some (x, codesFull2))
    (h : Written Z x) {N : H2U.Places4} (hN : H2U.placesOfMade Z.made = .ok N) :
    ∃ sentU rad2 rad5, SeatRadii 2 28 (p14Of Z.p.chains (Desc.K14.beforePointOf N))
      dryProofFull.2.1 sentU rad2 rad5 8342416 3131972 6117 := by
  obtain ⟨x', a1, a2⟩ := binders_radii_typed
  obtain rfl := sized_one hx a1
  have e : p14Of Z.p.chains (Desc.K14.beforePointOf N) =
      ⟨recordSet, .shared, codesFull2, x.shape, 0, Desc.K14.beforePointOf N⟩ := by
    unfold p14Of
    simp only [h.set, h.codes, h.shape, h.batch, Bool.false_eq_true, if_false]
  rw [e]
  exact a2 0 _ (h.before N hN)

/-- **At the typed parameters of a key file.** -/
theorem binders_radii_key (item : ℕ) (bp : List (ℕ × ℕ)) (hbp : bp ≠ []) : ∃ sentU rad2 rad5,
    SeatRadii 0 32 ⟨recordSet, .once, keyFull.codes, keyFull.once.shape, item, bp⟩
      dryKeyFull.2.1 sentU rad2 rad5 8342420 3138896 6130 :=
  radii_of (k14_key item bp hbp) key_testR index_key k14_rounds_key key_test64 key_testL four_key
    radii_key

/-- **The members' list's three pairs at the ledger's letters are K1's written pairs.** -/
theorem pairs_at_letters {fl work : ℕ} {Q : P14} {Wr : Rounds} {sentU : Array OracleNotice}
    {rad2 rad5 : ℕ → ℕ} {rU rO rSp : ℕ} (h : SeatRadii fl work Q Wr sentU rad2 rad5 rU rO rSp) :
    pairsOf Q.S (rad2 0) (rad5 0) (rad5 1) = pairsOf Q.S rU rO rSp := by
  rw [h.hrU, h.hrO, h.hrSp]

/-- **"The radius fits" at the ledger's letters**, in a proof file, where the shape is the typed
one. -/
theorem fit_at_letters_real {x : LinSized} (hx : realSized = some (x, codesFull2)) {work : ℕ}
    {Q : P14} {Wr : Rounds} {sentU : Array OracleNotice} {rad2 rad5 : ℕ → ℕ}
    (h : SeatRadii 2 work Q Wr sentU rad2 rad5 8342416 3131972 6117) (hS : Q.S = x.shape) :
    fitB setAt szUFull codesFull2 (pairsOf Q.S (rad2 0) (rad5 0) (rad5 1)) = true ∧
      fitB setAt szOFull codesFull2 (pairsOf Q.S (rad2 0) (rad5 0) (rad5 1)) = true := by
  obtain ⟨x', a1, a2, a3⟩ := fit_pairs_real
  obtain rfl := sized_one hx a1
  rw [pairs_at_letters h, hS]
  exact ⟨a2, a3⟩

/-- The like in a key file. -/
theorem fit_at_letters_key {work : ℕ} {Q : P14} {Wr : Rounds} {sentU : Array OracleNotice}
    {rad2 rad5 : ℕ → ℕ} (h : SeatRadii 0 work Q Wr sentU rad2 rad5 8342420 3138896 6130)
    (hS : Q.S = keyFull.once.shape) :
    fitB recordSet keyFull.once.folded.stages keyFull.codes
        (pairsOf Q.S (rad2 0) (rad5 0) (rad5 1)) = true ∧
      fitB recordSet keyFull.once.omega.stages keyFull.codes
        (pairsOf Q.S (rad2 0) (rad5 0) (rad5 1)) = true := by
  rw [pairs_at_letters h, hS]
  exact fit_pairs_key

end Desc.K14.Law

#print axioms Desc.K14.Law.ours_at_x
#print axioms Desc.K14.Law.radii_real
#print axioms Desc.K14.Law.radii_key
#print axioms Desc.K14.Law.radii_of
#print axioms Desc.K14.Law.binders_radii_typed
#print axioms Desc.K14.Law.seat_binders_radii
#print axioms Desc.K14.Law.binders_radii_key
#print axioms Desc.K14.Law.pairs_at_letters
#print axioms Desc.K14.Law.fit_at_letters_real
#print axioms Desc.K14.Law.fit_at_letters_key
