-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Goal/Numbers/K14RadiiTerms.lean: LLHARD/K14Radii.lean's "there are sentU, rad2, rad5" as three terms over
the shared chain's parameters Q, so that a filling of the shared table can lay them with no letter
left.
  sentUAt Q: what goes out with o_u: (withU Q.S).getD #[]
  rad2At fl Q, rad5At fl Q: the two functions of radii: radFrom of the two places at the pairs of
      the shared chain's first two written rows of sendings of file fl (2: a proof file; 0: a key
      file)
  radii_terms_of: SeatRadii at these three terms, from the same tests as radii_of
  radii_terms_typed, seat_radii_terms, radii_terms_key: at the typed parameters; at the seat, from
      Written Z x; at a key file
  size_of_ten: the number of messages that go out with o_u is 2, wherever the ten premises of
      Johnson/Goal/Numbers/K14PlanTen.lean stand

What is not claimed. Written Z x. What the heads of the files named do not claim. Nothing on
soundness, on an honest prover or on hiding.

-/
import Johnson.Goal.Numbers.K14Radii
import Johnson.Goal.Numbers.K14PlanTen

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Johnson.G (dryProofFull dryKeyFull codesFull2 sendsFullLit packFullLit)
open VerifiableInference.Desc.K1 (condPort radFrom realSized litAt)
open Lk6.AtPlan (keyFull)

/-- What goes out with o_u. -/
def sentUAt (Q : P14) : Array OracleNotice := (withU Q.S).getD #[]

/-- The radii at o_u's sending. -/
def rad2At (fl : ℕ) (Q : P14) : ℕ → ℕ :=
  radFrom (parU Q (sentUAt Q)) ((((litAt sendsFullLit packFullLit fl 1)[0]?).map (·.2.l)).getD [])

/-- The radii at o_omega's sending. -/
def rad5At (fl : ℕ) (Q : P14) : ℕ → ℕ :=
  radFrom (parO Q) ((((litAt sendsFullLit packFullLit fl 1)[1]?).map (·.2.l)).getD [])

/-- **SeatRadii at the three terms.** -/
theorem radii_terms_of {fl work : ℕ} {set : Setting} {scope : Scope} {codes : Codes} {S : LinShape}
    {Wr : Rounds} {item : ℕ} {bp : List (ℕ × ℕ)} {rU rO rSp : ℕ}
    (hc : K14Cond fl ⟨set, scope, codes, S, item, bp⟩ Wr)
    (hR : k14RB S Wr recordRadius cMax work = true) (hi : indexB S = true)
    (hr : K14Rounds S Wr recordRadius cMax work) (h64 : pointNB S Wr cMax64 64 = true)
    (hs : sendsLB fl ⟨set, scope, codes, S, 0, [(1, 0)]⟩ Wr = true)
    (hp : fourB codes S = true)
    (hq : radiiB fl ⟨set, scope, codes, S, 0, [(1, 0)]⟩ rU rO rSp = true) :
    SeatRadii fl work ⟨set, scope, codes, S, item, bp⟩ Wr
      (sentUAt ⟨set, scope, codes, S, item, bp⟩) (rad2At fl ⟨set, scope, codes, S, item, bp⟩)
      (rad5At fl ⟨set, scope, codes, S, item, bp⟩) rU rO rSp := by
  obtain ⟨sentU, yU, yO, e1, e2, a1, a2, a3, a4⟩ := ours_at_x item bp hc hR hs
  have s1 : sentUAt ⟨set, scope, codes, S, item, bp⟩ = sentU := by
    show (withU S).getD #[] = sentU
    rw [a1]
    rfl
  have r2 : rad2At fl ⟨set, scope, codes, S, item, bp⟩ =
      radFrom (parU ⟨set, scope, codes, S, item, bp⟩ sentU) yU.2.l := by
    unfold rad2At
    rw [s1, e1]
    rfl
  have r5 : rad5At fl ⟨set, scope, codes, S, item, bp⟩ =
      radFrom (parO ⟨set, scope, codes, S, item, bp⟩) yO.2.l := by
    unfold rad5At
    rw [e2]
    rfl
  rw [s1, r2, r5]
  unfold fourB at hp
  simp only [Bool.and_eq_true] at hp
  obtain ⟨⟨⟨p1, p2⟩, p3⟩, p4⟩ := hp
  unfold radiiB at hq
  have a1' : withU (⟨set, scope, codes, S, 0, [(1, 0)]⟩ : P14).S = some sentU := a1
  rw [e1, e2, Option.all_some, Option.all_some, a1', Option.all_some] at hq
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hq
  exact ⟨⟨a1, a2, a3, hi, hr, h64, a4, hs, p1, p2, p3, p4, hc.ha, hc.hi, hc.hroom⟩,
    hq.1, hq.2.1, hq.2.2⟩

/-- **At the typed parameters of a proof file.** -/
theorem radii_terms_typed : ∃ x : LinSized, realSized = some (x, codesFull2) ∧
    ∀ (item : ℕ) (bp : List (ℕ × ℕ)), bp ≠ [] →
      SeatRadii 2 28 ⟨recordSet, .shared, codesFull2, x.shape, item, bp⟩ dryProofFull.2.1
        (sentUAt ⟨recordSet, .shared, codesFull2, x.shape, item, bp⟩)
        (rad2At 2 ⟨recordSet, .shared, codesFull2, x.shape, item, bp⟩)
        (rad5At 2 ⟨recordSet, .shared, codesFull2, x.shape, item, bp⟩) 8342416 3131972 6117 := by
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
  exact ⟨x, a1, fun item bp hbp => radii_terms_of (a3 item bp hbp) hR hi c4 h64 hs hp hq⟩

/-- **At the seat: no "there is".** -/
theorem seat_radii_terms {Z : ProofFile.Pub} {x : LinSized} (hx : realSized = some (x, codesFull2))
    (h : Written Z x) {N : H2U.Places4} (hN : H2U.placesOfMade Z.made = .ok N) :
    SeatRadii 2 28 (p14Of Z.p.chains (Desc.K14.beforePointOf N)) dryProofFull.2.1
      (sentUAt (p14Of Z.p.chains (Desc.K14.beforePointOf N)))
      (rad2At 2 (p14Of Z.p.chains (Desc.K14.beforePointOf N)))
      (rad5At 2 (p14Of Z.p.chains (Desc.K14.beforePointOf N))) 8342416 3131972 6117 := by
  obtain ⟨x', a1, a2⟩ := radii_terms_typed
  obtain rfl := sized_one hx a1
  have e : p14Of Z.p.chains (Desc.K14.beforePointOf N) =
      ⟨recordSet, .shared, codesFull2, x.shape, 0, Desc.K14.beforePointOf N⟩ := by
    unfold p14Of
    simp only [h.set, h.codes, h.shape, h.batch, Bool.false_eq_true, if_false]
  rw [e]
  exact a2 0 _ (h.before N hN)

/-- **At the typed parameters of a key file.** -/
theorem radii_terms_key (item : ℕ) (bp : List (ℕ × ℕ)) (hbp : bp ≠ []) :
    SeatRadii 0 32 ⟨recordSet, .once, keyFull.codes, keyFull.once.shape, item, bp⟩ dryKeyFull.2.1
      (sentUAt ⟨recordSet, .once, keyFull.codes, keyFull.once.shape, item, bp⟩)
      (rad2At 0 ⟨recordSet, .once, keyFull.codes, keyFull.once.shape, item, bp⟩)
      (rad5At 0 ⟨recordSet, .once, keyFull.codes, keyFull.once.shape, item, bp⟩)
      8342420 3138896 6130 :=
  radii_terms_of (k14_key item bp hbp) key_testR index_key k14_rounds_key key_test64 key_testL
    four_key radii_key

/-- The number of messages that go out with o_u, wherever SeatRadii's hUw and the ten stand. -/
theorem size_of_ten {cs : Codes} {Q : P14} {sentU : Array OracleNotice} {layU layO : TreeLay}
    (h : Ten cs Q.S sentU layU layO) : (sentUAt Q).size = 2 := by
  show ((withU Q.S).getD #[]).size = 2
  rw [h.hU]
  exact h.hsU

end Desc.K14.Law

#print axioms Desc.K14.Law.radii_terms_of
#print axioms Desc.K14.Law.radii_terms_typed
#print axioms Desc.K14.Law.seat_radii_terms
#print axioms Desc.K14.Law.radii_terms_key
#print axioms Desc.K14.Law.size_of_ten
