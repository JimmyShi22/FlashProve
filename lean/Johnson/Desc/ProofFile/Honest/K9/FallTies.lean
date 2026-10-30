-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/FallTies.lean: K9's FALL AS THE LIST OF FALLS LAYS IT (`quietFall p n top notGood` at p
off the lot's reading, n := the tests' number of filled slots, top := the tests' second number less 1, cut off at 0:
`quietFallsAt`, Honest/K9/Falls.lean) AGAINST K9's FALL AS IT IS COUNTED (`k9_fallDebt`, `k9_fallDebt_blocks`,
Honest/K9/FallDebtK9.lean, where n, top and Pn are letters): THREE OF THE FOUR TIES THAT THAT FILE's HEAD NAMES AS
WANTED, AND THE COUNT AT THE LIST's OWN NUMBERS. Typed on a question of the frame's pen of its row 12 ("the shares"). No
file of ours turns by it. Statements and proofs; no goal is stated.
  `k9At_is`   the library's `IM.k9At Z l`, which K9's seat reads (`SeatedFree.numbers`), IS the lot's `k9Where
      (k9Stretches Z) l`, which `quietFalls` reads: by rfl: the library's name is an abbreviation
  `sizeOfE_is`   the stated share's lower number is the count's: sizeOfE = Fmt.Fld.two.p ^ 3 · `share_first_val`: the
      value, as the frame reads a stated share (`Odds.val`, Honest/Law/SharesHeld.lean), of the share's first half
      `batFallShare n top sizeOfE` is n * top of sizeOfE: by rfl
  `tests_plan`, `tests_plan_head`   at p4 and twelve groups: the second number of the library's `testsWhere X l 0` is
      the plan's number of claims, as the library's `planClaimsAt` reads it below 24, and X.H.nLin at 24
  **`planned_at_front`**   in the goals' scope, under an opening O, l < 25: at every state reached by the chain's own
      blocks in front of segment l's batching, wherever K9's lens answers, the ledger's planned number of claims is that
      second number (the library's `planClaims_at_batch`, `planClaims_at_head`). This is the tie that
      Honest/K9/FallDebtK9.lean's and Falls.lean's heads call shown nowhere
  **`k9_fallDebt_list`**, **`k9_fallDebt_list_blocks`**   so, at K9's seat Sd with its w: `FallDebt` of `quietFall p
      w.2.2.filled (w.2.1 - 1) notGood`, at every notGood and ft, at every Q that gives of the state in front: `goodW`
      at w.2.2.filled, and that it is reached; the bound is w.2.2.filled * (w.2.1 - 1) of sizeOfE: THE VALUE OF THE
      STATED SHARE's FIRST HALF (`share_first_val`), at typed challenges; kapSl 128 ^ 3 times that at strings of hash
      blocks
  `k4_used_is`   BESIDE: in scope, at a feed-forward segment: the feed-forward kind's own number of slots (p4.hp.used,
      p4 off the library's `LPFK9.k4ParAt`) is the tests' number of filled slots: the first of the two things that
      Honest/K9/AtSeat.lean's head calls shown nowhere of that kind's own "free-slot"; the second (its run is asked
      behind another run, at a later state) stays
SINCE THIS FILE the words "shown nowhere" (Honest/K9/FallDebtK9.lean's head) and "two readings of the plan, tied nowhere
yet" (Falls.lean's) are overtaken at states reached; these two files are not turned (the second lies, at its sum,
beneath the frame's list of falls).
WHAT STAYS OF THAT HEAD's LIST. notGood: A LETTER, WITH NO PAYER: the fourth tie (its lower number is not 0) is whoever
lays it · at strings of hash blocks the bound is kapSl 128 ^ 3 times the share's first half: the stated share holds no
such factor · where silence of marks pays `goodW` through Q, the share's second half pays the same event again · all of
that head's (3) to (6).
GROUND: beside the sealed library, what lies beneath Honest/K9/FallDebtK9.lean (files of the house of K8's and of the
frame's row 12 among it).
WHAT IS NOT CLAIMED. `goodW` at any state. That a state is reached. The seat (`free_at_seat_all`,
Honest/K9/AtSeatAll.lean, hands it in scope). No number is evaluated. No member; outside this file the nine are called
by no line; Honest/K9/AllTogether.lean alone imports it. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K9.FallDebtK9
import Johnson.Desc.First.Link.Law.PlanClaimsAtBatch
import Johnson.LPFK9R.K4Ties
import Johnson.IMR.K4Seat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open OnBytes.Maker (RDT uLT drawnT)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.LinkJoin (planClaimsAt planClaims_at_batch planClaims_at_head)
open Johnson.Desc.First.Walk.Tied (Reach)
open ProofFile.Honest (Odds Fall FallDebt)
open Iop
open scoped ENNReal

/-- The two readings of K9's numbers at a segment are one: the library's name is an abbreviation of the lot's. -/
theorem k9At_is (Z : ProofFile.Pub) (l : ℕ) : IM.k9At Z l = ProofFile.k9Where (ProofFile.k9Stretches Z) l := rfl

/-- The stated share's lower number is the size that the count's bound divides by. -/
theorem sizeOfE_is : sizeOfE = Fmt.Fld.two.p ^ 3 := by
  unfold sizeOfE
  rfl

/-- The value, as the frame reads a stated share, of the first half of K9's fall's share. -/
theorem share_first_val (n top : ℕ) :
    (batFallShare n top sizeOfE).val = ((n * top : ℕ) : ℝ≥0∞) / ((sizeOfE : ℕ) : ℝ≥0∞) := rfl

/-- Below the head's segment the tests' second number is the plan's number of claims. -/
theorem tests_plan {X : Verify.Public} (h4 : X.p4 = true) (hN : X.NGr = 12) {l : ℕ} (hl : l < 24)
    {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (ht : Desc.K9.testsWhere X l 0 = some w) :
    planClaimsAt X l = some w.2.1 := by
  unfold Desc.K9.testsWhere at ht
  simp only [h4, hN, if_true] at ht
  have e1 : (l == 2 * 12) = false := by
    rw [beq_eq_false_iff_ne]
    omega
  rw [e1] at ht
  unfold planClaimsAt
  by_cases hp : l % 2 = 0
  · have e2 : (l % 2 == 0) = true := beq_iff_eq.2 hp
    rw [e2] at ht
    obtain ⟨hpl, e0, e⟩ := Option.map_eq_some_iff.1 ht
    rw [if_pos hp, e0, ← e]
    rfl
  · have e2 : (l % 2 == 0) = false := beq_eq_false_iff_ne.2 hp
    rw [e2] at ht
    obtain ⟨a, e0, e⟩ := Option.map_eq_some_iff.1 ht
    rw [if_neg hp, e0, ← e]
    rfl

/-- At the head's segment. -/
theorem tests_plan_head {X : Verify.Public} (h4 : X.p4 = true) (hN : X.NGr = 12)
    {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (ht : Desc.K9.testsWhere X 24 0 = some w) :
    w.2.1 = X.H.nLin := by
  unfold Desc.K9.testsWhere at ht
  simp only [h4, hN, if_true] at ht
  have e1 : (24 == 2 * 12) = true := rfl
  rw [e1] at ht
  rw [← Option.some.inj ht]

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **At every state reached in front of a segment's batching the ledger's planned number of claims is the tests' second
number.** -/
theorem planned_at_front (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (ht : Desc.K9.testsWhere Z.p.X l 0 = some w) {Q' : Type}
    {start : Q' → S} {z : Q'} {s : S}
    (hq : Reach 0 c.blocksInOrder start (14 * l + (if l = 24 then 11 else 9)) (z, s)) :
    ∀ a0, Desc.K9.atS.get? s = some a0 → a0.F.planClaimsF = w.2.1 := by
  intro a0 ha0
  have hf := Desc.K9.get_fork s a0 ha0
  obtain ⟨h4, hN, -, -⟩ := Meaning.scope_plans hS hR (IM.ground_publicK O.pub O.blank)
  rw [← O.W] at ht
  by_cases h24 : l = 24
  · subst h24
    obtain ⟨G, g1, g2⟩ := planClaims_at_head hS hR O hq
    obtain rfl : a0.F = G := Option.some.inj (hf.symm.trans g1)
    rw [g2, tests_plan_head h4 hN ht]
  · rw [if_neg h24] at hq
    obtain ⟨G, n, g1, g2, g3⟩ := planClaims_at_batch hS hR O (by omega : l < 24) hq
    obtain rfl : a0.F = G := Option.some.inj (hf.symm.trans g1)
    rw [g3]
    exact Option.some.inj (g2.symm.trans (tests_plan h4 hN (by omega) ht))

/-- At a feed-forward segment the feed-forward kind's own number of slots is the tests' number of filled slots. -/
theorem k4_used_is (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12)
    {p4 : OnBytes.Desc.First.K4.Par} (hk : LPFK9.k4ParAt Z Bs.G₀ (2 * g) = some p4)
    {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (ht : Desc.K9.testsWhere Z.p.X (2 * g) 0 = some w) :
    p4.hp.used = w.2.2.filled := by
  obtain ⟨-, -, xm, -, -, hx, -, hl, -, -, hG, -⟩ := IM.k4_of hS hR O g hg
  have ep : p4 = LPFK9.parOfMember xm := Option.some.inj (hk.symm.trans (LPFK9.k4ParAt_of_mem hx hl))
  obtain ⟨h4, hN, -, -⟩ := Meaning.scope_plans hS hR (IM.ground_publicK O.pub O.blank)
  rw [← O.W] at ht
  unfold Desc.K9.testsWhere at ht
  simp only [h4, hN, if_true] at ht
  have e1 : (2 * g == 2 * 12) = false := by
    rw [beq_eq_false_iff_ne]
    omega
  have e2 : ((2 * g) % 2 == 0) = true := by
    rw [beq_iff_eq]
    omega
  have e3 : 2 * g / 2 = g := by omega
  rw [e1, e2, e3, hG] at ht
  rw [ep, ← Option.some.inj ht]
  rfl

/-- **K9's fall in the cover's form AT THE LIST's OWN NUMBERS, at typed challenges**: n := the tests' number of filled
slots, top := the tests' second number less 1: the bound is the stated share's first half. -/
theorem k9_fallDebt_list (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {Lk : Link S Claim} {p : Desc.K9.Where} {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere}
    (Sd : SeatedFree c Z l (if l = 24 then 9 else 7) Lk p w) (d : RDT) (he : d.entry = Desc.K9.entry p)
    (h5 : d.kind ≠ .seeds) (h6 : d.kind ≠ .sealed) (notGood : Odds) (ft : ℕ)
    (Q : List Fmt.Drawn → S → Prop) {Q' : Type} (start : Q' → S)
    (hQ : ∀ fr s', Q fr s' → goodW p (claimsInBy Lk.each Lk.hear Lk.order) s' w.2.2.filled ∧
      ∃ z, Reach 0 c.blocksInOrder start (14 * l + (if l = 24 then 11 else 9)) (z, s')) :
    FallDebt (_root_.Run.ck .two) (quietFall p w.2.2.filled (w.2.1 - 1) notGood) ft
      (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order))
      (c.blocksInOrder.drop (14 * l + (if l = 24 then 11 else 9) + 1)) [d] [] Q
      (((w.2.2.filled * (w.2.1 - 1) : ℕ) : ℝ≥0∞) / ((sizeOfE : ℕ) : ℝ≥0∞)) := by
  rw [sizeOfE_is]
  exact k9_fallDebt hS hR O hl Sd d he h5 h6 w.2.2.filled (w.2.1 - 1) w.2.1 notGood ft Q fun fr s' hq => by
    obtain ⟨hg, z, hr⟩ := hQ fr s' hq
    exact ⟨hg, planned_at_front hS hR O hl Sd.tested hr⟩

/-- **The same at strings of hash blocks**: the bound is kapSl 128 ^ 3 times the stated share's first half. -/
theorem k9_fallDebt_list_blocks (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {Lk : Link S Claim} {p : Desc.K9.Where} {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere}
    (Sd : SeatedFree c Z l (if l = 24 then 9 else 7) Lk p w) (d : RDT) (he : d.entry = Desc.K9.entry p)
    (h5 : d.kind ≠ .seeds) (h6 : d.kind ≠ .sealed) (notGood : Odds) (ft : ℕ)
    (Q : List Fmt.Drawn → S → Prop) {Q' : Type} (start : Q' → S)
    (hQ : ∀ fr s', Q fr s' → goodW p (claimsInBy Lk.each Lk.hear Lk.order) s' w.2.2.filled ∧
      ∃ z, Reach 0 c.blocksInOrder start (14 * l + (if l = 24 then 11 else 9)) (z, s')) :
    FallDebt (_root_.Run.ckP .two) (quietFall p w.2.2.filled (w.2.1 - 1) notGood) ft
      (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order))
      (c.blocksInOrder.drop (14 * l + (if l = 24 then 11 else 9) + 1)) [d] [] Q
      (kapSl 128 ^ 3 * ((w.2.2.filled * (w.2.1 - 1) : ℕ) : ℝ≥0∞) / ((sizeOfE : ℕ) : ℝ≥0∞)) := by
  rw [sizeOfE_is]
  exact k9_fallDebt_blocks hS hR O hl Sd d he h5 h6 w.2.2.filled (w.2.1 - 1) w.2.1 notGood ft Q fun fr s' hq => by
    obtain ⟨hg, z, hr⟩ := hQ fr s' hq
    exact ⟨hg, planned_at_front hS hR O hl Sd.tested hr⟩

end

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.k9At_is
#print axioms ProofFile.Honest.K9.sizeOfE_is
#print axioms ProofFile.Honest.K9.share_first_val
#print axioms ProofFile.Honest.K9.tests_plan
#print axioms ProofFile.Honest.K9.tests_plan_head
#print axioms ProofFile.Honest.K9.planned_at_front
#print axioms ProofFile.Honest.K9.k4_used_is
#print axioms ProofFile.Honest.K9.k9_fallDebt_list
#print axioms ProofFile.Honest.K9.k9_fallDebt_list_blocks
