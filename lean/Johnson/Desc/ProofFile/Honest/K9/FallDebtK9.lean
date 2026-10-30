-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/FallDebtK9.lean: K9's OWN FALL ("a slot's coefficient came out 0": `quietFall`,
Honest/K9/Falls.lean) IN THE FORM IN WHICH THE FRAME's COVER ASKS A HOUSE FOR A FALL: `FallDebt`
(Honest/Law/CoverJoin.lean): at the member without a round behind a segment's batching. Statements and proofs; no goal
is stated.
  `quietPlace_is`, `batching_at`   K9's place of that member is the place under which K8 names it: both
      are the place of one member of the description's flat list; the seated batching stands at the number 
      under which K8 names it
  `speaks_of_behind`, `behind_sub`   where the batching's own step, at a round that has drawn dr, returns a state at
      which K9's share of the test speaks, and dr's elements are the one field element x: `GateSpeaks 0 b s' n none x`
      (Honest/K9/GateCount.lean); the set of messages in the form that the count's lemma takes
  **`k9_fallDebt`**, **`k9_fallDebt_blocks`**   in the goals' scope, at each segment l < 25, at the segment's seated
      batching (`SeatedFree`, a premise: `free_at_seat_all`, Honest/K9/AtSeatAll.lean, hands it in this very form):
      FallDebt C (quietFall p n top notGood) ft b ‹the members behind› [d] [] Q q, at every ft, top, notGood, at every
      Q that gives, of the state s' in front of the batching: `goodW p g s' n` (Honest/K9/GateArms.lean: "good"
      without a yes and without a length) and "the plan's number of claims is Pn wherever K9's lens answers at s'"; q
      := n * (Pn - 1) / p ^ 3 (Pn - 1: cut off at 0) at typed challenges, kapSl 128 ^ 3 times that at strings of hash
      blocks; d: a round's data with the batching's entry, its kind neither seeds nor sealed
BY: `quiet_fallDebt_of` (Johnson/P1K8R/QuietFall.lean: the walk from the cover's wide event, at
every ft, to the batching's own step at 0), `behind_iff` (CountAtStep.lean), `quiet_there` (PlacesAtFlat.lean),
`oneElem_bat` (Johnson/Desc/K8/Honest/ChiTyped.lean), `gate_of_count`, `gate_of_count_blocks` (GateOfCount.lean: from
a count of field elements to the measure over one round's messages) and our `gate_few_weak` (Honest/K9/GateArms.lean:
the count). WHAT IT IS NOT. A FORM, NOT A DEBT PAID. (1) Q's two clauses are premises: that the state in front of
the batching is good but for a mark's event is the other kinds' and ours to show (the marks' shares: not here). (2) n,
top, Pn, notGood ARE LETTERS. At the list's fall (`quietFallsAt`, Honest/K9/Falls.lean) n := w.2.2.filled, top :=
w.2.1 - 1. The fall's stated share is not compared with q here; a comparison wants: the ledger's plan's number at s'
is w.2.1, so that Pn - 1 = top (shown nowhere) · the list's p (`k9Where`) is the seat's (`IM.k9At`) · sizeOfE =
Fmt.Fld.two.p ^ 3 · notGood's lower number is not 0. AT STRINGS OF HASH BLOCKS q IS kapSl 128 ^ 3 TIMES THE SHARE's
FIRST HALF: the stated share holds no such factor. Where the marks' silence pays `goodW` through Q, the share's second
half (notGood) pays the same event again: too much, not too little. (3) `FallGuards` (the frame's "the fall speaks
only where the member refuses") is not here: it is written out at n := w.2.2.filled alone (`quiet_guards`,
Honest/K9/FallGuard.lean); at another n nothing holds the fall from speaking where the member says yes. (4) That d is
the chain's own stretch of data at that member is not shown; that a member with a typed round stands behind the head's
batching (so that the cover's tail of fixed challenges is [] there) is not shown. (5) No joiner of the cover is
called; of its premises "[d] is as long as b's rounds" is `SeatedFree.shape`'s, "what is still to do is b and the
members behind" the frame's: neither is called here. (6) It imports files beside the seal (Johnson/P1K8R/, over the
frame's row 12): not for a seal as it lies; it turns with these. No number is evaluated. No member, in
the frame's sense either: that case of the cover stays without one. That the scope, the reading of the files and the
opening can be met together: under the library's head (Honest/K9/AtHead.lean).
WHAT IS NOT CLAIMED. `goodW` at any state. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K9.GateArms
import Johnson.Desc.ProofFile.Honest.K9.Falls
import Johnson.P1K8R.QuietFall
import Johnson.P1K8R.GateOfCount

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open OnBytes.Maker (RDT uLT drawnT)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest
open ProofFile.Honest (Odds Fall FallDebt)
open Iop
open scoped ENNReal

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- The two names of one place. -/
theorem quietPlace_is (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {Lk : Link S Claim} {p : Desc.K9.Where} {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere}
    (Sd : SeatedFree c Z l (if l = 24 then 9 else 7) Lk p w) :
    quietPlace p = ProofFile.Honest.K8.quietPlace l (if l = 24 then 1 else 0) := by
  obtain ⟨b', hb', hp', _⟩ := Sd.behind
  have h := P1K8.quiet_there hS hR O hl
  have e : 14 * l + (if l = 24 then 9 else 7) + 3 = 14 * l + (if l = 24 then 11 else 9) + 1 := by
    split <;> omega
  rw [← e, hb'] at h
  rw [← hp']
  exact Option.some.inj h

/-- The seated batching stands at the number under which the house of K8 names it. -/
theorem batching_at {l : ℕ} {Lk : Link S Claim} {p : Desc.K9.Where}
    {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere}
    (Sd : SeatedFree c Z l (if l = 24 then 9 else 7) Lk p w) :
    c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? =
      some (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)) := by
  have e : 14 * l + (if l = 24 then 9 else 7) + 2 = 14 * l + (if l = 24 then 11 else 9) := by
    split <;> omega
  rw [← e]
  exact Sd.batching

/-- From the test with code at the batching's own step to the event that is counted. -/
theorem speaks_of_behind (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    (b : Block S Claim) (hb : c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b) (n : ℕ) (s' : S)
    (dr : Fmt.Drawn) (x : Cb.Gl.E)
    (h : P1K8.behindT b (fun t => (freeSlotShare n t).isSome) s' [dr] = true)
    (hx : dr.elems = [Slice.ofE x]) : GateSpeaks 0 b s' n none x := by
  obtain ⟨r, cols, t, m, hr, hy, hq⟩ := (P1K8.behind_iff hS hR O hl b hb _ s' dr).1 h
  refine ⟨r, cols, t, m, by rw [hr]; exact hx, hy, ?_⟩
  unfold quietFallTest
  cases hf : freeSlotShare n t with
  | none => rw [hf] at hq; exact nomatch hq
  | some v => rfl

/-- The set of messages at which the test with code speaks, in the form that the count's lemma takes. -/
theorem behind_sub (Ck : _root_.Run.PQ.CK) (d : RDT) (b : Block S Claim) (no : S → Bool) (s' : S)
    (ρ : Iop.Rho (uLT Ck [d])) (h : P1K8.behindT b no s' (drawnT Ck [d] ρ) = true) :
    ∃ dr, drawnT Ck [d] ρ = [dr] ∧ P1K8.behindT b no s' [dr] = true := by
  cases hd : drawnT Ck [d] ρ with
  | nil => rw [hd] at h; exact nomatch h
  | cons dr t =>
    cases t with
    | nil => exact ⟨dr, rfl, by rw [hd] at h; exact h⟩
    | cons _ _ => rw [hd] at h; exact nomatch h

/-- **K9's fall in the cover's form, at typed challenges.** -/
theorem k9_fallDebt (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {Lk : Link S Claim} {p : Desc.K9.Where} {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere}
    (Sd : SeatedFree c Z l (if l = 24 then 9 else 7) Lk p w) (d : RDT) (he : d.entry = Desc.K9.entry p)
    (h5 : d.kind ≠ .seeds) (h6 : d.kind ≠ .sealed) (n top Pn : ℕ) (notGood : Odds) (ft : ℕ)
    (Q : List Fmt.Drawn → S → Prop)
    (hQ : ∀ fr s', Q fr s' → goodW p (claimsInBy Lk.each Lk.hear Lk.order) s' n ∧
      ∀ a0, Desc.K9.atS.get? s' = some a0 → a0.F.planClaimsF = Pn) :
    FallDebt (_root_.Run.ck .two) (quietFall p n top notGood) ft
      (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order))
      (c.blocksInOrder.drop (14 * l + (if l = 24 then 11 else 9) + 1)) [d] [] Q
      (((n * (Pn - 1) : ℕ) : ℝ≥0∞) / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞)) := by
  have hb := batching_at Sd
  refine P1K8.quiet_fallDebt_of hS hR O hl _ hb (_root_.Run.ck .two) d _ (freeSlotShare n)
    (quietPlace_is hS hR O hl Sd) (fun _ _ => rfl) ft _ Q ?_
  intro fr s' hq
  obtain ⟨hg, hP⟩ := hQ fr s' hq
  have h1 : OneElem d.entry d.kind := by
    rw [he]
    exact oneElem_bat p d.kind h5 h6
  refine le_trans (Prob.pr_mono _ fun ρ hρ => behind_sub _ d _ _ s' ρ hρ)
    (P1K8.gate_of_count d h1 _ (GateSpeaks 0 (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)) s' n none)
      (fun dr x h hx => speaks_of_behind hS hR O hl _ hb n s' dr x h hx) _
      (gate_few_weak hS hR O l hl _ Lk p w Sd s' n Pn hP hg 0))

/-- **The same at strings of hash blocks.** -/
theorem k9_fallDebt_blocks (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {Lk : Link S Claim} {p : Desc.K9.Where} {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere}
    (Sd : SeatedFree c Z l (if l = 24 then 9 else 7) Lk p w) (d : RDT) (he : d.entry = Desc.K9.entry p)
    (h5 : d.kind ≠ .seeds) (h6 : d.kind ≠ .sealed) (n top Pn : ℕ) (notGood : Odds) (ft : ℕ)
    (Q : List Fmt.Drawn → S → Prop)
    (hQ : ∀ fr s', Q fr s' → goodW p (claimsInBy Lk.each Lk.hear Lk.order) s' n ∧
      ∀ a0, Desc.K9.atS.get? s' = some a0 → a0.F.planClaimsF = Pn) :
    FallDebt (_root_.Run.ckP .two) (quietFall p n top notGood) ft
      (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order))
      (c.blocksInOrder.drop (14 * l + (if l = 24 then 11 else 9) + 1)) [d] [] Q
      (kapSl 128 ^ 3 * ((n * (Pn - 1) : ℕ) : ℝ≥0∞) / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞)) := by
  have hb := batching_at Sd
  refine P1K8.quiet_fallDebt_of hS hR O hl _ hb (_root_.Run.ckP .two) d _ (freeSlotShare n)
    (quietPlace_is hS hR O hl Sd) (fun _ _ => rfl) ft _ Q ?_
  intro fr s' hq
  obtain ⟨hg, hP⟩ := hQ fr s' hq
  have h1 : OneElem d.entry d.kind := by
    rw [he]
    exact oneElem_bat p d.kind h5 h6
  have hlog : d.entry.logN ≤ 64 := by
    rw [he]
    exact Nat.zero_le _
  refine le_trans (Prob.pr_mono _ fun ρ hρ => behind_sub _ d _ _ s' ρ hρ)
    (P1K8.gate_of_count_blocks d h1 hlog _
      (GateSpeaks 0 (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)) s' n none)
      (fun dr x h hx => speaks_of_behind hS hR O hl _ hb n s' dr x h hx) _
      (gate_few_weak hS hR O l hl _ Lk p w Sd s' n Pn hP hg 0))

end

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.quietPlace_is
#print axioms ProofFile.Honest.K9.batching_at
#print axioms ProofFile.Honest.K9.speaks_of_behind
#print axioms ProofFile.Honest.K9.behind_sub
#print axioms ProofFile.Honest.K9.k9_fallDebt
#print axioms ProofFile.Honest.K9.k9_fallDebt_blocks
