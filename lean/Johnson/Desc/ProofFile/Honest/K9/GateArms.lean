-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/GateArms.lean: K9's COUNT UNDER A "GOOD" THAT HOLDS NO YES AND NO LENGTH. Statements
and proofs ON THE VERIFIER's TEXT; no prover is in this file, and no goal is stated. No probability is in this file.

`goodS` (Honest/K9/QuietMore.lean), the premise of the count at a segment of which `SeatedFree` holds, says: draw and
gatherer return at SOME challenge, and there the Bool `goodAt` is true: every slot is live, AND the claims counted so
far with the list's length are within the plan's number. That they return is a YES: another share's. And the second
half of `goodAt` need not be asked: where the list is too long the batching's own adding refuses, so nothing falls
there.
  `goodW p g s n`   **"GOOD", WITHOUT A YES AND WITHOUT A LENGTH**: WHEREVER draw and gatherer return, every slot
      below n is live in what they yield (`K9H.slotsLive`, at the merge's slot of the state behind)
  `goodW_of_goodS`  under the laws `goodS` gives it
  `set_merge`, `draw_merge`   K9's OWN SHARE OF "the merge's slot is m": the draw does not turn it, in whichever sort
      of segment
  **`goodW_of_inv`**   THE KINDS' CLAUSES, JOINED: `slotsLive_of_inv` (Honest/K9/GatherFold.lean) at every challenge:
      one predicate I on states that holds behind the draw wherever the draw says yes, that every run of the order
      hands on, AND THAT FIXES THE MERGE's SLOT (I e → the merge's slot at e is m) · live · plain · unnamed as there:
      then `goodW`. No clause speaks of a length, and none of what draw and gatherer yield
  `good_of_yes`    of a segment of which `SeatedFree` holds: where `goodW` holds and the seated block's decision says
      yes at some x, `goodS` holds: the length is within the plan's number because the adding returned
      (`addList_only`, Johnson/Desc/K9/Honest/AddYes.lean), or, at an empty list, because no claim is counted behind
      the draw
  **`gate_few_weak`**   of such a segment, AT EVERY STATE at which `goodW` holds, P the plan's number of claims of the
      state's ledger if K9's lens answers there: at most n * (P - 1) field elements x at which `GateSpeaks`
      (Honest/K9/GateCount.lean) speaks. Two arms: it speaks somewhere, then `good_of_yes` and `gate_few_seated`; or
      nowhere (so where the lens is silent, or draw and gatherer return nowhere: by the first arm's steps read
      backwards; not stated on its own)
`goodW_of_inv` and `draw_merge` are called at a member: Honest/K9/GateToy.lean (`goodWG`, `startG`); `goodW_of_inv`
also by Honest/K9/GoodAtt.lean and GoodHead.lean, at no member. `good_of_yes` is called by `gate_few_weak` alone; that
by Honest/K9/FallDebtK9.lean; `goodW_of_goodS` by no line.
WHAT IS NOT CLAIMED. `goodW` at any state of a run; any clause of `goodW_of_inv` of any kind's run: I IS ONE PREDICATE
FOR THE WHOLE ORDER: every run that writes owes that it hands on the JOINT I: who carries whose clause is not settled.
That n and P are the public parameters'. What Honest/K9/GateCount.lean does not claim. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K9.GateCount
import Johnson.Desc.ProofFile.Honest.K9.GatherFold

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First

/-- **"Good", without a yes and without a length.** -/
def goodW (p : Desc.K9.Where) (g : S → Except String (List Claim × S)) (s : S) (n : ℕ) : Prop :=
  ∀ x y, gathered p g s x = some y → Desc.K9H.slotsLive n (Desc.K9.mergeOf y.1) y.2.2 = true

theorem goodW_of_goodS (p : Desc.K9.Where) (g : S → Except String (List Claim × S)) (s : S)
    (laws : RunsLaw p g s) (n : ℕ) (h : goodS p g s n) : goodW p g s n := by
  intro x y hy
  have h1 := (goodS_iff p g s laws n x y hy).1 h
  unfold goodAt at h1
  rw [Bool.and_eq_true] at h1
  exact h1.1

/-- Laying K9's part into a state does not turn the merge's slot. -/
theorem set_merge (u : S) (q : Desc.K9.Part) : Desc.K9.mergeOf (Desc.K9.atS.set u q) = Desc.K9.mergeOf u := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := u
  cases here with
  | head h0 =>
    obtain ⟨o1, o2⟩ : ∃ b, h0.opened = b := ⟨_, rfl⟩
    cases o1 with
    | true =>
      show Desc.K9.mergeOf { ((S.mk st book roots rowsOwed failed check out (.head h0) req).putLink q.L).putFork q.F
        with st := q.d.st, rowsOwed := q.owed } = _
      simp only [S.putLink, S.putFork, o2, if_true, Desc.K9.mergeOf]
    | false =>
      show Desc.K9.mergeOf { ((S.mk st book roots rowsOwed failed check out (.head h0) req).putLink q.L).putFork q.F
        with st := q.d.st, rowsOwed := q.owed } = _
      simp only [S.putLink, S.putFork, o2, Bool.false_eq_true, if_false, Desc.K9.mergeOf]
  | _ => rfl

/-- **K9's own share of "the merge's slot is m"**: the draw does not turn it, in whichever sort of segment. -/
theorem draw_merge (p : Desc.K9.Where) (s t₁ : S) (x : E)
    (h : (Desc.K9.drawAlone (Cl := Claim) Desc.K9.atS p).decide s [⟨[], drawnOne x⟩] [] = .ok t₁) :
    Desc.K9.mergeOf t₁ = Desc.K9.mergeOf s := by
  obtain ⟨a, ha⟩ := draw_open p s t₁ x h
  rw [draw_is p s t₁ x a ha h, set_merge]

/-- **THE KINDS' CLAUSES, JOINED**: `slotsLive_of_inv` (Honest/K9/GatherFold.lean) at every challenge. I: one predicate
on states that holds BEHIND THE DRAW at every challenge at which the draw says yes, that every run of the order hands
on, and that fixes the merge's slot; the clauses live, plain and unnamed as there. -/
theorem goodW_of_inv (p : Desc.K9.Where) (each : ℕ × String → List Claim → S → Except String Unit)
    (bs : List (Block S Claim)) (order : List (ℕ × String)) (s : S) (n : ℕ) (m : Option ℕ) (I : S → Prop)
    (start : ∀ x t₁, (Desc.K9.drawAlone (Cl := Claim) Desc.K9.atS p).decide s [⟨[], drawnOne x⟩] [] = .ok t₁ →
      I t₁)
    (hand : ∀ o ∈ order, ∀ run, claimsRunOf bs o = some run → ∀ k t z, I t → run k t = .ok z → I z.2)
    (merge : ∀ e, I e → Desc.K9.mergeOf e = m)
    (live : ∀ j < n, m ≠ some j → ∃ o ∈ order, ∀ run, claimsRunOf bs o = some run →
      ∀ k u z, I u → run k u = .ok z → Desc.K9H.liveAt z.1 j = true)
    (plain : ∀ j < n, m ≠ some j → ∀ o ∈ order, ∀ run, claimsRunOf bs o = some run →
      ∀ k u z, I u → run k u = .ok z → Desc.K9H.plainAt z.1 j = true)
    (unnamed : ∀ j < n, m = some j → ∀ o ∈ order, ∀ run, claimsRunOf bs o = some run →
      ∀ k u z, I u → run k u = .ok z → Desc.K9H.unnamedAt z.1 j = true) :
    goodW p (claimsInBy each bs order) s n := by
  intro x y hy
  obtain ⟨t₁, ht, hz, _⟩ := gathered_split p _ s x y hy
  have hI := start x t₁ ht
  obtain ⟨ls, _, hR⟩ := gather_ran each bs order t₁ (y.2.2, y.1) hz
  rw [merge y.1 (ran_inv bs I order 0 t₁ ls y.1 hand hI hR).2]
  exact slotsLive_of_inv each bs order t₁ (y.2.2, y.1) hz n m I hI hand live plain unnamed

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- Where the seated block's decision says yes somewhere, "good" without a yes is "good". -/
theorem good_of_yes {l k : ℕ} {Lk : Link S Claim} {p : Desc.K9.Where}
    {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (Sd : SeatedFree c Z l k Lk p w) (s s₁ : S) (n : ℕ)
    (hg : goodW p (claimsInBy Lk.each Lk.hear Lk.order) s n) (x : E)
    (hd : (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)).decide s [⟨[], drawnOne x⟩] [] = .ok s₁) :
    goodS p (claimsInBy Lk.each Lk.hear Lk.order) s n := by
  obtain ⟨pl, hk, hb⟩ := Sd.alone
  obtain ⟨e, a, cls, G, hy, hadd, _⟩ := batch_split p _ s s₁ x ((IM.yes_alone hb hk s s₁ _ []).1 hd).1
  refine ⟨x, (e, a, cls), hy, ?_⟩
  unfold goodAt
  rw [Bool.and_eq_true]
  refine ⟨hg x _ hy, decide_eq_true ?_⟩
  show a.F.nClaim + cls.length ≤ a.F.planClaimsF
  cases hc : cls with
  | nil =>
    obtain ⟨t₁, ht, hz, he⟩ := gathered_split p _ s x _ hy
    obtain ⟨a0, ha0⟩ := draw_open p s t₁ x ht
    obtain ⟨a₁, h1, hl⟩ := draw_facts p s t₁ x a0 ha0 ht
    obtain ⟨a', ha', hcore⟩ := Sd.keeps t₁ e cls a₁ hz h1
    obtain rfl : a' = a := Option.some.inj (ha'.symm.trans he)
    rw [hcore.count, hl.count]
    exact Nat.zero_le _
  | cons c0 l0 =>
    have h2 := (Desc.K9H.addList_only cls a.F G hadd).2 (by rw [hc]; exact List.cons_ne_nil _ _)
    unfold Desc.K9H.addReady at h2
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
    rw [← hc]
    exact h2.1.1.2

/-- **The count under "good" without a yes and without a length, at every state.** -/
theorem gate_few_weak (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (l : ℕ) (hl : l < 25) (k : ℕ)
    (Lk : Link S Claim) (p : Desc.K9.Where) (w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere)
    (Sd : SeatedFree c Z l k Lk p w) (s : S) (n Pn : ℕ)
    (hP : ∀ a0, Desc.K9.atS.get? s = some a0 → a0.F.planClaimsF = Pn)
    (hg : goodW p (claimsInBy Lk.each Lk.hear Lk.order) s n) (ft : ℕ) :
    Prob.cnt (GateSpeaks ft (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)) s n none) ≤ n * (Pn - 1) := by
  by_cases h : ∃ x, GateSpeaks ft (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)) s n none x
  · obtain ⟨x, r, cols, t, k', hx, hy, hq⟩ := h
    obtain ⟨pl, hk, hb⟩ := Sd.alone
    obtain ⟨s₁, hd, _⟩ := falls_of_seated_step hb hk ft s t r cols k' (Slice.ofE x) hx hy n none hq
    have hgood := good_of_yes Sd s s₁ n hg _ hd
    obtain ⟨e, a, cls, G, hy', _, _⟩ := batch_split p _ s s₁ _ ((IM.yes_alone hb hk s s₁ _ []).1 hd).1
    obtain ⟨t₁, ht, _, _⟩ := gathered_split p _ s _ _ hy'
    obtain ⟨a0, ha0⟩ := draw_open p s t₁ _ ht
    rw [← hP a0 ha0]
    exact gate_few_seated hS hR O l hl k Lk p w Sd s a0 n ha0 hgood ft
  · rw [Prob.cnt_false fun x hx => h ⟨x, hx⟩]
    exact Nat.zero_le _

end

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.goodW_of_goodS
#print axioms ProofFile.Honest.K9.set_merge
#print axioms ProofFile.Honest.K9.draw_merge
#print axioms ProofFile.Honest.K9.goodW_of_inv
#print axioms ProofFile.Honest.K9.good_of_yes
#print axioms ProofFile.Honest.K9.gate_few_weak
#print axioms ProofFile.Honest.K9.goodW
