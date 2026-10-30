-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/SecondCount.lean: THE SMALLNESS TEST's SECOND FALL: ITS SENTENCE (FallDebt) WITH EVERY
TERM A WRITTEN NUMBER, UNDER `SecondOwed`, A CONDITION THAT NO LEMMA OF THIS FILE GIVES AT ANY
STATE: THE LETTER FOR THE SECOND SHARE's CHANCE GIVES WAY TO `secondN` OF THE BUILT SEGMENT OVER
p^3, AND A PREMISE ON STATES COMES IN ITS PLACE. THE OBLIGATION MOVES; IT IS NOT MET. A definition
and lemmas; NONE OF THE LIBRARY's GOALS. Nothing on completeness, soundness or hiding.

  `SecondOwed b s'`   in front of the batching: `SecondLaid` and `PieceLive`
      (Johnson/Desc/K8/Honest/SecondFew.lean, SecondNz.lean); behind the batching's decision, AT
      EVERY FIELD ELEMENT at which it says yes: `SecondEqs` (SecondParts.lean): the equalities of
      the verifier's two tests on weights by a second computation
  `second_there`, `secondNo_gives`   what a yes of `secondNo` (Johnson/P1K8R/DebtsK8.lean) gives
  `secondN_at_batch`   in front of a segment's batching the number is the built segment's
  **`second_at_step`**   the count of field elements at the step, at all 25 segments
  **`second_gate`**, **`second_gate_blocks`**   the measure over the batching's one round
  **`share_fallDebt_counted`**, **`share_fallDebt_counted_blocks`**   `share_fallDebt_live`,
      `share_fallDebt_live_blocks` (Johnson/P1K8R/ShareLiveOf.lean) without the letter
By: `second_at_link` (Johnson/Desc/K8/Honest/SecondFew.lean) · `second_iff`, `second_silent`
(Johnson/P1K8R/SecondIff.lean) · `plain_at_seat` (Johnson/P1K8R/PlainAtSeat.lean), `step_chi`
(FallAtStep.lean), `behind_iff` (CountAtStep.lean) · `gate_of_count`, `gate_of_count_blocks`
(Johnson/P1K8R/GateOfCount.lean) · LinkJoin.planned_at_batch
(Johnson/Desc/First/Link/Law/PlannedAtDraw.lean) at planned_rows (RowsNumberAtBatch.lean).
Limits. `SecondOwed`, `ShareLive` and `RowsAsked Z` are premises; none is shown of any state or plan
here. The fall's own stated share stays a letter: the sentence's number is a written sum, not that
share's value. No number is evaluated.
-/
import Johnson.P1K8R.ShareLiveOf
import Johnson.P1K8R.SecondIff
import Johnson.Desc.K8.Honest.SecondFew
import Johnson.P1K8R.NumbersAtBatch
import Johnson.P1K8R.GateOfCount
import Johnson.P1K8R.CountAtStep

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 OnBytes.Slice
open OnBytes.Model.Stages (LinkH)
open OnBytes.Maker (RDT uLT drawnT)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest
open VerifiableInference.Desc.K9Asks (RowsAsked)
open Johnson.Desc.First.Walk.Tied (Reach reach_of_fold)
open ProofFile.Honest (Odds FallDebt)
open ProofFile.Honest.K8 (k8ShareFall k8Second)
open Iop
open scoped ENNReal

/-- **What is still owed for the second share's count**: on the frame and on what the lookup has
heard, in front of the batching; and `SecondEqs` behind the batching's decision, at every field
element at which it says yes. -/
def SecondOwed (b : Block S Claim) (s' : S) : Prop :=
  (∀ tl F', s'.tl? = some tl → s'.fork? = some F' → SecondLaid tl F' ∧
    ∀ g₀ nbW W, tl.heard = some g₀ → tl.wants = some (nbW, W) → PieceLive tl g₀ W) ∧
  ∀ x t, b.decide s' [⟨[], chiAt x⟩] [] = .ok t →
    ∀ tl' G, tlForkP.get? t = some (tl', G) → SecondEqs tl' G

/-- Where the second share speaks the three values are there. -/
theorem second_there {tl : HTailF2} {F : Fork} (h : k8Second tl F ≠ none) :
    ∃ g jo nbW W, tl.heard = some g ∧ tl.joinObj9 = some jo ∧ tl.wants = some (nbW, W) := by
  cases hg : tl.heard with
  | none => exact absurd (second_silent (Or.inl hg)) h
  | some g =>
    cases hj : tl.joinObj9 with
    | none => exact absurd (second_silent (Or.inr (Or.inl hj))) h
    | some jo =>
      cases hw : tl.wants with
      | none => exact absurd (second_silent (Or.inr (Or.inr hw))) h
      | some x => exact ⟨g, jo, x.1, x.2, rfl, rfl, rfl⟩

/-- What a yes of the test with code gives. -/
theorem secondNo_gives (t' : S) (tl' : HTailF2) (G : Fork)
    (h1 : tlForkP.get? t' = some (tl', G)) (h2 : secondNo t' = true) :
    ∃ g₀ jo nbW W, tl'.heard = some g₀ ∧ tl'.joinObj9 = some jo ∧
      tl'.wants = some (nbW, W) ∧ ¬ (SecondEqs tl' G ∧ SecondRest tl' G) := by
  unfold secondNo at h2
  rw [h1] at h2
  have h3 : (k8Second tl' G).isSome = true := h2
  have hne : k8Second tl' G ≠ none := fun e => by
    rw [e] at h3
    exact nomatch h3
  obtain ⟨g, jo, nbW, W, a1, a2, a3⟩ := second_there hne
  exact ⟨g, jo, nbW, W, a1, a2, a3, fun hh => hne ((second_iff a1 a2 a3).2 hh)⟩

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A₂ : ProofFile.SharedSeat} {B₂ : ProofFile.SecondSeat}

/-- In front of a segment's batching the number is the built segment's. -/
theorem secondN_at_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) {l : ℕ} (hl : l < 25)
    {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (z, s))
    {tl : HTailF2} (ht : s.tl? = some tl) : secondN tl = secondN Xl.tl := by
  have hx : (l, (if l = 24 then 5 else 4), (if l = 24 then 3 else 2)) ∈ P1K8S.stretches :=
    List.mem_map.2 ⟨l, List.mem_range.2 hl, rfl⟩
  have e : 14 * l + (if l = 24 then 5 else 4) + 3 + (if l = 24 then 3 else 2) =
      14 * l + (if l = 24 then 11 else 9) := by
    split_ifs <;> omega
  have h' : Reach 0 c.blocksInOrder (ProofFile.startS Z)
      (14 * l + (if l = 24 then 5 else 4) + 3 + (if l = 24 then 3 else 2)) (z, s) := by
    rw [e]
    exact h
  have g := LinkJoin.of_readTl
    (LinkJoin.planned_at_batch LinkJoin.planned_rows hS hR O hx e3 (z, s) h') tl ht
  have g1 : tl.NM = Xl.tl.NM := congrArg (·.1) g
  have g3 : tl.tau = Xl.tl.tau := congrArg (·.2.2.1) g
  have g4 : tl.shp = Xl.tl.shp := congrArg (·.2.2.2) g
  unfold secondN HTailF2.stepF
  rw [g1, g3, g4]

/-- **The count at the step, at all 25 segments.** -/
theorem second_at_step (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) {l : ℕ} (hl : l < 25) :
    ∃ (b : Block S Claim) (p : K9.Where),
      c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b ∧ IM.k9At Z l = some p ∧
      ∀ (s : S) (n : Nat), SecondOwed b s → (∀ tl, s.tl? = some tl → secondN tl ≤ n) →
        Prob.cnt (fun x : Cb.Gl.E => ∃ (r : Fmt.RoundView) (cols : List Desc.OpenedColumn) (t : S) (k : Nat),
          r.drawn.elems = [Slice.ofE x] ∧ b.step 0 s [r] cols = .ok (t, k) ∧
            secondNo t = true) ≤ n := by
  obtain ⟨Lk, p, -, e2, hflat, hplain, same, name, a, hk, hb⟩ := plain_at_seat hS hR O hl
  refine ⟨_, p, hflat, e2, fun s n hO hn => ?_⟩
  have hcount := second_at_link Lk hplain p
    (fun t rs => (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)).decide t rs []) s n secondNo
    (fun rs t ht => ((IM.yes_alone hb hk s t rs []).1 ht).1) secondNo_gives
    (fun tl F' ht hF => ⟨(hO.1 tl F' ht hF).1, (hO.1 tl F' ht hF).2, hn tl ht⟩)
    (fun x t' tl' G hbt hq => hO.2 x t' hbt tl' G hq)
  refine (Prob.cnt_mono fun x hx => ?_).trans hcount
  obtain ⟨r, cols, t, k, hel, hst, hz⟩ := hx
  have hdec := step_chi hb hk 0 s t r cols k x hel hst
  unfold K8.Honest.askBehind
  simp only [List.map_cons, List.map_nil]
  rw [hdec]
  exact hz

/-- **The measure: at typed challenges.** p is tied to the round's data d alone, not to b or l: at
a d that is not the block's own the sentence is true and idle. -/
theorem second_gate (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) {l : ℕ} (hl : l < 25)
    (b : Block S Claim) (hb : c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b) (p : K9.Where)
    (d : RDT) (he : d.entry = K9.entry p) (h5 : d.kind ≠ .seeds) (h6 : d.kind ≠ .sealed) (s : S)
    (n : Nat) (hO : SecondOwed b s) (hn : ∀ tl, s.tl? = some tl → secondN tl ≤ n) :
    Iop.prRho {ρ : Iop.Rho (uLT (_root_.Run.ck .two) [d]) |
      behindT b secondNo s (drawnT (_root_.Run.ck .two) [d] ρ) = true} ≤
      (n : ℝ≥0∞) / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) := by
  obtain ⟨b', p', hb', -, hc⟩ := second_at_step hS hR O hl
  obtain rfl : b' = b := Option.some.inj (hb'.symm.trans hb)
  have h1 : OneElem d.entry d.kind := by
    rw [he]
    exact oneElem_bat p d.kind h5 h6
  have k := gate_of_count d h1
    (fun dr => ∃ (r : Fmt.RoundView) (cols : List Desc.OpenedColumn) (t : S) (m : Nat), r.drawn = dr ∧
      b'.step 0 s [r] cols = .ok (t, m) ∧ secondNo t = true)
    (fun x => ∃ (r : Fmt.RoundView) (cols : List Desc.OpenedColumn) (t : S) (k : Nat),
      r.drawn.elems = [Slice.ofE x] ∧ b'.step 0 s [r] cols = .ok (t, k) ∧ secondNo t = true)
    (by
      rintro dr x ⟨r, cols, t, m, rfl, k1, k2⟩ hx
      exact ⟨r, cols, t, m, hx, k1, k2⟩) n (hc s n hO hn)
  refine (Prob.pr_mono _ fun ρ hρ => ?_).trans k
  obtain ⟨a, u⟩ := ρ
  refine ⟨(_root_.Run.ck .two).dr d.entry d.kind (Iop.GChal.old (b := d.entry.work) a), rfl, ?_⟩
  exact (behind_iff hS hR O hl b' hb secondNo s _).1 hρ

/-- **The measure: at strings of hash blocks.** -/
theorem second_gate_blocks (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) {l : ℕ} (hl : l < 25)
    (b : Block S Claim) (hb : c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b) (p : K9.Where)
    (d : RDT) (he : d.entry = K9.entry p) (h5 : d.kind ≠ .seeds) (h6 : d.kind ≠ .sealed) (s : S)
    (n : Nat) (hO : SecondOwed b s) (hn : ∀ tl, s.tl? = some tl → secondN tl ≤ n) :
    Iop.prRho {ρ : Iop.Rho (uLT (_root_.Run.ckP .two) [d]) |
      behindT b secondNo s (drawnT (_root_.Run.ckP .two) [d] ρ) = true} ≤
      kapSl 128 ^ 3 * (n : ℝ≥0∞) / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) := by
  obtain ⟨b', p', hb', -, hc⟩ := second_at_step hS hR O hl
  obtain rfl : b' = b := Option.some.inj (hb'.symm.trans hb)
  have h1 : OneElem d.entry d.kind := by
    rw [he]
    exact oneElem_bat p d.kind h5 h6
  have hlog : d.entry.logN ≤ 64 := by
    rw [he]
    exact Nat.zero_le _
  have k := gate_of_count_blocks d h1 hlog
    (fun dr => ∃ (r : Fmt.RoundView) (cols : List Desc.OpenedColumn) (t : S) (m : Nat), r.drawn = dr ∧
      b'.step 0 s [r] cols = .ok (t, m) ∧ secondNo t = true)
    (fun x => ∃ (r : Fmt.RoundView) (cols : List Desc.OpenedColumn) (t : S) (k : Nat),
      r.drawn.elems = [Slice.ofE x] ∧ b'.step 0 s [r] cols = .ok (t, k) ∧ secondNo t = true)
    (by
      rintro dr x ⟨r, cols, t, m, rfl, k1, k2⟩ hx
      exact ⟨r, cols, t, m, hx, k1, k2⟩) n (hc s n hO hn)
  refine (Prob.pr_mono _ fun ρ hρ => ?_).trans k
  obtain ⟨a, u⟩ := ρ
  refine ⟨(_root_.Run.ckP .two).dr d.entry d.kind (Iop.GChal.old (b := d.entry.work) a), rfl, ?_⟩
  exact (behind_iff hS hR O hl b' hb secondNo s _).1 hρ

/-- **THE SECOND FALL's SENTENCE WITH EVERY TERM A WRITTEN NUMBER: at typed challenges.** -/
theorem share_fallDebt_counted (hE : RowsAsked Z) (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) {l : ℕ} (hl : l < 25) :
    ∃ (b : Block S Claim) (p : K9.Where) (X : LinkH),
      c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b ∧ IM.k9At Z l = some p ∧
      Bs.G₀.built.toList[l]? = some X ∧
      ∀ (d : RDT), d.entry = K9.entry p → d.kind ≠ .seeds → d.kind ≠ .sealed →
        ∀ (ft : ℕ) (share : Odds) (Q : List Fmt.Drawn → S → Prop),
        (∀ fr s', Q fr s' → FoldEnd Z c l s' ∧ ShareLive s' ∧ SecondOwed b s') →
        FallDebt (_root_.Run.ck .two)
          (k8ShareFall l (if l = 24 then 1 else 0) (ProofFile.k8NU Bs.G₀ X) share) ft b
          (c.blocksInOrder.drop (14 * l + (if l = 24 then 11 else 9) + 1)) [d] [] Q
          ((((ProofFile.k8NU Bs.G₀ X).getD 2 0 * (p.rows - 1) : ℕ) : ℝ≥0∞) /
              ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) +
            (((2 * (X.tl.zzBlocks * X.tl.mz) * (p.rows - 1) : ℕ) : ℝ≥0∞) /
              ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) +
            (((linkedCount X.tl * (p.rows - 1) : ℕ) : ℝ≥0∞) / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) +
            (((3 * X.tl.bzColumns * (p.rows - 1) : ℕ) : ℝ≥0∞) / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) +
            (((symCount X.tl * (p.rows - 1) : ℕ) : ℝ≥0∞) / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) +
              (((secondN X.tl : ℕ) : ℝ≥0∞) / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) + 0)))))) := by
  obtain ⟨b, p, X, hb, hp, hX, H⟩ := share_fallDebt_live hE hS hR O hl
  refine ⟨b, p, X, hb, hp, hX, fun d he h5 h6 ft share Q hQ => ?_⟩
  refine H d he h5 h6 ft share _ Q (fun fr s' hq => ?_)
    fun fr s' hq => ⟨(hQ fr s' hq).1, (hQ fr s' hq).2.1⟩
  obtain ⟨⟨zp, rs, r, cs, c', hfold⟩, -, hO⟩ := hQ fr s' hq
  have hr : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (zp, s') :=
    reach_of_fold _ (List.getElem?_eq_some_iff.1 hb).1.le s' rs r cs c' hfold
  exact second_gate hS hR O hl b hb p d he h5 h6 s' (secondN X.tl) hO fun tl ht =>
    le_of_eq (secondN_at_batch hS hR O hl (by rw [← Array.getElem?_toList]; exact hX) hr ht)

/-- **The same at strings of hash blocks.** -/
theorem share_fallDebt_counted_blocks (hE : RowsAsked Z) (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) {l : ℕ} (hl : l < 25) :
    ∃ (b : Block S Claim) (p : K9.Where) (X : LinkH),
      c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b ∧ IM.k9At Z l = some p ∧
      Bs.G₀.built.toList[l]? = some X ∧
      ∀ (d : RDT), d.entry = K9.entry p → d.kind ≠ .seeds → d.kind ≠ .sealed →
        ∀ (ft : ℕ) (share : Odds) (Q : List Fmt.Drawn → S → Prop),
        (∀ fr s', Q fr s' → FoldEnd Z c l s' ∧ ShareLive s' ∧ SecondOwed b s') →
        FallDebt (_root_.Run.ckP .two)
          (k8ShareFall l (if l = 24 then 1 else 0) (ProofFile.k8NU Bs.G₀ X) share) ft b
          (c.blocksInOrder.drop (14 * l + (if l = 24 then 11 else 9) + 1)) [d] [] Q
          (kapSl 128 ^ 3 * (((ProofFile.k8NU Bs.G₀ X).getD 2 0 * (p.rows - 1) : ℕ) : ℝ≥0∞) /
              ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) +
            (kapSl 128 ^ 3 * ((2 * (X.tl.zzBlocks * X.tl.mz) * (p.rows - 1) : ℕ) : ℝ≥0∞) /
              ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) +
            (kapSl 128 ^ 3 * ((linkedCount X.tl * (p.rows - 1) : ℕ) : ℝ≥0∞) /
              ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) +
            (kapSl 128 ^ 3 * ((3 * X.tl.bzColumns * (p.rows - 1) : ℕ) : ℝ≥0∞) /
              ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) +
            (kapSl 128 ^ 3 * ((symCount X.tl * (p.rows - 1) : ℕ) : ℝ≥0∞) /
              ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) +
              (kapSl 128 ^ 3 * ((secondN X.tl : ℕ) : ℝ≥0∞) / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) +
                0)))))) := by
  obtain ⟨b, p, X, hb, hp, hX, H⟩ := share_fallDebt_live_blocks hE hS hR O hl
  refine ⟨b, p, X, hb, hp, hX, fun d he h5 h6 ft share Q hQ => ?_⟩
  refine H d he h5 h6 ft share _ Q (fun fr s' hq => ?_)
    fun fr s' hq => ⟨(hQ fr s' hq).1, (hQ fr s' hq).2.1⟩
  obtain ⟨⟨zp, rs, r, cs, c', hfold⟩, -, hO⟩ := hQ fr s' hq
  have hr : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (zp, s') :=
    reach_of_fold _ (List.getElem?_eq_some_iff.1 hb).1.le s' rs r cs c' hfold
  exact second_gate_blocks hS hR O hl b hb p d he h5 h6 s' (secondN X.tl) hO fun tl ht =>
    le_of_eq (secondN_at_batch hS hR O hl (by rw [← Array.getElem?_toList]; exact hX) hr ht)

end P1K8

#print axioms P1K8.SecondOwed
#print axioms P1K8.second_there
#print axioms P1K8.secondNo_gives
#print axioms P1K8.secondN_at_batch
#print axioms P1K8.second_at_step
#print axioms P1K8.second_gate
#print axioms P1K8.second_gate_blocks
#print axioms P1K8.share_fallDebt_counted
#print axioms P1K8.share_fallDebt_counted_blocks
