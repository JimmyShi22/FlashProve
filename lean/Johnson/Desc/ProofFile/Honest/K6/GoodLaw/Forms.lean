-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/GoodLaw/Forms.lean: every slot that the output head's own rounds
fill, but the last, is live in the head's own claims, where no challenge that its four masked
sumchecks keep reads as 0, nor the element sampled at the beginning of the third and of the fourth.
Statements and proofs ON THE VERIFIER's TEXT; no prover is in this file.

  `SumGood S`       no challenge that the sumcheck S keeps, the further variable's among them, reads
                    as 0
  `SumGoodEps S`    the element drawn at its beginning does not read as 0
  `live_W`          the slot of a sum of limb products is live by its carry's line
  `live_P`          the slot of a product is live by a line of the root or of the reciprocal
`forms_live_heard` **where the head's hearing returns from a well laid ledger F to G: every slot
from F.next on, 35 + 6 lt + 2 lPd of them, is live in the 29 forms of the run "norm"; every slot
from there on but the last is live in the two forms of the run "logits"**

Which claim keeps which slot alive. The nine sums of limb products: each its carry's line. The two
end values of the first sumcheck: the line that says that they are equal. The seven products: the
six lines of the root and of the reciprocal that name them (one with the coefficient -2). The second
sumcheck's claimed sum: the line that says that it is the batched sum of the seven products. Every
further end value but the last: the line that ties it to a read. The third and the fourth sumcheck's
claimed sums: the sumcheck's own form, under minus the element drawn at its beginning. Every
sumcheck's own scalars: its own form.

Limits. THE LAST SLOT, the fourth sumcheck's second end value, is not covered: by a reading of the
text no claim of this sub-protocol names it; that is shown by no theorem here. The premises: the
ledger in front is well laid; the hearing returns and uses the rounds up; the reads' entries name no
slot; the lookup's point on the positions has lt coordinates. Nothing on the batching element.
Nothing on the run "policy" (by a reading of the text it names no slot; no theorem here says so) or
on the run "join". The ground of GoodLaw/Coef.lean is this file's ground too.
Nothing on any property.

-/
import Johnson.Desc.Kinds.Law.NormHear
import Johnson.Desc.Kinds.Law.Cut
import Johnson.Desc.Kinds.Law.Takes
import Johnson.Desc.ProofFile.Honest.K6.GoodLaw.Coef

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace ProofFile.Honest.K6.GoodLaw

section
open OnBytes (E oneE)
open OnBytes.Model (Aff)
open VerifiableInference.Desc.Kinds
open VerifiableInference.Desc.Kinds.Head (asClaim)
open VerifiableInference.Desc.Kinds.Head.Law (K rd rowHas)
open VerifiableInference.Desc.K9H (liveAt)
open OnBytes.Desc.First.P6 (sm)
open OnBytes.Desc.First (P6.Row P6.Row.ofDigits)

/-- No challenge that the sumcheck keeps, the further variable's among them, reads as 0. -/
def SumGood (S : Sum) : Prop := ∀ hd, S.psc = some hd → ∀ x ∈ hd.r, rd x ≠ 0

/-- The element drawn at the sumcheck's beginning does not read as 0. -/
def SumGoodEps (S : Sum) : Prop := ∀ hd, S.psc = some hd → rd hd.eps ≠ 0

theorem slot_named (c : Nat) : ∀ x, x ∈ (Aff.slot c).slots.toList → x.1 = c := by
  intro x hx
  have : x = (c, oneE) := by simpa [Aff.slot] using hx
  rw [this]

section Slots
variable [Head.Sizes] [Head.Policy] [Head.Request] [Head.Token] [FinalNorm.In] [Head.In]
  [Norm.Heard] [FinalNorm.Heard] [Head.Heard] [FinalNorm.Reads] [Head.Reads]

theorem mem_square {f : Form} (h : f ∈ Norm.squareForms) : f ∈ FinalNorm.forms :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h))

theorem mem_product {f : Form} (h : f ∈ Norm.productForms) : f ∈ FinalNorm.forms :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))

theorem mem_row {f : Form} (h : f ∈ Norm.rowForms) : f ∈ FinalNorm.forms :=
  List.mem_append_left _ (List.mem_append_right _ h)

theorem mem_normed {f : Form} (h : f ∈ FinalNorm.normedForms) : f ∈ FinalNorm.forms :=
  List.mem_append_right _ h

variable (hN : ∀ r i, (FinalNorm.entry r i).slots = #[])
include hN

theorem digitPV_zero (j i : Nat) : delta j (Norm.digit .rowsAtPV 0 i) = 0 :=
  (kept_delta j).addN (delta_bare j _ (hN .rowAtPV i)) _

theorem digitPr_zero (j i : Nat) : delta j (Norm.digit .rowsAtProducts 0 i) = 0 :=
  (kept_delta j).addN (delta_bare j _ (hN .rowAtProducts i)) _

/-- The slot of sum number s of limb products is live: by its carry's line. -/
theorem live_W {a s : Nat} (hs : s < 9) (hv : (Norm.W.getD s {}).var = Aff.slot a) :
    liveAt (FinalNorm.forms.map asClaim) a = true := by
  have RH := rowHas (kept_delta a) (Norm.digit .rowsAtPV 0) (digitPV_zero hN a)
  have hv' : (Norm.W.getD (9 * 0 + s) {}).var = Aff.slot a := by
    rw [show 9 * 0 + s = s by omega]
    exact hv
  have hmem : (Norm.W.getD (9 * 0 + s) {}).var + (P6.Row.ofDigits (Norm.digit .rowsAtPV 0)).c s -
      Norm.digit .rowsAtPV 0 s - sm 256 ((P6.Row.ofDigits (Norm.digit .rowsAtPV 0)).c (s + 1)) ∈
      Norm.rowForms := by
    rw [Head.Law.rowForms_eq]
    refine List.mem_append_left _ ?_
    rw [OnBytes.Desc.First.P6.carries_eq]
    exact List.mem_map.2 ⟨s, List.mem_range.2 hs, rfl⟩
  refine live_of_delta (mem_row hmem) ?_
  have z1 : delta a ((P6.Row.ofDigits (Norm.digit .rowsAtPV 0)).c s) = 0 := RH.c s
  have z2 : delta a ((P6.Row.ofDigits (Norm.digit .rowsAtPV 0)).c (s + 1)) = 0 := RH.c (s + 1)
  rw [delta_sub, delta_sub, delta_add, hv', delta_slot, if_pos rfl, z1, digitPV_zero hN a s,
    delta_sm, z2]
  simp

/-- The slot of product number n is live: by a line of the root or of the reciprocal. -/
theorem live_P {c n : Nat} (hn : n < 7)
    (hv : ∀ m, m < 7 → (Norm.P.getD m {}).var = Aff.slot (c + m)) :
    liveAt (FinalNorm.forms.map asClaim) (c + n) = true := by
  have RH := rowHas (kept_delta (c + n)) (Norm.digit .rowsAtPV 0) (digitPV_zero hN (c + n))
  have hv' : ∀ m, m < 7 →
      delta (c + n) (Norm.P.getD (7 * 0 + m) {}).var = if m = n then 1 else 0 := by
    intro m hm
    rw [show 7 * 0 + m = m by omega, hv m hm, delta_slot]
    by_cases e : m = n
    · rw [if_pos e, if_pos (by omega)]
    · rw [if_neg e, if_neg (by omega)]
  have two : (2 : K) ≠ 0 := by
    have := Head.Law.two_pow_ne_zero 1
    simpa using this
  have hl : ∀ f, f ∈ OnBytes.Desc.First.P6.lines (P6.Row.ofDigits (Norm.digit .rowsAtPV 0))
      (fun n => (Norm.P.getD (7 * 0 + n) {}).var) ((FinalNorm.epsF : Nat) : E)
      ((2 ^ (FinalNorm.MF + 1) : Nat) : Form) → f ∈ FinalNorm.forms := fun f hf =>
    mem_row (by rw [Head.Law.rowForms_eq]; exact List.mem_append_right _ hf)
  have zBlo : delta (c + n) (P6.Row.ofDigits (Norm.digit .rowsAtPV 0)).Blo = 0 := RH.Blo
  have zBhi : delta (c + n) (P6.Row.ofDigits (Norm.digit .rowsAtPV 0)).Bhi = 0 := RH.Bhi
  have zVlo : delta (c + n) (P6.Row.ofDigits (Norm.digit .rowsAtPV 0)).Vlo = 0 := RH.Vlo
  have zVhi : delta (c + n) (P6.Row.ofDigits (Norm.digit .rowsAtPV 0)).Vhi = 0 := RH.Vhi
  have zl1 : delta (c + n) (P6.Row.ofDigits (Norm.digit .rowsAtPV 0)).l1 = 0 := RH.l1
  have zkap : delta (c + n) (P6.Row.ofDigits (Norm.digit .rowsAtPV 0)).kap = 0 := RH.kap
  have zq1 : delta (c + n) (P6.Row.ofDigits (Norm.digit .rowsAtPV 0)).q1 = 0 := RH.q1
  have zsig : delta (c + n) (P6.Row.ofDigits (Norm.digit .rowsAtPV 0)).sig = 0 := RH.sig
  have zs0 : delta (c + n) (P6.Row.ofDigits (Norm.digit .rowsAtPV 0)).s0 = 0 := RH.s0
  have zrr : delta (c + n) (P6.Row.ofDigits (Norm.digit .rowsAtPV 0)).rr = 0 := RH.rr
  have zeps : delta (c + n) (Aff.ofConst ((FinalNorm.epsF : Nat) : E)) = 0 := (kept_delta _).const _
  have ztwo : delta (c + n) ((2 ^ (FinalNorm.MF + 1) : Nat) : Form) = 0 := (kept_delta _).natCast _
  have hcases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine live_of_delta (hl _ (by
      rw [OnBytes.Desc.First.P6.lines, OnBytes.Desc.First.P6.root_eq]
      exact List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self))) ?_
    rw [delta_add, delta_sub, delta_sub, delta_sub, delta_add, delta_sm, delta_sm, hv' 0 hn, zVlo,
      zeps, zBlo, zl1, zkap]
    simp
  · refine live_of_delta (hl _ (by
      rw [OnBytes.Desc.First.P6.lines, OnBytes.Desc.First.P6.root_eq]
      exact List.mem_append_left _ List.mem_cons_self)) ?_
    rw [delta_sub, delta_sub, delta_sm, hv' 1 hn, zBlo, zBhi]
    simp
  · refine live_of_delta (hl _ (by
      rw [OnBytes.Desc.First.P6.lines, OnBytes.Desc.First.P6.root_eq]
      exact List.mem_append_left _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))) ?_
    rw [delta_sub, delta_sub, delta_sub, hv' 2 hn, zVhi, zBhi, zkap]
    simp
  · refine live_of_delta (hl _ (by
      rw [OnBytes.Desc.First.P6.lines, OnBytes.Desc.First.P6.reciprocal_eq]
      exact List.mem_append_right _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))) ?_
    rw [delta_sub, delta_sub, delta_sub, delta_sub, delta_add, delta_sm, delta_sm, delta_sm,
      hv' 3 hn, ztwo, zsig, zs0, zq1, zrr]
    simpa using two
  · refine live_of_delta (hl _ (by
      rw [OnBytes.Desc.First.P6.lines, OnBytes.Desc.First.P6.reciprocal_eq]
      exact List.mem_append_right _ List.mem_cons_self)) ?_
    rw [delta_sub, delta_add, hv' 4 hn, hv' 5 (by omega), zq1]
    simp
  · refine live_of_delta (hl _ (by
      rw [OnBytes.Desc.First.P6.lines, OnBytes.Desc.First.P6.reciprocal_eq]
      exact List.mem_append_right _ List.mem_cons_self)) ?_
    rw [delta_sub, delta_add, hv' 4 (by omega), hv' 5 hn, zq1]
    simp
  · refine live_of_delta (hl _ (by
      rw [OnBytes.Desc.First.P6.lines, OnBytes.Desc.First.P6.reciprocal_eq]
      exact List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self))) ?_
    rw [hv' 6 hn]
    simp

end Slots

end

section
open OnBytes (zeroE)
open OnBytes.Model (Aff Fork)
open VerifiableInference.Desc.Kinds
open VerifiableInference.Desc.Kinds.Head (asClaim HeardAll)
open VerifiableInference.Desc.Kinds.Head.Law (rd SlotsIn WellLaid rowHas)
open VerifiableInference.Desc.K9H (liveAt)

/-- A form "a form that does not name slot a, less the variable under it" makes slot a live. -/
theorem live_var' {fs : List Form} {v g : Form} (hmem : v - g ∈ fs) {a : Nat} (hg : g = Aff.slot a)
    (hv : delta a v = 0) : liveAt (fs.map asClaim) a = true := by
  refine live_of_delta hmem ?_
  rw [delta_sub, hg, delta_slot, if_pos rfl, hv]
  simp

theorem delta_slot_ne {a i : Nat} (h : i ≠ a) : delta a (Aff.slot i) = 0 := by
  rw [delta_slot, if_neg h]

section Whole
variable [Head.Sizes] [Head.Policy] [Head.Request] [Head.Token] [FinalNorm.In] [Head.In]

/-- **EVERY SLOT OF THE SUB-PROTOCOL's WINDOW BUT THE LAST IS LIVE**, where no challenge that the
four sumchecks keep reads as 0, nor the element at the beginning of the third and of the fourth. The
slots in front of the last sumcheck's are live in the run "norm", the others in the run "logits". -/
theorem forms_live_heard [FinalNorm.Reads] [Head.Reads] {F G : Fork} {rs : List Fmt.RoundView}
    {H : HeardAll} (hW : WellLaid F) (h : Head.hear F rs = some (H, G, []))
    (hN : ∀ r i, (FinalNorm.entry r i).slots = #[]) (hR : ∀ r i, (Head.entry r i).slots = #[])
    (hzt : (FinalNorm.zt).size = Norm.lt)
    (g1 : SumGood H.1.squares) (g2 : SumGood H.1.products) (g3 : SumGood H.2.1.normed)
    (g4 : SumGood H.2.2.logits) (e3 : SumGoodEps H.2.1.normed) (e4 : SumGoodEps H.2.2.logits) :
    letI : Norm.Heard := H.1
    letI : FinalNorm.Heard := H.2.1
    letI : Head.Heard := H.2.2
    (∀ j, F.next ≤ j → j < F.next + (35 + 6 * Norm.lt + 2 * Norm.lPd) →
      liveAt (FinalNorm.forms.map asClaim) j = true) ∧
    (∀ j, F.next + (35 + 6 * Norm.lt + 2 * Norm.lPd) ≤ j → j + 1 < G.next →
      liveAt (Head.logitForms.map asClaim) j = true) := by
  letI : Norm.Heard := H.1
  letI : FinalNorm.Heard := H.2.1
  letI : Head.Heard := H.2.2
  have sz : ∀ {X : Fork}, WellLaid X → OnBytes.PscRun.Sized X := fun w => ⟨w.2.1, w.2.2, w.1⟩
  obtain ⟨G1, G2, l1, hNorm, wG1, wG2, hsN, hsL, _⟩ := Head.Law.Came.hear_parts hW h
  obtain ⟨p0, p1, tS, p2, tP, Fa, Fb, Fc, _, h0, h1, _, h3, h4, h5, wa, wb, wc⟩ :=
    Head.Law.norm_parts hW hNorm
  have hpV : (H.1.pV).size = Norm.lt := Head.Law.drawPoint_size h0
  have hzS : (Head.Law.zS H.1.pV).size = Norm.lPd + Norm.lt := by
    simp [Head.Law.zS, halves, hpV]
  have hzL : (FinalNorm.zt ++ halves Norm.lPd).size = Norm.lt + Norm.lPd := by
    simp [halves, hzt]
  obtain ⟨vW, _, nA⟩ := Head.Law.batch_spec hW h1
  obtain ⟨vP, _, nC⟩ := Head.Law.batch_spec wb h4
  have sW := Head.Law.batch_slots (sz hW) h1
  have sP := Head.Law.batch_slots (sz wb) h4
  have nB := (Head.Law.takes_level (sz wa) h3).next
  have nG1 := (Head.Law.takes_sumcheck (sz wc) h5).next
  have nG2 := (Head.Law.takes_sumcheck (sz wG1) hsN).next
  have nG := (Head.Law.takes_sumcheck (sz wG2) hsL).next
  rw [hzS] at nB
  rw [hpV] at nG1
  rw [hzt] at nG2
  rw [hzL] at nG
  obtain ⟨R4, T4, r4, _, q4, _, _, E4⟩ := Head.Law.level_ends wa h3 (fun _ => zeroE)
  obtain ⟨c6, R6, T6, _, r6, _, cl6, q6, _, _, _, E6⟩ :=
    Head.Law.sumcheck_ends wc h5 (fun _ => zeroE)
  obtain ⟨c7, R7, T7, _, r7, _, cl7, q7, _, _, _, E7⟩ :=
    Head.Law.sumcheck_ends wG1 hsN (fun _ => zeroE)
  obtain ⟨c8, R8, T8, _, r8, _, cl8, q8, _, _, _, E8⟩ :=
    Head.Law.sumcheck_ends wG2 hsL (fun _ => zeroE)
  rw [Head.Law.hidOf_one] at cl6 q6 cl7 q7 cl8 q8
  rw [Head.Law.own_callOf] at E4 E6 E7 E8
  rw [hzS] at E4
  rw [hpV] at E6
  rw [hzt] at E7
  rw [hzL] at E8
  have hr4 : ∀ x ∈ R4.rounds.map (·.2), rd x ≠ 0 := g1 _ q4
  have hr6 : ∀ x ∈ R6.rounds.map (·.2), rd x ≠ 0 := g2 _ q6
  have hr7 : ∀ x ∈ R7.rounds.map (·.2), rd x ≠ 0 := g3 _ q7
  have hr8 : ∀ x ∈ R8.rounds.map (·.2), rd x ≠ 0 := g4 _ q8
  have he7 : rd R7.eps ≠ 0 := e3 _ q7
  have he8 : rd R8.eps ≠ 0 := e4 _ q8
  have K2 := Head.Law.kept_slotsIn F.next Fa.next
  have hstart : SlotsIn F.next Fa.next (Norm.squaresStart H.1.W H.1.gam #[]) := by
    unfold Norm.squaresStart
    exact K2.smulE _ (K2.sums _ _ fun i => K2.sums _ _ fun s => K2.smulE _ (sW _))
  -- the forms' places in the lists
  have mS0 : Norm.squares.left ((Norm.squares.end_ 0).shown * (Norm.squares.end_ 1).shown) ∈
      FinalNorm.forms := mem_square (by unfold Norm.squareForms; exact List.mem_cons_self)
  have mS1 : (Norm.squares.end_ 0).var - (Norm.squares.end_ 1).var ∈ FinalNorm.forms :=
    mem_square (by unfold Norm.squareForms; exact List.mem_cons_of_mem _ List.mem_cons_self)
  have hPF := Head.Law.productForms_eq
  have mN0 : FinalNorm.normed.left ((FinalNorm.normed.end_ 0).shown *
      (FinalNorm.normed.end_ 1).shown) ∈ FinalNorm.forms :=
    mem_normed (by unfold FinalNorm.normedForms; exact List.mem_cons_self)
  have mL0 : Head.logits.left ((Head.logits.end_ 0).shown * (Head.logits.end_ 1).shown) ∈
      Head.logitForms := by unfold Head.logitForms; exact List.mem_cons_self
  constructor
  · intro j j1 j2
    by_cases c1 : j < Fa.next
    · obtain ⟨s, rfl⟩ : ∃ s, j = F.next + s := ⟨j - F.next, by omega⟩
      exact live_W hN (s := s) (by omega) (vW s (by omega))
    by_cases c2 : j < Fa.next + 0 + (2 * (Head.Law.zS H.1.pV).size + 3)
    · exact live_own mS0 r4 q4 hr4 (fun x hx => by have := hstart x hx; omega) j (by omega) c2
    rw [hzS] at c2
    by_cases c3 : j < Fb.next
    · have e0 : (Norm.squares.end_ 0).var =
          Aff.slot (Fa.next + 0 + (2 * (Norm.lPd + Norm.lt) + 3) + 0) := by
        rw [(E4 0 (by omega)).1]
      have e1 : (Norm.squares.end_ 1).var =
          Aff.slot (Fa.next + 0 + (2 * (Norm.lPd + Norm.lt) + 3) + 1) := by
        rw [(E4 1 (by omega)).1]
      rcases (show j = Fa.next + 0 + (2 * (Norm.lPd + Norm.lt) + 3) + 0 ∨
          j = Fa.next + 0 + (2 * (Norm.lPd + Norm.lt) + 3) + 1 by omega) with rfl | rfl
      · exact live_var mS1 e0 (by rw [e1]; exact delta_slot_ne (by omega))
      · exact live_var' mS1 e1 (by rw [e0]; exact delta_slot_ne (by omega))
    by_cases c4 : j < Fc.next
    · obtain ⟨n, rfl⟩ : ∃ n, j = Fb.next + n := ⟨j - Fb.next, by omega⟩
      exact live_P hN (c := Fb.next) (n := n) (by omega) vP
    by_cases c5 : j = Fc.next + 0
    · subst c5
      refine live_var (mem_product (by rw [hPF]; exact List.mem_cons_self))
        (by rw [cl6]) ?_
      exact (kept_delta _).sums 7 _ fun n => (kept_delta _).smulE _
        (delta_slotsIn (sP n) _ (Or.inr (by omega)))
    by_cases c6 : j < Fc.next + 1 + (2 * (H.1.pV).size + 3)
    · exact live_own (mem_product (by
          rw [hPF]; exact List.mem_cons_of_mem _ List.mem_cons_self)) r6 q6 hr6
        (fun x hx => by have := slot_named _ x hx; omega) j (by omega) c6
    rw [hpV] at c6
    by_cases c7 : j < G1.next
    · have RH := rowHas (kept_delta j) (Norm.digit .rowsAtProducts 0) (digitPr_zero hN j)
      have ev : ∀ k, k < 4 → (Norm.products.end_ k).var =
          Aff.slot (Fc.next + 1 + (2 * Norm.lt + 3) + k) := fun k hk => by rw [(E6 k hk).1]
      rcases (show j = Fc.next + 1 + (2 * Norm.lt + 3) + 0 ∨
          j = Fc.next + 1 + (2 * Norm.lt + 3) + 1 ∨ j = Fc.next + 1 + (2 * Norm.lt + 3) + 2 ∨
          j = Fc.next + 1 + (2 * Norm.lt + 3) + 3 by omega) with e | e | e | e
      · subst e
        exact live_var (mem_product (by rw [hPF]; simp)) (ev 0 (by omega)) RH.a
      · subst e
        exact live_var (mem_product (by rw [hPF]; simp)) (ev 1 (by omega)) RH.b
      · subst e
        exact live_var (mem_product (by rw [hPF]; simp)) (ev 2 (by omega)) RH.Rlo
      · subst e
        exact live_var (mem_product (by rw [hPF]; simp)) (ev 3 (by omega)) RH.Rhi
    by_cases c8 : j = G1.next + 0
    · subst c8
      exact live_lead mN0 q7 hr7 (by omega) he7
    by_cases c9 : j < G1.next + 1 + (2 * (FinalNorm.zt).size + 3)
    · exact live_own mN0 r7 q7 hr7 (fun x hx => by have := slot_named _ x hx; omega) j
        (by omega) c9
    rw [hzt] at c9
    have en : ∀ k, k < 2 → (FinalNorm.normed.end_ k).var =
        Aff.slot (G1.next + 1 + (2 * Norm.lt + 3) + k) := fun k hk => by rw [(E7 k hk).1]
    rcases (show j = G1.next + 1 + (2 * Norm.lt + 3) + 0 ∨
        j = G1.next + 1 + (2 * Norm.lt + 3) + 1 by omega) with e | e
    · subst e
      refine live_var (mem_normed (by
        unfold FinalNorm.normedForms
        exact List.mem_cons_of_mem _ List.mem_cons_self)) (en 0 (by omega)) ?_
      exact (rowHas (kept_delta _) _ fun i =>
        (kept_delta _).addN (delta_bare _ _ (hN .rowAtNormed i)) _).R
    · subst e
      refine live_var (mem_normed (by
        unfold FinalNorm.normedForms
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
        (en 1 (by omega)) ?_
      exact (kept_delta _).sums _ _ fun i => (kept_delta _).sums _ _ fun l =>
        (kept_delta _).smulE _ (delta_bare _ _ (hN .streamAtNormed _))
  · intro j j1 j2
    by_cases c1 : j = G2.next + 0
    · subst c1
      exact live_lead mL0 q8 hr8 (by omega) he8
    by_cases c2 : j < G2.next + 1 + (2 * (FinalNorm.zt ++ halves Norm.lPd).size + 3)
    · exact live_own mL0 r8 q8 hr8 (fun x hx => by have := slot_named _ x hx; omega) j
        (by omega) c2
    rw [hzL] at c2
    have e0 : (Head.logits.end_ 0).var =
        Aff.slot (G2.next + 1 + (2 * (Norm.lt + Norm.lPd) + 3) + 0) := by
      rw [(E8 0 (by omega)).1]
    obtain rfl : j = G2.next + 1 + (2 * (Norm.lt + Norm.lPd) + 3) + 0 := by omega
    refine live_var (by
      unfold Head.logitForms
      exact List.mem_cons_of_mem _ List.mem_cons_self) e0 ?_
    exact (kept_delta _).sums _ _ fun k => (kept_delta _).smulE _ (by
      unfold FinalNorm.actAt
      exact (kept_delta _).add (delta_bare _ _ (hR .actAtLogits _))
        ((kept_delta _).smulN _ (delta_bare _ _ (hR .actAtLogits _))))

end Whole

end

#print axioms slot_named
#print axioms mem_square
#print axioms mem_product
#print axioms mem_row
#print axioms mem_normed
#print axioms digitPV_zero
#print axioms digitPr_zero
#print axioms live_W
#print axioms live_P
#print axioms live_var'
#print axioms delta_slot_ne
#print axioms forms_live_heard

end ProofFile.Honest.K6.GoodLaw
