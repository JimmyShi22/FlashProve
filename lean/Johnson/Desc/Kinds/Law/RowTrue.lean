-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/RowTrue.lean: "NO BAD DRAW" UNDER THE OUTPUT HEAD's ONE RULE CAN BE MET IF THE ROUNDS ARE AT THE TRUTH: at rounds on which the block's hearing returns and which
are "at the truth" (RowTruth: NormTruth for the normalization's own rounds; for "normed" and for the head's own sumcheck: the
claimed sum hides the true sum, and each round's completed polynomial is the true round polynomial), THE RULE's LISTS ARE EMPTY AT
EVERY FRONT THAT IS ASKED, WHATEVER IS DRAWN: Sound.NoBad (rowRuleC c mask F) rs: STATED AND PROVED.
WHAT IT DOES NOT SAY. THAT ANY ROUNDS MEET RowTruth: the true round polynomials (tqG, tqP, tqL) are chosen; that an honest prover's rounds
complete to them and that the hearing returns on them is shown nowhere here. So THE ROW's
PREMISES ARE NOT SHOWN TO BE MET TOGETHER. Nothing on Opened.
  noBad_append     clean under two rules: clean under their lists laid together.
  blockRule_front  at a front of at most the normalization's number of rounds the rule behind it is empty.
  NormedTrue · LogitsTrue · RowTruth   the truth, stretch by stretch.
  normed_true · logits_true · block_true · row_true
  ruleK6T_of_row   from the block's one rule to K6's rule cut at the tight ceiling (Law/RowPrice.lean), at a record.
IMPORTED, NOT PROVED HERE: Law/NormTrue.lean (norm_true, noBadG_true, noBad_glue, cut_of_noBad); Law/NoBadTrue.lean (noBad_true). The two
equations on tailRule at a front stand inside Law/RowHalf.lean's block_parts too.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.RowPrice

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E addE mulE)
open OnBytes.Model (Fork Reading)
open Norm (lt ls d lPd S2 T)
open Part.MaskedSum (movesOf readAll leadScalars Sent)
open Sound (cutTo strikeLast)
open Came (kG cvG tqG SmN sigN hSN)

variable [Sizes] [Policy] [Request] [Token] [FinalNorm.In]

/-- "normed" at the truth: the claimed sum hides the true sum; each round's completed polynomial is the true one. -/
def NormedTrue (c : NCells) (mask : Nat → E) (Fa : Fork) (tN : List Fmt.RoundView) : Prop :=
  ∀ R c0, readAll (kG FinalNorm.zt 2) tN = some R → leadScalars (kG FinalNorm.zt 2) tN = some [c0] →
    cvG mask Fa c0 = sigN c ∧
    ∀ i m, (movesOf Reading.gl (kG FinalNorm.zt 2).all R.rounds
        (addE R.mu (mulE R.eps (tgt c0))))[i]? = some m →
      m.1 = tqG FinalNorm.zt 2 (by omega) (SmN c mask Fa) (sigN c) (hSN c mask Fa) mask Fa
        (rd (tgt c0)) (sigN c) (rd R.mu) (rd R.eps)
        (((movesOf Reading.gl (kG FinalNorm.zt 2).all R.rounds
          (addE R.mu (mulE R.eps (tgt c0)))).take i).map (·.2))

variable [In]

/-- The head's own sumcheck at the truth. -/
def LogitsTrue (c : Cells) (mask : Nat → E) (Fb : Fork) (tL : List Fmt.RoundView) : Prop :=
  ∀ R c0, readAll kP tL = some R → leadScalars kP tL = some [c0] →
    cvP mask Fb c0 = sigP c ∧
    ∀ i m, (movesOf Reading.gl kP.all R.rounds
        (addE R.mu (mulE R.eps (tgt c0))))[i]? = some m →
      m.1 = tqP c mask Fb (rd (tgt c0)) (cvP mask Fb c0) (rd R.mu) (rd R.eps)
        (((movesOf Reading.gl kP.all R.rounds (addE R.mu (mulE R.eps (tgt c0)))).take i).map
          (·.2))

/-- **THE BLOCK's ROUNDS AT THE TRUTH**: at the stretches into which the hearing falls. -/
def RowTruth (c : NCells) (mask : Nat → E) (F : Fork) (rs : List Fmt.RoundView) : Prop :=
  NormTruth c mask F rs ∧
  ∀ (pre tN tL : List Fmt.RoundView) (Hn : Norm.Heard) (Fa Fb F1 : Fork) (SN SL : Sum),
    rs = pre ++ tN ++ tL → Norm.hear F pre = some (Hn, Fa, []) →
    sumcheck FinalNorm.zt 2 Fa tN = some (SN, Fb, []) →
    sumcheck (FinalNorm.zt ++ halves lPd) 2 Fb tL = some (SL, F1, []) →
    NormedTrue c mask Fa tN ∧ LogitsTrue c.toCells mask Fb tL

namespace Came

theorem noBad_append {a b : List Fmt.RoundView → List E} {rs : List Fmt.RoundView} (ha : NoBad a rs)
    (hb : NoBad b rs) : NoBad (fun f => a f ++ b f) rs :=
  fun i r hi x hx hm => (List.mem_append.mp hm).elim (ha i r hi x hx) (hb i r hi x hx)

/-- At a front of at most the normalization's number of rounds the rule behind it is empty. -/
theorem blockRule_front (c : NCells) (mask : Nat → E) (F : Fork) (hW : WellLaid F)
    {h : List Fmt.RoundView} (hl : h.length ≤ 3 + lvl + smc) : blockRule c mask F h = [] := by
  cases hN : Norm.hear F h with
  | none => exact blockRule_none c mask F hN
  | some v =>
    obtain ⟨H, G, left⟩ := v
    have e := norm_length hW hN
    have hz : left = [] := List.length_eq_zero_iff.mp (by omega)
    subst hz
    exact blockRule_at_end c mask F hN

theorem normed_true (c : NCells) (mask : Nat → E) {Fa Fb : Fork} {tN : List Fmt.RoundView} {S : Sum}
    (h : sumcheck FinalNorm.zt 2 Fa tN = some (S, Fb, [])) (hq : NormedTrue c mask Fa tN) :
    NoBad (normedRule c mask Fa) tN := by
  obtain ⟨ld, cA, Fx, Gx, hd, es, _, a2, _, a4, _⟩ := sumcheck_spec h
  obtain ⟨_, _, R, _, hread, _⟩ := Part.MaskedSum.hear_spec a4
  obtain ⟨r0, used, rv, front, ht, hs0, hfl, _⟩ :=
    Part.MaskedSum.readAll_spec
      (show readAll ⟨1, vsG FinalNorm.zt, some ⟨2, 2⟩⟩ tN = some R from hread)
  obtain ⟨c0, rfl⟩ := List.length_eq_one_iff.mp hfl
  have hs0' : Sent r0 2 1 [c0, R.mu] [R.eps] := hs0
  have hlead : leadScalars (kG FinalNorm.zt 2) tN = some [c0] := by
    rw [ht]
    exact lead_of_sent hs0'
  obtain ⟨hC, hm⟩ := hq R c0 hread hlead
  exact noBadG_true FinalNorm.zt 2 (by omega) _ _ _ mask Fa hread hlead hC hm

theorem logits_true (c : Cells) (mask : Nat → E) {Fb F1 : Fork} {tL : List Fmt.RoundView} {S : Sum}
    (h : sumcheck (FinalNorm.zt ++ halves lPd) 2 Fb tL = some (S, F1, []))
    (hq : LogitsTrue c mask Fb tL) : NoBad (badP c mask Fb) tL := by
  obtain ⟨ld, cA, Fx, Gx, hd, es, _, a2, _, a4, _⟩ := sumcheck_spec h
  obtain ⟨_, _, R, _, hread, _⟩ := Part.MaskedSum.hear_spec a4
  obtain ⟨r0, used, rv, front, ht, hs0, hfl, _⟩ :=
    Part.MaskedSum.readAll_spec (show readAll ⟨1, vsP, some ⟨2, 2⟩⟩ tL = some R from hread)
  obtain ⟨c0, rfl⟩ := List.length_eq_one_iff.mp hfl
  have hs0' : Sent r0 2 1 [c0, R.mu] [R.eps] := hs0
  have hlead : leadScalars kP tL = some [c0] := by
    rw [ht]
    exact lead_of_sent hs0'
  obtain ⟨hC, hm⟩ := hq R c0 hread hlead
  exact noBad_true c mask Fb hread hlead hC hm

/-- **At the truth no draw is bad under the rule behind the normalization's rounds.** -/
theorem block_true (c : NCells) (mask : Nat → E) (F : Fork) (hW : WellLaid F) {rs : List Fmt.RoundView}
    {H : HeardAll} {F1 : Fork} (hhear : hear F rs = some (H, F1, []))
    (ht : RowTruth c mask F rs) : NoBad (blockRule c mask F) rs := by
  obtain ⟨Fa, Fb, l1, hNorm, hWa, hWb, hsN, hsL, hleft⟩ := hear_parts hW hhear
  obtain ⟨pre0, hrs, eN⟩ := consumes_norm _ _ _ _ _ hNorm
  obtain ⟨pN, hpN, eS⟩ := consumes_sumcheck _ _ _ _ _ _ _ hsN
  rw [List.append_nil] at hpN
  have hlenN : (l1.take ((FinalNorm.zt).size + 3)).length = (FinalNorm.zt).size + 3 := by
    obtain ⟨_, _, h3⟩ := sumcheck_cut hsN
    rw [List.length_take] at h3 ⊢
    omega
  have hL' : (l1.drop ((FinalNorm.zt).size + 3)).take
      ((FinalNorm.zt ++ halves Norm.lPd).size + 3) = l1.drop ((FinalNorm.zt).size + 3) := by
    apply List.take_of_length_le
    have h0 := congrArg List.length hleft
    rw [List.length_nil, List.length_drop] at h0
    omega
  rw [hL'] at hsL
  have hcut : rs = pre0 ++ l1.take ((FinalNorm.zt).size + 3) ++ l1.drop ((FinalNorm.zt).size + 3) := by
    rw [List.append_assoc, List.take_append_drop]
    exact hrs
  have hpre : Norm.hear F pre0 = some (H.1, Fa, []) := by
    have := eN []
    rwa [List.append_nil] at this
  have hpl : pre0.length = 3 + lvl + smc := by
    have := norm_length hW hpre
    simpa using this
  obtain ⟨tN1, tL1⟩ := ht.2 pre0 _ _ H.1 Fa Fb F1 _ _ hcut hpre hsN hsL
  rw [hcut]
  refine noBad_glue (noBad_glue ?_ (fun i r hi => ?_) (normed_true c mask hsN tN1))
    (fun i r hi => ?_) (logits_true c.toCells mask hsL tL1)
  · -- inside the normalization's own rounds
    intro i r hi x _ hm
    have hil : i < pre0.length := (List.getElem?_eq_some_iff.mp hi).1
    rw [blockRule_front c mask F hW (by
      rw [List.length_append, List.length_take, List.length_singleton]
      omega)] at hm
    simp at hm
  · have hil : i < (l1.take ((FinalNorm.zt).size + 3)).length :=
      (List.getElem?_eq_some_iff.mp hi).1
    show tailRule (normedRule c mask) (badP c.toCells mask) F _ = _
    unfold tailRule
    rw [eN]
    dsimp only
    rw [if_pos]
    rw [List.length_append, List.length_take, List.length_singleton]
    omega
  · show tailRule (normedRule c mask) (badP c.toCells mask) F _ = _
    unfold tailRule
    rw [List.append_assoc, eN]
    dsimp only
    rw [if_neg (by rw [List.length_append, hlenN, List.length_append, List.length_singleton]; omega),
      hpN, eS]

/-- **AT THE TRUTH NO DRAW OF THE BLOCK's ROUNDS IS BAD, WHATEVER IS DRAWN.** -/
theorem row_true (c : NCells) (mask : Nat → E) (F : Fork) (hW : WellLaid F) {rs : List Fmt.RoundView}
    {H : HeardAll} {F1 : Fork} (hhear : hear F rs = some (H, F1, []))
    (ht : RowTruth c mask F rs) : Sound.NoBad (rowRuleC c mask F) rs := by
  obtain ⟨Fa, Fb, l1, hNorm, _⟩ := hear_parts hW hhear
  refine cut_of_noBad (p := pointRule c) (b := rowRule c mask F) (pointRule_empty c ht.1.1) ?_
  exact noBad_append
    (noBad_of_cut (p := pointRule c) (b := normRule c mask F) (norm_true c mask F hW hNorm ht.1))
    (block_true c mask F hW hhear ht)

end Came

end VerifiableInference.Desc.Kinds.Head.Law

namespace VerifiableInference.Desc.Kinds.Head.Law.Came

open OnBytes (E)

/-- Clean under the block's one rule at the letters that given returns: clean under K6's rule cut at the tight ceiling. -/
theorem ruleK6T_of_row {S : Type} (p : Par) (L : Seat S) (s : S) (c : NCells) (mask : Nat → E)
    {g : Given} (hg : given p L s = .ok g) {rs : List Fmt.RoundView}
    (h : Sound.NoBad (rowRuleC c mask (L.ledger s)) rs) :
    Sound.NoBad (ruleK6T p L s c mask) rs := by
  have h1 : Sound.NoBad (ruleCutAt p L s c mask) rs := by
    unfold ruleCutAt
    rw [hg]
    exact h
  exact noBadCut_take h1

end VerifiableInference.Desc.Kinds.Head.Law.Came

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.ruleK6T_of_row
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.block_true
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.row_true
