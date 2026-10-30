-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/MarksDebt.lean: THE SENTENCE `MarkDebt`
(Johnson/Desc/ProofFile/Honest/Law/CoverJoin.lean: over the verifier's uniform messages of a
member's rounds a mark's test speaks with measure at most a number) AT THE TWO MARKS OF AN ATTENTION
SEGMENT's OWN ROUNDS (kind K5), EACH AT ITS OWN STATED SHARE's VALUE, at strings of hash blocks.
CONDITIONAL: on the data of the member's rounds; in the later sections on the hypothesis on the
public input. Theorems alone; no definition. None of the library's goals. No property is claimed.

Why. Whoever adds up the chances at the first chain asks of each mark's owner a bound on how often
the mark speaks (the field hM of `FirstAsks`, Johnson/Desc/ProofFile/Honest/Law/CoverAsks.lean).
Here are the bounds for this kind's marks (24 under the head: `k5Marks_length`,
Law/MarksListLaw.lean).

Main names:
  `zero_gate_blocks`, `live_share` one listed round: "the one element drawn is 0, or none is shown,
    or its words are not below the prime" (the last two are not drawn at such a round: read off the
    proof of `P1K8.gate_of_count_blocks`; no statement says so): at most the factor's cube over the
    number of field elements; the written pair with the factor 1 is n times that
  `live_markDebt_blocks` **the second mark (`mkLive`, Law/MarkLive.lean) at its own stated share's
    value.** CONDITIONAL on hd: at each listed number the round's data draw one element and nothing
    else
  `pair_small` the written pair's value is below 1 where the factor times the number of listed
    rounds is at most 2 ^ 64: there a sentence at that value is no idle one. That both lists are so
    short under the head: Law/MarksSmall.lean
  `live_data`, `live_data_head`   hd from hk: the data fit the declared rounds
  `fits_of_kinds`, `fits_exists`, `fits_exists_head`, `k5Marks_fits` data that fit are there: so hk
    is not empty. THE DATA SHOWN ARE MADE UP: each round's entry and kind and nothing else; they are
    not the data that the description's maker makes (that those fit: `kinds_of_data`,
    Johnson/Desc/ProofFile/Honest/Law/DataKinds.lean, and `kindFits_at`, Law/CoverFitAt.lean beside
    it: not called here)
  `mkReads_debt_head`, `mkLive_debt_head` CONDITIONAL on the head h: both marks at the data of the
    member at number 14 (2 g + 1) + 4. The first is one call of `P1K8.reads_markDebt_blocks`
    (Johnson/P1K8R/MarkReadsDebt.lean) at `reads_data_head` (Law/MarksData.lean)
  `k5Marks_debt` CONDITIONAL on h and hB: **at every mark of `k5Marks` (Honest/K5/MarksList.lean),
    the chain's member at its place and all data that fit that member's rounds: the mark's sentence
    at its own stated share's value**, whatever is handed of the challenges in front
  `k5Marks_hM` **a sentence in the letters of the field hM**, at this kind's list, from cut: the
    chain's flat list is the gated members and a last one. At the field's own types:
    Law/MarksDebtField.lean

HOW THE SECOND MARK's BOUND GOES. As the bound for a mark that speaks where an element is 0 or 1
(Johnson/P1K8R/MarkRounds.lean), whose steps are general: one round's bound by a count of the bad
elements (`P1K8.gate_of_count_blocks`, Johnson/P1K8R/GateOfCount.lean), here at the count 1, since
this mark's test on one round says yes at 0 alone (`bad0_elem`,
Johnson/Desc/K5/Honest/Law/LiveMark.lean); from one round to all (`P1K8.rounds_le`); the listed
rounds are no more than the list is long (`P1K8.listedN_le`); the pair's value
(`P1K8.share_val_gen`, Johnson/P1K8R/DeadMark.lean).

Limits. AT STRINGS OF HASH BLOCKS ALONE (`Run.ckP .two`); at typed challenges nothing is stated
here. The uniform law on the rounds' messages is named in the sentence, not derived. NO SHARE IS
EVALUATED: each stays a written pair. A sentence at a value of 1 or more says nothing: that each of
the 24 values is below 1 is shown under the head in Law/MarksSmall.lean, not here. How large the 24
are together is not said. The sentence speaks of how often a mark speaks; what a mark's silence
gives stands in Law/MarkLive.lean, Law/MarkReads.lean and Law/MarksOwn.lean. The heads of the first
two say that no sentence on a measure stands in them: it stands here. NO MEMBER OF `FirstAsks` IS
BUILT: what stands here is the sentence of its one field hM, at this kind's marks alone; its other
fields, the sum of the numbers among them, are not treated. The first mark covers two of the
segment's matrices. ON h: it is a hypothesis of every statement that names it; at the library's full
size and the format's second hash function alone. It can be met: AtFullSide.Top.headMember_zFull
(AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say what it is worth).
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.P1K8R.MarkReadsDebt
import Johnson.Desc.ProofFile.Honest.K5.Law.MarksData
import Johnson.Desc.ProofFile.Honest.K5.Law.MarkLive
import Johnson.Desc.K5.Honest.Law.LiveEntries

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest (OneElem)
open H2K5.Honest (liveRounds readRounds bad0 bad0_elem live_round live_draws)
open P5J (AtMgA TS)
open Iop (kapSl)
open scoped ENNReal

/-! ## 1 The second mark: one listed round, the written pair, the sentence -/

/-- **One listed round, at strings of hash blocks**: a round that draws one field element and
nothing else: "the element is 0, or none is shown, or its words are not below the prime" has measure
at most the factor's cube over the number of field elements. Conditional: h1; hlog. -/
theorem zero_gate_blocks (d : RDT) (h1 : OneElem d.entry d.kind) (hlog : d.entry.logN ≤ 64) :
    Iop.prRho {ρ : Iop.Rho (uLT (_root_.Run.ckP .two) [d]) |
      P1K8.oneBad bad0 (drawnT (_root_.Run.ckP .two) [d] ρ) = true} ≤
      kapSl 128 ^ 3 * ((1 : ℕ) : ℝ≥0∞) / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) :=
  le_trans (Prob.pr_mono _ fun _ hρ => P1K8.oneBad_some bad0 _ hρ)
    (P1K8.gate_of_count_blocks d h1 hlog (fun dr => bad0 dr = true) (fun x => x = 0)
      (fun _ _ hb he => bad0_elem hb he) 1 (Prob.cnt_le_one fun _ _ ha hb => ha.trans hb.symm))

/-- The value of the written pair with the factor 1 is n times that bound. -/
theorem live_share (n : ℕ) :
    (⟨1 * n * (2 ^ 128 + 1) ^ 3, Code.pGold ^ 3 * (2 ^ 128) ^ 3⟩ : Odds).val =
      (n : ℝ≥0∞) * (kapSl 128 ^ 3 * ((1 : ℕ) : ℝ≥0∞) / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞)) := by
  rw [P1K8.share_val_gen (1 * n) (Code.pGold ^ 3) 128, Slice.two_p]
  simp only [div_eq_mul_inv]
  push_cast
  ring

/-- **THE SECOND MARK's SENTENCE AT STRINGS OF HASH BLOCKS, AT ITS OWN STATED SHARE's VALUE.**
Conditional: hd: at each listed number the round's data draw one element and nothing else. -/
theorem live_markDebt_blocks (l : ℕ) (x : OnBytes.Params.AttentionRounds) (ds : List RDT)
    (hd : ∀ i d, ds[i]? = some d → i ∈ liveRounds x →
      OneElem d.entry d.kind ∧ d.entry.logN ≤ 64) (Q : List Fmt.Drawn → Prop) :
    MarkDebt (_root_.Run.ckP .two) (mkLive l x) ds Q (mkLive l x).share.val := by
  intro fr _
  refine le_trans (le_trans (Prob.pr_mono _ fun ρ hρ => ?_)
    (P1K8.rounds_le _ bad0 (fun i => decide (i ∈ liveRounds x)) _ ds fun i d hi hm =>
      zero_gate_blocks d (hd i d hi (of_decide_eq_true hm)).1
        (hd i d hi (of_decide_eq_true hm)).2)) ?_
  · show P1K8.anyBad bad0 (fun i => decide (i ∈ liveRounds x)) 0 _ = true
    rw [← P1K8.anyBad_eq]
    exact mkLive_walk l x fr _ hρ
  · show _ ≤ (⟨1 * (liveRounds x).length * (2 ^ 128 + 1) ^ 3,
      Code.pGold ^ 3 * (2 ^ 128) ^ 3⟩ : Odds).val
    rw [live_share]
    exact mul_le_mul' (by exact_mod_cast P1K8.listedN_le (liveRounds x) 0 ds.length) le_rfl

/-- **The written pair's value is below 1 where the factor times the number of listed rounds is at
most 2 ^ 64**: so a sentence at that value is no idle one there. k: the factor times the number. -/
theorem pair_small (k : ℕ) (hk : k ≤ 2 ^ 64) :
    (⟨k * (2 ^ 128 + 1) ^ 3, Code.pGold ^ 3 * (2 ^ 128) ^ 3⟩ : Odds).val < 1 := by
  have h1 : k * (2 ^ 128 + 1) ^ 3 < Code.pGold ^ 3 * (2 ^ 128) ^ 3 :=
    lt_of_le_of_lt (Nat.mul_le_mul_right _ hk) (by
      unfold Code.pGold
      norm_num)
  refine ENNReal.div_lt_of_lt_mul ?_
  rw [one_mul]
  exact_mod_cast h1

/-! ## 2 The data at the rounds that the second mark lists -/

/-- **The data at the rounds that the second mark lists, at the kind's own declared rounds.**
Conditional: hk: the data fit the declared rounds. -/
theorem live_data (p : Att.P.Par) {dsb : List RDT}
    (hk : List.Forall₂ KindFits dsb (Att.P.rounds p)) :
    ∀ i d, dsb[i]? = some d → i ∈ liveRounds p.own →
      OneElem d.entry d.kind ∧ d.entry.logN ≤ 64 := by
  intro i d hi hL
  obtain ⟨e, he, hr⟩ := live_round p i hL
  obtain ⟨e', he', -, hl, ⟨k, hk1, hk2, hk3⟩, hds⟩ := live_draws p.own i hL
  obtain rfl : e' = e := Option.some.inj (he'.symm.trans he)
  obtain ⟨e1, e2⟩ := K5Law.forall₂_at hk hi hr
  have e3 : Fmt.kindOf e'.name = some d.kind := e2
  obtain rfl : k = d.kind := Option.some.inj (hk1.symm.trans e3)
  rw [e1]
  exact ⟨hds p.work _ hk3 hk2, by
    show e'.logN ≤ 64
    rw [hl]
    exact Nat.zero_le _⟩

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : Look.Place}

/-- **The same under the head, at the member.** Conditional: h: the head; hg; ea: the group's plan;
f4: which member; hk: the data fit its declared rounds. -/
theorem live_data_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {g : ℕ} (hg : g < 12)
    {a : Attention.Plan} (ea : (P5J.At.X Zp).A[g]? = some a) {b4 : Block S ProofFile.Cl}
    (f4 : cF.blocksInOrder[14 * (2 * g + 1) + 4]? = some b4) {dsb : List RDT}
    (hk : List.Forall₂ KindFits dsb b4.rounds) :
    ∀ i d, dsb[i]? = some d → i ∈ liveRounds a.own →
      OneElem d.entry d.kind ∧ d.entry.logN ≤ 64 := by
  rw [rounds_at_head h hg ea f4] at hk
  exact live_data (parAt Zp g a) hk

/-! ## 3 Data that fit are there -/

/-- Where the format knows every declared round's name, there are data that fit the rounds. -/
theorem fits_of_kinds : ∀ zs : List Fmt.DeclaredRound,
    (∀ z ∈ zs, ∃ k, Fmt.kindOf z.entry.name = some k) → ∃ ds : List RDT, List.Forall₂ KindFits ds zs
  | [], _ => ⟨[], .nil⟩
  | z :: zs, hz => by
    obtain ⟨k, hk⟩ := hz z (List.mem_cons_self ..)
    obtain ⟨ds, hd⟩ := fits_of_kinds zs fun w hw => hz w (List.mem_cons_of_mem _ hw)
    exact ⟨⟨⟨z.entry, k, [], [], []⟩, []⟩ :: ds, .cons ⟨rfl, hk⟩ hd⟩

/-- **There are data that fit the kind's own declared rounds**: so the premise hk is not empty. No
premise. -/
theorem fits_exists (p : Att.P.Par) :
    ∃ ds : List RDT, List.Forall₂ KindFits ds (Att.P.rounds p) := by
  refine fits_of_kinds _ fun z hz => ?_
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hz
  obtain ⟨k, hk, -⟩ := Att.P.kind_entriesOf _ _ e he
  refine ⟨k, ?_⟩
  show Fmt.kindOf (if e.drawE == 0 then e else { e with work := p.work }).name = some k
  split <;> exact hk

/-- The same under the head, at the member. Conditional: h; hg; ea; f4. -/
theorem fits_exists_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {g : ℕ} (hg : g < 12)
    {a : Attention.Plan} (ea : (P5J.At.X Zp).A[g]? = some a) {b4 : Block S ProofFile.Cl}
    (f4 : cF.blocksInOrder[14 * (2 * g + 1) + 4]? = some b4) :
    ∃ ds : List RDT, List.Forall₂ KindFits ds b4.rounds := by
  rw [rounds_at_head h hg ea f4]
  exact fits_exists _

/-! ## 4 Both marks under the head -/

/-- **THE FIRST MARK's SENTENCE UNDER THE HEAD, AT THE MEMBER's DATA.** Conditional: as
`reads_data_head`. -/
theorem mkReads_debt_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {g : ℕ} (hg : g < 12)
    {a : Attention.Plan} (ea : (P5J.At.X Zp).A[g]? = some a) {b4 : Block S ProofFile.Cl}
    (f4 : cF.blocksInOrder[14 * (2 * g + 1) + 4]? = some b4) {dsb : List RDT}
    (hk : List.Forall₂ KindFits dsb b4.rounds) (Q : List Fmt.Drawn → Prop) :
    MarkDebt (_root_.Run.ckP .two) (mkReads (2 * g + 1) a.own (Att.P.parCOf a).geo) dsb Q
      (mkReads (2 * g + 1) a.own (Att.P.parCOf a).geo).share.val :=
  P1K8.reads_markDebt_blocks _ _ _ _ dsb (reads_data_head h hg ea f4 hk) Q

/-- **THE SECOND MARK's SENTENCE UNDER THE HEAD, AT THE MEMBER's DATA.** Conditional: as
`live_data_head`. -/
theorem mkLive_debt_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {g : ℕ} (hg : g < 12)
    {a : Attention.Plan} (ea : (P5J.At.X Zp).A[g]? = some a) {b4 : Block S ProofFile.Cl}
    (f4 : cF.blocksInOrder[14 * (2 * g + 1) + 4]? = some b4) {dsb : List RDT}
    (hk : List.Forall₂ KindFits dsb b4.rounds) (Q : List Fmt.Drawn → Prop) :
    MarkDebt (_root_.Run.ckP .two) (mkLive (2 * g + 1) a.own) dsb Q
      (mkLive (2 * g + 1) a.own).share.val :=
  live_markDebt_blocks _ _ dsb (live_data_head h hg ea f4 hk) Q

/-! ## 5 At every mark of the list -/

/-- **AT EVERY MARK OF THE LIST AND THE CHAIN's MEMBER AT ITS PLACE: THE MARK's SENTENCE AT ITS OWN
STATED SHARE's VALUE.** Conditional: h: the head; hB: the base's return; hm; hb; hp: the two places
are one; hk: the data fit the member's declared rounds. -/
theorem k5Marks_debt (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) {mk : Mark}
    (hm : mk ∈ k5Marks Zp Bs.G₀) {b : Block S ProofFile.Cl} (hb : b ∈ cF.blocksInOrder)
    (hp : mk.place = b.place) {dsb : List RDT} (hk : List.Forall₂ KindFits dsb b.rounds)
    (Q : List Fmt.Drawn → Prop) : MarkDebt (_root_.Run.ckP .two) mk dsb Q mk.share.val := by
  obtain ⟨g, hg, a, ea, f4, rfl | rfl⟩ := k5Marks_member_is_head h hB hm hb hp
  · exact mkReads_debt_head h hg ea f4 hk Q
  · exact mkLive_debt_head h hg ea f4 hk Q

/-- At every mark of the list and the chain's member at its place there are data that fit.
Conditional: h; hB; hm; hb; hp. -/
theorem k5Marks_fits (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) {mk : Mark}
    (hm : mk ∈ k5Marks Zp Bs.G₀) {b : Block S ProofFile.Cl} (hb : b ∈ cF.blocksInOrder)
    (hp : mk.place = b.place) : ∃ ds : List RDT, List.Forall₂ KindFits ds b.rounds := by
  obtain ⟨g, hg, a, ea, f4, -⟩ := k5Marks_member_is_head h hB hm hb hp
  exact fits_exists_head h hg ea f4

/-- **THE SAME IN THE LETTERS OF THE FIELD hM** (`FirstAsks`,
Johnson/Desc/ProofFile/Honest/Law/CoverAsks.lean), at the list of this kind's marks, at the number
"the mark's own stated share's value", whatever PM. Conditional: h; hB; cut: the chain's flat list
is the gated members and a last one. -/
theorem k5Marks_hM (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)
    {pre₁ : List (Block S ProofFile.Cl)} {e₁ : Block S ProofFile.Cl} (cut : cF.blocksInOrder = pre₁ ++ [e₁])
    (PM : Block S ProofFile.Cl → List Fmt.Drawn → Prop) :
    ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      ∀ mk ∈ (k5Marks Zp Bs.G₀).filter (fun m => m.place == b.place), ∀ dsb : List RDT,
      List.Forall₂ KindFits dsb b.rounds →
      MarkDebt (_root_.Run.ckP .two) mk dsb (PM b) mk.share.val := by
  intro A b b' B hpre mk hmk dsb hk
  obtain ⟨hm, hq⟩ := List.mem_filter.1 hmk
  have hb : b ∈ cF.blocksInOrder := by
    rw [cut, hpre]
    simp
  exact k5Marks_debt h hB hm hb (eq_of_beq hq) hk (PM b)

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.zero_gate_blocks
#print axioms ProofFile.Honest.K5.live_share
#print axioms ProofFile.Honest.K5.live_markDebt_blocks
#print axioms ProofFile.Honest.K5.pair_small
#print axioms ProofFile.Honest.K5.live_data
#print axioms ProofFile.Honest.K5.live_data_head
#print axioms ProofFile.Honest.K5.fits_of_kinds
#print axioms ProofFile.Honest.K5.fits_exists
#print axioms ProofFile.Honest.K5.fits_exists_head
#print axioms ProofFile.Honest.K5.mkReads_debt_head
#print axioms ProofFile.Honest.K5.mkLive_debt_head
#print axioms ProofFile.Honest.K5.k5Marks_debt
#print axioms ProofFile.Honest.K5.k5Marks_fits
#print axioms ProofFile.Honest.K5.k5Marks_hM
