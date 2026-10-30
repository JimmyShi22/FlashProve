-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Law/K6MarksBlocks.lean: WHAT IS OWED FOR THE TWO MARKS OF THE
OUTPUT HEAD's OWN SUB-PROTOCOL (K6), AT ONE NAMED KIT: STRINGS OF HASH BLOCKS (`Run.ckP .two`):
`part4Marks_debt_share` (Honest/K6/Law/K6MarksLaw.lean) WITHOUT ITS TWO PREMISES hzG AND hzL.
CONDITIONAL: h; hG; hb; hp; hf. STATEMENTS OVER A CHANCE: NOT YET SEEN BY THE REVIEWER WHO OWNS
SUCH STATEMENTS. Six theorems.

What is here. hzG and hzL bound, at each round that a mark reads, over that one round's messages,
the measure of "the first element that the round draws is 0" (for the second mark: "is 0 or 1").
They are no facts on the sub-protocol: they say what a kit makes of a round's message. At a free
kit they cannot be shown. At strings of hash blocks another sub-protocol's authors have the bound
for a round that draws just one element (`P1K8.gate_of_count_blocks`,
Johnson/P1K8R/GateOfCount.lean). Here it is called at the two marks' rounds.

  `goodRounds_round`        each round that the first mark reads is, as data, a sumcheck's round in
                            a variable, or a sumcheck's first round
  `goodRounds_oneElem`      **so, at data that fit the declared rounds, each such round draws just
                            one element and nothing else**; the second mark's rounds are among them
                            (`linkedRounds_good`, Honest/K6/LinkedMark.lean)
  `goodBad_field`           from the word 0 to the field's 0 (for the second mark:
                            `linkedBad_field`)
  `k6_first_zero_blocks`    one round, the first mark's event
  `k6_first_bit_blocks`     one round, the second mark's event
  `part4Marks_debt_blocks`  **at every mark of the list: `MarkDebt` at that kit, at the mark's own
                            stated share's numerator times one number**

Near kin: `P1K8.bad_gate_blocks_k` (Johnson/P1K8R/MarkRoundsK.lean), the same bound at that file's
own test `oneBad`. It is not called: the two premises are typed at `elemOf`, and the lemma beneath
it serves at once.

Limits.
  * AT ONE KIT ALONE. Which kit a bound on falls is stated at is its authors' to say.
  * THE UNIFORM LAW ON THE ROUNDS' MESSAGES IS NAMED, NOT DERIVED: the called files' own limit.
  * No number is evaluated as a chance.
  * The marks' stated shares are not shown to be held at this kit: they lack the factor
    `Iop.kapSl 128 ^ 3`. Their numerators alone are spent.
  * No theorem ties either mark to the verifier's test that it is for.
  * h: the full size and the format's second hash function alone. hb: that the member lies in the list over
    which a joiner runs stays a premise.
  * All limits of Honest/K6/Law/K6MarksLaw.lean hold here too.
  * Nothing on any property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.K6.Law.K6MarksLaw
import Johnson.P1K8R.MarkRoundsK

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K6
open scoped ENNReal
open OnBytes (E isZeroE)
open OnBytes.Maker (WholeD RDT uLT drawnT)
open VerifiableInference.Desc (Block Place Chain)
open VerifiableInference.Desc.Kinds
open VerifiableInference.Desc.First.K8.Honest (OneElem oneElem_of)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {G₀ : ProofFile.Ground}

/-- Each round that the first mark reads is, as data, a sumcheck's round in a variable or a
sumcheck's first round. No premise. -/
theorem goodRounds_round (p : Head.Par) : ∀ r ∈ goodRounds p,
    (headRoundsOf (headLt p) (headLPd p))[r]? = some headVarRound ∨
      (headRoundsOf (headLt p) (headLPd p))[r]? = some headFirstRound := by
  obtain ⟨f2, f5, f6, f7⟩ := headInFront_at p
  obtain ⟨v2, _⟩ := headRounds_at2 (headLt p) (headLPd p)
  obtain ⟨⟨v5, _⟩, ⟨e6, v6, _⟩, e7, v7, _⟩ := headRounds_at567 (headLt p) (headLPd p)
  intro r hr
  rcases (mem_goodRounds p r).1 hr with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
  · rw [f2]
    exact .inl (v2 j hj)
  · rw [f5]
    exact .inl (v5 j hj)
  · rw [f6]
    cases j with
    | zero =>
      rw [Nat.add_zero]
      exact .inr e6
    | succ j =>
      rw [show headLPd p + 2 * headLt p + 10 + (j + 1) = headLPd p + 2 * headLt p + 10 + 1 + j by
        omega]
      exact .inl (v6 j (by omega))
  · rw [f7]
    cases j with
    | zero =>
      rw [Nat.add_zero]
      exact .inr e7
    | succ j =>
      rw [show headLPd p + 3 * headLt p + 13 + (j + 1) = headLPd p + 3 * headLt p + 13 + 1 + j by
        omega]
      exact .inl (v7 j (by omega))

/-- **EACH ROUND THAT THE FIRST MARK READS DRAWS JUST ONE ELEMENT AND NOTHING ELSE**, at data that
fit the declared rounds; and its positions' logarithm is no more than 64 (it is 0). -/
theorem goodRounds_oneElem (p : Head.Par) (dsb : List RDT)
    (hf : List.Forall₂ KindFits dsb p.rounds) :
    ∀ r ∈ goodRounds p, ∀ d, dsb[r]? = some d → OneElem d.entry d.kind ∧ d.entry.logN ≤ 64 := by
  intro r hr d hd
  obtain ⟨z, hz, he, hk⟩ := H2K.First.forall₂_at KindFits hf r d hd
  rw [headRounds_are, List.getElem?_map] at hz
  rcases goodRounds_round p r hr with e | e
  · rw [e] at hz
    obtain rfl := Option.some.inj hz
    have hk' : d.kind = .elems :=
      Option.some.inj (hk.symm.trans (show Fmt.kindOf "PSC round" = some .elems by decide))
    rw [he, hk']
    exact ⟨oneElem_of _ _ rfl rfl rfl rfl (by decide) (by decide), Nat.zero_le _⟩
  · rw [e] at hz
    obtain rfl := Option.some.inj hz
    have hk' : d.kind = .join :=
      Option.some.inj (hk.symm.trans (show Fmt.kindOf "PSC epsilon" = some .join by decide))
    rw [he, hk']
    exact ⟨oneElem_of _ _ rfl rfl rfl rfl (by decide) (by decide), Nat.zero_le _⟩

/-- **FROM THE WORD 0 TO THE FIELD's 0**: where the first mark's test on one round's challenge
speaks and that challenge shows just one field element x, laid into words by the library's own
`Slice.ofE`, x is 0. No premise beside. -/
theorem goodBad_field (dr : Fmt.Drawn) (x : Cb.Gl.E) (h : isZeroE (elemOf [dr] 0) = true)
    (he : dr.elems = [OnBytes.Slice.ofE x]) : x = 0 := by
  have e : elemOf [dr] 0 = E.ofTriple (OnBytes.Slice.ofE x) := by
    unfold elemOf elemsOf
    simp [he]
  rw [e] at h
  have hx := OnBytes.Slice.toE_ofE x
  unfold isZeroE at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  have t : OnBytes.Slice.ofE x = Fmt.Fld.zeroE := Prod.ext h.1.1 (Prod.ext h.1.2 h.2)
  rw [← hx, t, OnBytes.Slice.toE_zeroE]

/-- One round that draws just one element, at strings of hash blocks: the measure, over that round's
messages, of "the first element that the round draws is 0". -/
theorem k6_first_zero_blocks (d : RDT) (h1 : OneElem d.entry d.kind) (hlog : d.entry.logN ≤ 64) :
    Iop.prRho {ρ : Iop.Rho (uLT (_root_.Run.ckP .two) [d]) |
      isZeroE (elemOf (drawnT (_root_.Run.ckP .two) [d] ρ) 0) = true} ≤
      Iop.kapSl 128 ^ 3 / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) := by
  have k := P1K8.gate_of_count_blocks d h1 hlog (fun dr => isZeroE (elemOf [dr] 0) = true)
    (fun x => x = 0) goodBad_field 1 P1K8.cnt_zero
  rw [Nat.cast_one, mul_one] at k
  refine le_trans (Prob.pr_mono _ fun ρ hρ => ?_) k
  obtain ⟨dr, e⟩ := List.length_eq_one_iff.1
    (VerifiableInference.Desc.Sound.drawnT_length (_root_.Run.ckP .two) [d] ρ)
  have h' : isZeroE (elemOf [dr] 0) = true := by
    rw [← e]
    exact hρ
  exact (⟨dr, e, h'⟩ : ∃ dr, drawnT (_root_.Run.ckP .two) [d] ρ = [dr] ∧
    isZeroE (elemOf [dr] 0) = true)

/-- The same of "is 0 or 1". -/
theorem k6_first_bit_blocks (d : RDT) (h1 : OneElem d.entry d.kind) (hlog : d.entry.logN ≤ 64) :
    Iop.prRho {ρ : Iop.Rho (uLT (_root_.Run.ckP .two) [d]) |
      (!headNotBit (elemOf (drawnT (_root_.Run.ckP .two) [d] ρ) 0)) = true} ≤
      2 * (Iop.kapSl 128 ^ 3 / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞)) := by
  have k := P1K8.gate_of_count_blocks d h1 hlog
    (fun dr => (!headNotBit (elemOf [dr] 0)) = true) (fun x => x = 0 ∨ x = 1) linkedBad_field 2
    P1K8.cnt_zero_one
  have e2 : Iop.kapSl 128 ^ 3 * ((2 : ℕ) : ℝ≥0∞) / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) =
      2 * (Iop.kapSl 128 ^ 3 / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞)) := by
    simp only [div_eq_mul_inv]
    push_cast
    ring
  rw [e2] at k
  refine le_trans (Prob.pr_mono _ fun ρ hρ => ?_) k
  obtain ⟨dr, e⟩ := List.length_eq_one_iff.1
    (VerifiableInference.Desc.Sound.drawnT_length (_root_.Run.ckP .two) [d] ρ)
  have h' : (!headNotBit (elemOf [dr] 0)) = true := by
    rw [← e]
    exact hρ
  exact (⟨dr, e, h'⟩ : ∃ dr, drawnT (_root_.Run.ckP .two) [d] ρ = [dr] ∧
    (!headNotBit (elemOf [dr] 0)) = true)

/-- CONDITIONAL: h; hG; hb; hp; hf. **`part4Marks_debt_share` AT STRINGS OF HASH BLOCKS, WITHOUT
hzG AND hzL**: at every mark of the list, at its own stated share's numerator times one number. -/
theorem part4Marks_debt_blocks (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀) {b : Block P5J.TS ProofFile.Cl}
    (hb : b ∈ cF.blocksInOrder) (hp : b.place = IM.k6Place) (dsb : List RDT)
    (hf : List.Forall₂ KindFits dsb b.rounds) (P : List Fmt.Drawn → Prop) :
    ∀ mk ∈ part4Marks Zp G₀, MarkDebt (_root_.Run.ckP .two) mk dsb P
      ((mk.share.num : ℝ≥0∞) * (Iop.kapSl 128 ^ 3 / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞))) := by
  have hr : b.rounds = (headParAt G₀).rounds := by
    rw [part4Marks_par hG]
    exact (head_seated_at_head h b hb hp).1
  have hf' := hf
  rw [hr] at hf'
  have one := goodRounds_oneElem (headParAt G₀) dsb hf'
  exact part4Marks_debt_share h hG (_root_.Run.ckP .two) hb hp dsb hf _
    (fun n hn d hd => k6_first_zero_blocks d (one n hn d hd).1 (one n hn d hd).2)
    (fun n hn d hd => k6_first_bit_blocks d
      (one n (linkedRounds_good (headParAt G₀) n hn) d hd).1
      (one n (linkedRounds_good (headParAt G₀) n hn) d hd).2) P

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.goodRounds_round
#print axioms ProofFile.Honest.K6.goodRounds_oneElem
#print axioms ProofFile.Honest.K6.goodBad_field
#print axioms ProofFile.Honest.K6.k6_first_zero_blocks
#print axioms ProofFile.Honest.K6.k6_first_bit_blocks
#print axioms ProofFile.Honest.K6.part4Marks_debt_blocks
