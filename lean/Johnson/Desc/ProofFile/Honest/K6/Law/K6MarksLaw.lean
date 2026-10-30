-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Law/K6MarksLaw.lean: the list `part4Marks` (Honest/K6/K6Marks.lean)
at the full size: its place under the library's other name, its public numbers, how many rounds
each mark names, and what is owed for the two marks. CONDITIONAL. Thirteen small theorems.

  `part4Marks_eq`         **the list is the list of `goodK6Mark` and `linkedK6TMark`**
                        (Honest/K6/GoodMark.lean, Honest/K6/LinkedMark.lean) at `headParAt G₀` and
                        `IM.k6Place`: by `rfl`. All that follows stands behind it
  `headPlace_is`, `k6Place_is`   the place on the list under the library's two names
  `part4Marks_stands`     under the one hypothesis a member of the chain stands at each mark's place
  `ground_of_base`        where the library's maker of the base returns, its ground is the blank one
  `part4Marks_two`        the list has two members, in the form asked of every such list
  `part4Marks_par`        at the blank ground the list's public numbers are those at which
                        `good_at_head` (Honest/K6/GoodLaw/AtHead.lean) speaks of the first mark
  `markRounds_at`, `part4Marks_rounds`   at the full size the first mark names 68 rounds and the
                        second 36: so neither is a mark that can never speak
  `part4Marks_fits`       data that fit the rounds of the chain's member at the place have a round
                        at each number that either mark reads
  `part4Marks_debt`       **what is owed for each mark, each at its own number**
  `part4Marks_debt_all`   the same at one number for both: in the form `MarkDebt C mk dsb P q` at
                        every mk of the list
  `part4Marks_debt_share`   **at every mk of the list, at its own stated share's numerator times one
                        letter**: the sharp bill in that form

What is paid and what is not. Both debts are calls of `goodK6_markDebt` and `linkedK6T_markDebt`. Of
their two premises the first, that the data have a round at each number read, is paid here under the
one hypothesis at the full size: `head_seated_at_head` (Honest/K6/Law/RowAtHead.lean) gives the
member's rounds. THE SECOND IS A PREMISE HERE TOO, ONCE FOR EACH MARK (hzG, hzL): at each named
round a bound, over that one round's messages, on "its first sampled element is 0" (for the second
mark: "is 0 or 1"). How such a bound comes from a count of values hangs on the kit C. Met for
nothing at the bound 1.

One number for both. Whoever joins the debts of all marks at a place asks one function from marks
to numbers, and pays the sum of its values over the marks there. The two marks stand at one place,
and a mark holds a function, so which of the two a given mark is cannot be tested. So
`part4Marks_debt_all` gives both the sum of the two numbers, and the joined bill is twice that sum.
The sharp bill at two free functions zG and zL wants a test on marks, for example a name in the
structure.

The sharp bill at one letter. A mark bears its stated share, and each share's numerator here is the
number of its events: one at each round of `goodRounds`, two at each round of `linkedRounds`. So
where one letter kap bounds, at each named round, the measure of "its first sampled element is 0",
and 2 kap that of "is 0 or 1", each mark's debt is met at its own numerator times kap
(`part4Marks_debt_share`): a function of the mark that needs no test on marks. The joined bill is
then the sum of the two numerators times kap: at the full size 68 + 72 events.

Limits.
  * That the member b lies in the list over which a joiner runs is a premise (hb).
  * No number is evaluated as a chance. 68 and 36 are counts of rounds.
  * No theorem ties either mark to the verifier's test that it is for.
  * All limits of Honest/K6/K6Marks.lean hold here too.
  * Nothing on any property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.K6.K6Marks
import Johnson.Desc.ProofFile.Honest.K6.LinkedMark
import Johnson.Desc.ProofFile.Honest.K6.Law.RowAtHead
import Johnson.Desc.ProofFile.Law.MakerPublic
import Johnson.Desc.Kinds.Law.K6FrontSays
import Johnson.Desc.Kinds.Law.TablesPlanInScope
import Johnson.Desc.Kinds.Law.WeightTwinAt
import Johnson.IMR.PureJoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K6
open scoped ENNReal
open OnBytes (E isZeroE)
open OnBytes.Maker (WholeD RDT uLT drawnT)
open _root_.Run.PQ (CK)
open VerifiableInference.Desc (Block Place Chain)
open VerifiableInference.Desc.Kinds
open VerifiableInference.Desc.Kinds.Head.Law (workOf)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {G₀ : ProofFile.Ground}

/-- **The list is the list of the two marks as their own files define them.** The light file writes
the two structures out. -/
theorem part4Marks_eq (Zp : ProofFile.Pub) (G₀ : ProofFile.Ground) :
    part4Marks Zp G₀ =
      [goodK6Mark (headParAt G₀) IM.k6Place, linkedK6TMark (headParAt G₀) IM.k6Place] :=
  rfl

/-- The place on the list is the library's. -/
theorem headPlace_is : headPlace 24 4 = IM.k6Place :=
  rfl

/-- The library has the place under two names. -/
theorem k6Place_is : IM.k6Place = VerifiableInference.Desc.Kinds.Head.Law.AtFold.placeK6 :=
  rfl

/-- Where the maker of the base returns, its ground is the one made at the blank request. -/
theorem ground_of_base {Bs : ProofFile.PureBase}
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) :
    ProofFile.blankBy ProofFile.pureRoad.links Zp = some Bs.G₀ :=
  (IM.base_made hB).2.2.1

/-- Two marks, under the two hypotheses under which the length of such a list is asked. Neither is
spent: see `part4Marks_length`. -/
theorem part4Marks_two (_h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    (_hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) :
    (part4Marks Zp Bs.G₀).length = 2 :=
  rfl

/-- At the blank ground the sub-protocol's public numbers are those read off the public part. -/
theorem part4Marks_par (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀) :
    headParAt G₀ = Head.parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp)) := by
  unfold headParAt
  rw [ProofFile.Law.blankBy_W hG]
  rfl

/-- The two lists' lengths, from three numbers. -/
theorem markRounds_at (p : Head.Par) (h1 : headLt p = 10) (h2 : headLs p = 6)
    (h3 : headLPd p = 13) : (goodRounds p).length = 68 ∧ (linkedRounds p).length = 36 := by
  have g := goodRounds_length p
  have l := linkedRounds_length p (by omega)
  unfold goodK6Events at g
  exact ⟨by omega, by omega⟩

/-- **At the full size the first mark names 68 rounds and the second 36.** -/
theorem part4Marks_rounds (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀) :
    (goodRounds (headParAt G₀)).length = 68 ∧ (linkedRounds (headParAt G₀)).length = 36 := by
  obtain ⟨_, _, _, _, s5, s6, s7, _⟩ :=
    VerifiableInference.Desc.Kinds.Head.Law.InScope.sizes_five h.scope h.reads h.pubOne
  rw [part4Marks_par hG]
  exact markRounds_at _ s6 s5
    (@VerifiableInference.Desc.Kinds.Head.Law.Came.lPd_ref
      (Head.parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))).sizes s7)

/-- **A member of the chain stands at each mark's place**: so each mark is asked. CONDITIONAL: the
one hypothesis. -/
theorem part4Marks_stands (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∀ mk ∈ part4Marks Zp G₀, ∃ b ∈ cF.blocksInOrder, b.place = mk.place := by
  obtain ⟨b, e, M⟩ := P4.k6_member_at_mg h.toAtMg
  have hb : b ∈ cF.blocksInOrder := List.mem_of_getElem? e
  have hp : b.place = IM.k6Place := (member_is M).1
  intro mk hmk
  rw [part4Marks_eq] at hmk
  rcases List.mem_cons.1 hmk with rfl | h2
  · exact ⟨b, hb, hp⟩
  · rcases List.mem_cons.1 h2 with rfl | h3
    · exact ⟨b, hb, hp⟩
    · exact absurd h3 List.not_mem_nil

/-- Data that fit the rounds of the chain's member at the place have a round at each number that the
first mark reads, and so at each that the second reads. -/
theorem part4Marks_fits (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀) {b : Block P5J.TS ProofFile.Cl}
    (hb : b ∈ cF.blocksInOrder) (hp : b.place = IM.k6Place) (dsb : List RDT)
    (hf : List.Forall₂ KindFits dsb b.rounds) :
    ∀ n ∈ goodRounds (headParAt G₀), n < dsb.length := by
  have hr : b.rounds = (headParAt G₀).rounds := by
    rw [part4Marks_par hG]
    exact (head_seated_at_head h b hb hp).1
  rw [hr] at hf
  exact goodRounds_lt_of_fits (headParAt G₀) dsb hf

/-- **WHAT IS OWED FOR EACH MARK, EACH AT ITS OWN NUMBER.** b: the chain's member at the place. dsb:
data that fit its rounds. zG, zL: at a round's number, a bound over that one round's messages (hzG,
hzL: premises). P: what is handed of the challenges in front: any: neither test reads them. -/
theorem part4Marks_debt (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀) (C : CK) {b : Block P5J.TS ProofFile.Cl}
    (hb : b ∈ cF.blocksInOrder) (hp : b.place = IM.k6Place) (dsb : List RDT)
    (hf : List.Forall₂ KindFits dsb b.rounds) (zG zL : Nat → ℝ≥0∞)
    (hzG : ∀ n ∈ goodRounds (headParAt G₀), ∀ d, dsb[n]? = some d →
      Iop.prRho {ρ : Iop.Rho (uLT C [d]) | isZeroE (elemOf (drawnT C [d] ρ) 0) = true} ≤ zG n)
    (hzL : ∀ n ∈ linkedRounds (headParAt G₀), ∀ d, dsb[n]? = some d →
      Iop.prRho {ρ : Iop.Rho (uLT C [d]) | (!headNotBit (elemOf (drawnT C [d] ρ) 0)) = true} ≤
        zL n)
    (P : List Fmt.Drawn → Prop) :
    MarkDebt C (goodK6Mark (headParAt G₀) IM.k6Place) dsb P
        ((goodRounds (headParAt G₀)).map zG).sum ∧
      MarkDebt C (linkedK6TMark (headParAt G₀) IM.k6Place) dsb P
        ((linkedRounds (headParAt G₀)).map zL).sum := by
  have hlen := part4Marks_fits h hG hb hp dsb hf
  exact ⟨goodK6_markDebt C dsb (headParAt G₀) IM.k6Place zG hlen hzG P,
    linkedK6T_markDebt C dsb (headParAt G₀) IM.k6Place zL
      (fun n hn => hlen n (linkedRounds_good (headParAt G₀) n hn)) hzL P⟩

/-- **The same at one number for both marks**: at every mark of the list. The number is the sum of
the two, so a joiner that adds it up over the two marks pays twice that sum. -/
theorem part4Marks_debt_all (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀) (C : CK) {b : Block P5J.TS ProofFile.Cl}
    (hb : b ∈ cF.blocksInOrder) (hp : b.place = IM.k6Place) (dsb : List RDT)
    (hf : List.Forall₂ KindFits dsb b.rounds) (zG zL : Nat → ℝ≥0∞)
    (hzG : ∀ n ∈ goodRounds (headParAt G₀), ∀ d, dsb[n]? = some d →
      Iop.prRho {ρ : Iop.Rho (uLT C [d]) | isZeroE (elemOf (drawnT C [d] ρ) 0) = true} ≤ zG n)
    (hzL : ∀ n ∈ linkedRounds (headParAt G₀), ∀ d, dsb[n]? = some d →
      Iop.prRho {ρ : Iop.Rho (uLT C [d]) | (!headNotBit (elemOf (drawnT C [d] ρ) 0)) = true} ≤
        zL n)
    (P : List Fmt.Drawn → Prop) :
    ∀ mk ∈ part4Marks Zp G₀, MarkDebt C mk dsb P
      (((goodRounds (headParAt G₀)).map zG).sum + ((linkedRounds (headParAt G₀)).map zL).sum) := by
  obtain ⟨dG, dL⟩ := part4Marks_debt h hG C hb hp dsb hf zG zL hzG hzL P
  unfold MarkDebt at dG dL
  intro mk hmk
  rw [part4Marks_eq] at hmk
  rcases List.mem_cons.1 hmk with rfl | h2
  · unfold MarkDebt
    intro fr hfr
    exact le_trans (dG fr hfr) le_self_add
  · rcases List.mem_cons.1 h2 with rfl | h3
    · unfold MarkDebt
      intro fr hfr
      exact le_trans (dL fr hfr) le_add_self
    · exact absurd h3 List.not_mem_nil

/-- **At every mark of the list, at its own stated share's numerator times kap.** kap: a bound, at
each round that either mark reads, over that one round's messages, on "its first sampled element is
0" (hzG); twice kap bounds "is 0 or 1" (hzL). Both are premises. -/
theorem part4Marks_debt_share (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀) (C : CK) {b : Block P5J.TS ProofFile.Cl}
    (hb : b ∈ cF.blocksInOrder) (hp : b.place = IM.k6Place) (dsb : List RDT)
    (hf : List.Forall₂ KindFits dsb b.rounds) (kap : ℝ≥0∞)
    (hzG : ∀ n ∈ goodRounds (headParAt G₀), ∀ d, dsb[n]? = some d →
      Iop.prRho {ρ : Iop.Rho (uLT C [d]) | isZeroE (elemOf (drawnT C [d] ρ) 0) = true} ≤ kap)
    (hzL : ∀ n ∈ linkedRounds (headParAt G₀), ∀ d, dsb[n]? = some d →
      Iop.prRho {ρ : Iop.Rho (uLT C [d]) | (!headNotBit (elemOf (drawnT C [d] ρ) 0)) = true} ≤
        2 * kap)
    (P : List Fmt.Drawn → Prop) :
    ∀ mk ∈ part4Marks Zp G₀, MarkDebt C mk dsb P ((mk.share.num : ℝ≥0∞) * kap) := by
  have hlen := part4Marks_fits h hG hb hp dsb hf
  intro mk hmk
  rw [part4Marks_eq] at hmk
  rcases List.mem_cons.1 hmk with rfl | h2
  · exact goodK6_markDebt_one C dsb (headParAt G₀) IM.k6Place kap hlen hzG P
  · rcases List.mem_cons.1 h2 with rfl | h3
    · have d := linkedK6T_markDebt_one C dsb (headParAt G₀) IM.k6Place (2 * kap)
        (fun n hn => hlen n (linkedRounds_good (headParAt G₀) n hn)) hzL P
      have e : (((linkedK6TMark (headParAt G₀) IM.k6Place).share.num : ℕ) : ℝ≥0∞) * kap =
          ((linkedRounds (headParAt G₀)).length : ℝ≥0∞) * (2 * kap) := by
        show ((2 * (linkedRounds (headParAt G₀)).length : ℕ) : ℝ≥0∞) * kap = _
        push_cast
        ring
      rw [e]
      exact d
    · exact absurd h3 List.not_mem_nil

#print axioms part4Marks_eq
#print axioms headPlace_is
#print axioms k6Place_is
#print axioms ground_of_base
#print axioms part4Marks_two
#print axioms part4Marks_par
#print axioms markRounds_at
#print axioms part4Marks_rounds
#print axioms part4Marks_stands
#print axioms part4Marks_fits
#print axioms part4Marks_debt
#print axioms part4Marks_debt_all
#print axioms part4Marks_debt_share

end ProofFile.Honest.K6
