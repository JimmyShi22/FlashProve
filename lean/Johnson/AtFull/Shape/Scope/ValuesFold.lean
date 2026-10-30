-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/ValuesFold.lean: THE FIRST CHAIN's DEBT ON THE VALUES, CUT BY SORT OF MEMBER. The rule
for acceptance at the table of steps (first_chain_debts_halved, RuleAtTable.lean) asks `ValuesJ` at each of
the 358 members. At 204 of them the table's test on values is no test: `plainV`, `vals_plain`. What is left,
154 members in eighteen sorts, is one structure with a field a sort: `SortValues`. `values_fold`: it gives the
rule's premise. `debts_of_sorts`: the rule with that premise handed in. General in the public part and the
ground but for the last law, which stands under the head. Nothing is evaluated but one count.

Limits. NOTHING SAYS THAT A FIELD OF SortValues CAN BE MET. The run on shapes (hyes) and the test `halved` stay
premises of debts_of_sorts. RuleAtTable.lean's Limits are inherited: T, Said and fall are free letters. Nothing
on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.RuleAtTable

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S)
open OnBytes.Maker (WholeD)
open P5J (AtMgA)
open ProofFile.Honest (Shape Thread Coins Mid ProverCoinCounts ValuesJ NextJ AcceptedJ shapeJ halved)

/-! ## 1 Where the table's test on values is no test -/

def plainLink (l : Nat) : LinkRow Bool where
  laid := true
  first := l == 0
  lookCalls := true
  own := l % 2 == 1
  reads := l % 2 == 0
  draw := true
  digits := true
  lookDigits := true
  batch := false
  behind := false
  equation := false
  close := false
  shut := true
  cleared := true

def plainHead : HeadRow Bool where
  laid := true
  reply := false
  switch := false
  lookCalls := true
  own := false
  reads := false
  draw := true
  digits := true
  lookDigits := false
  merge := true
  batch := false
  behind := false
  equation := false
  close := false
  shut := true
  cleared := true

def plainBack : BackRow Bool where
  finish := false
  test := false
  batching := true
  sendW := true
  sealing := true

/-- The numbers of the members at which the table's test on values is no test. -/
def plainV : Nat → Bool := table true plainLink plainHead plainBack

theorem plainV_count : ((List.range 358).filter plainV).length = 204 := by decide +kernel

section
variable (Z : ProofFile.Pub) (G : ProofFile.Ground) (s : S) (rs : List Fmt.RoundView)
  (gs : List (List (Nat × List UInt64)))

theorem opening_v : (Tab.opening Z G).2 s rs gs = true := by
  unfold Tab.opening
  repeat' split
  all_goals rfl

theorem lookCalls_v (l : Nat) : (Tab.lookCalls Z l).2 s rs gs = true := by
  unfold Tab.lookCalls
  repeat' split
  all_goals rfl

theorem lookDigits_v (l : Nat) : (Tab.lookDigits Z l).2 s rs gs = true := by
  unfold Tab.lookDigits
  repeat' split
  all_goals rfl

theorem k5_v (g : Nat) : (Tab.k5 Z g).2 s rs gs = true := by
  unfold Tab.k5
  repeat' split
  all_goals rfl

theorem reads_lay_v (l : Nat) (h : l % 2 = 0) : (Tab.reads Z G l).2 s rs gs = true := by
  unfold Tab.reads
  split
  · rw [if_pos (by simp [h])]
    split <;> rfl
  · rfl

theorem draw_v (l : Nat) : (Tab.draw Z G l).2 s rs gs = true := by
  unfold Tab.draw
  repeat' split
  all_goals rfl

theorem digits_v (l : Nat) : (Tab.digits Z G l).2 s rs gs = true := by
  unfold Tab.digits
  repeat' split
  all_goals rfl

theorem cleared_v (l : Nat) : (Tab.cleared Z l).2 s rs gs = true := by
  unfold Tab.cleared
  repeat' split
  all_goals rfl

theorem sendW_v : (Tab.sendW Z).2 s rs gs = true := by
  unfold Tab.sendW
  repeat' split
  all_goals rfl

/-- A number below 358 is the front's, a link's, the head's link's or the back row's. -/
theorem number_cases {b : Nat} (hb : b < 358) :
    b = 0 ∨ (∃ l j, l < 24 ∧ j < 14 ∧ b = 14 * l + j + 1) ∨ (∃ j, j < 16 ∧ b = 337 + j) ∨
      ∃ j, j < 5 ∧ b = 353 + j := by
  by_cases h0 : b = 0
  · exact Or.inl h0
  by_cases h1 : b < 337
  · exact Or.inr (Or.inl ⟨(b - 1) / 14, (b - 1) % 14, by omega, by omega, by omega⟩)
  by_cases h2 : b < 353
  · exact Or.inr (Or.inr (Or.inl ⟨b - 337, by omega, by omega⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨b - 353, by omega, by omega⟩))

/-- **AT THESE NUMBERS THE TABLE's TEST ON VALUES ACCEPTS EVERYTHING.** No premise on Z and G. -/
theorem vals_plain {b : Nat} (hb : b < 358) (h : plainV b = true) : Tab.vals Z G b s rs gs = true := by
  unfold Tab.vals Tab.cells
  unfold plainV at h
  rcases number_cases hb with rfl | ⟨l, j, hl, hj, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
  · rfl
  · rw [table_link _ _ _ _ l j hl hj] at h ⊢
    interval_cases j
    · rfl
    · have h0 : l = 0 := eq_of_beq (show (l == 0) = true from h)
      subst h0
      exact opening_v Z G s rs gs
    · exact lookCalls_v Z s rs gs l
    · have h1 : l % 2 = 1 := eq_of_beq (show (l % 2 == 1) = true from h)
      show (if l % 2 == 0 then Tab.k4 G (l / 2) else Tab.k5 Z (l / 2)).2 s rs gs = true
      rw [if_neg (by simp [h1])]
      exact k5_v Z s rs gs _
    · exact reads_lay_v Z G s rs gs l (eq_of_beq (show (l % 2 == 0) = true from h))
    · exact draw_v Z G s rs gs l
    · exact digits_v Z G s rs gs l
    · exact lookDigits_v Z s rs gs l
    · exact absurd (show false = true from h) (by decide)
    · exact absurd (show false = true from h) (by decide)
    · exact absurd (show false = true from h) (by decide)
    · exact absurd (show false = true from h) (by decide)
    · rfl
    · exact cleared_v Z s rs gs l
  · rw [table_head _ _ _ _ j hj] at h ⊢
    interval_cases j
    · rfl
    · exact absurd (show false = true from h) (by decide)
    · exact absurd (show false = true from h) (by decide)
    · exact lookCalls_v Z s rs gs 24
    · exact absurd (show false = true from h) (by decide)
    · exact absurd (show false = true from h) (by decide)
    · exact draw_v Z G s rs gs 24
    · exact digits_v Z G s rs gs 24
    · exact absurd (show false = true from h) (by decide)
    · rfl
    · exact absurd (show false = true from h) (by decide)
    · exact absurd (show false = true from h) (by decide)
    · exact absurd (show false = true from h) (by decide)
    · exact absurd (show false = true from h) (by decide)
    · rfl
    · exact cleared_v Z s rs gs 24
  · rw [table_back _ _ _ _ j] at h ⊢
    interval_cases j
    · exact absurd (show false = true from h) (by decide)
    · exact absurd (show false = true from h) (by decide)
    · rfl
    · exact sendW_v Z s rs gs
    · rfl

end

/-! ## 2 What is left, a field a sort -/

section
variable {V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S ProofFile.Cl V W X Pb)
  (Said : Nat → Coins Bk → Mid W X → Prop) (J : Nat → S → Prop) (Zs : Shape S)
  (fall : Nat → S → List Fmt.Drawn → Option String)

/-- **THE DEBT ON THE VALUES AT THE FIRST CHAIN, BY SORT OF MEMBER**: `ValuesJ` at the 154 members at which
the table has a test on values. It is a definition: a premise's form. -/
structure SortValues : Prop where
  /-- the code switch at the links 1 to 23: switchW -/
  switch : ∀ l, 0 < l → l < 24 → ValuesJ T Said J Zs fall (14 * l + 1 + 1)
  /-- the layers' own rounds, at the even links: k4ValsV -/
  layers : ∀ l, l < 24 → l % 2 = 0 → ValuesJ T Said J Zs fall (14 * l + 3 + 1)
  /-- the reads' sending at the attention's links: midV at valsTS -/
  readsAtt : ∀ l, l < 24 → l % 2 = 1 → ValuesJ T Said J Zs fall (14 * l + 4 + 1)
  /-- the batching: cellV -/
  batch : ∀ l, l < 24 → ValuesJ T Said J Zs fall (14 * l + 8 + 1)
  /-- behind the batching: behindV₃ | behindV -/
  behind : ∀ l, l < 24 → ValuesJ T Said J Zs fall (14 * l + 9 + 1)
  /-- the one equation: oneV -/
  equation : ∀ l, l < 24 → ValuesJ T Said J Zs fall (14 * l + 10 + 1)
  /-- the closing: closeInOrdB -/
  close : ∀ l, l < 24 → ValuesJ T Said J Zs fall (14 * l + 11 + 1)
  /-- the reply: replyV -/
  reply : ValuesJ T Said J Zs fall (337 + 1)
  /-- the code switch at the head: headW -/
  switchHead : ValuesJ T Said J Zs fall (337 + 2)
  /-- the head's own rounds: k6V -/
  head : ValuesJ T Said J Zs fall (337 + 4)
  /-- the head's reads: midV at covered -/
  readsHead : ValuesJ T Said J Zs fall (337 + 5)
  /-- the lookup on the head's own digits: headVals -/
  lookHead : ValuesJ T Said J Zs fall (337 + 8)
  /-- the batching at the head: cellV -/
  batchHead : ValuesJ T Said J Zs fall (337 + 10)
  /-- behind it: behindV -/
  behindHead : ValuesJ T Said J Zs fall (337 + 11)
  /-- the one equation at the head: oneV -/
  equationHead : ValuesJ T Said J Zs fall (337 + 12)
  /-- the closing at the head: closeInOrdB -/
  closeHead : ValuesJ T Said J Zs fall (337 + 13)
  /-- the finish: switchW -/
  finish : ValuesJ T Said J Zs fall (353 + 0)
  /-- the proximity test: testV -/
  test : ValuesJ T Said J Zs fall (353 + 1)

end

section
variable {V W X Pb : Type} {Bk : ProverCoinCounts} {T : Thread Bk S ProofFile.Cl V W X Pb}
  {Said : Nat → Coins Bk → Mid W X → Prop} {J : Nat → S → Prop}
  {fall : Nat → S → List Fmt.Drawn → Option String} {Z : ProofFile.Pub} {G : ProofFile.Ground}

/-- At a number where the table has no test the debt on the values is paid. -/
theorem valuesJ_plain {b : Nat} (hb : b < 358) (h : plainV b = true) :
    ValuesJ T Said J (firstZA (Tab.g Z G) (Tab.vals Z G)) fall b :=
  fun _ _ _ s _ _ _ y cols _ _ _ _ _ _ => vals_plain Z G s _ _ hb h

/-- **THE FOLD**: the sorts' debts give the rule's premise at all 358 members. -/
theorem values_fold (H : SortValues T Said J (firstZA (Tab.g Z G) (Tab.vals Z G)) fall) (b : Nat)
    (hb : b < 358) : ValuesJ T Said J (firstZA (Tab.g Z G) (Tab.vals Z G)) fall b := by
  by_cases hp : plainV b = true
  · exact valuesJ_plain hb hp
  · unfold plainV at hp
    rcases number_cases hb with rfl | ⟨l, j, hl, hj, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
    · exact absurd rfl hp
    · rw [table_link _ _ _ _ l j hl hj] at hp
      interval_cases j
      · exact absurd rfl hp
      · refine H.switch l (Nat.pos_of_ne_zero fun e => hp ?_) hl
        subst e
        rfl
      · exact absurd rfl hp
      · refine H.layers l hl ?_
        have : ¬ l % 2 = 1 := fun e => hp (show (l % 2 == 1) = true from by simp [e])
        omega
      · refine H.readsAtt l hl ?_
        have : ¬ l % 2 = 0 := fun e => hp (show (l % 2 == 0) = true from by simp [e])
        omega
      · exact absurd rfl hp
      · exact absurd rfl hp
      · exact absurd rfl hp
      · exact H.batch l hl
      · exact H.behind l hl
      · exact H.equation l hl
      · exact H.close l hl
      · exact absurd rfl hp
      · exact absurd rfl hp
    · rw [table_head _ _ _ _ j hj] at hp
      interval_cases j
      · exact absurd rfl hp
      · exact H.reply
      · exact H.switchHead
      · exact absurd rfl hp
      · exact H.head
      · exact H.readsHead
      · exact absurd rfl hp
      · exact absurd rfl hp
      · exact H.lookHead
      · exact absurd rfl hp
      · exact H.batchHead
      · exact H.behindHead
      · exact H.equationHead
      · exact H.closeHead
      · exact absurd rfl hp
      · exact absurd rfl hp
    · rw [table_back _ _ _ _ j] at hp
      interval_cases j
      · exact H.finish
      · exact H.test
      · exact absurd rfl hp
      · exact absurd rfl hp
      · exact absurd rfl hp

end

/-! ## 3 The rule with that premise handed in -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {Bs : ProofFile.PureBase}

/-- **THE FIRST CHAIN's TWO DEBTS FROM THE RUN ON SHAPES, ONE TEST WITH CODE, AND THE SORTS' VALUES.** -/
theorem debts_of_sorts (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) {V W X Pb : Type} {Bk : ProverCoinCounts}
    (T : Thread Bk S ProofFile.Cl V W X Pb) (hbs : T.bs = cF.blocksInOrder)
    (Said : Nat → Coins Bk → Mid W X → Prop)
    (fall : Nat → S → List Fmt.Drawn → Option String)
    (hyes : (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)).yes startShA 358 = true)
    (h4 : halved cF.blocksInOrder T.hs = true)
    (H : SortValues T Said (shapeJ (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) startShA)
      (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) fall) :
    (∀ b, b < T.bs.length →
        AcceptedJ T Said (shapeJ (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) startShA) fall b) ∧
      (∀ b, b < T.bs.length →
        NextJ T Said (shapeJ (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) startShA) fall b) :=
  first_chain_debts_halved h hB T hbs Said fall startShA hyes h4 (values_fold H)

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.plainV_count
#print axioms Johnson.AtFull.Shape.vals_plain
#print axioms Johnson.AtFull.Shape.valuesJ_plain
#print axioms Johnson.AtFull.Shape.values_fold
#print axioms Johnson.AtFull.Shape.debts_of_sorts
