-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/JoinKeepsLastShape.lean: THE JOINTS OF THE RUN ON SHAPES ONCE MORE, KEEPING
THE LAST SHAPE. JoinAll.lean's yes_of_runsAll and JoinTable.lean's table_yes_of_runsAll conclude
that the run on shapes RETURNS; by their own Limits they drop what it returns. Here: from one fact
for each piece (RunsAll, JoinAll.lean) the run over the table's own steps, under the head at the
stored full-size files, returns THE LAST WRITTEN BORDER; and so a state of which the run returns
the shape has that border as its shape. Seven theorems. Implications; nothing is evaluated in this
file.

Purpose. A law on a member far back in the first chain (the proximity test at number 354; the start
of the last chain behind number 358) wants a test on the shape of the state in front to accept.
Such a test can be evaluated only at a written shape. So its caller needs "the state's shape is
this written term", not "the run returns".

Main names.
* `run_of_runsAll`: with a named shape at each border, one RunsAll for each piece: at every record
  that publicOfO returns at the stored full-size files the run over the table's second text, from c
  0, over border len K members, returns c K. (yes_of_runsAll with the value kept: run_of_pieces
  instead of yes_of_pieces.)
* `run_returns_congr`: run_congr (LettersRun.lean) in the form "the run returns e", at letters.
* `run_of_public`, `run_of_public_numerals`: yes_of_public (YesAtZFull.lean) and yes_of_publicN
  (YesAtZFullN.lean) for "the run returns e" instead of "the run returns": from the table's second
  text at LW | LWn of the record that publicOfO returns to the table's own steps at the head's own
  letters. The two elder laws follow from these.
* **`table_run_of_runsAll`**: all pieces as one hypothesis, the first border startShA, the lengths'
  sum n: under the head: (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)).run n startShA = .ok (c K).
  GENERAL IN n: a caller takes the pieces up to the border that it wants.
* `table_yes_at_of_runsAll`: table_yes_of_runsAll (JoinTable.lean) at every border n: the run
  returns over the first n members: the premise on the run of NextWithoutValues.lean's
  first_chain_next.
* **`state_shape_of_runsAll`**: besides, a state s at which the third family for acceptance holds
  at border n (shapeJ, Johnson/Desc/ProofFile/Honest/Thread/ShapeJ.lean: the run over the n members
  in front returns the state's shape): shA s = c K.

Limits. ALL PIECES ARE ONE PREMISE, as in JoinTable.lean: not one RunsAll is shown here, and in the
library none is. If the run on shapes refuses at a guard below n, no len, c, K meet hp, h0 and hK
together, and every theorem here is empty: whether it returns is answered by no theorem
(RuleAtTable.lean's head). UNDER THE HEAD P5J.AtMgA at VerifierAndGoals.storedPublicFiles, with baseOf's return, and
under hsz: that the head has a member, and hsz itself, are shown in a side library alone. n IS NOT
BOUND: from 358 on the table answers every number with the seal's cell, in silence (Table.lean): a
caller that lays pieces beyond 358 gets a true statement about no member of the chain.
state_shape_of_runsAll TAKES shapeJ AT THE STATE AS A PREMISE: NOTHING HERE SHOWS IT AT ANY STATE.
It is carried one member on by NextJ, from first_chain_start. RuleAtTable.lean's first_chain_debts
gives NextJ only under the values at all 358 members, among them 354, where the table's test is
testV, which said no at the one honest run that has been evaluated (TestReturnsFrame.lean's head):
that law carries it at no border of that run. NextWithoutValues.lean's first_chain_next asks the
values at the 25 batching members alone. A state that is held as reached by yeses alone does not
have it (shape_reach, Johnson/Desc/ProofFile/Honest/Thread/Shape.lean, asks the strong Carries at
every member). The theorems rest, through lettersTest_atXL and what lies beneath lw_alike and
record_there, on lines of Lean's kernel, as JoinTable.lean's head lists. For VerifierAndGoals.zGap no such
joint stands. At the format's second hash function; synthetic weights. Nothing on soundness, completeness
or hiding.
-/
import Johnson.AtFull.Shape.JoinTable

set_option autoImplicit false
set_option relaxedAutoImplicit false

-- No default table of scales is in sight: a statement that reads a table says which.
attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.PlanWritten (publicOfO)
open OnBytes.Maker (WholeD)
open P5J (AtMgA)

/-- **yes_of_runsAll WITH THE VALUE KEPT**: with a named shape at each border, one RunsAll for each
piece gives, at every record that publicOfO returns, that the run on shapes over all pieces returns
the last border. -/
theorem run_of_runsAll (len : Nat → Nat) (c : Nat → ShA) (K : Nat)
    (h : ∀ k, k < K → RunsAll (ProofFile.Honest.border len k) (len k) (c k) (c (k + 1)))
    (X₀ : Verify.Public)
    (hX : publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) =
      .ok X₀) :
    (shapeL (LWn X₀)).run (ProofFile.Honest.border len K) (c 0) = .ok (c K) :=
  ProofFile.Honest.run_of_pieces (shapeL (LWn X₀)) len c K fun k hk => h k hk X₀ hX

/-- run_congr (LettersRun.lean) in the form in which a caller hands in what the run returns: the
steps and the tests are letters here, so that Lean compares no two tables of steps. -/
theorem run_returns_congr {g g' : Nat → ShA → Except String ShA}
    {v v' : Nat → S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool}
    (hg : g = g') (hv : v = v') {n : Nat} {a e : ShA}
    (h : (firstZA g' v').run n a = .ok e) : (firstZA g v).run n a = .ok e :=
  (run_congr hg hv n a).trans h

variable {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {Bs : ProofFile.PureBase}

/-- yes_of_public (YesAtZFull.lean) for the run's value. -/
theorem run_of_public (h : AtMgA OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) {a e : ShA} {n : Nat}
    (hk : ∃ X₀ : Verify.Public,
      publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀ ∧
      (shapeL (LW X₀)).run n a = .ok e) :
    (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)).run n a = .ok e := by
  obtain ⟨X₀, hX, ht⟩ := hk
  obtain rfl : X₀ = Zp.p.X := Except.ok.inj (hX.symm.trans (ProofFile.Law.pub_public h.laid.pub))
  obtain ⟨Bs', base, O⟩ := h.laid.opened
  obtain rfl : Bs' = Bs := Except.ok.inj (O.made.symm.trans hB)
  exact run_returns_congr (g_of_alike (lw_alike h O)) (vals_of_alike (lw_alike h O)) ht

/-- yes_of_publicN (YesAtZFullN.lean) for the run's value. -/
theorem run_of_public_numerals (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975)
    (h : AtMgA OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) {a e : ShA} {n : Nat}
    (hk : ∃ X₀ : Verify.Public,
      publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀ ∧
      (shapeL (LWn X₀)).run n a = .ok e) :
    (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)).run n a = .ok e := by
  obtain ⟨X₀, hX, ht⟩ := hk
  obtain ⟨X₁, hX₁, hl⟩ := atXL_zFull hsz lettersTest_atXL
  obtain rfl : X₁ = X₀ := Except.ok.inj (hX₁.symm.trans hX)
  exact run_of_public h hB ⟨_, hX,
    run_returns_congr (funext fun k => congrArg Prod.fst (cells_alike (lwn_alike hl) k))
      (funext fun k => congrArg Prod.snd (cells_alike (lwn_alike hl) k)) ht⟩

/-- **THE LAST JOINT, KEEPING THE LAST SHAPE**: all pieces as one hypothesis, the first border
startShA, the lengths' sum n ⊢ under the head at the stored full-size files the run on shapes over
the table's own steps, over the first n members, returns the last written border. -/
theorem table_run_of_runsAll (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975)
    (h : AtMgA OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)
    (len : Nat → Nat) (c : Nat → ShA) (K n : Nat)
    (hp : ∀ k, k < K → RunsAll (ProofFile.Honest.border len k) (len k) (c k) (c (k + 1)))
    (h0 : c 0 = startShA) (hK : ProofFile.Honest.border len K = n) :
    (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)).run n startShA = .ok (c K) := by
  obtain ⟨X₀, hX⟩ := record_there hsz
  have e := run_of_runsAll len c K hp X₀ hX
  rw [h0, hK] at e
  exact run_of_public_numerals hsz h hB ⟨X₀, hX, e⟩

/-- table_yes_of_runsAll (JoinTable.lean) at every border: the run returns over the first n
members. -/
theorem table_yes_at_of_runsAll (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975)
    (h : AtMgA OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)
    (len : Nat → Nat) (c : Nat → ShA) (K n : Nat)
    (hp : ∀ k, k < K → RunsAll (ProofFile.Honest.border len k) (len k) (c k) (c (k + 1)))
    (h0 : c 0 = startShA) (hK : ProofFile.Honest.border len K = n) :
    (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)).yes startShA n = true := by
  unfold ProofFile.Honest.Shape.yes
  rw [table_run_of_runsAll hsz h hB len c K n hp h0 hK]
  rfl

/-- **THE STATE's SHAPE IS THE WRITTEN BORDER**: at a state s at which the third family for
acceptance holds at border n. -/
theorem state_shape_of_runsAll (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975)
    (h : AtMgA OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)
    (len : Nat → Nat) (c : Nat → ShA) (K n : Nat)
    (hp : ∀ k, k < K → RunsAll (ProofFile.Honest.border len k) (len k) (c k) (c (k + 1)))
    (h0 : c 0 = startShA) (hK : ProofFile.Honest.border len K = n) (s : S)
    (hJ : ProofFile.Honest.shapeJ (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) startShA n s) :
    shA s = c K :=
  Except.ok.inj (Eq.trans (Eq.symm hJ) (table_run_of_runsAll hsz h hB len c K n hp h0 hK))

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.run_of_runsAll
#print axioms Johnson.AtFull.Shape.run_returns_congr
#print axioms Johnson.AtFull.Shape.run_of_public
#print axioms Johnson.AtFull.Shape.run_of_public_numerals
#print axioms Johnson.AtFull.Shape.table_run_of_runsAll
#print axioms Johnson.AtFull.Shape.table_yes_at_of_runsAll
#print axioms Johnson.AtFull.Shape.state_shape_of_runsAll
