-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/Row117PubFull.lean: THE KEY FILE's ROW 1.17: ITS PUBLIC PREMISES (Public117 · «W's mask's number is below noId») AS CLOSED FACTS BY THE KERNEL AT THE WRITTEN KEY (Lk6.AtPlan.keyFull), and the joint to the source's letters: so that IN THE GOALS' SCOPE they are theorems, not tests.
  wMsg                       what the written shape's message with W holds
  wMsg_some · wMsg_size · w_answers · m_answers · w_noSplit · w_ahead · w_lay · w_small     BY THE KERNEL at keyFull
  w_answers_no               A CONTROL: W's notice does not have 0 answers (the test on the answers can say no)
  w_trees · trees117_full    BY THE KERNEL: the place has just one tree there; so Row117Eight's «the place has a tree» holds in scope
  public117_full             FROM «the source's ranges, shape and codes are keyFull's» (five_in_scope, Johnson/RunOne/Law/KeyInScope.lean, gives all three in scope) · «the plan's samples are 1» · the sending kind's own test on the plan at the place: THERE IS a Public117, and the number is small
TWO THINGS STAY PREMISES: (a) one.given.plan.samples = 1: it is none of the five equations in scope · (b) planOkOwn at the place (it reads the groups told, which are the source's): cond_parts (Johnson/Desc/K1/Law/Port6.lean) has it out of condPort.
Nothing on soundness.
-/
import Johnson.RunOne.KeyWLaid
import Johnson.Goal.PlanValues.KeySizedReturns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFD
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.Key
open VerifiableInference.Desc.K1 (planOkOwn)
open Johnson.RunOne.KeyRows1 (Public117 parW' wAt)
open Lk6.AtPlan (keyFull)

def wMsg : Array OracleNotice := (linMessageW keyFull.once.shape).getD #[]

theorem wMsg_isSome : (linMessageW keyFull.once.shape).isSome = true := by decide +kernel

theorem wMsg_some : linMessageW keyFull.once.shape = some wMsg := by
  have h := wMsg_isSome
  unfold wMsg
  cases h' : linMessageW keyFull.once.shape with
  | none => rw [h'] at h; cases h
  | some m => rfl

theorem wMsg_size : wMsg.size = 2 := by decide +kernel
theorem w_answers : (wMsg[0]?).map (·.shape.answers) = some 1 := by decide +kernel
theorem w_answers_no : ¬ (wMsg[0]?).map (·.shape.answers) = some 0 := by decide +kernel
theorem m_answers : (wMsg[1]?).map (·.shape.answers) = some 0 := by decide +kernel
theorem w_noSplit : keyFull.once.shape.ownSplitNeeded = false := by decide +kernel
theorem w_ahead : keyFull.once.shape.masksAhead = true := by decide +kernel
theorem w_small : 1 + 2 * keyFull.ranges.x.stages.length + 1 < noId := by decide +kernel

def layB (codes : Codes) (msg : Array OracleNotice) : Bool :=
  match layTrees codes msg with
  | some lay => lay.shapes.size == 1 && lay.tree.getD 0 0 == 0 && lay.part.getD 0 0 == 0 && lay.tree.getD 1 0 == 0 && lay.part.getD 1 0 == 1
  | none => true

theorem w_lay : layB keyFull.codes wMsg = true := by decide +kernel
/-- The layout is made there: so w_lay is not met by the arm «none». -/
theorem w_lay_made : (layTrees keyFull.codes wMsg).isSome = true := by decide +kernel

theorem two_of_size {α : Type} (m : Array α) (h : m.size = 2) : ∃ a b, m = #[a, b] := by
  obtain ⟨l⟩ := m
  match l, h with
  | [a, b], _ => exact ⟨a, b, rfl⟩

theorem public117_full (one : OneTime) (N : Pieces) (groups : List (List Nat)) (h1 : one.ranges = keyFull.ranges.x) (h2 : one.lin = keyFull.once.shape) (h5 : one.codes = keyFull.codes)
    (hsmp : one.given.plan.samples = 1) (hplan : ∀ msg, linMessageW one.lin = some msg → planOkOwn (parW' one N groups msg) = true) :
    Nonempty (Public117 one N groups) ∧ wAt one + 1 < noId := by
  obtain ⟨a, b, hab⟩ := two_of_size wMsg wMsg_size
  have hm : linMessageW one.lin = some #[a, b] := by rw [h2, wMsg_some, hab]
  have ha : a.shape.answers = 1 := by
    have := w_answers
    rw [hab] at this
    exact Option.some.inj this
  have hb : b.shape.answers = 0 := by
    have := m_answers
    rw [hab] at this
    exact Option.some.inj this
  refine ⟨⟨{ n₁ := a, n₂ := b, two := hm, plan := hplan _ hm, answers := by rw [ha, hsmp], sampled := by rw [ha]; decide, bare := hb
             noSplit := by rw [h2]; exact w_noSplit, ahead := by rw [h2]; exact w_ahead
             lay := fun lay hl => by
               have h := w_lay
               unfold layB at h
               rw [hab, ← h5, hl] at h
               simp only [Bool.and_eq_true, beq_iff_eq] at h
               exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩ }⟩, ?_⟩
  unfold wAt
  rw [h1]
  exact w_small

/-- The place has just one tree, at the written key. -/
theorem w_trees : (((VerifiableInference.Desc.Own.treesMade keyFull.codes wMsg).map (·.shapes.toList)).getD []).length = 1 := by decide +kernel

/-- **«The place has a tree»** (Row117Eight's htrees), from the shape's and the codes' equations. -/
theorem trees117_full (one : OneTime) (N : Pieces) (groups : List (List Nat)) (h2 : one.lin = keyFull.once.shape) (h5 : one.codes = keyFull.codes) (Pb : Public117 one N groups) :
    0 < (parW' one N groups #[Pb.n₁, Pb.n₂]).trees.length := by
  have e : #[Pb.n₁, Pb.n₂] = wMsg := Option.some.inj (Pb.two.symm.trans (h2 ▸ wMsg_some))
  show 0 < (((VerifiableInference.Desc.Own.treesMade one.codes #[Pb.n₁, Pb.n₂]).map (·.shapes.toList)).getD []).length
  rw [e, h5, w_trees]
  decide

end LPFD

#print axioms LPFD.w_trees
#print axioms LPFD.trees117_full
#print axioms LPFD.wMsg_size
#print axioms LPFD.w_lay
#print axioms LPFD.w_answers_no
#print axioms LPFD.public117_full
