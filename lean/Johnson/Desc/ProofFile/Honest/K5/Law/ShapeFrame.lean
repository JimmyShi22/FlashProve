-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/ShapeFrame.lean: CONDITIONAL: THE FRAME's TWO PREMISES
(Carries, Returns: Honest/Thread/Shape.lean) AT THE MEMBER OF THE KIND "AN ATTENTION SEGMENT's OWN
ROUNDS" (K5) OF EACH OF THE TWELVE GROUPS, AT THE FIRST CHAIN's LETTERS AT THE END: firstZA g vals
(Johnson/AtFull/Shape/FrameForm.lean), whose shapes are the chain's shape with the rows' makes.
Definitions, and statements with their proofs.

Why. Honest/K5/Law/ShapeChain.lean has the two premises at firstShape guard upd vals, whose shapes
are the chain's shape alone. Johnson/AtFull/Shape/FrameLift.lean carries such a pair over
(carries_lift, returns_lift) at a member whose accepting step leaves the rows' makes. The kind's
step leaves the whole statement: by the term of the state behind. (FrameForm.lean's head leaves open
whether these shapes are enough for every member's step: at this kind they are: k5Q reads and turns
the chain's shape alone.) THE PREMISE ON vals IS NOT SPENT: the kind's member has no test on values;
it stands for the table's form.

Main names:
  `k5Q x`   **the kind's step on the chain's shape as one named term**: the kind's one Bool, then
    its one update
  `k5V`   **the kind's test on values as one named Bool**: it has none: true
  `k5Q_is`   it is firstShape's step at the kind's letters
  `k5_leaves_makes`   the member's accepting step leaves the rows' makes
  `k5_frame`   **for g below 12: a member stands at 28 g + 18; a is the group's plan; and for every
    ft, G and vals with G (28 g + 18) = liftQ (k5Q …) and vals (28 g + 18) = k5V: Carries and
    Returns at firstZA G vals**

`k5_frame` IS CONDITIONAL on the hypothesis on the public input (P5J.AtMgA,
Johnson/P5J/MgAtAll.lean): h is a hypothesis of every statement that names it; the library's
P5J.head_exists_at_name gives a member under four premises on the public files; this file does not
call it.
Whose. By the authors of the attention sub-protocol's (K5's) own rounds.
Limits. TWO PREMISES OF THE RULE AT TWELVE MEMBERS: the rule asks them at every member, and more. G
and vals are letters: no table of steps is laid. No state at which k5Q returns is laid here
(Honest/K5/Law/ShapeChain.lean's k5GC_at_thr has the Bool's yes wherever the thread thrAt stands in
front of the member, under that thread's sentence). The Bool is sufficient, not proved to be
necessary. At the format's second hash function.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.ShapeChain
import Johnson.AtFull.Shape.FrameLift

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc (Block Chain Claim First.S step_iff)
open VerifiableInference.Desc.First.Att.P
open VerifiableInference.Desc.First.Shape (ChainSh formsOf)
open Johnson.AtFull.Shape (ShA firstZA liftQ LeavesMakes carries_lift returns_lift)
open H2K5.Honest (k5_yes_is)
open P5J (AtMgA TS)

/-- **THE KIND's STEP ON THE CHAIN's SHAPE, AS ONE NAMED TERM**: its one Bool, then its one update
(`k5GC`, `k5StepC`: Honest/K5/Law/ShapeChain.lean). -/
def k5Q (x : Params.AttentionRounds) (a : ChainSh) : Except String ChainSh :=
  if k5GC x a then .ok (k5StepC x a) else .error "a guard on the shape"

/-- **THE KIND's TEST ON VALUES, AS ONE NAMED BOOL**: the kind's member has none. -/
def k5V (_ : First.S) (_ : List Fmt.RoundView) (_ : List (List (Nat × List UInt64))) : Bool := true

/-- It is firstShape's step at the kind's letters, at every border. -/
theorem k5Q_is (x : Params.AttentionRounds)
    (vals : Nat → First.S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool) (b : Nat) :
    (firstShape (fun _ => k5GC x) (fun _ => k5StepC x) vals).g b = k5Q x := rfl

/-- **THE MEMBER's ACCEPTING STEP LEAVES THE ROWS' MAKES**: it leaves the whole statement.
CONDITIONAL on: blk is the member number b and decides as the kind's decision with the two tests
more. -/
theorem k5_leaves_makes {bs : List (Block First.S Claim)} {ft b : Nat} {p : Par}
    {blk : Block First.S Claim} (hb : bs[b]? = some blk) (Dc : DecidesAs p blk) :
    LeavesMakes bs ft b := by
  intro blk' hb' s rs cols s' n hs
  obtain rfl : blk = blk' := Option.some.inj (hb.symm.trans hb')
  obtain ⟨_, hd, _⟩ := (step_iff ft blk s s' rs cols n).1 hs
  obtain ⟨a, hh, G, _, _, rfl⟩ := k5_yes_is p ((Dc.decides _ _ _ _).1 hd).1
  rfl

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **THE FRAME's TWO PREMISES AT THE KIND's MEMBER OF EACH OF THE TWELVE GROUPS.** CONDITIONAL:
under the hypothesis h, which is proved of nothing here. -/
theorem k5_frame (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (g : Nat) (hg : g < 12) :
    ∃ a : Attention.Plan, (cF.blocksInOrder[28 * g + 18]?).isSome = true ∧
      (P5J.At.X Zp).A[g]? = some a ∧
      ∀ (ft : Nat) (G : Nat → ShA → Except String ShA)
        (vals : Nat → First.S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool),
        G (28 * g + 18) = liftQ (k5Q (parAt Zp g a).own) →
        (∀ s rs gs, vals (28 * g + 18) s rs gs = k5V s rs gs) →
        Carries cF.blocksInOrder ft (firstZA G vals) (28 * g + 18) ∧
          Returns cF.blocksInOrder ft (firstZA G vals) (28 * g + 18) := by
  obtain ⟨blk, a, hfl, Pl, Dc⟩ := k5_member h hg
  have eb : borderOf g = 28 * g + 18 := by
    unfold borderOf
    omega
  rw [eb] at hfl
  refine ⟨a, by rw [hfl]; rfl, Pl.plan, fun ft G vals hG _ => ?_⟩
  have hg' : G (28 * g + 18) = liftQ ((firstShape (fun _ => k5GC (parAt Zp g a).own)
      (fun _ => k5StepC (parAt Zp g a).own) vals).g (28 * g + 18)) := by
    rw [k5Q_is]
    exact hG
  exact ⟨carries_lift (k5_carries_first hfl Dc rfl rfl) (k5_leaves_makes hfl Dc) hg',
    returns_lift (k5_returns_first hfl Dc rfl) hg' rfl⟩

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.k5Q_is
#print axioms ProofFile.Honest.K5.k5_leaves_makes
#print axioms ProofFile.Honest.K5.k5_frame
#print axioms ProofFile.Honest.K5.k5Q
#print axioms ProofFile.Honest.K5.k5V
