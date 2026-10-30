-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/ShapeMember.lean: CONDITIONAL: THE CUT "STRUCTURE | VALUES"
(Honest/Thread/Shape.lean: Shape, Carries, Returns) AT THE MEMBER OF THE KIND "AN ATTENTION
SEGMENT's OWN ROUNDS" (K5), AS THAT MEMBER STANDS IN A CHAIN's FLAT LIST: the kind's decision inside
its two wrappers (a refusal at a mark behind the decision; a test that the reply is as it was in
front). A definition, and statements with their proofs.

Why. Johnson/Desc/K5/Honest/Law/ShapeK5.lean has the kind's own decision as one Bool and one update,
with two laws. The two forms of Honest/Thread/Shape.lean speak of a member's step and decide.
Between them lie: the step's test on the rounds against the shape that the hearing reads, at the
rounds without the sealed digest; the two wrappers; the test on the plan.

Main names:
  k5Z, k5Z_ok    the cut's letters for the kind: the shape of five readers, the one Bool and the one
                 update, no test on values
  k5_carries_member, k5_returns_member   **Carries and Returns at the member**: GENERAL IN THE LIST
    OF MEMBERS
  k5_shape_at_head   both at the kind's member of a group of the proof file's own flat list
  k5G_at_thr     the Bool says yes wherever the first chain's thread stands in front of the kind's
    member

Conditional on: the two at the member: blk is the member number b, and it decides as the kind's
decision with the two tests more (DecidesAs, Honest/K5/Law/Member.lean, which also holds its rounds
and the test on the plan). k5_shape_at_head: the hypothesis on the public input (P5J.AtMgA,
Johnson/P5J/MgAtAll.lean), which is proved of nothing here. k5G_at_thr: that, the plan's facts, and
the thread's sentence at the border.
By step_iff (Johnson/Top/H0/StepLaws/StepLaws.lean), same_of_out (Johnson/H2K5R/SeatedStates.lean),
fits_of_roundsFit and rounds_plain (Honest/K5/Law/Plays.lean), k5_member (Law/Member.lean),
readyO_of_thr (Law/Ready.lean), k5_returns_whole (Johnson/Desc/K5/Honest/Law/Returns.lean),
k5_shape_carries, readyO_of_G (Law/ShapeK5.lean), G_of_readyO (Law/ShapeK5Yes.lean).
Whose. By the authors of the attention sub-protocol's (K5's) own rounds.
Limits. THE SHAPE IS THE KIND's OWN, OF FIVE READERS, NOT THE CHAIN's: Carries says nothing of what
the chain's shape sees beside these five. k5Z has the kind's guards at every border: so it can never
be the one shape that the rule of Honest/Thread/Shape.lean takes for a whole chain: the two laws at
the member hold at a component's letters. The like at the first chain's own shape:
Honest/K5/Law/ShapeChain.lean. The second wrapper compares two values of the reply; it wants no
entry among the tests on values because the kind's term leaves that field. Of the kind's runs of
claims nothing is said. That the thread's sentence holds at any run is not proved here.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.ShapeK5Yes
import Johnson.Desc.ProofFile.Honest.K5.Law.Accepted
import Johnson.Desc.ProofFile.Honest.Thread.Shape

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc (Block Strs Chain Claim First.S noDigest step_iff)
open VerifiableInference.Desc.First.Att.P
open H2K5.Honest (K5Sh k5Sh k5G k5Step k5_shape_carries readyO_of_G G_of_readyO k5_returns_whole)
open ProofFile.Honest.FirstThread (Script WtF)
open P5J (AtMgA TS CellsM)

/-! ## 1 General in the list of members -/

/-- **The letters of the cut "structure | values" (`Shape`, Honest/Thread/Shape.lean) for the kind's
member**: the shape of five readers (Johnson/Desc/K5/Honest/Law/ShapeK5.lean); at every border the
kind's one Bool and one update; NO TEST ON VALUES. x: the plan's numbers of the segment's rounds. A
COMPONENT's LETTERS, NOT A CHAIN's SHAPE: the rule of Honest/Thread/Shape.lean takes one shape for
the whole chain and runs its guards over all members in front; at these letters that run says no
from the first member on, where no attention link stands open. It is a definition. -/
def k5Z (x : Params.AttentionRounds) : Shape First.S where
  Sh := K5Sh
  sh := k5Sh
  g := fun _ a => if k5G x a then .ok (k5Step x a) else .error "K5.shape"
  vals := fun _ _ _ _ => true

/-- The guards' return. -/
theorem k5Z_ok {x : Params.AttentionRounds} {b : Nat} {a t : K5Sh}
    (h : (k5Z x).g b a = .ok t) : k5G x a = true ∧ t = k5Step x a := by
  have h' : (if k5G x a then Except.ok (k5Step x a) else Except.error "K5.shape") = .ok t := h
  cases e : k5G x a with
  | true =>
    rw [e] at h'
    exact ⟨rfl, (Except.ok.inj h').symm⟩
  | false =>
    rw [e] at h'
    cases h'

variable {bs : List (Block First.S Claim)} {ft b : Nat} {p : Par} {blk : Block First.S Claim}

/-- **CARRIES, AT THE MEMBER** (`Carries`, Honest/Thread/Shape.lean): where the member's own step
says yes and the guards return at the shape in front, they return the shape behind. CONDITIONAL on:
blk is the member number b; it decides as the kind's decision with the two tests more (`DecidesAs`,
Honest/K5/Law/Member.lean). -/
theorem k5_carries_member (hb : bs[b]? = some blk) (Dc : DecidesAs p blk) :
    Carries bs ft (k5Z p.own) b := by
  intro blk' hb' s rs cols s' n t hs hg
  obtain rfl : blk = blk' := Option.some.inj (hb.symm.trans hb')
  obtain ⟨hG, rfl⟩ := k5Z_ok hg
  obtain ⟨_, hd, _⟩ := (step_iff ft blk s s' rs cols n).1 hs
  exact (k5_shape_carries p ((Dc.decides _ _ _ _).1 hd).1 hG).symm

/-- **RETURNS, AT THE MEMBER** (`Returns`, Honest/Thread/Shape.lean): where the guards return at the
shape in front and the step's own tests on rounds and columns pass, the member's decide returns: the
kind's decision AND the two tests around it (no mark behind; the reply as in front): the kind's term
leaves both fields. The list of tests on values is empty. CONDITIONAL as `k5_carries_member`. -/
theorem k5_returns_member (hb : bs[b]? = some blk) (Dc : DecidesAs p blk) :
    Returns bs ft (k5Z p.own) b := by
  intro blk' hb' s rs cols t hg hF _
  obtain rfl : blk = blk' := Option.some.inj (hb.symm.trans hb')
  obtain ⟨hG, _⟩ := k5Z_ok hg
  have R := readyO_of_G p hG
  have h1 : VerifiableInference.Desc.roundsFit (rounds p) rs = true := by
    rw [← Dc.rounds]
    exact hF.1
  obtain ⟨a, hd, G, _, _, hdec, B⟩ :=
    k5_returns_whole p Dc.plan R (fits_of_roundsFit _ _ h1 (rounds_plain p))
  exact ⟨_, (Dc.decides _ _ _ _).2 ⟨hdec, B.failed.trans R.clean, same_of_out s _ B.out⟩⟩

/-! ## 2 At the library's own letters -/

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

include h in
/-- **BOTH AT THE KIND's MEMBER OF GROUP g OF THE PROOF FILE's OWN FLAT LIST.** CONDITIONAL: under
the hypothesis h, which is proved of nothing here; g is below 12; a is the plan of group g. -/
theorem k5_shape_at_head {g : Nat} (hg : g < 12) {a : Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a) (ft : Nat) :
    Carries cF.blocksInOrder ft (k5Z (parAt Zp g a).own) (borderOf g) ∧
      Returns cF.blocksInOrder ft (k5Z (parAt Zp g a).own) (borderOf g) := by
  obtain ⟨blk, a', hfl, Pl, Dc⟩ := k5_member h hg
  obtain rfl : a' = a := Option.some.inj (Pl.plan.symm.trans ha)
  exact ⟨k5_carries_member hfl Dc, k5_returns_member hfl Dc⟩

variable {Bk : ProverCoinCounts} {W₀ Rc Tr X : Type}
  (hs : List (Placed (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X))
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok
    VerifiableInference.Desc.Sound.MsgT)
  (stored : Local W₀ Rc ProofFile.Inst Tr → Nat → Nat → Option (List UInt64))
  (ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (test : Nat → TS → Option String)
  (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ : Nat)
  (valid : Local W₀ Rc ProofFile.Inst Tr → Prop) (rides : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
  (keeps : Nat → TS → TS → Prop)

/-- **THE BOOL SAYS YES AT EVERY STATE AT WHICH THE FIRST CHAIN's THREAD STANDS IN FRONT OF THE
KIND's MEMBER.** CONDITIONAL: under the hypothesis h, the plan's facts, and `Thr` at the border:
none is proved here. -/
theorem k5G_at_thr {g : Nat} (hg : g < 12) {a : Attention.Plan} (Pl : PlanAt Zp g a)
    {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hT : Thr (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) (borderOf g)
      k s m E) : k5G (parAt Zp g a).own (k5Sh s) = true := by
  exact G_of_readyO _
    (readyO_of_thr h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hg Pl hT)

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.k5Z_ok
#print axioms ProofFile.Honest.K5.k5_carries_member
#print axioms ProofFile.Honest.K5.k5_returns_member
#print axioms ProofFile.Honest.K5.k5_shape_at_head
#print axioms ProofFile.Honest.K5.k5G_at_thr
#print axioms ProofFile.Honest.K5.k5Z
