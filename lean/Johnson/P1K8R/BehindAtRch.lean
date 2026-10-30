-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/BehindAtRch.lean: THE SMALLNESS TEST: THE SENTENCES OF
Johnson/P1K8R/BehindAtReach.lean AT THE OTHER FAMILY OF "REACHED": AT THE STATES THAT THE WRAPPED
BLOCKS REACH (RchAt, Johnson/Top/H0/Walk/ReachAt.lean: each block with the test "every word shown is
below the prime" in front of its decision: Sound.below, Johnson/Desc/Sound/ChainRule.lean). THERE,
AT THE HEAD's SEGMENT, THREE MORE FIELDS OF `StillHead` HOLD. UNDER THE SCOPE, THE FILES READ,
IM.Open AND THE DESCRIPTION's TEST ON ITS PLAN. A structure and lemmas; none of the library's goals.
No prover stands in them; nothing on completeness, soundness or hiding. Why. What the wrapped blocks
reach, the chain's own blocks reach (P4.reach_of_rchAt, Johnson/P4R/K6AtRchAt.lean): so all that
BehindAtReach.lean has holds there. The library's laws on what the head has heard stand at the
wrapped family alone.

  `StillHeadW s`   what is left of `StillHead` there: three of its six fields
  `parOk_atW`   the field ok: Kinds.Head.Law.parOk_open (Johnson/Desc/Kinds/Law/K6NamesNot.lean). No
      state stands in it: it holds at both families
  **`k6_at_rch`**   the field k6: LinkJoin.k6HeardAt_347
      (Johnson/Desc/First/Link/Law/K6HeardAtBatch.lean), its array's number by
      Kinds.Head.Law.AtFold.reads_zero (Johnson/Goal/Meaning/K6SeatsScope.lean); the bits of work
      are one text under two names (P4.work_is, Johnson/Desc/Kinds/Law/K6StateAtHead.lean)
  **`head_at_rch`**   the field head: LinkJoin.frontLater_back_head, alikeFront_of_later
      (K6HeardAtBatch.lean), P4.heard_342 (Johnson/P4R/Head342.lean). ITS PROOF IS THAT OF
      LinkJoin.k6HeardAt_347, ALL BUT THAT PROOF's LAST LINE, WRITTEN A FURTHER TIME (sixteen lines
      there), then three lines of its own: that law's statement does not hand what its proof shows
      on the way. With it a ledger is open at such a state
  **`behind_rch_head`**, `behind_rch_layers`, `behind_rch_att`   `behind_reach_head` with the three;
      the other two are `behind_reach_layers`, `behind_reach_att` by one call: nothing more holds
      there
Limits. `StillFront`, `StillHeadW`, `StillAtt`, AND AT THE LAYERS ProofFile.Honest.K4.RunAsks, ARE SHOWN
OF NO STATE HERE. Whoever spends these sentences must show its states reached by the wrapped blocks.
Nothing on whether any state is reached.
Terms: lean/GLOSSARY.md.
-/
import Johnson.P1K8R.BehindAtReach
import Johnson.Desc.First.Link.Law.K6HeardAtBatch
import Johnson.Desc.Kinds.Law.K6NamesNot
import Johnson.Goal.Meaning.K6SeatsScope
import Johnson.P4R.Head342
import Johnson.P4R.K6AtRchAt
import Johnson.Top.H0.Walk.ReachAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest
open OnBytes.Model.Stages (LinkH)
open Johnson.Desc.First.Walk.Tied (Reach RchAt)

/-- **What is left of `StillHead` (Johnson/P1K8R/BehindAtReach.lean) at a state that the WRAPPED
blocks reach in front of the head's batching**: three of its six fields. Its cEnd and leaves speak
of what the lookup on the CALLS has heard; its digits of what the lookup on the DIGITS has. -/
structure StillHeadW (s : S) : Prop where
  cEnd : ∀ g, s.lookHeard? = some g → g.cEnd.ents = #[]
  leaves : ∀ g, s.lookHeard? = some g → g.leaves.start.ents = #[]
  digits : ∀ g, s.tl?.bind (·.heard) = some g → ∀ f ∈ g.rows.toList, f.ents = #[]

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **The head's own test on its plan says yes**, at the letters of `behind_seat_head`. No state
stands in it. -/
theorem parOk_atW (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true) :
    (Kinds.Head.parOf Bs.G₀.W.hS (Kinds.Head.Law.workAtW Bs.G₀.W)).ok = true :=
  Kinds.Head.Law.parOk_open hS hR O hOk

/-- **What the head has heard is read back at every state that the wrapped blocks reach in front of
the head's batching**, at the letters of `behind_seat_head`: LinkJoin.k6HeardAt_347
(Johnson/Desc/First/Link/Law/K6HeardAtBatch.lean) across the two seams: the array's number by
Kinds.Head.Law.AtFold.reads_zero (Johnson/Goal/Meaning/K6SeatsScope.lean); the bits of work are one
text under two names (P4.work_is, Johnson/Desc/Kinds/Law/K6StateAtHead.lean). -/
theorem k6_at_rch {Str : Type} (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    (a : (ProofFile.InstPub × S) × Str) (h : RchAt (P4.FD Z A B c) 347 a) :
    Kinds.Head.Law.K6HeardAt Bs.G₀.W.hS 0
      (Kinds.Head.parOf Bs.G₀.W.hS (Kinds.Head.Law.workAtW Bs.G₀.W)) a.1.2 := by
  have k := LinkJoin.k6HeardAt_347 hS hR O hOk a h
  rw [Kinds.Head.Law.AtFold.reads_zero O.public] at k
  exact k

/-- **Such a state stands in the head's segment, opened, and its ledger has its sizes.** The proof
is that of LinkJoin.k6HeardAt_347, all but its last line, written a further time; then three
lines. -/
theorem head_at_rch {Str : Type} (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    (a : (ProofFile.InstPub × S) × Str) (h : RchAt (P4.FD Z A B c) 347 a) :
    ∃ o, a.1.2.here = .head o ∧ o.opened = true ∧ PscRun.Sized o.F := by
  have h' : Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) 347 (a.1.1, a.1.2) := h
  have hp : ∀ b ∈ c.blocksInOrder, b.planOk = true := by
    have e := O.desc
    subst e
    exact (Keeps.planOk_blocks _ hOk).1
  obtain ⟨s, o, r, ho, hop, q⟩ := LinkJoin.frontLater_back_head hS hR O hp h'
  have k : Kinds.Head.Law.K6HeardAt Bs.G₀.W.hS (Kinds.Head.Law.readsOf Bs.G₀.W)
      (Kinds.Head.parOf Bs.G₀.W.hS (Kinds.Head.Law.workOf Bs.G₀.W)) s :=
    P4.heard_342 hS hR O hOk (Str := Unit) ((a.1.1, s), ()) r
  have hz : PscRun.Sized o.F := by
    obtain ⟨g, H, F0, G, rs, _, _, hW, hh, hL⟩ := k
    have e : (Kinds.Head.seatAt Bs.G₀.W.hS (Kinds.Head.Law.readsOf Bs.G₀.W)).ledger s = o.F := by
      show s.fork?.getD {} = o.F
      simp [S.fork?, ho, hop]
    rw [e] at hL
    exact Kinds.Head.Law.sized_of_wellLaid (Kinds.Head.Law.Came.wellLaid_later
      (Kinds.Head.Law.Came.wellLaid_later hW (Kinds.Head.Law.keeps_hear _ _ _ _ _ hh)) hL)
  obtain ⟨o1, o', h1, h2, -, -, e3, -, -, -, hL⟩ := LinkJoin.alikeFront_of_later q ho hop hz
  obtain rfl : o = o1 := Here.head.inj (ho.symm.trans h1)
  exact ⟨o', h2, e3.trans hop, hL.sized hz⟩

/-- **THE HEAD, AT THE WRAPPED FAMILY**: at the seated batching block, at every state that the
wrapped blocks reach in front of it: `SecondEqs` behind every yes, from `StillFront` and three
fields. -/
theorem behind_rch_head (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true) :
    ∃ (b : Block S Claim) (Xl : LinkH), c.blocksInOrder[347]? = some b ∧ Bs.G₀.built[24]? = some Xl ∧
      ∀ (Str : Type) (a : (ProofFile.InstPub × S) × Str), RchAt (P4.FD Z A B c) 347 a →
        ∀ (tl : HTailF2) (G : Fork) (funs : Array HFun), a.1.2.tl? = some tl →
          a.1.2.fork? = some G → StillFront Xl a.1.2 tl G funs → StillHeadW a.1.2 →
          BehindEqs b a.1.2 := by
  obtain ⟨b, Xl, hb, e3, H⟩ := behind_reach_head hS hR O hOk
  exact ⟨b, Xl, hb, e3, fun Str a h tl G funs ht hG L M =>
    H a.1.1 a.1.2 (P4.reach_of_rchAt h) tl G funs ht hG L
      ⟨M.cEnd, M.leaves, M.digits, parOk_atW hS hR O hOk, k6_at_rch hS hR O hOk a h,
        head_at_rch hS hR O hOk a h⟩⟩

/-- **THE LAYERS, AT THE WRAPPED FAMILY**: `behind_reach_layers`, by one call. -/
theorem behind_rch_layers (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {g : ℕ} (hg : g < 12) :
    ∃ (b : Block S Claim) (p4 : OnBytes.Desc.First.K4.Par) (Xl : LinkH),
      c.blocksInOrder[28 * g + 9]? = some b ∧ LPFK9.k4ParAt Z Bs.G₀ (2 * g) = some p4 ∧
      Bs.G₀.built[2 * g]? = some Xl ∧
      ∀ (Str : Type) (a : (ProofFile.InstPub × S) × Str), RchAt (P4.FD Z A B c) (28 * g + 9) a →
        ∀ (tl : HTailF2) (G : Fork) (funs : Array HFun), a.1.2.tl? = some tl →
          a.1.2.fork? = some G → StillFront Xl a.1.2 tl G funs →
          (∀ o, a.1.2.own? = some o → ProofFile.Honest.K4.RunAsks p4 o 0) → BehindEqs b a.1.2 := by
  obtain ⟨b, p4, Xl, hb, hp, e3, H⟩ := behind_reach_layers hS hR O hOk hg
  exact ⟨b, p4, Xl, hb, hp, e3, fun Str a h => H a.1.1 a.1.2 (P4.reach_of_rchAt h)⟩

/-- **ATTENTION, AT THE WRAPPED FAMILY**: `behind_reach_att`, by one call. -/
theorem behind_rch_att (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {g : ℕ} (hg : g < 12) :
    ∃ (b : Block S Claim) (Ap : Attention.Plan) (Xl : LinkH),
      c.blocksInOrder[14 * (2 * g + 1) + 9]? = some b ∧ Bs.G₀.W.A[g]? = some Ap ∧
      Bs.G₀.built[2 * g + 1]? = some Xl ∧
      ∀ (Str : Type) (a : (ProofFile.InstPub × S) × Str),
        RchAt (P4.FD Z A B c) (14 * (2 * g + 1) + 9) a →
        ∀ (tl : HTailF2) (G : Fork) (funs : Array HFun), a.1.2.tl? = some tl →
          a.1.2.fork? = some G → StillFront Xl a.1.2 tl G funs → StillAtt Ap a.1.2 →
          BehindEqs b a.1.2 := by
  obtain ⟨b, Ap, Xl, hb, hA, e3, H⟩ := behind_reach_att hS hR O hOk hg
  exact ⟨b, Ap, Xl, hb, hA, e3, fun Str a h => H a.1.1 a.1.2 (P4.reach_of_rchAt h)⟩

end

end P1K8

#print axioms P1K8.parOk_atW
#print axioms P1K8.k6_at_rch
#print axioms P1K8.head_at_rch
#print axioms P1K8.behind_rch_head
#print axioms P1K8.behind_rch_layers
#print axioms P1K8.behind_rch_att
#print axioms P1K8.StillHeadW
