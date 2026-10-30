-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/BehindPaid.lean: THE SMALLNESS TEST: THE SENTENCES OF Johnson/P1K8R/BehindAtReach.lean
AND Johnson/P1K8R/BehindAtRch.lean ANEW, WITH WHAT THE FILES NAMED BELOW SHOW OF A REACHED STATE
LAID IN: AT EACH SORT OF SEGMENT, AT THE SEATED BATCHING BLOCK, AT EVERY STATE REACHED IN FRONT OF
IT: `SecondEqs` BEHIND EVERY YES, FROM A SHORTER LIST OF WHAT IS LEFT. AT BOTH FAMILIES OF
"REACHED": THE CHAIN's OWN BLOCKS (Reach) AND THE WRAPPED BLOCKS (RchAt,
Johnson/Top/H0/Walk/ReachAt.lean). UNDER THE SCOPE, THE FILES READ, IM.Open AND THE DESCRIPTION's
TEST ON ITS PLAN. Structures and lemmas; none of the library's goals. No prover stands in them;
nothing on completeness, soundness or hiding. Why. The list of what is left should be Lean's.

  `StillCore Xl tl F`   what is left at every sort: five fields. IT IS NO SENTENCE ON THE PUBLIC
      FILES: only its field static is; the other four speak of a state's data and ledger
  `StillAtt2 Ap s`   what else is left at an attention segment: two fields
  `StillHeadR h iU3 p6 s`   what else is left at the head's segment at the chain's own blocks: two
      fields. At the wrapped blocks: nothing else
  `stillFront_of_core`   `StillFront` from `StillCore`, the tables, and what the lookup on the
      digits has heard
  **`paid_reach_layers`**   the tables are there by LinkJoin.funsSkel_at_batch
      (Johnson/Desc/First/Link/Law/FunsAtBatch.lean); the digits' cEnd and leaves by
      `digitsLeft_at_batch` (Johnson/P1K8R/NamedAtBatch.lean)
  **`paid_reach_att`**   the tables by LinkJoin.attSkel_at_batch
      (Johnson/Desc/First/Link/Law/AttSkelAtBatch.lean); the digits' two as at the layers; the
      calls' cEnd and leaves by `callsLeft_att` (Johnson/P1K8R/LeftAtBatch.lean)
  **`paid_reach_head`**   the tables by LinkJoin.headSkel_at_batch
      (Johnson/Desc/First/Link/Law/HeadSkel.lean); the digits' cEnd, leaves and rows by
      `digitsHeard_head` (Johnson/P1K8R/HeadDigitsAtBatch.lean), from the field head; the calls'
      cEnd and leaves by `callsLeft_head` (NamedAtBatch.lean); the field ok by `parOk_atW`
      (BehindAtRch.lean)
  **`paid_rch_head`**   at the wrapped blocks: besides, `k6_at_rch` and `head_at_rch`
      (BehindAtRch.lean)
  `paid_rch_layers`, `paid_rch_att`   at the wrapped blocks: `paid_reach_layers`, `paid_reach_att`
      by one call (P4.reach_of_rchAt, Johnson/P4R/K6AtRchAt.lean)
Limits. A JOINING: nothing is shown here that the files named do not show. `StillCore`, `StillAtt2`
AND, AT THE LAYERS, ProofFile.Honest.K4.RunAsks ARE SHOWN OF NO STATE HERE; `StillHeadR` of the states
that the wrapped blocks reach alone (in `paid_rch_head`). The library may show more of their fields
than is laid in. The counts of fields understate what is left: front is `TieFront` (four fields),
want is `PieceFront` (eleven) at every expected piece. Nothing on whether any state is reached.
Terms: lean/GLOSSARY.md.
-/
import Johnson.P1K8R.BehindAtRch
import Johnson.P1K8R.LeftAtBatch
import Johnson.P1K8R.HeadDigitsAtBatch
import Johnson.Desc.First.Link.Law.AttSkelAtBatch
import Johnson.Desc.First.Link.Law.FunsAtBatch
import Johnson.Desc.First.Link.Law.HeadSkel

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest
open OnBytes.Model.Stages (LinkH)
open Johnson.Desc.First.Walk.Tied (Reach RchAt)

/-- **What is left on the frame at every sort of segment**: five fields, WITH NO STATE IN THEM BUT
ITS DATA AND ITS LEDGER: one closed sentence on the built segment; the ties' front; a row at each
matrix's array of symbols; `PieceFront` at every expected piece; the pieces' rows lie in the
digits' array. Only the first speaks of the public files alone: the other four speak of the data and
the ledger of a state of a run. -/
structure StillCore (Xl : LinkH) (tl : HTailF2) (F : Fork) : Prop where
  static : LinkJoin.StaticOk Xl.tl Xl.Fp
  front : TieFront tl
  row : ∀ mu, mu < tl.NM → Fo.HasRow F (tl.gtTree.getD mu 0) 0
  want : ∀ g nbW W, tl.heard = some g → tl.wants = some (nbW, W) → ∀ w ∈ W, PieceFront tl g w
  rows : ∀ nbW W, tl.wants = some (nbW, W) → ∀ w ∈ W,
    w.r0 + w.Rp ≤ (F.trees.getD tl.ix.ZZ {}).R

/-- What else is left at an attention segment. -/
structure StillAtt2 (Ap : Attention.Plan) (s : S) : Prop where
  five : ∃ hd, s.heard5? = some hd ∧ K5Law.HeardPlain hd
  here : ∃ a, s.here = .att a ∧ Att.P.U3At Ap (Att.P.plannedK Ap) a.F

/-- What else is left at the head's segment, at a state that the chain's own blocks reach. At a
state that the wrapped blocks reach both hold (`k6_at_rch`, `head_at_rch`,
Johnson/P1K8R/BehindAtRch.lean). -/
structure StillHeadR (h : Model.Head.Shape) (iU3 : Nat) (p6 : Kinds.Head.Par) (s : S) : Prop where
  k6 : Kinds.Head.Law.K6HeardAt h iU3 p6 s
  head : ∃ o, s.here = .head o ∧ o.opened = true ∧ PscRun.Sized o.F

/-- `StillFront` (Johnson/P1K8R/BehindAtReach.lean) from `StillCore`, the tables, and what the
lookup on the digits has heard. -/
theorem stillFront_of_core {Xl : LinkH} {s : S} {tl : HTailF2} {G : Fork} {funs : Array HFun}
    (ht : s.tl? = some tl) (hf : s.funs? = some funs) (K : StillCore Xl tl G)
    (hd : ∃ d, s.tl?.bind (·.heard) = some d ∧ d.cEnd.ents = #[] ∧ d.leaves.start.ents = #[]) :
    StillFront Xl s tl G funs := by
  obtain ⟨d, hd, d1, d2⟩ := hd
  have hd' : tl.heard = some d := by
    rw [ht] at hd
    exact hd
  refine ⟨hf, K.static, K.front, K.row, fun g hg => ?_, fun g hg => ?_, K.want, K.rows⟩
  · obtain rfl : d = g := Option.some.inj (hd'.symm.trans hg)
    exact Array.isEmpty_iff.mpr d1
  · obtain rfl : d = g := Option.some.inj (hd'.symm.trans hg)
    exact Array.isEmpty_iff.mpr d2

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **THE LAYERS**: `SecondEqs` behind every yes of the seated batching block of the segment 2 g, at
every state reached in front of it, from `StillCore` and ProofFile.Honest.K4.RunAsks. -/
theorem paid_reach_layers (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {g : ℕ} (hg : g < 12) :
    ∃ (b : Block S Claim) (p4 : OnBytes.Desc.First.K4.Par) (Xl : LinkH),
      c.blocksInOrder[28 * g + 9]? = some b ∧ LPFK9.k4ParAt Z Bs.G₀ (2 * g) = some p4 ∧
      Bs.G₀.built[2 * g]? = some Xl ∧
      ∀ (z : ProofFile.InstPub) (s : S), Reach 0 c.blocksInOrder (ProofFile.startS Z) (28 * g + 9) (z, s) →
        ∀ (tl : HTailF2) (G : Fork), s.tl? = some tl → s.fork? = some G → StillCore Xl tl G →
          (∀ o, s.own? = some o → ProofFile.Honest.K4.RunAsks p4 o 0) → BehindEqs b s := by
  obtain ⟨b, p4, Xl, hb, hp, e3, H⟩ := behind_reach_layers hS hR O hOk hg
  refine ⟨b, p4, Xl, hb, hp, e3, fun z s h tl G ht hG K hown => ?_⟩
  obtain ⟨funs, hf, -⟩ := LinkJoin.funsSkel_at_batch hS hR O hg h
  have h9 : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * (2 * g) + 9) (z, s) := by
    rw [show 14 * (2 * g) + 9 = 28 * g + 9 by omega]
    exact h
  exact H z s h tl G funs ht hG
    (stillFront_of_core ht hf K (digitsLeft_at_batch hS hR O hOk (l := 2 * g) (by omega) h9)) hown

/-- **ATTENTION**: the like at the segment 2 g + 1, from `StillCore` and `StillAtt2`. -/
theorem paid_reach_att (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {g : ℕ} (hg : g < 12) :
    ∃ (b : Block S Claim) (Ap : Attention.Plan) (Xl : LinkH),
      c.blocksInOrder[14 * (2 * g + 1) + 9]? = some b ∧ Bs.G₀.W.A[g]? = some Ap ∧
      Bs.G₀.built[2 * g + 1]? = some Xl ∧
      ∀ (z : ProofFile.InstPub) (s : S),
        Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * (2 * g + 1) + 9) (z, s) →
        ∀ (tl : HTailF2) (G : Fork), s.tl? = some tl → s.fork? = some G → StillCore Xl tl G →
          StillAtt2 Ap s → BehindEqs b s := by
  obtain ⟨b, Ap, Xl, hb, hA, e3, H⟩ := behind_reach_att hS hR O hOk hg
  refine ⟨b, Ap, Xl, hb, hA, e3, fun z s h tl G ht hG K M => ?_⟩
  obtain ⟨-, funs, -, hf, -⟩ := LinkJoin.attSkel_at_batch hS hR O hg h
  obtain ⟨k, hk, k1, k2⟩ := callsLeft_att hS hR O hOk hg h
  refine H z s h tl G funs ht hG
    (stillFront_of_core ht hf K
      (digitsLeft_at_batch hS hR O hOk (l := 2 * g + 1) (by omega) h))
    ⟨fun q hq => ?_, fun q hq => ?_, M.five, M.here⟩
  · obtain rfl : k = q := Option.some.inj (hk.symm.trans hq)
    exact k1
  · obtain rfl : k = q := Option.some.inj (hk.symm.trans hq)
    exact k2

/-- **THE HEAD, AT THE CHAIN's OWN BLOCKS**: from `StillCore` and `StillHeadR`. -/
theorem paid_reach_head (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true) :
    ∃ (b : Block S Claim) (Xl : LinkH), c.blocksInOrder[347]? = some b ∧ Bs.G₀.built[24]? = some Xl ∧
      ∀ (z : ProofFile.InstPub) (s : S), Reach 0 c.blocksInOrder (ProofFile.startS Z) 347 (z, s) →
        ∀ (tl : HTailF2) (G : Fork), s.tl? = some tl → s.fork? = some G → StillCore Xl tl G →
          StillHeadR Bs.G₀.W.hS 0
            (Kinds.Head.parOf Bs.G₀.W.hS (Kinds.Head.Law.workAtW Bs.G₀.W)) s →
          BehindEqs b s := by
  obtain ⟨b, Xl, hb, e3, H⟩ := behind_reach_head hS hR O hOk
  refine ⟨b, Xl, hb, e3, fun z s h tl G ht hG K M => ?_⟩
  obtain ⟨funs, -, hf, -⟩ := LinkJoin.headSkel_at_batch hS hR O h
  obtain ⟨k, hk, k1, k2⟩ := callsLeft_head hS hR O hOk h
  obtain ⟨o, ho, hop, hz⟩ := M.head
  obtain ⟨d, hd, d1, d2, d3⟩ := digitsHeard_head hS hR O hOk h
    ⟨o.F, by simp [S.fork?, ho, hop], hz⟩
  refine H z s h tl G funs ht hG (stillFront_of_core ht hf K ⟨d, hd, d1, d2⟩)
    ⟨fun q hq => ?_, fun q hq => ?_, fun q hq => ?_, parOk_atW hS hR O hOk, M.k6, M.head⟩
  · obtain rfl : k = q := Option.some.inj (hk.symm.trans hq)
    exact k1
  · obtain rfl : k = q := Option.some.inj (hk.symm.trans hq)
    exact k2
  · obtain rfl : d = q := Option.some.inj (hd.symm.trans hq)
    exact d3

/-- **THE HEAD, AT THE WRAPPED BLOCKS**: from `StillCore` alone. -/
theorem paid_rch_head (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true) :
    ∃ (b : Block S Claim) (Xl : LinkH), c.blocksInOrder[347]? = some b ∧ Bs.G₀.built[24]? = some Xl ∧
      ∀ (Str : Type) (a : (ProofFile.InstPub × S) × Str), RchAt (P4.FD Z A B c) 347 a →
        ∀ (tl : HTailF2) (G : Fork), a.1.2.tl? = some tl → a.1.2.fork? = some G →
          StillCore Xl tl G → BehindEqs b a.1.2 := by
  obtain ⟨b, Xl, hb, e3, H⟩ := paid_reach_head hS hR O hOk
  exact ⟨b, Xl, hb, e3, fun Str a h tl G ht hG K =>
    H a.1.1 a.1.2 (P4.reach_of_rchAt h) tl G ht hG K
      ⟨k6_at_rch hS hR O hOk a h, head_at_rch hS hR O hOk a h⟩⟩

/-- **THE LAYERS, AT THE WRAPPED BLOCKS**: `paid_reach_layers`, by one call. -/
theorem paid_rch_layers (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {g : ℕ} (hg : g < 12) :
    ∃ (b : Block S Claim) (p4 : OnBytes.Desc.First.K4.Par) (Xl : LinkH),
      c.blocksInOrder[28 * g + 9]? = some b ∧ LPFK9.k4ParAt Z Bs.G₀ (2 * g) = some p4 ∧
      Bs.G₀.built[2 * g]? = some Xl ∧
      ∀ (Str : Type) (a : (ProofFile.InstPub × S) × Str), RchAt (P4.FD Z A B c) (28 * g + 9) a →
        ∀ (tl : HTailF2) (G : Fork), a.1.2.tl? = some tl → a.1.2.fork? = some G →
          StillCore Xl tl G → (∀ o, a.1.2.own? = some o → ProofFile.Honest.K4.RunAsks p4 o 0) →
          BehindEqs b a.1.2 := by
  obtain ⟨b, p4, Xl, hb, hp, e3, H⟩ := paid_reach_layers hS hR O hOk hg
  exact ⟨b, p4, Xl, hb, hp, e3, fun Str a h => H a.1.1 a.1.2 (P4.reach_of_rchAt h)⟩

/-- **ATTENTION, AT THE WRAPPED BLOCKS**: `paid_reach_att`, by one call. -/
theorem paid_rch_att (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {g : ℕ} (hg : g < 12) :
    ∃ (b : Block S Claim) (Ap : Attention.Plan) (Xl : LinkH),
      c.blocksInOrder[14 * (2 * g + 1) + 9]? = some b ∧ Bs.G₀.W.A[g]? = some Ap ∧
      Bs.G₀.built[2 * g + 1]? = some Xl ∧
      ∀ (Str : Type) (a : (ProofFile.InstPub × S) × Str),
        RchAt (P4.FD Z A B c) (14 * (2 * g + 1) + 9) a →
        ∀ (tl : HTailF2) (G : Fork), a.1.2.tl? = some tl → a.1.2.fork? = some G →
          StillCore Xl tl G → StillAtt2 Ap a.1.2 → BehindEqs b a.1.2 := by
  obtain ⟨b, Ap, Xl, hb, hA, e3, H⟩ := paid_reach_att hS hR O hOk hg
  exact ⟨b, Ap, Xl, hb, hA, e3, fun Str a h => H a.1.1 a.1.2 (P4.reach_of_rchAt h)⟩

end

end P1K8

#print axioms P1K8.stillFront_of_core
#print axioms P1K8.paid_reach_layers
#print axioms P1K8.paid_reach_att
#print axioms P1K8.paid_reach_head
#print axioms P1K8.paid_rch_head
#print axioms P1K8.paid_rch_layers
#print axioms P1K8.paid_rch_att
#print axioms P1K8.StillCore
#print axioms P1K8.StillAtt2
#print axioms P1K8.StillHeadR
