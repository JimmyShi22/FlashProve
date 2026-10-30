-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/BehindAtReach.lean: THE SMALLNESS TEST: AT EACH OF THE THREE SORTS OF SEGMENT, AT THE
SEATED BATCHING BLOCK, AT EVERY STATE THAT THE FIRST CHAIN's OWN BLOCKS REACH IN FRONT OF IT:
`SecondEqs` (Johnson/Desc/K8/Honest/SecondParts.lean) BEHIND EVERY YES, FROM WHAT IS STILL LEFT, AS
THREE STRUCTURES. UNDER THE SCOPE, THE FILES READ, IM.Open AND THE DESCRIPTION's TEST ON ITS PLAN.
Structures and lemmas; none of the library's goals. No prover stands in them; nothing on
completeness, soundness or hiding. A JOINING: NOTHING IS PAID BY THIS FILE. Why. So that what is
still open is a Lean structure, not a page.

  `StillFront Xl s tl F funs`, `StillAtt Ap s`, `StillHead h iU3 p6 s`   what is left of `FrontOwed`
      (Johnson/P1K8R/SecondAtSeat.lean), of `AttAsks` (AttApart.lean) and of the three premises
      beside it (two are left), of `HeadWants` (HeadApart.lean). Eight, four and six fields; of
      these front is `TieFront` (four clauses) and want is `PieceFront` (eleven) at every expected
      piece; static is a closed sentence on the built segment, with no state in it
  `frontOwed_at_batch`   by `secondFront_at_batch` (SecondFrontAtBatch.lean), `static_at_batch`,
      `three_of_static` (StaticAtBatch.lean)
  **`behind_reach_layers`**, **`behind_reach_att`**, **`behind_reach_head`**   `behind_seat_layers`,
      `behind_seat_att`, `behind_seat_head` (SecondAtSeat.lean) with `callsRows_layers`
      (LookAtBatch.lean), `callsRows_att`, `callsRows_head` (LookAtBatchAll.lean),
      `digitsRows_at_batch` (HeardAtBatch.lean), `u2_at_batch`, `apartAt_iU3`, `apartAt_zero`
      (ThirdTie.lean), `mergeBare_at_batch` (MergeAtBatch.lean). The built segment is there by
      IM.k1_reads_of (Johnson/IMR/K1Scope.lean)
Limits. THE THREE STRUCTURES, AND AT THE LAYERS ProofFile.Honest.K4.RunAsks, ARE SHOWN OF NO STATE HERE.
Nothing on whether any state is reached.
Terms: lean/GLOSSARY.md.
-/
import Johnson.P1K8R.SecondAtSeat
import Johnson.P1K8R.SecondFrontAtBatch
import Johnson.P1K8R.StaticAtBatch
import Johnson.P1K8R.HeardAtBatch
import Johnson.P1K8R.MergeAtBatch
import Johnson.P1K8R.ThirdTie
import Johnson.P1K8R.LookAtBatch
import Johnson.P1K8R.LookAtBatchAll
import Johnson.IMR.K1Scope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest
open OnBytes.Model.Stages (LinkH)
open Johnson.Desc.First.Walk.Tied (Reach)

/-- **What is left of `FrontOwed` (Johnson/P1K8R/SecondAtSeat.lean) at a state reached in front of a
segment's batching**: the tables are there; one closed sentence on the built segment; five of the
eleven fields of `SecondFront`; the pieces' rows lie in the digits' array. Its cEnd and leaves
speak of what the lookup on the DIGITS has heard (tl.heard). -/
structure StillFront (Xl : LinkH) (s : S) (tl : HTailF2) (F : Fork) (funs : Array HFun) : Prop where
  tables : s.funs? = some funs
  static : LinkJoin.StaticOk Xl.tl Xl.Fp
  front : TieFront tl
  row : ∀ mu, mu < tl.NM → Fo.HasRow F (tl.gtTree.getD mu 0) 0
  cEnd : ∀ g, tl.heard = some g → g.cEnd.ents.isEmpty = true
  leaves : ∀ g, tl.heard = some g → g.leaves.start.ents.isEmpty = true
  want : ∀ g nbW W, tl.heard = some g → tl.wants = some (nbW, W) → ∀ w ∈ W, PieceFront tl g w
  rows : ∀ nbW W, tl.wants = some (nbW, W) → ∀ w ∈ W,
    w.r0 + w.Rp ≤ (F.trees.getD tl.ix.ZZ {}).R

/-- What is left of `AttAsks` and of the three premises beside it: of these two are left, in the
field here. Its cEnd and leaves speak of what the lookup on the CALLS has heard (s.lookHeard?). -/
structure StillAtt (Ap : Attention.Plan) (s : S) : Prop where
  cEnd : ∀ g, s.lookHeard? = some g → g.cEnd.ents = #[]
  leaves : ∀ g, s.lookHeard? = some g → g.leaves.start.ents = #[]
  five : ∃ hd, s.heard5? = some hd ∧ K5Law.HeardPlain hd
  here : ∃ a, s.here = .att a ∧ Att.P.U3At Ap (Att.P.plannedK Ap) a.F

/-- What is left of `HeadWants`. Its cEnd and leaves speak of what the lookup on the CALLS has heard
(s.lookHeard?). -/
structure StillHead (h : Model.Head.Shape) (iU3 : Nat) (p6 : Kinds.Head.Par) (s : S) : Prop where
  cEnd : ∀ g, s.lookHeard? = some g → g.cEnd.ents = #[]
  leaves : ∀ g, s.lookHeard? = some g → g.leaves.start.ents = #[]
  digits : ∀ g, s.tl?.bind (·.heard) = some g → ∀ f ∈ g.rows.toList, f.ents = #[]
  ok : p6.ok = true
  k6 : Kinds.Head.Law.K6HeardAt h iU3 p6 s
  head : ∃ o, s.here = .head o ∧ o.opened = true ∧ PscRun.Sized o.F

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **`FrontOwed` at a reached state, from what is left of it.** -/
theorem frontOwed_at_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (z, s))
    {tl : HTailF2} {G : Fork} {funs : Array HFun} (ht : s.tl? = some tl) (hG : s.fork? = some G)
    (L : StillFront Xl s tl G funs) : FrontOwed s tl G funs := by
  obtain ⟨hb, hc, -⟩ := three_of_static (static_at_batch hS hR O hl e3 h ht hG L.static)
  exact ⟨ht, hG, L.tables, secondFront_at_batch hS hR O hl h ht hG
    ⟨L.front, L.row, hb, L.cEnd, L.leaves, L.want⟩, hc, L.rows⟩

/-- **THE LAYERS**: at the seated batching block of the segment 2 g, at every state reached in front
of it: `SecondEqs` behind every yes, from what is left. -/
theorem behind_reach_layers (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {g : ℕ} (hg : g < 12) :
    ∃ (b : Block S Claim) (p4 : OnBytes.Desc.First.K4.Par) (Xl : LinkH),
      c.blocksInOrder[28 * g + 9]? = some b ∧ LPFK9.k4ParAt Z Bs.G₀ (2 * g) = some p4 ∧
      Bs.G₀.built[2 * g]? = some Xl ∧
      ∀ (z : ProofFile.InstPub) (s : S), Reach 0 c.blocksInOrder (ProofFile.startS Z) (28 * g + 9) (z, s) →
        ∀ (tl : HTailF2) (G : Fork) (funs : Array HFun), s.tl? = some tl → s.fork? = some G →
          StillFront Xl s tl G funs → (∀ o, s.own? = some o → ProofFile.Honest.K4.RunAsks p4 o 0) →
          BehindEqs b s := by
  have n24 : ¬ 2 * g = 24 := by omega
  obtain ⟨b, p4, hb, hp, H⟩ := behind_seat_layers hS hR O (2 * g) (by omega)
    (by unfold IM.subAt; rw [if_neg n24, if_pos (by omega)])
  rw [show 14 * (2 * g) + 9 = 28 * g + 9 by omega] at hb
  obtain ⟨-, -, Xl, -, -, -, -, -, e3, -, -⟩ := IM.k1_reads_of hS hR O (2 * g) (by omega)
  refine ⟨b, p4, Xl, hb, hp, e3, fun z s h tl G funs ht hG L hown => ?_⟩
  have h' : Reach 0 c.blocksInOrder (ProofFile.startS Z)
      (14 * (2 * g) + (if 2 * g = 24 then 11 else 9)) (z, s) := by
    rw [if_neg n24, show 14 * (2 * g) + 9 = 28 * g + 9 by omega]
    exact h
  have h9 : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * (2 * g) + 9) (z, s) := by
    rw [show 14 * (2 * g) + 9 = 28 * g + 9 by omega]
    exact h
  obtain ⟨t1, h1, hu⟩ := u2_at_batch hS hR O (l := 2 * g) (by omega) h'
  obtain rfl : tl = t1 := Option.some.inj (ht.symm.trans h1)
  obtain ⟨k, hk, kb⟩ := callsRows_layers hS hR O hOk hg h
  obtain ⟨d, hd, db⟩ := digitsRows_at_batch hS hR O hOk (l := 2 * g) (by omega) h9
  refine H s tl G funs (frontOwed_at_batch hS hR O (by omega) e3 h' ht hG L) ⟨fun q hq => ?_,
    fun q hq => ?_, ?_⟩
  · obtain rfl : k = q := Option.some.inj (hk.symm.trans hq)
    exact kb
  · obtain rfl : d = q := Option.some.inj (hd.symm.trans hq)
    exact db
  · rw [hu]
    exact hown

/-- **ATTENTION**: the like at the segment 2 g + 1. -/
theorem behind_reach_att (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {g : ℕ} (hg : g < 12) :
    ∃ (b : Block S Claim) (Ap : Attention.Plan) (Xl : LinkH),
      c.blocksInOrder[14 * (2 * g + 1) + 9]? = some b ∧ Bs.G₀.W.A[g]? = some Ap ∧
      Bs.G₀.built[2 * g + 1]? = some Xl ∧
      ∀ (z : ProofFile.InstPub) (s : S),
        Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * (2 * g + 1) + 9) (z, s) →
        ∀ (tl : HTailF2) (G : Fork) (funs : Array HFun), s.tl? = some tl → s.fork? = some G →
          StillFront Xl s tl G funs → StillAtt Ap s → BehindEqs b s := by
  have n24 : ¬ 2 * g + 1 = 24 := by omega
  obtain ⟨b, Ap, g', hb, hgg, hA, H⟩ := behind_seat_att hS hR O (2 * g + 1) (by omega)
    (by unfold IM.subAt; rw [if_neg n24, if_neg (by omega)])
  obtain rfl : g = g' := by omega
  obtain ⟨-, -, Xl, -, -, -, -, -, e3, -, -⟩ := IM.k1_reads_of hS hR O (2 * g + 1) (by omega)
  refine ⟨b, Ap, Xl, hb, hA, e3, fun z s h tl G funs ht hG L M => ?_⟩
  have h' : Reach 0 c.blocksInOrder (ProofFile.startS Z)
      (14 * (2 * g + 1) + (if 2 * g + 1 = 24 then 11 else 9)) (z, s) := by
    rw [if_neg n24]
    exact h
  obtain ⟨k, hk, kb⟩ := callsRows_att hS hR O hOk hg h
  obtain ⟨d, hd, db⟩ := digitsRows_at_batch hS hR O hOk (l := 2 * g + 1) (by omega) h
  obtain ⟨a, ha, hU⟩ := M.here
  refine H s tl G funs a (frontOwed_at_batch hS hR O (by omega) e3 h' ht hG L)
    ⟨fun q hq => ?_, M.cEnd, M.leaves, fun q hq => ?_, M.five⟩ ha hU
    (apartAt_iU3 hS hR O (by omega) h' ht hA)
  · obtain rfl : k = q := Option.some.inj (hk.symm.trans hq)
    exact kb
  · obtain rfl : d = q := Option.some.inj (hd.symm.trans hq)
    exact db

/-- **THE HEAD**: the like at the segment 24. -/
theorem behind_reach_head (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true) :
    ∃ (b : Block S Claim) (Xl : LinkH), c.blocksInOrder[347]? = some b ∧ Bs.G₀.built[24]? = some Xl ∧
      ∀ (z : ProofFile.InstPub) (s : S), Reach 0 c.blocksInOrder (ProofFile.startS Z) 347 (z, s) →
        ∀ (tl : HTailF2) (G : Fork) (funs : Array HFun), s.tl? = some tl → s.fork? = some G →
          StillFront Xl s tl G funs →
          StillHead Bs.G₀.W.hS 0
            (Kinds.Head.parOf Bs.G₀.W.hS (Kinds.Head.Law.workAtW Bs.G₀.W)) s →
          BehindEqs b s := by
  obtain ⟨b, hb, H⟩ := behind_seat_head hS hR O
  obtain ⟨-, -, Xl, -, -, -, -, -, e3, -, -⟩ := IM.k1_reads_of hS hR O 24 (by omega)
  refine ⟨b, Xl, hb, e3, fun z s h tl G funs ht hG L M => ?_⟩
  have h' : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * 24 + (if 24 = 24 then 11 else 9)) (z, s) := h
  obtain ⟨k, hk, kb⟩ := callsRows_head hS hR O hOk h
  refine H s tl G funs (frontOwed_at_batch hS hR O (by omega) e3 h' ht hG L)
    ⟨fun q hq => ?_, M.cEnd, M.leaves, M.digits, M.ok, M.k6, M.head,
      mergeBare_at_batch hS hR O h⟩ (apartAt_zero hS hR O (by omega) h' ht)
  obtain rfl : k = q := Option.some.inj (hk.symm.trans hq)
  exact kb

end

end P1K8

#print axioms P1K8.frontOwed_at_batch
#print axioms P1K8.behind_reach_layers
#print axioms P1K8.behind_reach_att
#print axioms P1K8.behind_reach_head
#print axioms P1K8.StillFront
#print axioms P1K8.StillAtt
#print axioms P1K8.StillHead
