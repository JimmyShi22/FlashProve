-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/Front.lean: CONDITIONAL: what the first chain's invariant
(`Thr`, Honest/Thread/Thr.lean), at the library's own letters, hands over at the border in front of
an attention segment's own rounds (kind K5), in the library's own terms: so that the library's
lemmas on reached states and on the table's promise can be called at the state of an honest run.

  `reach_of_thr`   CONDITIONAL: the verifier's state at a border is reached in the library's sense
                   (`Reach`, Johnson/Top/H0/Walk/Reach.lean), over the chain's own flat list, from
                   the chain's own first state, at the input's public part
  `onAt_of_thr`    CONDITIONAL: at the kind's border of group g the state bears no mark of failure,
                   and the table's promise `onAt` (Johnson/Desc/First/Borders.lean) holds of it at
                   the kind's place, at the table's open sets there, at the honest letters
  `open8_k5`       eight public items are open at that border, at the closed list of extra public
                   tests

The honest letters. The meaning in `onAt_of_thr` is `honest (mgAtAll h) ans test`
(Honest/Thread/First.lean): its fields pub, pubP, held, inOrder and more are those of `mgAtAll h` by
unfolding; decodes, shown and noColl are true there.

"Reached" here is over the flat list as it stands, not over the list in which each sub-protocol
first tests that every shown word is below the prime: the second family is the narrower one.

What it is for. Laws over the library alone on what holds in front of the kind's step and behind it
can take just these three as premises.
That the border lies within the list (`reach_of_thr`'s first premise) follows wherever the list has
a member at the border. The library's decisions on the written lists, on which `open8_k5` leans
(Johnson/Desc/First/Att/Door/Law/K5ListsFull.lean), lie compiled beneath this file.

Limits. Every theorem is conditional: on the hypothesis `P5J.AtMgA`, which is not shown here, and on
`Thr` in front. Nothing shows that `Thr` holds at any run.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.Ready
import Johnson.Desc.ProofFile.Honest.Thread.MadeLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc (Block Place Strs Chain Claim First.S First.Pub)
open VerifiableInference.Desc.First (onAt openSets pubSets start leavesName)
open VerifiableInference.Desc.Sound (doorsFitB_parts)
open H2K5.Door (moreOver9)
open Johnson.Desc.First.Walk.Tied (Reach)
open ProofFile.Honest.FirstThread (Script WtF honest noStrs)
open P5J (AtMgA mgAtAll TS CellsM)

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr X : Type}
  (hs : List (Placed (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X))
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok
    VerifiableInference.Desc.Sound.MsgT)
  (stored : Local W₀ Rc ProofFile.Inst Tr → Nat → Nat → Option (List UInt64))
  (ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (test : Nat → TS → Option String)
  (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ : Nat)
  (valid : Local W₀ Rc ProofFile.Inst Tr → Prop) (rides : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
  (keeps : Nat → TS → TS → Prop)

/-- **The verifier's state at a border is reached**, over the chain's own flat list. CONDITIONAL:
under `Thr` at the border number b, which lies within the list. -/
theorem reach_of_thr {b : Nat} (hb : b ≤ cF.blocksInOrder.length) {k : Coins Bk} {s : TS}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hT : Thr (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) b k s m E) :
    Reach 0 cF.blocksInOrder (ProofFile.startS Zp) b (m.st.input.x.pub, s) :=
  reach_of_made (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) (ProofFile.startS Zp)
    m.st.input.x.pub hb (fun _ e => e) hT.2.2.2.2.1

/-- **No mark, and the table's promise at the kind's place.** CONDITIONAL: under `Thr` at the
kind's border of group g. -/
theorem onAt_of_thr {g : Nat} (hg : g < 12) {k : Coins Bk} {s : TS}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hT : Thr (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) (borderOf g)
      k s m E) :
    s.failed = none ∧
      onAt (P5J.At.N Zp cF) (honest (mgAtAll h) ans test) P5J.At.links
        (some ⟨1, some (2 * g + 1), 3, .K5⟩)
        (((openSets P5J.At.links P5J.At.ps (start P5J.At.links))[borderOf g]?).getD [])
        (((pubSets ((moreOver9 {}).strike leavesName) P5J.At.links P5J.At.ps)[borderOf g]?).getD [])
        (m.st.input.x.pub, s) noStrs := by
  obtain ⟨hf0, hon0⟩ := hT.2.2.1
  have hpl : P5J.At.ps[borderOf g]? = some ⟨1, some (2 * g + 1), 3, .K5⟩ :=
    H2K5.Door.place_full hg
  have hm : (honest (mgAtAll h) ans test).more = (moreOver9 {}).strike leavesName :=
    H2K5.Door.hm_all h
  have hon : onAt (P5J.At.N Zp cF) (honest (mgAtAll h) ans test) P5J.At.links
      (P5J.At.ps[borderOf g]?)
      (((openSets P5J.At.links P5J.At.ps (start P5J.At.links))[borderOf g]?).getD [])
      (((pubSets (honest (mgAtAll h) ans test).more P5J.At.links P5J.At.ps)[borderOf g]?).getD [])
      (m.st.input.x.pub, s) noStrs := hon0
  rw [hpl, hm] at hon
  exact ⟨Option.isNone_iff_eq_none.1 hf0, hon⟩

end

/-- **Eight public items are open at the kind's border**, at the closed list of extra public tests.
By two of the library's decisions on the written lists, as `open_k5`. CONDITIONAL: g is below 12. -/
theorem open8_k5 {g : Nat} (hg : g < 12) (q : First.Pub)
    (hq : q ∈ [First.Pub.more (some (2 * g + 1)) "K5.liveReq",
      .more (some (2 * g + 1)) "K5.readsThere", .look (2 * g + 1), .ledger (2 * g + 1),
      .freeAbove (2 * g + 1), .left (2 * g + 1), .linkFresh (2 * g + 1),
      .more (some (2 * g + 1)) "frame.sentIs"]) :
    q ∈ (pubSets ((moreOver9 {}).strike leavesName) P5J.At.links P5J.At.ps)[borderOf g]?.getD
      [] := by
  have hw : H2K5.Door.isWideQ q = false := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  have ha : q ∈ [First.Pub.more (some (2 * g + 1)) "K5.liveReq",
      .more (some (2 * g + 1)) "K5.readsThere", .look (2 * g + 1), .ledger (2 * g + 1),
      .freeAbove (2 * g + 1), .left (2 * g + 1), .more (some (2 * g + 1)) "frame.liveIs",
      .linkFresh (2 * g + 1), .more none "K12.seatsCarried", .more none "K12.msgShapes",
      .more (some (2 * g + 1)) "frame.sentIs", .more (some (2 * g + 1)) "K5.rowsBare",
      .more (some (2 * g + 1)) "K5.lookLeft", .callerIn (2 * g + 1)] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq ⊢
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  rcases (doorsFitB_parts (H2K5.Door.doors_full hg)).2.1 q (H2K5.Door.fourteen_full hg q ha) with
    h1 | h1
  · rw [hw] at h1
    cases h1
  · exact h1

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.reach_of_thr
#print axioms ProofFile.Honest.K5.onAt_of_thr
#print axioms ProofFile.Honest.K5.open8_k5
