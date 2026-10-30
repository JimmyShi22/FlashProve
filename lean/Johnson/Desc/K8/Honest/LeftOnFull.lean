-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K8/Honest/LeftOnFull.lean: THE SMALLNESS TEST, THE HONEST PROVER's SIDE: WHAT THE
LOOKUP ON THE DIGITS HAS LEFT, WHOLE, AT THE STATE IN FRONT OF EACH OF THE 25 BATCHINGS: WHAT WAS
HEARD STANDS AT ONE LIST OF ROUNDS, AT A LEDGER THAN WHICH THE STATE's OWN IS LATER: IN THE GOALS'
SCOPE, THE FILES READ, UNDER AN OPENING OF THE DESCRIPTION AND ITS TEST ON ITS PLAN, AT EVERY STATE
REACHED THERE. THAT ANY SUCH STATE IS REACHED IS NOT SHOWN. THE LAW IS THE LIBRARY's: calls, and
what they hand kept; none of the library's goals.

  `leftOnFull_at_batch` the four · l < 24 · the built segment Xl · Reach 0 c.blocksInOrder (ProofFile.startS Z) (14
                   l + 9) (z, s) · s.tl? = some tl · s.fork? = some G ⊢ heldFields tl = heldFields
                   Xl.tl ∧ ∃ P' g F₀ F' rs, placeAt Bs.G₀.W l true = some P' ∧ tl.heard = some g ∧
                   FoNums.ok tl.f9 = true ∧ F₀.next = P'.first ∧ K3Left Reading.gl tl.f9 5 F₀ F' g
                   rs ∧ Fo.Later F' G
  `leftOnFull_at_head_seg` the same at l = 24, at a state that the blocks with the test on words in
                   front (`Sound.below`) reach at 347
  **`heardIs_at_all`** the four · l < 25 · Xl · the wrapped blocks' reach at the segment's batching
                   · tl · G ⊢ ∃ P' g F' rs, placeAt Bs.G₀.W l true = some P' ∧ tl.heard = some g ∧
                   tl.f9 = g.shape ∧ FoNums.ok g.shape = true ∧ Fo.Later F' G ∧ HeardIs Reading.gl g
                   F' (endsOf g.shape 5 P'.first rs)
By: the library's LinkJoin.leftOn_digits_front and leftOn_digits_head
(Johnson/Desc/First/Link/Law/KxAtFront.lean), at lm := 5, whose end is `K3LeftOn`
(Johnson/Top/H/K3LeftStatement.lean: one list of rounds, the ledger left, the state's own ledger
later than it); `K3Left`'s fields heardIs and shape · the shape tied to the test's data:
`shape_at_built`, `planned_heldFields` (LeftAtReach.lean, HeldPublic.lean) with
LinkJoin.planned_at_batch · the ledger's sizes, which both laws ask: P1K8.sized_at_batch
(Johnson/P1K8R/HeardAtBatch.lean), `sized_at_head_wrap` (AllFrontAtHeadSeg.lean): it is for these
that the head's segment stands at the wrapped family.
IT OVERTAKES `left_at_batch` (LeftAtReach.lean) and `digitsLeft_at_head_seg`
(AllFrontAtHeadSeg.lean), which stay as they are: the same calls and the same first conjunct; of the
six clauses that these two drop, four are kept here: FoNums.ok · F₀.next = P'.first · the state's
own ledger (as the binder G) · Fo.Later F' G; and the place P' is handed on. THE TWO PROOFS ARE
WRITTEN A FURTHER TIME, line for line but for that. KIN IN THE LIBRARY, NOT CALLED: P5J.leftD_at
(Johnson/P5J/K09LeftD.lean) calls the same two laws at all 25, under the library's head, at the
states of the verifier's side's frame, tied to tlD.f9 by shape_of_dig
(Johnson/LPFE1R/ShapeOfDig.lean); it leaves the first slot under "there is", and stands at no reach.
WHAT IT IS FOR: four clauses of `FourFacts` (FourFacts.lean), at jLK := P'.first.
ONE DEVICE STANDS IN IT: `attribute [-instance] Inst.Model.Scl.ref`. TACTICS THAT SEARCH: `omega` on
six lines, on numbers of segments alone.
Limits. NOTHING SAYS THAT ANY STATE IS REACHED: where none is, all is idle. rs IS SOME LIST: that it
is what a prover played is not said. `K3Planes`, `K3Keys`, the ties of the letters to a witness's
data, the sizes of g.zk and the other facts of `FourFacts` are not here. IN SCOPE ALONE: the full
size; the first chain; at OnBytes.secondHashFunction. Which of the files beneath it are rows of the library is
for the library's own list to say: it is not said here. No prover stands in it.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.K8.Honest.AllFrontAtHeadSeg
import Johnson.Desc.K8.Honest.LeftAtReach

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.K8.Honest
open TwV OnBytes OnBytes.Model OnBytes.Model.HTailF2 Cb.Fo
open _root_.Fo
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.OnPublicFiles (K3Left)
open VerifiableInference.Desc.First.Look (placeAt)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **In front of the batching of a segment in front of the head's: what the lookup on the digits
has left, whole.** -/
theorem leftOnFull_at_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 24) {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + 9) (z, s)) {tl : HTailF2} {G : Fork}
    (ht : s.tl? = some tl) (hG : s.fork? = some G) :
    heldFields tl = heldFields Xl.tl ∧ ∃ (P' : First.Look.P) (g : Forest.Heard) (F₀ F' : Fork)
      (rs : TwV.Rounds Cb.Gl.E), placeAt Bs.G₀.W l true = some P' ∧ tl.heard = some g ∧
      FoNums.ok tl.f9 = true ∧ F₀.next = P'.first ∧ K3Left Reading.gl tl.f9 5 F₀ F' g rs ∧
      _root_.Fo.Later F' G := by
  have hx : (l, (if l = 24 then 5 else 4), (if l = 24 then 3 else 2)) ∈ P1K8S.stretches :=
    List.mem_map.2 ⟨l, List.mem_range.2 (by omega), rfl⟩
  have h' : Reach 0 c.blocksInOrder (ProofFile.startS Z)
      (14 * l + (if l = 24 then 5 else 4) + 3 + (if l = 24 then 3 else 2)) (z, s) := by
    rw [if_neg (by omega), if_neg (by omega)]
    exact h
  have v : heldFields tl = heldFields Xl.tl := LinkJoin.of_readTl
    (LinkJoin.planned_at_batch planned_heldFields hS hR O hx e3 (z, s) h') tl ht
  have v9 : tl.f9 = Xl.tl.f9 := congrArg (·.f9) v
  obtain ⟨P', hh, hP, hs, hok, F₀, F', G₂, g, rs, -, hn, K, hg, hG₂, hL, -⟩ :=
    LinkJoin.leftOn_digits_front hS hR O (blocks_planOk O hOk) hl h
      (_root_.P1K8.sized_at_batch hS hR O hOk hl h) 5
  have e9 : hh = tl.f9 := (shape_at_built hS hR O (by omega) e3 hP hs).trans v9.symm
  subst e9
  obtain rfl : G₂ = G := Option.some.inj (hG₂.symm.trans hG)
  refine ⟨v, P', g, F₀, F', rs, hP, ?_, hok, hn, K, hL⟩
  have hg' : s.tl?.bind (·.heard) = some g := hg
  rw [ht] at hg'
  exact hg'

/-- **The like in front of the head's segment's batching**, at the blocks with the test on words in
front. -/
theorem leftOnFull_at_head_seg (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {Xl : LinkH} (e3 : Bs.G₀.built[24]? = some Xl) {z : ProofFile.InstPub} {s : S}
    (hw : Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) 347 (z, s)) {tl : HTailF2} {G : Fork}
    (ht : s.tl? = some tl) (hG : s.fork? = some G) :
    heldFields tl = heldFields Xl.tl ∧ ∃ (P' : First.Look.P) (g : Forest.Heard) (F₀ F' : Fork)
      (rs : TwV.Rounds Cb.Gl.E), placeAt Bs.G₀.W 24 true = some P' ∧ tl.heard = some g ∧
      FoNums.ok tl.f9 = true ∧ F₀.next = P'.first ∧ K3Left Reading.gl tl.f9 5 F₀ F' g rs ∧
      _root_.Fo.Later F' G := by
  have h : Reach 0 c.blocksInOrder (ProofFile.startS Z) 347 (z, s) := reach_raw hw
  have hx : ((24, 5, 3) : ℕ × ℕ × ℕ) ∈ P1K8S.stretches :=
    List.mem_map.2 ⟨24, List.mem_range.2 (by omega), rfl⟩
  have v : heldFields tl = heldFields Xl.tl := LinkJoin.of_readTl
    (LinkJoin.planned_at_batch planned_heldFields hS hR O hx e3 (z, s) h) tl ht
  have v9 : tl.f9 = Xl.tl.f9 := congrArg (·.f9) v
  obtain ⟨P', hh, hP, hs, hok, F₀, F', G₂, g, rs, -, hn, K, hg, hG₂, hL, -⟩ :=
    LinkJoin.leftOn_digits_head hS hR O (blocks_planOk O hOk) h
      (sized_at_head_wrap hS hR O hOk hw) 5
  have e9 : hh = tl.f9 := (shape_at_built hS hR O (by omega) e3 hP hs).trans v9.symm
  subst e9
  obtain rfl : G₂ = G := Option.some.inj (hG₂.symm.trans hG)
  refine ⟨v, P', g, F₀, F', rs, hP, ?_, hok, hn, K, hL⟩
  have hg' : s.tl?.bind (·.heard) = some g := hg
  rw [ht] at hg'
  exact hg'

/-- **AT ALL 25 SEGMENTS: WHAT WAS HEARD STANDS, AT ONE LIST OF ROUNDS, AT A LEDGER THAN WHICH THE
STATE's OWN IS LATER.** -/
theorem heardIs_at_all (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 25) {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z)
      (14 * l + (if l = 24 then 11 else 9)) (z, s)) {tl : HTailF2} {G : Fork}
    (ht : s.tl? = some tl) (hG : s.fork? = some G) :
    ∃ (P' : First.Look.P) (g : Forest.Heard) (F' : Fork) (rs : TwV.Rounds Cb.Gl.E),
      placeAt Bs.G₀.W l true = some P' ∧ tl.heard = some g ∧ tl.f9 = g.shape ∧
      FoNums.ok g.shape = true ∧ _root_.Fo.Later F' G ∧
      HeardIs Reading.gl g F' (endsOf g.shape 5 P'.first rs) := by
  have key : ∃ (P' : First.Look.P) (g : Forest.Heard) (F₀ F' : Fork) (rs : TwV.Rounds Cb.Gl.E),
      placeAt Bs.G₀.W l true = some P' ∧ tl.heard = some g ∧ FoNums.ok tl.f9 = true ∧
      F₀.next = P'.first ∧ K3Left Reading.gl tl.f9 5 F₀ F' g rs ∧ _root_.Fo.Later F' G := by
    by_cases h24 : l = 24
    · subst h24
      exact (leftOnFull_at_head_seg hS hR O hOk e3 h ht hG).2
    · have r := reach_raw h
      rw [if_neg h24] at r
      exact (leftOnFull_at_batch hS hR O hOk (by omega) e3 r ht hG).2
  obtain ⟨P', g, F₀, F', rs, hP, hg, hok, hn, K, hL⟩ := key
  have e : g.shape = tl.f9 := K.shape
  refine ⟨P', g, F', rs, hP, hg, e.symm, ?_, hL, ?_⟩
  · rw [e]
    exact hok
  · rw [e, ← hn]
    exact K.heardIs

end

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.leftOnFull_at_batch
#print axioms VerifiableInference.Desc.First.K8.Honest.leftOnFull_at_head_seg
#print axioms VerifiableInference.Desc.First.K8.Honest.heardIs_at_all
