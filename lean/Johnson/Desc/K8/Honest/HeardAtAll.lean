-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K8/Honest/HeardAtAll.lean: THE SMALLNESS TEST, THE HONEST PROVER's SIDE: OF WHAT THE
LOOKUP ON THE DIGITS HAS HEARD, AT EACH EXPECTED PIECE: THE KEY POINT OF THE PIECE's CALL HAS THE
CALL's LENGTH, AND THE CALL's WEIGHT IS THE WEIGHT COMPUTED AGAIN: AT THE 25th SEGMENT, THE OUTPUT
HEAD's, AND SO AT ALL 25: AT EVERY STATE THAT THE FIRST CHAIN's BLOCKS WITH THE TEST ON WORDS IN
FRONT (`Sound.below`) REACH IN FRONT OF A SEGMENT's BATCHING, IN THE GOALS' SCOPE, THE FILES READ,
UNDER AN OPENING OF THE DESCRIPTION AND ITS TEST ON ITS PLAN. THAT ANY SUCH STATE IS REACHED IS NOT
SHOWN. Lemmas; none of the library's goals.

  `heard_of_leaves` AT ALL 25, at a state that the chain's own blocks reach in front of the batching
                   and that shows tl: from three things (the held fields are the built segment's ·
                   `K3Left` at the state's own f9 · the first coordinate of zy has its words below
                   the prime) ⊢ for all nbW, W with tl.wants = some (nbW, W) and every w in W:
                   (g.zk.getD w.call #[]).size = (tl.zOf w.call).call.n and g.e.getD w.call zeroE =
                   callWeightAgain g w.call
  **`heard_at_head_seg`** the scope · the files read · the opening · the test on the plan · the
                   built segment number 24 · a state that the wrapped blocks reach at 347 ⊢ for
                   every tl that the state shows, every g that tl has heard, all nbW, W as above and
                   every w in W: the same two
  **`heard_at_all`** the same at l < 25, at the border 14 l + (if l = 24 then 11 else 9)
Why. The end is, sign for sign, the body of `HeardAtZ` (Johnson/P1K8R/BehindHeard.lean);
`heardAtZ_of_head` (BehindButHead.lean) takes it at l = 24 as a premise. That file is not imported:
the join is its writer's.
By: `digitsLeft_at_head_seg`, `sized_at_head_wrap`, `tl_back_over_merge`, `zy_below_behind_digits`
(Johnson/Desc/K8/Honest/AllFrontAtHeadSeg.lean) · `heard_at_wrap` (OneSentenceLeft.lean: l < 24) ·
`weights_of_below` (WeightsAtReach.lean) · `heldPub_at_batch`, `two_calls_of_tests`,
`tests_at_built`, `drawn_at_batch`, `wants_128`, which all reach l < 25.
WRITTEN A FURTHER TIME: `heard_of_leaves` is `heard_at_z`'s proof (HeardJoin.lean) with the leaf as
premises in the stead of l < 24, and with the two lines on sizes of `heardSizes_at_batch`
(HeardAtReach.lean) laid in · the ten lines of `heard_at_head_seg` that bring zy's first coordinate
are those of `allFront_at_head_seg`.
ONE DEVICE STANDS IN IT: `attribute [-instance] Inst.Model.Scl.ref`. TACTICS THAT SEARCH: `simp [a
list]` inside a term, twice · `simp only [a list]`, twice · `omega` on seven lines, on numbers of
segments, borders and calls alone.
Limits. NOTHING SAYS THAT ANY STATE IS REACHED IN FRONT OF A BATCHING: where none is, all is idle.
AT THE WRAPPED FAMILY ALONE (`Sound.below` is a device of the proof and runs nowhere);
`heard_of_leaves` speaks at the chain's own blocks' family, under premises. UNDER THE DESCRIPTION's
TEST ON ITS PLAN. IN SCOPE ALONE: the full size; the first chain. Which of the files beneath it are
rows of the library is for the library's own list to say: it is not said here. No prover stands in
it.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.K8.Honest.AllFrontAtHeadSeg

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.OnPublicFiles (K3Left)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **AT EVERY EXPECTED PIECE, FROM THE LEAVES, AT ALL 25 SEGMENTS: the size of its call's point,
and its call's weight.** -/
theorem heard_of_leaves (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 25) {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (z, s))
    {tl : HTailF2} (ht : s.tl? = some tl)
    {g : Forest.Heard} {F₀ F' : Fork} {rs : TwV.Rounds Cb.Gl.E}
    (v : heldFields tl = heldFields Xl.tl) (K : K3Left Reading.gl tl.f9 5 F₀ F' g rs)
    (hz : OnBytes.okE (g.zy.getD 0 zeroE) = true) :
    ∀ nbW W, tl.wants = some (nbW, W) → ∀ w ∈ W,
      (g.zk.getD w.call #[]).size = (tl.zOf w.call).call.n ∧
        g.e.getD w.call zeroE = callWeightAgain g w.call := by
  intro nbW W hW w hw
  have hP : heldPubB Xl.tl = true := heldPub_at_batch hS hR O hOk hl e3 h ht
  have hP' : heldPubB tl = true := by
    rw [pub_heldFields tl, v, ← pub_heldFields Xl.tl]
    exact hP
  have T := _root_.P1K8.tests_at_built hS O hl e3
  have v9 : tl.f9 = Xl.tl.f9 := congrArg (·.f9) v
  have v1 : tl.z1 = Xl.tl.z1 := congrArg (·.z1) v
  have v2 : tl.z2 = Xl.tl.z2 := congrArg (·.z2) v
  have nc : tl.f9.NC = 2 := by
    rw [v9]
    exact (two_calls_of_tests T).1
  have t4 := T.t4
  unfold _root_.Fo.callsTest at t4
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, beq_iff_eq] at t4
  obtain ⟨k0, k1⟩ := t4
  have z0 : (Xl.tl.zOf 0) = Xl.tl.z1 := rfl
  have z1 : (Xl.tl.zOf 1) = Xl.tl.z2 := rfl
  have s0 : (g.zk.getD 0 #[]).size = tl.z1.call.n := by
    rw [K.zkLen 0 (by omega), v9, k0, z0, v1]
  have s1 : (g.zk.getD 1 #[]).size = tl.z2.call.n := by
    rw [K.zkLen 1 (by omega), v9, k1, z1, v2]
  have he := weights_of_below K hP' nc hz
  obtain ⟨t, a, -, hT⟩ := _root_.P1K8.drawn_at_batch hS hR O hl h
  rw [Option.some.inj (a.symm.trans ht)] at hT
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj ((_root_.P1K8.wants_128 hT).symm.trans hW))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · exact ⟨s0, he 0 (by omega)⟩
  · exact ⟨s1, he 1 (by omega)⟩

/-- **IN FRONT OF THE HEAD's BATCHING**, at every state that the blocks with the test on words in
front reach there. -/
theorem heard_at_head_seg (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {Xl : LinkH} (e3 : Bs.G₀.built[24]? = some Xl) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) 347 (z, s)) :
    ∀ tl, s.tl? = some tl → ∀ g nbW W, tl.heard = some g → tl.wants = some (nbW, W) → ∀ w ∈ W,
      (g.zk.getD w.call #[]).size = (tl.zOf w.call).call.n ∧
        g.e.getD w.call zeroE = callWeightAgain g w.call := by
  intro tl ht g nbW W hg hW
  have hr : Reach 0 c.blocksInOrder (ProofFile.startS Z) 347 (z, s) := reach_raw h
  have h' : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * 24 + (if (24 : ℕ) = 24 then 11 else 9)) (z, s) :=
    hr
  obtain ⟨v, g₀, F₀, F', rs, hg₀, K⟩ :=
    digitsLeft_at_head_seg hS hR O hOk e3 hr (sized_at_head_wrap hS hR O hOk h) ht
  obtain rfl : g₀ = g := Option.some.inj (hg₀.symm.trans hg)
  obtain ⟨s6, r6, e6⟩ := tl_back_over_merge hS hR O h
  have zy := zy_below_behind_digits hS hR O hOk (l := 24) (by omega) r6 (e6 ▸ ht) hg
  have hz0 : OnBytes.okE (g₀.zy.getD 0 zeroE) = true := by
    by_cases hj : 0 < g₀.zy.size
    · have e : g₀.zy.getD 0 zeroE = g₀.zy[0] := by simp [Array.getD, hj]
      rw [e]
      exact zy _ (Array.getElem_mem_toList hj)
    · have e : g₀.zy.getD 0 zeroE = zeroE := by simp [Array.getD, hj]
      rw [e]
      rfl
  exact heard_of_leaves hS hR O hOk (by omega : 24 < 25) e3 h' ht v K hz0 nbW W hW

/-- **AT ALL 25 SEGMENTS.** -/
theorem heard_at_all (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 25) {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z)
      (14 * l + (if l = 24 then 11 else 9)) (z, s)) :
    ∀ tl, s.tl? = some tl → ∀ g nbW W, tl.heard = some g → tl.wants = some (nbW, W) → ∀ w ∈ W,
      (g.zk.getD w.call #[]).size = (tl.zOf w.call).call.n ∧
        g.e.getD w.call zeroE = callWeightAgain g w.call := by
  by_cases h24 : l = 24
  · subst h24
    exact heard_at_head_seg hS hR O hOk e3 h
  · rw [if_neg h24] at h
    exact heard_at_wrap hS hR O hOk (by omega) e3 h

end

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.heard_of_leaves
#print axioms VerifiableInference.Desc.First.K8.Honest.heard_at_head_seg
#print axioms VerifiableInference.Desc.First.K8.Honest.heard_at_all
