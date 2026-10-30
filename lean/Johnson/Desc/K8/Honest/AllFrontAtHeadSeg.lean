-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K8/Honest/AllFrontAtHeadSeg.lean: THE SMALLNESS TEST, THE HONEST PROVER's SIDE:
`AllFront` (Johnson/Desc/K8/Honest/LeftAtLink.lean) AT THE 25th SEGMENT, THE OUTPUT HEAD's: AT EVERY
STATE THAT THE FIRST CHAIN's BLOCKS WITH THE TEST ON WORDS IN FRONT (`Sound.below`) REACH IN FRONT
OF THE HEAD's BATCHING (BORDER 347), IN THE GOALS' SCOPE, THE FILES READ, UNDER AN OPENING OF THE
DESCRIPTION AND ITS TEST ON ITS PLAN. THAT ANY SUCH STATE IS REACHED IS NOT SHOWN. Lemmas; none of
the library's goals.

  **`allFront_of_leaves`** AT ALL 25 SEGMENTS, at a state that the chain's own blocks reach in front
                   of the batching and that shows tl and G: from six things: the held fields are the
                   built segment's · what the lookup on the digits has heard stands in the library's
                   promise (`K3Left`, at the state's own f9) · its forms cEnd and leaves.start name
                   no entry · the first coordinate of zy has its words below the prime · the digits'
                   array bears its name ⊢ there are nbW, Wn with AllFront tl G g nbW Wn
  `sized_at_head_wrap` at a state that the wrapped blocks reach at 347 a ledger is open, with its
                   sizes
  `digitsLeft_at_head_seg` at a state that the chain's own blocks reach at 347, where a ledger is
                   open with its sizes: the first two of the six
  `zy_below_behind_digits` AT ALL 25, at a state that the wrapped blocks reach right behind the
                   lookup on the digits (border 14 l + IM.k3Ix l true + 2 + 1: 14 l + 9 at l < 24;
                   346 at the head's): every coordinate of zy has its words below the prime
  `tl_back_over_merge` at a state s reached at 347: THERE IS a state reached at 346, at the same z,
                   with the same data of the test. That it is the state one block in front of s is
                   not said. Two calls of the library's laws
  **`allFront_at_head_seg`** the scope · the files read · the opening · the test on the plan · the
                   built segment number 24 · a state that the wrapped blocks reach at 347 ⊢ there
                   are tl, G, g, nbW, Wn with s.tl? = some tl, s.fork? = some G, tl.heard = some g
                   and AllFront tl G g nbW Wn
WHY THE HEAD's SEGMENT WANTED A FILE OF ITS OWN. At l < 24 the state in front of the batching is the
one right behind the lookup on the digits, and the library has the ledger's sizes from the front
(OnPublicFiles.sized_upTo). At the head's one block more, the merge (number 346), stands between, and that
law does not reach.
By: `head_at_rch` (Johnson/P1K8R/BehindAtRch.lean) · `digitsHeard_head` (HeadDigitsAtBatch.lean) ·
`drawn_at_batch` · the library's LinkJoin.leftOn_digits_head
(Johnson/Desc/First/Link/Law/KxAtFront.lean), LinkJoin.backB_of (K6HeardAtBatch.lean: one block back
along the wrapped list, general in a relation), MergeLaw.merge_leaves_tl
(Johnson/Top/H0/MergeLaw/LeavesTl.lean: the merge's block leaves S.tl?), IM.k11_of, IM.k3_of,
`Sound.below_yes`, `reach_pred`, `reach_raw` · `zy_behind_digits` (ZyBelowAtWrap.lean) ·
`zzName_at_batch` (NamesAtBatch.lean) · `heldPub_at_batch`, `six_of_heard`, `leftOver_of_six`,
`allFront_at_batch`, `pointsHeld_of_weights`, `weights_of_below`, `shape_at_built`, which all reach
l < 25.
WRITTEN A FURTHER TIME: `allFront_of_leaves` gathers the proofs of `heardSizes_at_batch`
(HeardAtReach.lean), `pointsHeld_at_batch` (WeightsAtReach.lean) and the calls of `allFront_of_six`
| `_heard` | `_three` | `_below` | `_two`, with the two leaves as premises in the stead of l < 24 ·
`digitsLeft_at_head_seg` is `left_at_batch`'s proof (LeftAtReach.lean) at the library's law for the
head's · `zy_below_behind_digits` is `zy_below_at_wrap`'s proof (ZyBelowAtWrap.lean), less its first
step: it holds that theorem as the case l < 24; its walk one block back is `backB_of`'s, which
cannot be called here: that law throws away the yes of the test on words, and just that yes is
wanted.
KIN, AND FIRST: that the words of every coordinate of zy lie below the prime where the rounds'
sampled words do is shown, on another road (the structure that the challenges alone make), behind an
accepting step of the member at the lookup on the digits, at all 25 segments, under the library's
`P5J.AtMgA` and one premise more, in Johnson/Desc/ProofFile/Honest/K3/Law/Thread/DigitsPointsAt.lean
(`digits_points_link`, `ok_zy_at`, `ok_layBack`), which the library may not hold.
`zy_below_behind_digits` speaks at all 25 too: where both stand in one tree, one should be weighed
against the other.
ONE DEVICE STANDS IN IT: `attribute [-instance] Inst.Model.Scl.ref`. TACTICS THAT SEARCH: one bare
`simp` (in `zy_below_behind_digits`, as in `zy_below_at_wrap`) · `simp [a list]` inside a term,
thrice · `simp only [a list]`, once · `omega` on twelve lines, on numbers of segments, borders and
sizes alone.
Limits. NOTHING SAYS THAT ANY STATE IS REACHED AT 347: where none is, all is idle. AT THE WRAPPED
FAMILY ALONE (`Sound.below` is a device of the proof and runs nowhere): both the ledger's sizes
(`head_at_rch`) and zy's words are had there alone; `allFront_of_leaves` and
`digitsLeft_at_head_seg` speak at the chain's own blocks' family, under premises. UNDER THE
DESCRIPTION's TEST ON ITS PLAN. IN SCOPE ALONE: the full size; the first chain. Which of the files
beneath it are rows of the library is for the library's own list to say: it is not said here. No
prover stands in it.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.K8.Honest.NamesAtBatch
import Johnson.P1K8R.BehindAtRch
import Johnson.P1K8R.HeadDigitsAtBatch
import Johnson.Top.H0.MergeLaw.LeavesTl
import Johnson.Desc.First.Link.Law.K6HeardAtBatch

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.OnPublicFiles (K3Left okRoundsE)
open VerifiableInference.Desc.LinkJoin (piece_digits)
open Johnson.Desc.First.Walk.Tied (Reach StepYes stepYes_decide reach_raw RchAt)
open OnBytes.Road.K4 (reach_pred)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **FROM THE TWO LEAVES, AT ALL 25 SEGMENTS**: what the lookup on the digits has heard stands in
the library's promise; two of its forms name no entry; the first coordinate of zy has its words
below the prime; the digits' array bears its name. -/
theorem allFront_of_leaves (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 25) {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (z, s))
    {tl : HTailF2} {G : Fork} (ht : s.tl? = some tl) (hG : s.fork? = some G)
    {g : Forest.Heard} {F₀ F' : Fork} {rs : TwV.Rounds Cb.Gl.E}
    (v : heldFields tl = heldFields Xl.tl) (K : K3Left Reading.gl tl.f9 5 F₀ F' g rs)
    (h1 : g.cEnd.ents.isEmpty = true) (h2 : g.leaves.start.ents.isEmpty = true)
    (hz : OnBytes.okE (g.zy.getD 0 zeroE) = true)
    (hn : (G.trees.getD tl.ix.ZZ {}).name = "ZZ") :
    ∃ (nbW : Nat) (Wn : List Want), AllFront tl G g nbW Wn := by
  have hP : heldPubB Xl.tl = true := heldPub_at_batch hS hR O hOk hl e3 h ht
  have hP' : heldPubB tl = true := by
    rw [pub_heldFields tl, v, ← pub_heldFields Xl.tl]
    exact hP
  obtain ⟨n1, n2⟩ := pub_numbers hP'
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
  have hZ : HeardSizes tl g := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [K.zy, n2]
    · rw [K.zx, n1]
    · rw [K.eRaw, Array.size_map, Array.size_range, nc]
    · rw [K.zkLen 0 (by omega), v9, k0, z0, v1]
    · rw [K.zkLen 1 (by omega), v9, k1, z1, v2]
  have b0 : g.zb0.size = 5 + (tl.f9.kT + tl.f9.cK) := by
    rw [K.zb_size.1]
    omega
  have b1 : g.zb1.size = 5 + (tl.f9.kT + tl.f9.cK) := by
    rw [K.zb_size.2]
    omega
  have hp : tl.pointsHeld g = true :=
    pointsHeld_of_weights K hP' nc (weights_of_below K hP' nc hz)
  exact allFront_at_batch hS hR O hOk hl e3 h ht hG
    (leftOver_of_six hS hR O hl e3 h ht
      (six_of_heard hS hR O hl e3 h ht hP ⟨b0, b1, hZ, hp, hn⟩) h1 h2)

/-- At a state that the wrapped blocks reach in front of the head's batching a ledger is open, with
its sizes. -/
theorem sized_at_head_wrap (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) 347 (z, s)) :
    ∃ G, s.fork? = some G ∧ PscRun.Sized G := by
  obtain ⟨o, ho, hop, hz⟩ := _root_.P1K8.head_at_rch hS hR O hOk (Str := Unit) ((z, s), ()) h
  have ho' : s.here = .head o := ho
  exact ⟨o.F, by simp [S.fork?, ho', hop], hz⟩

/-- **What the lookup on the digits heard stands in the library's promise, at the state's own f9,
in front of the head's batching**, where a ledger is open with its sizes. -/
theorem digitsLeft_at_head_seg (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {Xl : LinkH} (e3 : Bs.G₀.built[24]? = some Xl) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) 347 (z, s))
    (hB : ∃ G', s.fork? = some G' ∧ PscRun.Sized G') {tl : HTailF2} (ht : s.tl? = some tl) :
    heldFields tl = heldFields Xl.tl ∧ ∃ (g : Forest.Heard) (F₀ F' : Fork)
      (rs : TwV.Rounds Cb.Gl.E), tl.heard = some g ∧ K3Left Reading.gl tl.f9 5 F₀ F' g rs := by
  have hx : ((24, 5, 3) : ℕ × ℕ × ℕ) ∈ P1K8S.stretches :=
    List.mem_map.2 ⟨24, List.mem_range.2 (by omega), rfl⟩
  have v : heldFields tl = heldFields Xl.tl := LinkJoin.of_readTl
    (LinkJoin.planned_at_batch planned_heldFields hS hR O hx e3 (z, s) h) tl ht
  have v9 : tl.f9 = Xl.tl.f9 := congrArg (·.f9) v
  obtain ⟨P', hh, hP, hs, -, F₀, F', G, g, rs, -, -, K, hg, -, -, -⟩ :=
    LinkJoin.leftOn_digits_head hS hR O (blocks_planOk O hOk) h hB 5
  have e9 : hh = tl.f9 := (shape_at_built hS hR O (by omega) e3 hP hs).trans v9.symm
  subst e9
  refine ⟨v, g, F₀, F', rs, ?_, K⟩
  have hg' : s.tl?.bind (·.heard) = some g := hg
  rw [ht] at hg'
  exact hg'

/-- **Behind the lookup on the digits, at all 25 segments, at the wrapped family**: every coordinate
of zy has its words below the prime. -/
theorem zy_below_behind_digits (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 25) {z : ProofFile.InstPub} {s : S}
    (h1 : Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z)
      (14 * l + IM.k3Ix l true + 2 + 1) (z, s)) {tl : HTailF2}
    {g : Forest.Heard} (ht : s.tl? = some tl) (hg : tl.heard = some g) :
    ∀ x ∈ g.zy.toList, OnBytes.okE x = true := by
  have hp := blocks_planOk O hOk
  obtain ⟨Lk, b, b', e1, e2, e3, e4⟩ := IM.k3_of hS hR O l hl true
  obtain ⟨z', s₀, s'', b₀, e, hr, hb, hy⟩ := reach_pred h1
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
  have hf : c.blocksInOrder[14 * l + IM.k3Ix l true + 2]? = some b := by
    rw [← IM.flatIx_scope hS hR O (by omega : l ≤ 24) (IM.k3Ix l true)]
    exact IM.hear_at_flat e1 e2
  rw [List.getElem?_map, hf] at hb
  obtain rfl : Sound.below b = b₀ := Option.some.inj hb
  obtain ⟨rs, gs, hd⟩ := stepYes_decide hy
  obtain ⟨hv, hd₀⟩ := Sound.below_yes b _ _ _ _ hd
  have hw : okRoundsE rs = true := Sound.okWords_of_view _ hv
  have hd' := ((IM.yes_alone e4 (fun h => nomatch h) s₀ _ rs gs).1 hd₀).1
  have hOk' : b'.planOk = true := by
    rw [← IM.alone_planOk e4]
    exact hp b (List.mem_of_getElem? hf)
  have h7 : 7 ≤ (IM.k3Place l true).piece := by
    show 7 ≤ (if true = true then 6 else 1) + (if l = 24 then 1 else 0) + 1
    simp
  have hpc := piece_digits _ _ _ _ _ _ b' e3 l rfl h7
  obtain ⟨g', hg', hz⟩ := zy_behind_digits _ _ _ _ _ _ b' e3 hOk' l rfl hpc s₀ _ rs gs hd' hw
  rw [ht] at hg'
  obtain rfl : g = g' := Option.some.inj (hg.symm.trans hg')
  exact hz

/-- Over the merge: there is a state reached at 346, at the same z, with the test's data of s. That
it is the state one wrapped block in front of s is not in the statement. -/
theorem tl_back_over_merge (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) 347 (z, s)) :
    ∃ s6, Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) 346 (z, s6) ∧ s.tl? = s6.tl? := by
  obtain ⟨Lk, b, e1, e2, e4, -⟩ := IM.k11_of hS hR O
  exact LinkJoin.backB_of (R := fun u t => t.tl? = u.tl?) hS hR O (l := 24) (i := 8) (by omega)
    e1 e2 e4 (fun h => nomatch h) (fun u rs gs t hd => MergeLaw.merge_leaves_tl _ u rs gs t hd) h

/-- **`AllFront` IN FRONT OF THE HEAD's BATCHING**, at every state that the blocks with the test on
words in front reach there. -/
theorem allFront_at_head_seg (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {Xl : LinkH} (e3 : Bs.G₀.built[24]? = some Xl) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) 347 (z, s)) :
    ∃ (tl : HTailF2) (G : Fork) (g : Forest.Heard) (nbW : Nat) (Wn : List Want),
      s.tl? = some tl ∧ s.fork? = some G ∧ tl.heard = some g ∧ AllFront tl G g nbW Wn := by
  have hr : Reach 0 c.blocksInOrder (ProofFile.startS Z) 347 (z, s) := reach_raw h
  have h' : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * 24 + (if (24 : ℕ) = 24 then 11 else 9)) (z, s) :=
    hr
  obtain ⟨G, hG, hz⟩ := sized_at_head_wrap hS hR O hOk h
  obtain ⟨tl, ht, -, -⟩ := _root_.P1K8.drawn_at_batch hS hR O (by omega : 24 < 25) h'
  obtain ⟨v, g, F₀, F', rs, hg, K⟩ := digitsLeft_at_head_seg hS hR O hOk e3 hr ⟨G, hG, hz⟩ ht
  obtain ⟨g', hg', c1, c2, -⟩ := _root_.P1K8.digitsHeard_head hS hR O hOk hr ⟨G, hG, hz⟩
  rw [ht] at hg'
  obtain rfl : g = g' := Option.some.inj (hg.symm.trans hg')
  obtain ⟨s6, r6, e6⟩ := tl_back_over_merge hS hR O h
  have zy := zy_below_behind_digits hS hR O hOk (l := 24) (by omega) r6 (e6 ▸ ht) hg
  have hz0 : OnBytes.okE (g.zy.getD 0 zeroE) = true := by
    by_cases hj : 0 < g.zy.size
    · have e : g.zy.getD 0 zeroE = g.zy[0] := by simp [Array.getD, hj]
      rw [e]
      exact zy _ (Array.getElem_mem_toList hj)
    · have e : g.zy.getD 0 zeroE = zeroE := by simp [Array.getD, hj]
      rw [e]
      rfl
  obtain ⟨nbW, Wn, a⟩ := allFront_of_leaves hS hR O hOk (by omega : 24 < 25) e3 h' ht hG v K
    (by rw [c1]; rfl) (by rw [c2]; rfl) hz0
    (zzName_at_batch hS hR O (by omega : 24 < 25) e3 h' ht hG)
  exact ⟨tl, G, g, nbW, Wn, ht, hG, hg, a⟩

end

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.allFront_of_leaves
#print axioms VerifiableInference.Desc.First.K8.Honest.sized_at_head_wrap
#print axioms VerifiableInference.Desc.First.K8.Honest.digitsLeft_at_head_seg
#print axioms VerifiableInference.Desc.First.K8.Honest.zy_below_behind_digits
#print axioms VerifiableInference.Desc.First.K8.Honest.tl_back_over_merge
#print axioms VerifiableInference.Desc.First.K8.Honest.allFront_at_head_seg
