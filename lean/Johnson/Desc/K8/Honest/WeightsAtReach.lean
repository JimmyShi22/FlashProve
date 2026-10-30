-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/WeightsAtReach.lean: THE SMALLNESS TEST: THE VERIFIER's TEST `pointsHeld`
(OnBytes/Model/Tail.lean), AND SO `AllFront` (Johnson/Desc/K8/Honest/LeftAtLink.lean), AT EVERY
STATE THAT THE FIRST CHAIN's OWN BLOCKS REACH IN FRONT OF THE BATCHING OF ONE OF THE 24 SEGMENTS IN
FRONT OF THE HEAD's, IN THE GOALS' SCOPE, FROM: ONE PUBLIC TEST WITH CODE AT THE BUILT SEGMENT's
DATA · THE WORDS OF ONE COORDINATE OF THE LOOKUP's KEY POINT LIE BELOW THE PRIME · THE NAME OF THE
DIGITS' ARRAY. Lemmas; none of the library's goals.

  `one_mul_below`   1 times an element whose words lie below the prime is that element, as words
  `at_range`   an entry of a table made over a range
  `pub_first`   the public test ⊢ f9.first = #[0, 2 ^ io]
  `weights_raw` at a shape of two calls with rK = io + 1 · iota = #[io, io] · first = #[0, 2 ^ io]:
                   the lookup's two weights at zy are 1 - zy_0 and zy_0, as words, where zy_0's
                   words lie below the prime
  **`weights_of_below`** K3Left … tl.f9 … g · the public test · two calls · that sentence on zy_0 ⊢
                   each call's weight is the second computation's
  **`pointsHeld_at_batch`**   so pointsHeld tl g = true at a reached state, l < 24
  **`allFront_of_below`** what the lookup heard is there; and that sentence · the name "ZZ" at it ⊢
                   there are nbW, Wn with AllFront tl G g nbW Wn
WRITTEN A FURTHER TIME: `one_mul_below`, `at_range` and the two halves of `weights_raw` are another
file's `one_mul_ok`, `getD_map_range` and the lines e0 | e1' of its `pointsHeld_of`
(Johnson/Desc/ProofFile/Honest/K3/Law/DigitsPoints.lean: no part of the library), with the shape
and the point as letters.
By: `left_at_batch` (Johnson/Desc/K8/Honest/LeftAtReach.lean) · `pointsHeld_of_weights`
(PointsAtReach.lean) · `allFront_of_three` (HeardAtReach.lean) · the library's readE_inj, readE_mul,
readE_one (OnBytes.Slice) · MaskedSum.okE_mul, okE_sub.
Limits. AN IMPLICATION: THE PUBLIC TEST IS A PREMISE HERE; IN SCOPE, UNDER AN OPENING OF THE
DESCRIPTION AND ITS TEST ON ITS PLAN, IT SAYS YES AT EACH OF THE 25 BUILT SEGMENTS' DATA
(`heldPub_at_built`, Johnson/Desc/K8/Honest/HeldOutright.lean); THE SENTENCE ON zy_0's WORDS AND THE
NAME ARE PAID BY NOBODY HERE. THAT SENTENCE CANNOT BE MADE WEAKER, by reading: the test compares
words, and the second call's weight is 1 times zy_0, whose words are reduced: where pointsHeld says
yes, zy_0's words lie below the prime. AT THE FAMILY OF STATES AT
WHICH THESE THEOREMS STAND (reached by the blocks' own steps, whatever words the rounds hold) IT CAN
FAIL: zy_0 is a drawn element; of the states that the blocks reach under the library's wrapper
"below", which refuses a word that is not below the prime, it is to be expected, and not shown: that
zy_0 is, word for word, an element of such a round is typed by nobody. By a reading of all its
fields `K3Left` bounds no word. NOTHING AT THE HEAD's SEGMENT. IN SCOPE ALONE: under an opening of
the description and its test on its plan; the first chain; the family of states from the
description's own first state. Nothing says that any state is reached. No prover stands in it.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.K8.Honest.HeardAtReach
import Johnson.Desc.K8.Honest.PointsAtReach
import Johnson.Desc.First.Look.Via.Via
import Johnson.Top.H.P1Tie.Words

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Model.Stages (LinkH)
open OnBytes.Slice (readE readE_mul readE_one readE_inj)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.Part
open VerifiableInference.OnPublicFiles (K3Left)
open Johnson.Desc.First.Walk.Tied (Reach)

/-- 1 times an element whose words lie below the prime is that element, as words. -/
theorem one_mul_below (x : E) (hx : OnBytes.okE x = true) : mulE oneE x = x := by
  apply readE_inj _ _ (MaskedSum.okE_mul _ _) hx
  rw [readE_mul, readE_one, one_mul]

/-- An entry of a table made over a range. -/
theorem at_range {α : Type} (f : Nat → α) (n i : Nat) (d : α) (hi : i < n) :
    ((Array.range n).map f).getD i d = f i := by
  simp [Array.getD, hi]

/-- One more number of the shape, off the public test. -/
theorem pub_first {tl : HTailF2} (hP : heldPubB tl = true) :
    tl.f9.first = #[0, 2 ^ (tl.z1.call.n - min tl.z1.call.n tl.lidb)] := by
  unfold heldPubB at hP
  rw [Bool.and_eq_true] at hP
  have p1 := hP.1
  simp only [HTailF2.forestHeld, Bool.and_eq_true, beq_iff_eq] at p1
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, -⟩, q7⟩, -⟩, -⟩, -⟩ := p1
  exact q7

/-- The lookup's two weights, as words. -/
theorem weights_raw (h : Forest.Shape) (zy : Array E) (io : Nat) (hNC : h.NC = 2)
    (hio : h.iota = #[io, io]) (hfirst : h.first = #[0, 2 ^ io]) (hrK : h.rK = io + 1)
    (hz : OnBytes.okE (zy.getD 0 zeroE) = true) :
    ((Array.range h.NC).map (Forest.callWeight h zy)).getD 0 zeroE =
        subE oneE (zy.getD 0 zeroE) ∧
      ((Array.range h.NC).map (Forest.callWeight h zy)).getD 1 zeroE = zy.getD 0 zeroE := by
  have hpos : 0 < 2 ^ io := Nat.pos_of_ne_zero (by positivity)
  constructor
  · rw [hNC, at_range _ _ _ _ (by omega)]
    unfold Forest.callWeight
    simp [hrK, hio, hfirst, List.range_succ]
    exact one_mul_below _ (MaskedSum.okE_sub _ _)
  · rw [hNC, at_range _ _ _ _ (by omega)]
    unfold Forest.callWeight
    simp [hrK, hio, hfirst, List.range_succ, Nat.div_self hpos]
    exact one_mul_below _ (by simpa using hz)

/-- **Each call's weight is the second computation's.** -/
theorem weights_of_below {tl : HTailF2} {g : Forest.Heard} {lm : Nat} {F₀ F' : Fork}
    {rs : TwV.Rounds Cb.Gl.E} (K : K3Left Reading.gl tl.f9 lm F₀ F' g rs)
    (hP : heldPubB tl = true) (nc : tl.f9.NC = 2) (hz : OnBytes.okE (g.zy.getD 0 zeroE) = true) :
    ∀ q, q < 2 → g.e.getD q zeroE = callWeightAgain g q := by
  obtain ⟨n1, n2⟩ := pub_more hP
  obtain ⟨w0, w1⟩ := weights_raw tl.f9 g.zy _ nc n2 (pub_first hP) n1 hz
  intro q hq
  rcases Nat.lt_succ_iff_lt_or_eq.1 hq with h | h
  · obtain rfl : q = 0 := by omega
    rw [K.eRaw, w0]
    rfl
  · subst h
    rw [K.eRaw, w1]
    rfl

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **The test at a reached state.** -/
theorem pointsHeld_at_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 24) {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + 9) (z, s)) {tl : HTailF2}
    (ht : s.tl? = some tl) (hP : heldPubB Xl.tl = true) :
    ∃ g, tl.heard = some g ∧ (OnBytes.okE (g.zy.getD 0 zeroE) = true → tl.pointsHeld g = true) := by
  obtain ⟨v, g, F₀, F', rs, hg, K⟩ := left_at_batch hS hR O hOk hl e3 h ht
  have hP' : heldPubB tl = true := by
    rw [pub_heldFields tl, v, ← pub_heldFields Xl.tl]
    exact hP
  have nc : tl.f9.NC = 2 := by
    rw [show tl.f9 = Xl.tl.f9 from congrArg (·.f9) v]
    exact (two_calls_of_tests (_root_.P1K8.tests_at_built hS O (by omega : l < 25) e3)).1
  exact ⟨g, hg, fun hz => pointsHeld_of_weights K hP' nc (weights_of_below K hP' nc hz)⟩

/-- **SO `AllFront` THERE.** -/
theorem allFront_of_below (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 24) {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + 9) (z, s))
    {tl : HTailF2} {G : Fork} (ht : s.tl? = some tl) (hG : s.fork? = some G)
    (hP : heldPubB Xl.tl = true) :
    ∃ g, tl.heard = some g ∧ (OnBytes.okE (g.zy.getD 0 zeroE) = true →
      (G.trees.getD tl.ix.ZZ {}).name = "ZZ" →
      ∃ (nbW : Nat) (Wn : List Want), AllFront tl G g nbW Wn) := by
  obtain ⟨g, hg, k⟩ := allFront_of_three hS hR O hOk hl e3 h ht hG hP
  obtain ⟨g', hg', p⟩ := pointsHeld_at_batch hS hR O hOk hl e3 h ht hP
  obtain rfl : g = g' := Option.some.inj (hg.symm.trans hg')
  exact ⟨g, hg, fun hz hn => k (p hz) hn⟩

end

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.one_mul_below
#print axioms VerifiableInference.Desc.First.K8.Honest.at_range
#print axioms VerifiableInference.Desc.First.K8.Honest.pub_first
#print axioms VerifiableInference.Desc.First.K8.Honest.weights_raw
#print axioms VerifiableInference.Desc.First.K8.Honest.weights_of_below
#print axioms VerifiableInference.Desc.First.K8.Honest.pointsHeld_at_batch
#print axioms VerifiableInference.Desc.First.K8.Honest.allFront_of_below
