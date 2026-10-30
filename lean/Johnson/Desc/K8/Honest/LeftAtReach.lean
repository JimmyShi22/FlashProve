-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/LeftAtReach.lean: THE SMALLNESS TEST: AT EVERY STATE THAT THE FIRST CHAIN's
OWN BLOCKS REACH IN FRONT OF THE BATCHING OF ONE OF THE 24 SEGMENTS IN FRONT OF THE HEAD's, IN THE
GOALS' SCOPE, WHAT THE DIGITS' LOOKUP HAS HEARD IS THERE AND STANDS IN THE LIBRARY's PROMISE
`K3Left` (Johnson/Top/H/K3LeftStatement.lean) AT THE STATE's OWN f9. The library's own law at these
very states (`leftOn_digits_front`, Johnson/Desc/First/Link/Law/KxAtFront.lean) has the promise at
the shape that the lookup's parameters fix; here that shape is tied to the data. Lemmas; none of the
library's goals.

  `blocks_planOk`   the description's test on its plan gives each block's of the first chain
  `tlAt_at_built` the library's reader of a link's data off the public structure returns the built
                   segment's data
  `shape_at_built` so the shape that the digits' lookup's parameters fix at link l is the built
                   segment's f9
  **`left_at_batch`** at a reached state, l < 24: the five planned fields `heldFields`
                   (Johnson/Desc/K8/Honest/HeldPublic.lean) are the built segment's; there are g,
                   two ledgers and rounds with tl.heard = some g and K3Left Reading.gl tl.f9 5 … g …
By: `leftOn_digits_front` · `digits_shape_at`, `shapeZAll_of_public`
(Johnson/Desc/First/Look/DigitsShapeAt.lean) · K9Asks.tlAt_built, blank_at
(Johnson/Desc/First/Link/Law/K9DigStatic.lean), built_tl (K9RowsAskLaw.lean) · Keeps.planOk_blocks
(Johnson/Desc/PlanPasses.lean) · `sized_at_batch` (Johnson/P1K8R/HeardAtBatch.lean) ·
LinkJoin.planned_at_batch (Johnson/Desc/First/Link/Law/PlannedAtDraw.lean).
KIN: the library's `shape_of_dig` (Johnson/LPFE1R/ShapeOfDig.lean) ties the same shape to what
another reader (digAt) lays; `three_of_leftOn` (ThreeOfLeftOn.lean) spends the promise at what is
fixed in front. Not called.
Limits. NOTHING AT THE HEAD's SEGMENT in the last (the library's `leftOn_digits_head` asks there
that a ledger is open with its sizes). The two ledgers and the rounds are hidden behind "there are".
IN SCOPE ALONE: under an opening of the description and its test on its plan; the first chain; the
family of states from the description's own first state. Nothing says that any state is reached. No
prover stands in it.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.K8.Honest.HeldPublic
import Johnson.Desc.First.Link.Law.KxAtFront
import Johnson.Desc.First.Link.Law.K9RowsAskLaw
import Johnson.Desc.First.Link.Law.K9DigStatic
import Johnson.Desc.First.Look.DigitsShapeAt
import Johnson.Desc.PlanPasses
import Johnson.P1K8R.HeardAtBatch

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.OnPublicFiles (K3Left)
open Johnson.Desc.First.Walk.Tied (Reach)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- The description's test on its plan gives each block's of the first chain. -/
theorem blocks_planOk (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hOk : F.planOk = true) : ∀ b ∈ c.blocksInOrder, b.planOk = true := by
  have e := O.desc
  subst e
  exact (Keeps.planOk_blocks _ hOk).1

/-- The reader of a link's data returns the built segment's. -/
theorem tlAt_at_built (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {l : ℕ} (hl : l < 25) {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) :
    Look.tlAt Bs.G₀.W l = some Xl.tl := by
  obtain ⟨X', hX', e⟩ := K9Asks.built_tl O.blank e3
  obtain ⟨b, hb, eb⟩ := ProofFile.Law.pub_builtOf O.pub
  have hX'' : (ProofFile.Law.blankB b).links[l]? = some X' := by
    rw [eb]
    exact hX'
  obtain ⟨c0, hc, t, -, -⟩ := K9Asks.blank_at hX''
  have hW : Verify.publicOf P.pol P.KL (some lay) = .ok Z.p.X := by
    rw [← O.W]
    exact O.public
  rw [O.W, e, t]
  exact K9Asks.tlAt_built hS hR hW hb hl hc

/-- The shape that the digits' lookup's parameters fix is the built segment's f9. -/
theorem shape_at_built (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {l : ℕ} (hl : l < 25) {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) {P' : Look.P}
    {hh : Forest.Shape} (hP : Look.placeAt Bs.G₀.W l true = some P') (hs : P'.shape = some hh) :
    hh = Xl.tl.f9 := by
  unfold Look.placeAt at hP
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 hP
  have k := Look.digits_shape_at (Look.shapeZAll_of_public O.public) hx
    (tlAt_at_built hS hR O hl e3) (Params.settingOf Bs.G₀.W.P.frame)
  exact Option.some.inj (hs.symm.trans k)

/-- **What the lookup heard stands in the library's promise, at the state's own f9.** -/
theorem left_at_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 24) {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + 9) (z, s)) {tl : HTailF2}
    (ht : s.tl? = some tl) :
    heldFields tl = heldFields Xl.tl ∧ ∃ (g : Forest.Heard) (F₀ F' : Fork)
      (rs : TwV.Rounds Cb.Gl.E), tl.heard = some g ∧ K3Left Reading.gl tl.f9 5 F₀ F' g rs := by
  have hx : (l, (if l = 24 then 5 else 4), (if l = 24 then 3 else 2)) ∈ P1K8S.stretches :=
    List.mem_map.2 ⟨l, List.mem_range.2 (by omega), rfl⟩
  have h' : Reach 0 c.blocksInOrder (ProofFile.startS Z)
      (14 * l + (if l = 24 then 5 else 4) + 3 + (if l = 24 then 3 else 2)) (z, s) := by
    rw [if_neg (by omega), if_neg (by omega)]
    exact h
  have v : heldFields tl = heldFields Xl.tl := LinkJoin.of_readTl
    (LinkJoin.planned_at_batch planned_heldFields hS hR O hx e3 (z, s) h') tl ht
  have v9 : tl.f9 = Xl.tl.f9 := congrArg (·.f9) v
  obtain ⟨P', hh, hP, hs, -, F₀, F', G, g, rs, -, -, K, hg, -, -, -⟩ :=
    LinkJoin.leftOn_digits_front hS hR O (blocks_planOk O hOk) hl h
      (_root_.P1K8.sized_at_batch hS hR O hOk hl h) 5
  have e9 : hh = tl.f9 := (shape_at_built hS hR O (by omega) e3 hP hs).trans v9.symm
  subst e9
  refine ⟨v, g, F₀, F', rs, ?_, K⟩
  have hg' : s.tl?.bind (·.heard) = some g := hg
  rw [ht] at hg'
  exact hg'

end

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.blocks_planOk
#print axioms VerifiableInference.Desc.First.K8.Honest.tlAt_at_built
#print axioms VerifiableInference.Desc.First.K8.Honest.shape_at_built
#print axioms VerifiableInference.Desc.First.K8.Honest.left_at_batch
