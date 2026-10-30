-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/DrawAt.lean: CONDITIONAL, under the library's one head on the public
input (`P5J.AtMgA`, Johnson/P5J/MgAtAll.lean): WHICH sub-protocol stands at number 14 (2 g + 1) + 6
of the first chain's flat list: the smallness test's block at the numbers `ProofFile.k8ParW`
(Johnson/Desc/ProofFile/Lot/K8.lean) of the very ground and link of `ReadsMember`
(Johnson/Desc/K5/Honest/Law/ReadsAtHead.lean); and that, at every state reached in front of it, two
of the tests of its draw's decision (Johnson/Desc/First/K8/Hear.lean) pass: "the list of parts is
closed", and "the closed list has the place's shapes".

Why. `tabs_at_reach` (Johnson/Desc/K5/Honest/Law/TabsAtReach.lean) speaks of a number of the flat
list and of `K8.tabs (ProofFile.k8Par …)`. That the draw stands at that number, and that these are its own
place's numbers, was left open there.

How. The library has the member as a term: `IM.k8_of_attention` (Johnson/IMR/K8Seat.lean), by the
link's list of sub-protocols; `IM.hear_at_flat` and `IM.flatIx_scope` give its number in the flat
list. `ProofFile.k8ParW … .toPar` is `ProofFile.k8Par …` by its text.

Main names:
  `draw_member`: the member at 14 (2 g + 1) + 6.
  `draw_tests`: at a state reached there: the seat's `closed` says yes, and the seat's `tabs` is
    `K8.tabs` of the member's own numbers.
  `keep_at_draw`: at a state reached there: the library's tuple `K8.Ready.keep` is the plan's, with
    no draw counted.
  `drawPlacesB`, `drawPlaces_closed`, `drawPlaces_bite`, `draw_place`: the same number in the
    written list of places `P5J.At.ps`: a closed fact, by the kernel, with a control.

Limits. The head is a hypothesis. The draw's six other tests (nothing is owed; nothing is drawn; the
number of matrices, their columns and rows, the number of combinations) are not shown to pass:
`keep_at_draw` has the values that five of them read, as the plan's; that the plan's values are the
place's, and that the plan's drawn matrix has no entry, is not shown here. Where no state is reached
the theorems say nothing. At the function `OnBytes.secondHashFunction`, of
which nothing is asked here; at the library's full size alone.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.TabsAtReach
import Johnson.Desc.K5.Honest.Law.KeepAtReach
import Johnson.Desc.First.K8.LawCondK1

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.First
open Johnson.Desc.First.Walk.Tied (Reach)
open P5J (AtMgA TS)

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : Look.Place} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

include h in
/-- **Which sub-protocol stands at number 14 (2 g + 1) + 6**: the smallness test's block, whole, at
the numbers of the ground G₀ and the link Xl of M, wrapped alone. Conditional: the head; hg; M. -/
theorem draw_member {g : ℕ} (hg : g < 12) {G₀ : ProofFile.Ground} {Xl : Stages.LinkH} {pd : ℕ}
    {reads digits : Option (List ℕ)} {b : Block S ProofFile.Cl}
    (M : ReadsMember Zp cF g G₀ Xl pd reads digits b) :
    ∃ b₈ : Block S ProofFile.Cl, cF.blocksInOrder[14 * (2 * g + 1) + 6]? = some b₈ ∧
      IM.LaidAlone ProofFile.sameReply b₈ (K8.whole (ProofFile.k8ParW Zp G₀ Xl (2 * g + 1))) b₈.name
        ⟨1, some (2 * g + 1), 5, .K8⟩ := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain rfl : Bs.G₀ = G₀ := Option.some.inj (O.blank.symm.trans M.blank)
  obtain ⟨Lk, b₈, X, _, e1, e2, eX, hla, _⟩ := IM.k8_of_attention h.scope h.reads O g hg
  obtain rfl : X = Xl := Option.some.inj (eX.symm.trans M.built)
  have hfl := IM.hear_at_flat e1 e2
  rw [IM.flatIx_scope h.scope h.reads O (l := 2 * g + 1) (by omega) 4,
    show 14 * (2 * g + 1) + 2 + 4 = 14 * (2 * g + 1) + 6 by omega] at hfl
  exact ⟨b₈, hfl, hla⟩

include h in
/-- **At every state reached in front of the draw, two of its decision's tests pass**: the list is
closed; the closed list has the shapes of the member's own numbers. Conditional: the head; hg; M;
hr. -/
theorem draw_tests {g : ℕ} (hg : g < 12) {G₀ : ProofFile.Ground} {Xl : Stages.LinkH} {pd : ℕ}
    {reads digits : Option (List ℕ)} {b : Block S ProofFile.Cl}
    (M : ReadsMember Zp cF g G₀ Xl pd reads digits b) {π : ProofFile.InstPub} {s : S}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * (2 * g + 1) + 6) (π, s)) :
    K8.atS.closed s = true ∧
      K8.atS.tabs s = K8.tabs (ProofFile.k8ParW Zp G₀ Xl (2 * g + 1)).toPar := by
  obtain ⟨tl, e, hc, ht⟩ := tabs_at_reach h hg M hr
  refine ⟨?_, ?_⟩
  · show (s.tl?.map (·.funClosed)).getD false = true
    rw [e]
    exact hc
  · show (s.tl?.map fun tl => tl.funs.toList.map fun Fn => (Fn.mat, Fn.len, Fn.start)).getD [] = _
    rw [e]
    exact ht

include h in
/-- **The five values in front of the draw**: at every state reached at number 14 (2 g + 1) + 6 the
library's tuple `K8.Ready.keep` is still the plan's, with no draw counted: the sending leaves the
smallness test's part of the state (the library's `laterAt_tl`), and the quiet step behind it turns
the list of tables and the mark "closed" alone (the library's `attO_yes`). Conditional: the head;
hg; ea: the group's plan; hr. -/
theorem keep_at_draw {g : ℕ} (hg : g < 12) {a : Attention.Plan}
    (ea : (P5J.At.X Zp).A[g]? = some a) {π : ProofFile.InstPub} {s : S}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * (2 * g + 1) + 6) (π, s)) :
    K8.Ready.keep s =
      some (a.seam.tl.NM, a.seam.tl.mats, a.seam.tl.tau, a.seam.tl.cfF, 0) := by
  obtain ⟨G₀, Xl, pd, reads, digits, b, M⟩ := member_at_head h hg
  have hA : G₀.W.A[Xl.g]? = some a := by
    rw [M.group, M.pubW]
    exact ea
  obtain ⟨s0, b', h0, hb, R, c, _, e⟩ := reach_last (k := 14 * (2 * g + 1) + 5) hr
  obtain rfl : b = b' := Option.some.inj (M.flat.symm.trans hb)
  obtain ⟨_, _, _, h4⟩ := (VerifiableInference.Desc.Sound.step_ok_iff 0 b s0 s R c c.length).1 e
  rw [M.is] at h4
  obtain ⟨m, h1, hm⟩ := seated_reads_inv Zp G₀ (2 * g + 1) Xl reads b.name M.kind hA h4
  obtain ⟨tl0, funs, e1, e2, _⟩ := K8.Ready.attO_yes a m s hm
  have e0 : m.tl? = s0.tl? := (VerifiableInference.Desc.K1.laterAt_tl _ _ _ _ _ _ s0 m _ _ h1).1
  rw [← keep_at_reach h hg ea h0]
  unfold K8.Ready.keep
  rw [e2, ← e0, e1]
  rfl

end

/-- A test with code on the written list of places: d places behind the block of the own rounds of
each of the twelve attention segments stands the smallness test's place, piece 5. -/
def drawPlacesB (d : ℕ) : Bool :=
  (List.range 12).all fun g =>
    P5J.At.ps[14 * (2 * g + 1) + 4 + d]? == some ⟨1, some (2 * g + 1), 5, .K8⟩

set_option maxRecDepth 1000000 in
/-- **The test says yes at two places behind.** No premise: a closed fact, by the kernel. -/
theorem drawPlaces_closed : drawPlacesB 2 = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: at one place behind the test says no. No premise: a closed fact, by the kernel. -/
theorem drawPlaces_bite : drawPlacesB 1 = false := by decide +kernel

/-- The written list of places has the smallness test's place at number 14 (2 g + 1) + 6.
Conditional: hg. -/
theorem draw_place {g : ℕ} (hg : g < 12) :
    P5J.At.ps[14 * (2 * g + 1) + 6]? = some ⟨1, some (2 * g + 1), 5, .K8⟩ :=
  beq_iff_eq.1 (List.all_eq_true.1 drawPlaces_closed g (List.mem_range.2 hg))

end H2K5.Honest

#print axioms H2K5.Honest.draw_member
#print axioms H2K5.Honest.draw_tests
#print axioms H2K5.Honest.keep_at_draw
#print axioms H2K5.Honest.drawPlaces_closed
#print axioms H2K5.Honest.drawPlaces_bite
#print axioms H2K5.Honest.draw_place
