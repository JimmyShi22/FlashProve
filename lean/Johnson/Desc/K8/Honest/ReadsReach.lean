-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K8/Honest/ReadsReach.lean: THE SMALLNESS TEST: WHAT EVERY STATE HOLDS THAT IS REACHED
IN FRONT OF THE DRAW, AT A LAYERS' SEGMENT AND AT THE OUTPUT HEAD OF THE PROOF FILE's DESCRIPTION,
IN THE GOALS' SCOPE: the test's data there are the planned link's, closed; at the head, besides, the
closed list has the shapes of the place of the kind's own lot. Laws on the verifier's chain alone:
no honest side; neither the table's promise nor "the state bears no mark" is asked; none of the
library's goals.

  `reach_prev`   what is reached at k + 1 comes of what is reached at k by an accepting step of
                   member k (the same sentence as `reach_back` of
                   Johnson/Desc/ProofFile/Honest/K8/SeatedReady.lean, a file that the library may
                   not hold: a second copy, so that this file imports nothing of the honest side)
  **`front_layers`**   g < 12: there is the planned link Xl at 2 g, of kind 0; the flat list is that
                   long; and AT EVERY STATE REACHED AT NUMBER 28 g + 6, from whatever start: the
                   library's tuple `Ready.keep` is Xl.tl's five fields, and the list is closed
  **`front_head`**   the like at number 343, at the planned link Xl at 24, of kind 2; AND the closed
                   list has the shapes `tabs (ProofFile.k8Par Z G₀ Xl 24)`
  `seats_of_alone`   a block that the description lays alone over the kind's block, whole, is seated
                   over the draw's block (`Seats`, Johnson/Desc/First/K8/LawSeated.lean): the seat's
                   guard on the reply never bites
  **`draw_layers`**, **`draw_head`**   THE DRAW's OWN MEMBER STANDS AT THESE NUMBERS, 28 g + 6 and
                   343, seated over the draw's block at the place of the kind's own lot; at a
                   layers' segment, besides, the link's number of matrices is the length of the
                   place's list of columns (the library's `IM.k8_of_layers`)
By: the library's seats of the member in front (`IM.k1_reads_layers`, `IM.k1_reads_of`), its numbers
in the flat list (`IM.hear_at_flat`, `IM.flatIx_scope`), the links' plans (`IM.ground_tails`,
`IM.ground_named`); Johnson/Desc/K8/Honest/ReadsSeat.lean, ParFacts.lean.
Limits. THE FULL SIZE ALONE, in the goals' scope, at the format's second hash function. THAT ANY STATE IS
REACHED THERE IS NOT SHOWN. At a layers' segment nothing on the list's shapes. Nothing on what is
owed a count.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.K8.Honest.ReadsSeat
import Johnson.Desc.K8.Honest.ParFacts
import Johnson.Desc.K8.Honest.Keeps
import Johnson.IMR.K1Scope
import Johnson.IMR.K8Seat
import Johnson.IMR.FlatScope
import Johnson.Top.H0.Walk.ReachInv

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open VerifiableInference.Desc (Block FileDescription Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K8 (tabs Seats approximateRangeProofDrawKind atS ParW)
open VerifiableInference.Desc.First.K8.Ready (keep closedAt)
open Johnson.Desc.First.Walk.Tied (Reach StepYes stepYes_decide)

/-- What is reached at k + 1 comes of what is reached at k by an accepting step of member k. -/
theorem reach_prev {σ Cl Q : Type} {ft : Nat} {bs : List (Block σ Cl)} {start : Q → σ} {k : Nat}
    {z : Q} {s' : σ} (h : Reach ft bs start (k + 1) (z, s')) :
    ∃ s b, Reach ft bs start k (z, s) ∧ bs[k]? = some b ∧ StepYes ft b s s' := by
  cases h with
  | succ hr hb hy => exact ⟨_, _, hr, hb, hy⟩

/-- **A block that the description lays alone over the kind's block, whole, is seated over the
draw's block**: the seat's further guard, that the reply stays, never bites: the draw leaves what
was put out. -/
theorem seats_of_alone {b : Block S ProofFile.Cl} {p : ParW} {name : String} {l i : Nat}
    (h : IM.LaidAlone ProofFile.sameReply b (VerifiableInference.Desc.First.K8.whole p) name
      { chain := 1, link := some l, piece := i, kind := .K8 }) :
    Seats b (approximateRangeProofDrawKind (Cl := ProofFile.Cl) atS p.toPar) := by
  refine ⟨(IM.alone_underR h).1, fun s rs gs t => ?_⟩
  rw [IM.k8_yes h s t rs gs]
  refine ⟨fun hy => ⟨hy.1, hy.2.1⟩, fun hy => ⟨hy.1, hy.2, ?_⟩⟩
  have e : t.out = s.out := (keeps_of_decide p.toPar hy.1).rest.2.2.2.2.2.2.1
  unfold ProofFile.sameReply
  rw [e]
  exact beq_self_eq_true _

variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **In front of the draw of a layers' segment.** -/
theorem front_layers (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) {g : Nat} (hg : g < 12) :
    ∃ Xl : LinkH, Bs.G₀.built[2 * g]? = some Xl ∧ Xl.kind = 0 ∧ 28 * g + 6 ≤ c.blocksInOrder.length ∧
      ∀ {Q : Type} (start : Q → S) (z : Q) (s : S), Reach 0 c.blocksInOrder start (28 * g + 6) (z, s) →
        keep s = some (Xl.tl.NM, Xl.tl.mats, Xl.tl.tau, Xl.tl.cfF, Xl.tl.foldDrawn) ∧
          closedAt s = some true := by
  obtain ⟨Lk, b, Xl, pd, reads, digits, e1, e2, hX, hk, hgX, -, la⟩ :=
    IM.k1_reads_layers hS hR O g hg
  obtain ⟨hp, a, l, l', eG, -, el, etl, -⟩ := (IM.ground_tails hS hR O.pub O.blank).1 g hg
  obtain rfl : l = Xl := Option.some.inj (el.symm.trans hX)
  have hfl : c.blocksInOrder[28 * g + 5]? = some b := by
    have h0 := IM.hear_at_flat e1 e2
    rw [IM.flatIx_scope hS hR O (l := 2 * g) (by omega) 3,
      show 14 * (2 * g) + 3 + 2 = 28 * g + 5 by omega] at h0
    exact h0
  have hL : LaysClosed hp.tl b := reads_closed_layers hX hk (by rw [hgX]; exact eG) la
  refine ⟨l, hX, hk, (List.getElem?_eq_some_iff.1 hfl).1, fun start z s hr => ?_⟩
  obtain ⟨sj, b', -, hb', hy⟩ := reach_prev (k := 28 * g + 5) hr
  obtain rfl : b = b' := Option.some.inj (hfl.symm.trans hb')
  obtain ⟨rs, gs, hd⟩ := stepYes_decide hy
  rw [etl]
  exact ⟨hL.keep hd, hL.closed hd⟩

/-- **In front of the draw of the output head.** -/
theorem front_head (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) :
    ∃ Xl : LinkH, Bs.G₀.built[24]? = some Xl ∧ Xl.kind = 2 ∧ 343 ≤ c.blocksInOrder.length ∧
      ∀ {Q : Type} (start : Q → S) (z : Q) (s : S), Reach 0 c.blocksInOrder start 343 (z, s) →
        keep s = some (Xl.tl.NM, Xl.tl.mats, Xl.tl.tau, Xl.tl.cfF, Xl.tl.foldDrawn) ∧
          closedAt s = some true ∧
          ∀ tl, s.tl? = some tl → tl.funs.toList.map (fun Fn => (Fn.mat, Fn.len, Fn.start)) =
            tabs (ProofFile.k8Par Z Bs.G₀ Xl 24) := by
  obtain ⟨Lk, b, Xl, pd, reads, digits, e1, e2, hX, -, la⟩ := IM.k1_reads_of hS hR O 24 (by omega)
  obtain ⟨l, el, etl, -⟩ := (IM.ground_tails hS hR O.pub O.blank).2
  obtain rfl : l = Xl := Option.some.inj (el.symm.trans hX)
  obtain ⟨l', el', hk, -⟩ := (IM.ground_named hS hR O.pub O.blank).2
  obtain rfl : l' = l := Option.some.inj (el'.symm.trans hX)
  have hfl : c.blocksInOrder[342]? = some b := by
    have h0 := IM.hear_at_flat e1 e2
    rw [IM.flatIx_scope hS hR O (l := 24) (by omega) (IM.k1Ix 24 false)] at h0
    exact h0
  have hL : LaysClosed Bs.G₀.W.H.tl b := reads_closed_head hX hk la
  have hT := reads_tabs_head (ProofFile.k8Par Z Bs.G₀ l' 24) hX hk la
    (k8Par_asks_head Z Bs.G₀ l' 24 hk) (by rw [← etl]; exact k8Par_ks Z Bs.G₀ l' 24)
    (by rw [← etl]; exact k8Par_ms Z Bs.G₀ l' 24)
  refine ⟨l', hX, hk, (List.getElem?_eq_some_iff.1 hfl).1, fun start z s hr => ?_⟩
  obtain ⟨sj, b', -, hb', hy⟩ := reach_prev (k := 342) hr
  obtain rfl : b = b' := Option.some.inj (hfl.symm.trans hb')
  obtain ⟨rs, gs, hd⟩ := stepYes_decide hy
  rw [etl]
  exact ⟨hL.keep hd, hL.closed hd, hT sj rs gs s hd⟩

/-- **The draw's own member at a layers' segment**; and the number of matrices, off the library. -/
theorem draw_layers (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) {g : Nat} (hg : g < 12) :
    ∃ (b : Block S ProofFile.Cl) (Xl : LinkH), Bs.G₀.built[2 * g]? = some Xl ∧
      c.blocksInOrder[28 * g + 6]? = some b ∧
      Seats b (approximateRangeProofDrawKind (Cl := ProofFile.Cl) atS (ProofFile.k8Par Z Bs.G₀ Xl (2 * g))) ∧
      Xl.tl.NM = (ProofFile.k8Par Z Bs.G₀ Xl (2 * g)).ks.length := by
  obtain ⟨Lk, b, Xl, hp, e1, e2, hX, la, eG, -, -, -, hnm⟩ := IM.k8_of_layers hS hR O g hg
  obtain ⟨hp', a, l, l', eG', -, el, etl, -⟩ := (IM.ground_tails hS hR O.pub O.blank).1 g hg
  obtain rfl : l = Xl := Option.some.inj (el.symm.trans hX)
  obtain rfl : hp' = hp := Option.some.inj (eG'.symm.trans eG)
  refine ⟨b, l, hX, ?_, seats_of_alone la, by rw [etl]; exact hnm⟩
  have h0 := IM.hear_at_flat e1 e2
  rw [IM.flatIx_scope hS hR O (l := 2 * g) (by omega) 4,
    show 14 * (2 * g) + 4 + 2 = 28 * g + 6 by omega] at h0
  exact h0

/-- **The draw's own member at the output head.** -/
theorem draw_head (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) :
    ∃ (b : Block S ProofFile.Cl) (Xl : LinkH), Bs.G₀.built[24]? = some Xl ∧ c.blocksInOrder[343]? = some b ∧
      Seats b (approximateRangeProofDrawKind (Cl := ProofFile.Cl) atS (ProofFile.k8Par Z Bs.G₀ Xl 24)) := by
  obtain ⟨Lk, b, Xl, e1, e2, hX, la, -⟩ := IM.k8_of_head hS hR O
  refine ⟨b, Xl, hX, ?_, seats_of_alone la⟩
  have h0 := IM.hear_at_flat e1 e2
  rw [IM.flatIx_scope hS hR O (l := 24) (by omega) 5] at h0
  exact h0

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.seats_of_alone
#print axioms VerifiableInference.Desc.First.K8.Honest.draw_layers
#print axioms VerifiableInference.Desc.First.K8.Honest.draw_head
#print axioms VerifiableInference.Desc.First.K8.Honest.reach_prev
#print axioms VerifiableInference.Desc.First.K8.Honest.front_layers
#print axioms VerifiableInference.Desc.First.K8.Honest.front_head
