-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/FrontIs.lean: THE ARRAYS AND THE LIST IN FRONT OF A BATCHING ARE THE OPENING's: in the goals'
scope, at each of the 25 segments of the first chain: at a state that is reached in front of the batching, the open ledger's
arrays are, but for the mark "the commitment is received", those that the opening laid off the segment's record, and the open
book-keeping's list is the record's.

  **`front_is`**      a state reached at 14 l + `IM.nAt l` + 2 with book-keeping L and a ledger G open: there are L₀, G₀ with
                      `OpenedOf X L₀ G₀` (Honest/K9/OpenIs.lean), X the segment's record, `lnk L₀ = lnk L` and `tr G = tr G₀`
                      (Honest/K9/TrLot.lean)
  `BareL trees`      every virtual row of every array is the empty row, but for its weights on the columns
  `bareL_of_tr`, `bareL_of_frame`, `bareL_fill`, `bareL_laid`   what hands it on: equal readings `tr`; equal frames
                        (`treesFrame`, OnBytes/Model/HideLaws.lean); the draw's filling; the opening's laying
  **`sizes_at_front`**   the ledger has just as many arrays as the list has entries
  **`bare_at_front`**    `BareL` of the ledger's arrays

How. The cut of the fold at the opening is that of `back_to_open` (Honest/K9/FreshAtHead.lean). The record's two facts: the
library's `public_trees` (Johnson/Desc/First/Link/Law/PlanTreesSize.lean) and `public_bare` (Honest/K9/PlanBare.lean), carried
to the records by `built_all` (Honest/K9/BuiltAll.lean).

Limits. In the goals' scope, at the hash function `secondHashFunction`. It shows of no state that it is reached. This file proves no
property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K9.OpenIs
import Johnson.Desc.ProofFile.Honest.K9.TrLot
import Johnson.Desc.ProofFile.Honest.K9.PlanBare
import Johnson.Desc.First.Link.Law.PlanTreesSize
import Johnson.Desc.First.Batch.Law.AtBlock

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.LinkJoin (lnk tr KeepsTr Bare public_bare public_trees)
open Johnson.Desc.First.Walk (emptySlots weightsAtZero)
open Johnson.Desc.First.Walk.Tied (Reach)
open Meaning.K2
open ProofFile (Cl)

/-- Every virtual row of every array is the empty row, but for its weights on the columns. -/
def BareL (trees : Array HTree) : Prop := ∀ Y ∈ trees, ∀ r ∈ Y.rows, ({ r with L := #[] } : HRow) = {}

theorem bareL_of_tr {F G : Fork} (h : tr G = tr F) (hF : BareL F.trees) : BareL G.trees := by
  intro Y hY r hr
  have h1 : ({ Y with root := none } : HTree) ∈ tr G := Array.mem_map.2 ⟨Y, hY, rfl⟩
  rw [h] at h1
  obtain ⟨Y', hY', e⟩ := Array.mem_map.1 h1
  have e' : Y'.rows = Y.rows := congrArg (·.rows) e
  exact hF Y' hY' r (e' ▸ hr)

theorem bareL_of_frame {A B : Array HTree} (h : treesFrame A = treesFrame B) (hB : BareL B) : BareL A := by
  intro Y hY r hr
  have h1 : Y.frame ∈ treesFrame A := Array.mem_map.2 ⟨Y, hY, rfl⟩
  rw [h] at h1
  obtain ⟨Y', hY', e⟩ := Array.mem_map.1 h1
  have e' : Y'.rows.map HRow.frame = Y.rows.map HRow.frame := congrArg (·.2) e
  have h2 : r.frame ∈ Y.rows.map HRow.frame := Array.mem_map.2 ⟨r, hr, rfl⟩
  rw [← e'] at h2
  obtain ⟨r', hr', e2⟩ := Array.mem_map.1 h2
  have e3 : ({ r' with L := #[] } : HRow) = { r with L := #[] } := congrArg (·.1) e2
  rw [← e3]
  exact hB Y' hY' r' hr'

theorem bareRows_fillOne (X : HTree) (h : ∀ r ∈ X.rows, ({ r with L := #[] } : HRow) = {}) :
    ∀ r ∈ (K9L.fillOne X).rows, ({ r with L := #[] } : HRow) = {} := by
  intro r hr
  simp only [K9L.fillOne, Array.mem_map] at hr
  obtain ⟨r0, hr0, rfl⟩ := hr
  split
  · exact h r0 hr0
  · exact h r0 hr0

theorem bareL_fold : ∀ (l : List Nat) (trees : Array HTree), BareL trees →
    BareL (l.foldl (fun trees ti => trees.modify ti K9L.fillOne) trees)
  | [], _, h => h
  | ti :: l, trees, h => by
    rw [List.foldl_cons]
    apply bareL_fold l
    intro X hX
    rw [← Array.mem_toList_iff, Array.toList_modify] at hX
    exact OnBytes.all_modify (fun X : HTree => ∀ r ∈ X.rows, ({ r with L := #[] } : HRow) = {}) K9L.fillOne
      bareRows_fillOne trees.toList ti (fun a ha => h a (Array.mem_toList_iff.mp ha)) X hX

/-- The draw's filling. -/
theorem bareL_fill (F : Fork) (T : Tail2) (h : BareL F.trees) : BareL (t2FillL F T).trees :=
  bareL_fold (List.range T.nt.size) F.trees h

/-- The opening's laying. -/
theorem bareL_laid {F₀ : Fork} (h : Bare F₀) (n : ℕ) : BareL (emptySlots (weightsAtZero F₀) n).trees := by
  intro Y hY r hr
  have hY' : Y ∈ F₀.trees.map fun X =>
      { X with rows := X.rows.map fun r => { r with L := Array.replicate X.K zeroE } } := hY
  obtain ⟨X0, h0, rfl⟩ := Array.mem_map.1 hY'
  obtain ⟨r0, h1, rfl⟩ := Array.mem_map.1 hr
  rw [h X0 h0 r0 h1]

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **From the batching's front back to the segment's opening, to the letter.** -/
theorem front_is (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25) {X : LinkH}
    (hX : Z.p.built.links[l]? = some X) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + IM.nAt l + 2) (z, s))
    {L : LinkCtx} {G : Fork} (hL : s.link? = some L) (hG : s.fork? = some G) :
    ∃ L₀ G₀, OpenedOf X L₀ G₀ ∧ lnk L₀ = lnk L ∧ tr G = tr G₀ := by
  have hk : 14 * l + IM.nAt l + 2 =
      k2Number l + 1 + (IM.nAt l - ((if l = 24 then 1 else 0) + 1)) := by
    by_cases h24 : l = 24
    · subst h24
      rfl
    · simp only [k2Number, IM.nAt, if_neg h24]
  have hn : (if l = 24 then 1 else 0) + 1 + (IM.nAt l - ((if l = 24 then 1 else 0) + 1)) ≤ IM.nAt l := by
    by_cases h24 : l = 24
    · subst h24
      exact Nat.le_refl _
    · simp only [IM.nAt, if_neg h24]
      exact Nat.le_refl _
  obtain ⟨hle, rs, cols, f⟩ := h.fold
  have f0 : foldBlocks 0 (c.blocksInOrder.take (k2Number l + 1 +
               (IM.nAt l - ((if l = 24 then 1 else 0) + 1)))) (ProofFile.startS Z z) rs cols = .ok (s, [], []) := by
    rw [← hk]
    exact f
  obtain ⟨v, Rv, Cv, fv⟩ := fold_cut (k := k2Number l + 1) _ f0
  obtain ⟨u, Ru, Cu, fu⟩ := fold_back (k := k2Number l) fv
  obtain ⟨b, hb⟩ : ∃ b, c.blocksInOrder[k2Number l]? = some b :=
    ⟨_, List.getElem?_eq_getElem (by omega : k2Number l < c.blocksInOrder.length)⟩
  obtain ⟨rs', gs', dd⟩ := fold_next hb fu fv
  have e1 : k2Number l + 1 = 14 * l + ((if l = 24 then 1 else 0) + 1) + 2 := by
    unfold k2Number
    omega
  rw [e1] at fv f0
  have K := hear_backT hS hR O hl (by omega) (fun e => by simp [e]) fv _ hn s [] [] f0
  obtain ⟨G₀, L₀, g0, l0, e3, e4⟩ := K G L hG hL
  exact ⟨L₀, G₀, opened_is hS hR O hl hX hb dd l0 g0, e3, e4⟩

/-- **The ledger has just as many arrays as the list has entries.** -/
theorem sizes_at_front (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {z : ProofFile.InstPub} {s : S} (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + IM.nAt l + 2) (z, s))
    {L : LinkCtx} {G : Fork} (hL : s.link? = some L) (hG : s.fork? = some G) :
    G.trees.size = L.list.nt.size := by
  have hP : Verify.publicOf P.pol P.KL (some lay) = .ok Z.p.X := by
    rw [← O.W]
    exact O.public
  obtain ⟨t1, t2, t3⟩ := public_trees hP
  obtain ⟨X, hX, hs⟩ := built_all hS hR O (fun Fp Tp => Fp.trees.size = Tp.nt.size) t1 t2 t3 l hl
  obtain ⟨L₀, G₀, ⟨⟨ck, m, rfl⟩, F₀, n, hF₀, rfl⟩, e1, e2⟩ := front_is hS hR O hl hX h hL hG
  have a1 : X.Tp = L.list := congrArg (·.2.1) e1
  have a2 : G.trees.size = (emptySlots (weightsAtZero F₀) n).trees.size := by
    have k := congrArg Array.size e2
    simpa [tr] using k
  have a3 : (emptySlots (weightsAtZero F₀) n).trees.size = F₀.trees.size := by
    show (F₀.trees.map _).size = _
    rw [Array.size_map]
  rw [a2, a3, hF₀, hs, a1]

/-- **Every virtual row is the empty row, but for its weights on the columns.** -/
theorem bare_at_front (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {z : ProofFile.InstPub} {s : S} (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + IM.nAt l + 2) (z, s))
    {L : LinkCtx} {G : Fork} (hL : s.link? = some L) (hG : s.fork? = some G) : BareL G.trees := by
  have hP : Verify.publicOf P.pol P.KL (some lay) = .ok Z.p.X := by
    rw [← O.W]
    exact O.public
  obtain ⟨t1, t2, t3⟩ := public_bare hP
  obtain ⟨X, hX, hs⟩ := built_all hS hR O (fun Fp _ => Bare Fp) t1 t2 t3 l hl
  obtain ⟨L₀, G₀, ⟨-, F₀, n, hF₀, rfl⟩, -, e2⟩ := front_is hS hR O hl hX h hL hG
  have hb : Bare F₀ := by
    intro Y hY
    rw [hF₀] at hY
    exact hs Y hY
  exact bareL_of_tr e2 (bareL_laid hb n)

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.bareL_of_tr
#print axioms ProofFile.Honest.K9.bareL_of_frame
#print axioms ProofFile.Honest.K9.bareRows_fillOne
#print axioms ProofFile.Honest.K9.bareL_fold
#print axioms ProofFile.Honest.K9.bareL_fill
#print axioms ProofFile.Honest.K9.bareL_laid
#print axioms ProofFile.Honest.K9.front_is
#print axioms ProofFile.Honest.K9.sizes_at_front
#print axioms ProofFile.Honest.K9.bare_at_front
