-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Walk/FrameBase.lean: IN A ROW OF PIECES THAT HOLDS A
DESCRIPTION's BLOCKS AND TILES ITS FIRST CHAIN, A PIECE's BASE IS THE NUMBER OF TREES THAT THE BLOCKS
IN FRONT TELL; SO THE TREES THAT ARE SAMPLED IN FRONT LIE BELOW IT, where the test fenceFit says yes.
Book-keeping on lists over other files' theorems; no round is evaluated.

  trees_of_along   data that stand along declared rounds (RoundIs), as many as these: they list as
                   many trees as the rounds' entries say roots
  told_of_shaped   a shaped block tells of as many trees as its declared rounds' entries say roots
  trees_in_front   the pieces in front of number k list as many trees as the blocks in front tell
  base_is_told     **q.base = treesTold told k**, told: what each block of the first chain tells
  low_of_fence     **x.1 < q.base for every sampled tenant x whose pin is open at border k**, at
                   numbers N whose treesAt at that border is treesTold told k, under fenceFit's yes
  low_withTold     the same at N.withTold ps told, ps a list of places without a repeat

Limits. WHAT IS ASKED BESIDE OfDesc: the description's data are made (G.data file = .ok D); three
fields of Three.Fits (the row tiles the chain; its data are D.ds₁; its first base is 0); every block
of the first chain is shaped (a clause of blocksOk); k is a number of the chain. OfDesc ALONE DOES
NOT FIX A PIECE's BASE. fenceFit's YES IS A PREMISE: a test with code on the plan's seats; no member
here. Nothing on soundness.

-/
import Johnson.Road.K4.PieceAtFits
import Johnson.Desc.First.FenceFit
import Johnson.Top.H0.Walk.FrameNone

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.Walk.Tied
open OnBytes OnBytes.Maker OnBytes.Flat
open _root_.Run.PQ (CK)
open VerifiableInference.Desc (Block FileDescription Place numAt)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Numbers treesTold sampledIn openSets start fenceFit
  fenceFit_at)
open OnBytes.Road.K4 (tiled_base fits_piece)

/-- Data along declared rounds, as many as these, list as many trees as the entries say roots. -/
theorem trees_of_along (num : Fmt.TreeSource → ℕ) : ∀ (rs : List Fmt.DeclaredRound) (ds : List RDT),
    ds.length = rs.length → Along (RoundIs num) rs ds →
    (ds.map (·.trees.length)).sum = (rs.map (·.entry.roots)).sum
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | r :: rs, d :: ds, h, hA => by
    have hA' : RoundIs num r d ∧ Along (RoundIs num) rs ds := hA
    rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, hA'.1.2.2.2.2.2,
      trees_of_along num rs ds (by simpa using h) hA'.2]

/-- Lists of oracles, one for each round, each with a member for each of the round's roots. -/
theorem flatten_len : ∀ (rs : List Fmt.DeclaredRound) (os : List (List VerifiableInference.Desc.Oracle)),
    os.length = rs.length → (∀ x ∈ rs.zip os, x.2.length = x.1.entry.roots) →
    os.flatten.length = (rs.map (·.entry.roots)).sum
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | r :: rs, o :: os, h, g => by
    have e : o.length = r.entry.roots := g (r, o) (by simp)
    rw [List.flatten_cons, List.length_append, List.map_cons, List.sum_cons, e,
      flatten_len rs os (by simpa using h) fun x hx => g x (by
        rw [List.zip_cons_cons]
        exact List.mem_cons_of_mem _ hx)]

/-- **A shaped block tells of as many trees as its declared rounds' entries say roots.** -/
theorem told_of_shaped {S Cl : Type} (b : Block S Cl) (h : b.shaped = true) :
    b.oracles.flatten.length = (b.rounds.map (·.entry.roots)).sum := by
  unfold Block.shaped at h
  obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp h
  refine flatten_len b.rounds b.oracles (by simpa using h1) fun x hx => ?_
  have h3 := List.all_eq_true.1 h2 x hx
  exact by simpa using ((Bool.and_eq_true _ _).mp h3).1

section
variable {C : CK} {W Xi : Type} (G : FileDescription Xi) (file : String) (D : WholeD)
  (hD : G.data file = .ok D) {all : List LeftT} {X₁ X₂ : Type} (R : ThreeAt C D all G X₁ X₂ W)
  (hO : OfDesc G R) (ht : Tiled R.p₁ R.l₁) (hd : rowData R.p₁ R.l₁ = D.ds₁)
  (hsh : ∀ b ∈ G.first.blocksInOrder, b.shaped = true)
include hD hO ht hd hsh

/-- **The pieces in front of number k list as many trees as the blocks in front tell.** -/
theorem trees_in_front (k : ℕ) (hk : k < G.first.blocksInOrder.length) :
    (((R.p₁ :: R.l₁).take k).map (·.trees)).sum =
      treesTold (G.first.blocksInOrder.map fun b => b.oracles.flatten) k := by
  have hlen : (R.p₁ :: R.l₁).length = G.first.blocksInOrder.length := by
    have h5 := congrArg List.length hO.b₁
    simpa only [List.length_map] using h5
  induction k with
  | zero => simp [treesTold]
  | succ k ih =>
    have ih' := ih (by omega)
    have hqi : (R.p₁ :: R.l₁)[k]? = some ((R.p₁ :: R.l₁)[k]'(by rw [hlen]; omega)) :=
      List.getElem?_eq_getElem _
    have hbi : G.first.blocksInOrder[k]? = some (G.first.blocksInOrder[k]'(by omega)) := List.getElem?_eq_getElem _
    obtain ⟨_, _, hl, hA⟩ := fits_piece G file D hD R hO ht hd hqi hbi hk
    have e1 := trees_of_along _ _ _ hl hA
    have e2 := told_of_shaped _ (hsh _ (List.getElem_mem (by omega : k < G.first.blocksInOrder.length)))
    unfold treesTold at ih' ⊢
    rw [List.take_add_one, hqi, List.take_add_one, List.getElem?_map, hbi]
    simp only [Option.map_some, Option.toList_some, List.map_append, List.sum_append,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    rw [ih', e2]
    exact congrArg _ e1

variable (h0 : R.p₁.base = 0) {k : ℕ}
  {q : Piece C (frameAt D all D.key₁ R.ft₁) (G.XiPub × G.S₁) G.Cl W}
  (hq : (R.p₁ :: R.l₁)[k]? = some q)
include h0 hq

/-- **A PIECE's BASE IS THE NUMBER OF TREES THAT THE BLOCKS IN FRONT TELL.** -/
theorem base_is_told : q.base = treesTold (G.first.blocksInOrder.map fun b => b.oracles.flatten) k := by
  have hlen : (R.p₁ :: R.l₁).length = G.first.blocksInOrder.length := by
    have h5 := congrArg List.length hO.b₁
    simpa only [List.length_map] using h5
  have hk : k < G.first.blocksInOrder.length := by
    rw [← hlen]
    exact (List.getElem?_eq_some_iff.1 hq).1
  rw [tiled_base R.l₁ R.p₁ ht k q hq, h0, Nat.zero_add]
  exact trees_in_front G file D hD R hO ht hd hsh k hk

/-- **THE TREES THAT ARE SAMPLED IN FRONT LIE BELOW THE PIECE's BASE**: at numbers whose treesAt at
border k is what the blocks in front tell, under the yes of the test fenceFit. -/
theorem low_of_fence (N : Numbers) (links : List ModelPart) (ps : List Place)
    (hf : fenceFit N links ps = true) (hkp : k ≤ ps.length)
    (hb : N.treesAt ps[k]? = treesTold (G.first.blocksInOrder.map fun b => b.oracles.flatten) k) :
    ∀ x ∈ sampledIn N ((openSets links ps (start links))[k]?.getD []), x.1 < q.base := by
  intro x hx
  rw [base_is_told G file D hD R hO ht hd hsh h0 hq, ← hb]
  exact fenceFit_at N links ps hf k hkp x hx

/-- **At the numbers that are filled off what the blocks tell**, ps without a repeat. -/
theorem low_withTold (N : Numbers) (links : List ModelPart) (ps : List Place) (hn : ps.Nodup)
    (hkp : k ≤ ps.length)
    (hf : fenceFit (N.withTold ps (G.first.blocksInOrder.map fun b => b.oracles.flatten)) links ps = true) :
    ∀ x ∈ sampledIn (N.withTold ps (G.first.blocksInOrder.map fun b => b.oracles.flatten))
      ((openSets links ps (start links))[k]?.getD []), x.1 < q.base :=
  low_of_fence G file D hD R hO ht hd hsh h0 hq _ links ps hf hkp
    (congrArg (treesTold _) (borderOf_le hn hkp))

end

end Johnson.Desc.First.Walk.Tied

#print axioms Johnson.Desc.First.Walk.Tied.trees_of_along
#print axioms Johnson.Desc.First.Walk.Tied.told_of_shaped
#print axioms Johnson.Desc.First.Walk.Tied.trees_in_front
#print axioms Johnson.Desc.First.Walk.Tied.base_is_told
#print axioms Johnson.Desc.First.Walk.Tied.low_of_fence
#print axioms Johnson.Desc.First.Walk.Tied.low_withTold
