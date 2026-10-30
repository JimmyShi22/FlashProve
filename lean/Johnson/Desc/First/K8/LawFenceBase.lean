-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/LawFenceBase.lean: THE FENCE AT THE STATE's OWN LIST: every seat that the
approximate range proof's sub-protocol (our files: the smallness test's block) names at the
verifier's state lies in a tree BELOW THE FIRST TREE OF THE PIECE that holds the sub-protocol. And,
without the kind, what that first tree is: THE NUMBER OF ROOTS THAT THE SUB-PROTOCOLS IN FRONT
DECLARE. Statements and proofs: counting on lists; no round is evaluated.

  `trees_of_along`: a stretch whose rounds' data are those of declared rounds (`RoundIs`,
    Johnson/Desc/Sound/Stretch.lean), as many as these, sends as many trees as these declare roots.
  `trees_in_front`: at rows of pieces that hold a written IOP's sub-protocols (`OfDesc`) and tile
    its first chain: the pieces in front of number k send as many trees as the sub-protocols in
    front of number k declare roots.
  `base_is_roots_flat`, `base_is_roots`: **so, where the first piece's first tree is 0, the piece at
    number k has q.base = rootsIn of the declared rounds in front**: as the rounds of the
    sub-protocols in front, and as the first `roundsIn` rounds of the chain's declared rounds.
    KIND-FREE. Over `tiled_base` and `fits_piece` (Johnson/Road/K4/PieceAtFits.lean).
  `named_seats_below_base`: **`Named.namedB p S book tl L = true` gives, at every i,
    `(Named.seatFn rad S book tl L i).1 < q.base`**, at the piece q at the number of a sub-protocol
    b with `LikeP seat p b`, where the file's test on the plan says yes. By `named_seats_below_P`
    (LawSeatedPlan.lean).
  `named_seats_below_fits`: the same, the three facts on the rows taken from `Three.Fits`
    (Johnson/Desc/Sound/FileRule.lean).

Limits. That the sub-protocol at a number of the proof file's first chain has `LikeP`, that the rows
fit and that the plan's test says yes are premises: shown at no written IOP here. S, book, tl, L are
letters: the verifier's state's own values among them. Nothing on what a tree holds. No soundness
statement.

-/
import Johnson.Desc.First.K8.LawSeatedPlan
import Johnson.Road.K4.PieceAtFits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8
open OnBytes.Maker
open _root_.Run.PQ (CK)
open VerifiableInference.Desc (Block FileDescription numAt rootsIn roundsIn length_flatMap_rounds)
open VerifiableInference.Desc.Sound

/-- A stretch sends as many trees as its declared rounds say roots. -/
theorem trees_of_along (num : Fmt.TreeSource → ℕ) : ∀ (rs : List Fmt.DeclaredRound) (ds : List RDT),
    ds.length = rs.length → Along (RoundIs num) rs ds →
      (ds.map (·.trees.length)).sum = rootsIn rs
  | [], [], _, _ => rfl
  | r :: rs, d :: ds, hl, hA => by
    have ih := trees_of_along num rs ds (by simpa using hl) hA.2
    simp only [rootsIn, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, hA.1.2.2.2.2.2]
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

theorem rootsIn_append (a b : List Fmt.DeclaredRound) : rootsIn (a ++ b) = rootsIn a + rootsIn b := by
  simp [rootsIn]

section
variable {Xi : Type} {C : CK} {W : Type} (G : FileDescription Xi) (file : String) (D : WholeD)
  (hD : G.data file = .ok D) {all : List LeftT} {X₁ X₂ : Type} (R : ThreeAt C D all G X₁ X₂ W)
  (hO : OfDesc G R) (ht : Tiled R.p₁ R.l₁) (hd : rowData R.p₁ R.l₁ = D.ds₁)

include hD hO ht hd in
/-- The pieces in front of number k send as many trees as the sub-protocols in front declare roots.
-/
theorem trees_in_front (k : ℕ) (hk : k < G.first.blocksInOrder.length) :
    (((R.p₁ :: R.l₁).take k).map (·.trees)).sum =
      rootsIn ((G.first.blocksInOrder.take k).flatMap (·.rounds)) := by
  have hlen : (R.p₁ :: R.l₁).length = G.first.blocksInOrder.length := by
    have h5 := congrArg List.length hO.b₁
    simpa only [List.length_map] using h5
  induction k with
  | zero => simp [rootsIn]
  | succ k ih =>
    have hkf : k < G.first.blocksInOrder.length := by omega
    have hk' : k < (R.p₁ :: R.l₁).length := by omega
    have hq : (R.p₁ :: R.l₁)[k]? = some (R.p₁ :: R.l₁)[k] := List.getElem?_eq_getElem hk'
    have hb : G.first.blocksInOrder[k]? = some G.first.blocksInOrder[k] := List.getElem?_eq_getElem hkf
    obtain ⟨-, -, hl, hA⟩ := OnBytes.Road.K4.fits_piece G file D hD R hO ht hd hq hb hk
    rw [List.take_succ, List.take_succ, hq, hb]
    simp only [Option.toList_some, List.map_append, List.sum_append, List.flatMap_append,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, Nat.add_zero]
    rw [ih hkf, rootsIn_append]
    congr 1
    exact trees_of_along _ _ _ hl hA

include hD hO ht hd in
/-- **The first tree of the piece at number k: the roots that the sub-protocols in front declare.**
-/
theorem base_is_roots_flat (h0 : R.p₁.base = 0) {k : ℕ}
    {q : Piece C (frameAt D all D.key₁ R.ft₁) (G.XiPub × G.S₁) G.Cl W}
    (hq : (R.p₁ :: R.l₁)[k]? = some q) :
    q.base = rootsIn ((G.first.blocksInOrder.take k).flatMap (·.rounds)) := by
  have hlen : (R.p₁ :: R.l₁).length = G.first.blocksInOrder.length := by
    have h5 := congrArg List.length hO.b₁
    simpa only [List.length_map] using h5
  have hk : k < G.first.blocksInOrder.length := by
    have h1 := (List.getElem?_eq_some_iff.1 hq).1
    omega
  rw [OnBytes.Road.K4.tiled_base R.l₁ R.p₁ ht k q hq, h0, Nat.zero_add,
    trees_in_front G file D hD R hO ht hd k hk]

include hD hO ht hd in
/-- The same, as the first rounds of the chain's declared rounds. -/
theorem base_is_roots (h0 : R.p₁.base = 0) {k : ℕ}
    {q : Piece C (frameAt D all D.key₁ R.ft₁) (G.XiPub × G.S₁) G.Cl W}
    (hq : (R.p₁ :: R.l₁)[k]? = some q) :
    q.base = rootsIn (G.roundsDeclaredByBlocks.1.take (roundsIn (G.first.blocksInOrder.take k))) := by
  rw [base_is_roots_flat G file D hD R hO ht hd h0 hq]
  congr 1
  have e : G.roundsDeclaredByBlocks.1 = (G.first.blocksInOrder.take k ++ G.first.blocksInOrder.drop k).flatMap (·.rounds) := by
    rw [List.take_append_drop]
    rfl
  rw [e, List.flatMap_append, ← length_flatMap_rounds, List.take_left]

include hD hO ht hd in
/-- **THE FENCE AT THE STATE's OWN LIST.** -/
theorem named_seats_below_base (h0 : R.p₁.base = 0) {seat : Seat G.S₁} {p : Par}
    {b : Block G.S₁ G.Cl} (h : LikeP seat p b) {k : ℕ}
    {q : Piece C (frameAt D all D.key₁ R.ft₁) (G.XiPub × G.S₁) G.Cl W}
    (hq : (R.p₁ :: R.l₁)[k]? = some q) (hk : G.first.blocksInOrder[k]? = some b) (hF : G.planOk = true)
    (rad : OnBytes.OracleShape → Nat) (S : OnBytes.Statement) (book : OnBytes.TreeBook)
    (tl : OnBytes.Model.HTailF2) (L : OnBytes.Model.LinkCtx)
    (hN : Named.namedB p S book tl L = true) (i : Fin (Named.listOf rad S book tl L).length) :
    (Named.seatFn rad S book tl L i).1 < q.base := by
  rw [base_is_roots G file D hD R hO ht hd h0 hq]
  exact named_seats_below_P G h _ _ (cut_at hk) hF rad S book tl L hN i

include hD hO in
/-- The same, from `Three.Fits`. -/
theorem named_seats_below_fits (hf : Three.Fits R) {seat : Seat G.S₁} {p : Par}
    {b : Block G.S₁ G.Cl} (h : LikeP seat p b) {k : ℕ}
    {q : Piece C (frameAt D all D.key₁ R.ft₁) (G.XiPub × G.S₁) G.Cl W}
    (hq : (R.p₁ :: R.l₁)[k]? = some q) (hk : G.first.blocksInOrder[k]? = some b) (hF : G.planOk = true)
    (rad : OnBytes.OracleShape → Nat) (S : OnBytes.Statement) (book : OnBytes.TreeBook)
    (tl : OnBytes.Model.HTailF2) (L : OnBytes.Model.LinkCtx)
    (hN : Named.namedB p S book tl L = true) (i : Fin (Named.listOf rad S book tl L).length) :
    (Named.seatFn rad S book tl L i).1 < q.base :=
  named_seats_below_base G file D hD R hO hf.tiled₁ hf.data₁ hf.base₁ h hq hk hF rad S book tl L
    hN i

end

end VerifiableInference.Desc.First.K8

#print axioms VerifiableInference.Desc.First.K8.trees_of_along
#print axioms VerifiableInference.Desc.First.K8.trees_in_front
#print axioms VerifiableInference.Desc.First.K8.base_is_roots_flat
#print axioms VerifiableInference.Desc.First.K8.base_is_roots
#print axioms VerifiableInference.Desc.First.K8.named_seats_below_base
#print axioms VerifiableInference.Desc.First.K8.named_seats_below_fits
