-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/LedgerNumbers.lean: THE NUMBERS OF TREES AGAINST THE PIECES' BASES, AT A TILED
ROW OF THE SHARED CHAIN AND AT THE TENANTS tenantSh (Johnson/Desc/Sound/SharedMembers.lean): binders
of ledger_at_cap | ledger_whole (Johnson/Desc/K14/Law/LedgerAtCap.lean): hlo, tU, tO, tS, hb2; hw,
hi; htree2, htree5.

  along_len         a piece of a tiled row with nothing put behind it: its written rounds are as
                    many as its block declares.
  numbers_of_tiled  the bases of "LIN point"'s piece and of the pieces 2 and 5; o_u's tree lies
                    below piece 3's base, o_omega's and o_sp's below piece 6's; all three from the
                    row's first base on.
  own_of_sorted     W's and the index masks' trees lie below N.lo, from the table's own test.
  seed_trees        the first written round of a sending sends as many trees as its layout has.
  htree_of_seats    htree2 | htree5's form, for a family of members of which number k sits in the
                    tree that the layout gives message number k.
HOW. bases (Johnson/Desc/K14/Law/LedgerBases.lean) · tU_sh, tO_sh, tS_sh, hlo_sh
(Johnson/Desc/Sound/SeamTreesSh.lean) · places, lengths, sizeOmega
(Johnson/Desc/K14/Law/PlanShapes.lean) · seedRounds (Johnson/Desc/K14/Law/LedgerSeedRounds.lean) ·
lay_lt · roots_send (LedgerBases.lean).
WHO PAYS numbers_of_tiled's PREMISES: the tiling, "along" and the first base: row_of_cut
(Johnson/Desc/K14/Law/LedgerRowOfCut.lean) · the six equations on declared rounds: rfl at the forms
that letters_of_cut gives (Johnson/Desc/K14/Law/LedgerLettersOfCut.lean), hx3 at piece 3,
front_of_chain at the front · hN: by the choice of N.tenant, at lo := the row's first base.
WHAT IS LEFT: N.sorted (own_of_sorted), which says of the first chain's numbers N₁.w, N₁.index that
their trees lie below the shared chain's first · hs (htree_of_seats): where the family memK2 | memK5
sits: no term for these letters lies on a ground.
What is not claimed. What is left. No instance. Nothing on soundness.

-/
import Johnson.Desc.K14.Law.LedgerBases
import Johnson.Desc.Sound.SeamTreesSh
import Johnson.Desc.K14.Law.PlanShapes
import Johnson.Desc.K14.Law.LedgerSeedRounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Maker
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared
open _root_.Run.PQ (CK)
open Desc.K14.Law.Fence (tenantSh tU_sh tO_sh tS_sh hlo_sh)

/-- A piece with nothing put behind it has as many written rounds as its block declares. -/
theorem along_len {C : CK} {Fr : Frame} {S Cl W : Type} (num : Fmt.TreeSource → ℕ)
    (x : Piece C Fr S Cl W) (b : Block St Unit) (hr : x.b.rounds = b.rounds) (ho : x.Owed)
    (hk : x.back = []) (ha : Along (RoundIs num) x.b.rounds x.ds) :
    Along (RoundIs num) b.rounds x.ds ∧ x.ds.length = b.rounds.length := by
  have h := ho.1
  rw [hk, hr] at h
  rw [hr] at ha
  exact ⟨ha, h⟩

/-- **The numbers, at a tiled row.** -/
theorem numbers_of_tiled (Q : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (sentU : Array OracleNotice) (layU layO : TreeLay)
    (hbl : blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8]) (hU : withU Q.S = some sentU)
    (hlU : layTrees Q.codes sentU = some layU)
    (hlO : layTrees Q.codes (withOmega Q.S) = some layO) (hS : Q.S.sharedSplitNeeded = true)
    {C : CK} {Fr : Frame} {S Cl W : Type} (num : Fmt.TreeSource → ℕ)
    (f pt x2 x3 x4 x5 x6 : Piece C Fr S Cl W) (rest : List (Piece C Fr S Cl W))
    (ht : Tiled f (pt :: x2 :: x3 :: x4 :: x5 :: x6 :: rest)) (hfr : f.b.rounds = [])
    (hr1 : pt.b.rounds = b1.rounds) (hr2 : x2.b.rounds = b2.rounds)
    (hr3 : x3.b.rounds = b3.rounds) (hr4 : x4.b.rounds = b4.rounds)
    (hr5 : x5.b.rounds = b5.rounds)
    (hal : ∀ p ∈ [pt, x2, x3, x4, x5], Along (RoundIs num) p.b.rounds p.ds) (N : NumbersS)
    (hN : N.tenant = tenantSh f.base layU layO) :
    pt.base = f.base ∧ x2.base = f.base ∧ x5.base = f.base + layU.shapes.size ∧
      (N.tenant .oU).1 < x3.base ∧ (N.tenant .oOmega).1 < x6.base ∧
      (N.tenant .oSp).1 < x6.base ∧ ∀ m, f.base ≤ (N.tenant m).1 := by
  have ht' := ht
  obtain ⟨o0, -, -, -, o1, -, k1, -, o2, -, k2, -, o3, -, k3, -, o4, -, k4, -, o5, -, k5, -⟩ := ht'
  have hf : f.ds = [] := by
    have h := o0.1
    rw [hfr] at h
    exact List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_add_eq_zero_right h)
  obtain ⟨e1, e2, e3, e5, e6⟩ := bases Q b1 b2 b3 b4 b5 b6 b7 b8 sentU layU layO hbl hU hlU hlO C
    Fr S Cl W num f pt x2 x3 x4 x5 x6 rest ht hf (by
      intro y hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl
      · exact along_len num pt b1 hr1 o1 k1 (hal pt (by simp))
      · exact along_len num x2 b2 hr2 o2 k2 (hal x2 (by simp))
      · exact along_len num x3 b3 hr3 o3 k3 (hal x3 (by simp))
      · exact along_len num x4 b4 hr4 o4 k4 (hal x4 (by simp))
      · exact along_len num x5 b5 hr5 o5 k5 (hal x5 (by simp)))
  have sU : 0 < sentU.size := (lengths Q sentU).1 ▸ (places Q sentU).1 hU
  have sO : 1 < (withOmega Q.S).size := by
    rw [sizeOmega Q.S hS]
    decide
  refine ⟨e1, e2, e5, ?_, ?_, ?_, fun m => ?_⟩
  · rw [hN, e3]
    exact tU_sh f.base layU layO Q.codes sentU hlU sU
  · rw [hN, e6]
    exact tO_sh f.base layU layO Q.codes (withOmega Q.S) hlO sO
  · rw [hN, e6]
    exact tS_sh f.base layU layO Q.codes (withOmega Q.S) hlO sO
  · rw [hN]
    exact hlo_sh f.base layU layO m

/-- W's and the index masks' trees lie below the shared chain's first, from the table's test. -/
theorem own_of_sorted (N : NumbersS) (hs : N.sorted = true) :
    N.w.1 < N.lo ∧ N.index.1 < N.lo := by
  unfold NumbersS.sorted at hs
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
  exact ⟨hs.1.2, hs.2⟩

/-- The trees of K1's parameters at one of the two sendings are the layout's. -/
theorem trees_parK1 (Q : P14) (piece : ℕ) (part : String) (sent : Array OracleNotice)
    (lay : TreeLay) (hl : layTrees Q.codes sent = some lay) :
    (parK1 Q piece part sent).trees.length = lay.shapes.size := by
  have h := roots_send Q piece part sent lay hl
  have h' : ((parK1 Q piece part sent).trees.length + (0 + 0) : ℕ) = lay.shapes.size := h
  omega

/-- **The first written round of a sending sends as many trees as its layout has.** -/
theorem seed_trees (Q : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (sentU : Array OracleNotice) (layU layO : TreeLay)
    (hbl : blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8]) (hU : withU Q.S = some sentU)
    (hlU : layTrees Q.codes sentU = some layU)
    (hlO : layTrees Q.codes (withOmega Q.S) = some layO) (num : Fmt.TreeSource → ℕ) (d₁ d₂ : RDT) :
    (Along (RoundIs num) b2.rounds [d₁, d₂] → d₁.trees.length = layU.shapes.size) ∧
      (Along (RoundIs num) b5.rounds [d₁, d₂] → d₁.trees.length = layO.shapes.size) := by
  obtain ⟨h2, h5⟩ := seedRounds Q b1 b2 b3 b4 b5 b6 b7 b8 sentU hbl hU num d₁ d₂
  exact ⟨fun h => (h2 h).2.2.trans (trees_parK1 Q 2 _ sentU layU hlU),
    fun h => (h5 h).2.2.trans (trees_parK1 Q 5 _ _ layO hlO)⟩

/-- **htree2 | htree5's form**, where member number k sits in the tree that the layout gives
message number k, counted from the sending's first tree b. -/
theorem htree_of_seats (codes : Codes) (sent : Array OracleNotice) (lay : TreeLay)
    (hl : layTrees codes sent = some lay) {L : ℕ} (hL : L = sent.size) (memK : Fin L → Mem)
    (b T : ℕ) (hT : T = lay.shapes.size)
    (hs : ∀ k, ((memK k).1.seat (memK k).2).1 = b + lay.tree.getD k.val 0) :
    ∀ k, ∃ j, ((memK k).1.seat (memK k).2).1 = b + j ∧ j < T := fun k =>
  ⟨_, hs k, by
    rw [hT]
    exact OnBytes.Tie.Pv.Keeps.Fit.lay_lt hl (hL ▸ k.isLt)⟩

end Desc.K14.Law

#print axioms Desc.K14.Law.along_len
#print axioms Desc.K14.Law.numbers_of_tiled
#print axioms Desc.K14.Law.own_of_sorted
#print axioms Desc.K14.Law.trees_parK1
#print axioms Desc.K14.Law.seed_trees
#print axioms Desc.K14.Law.htree_of_seats
