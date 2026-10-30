-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LPFK10R/HeadLinkJoins.lean: THE HEAD's LINK (l = 24): THE LAST OF THE 75 NUMBERS OF THE FIELD close (see room_close_all); AND THE FLAGS OF ITS GROUP. Statements and proofs.
  ownIn_head       InScope P · readFiles P = .ok pp · IM.Open secondHashFunction P.pol lay P.KL F Z Bs base c A B: OwnInAt c (ProofFile.startS Z) 24 (OwnInAt.lean): at every state reached in front of the head's link's one equation (number 349) the link's own messages are members of group 24.
  ownIn_all        the same three: OwnIn c (ProofFile.startS Z) (RoomClose.lean): all 25 links.
  room_close_all   the same three: THE FIELD close OF KeepShares (Johnson/P1L20R/RoomKeep.lean), ITS OWN TEXT, at start := ProofFile.startS Z: all 75 numbers: NO PREMISE BEYOND SCOPE AND Open.
  flags_at_head    the same three, with hsh : Z.first.shape = shapeFull: at the fold's cuts 340 + n, 5 ≤ n ≤ 10 (n = 10: in front of K10): group 24's members: no number twice; its flags are (joinersAt shapeFull 24).map (·.2): flags_at_cut (ShapesAtCut.lean) at the head's link.
BY: members_head and flags_head (Johnson/IMR/HeadMembers.lean) · reach_fold · ownIn_real, room_close_real (OwnInAt.lean) · flags_join_full (Johnson/Desc/First/Close/Law/FlagsJoin.lean).
LIMITS. At the start ProofFile.startS Z alone; in scope; at OnBytes.secondHashFunction. One field of thirteen. hsh is a premise of flags_at_head ((P1): not laid). ShapesAre at the head's link is not typed here (it wants the members' shapes, as at the other links). Link 0's flags: not treated. THE SET OF FILES OVER WHICH THIS FILE WAS WRITTEN IS NO CLEAN COPY OF A LISTED SET: a copy of
AN EARLIER SET OF THIS PROJECT's LEAN FILES, WITH FILES OF THREE OTHER SETS LAID UNCHANGED, five of them in the place of an elder version that that set has (listed, by program, in a text of ours, not in this repository); among them the version of Johnson/IMR/FrameAll.lean then laid, which its writers call a working state. No soundness statement.

-/
import Johnson.LPFK10R.OwnInAt
import Johnson.LPFK10R.ShapesAtCut
import Johnson.IMR.HeadMembers

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace LPFK10

open OnBytes
open VerifiableInference.Desc (Block Chain FileDescription foldBlocks)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Close (joinersAt flags_join_full)
open VerifiableInference.Desc.ReqLit
open Johnson.Desc.First.Walk.Tied
open ProofFile (Cl)
open P1L20 (nA)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **OwnIn's SENTENCE AT THE HEAD's LINK.** -/
theorem ownIn_head (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    OwnInAt c (ProofFile.startS Z) 24 := by
  intro z s hr L hL o ho
  obtain ⟨-, rs, cols, g⟩ := reach_fold.1 hr
  have e : 14 * 24 + nA 24 + 4 = 340 + 9 := by decide
  rw [e] at g
  obtain ⟨L', G, n₀, h1, -, -, h4, h5, -, -⟩ :=
    Meaning.K2.members_head hS hR O (n := 9) (by omega) g
  obtain rfl : L = L' := Option.some.inj (hL.symm.trans h1)
  refine ⟨G, Array.mem_of_getElem? h4, ?_⟩
  rw [h5]
  exact Array.mem_append_right _ ho

/-- **OwnIn AT THE REAL CHAIN AND ITS OWN START: NO PREMISE BEYOND SCOPE AND Open.** -/
theorem ownIn_all (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) : OwnIn c (ProofFile.startS Z) :=
  ownIn_real hS hR O (ownIn_head hS hR O)

/-- **THE FIELD close OF KeepShares, TO THE LETTER, AT THE REAL CHAIN AND ITS OWN START: ALL 75 NUMBERS: NO PREMISE BEYOND SCOPE AND Open.** -/
theorem room_close_all (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∀ l < 25, ∀ p Q j (x : Block S Unit), IM.k9At Z l = some p →
      ProofFile.k10Par Z (ProofFile.k9Stretches Z) p = some Q →
      (VerifiableInference.Desc.K9.closeOf p Q : List (Block S Unit))[j]? = some x →
      P1L20.KeepsAt c (ProofFile.startS Z) (14 * l + nA l + 4 + j) (x.retype : Block S Cl) :=
  room_close_real hS hR O (ownIn_head hS hR O)

/-- **THE HEAD's LINK's GROUP's FLAGS ARE THE JOINERS'**, at the cuts 340 + n, 5 ≤ n ≤ 10, where the first chain's shape is the written one. -/
theorem flags_at_head (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hsh : Z.first.shape = shapeFull) {p : ProofFile.InstPub} {R : List Fmt.RoundView}
    {C : List VerifiableInference.Desc.OpenedColumn} {n : ℕ} (h5 : 5 ≤ n) (hn : n ≤ 10) {t : S}
    {r : List Fmt.RoundView} {q : List VerifiableInference.Desc.OpenedColumn}
    (g : foldBlocks 0 (c.blocksInOrder.take (340 + n)) (ProofFile.startS Z p) R C = .ok (t, r, q)) :
    ∃ G : Group, t.st.groups[24]? = some G ∧ G.members.toList.Nodup ∧
      G.kept.toList = (joinersAt shapeFull 24).map (·.2) := by
  obtain ⟨G, a1, a2⟩ := Meaning.K2.flags_head hS hR O h5 hn g
  obtain ⟨-, G', -, -, -, -, b4, -, -, b7⟩ := Meaning.K2.members_head hS hR O hn g
  obtain rfl : G = G' := Option.some.inj (a1.symm.trans b4)
  refine ⟨G, a1, b7, ?_⟩
  rw [a2, hsh]
  exact flags_join_full (f := VerifiableInference.Desc.First.K2.frameAtLink shapeFull 24)
    (by omega) (by omega) rfl rfl

end LPFK10

#print axioms LPFK10.ownIn_head
#print axioms LPFK10.ownIn_all
#print axioms LPFK10.room_close_all
#print axioms LPFK10.flags_at_head
