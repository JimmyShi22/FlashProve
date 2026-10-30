-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LPFK10R/RoundsLive.lean: THE FIRST CLAUSE («its rounds have the proved sub-protocol's shape») OF THE ROW ON K10's ROUNDS IN THE LIST OF WHAT IS OWED (a text of ours, not in this repository) AT THE PIECES THAT THE MAKER CUTS OF THE PROOF FILE's OWN IOP AS WRITTEN IN LEAN, UNDER THE GATE's OWN YES.
Statements and proofs. (In the Lean names a «block» is a sub-protocol and a «description» the IOP as written in Lean.)
WHY. RoundsAt.lean (beside this file) left its last step untyped: that the data which the road makes of K10's declared rounds are the data at which K10's law is typed. k10_piece_at_desc (Johnson/Desc/First/Close/Law/PieceAtDescK10.lean)
types it at every description whose data return; k10_sits_live (SitsLive.lean) gives, under the gate's yes in scope, the description, its data's return, planOk and the yes of the tests that the laws ask. Here they are joined.
  ix_not_last    at either table of places K10's 25 numbers are not the last: by the kernel.   ix_lt_flat   so, in scope: ixK10 l + 1 < c.blocksInOrder.length.
  descAt Z A B c   the term that the proof file's IOP is, at a first chain c.
  k10_rounds_live  InScope P · readFiles P = .ok pp · protocolDataWellFormed (asDescriptionFiles P) = true: THERE ARE Z, Bs, base, c, A, B WITH: Open … at descAt Z A B c · its data "proof file" return theProofData (asDescriptionFiles P) · AND AT EVERY SUB-PROTOCOL b OF c.blocksInOrder
                   OF THE KIND K10: l < 25, p, Q with k9At Z l = some p · k10Par … = some Q · c.blocksInOrder[ixK10 l]? = some b · AND at every choice of the maker's letters (the three rows' first members, rest₁ rest₂ rest₃, d, wEnd): the first row's
                   piece number ixK10 l of piecesAt … IS pieceOf (held b) base' (dBat Q.rows :: dEps :: Q.k times dTwo) [] (rest₁ …). NO CONDITION ON Q IS LEFT: that both numbers of proof of work are 0 is works_of_written's (WorksLive.lean).
LIMITS. (1) «Both numbers of proof of work are 0» is no condition inside the statement. (2) k10_rounds_live's three premises (in scope · read · protocolDataWellFormed's yes) are shown here of no files. Other Lean files prove them at `VerifierAndGoals.storedPublicFiles` and `VerifierAndGoals.zGap`, not throughout the scope: the first two `VerifierAndGoals.filesRead` (Johnson/Goal/Files/FilesReadProof.lean), the third `theLive_zFull`, `theLive_zGap` (AtFullSide/Top/LiveAtFull.lean, LiveAtPolicies.lean: a side library). Limits there. (3) That dBat | dEps | dTwo
are the proved sub-protocol's rounds' data is RoundsOfPar.lean's (dBat_is and its like): not called here. (4) THE ROW's SECOND CLAUSE (the count of bad challenges is at most the cap) is not here. (5) Q.k and Q.rows are tied to the typed group's numbers by
nobody. (6) base' stands under «there is». At OnBytes.secondHashFunction, in scope; the proof file alone. Nothing on soundness.

-/
import Johnson.LPFK10R.WorksLive
import Johnson.Desc.First.Close.Law.PieceAtDescK10

set_option autoImplicit false

namespace LPFK10
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.First (S ModelPart flatPlacesOf)
open VerifiableInference.Desc.First.Close (Par kind dBat dEps dTwo k10_piece_at_desc)
open VerifiableInference.Desc.Sound (piecesAt held pieceOf)
open OnBytes.Maker OnBytes.Flat KObj
open ProofFile (Cl)
open IM

/-- K10's number is not the last, at either table of places. -/
theorem ix_not_last : ∀ several : Bool, (List.range 25).all (fun l =>
    decide (ixK10 l + 1 < (flatPlacesOf ((List.range 25).map subAt) several).length)) = true := by
  decide +kernel

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

theorem ix_lt_flat (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25) :
    ixK10 l + 1 < c.blocksInOrder.length := by
  obtain ⟨H, several, hf⟩ := chain_first O
  have hp := VerifiableInference.Desc.First.flat_places H _ several c hf
  rw [subs_eq hS hR O] at hp
  have h := List.all_eq_true.1 (ix_not_last several) l (List.mem_range.2 hl)
  have h' := of_decide_eq_true h
  rw [← hp, List.length_map] at h'
  exact h'

end

/-- The term that the proof file's IOP as written in Lean is, at a first chain c. -/
abbrev descAt (Z : ProofFile.Pub) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (c : Chain S Cl) :
    FileDescription ProofFile.Inst :=
  ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c

/-- **K10's ROUNDS AT THE IOP's OWN PIECES, UNDER THE GATE's OWN YES.** -/
theorem k10_rounds_live (P : VerifierAndGoals.PublicFiles) {pp : Inst.Model.ScalesAndPolicy} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp) (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles P) = true) :
    ∃ (Z : ProofFile.Pub) (Bs : ProofFile.PureBase) (base : List (Block S Cl)) (c : Chain S Cl)
      (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat),
      Open OnBytes.secondHashFunction P.pol P.lay P.KL (descAt Z A B c) Z Bs base c A B ∧
      (descAt Z A B c).data "proof file" = .ok (FlashProve.theProofData (VerifierAndGoals.asDescriptionFiles P)) ∧
      ∀ b ∈ c.blocksInOrder, b.place.kind = KindName.K10 →
        ∃ l < 25, ∃ (p : VerifiableInference.Desc.K9.Where) (Q : Par),
          k9At Z l = some p ∧ ProofFile.k10Par Z (ProofFile.k9Stretches Z) p = some Q ∧
          c.blocksInOrder[ixK10 l]? = some b ∧
          (∀ {W : Type} {C : _root_.Run.PQ.CK} (b₁ : Block S Cl) (l₁ : List (Block S Cl))
              (b₂ : Block (descAt Z A B c).S₂ Cl) (l₂ : List (Block (descAt Z A B c).S₂ Cl))
              (b₃ : Block (descAt Z A B c).S₃ Cl) (l₃ : List (Block (descAt Z A B c).S₃ Cl))
              (_ : (descAt Z A B c).first.blocksInOrder = b₁ :: l₁)
              (_ : (descAt Z A B c).shared.blocksInOrder = b₂ :: l₂)
              (_ : (descAt Z A B c).second.blocksInOrder = b₃ :: l₃) rest₁ rest₂ rest₃ (d wEnd : W),
              ∃ base' : ℕ,
                ((piecesAt C (descAt Z A B c) (FlashProve.theProofData (VerifierAndGoals.asDescriptionFiles P)) b₁ l₁ b₂
                    l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).p₁ ::
                  (piecesAt C (descAt Z A B c) (FlashProve.theProofData (VerifierAndGoals.asDescriptionFiles P)) b₁ l₁
                    b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).l₁)[ixK10 l]? =
                  some (pieceOf (held b) base'
                    (dBat Q.rows :: dEps :: List.replicate Q.k dTwo) []
                    (rest₁ (ixK10 l) (dBat Q.rows :: dEps :: List.replicate Q.k dTwo)))) := by
  obtain ⟨F, Z, Bs, base, c, A, B, -, h2, h3, h4, -, O, ⟨rfl, -⟩, -, -, -⟩ :=
    k10_sits_live P hS hR live
  have hw := (VerifiableInference.PlanWritten.seat_in_scope _ _ P hS
    (h4 _ List.mem_cons_self : VerifiableInference.PlanWritten.seatPinnedProof P.pol
      (descAt Z A B c) = true)).1
  refine ⟨Z, Bs, base, c, A, B, O, h3, fun b hb hk => ?_⟩
  obtain ⟨l, hl, Lk, p, Q, -, e2, e3, -, e5, e6⟩ := k10_sits_each hS hR O b hb hk
  obtain ⟨w1, w2⟩ := works_of_written hw (b := b) hb (alone_rounds e6) (one_le_k h2 hb e6)
  refine ⟨l, hl, p, Q, e2, e3, e5, fun {W C} b₁ l₁ b₂ l₂ b₃ l₃ g₁ g₂ g₃ rest₁ rest₂ rest₃ d wEnd =>
    ?_⟩
  have hs : (descAt Z A B c).sealLast = true := by
    have := h2
    unfold FileDescription.planOk at this
    exact (Bool.and_eq_true _ _ ▸ this).2
  exact k10_piece_at_desc (Cl' := Unit) (descAt Z A B c) "proof file" _ h3 hs b₁ l₁ b₂ l₂ b₃ l₃ g₁
    g₂ g₃ rest₁ rest₂ rest₃ d wEnd (ixK10 l) b e5 (ix_lt_flat hS hR O hl) Q w1 w2
    (alone_rounds e6)

end LPFK10

#print axioms LPFK10.k10_rounds_live
#print axioms LPFK10.ix_not_last
#print axioms LPFK10.ix_lt_flat
