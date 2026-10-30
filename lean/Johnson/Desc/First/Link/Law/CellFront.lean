-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/CellFront.lean: THREE FIELDS OF THE LOOKUPS' `CellOkR`
(Johnson/Top/H/Keep/DigitsCell.lean: frame · lay · arr), AND THE FIRST HALF OF A FOURTH (the frame
finds the own message of a seat), AT EVERY PART THAT THE BATCHING's LENS READS AT A STATE REACHED AT
A LINK's BATCHING's FRONT, AT THE LOOKUPS' PUBLIC VALUES `sentAt Z`. By calls. Theorems. It changes
no other file.

  `frameIs_of`, `lay_of`, `arr_of`, `oracle_of`: from `FrameAtLink` (FrameFindsOf.lean) on one part,
    at any D with the first chain's shape | layout | the built link's list of names.
  `sent_arr`: (sentAt Z).arrayOf.getD l #[] is the blank letters' link's list of names.
  `cell_front`: **FrameIs (sentAt Z) l a.L.check.frame ∧ a.L.check.rows.layout = (sentAt Z).layout ∧
    a.L.arrayOf = (sentAt Z).arrayOf.getD l #[] ∧ ∀ k below the number of the link's messages,
    oracleOfMsg a.L.check.frame 0 k is some.**
Limits. `CellOkR`'s seat (which seat; the statement's bits) and laid are not treated. The link has
at most three moments: a premise on the public part. In scope, at secondHashFunction alone. No member. Nothing
on soundness.
-/
import Johnson.Desc.First.Link.Law.FrameAtFront
import Johnson.Desc.First.Att.K05SeatsOne
import Johnson.Desc.First.Att.K05DoorB

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open Inst.Model
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open OnBytes.Params (ReqLink)
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Look (Sent)
open VerifiableInference.Desc.First.Att.P (FrameIs born_of_groups oracleOfMsg)
open Meaning.K2 (sentAt)
open Johnson.Desc.First.Walk.Tied (Reach)
open IM (nAt)
open ProofFile (Cl)

section
variable {first : Params.First} {l : ℕ} {Xl : LinkH} {a : K9.Part} {D : Sent}

theorem frameIs_of (H : FrameAtLink first l Xl a) (hs : D.shape = first.shape) :
    FrameIs D l a.L.check.frame :=
  ⟨H.shape.trans hs.symm, born_of_groups (by rw [H.groups, hs]) H.link, H.link, H.next⟩

theorem lay_of (H : FrameAtLink first l Xl a) (hl : D.layout = first.layout) :
    a.L.check.rows.layout = D.layout := H.layout.trans hl.symm

theorem arr_of (H : FrameAtLink first l Xl a) (ha : D.arrayOf.getD l #[] = Xl.arrayOf) :
    a.L.arrayOf = D.arrayOf.getD l #[] := H.names.trans ha.symm

theorem oracle_of (H : FrameAtLink first l Xl a) {L : ReqLink}
    (hL : first.shape.link[l]? = some L) {k : ℕ} (hk : k < L.messages.length) :
    ∃ o, oracleOfMsg a.L.check.frame 0 k = some o := by
  have h : k < a.L.check.frame.own.size := by rw [H.own L hL]; exact hk
  exact ⟨a.L.check.frame.own[k], by
    unfold oracleOfMsg
    simp [h]⟩

end

variable {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

theorem sent_arr {mk : ProofFile.LinksBy} {G : ProofFile.Ground} (h : ProofFile.blankBy mk Z = some G) {l : ℕ}
    {Xl : LinkH} (e3 : G.built[l]? = some Xl) : (sentAt Z).arrayOf.getD l #[] = Xl.arrayOf :=
  (Meaning.K2.built_arr h e3).symm

/-- **AT THE BATCHING's FRONT, AT THE LOOKUPS' PUBLIC VALUES.** -/
theorem cell_front (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl)
    (h3 : ∀ L, Z.first.shape.link[l]? = some L → reqMoments L ≤ 3) {y : ProofFile.InstPub × S}
    (hr : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + nAt l + 2) y) {a : K9.Part}
    (ha : atS.get? y.2 = some a) :
    FrameIs (sentAt Z) l a.L.check.frame ∧ a.L.check.rows.layout = (sentAt Z).layout ∧
      a.L.arrayOf = (sentAt Z).arrayOf.getD l #[] ∧
      ∀ L, Z.first.shape.link[l]? = some L → ∀ k, k < L.messages.length →
        ∃ o, oracleOfMsg a.L.check.frame 0 k = some o := by
  have H := frameAtLink_front hS hR O hl e3 h3 hr ha
  exact ⟨frameIs_of H rfl, lay_of H rfl, arr_of H (sent_arr O.blank e3),
    fun L hL k hk => oracle_of H hL hk⟩

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.frameIs_of
#print axioms VerifiableInference.Desc.LinkJoin.oracle_of
#print axioms VerifiableInference.Desc.LinkJoin.cell_front
