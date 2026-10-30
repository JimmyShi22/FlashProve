-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No witness and no real list of rounds is shown at which all premises hold.
Johnson/Desc/First/Look/K3CopiesRead.lean: THE PREMISE SymsAre
(Johnson/Goal/Meaning/ReadingsOneLook.lean) AT THE FAMILY OF READINGS THAT hidAtSeat
READS: msgF k := the witness's messages as segment k reads them (Desc.Sound.readAt,
Johnson/Desc/Sound/ReadAt.lean): the family's member k has, at the seats of sub-proof k, the symbols
of the witness's own tuple of link k (msgsOf: the tuple of which the closed caller's relation
speaks). A joining: symsAre_witness (Johnson/Desc/First/Look/K3CopiesOne.lean, at the one reading by
numbers) and readAt_offPad (ReadAt.lean: outside the pads every segment reads the one
component that all copies share). hidAtSeat: Johnson/P5J/MeansQ.lean. NO SOUNDNESS IS CLAIMED.

OBJECT: no text that runs: two readings of a witness of the table of joints.
USER: K3CallsModelFits.lean (symsAre_readAt_att, symsAre_readAt_lay),
  Johnson/Desc/First/Att/Door/Law/K5CellsAny.lean (symsAre_readAt); 13 more files name OwnNamed.
  Meant: the premise hm of att_model_hid, lay_model_hid
  (Johnson/Desc/First/Look/K3CallsModelAt.lean).
LETTERS: those of K3CopiesOne.lean; ms, N: the table's list of members and its numbers.

THE PREMISES, ALL ON PUBLIC LETTERS: T (linkTieB) · O (OneNumber at wn := id: the member's number is
  the label's, and the place is no pad's place of the list's own member) · Own (OwnNamed: at every
  seat of sub-proof k: segment k's group has just one tenant with that number, and the place is no
  pad's place of any member of ms that sits there) · hg (GroupsSeated).

Main names: `OwnNamed`, `symsAre_readAt`, `symsAre_readAt_att`, `symsAre_readAt_lay`.

Limits. A rule over letters: none of the four premises is shown at any list of rounds.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3CopiesOne
import Johnson.Desc.Sound.ReadAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.Sound (MsgT msgsOf Mem namedOnce GroupsSeated OffPad readAt_offPad)
open VerifiableInference.Desc.First.Look (Sent sigListCalls szOf ownPart)
open _root_.Meaning (Msgs SymsAre linkTieB fLay labAt)

section
variable {Cells Tok : Type} (X : Verify.Public) (D : Sent) (num : ℕ → ℕ → ℕ) (tls : ℕ → HTailF2)
  (k : ℕ) (arr : ℕ → ℕ → ℕ) (ms : List Mem) (N : Numbers)

/-- **The premise on the table's numbers**: at every seat of sub-proof k. -/
def OwnNamed : Prop :=
  ∀ μ i c : ℕ, μ < (szOf (tls k)).NM → i < Alg.symRows ((szOf (tls k)).m μ) →
    c < (szOf (tls k)).k μ →
    namedOnce arr N k (fLay D.layout num (labAt X k μ) i c).1 = true ∧
      OffPad D.codes arr ms N k (fLay D.layout num (labAt X k μ) i c).1
        (fLay D.layout num (labAt X k μ) i c).2.1 (fLay D.layout num (labAt X k μ) i c).2.2

variable {X D num tls k arr ms N} {rad : OracleShape → ℕ} {idx : ℕ → ℕ}
  {seatT : Fin (sigListCalls D rad k).length → ℕ × ℕ}

/-- **SymsAre at the family "as segment k reads them".** -/
theorem symsAre_readAt (T : linkTieB X D rad num idx k (tls k) = true)
    (O : OneNumber X D rad num idx tls k seatT arr id) (Own : OwnNamed X D num tls k arr ms N)
    (hg : GroupsSeated ms N) (w : Wit Cells Tok MsgT) :
    SymsAre X D rad num idx tls (fun j => Desc.Sound.readAt D.codes arr ms N j w) k
      (msgsOf D.codes (sigListCalls D rad k) seatT arr w) := by
  have h0 := symsAre_witness T O w
  unfold SymsAre at h0 ⊢
  rw [← h0]
  funext μ i' c
  obtain ⟨o1, o2⟩ := Own μ.val i'.val c.val μ.isLt i'.isLt c.isLt
  exact readAt_offPad D.codes arr ms N k _ _ _ w o1 hg o2

end

section
variable {Cells Tok : Type} {X : Verify.Public} {D : Sent} {rad : OracleShape → ℕ}
  {num : ℕ → ℕ → ℕ} {idx : ℕ → ℕ} {tls : ℕ → HTailF2} {x : Desc.First.Look.Place}
  {seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ} {arr : ℕ → ℕ → ℕ} {ms : List Mem}
  {N : Numbers}

/-- **hm at an attention link.** -/
theorem symsAre_readAt_att (T : linkTieB X D rad num idx x.link (tls x.link) = true)
    (O : OneNumber X D rad num idx tls x.link seatT arr id)
    (Own : OwnNamed X D num tls x.link arr ms N) (hg : GroupsSeated ms N)
    (w : Wit Cells Tok MsgT) :
    SymsAre X D rad num idx tls (fun j => Desc.Sound.readAt D.codes arr ms N j w) x.link
      (attMs x D rad seatT arr w) :=
  symsAre_readAt T O Own hg w

/-- **hm at a layers' link.** -/
theorem symsAre_readAt_lay {oW : Cb.OMsg Cb.Gl.E} (msgW : Wit Cells Tok MsgT → oW.Msg)
    (T : linkTieB X D rad num idx x.link (tls x.link) = true)
    (O : OneNumber X D rad num idx tls x.link seatT arr id)
    (Own : OwnNamed X D num tls x.link arr ms N) (hg : GroupsSeated ms N)
    (w : Wit Cells Tok MsgT) :
    SymsAre X D rad num idx tls (fun j => Desc.Sound.readAt D.codes arr ms N j w) x.link
      (ownPart (layMs x D rad oW seatT arr msgW w)) :=
  symsAre_readAt T O Own hg w

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.symsAre_readAt
#print axioms VerifiableInference.OnPublicFiles.symsAre_readAt_att
#print axioms VerifiableInference.OnPublicFiles.symsAre_readAt_lay
