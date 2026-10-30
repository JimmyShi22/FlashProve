-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/HeadLetters.lean: THE FIRST CHAIN's LAID LETTERS IN THE TERMS
IN WHICH THE LIBRARY's LAWS ARE STATED. Three sets of files ask for these lines:
the library's laws on what one sub-protocol owes take premises of the form "Mg.pub = pubAll D base",
"Mg.more = moreAll", "Mg.pubP = (fillK3 ...).pubP", and stand at the lists `linksFull` and
`flatPlacesOf linksFull true`, or at `IM.linksW` and `IM.placesW`, and at numbers of the form
`N₀.withTold ...`. At `lettersHead` the promise's meaning has the library's `P5J.mgAtAll h`'s
fields (Honest/Thread/FormXKFront.lean); here each of these premises at that meaning and these
lists: by unfolding, or by a call of a lemma of the library. No definition.

  `head_pub_all`, `head_more_all`, `head_pubP_all`   the meaning's three fields
  `head_links_full`, `head_ps_full`, `head_links_W`, `head_ps_W`   the two lists
  `head_N_told`   the numbers end in "withTold" at the written places and what the members tell
                  (`Sound.toldOf`: the library has other functions of that short name)

Limits. The full size and the format's second hash function alone: as the library's head, which is a
premise. Equations on letters: nothing is paid by them. None is one of the library's goals. This
file proves nothing about soundness, completeness, hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FormXKFront
import Johnson.Desc.Sound.MoreAll
import Johnson.Desc.AtSeats.HearAtFifty

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place)
open VerifiableInference.Desc.First (flatPlacesOf pubAll Numbers Meaning)
open VerifiableInference.Desc.Sound (MsgT linksFull moreAll mgBase)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- The public tests are the library's function with code, over the closed meaning's. -/
theorem head_pub_all :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP.pub =
      pubAll h.𝔇.pubD (mgBase : Meaning ProofFile.InstPub WtF).pub := rfl

/-- The list of further public tests is the library's written one. -/
theorem head_more_all :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP.more = moreAll :=
  (VerifiableInference.Desc.Sound.mgAll_more_base h.𝔇).trans
    VerifiableInference.Desc.Sound.mgMore_is

/-- What the public items say beside their Bools: the lookups' filling's, over the first part's: the
library's `mgAll_pubP`, at the head's data and the closed meaning. -/
theorem head_pubP_all :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP.pubP =
      (VerifiableInference.Desc.First.Look.fillK3 (P5J.At.X Zp) h.𝔇.sent
        (VerifiableInference.Desc.First.FillP1.fillP1 h.𝔇.d1 h.𝔇.rw13 h.𝔇.A1 h.𝔇.cr1
          mgBase)).pubP :=
  VerifiableInference.Desc.Sound.mgAll_pubP h.𝔇 mgBase

theorem head_links_full :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).links = linksFull := rfl

theorem head_ps_full :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).ps =
      flatPlacesOf linksFull true := rfl

theorem head_links_W :
    IM.linksW = (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).links :=
  HashBuild.linksW_full

theorem head_ps_W :
    IM.placesW = (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).ps :=
  HashBuild.placesW_full

/-- The numbers end in "withTold", at the written places and at what the chain's members tell. -/
theorem head_N_told :
    ∃ N₀ : Numbers, (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).N =
      N₀.withTold (flatPlacesOf linksFull true)
        (VerifiableInference.Desc.Sound.toldOf cF.blocksInOrder) := ⟨_, rfl⟩

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.head_pub_all
#print axioms ProofFile.Honest.FirstThread.head_more_all
#print axioms ProofFile.Honest.FirstThread.head_pubP_all
#print axioms ProofFile.Honest.FirstThread.head_links_full
#print axioms ProofFile.Honest.FirstThread.head_ps_full
#print axioms ProofFile.Honest.FirstThread.head_links_W
#print axioms ProofFile.Honest.FirstThread.head_ps_W
#print axioms ProofFile.Honest.FirstThread.head_N_told
