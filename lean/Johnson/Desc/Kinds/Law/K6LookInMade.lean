-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6LookInMade.lean: THE SUB-PROTOCOL AT THE OUTPUT HEAD MAKES THE PUBLIC TEST
lookIn 24 8 (the condition in front of the lookup on the digits), AT THE COMPOSED MEANING OF THE
OPEN CLAIMS (Johnson/Desc/Sound/MgAll.lean: mgAll). One statement with its proof.

By K6's files' maker's lemma (Law/K6Makes.lean: lookIn_below). What that lemma asks of the
verifier's state in front comes from the public sentence "what the lookup on the calls left"
(Law/K6LeftSays.lean: left_says: the ledger's next free number as an equation; its number of
slots; that all is free from there on; the size of the first point that was heard) and from two
facts that are asked here in the letters in which another of K6's files concludes them off
the table's promise (hrows, hlk).

WHAT IT IS NOT. An implication. Nothing on soundness. PREMISES: the sentence (left) · hrows · hlk ·
K6Left · ON PUBLIC PARAMETERS ALONE: planB · hsort8 (piece 8 of segment 24 is the lookup on the
digits) · hp8, hsh8 (its place is there and makes a shape) · hnum: THREE FACTS ON NUMBERS: the
calls' first slot, the calls' number of hidden values and what the head's hearing takes give the
digits' first slot; the digits' hidden values have room; the first point that the lookup on the
calls hears has lt coordinates at least. No values are shown at which the premises hold together.
LETTERS. No letter stands under "there is" in the conclusion. In hlk: L: pinned by a.1.2.link?.

-/
import Johnson.Desc.Kinds.Law.K6PubMore
import Johnson.Desc.Kinds.Law.K6LeftSays
import Johnson.Desc.First.Look.K3CallsAddress

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable

open OnBytes
open OnBytes.Maker OnBytes.Flat Johnson.Pack
open VerifiableInference.OnPublicFiles.Flat (GE)
open VerifiableInference.Desc.First (S Meaning Pub)
open VerifiableInference.Desc.Sound (Piece Frame MsgT MgData mgAll)

variable {Xi P Tok : Type} {rows cols nR : ℕ} {Wp : OnBytes.Model.Verify.Public}
  (D : MgData Xi P Tok rows cols nR Wp)
  (Mg : Meaning P (Wit (Fin rows → Fin cols → GE) Tok MsgT)) {fld : Fmt.Fld} {Fr : Frame}
  {q : Piece (_root_.Run.ckP fld) Fr (P × S) Claim (Wit (Fin rows → Fin cols → GE) Tok MsgT)}
  {bef : List (ℕ × ℕ)} {B bS : Block S Claim}

/-- **BEHIND AN ACCEPT OF THE SUB-PROTOCOL AT THE OUTPUT HEAD THE CONDITION IN FRONT OF THE LOOKUP
ON THE DIGITS HOLDS.** a: the state in front; b: behind. -/
theorem made_lookIn (H : Seated Wp fld Fr q 24 bef B bS) (hplan : planB Wp = true)
    (a b : (P × S) × Fr.E.Str) (τ : Iop.Tr (uLT (_root_.Run.ckP fld) q.ds))
    (hb : q.ior.red.out a τ = some b) (hL : K6Left Wp a.1.2)
    (left : VerifiableInference.OnPublicFiles.k3LeftItemAt Wp 24 a.1.2)
    (hrows : First.Tape.RowsOwed.noneWaits a.1.2.rowsOwed = true)
    (hlk : (∃ L, a.1.2.link? = some L ∧ L.link = 24 ∧ L.arrayOf = D.sent.arrayOf.getD 24 #[]) ∧
      (a.1.2.tl?.bind (·.heard)).isNone = true)
    (hsort8 : First.Look.k3SortAt Wp 24 8 = some true) (p8 : First.Look.P)
    (hp8 : First.Look.placeAt Wp 24 true = some p8) (sh8 : OnBytes.Model.Forest.Shape)
    (hsh8 : p8.shape = some sh8)
    (hnum : ∀ p3 h3, First.Look.placeAt Wp 24 false = some p3 → p3.shape = some h3 →
      p3.first + OnBytes.Model.Forest.elems h3 + takesOf (parOf Wp.hS (workOf Wp)) = p8.first ∧
        p8.first + OnBytes.Model.Forest.elems sh8 ≤ p3.ns ∧
        (parOf Wp.hS (workOf Wp)).sizes.lt ≤ h3.dT) :
    (mgAll D Mg).pub (.lookIn 24 8) b.1 = true := by
  obtain ⟨p3, hp3, L3⟩ := left
  obtain ⟨h3, F, g, hs3, hF, hg, Y, _⟩ := left_says p3 a.1.2 L3
  obtain ⟨n1, n2, n3⟩ := hnum p3 h3 hp3 hs3
  obtain ⟨b6, rs, gs, h6, hd⟩ := below_yes_seated H a b τ hb
  obtain ⟨x8, hx8, rfl⟩ := Option.map_eq_some_iff.1 hp8
  have hl8 : x8.link = 24 := VerifiableInference.OnPublicFiles.lookAt_link hx8
  have K := lookIn_below Wp 24 b6 h6 a.1.2 b.1.2 rs gs hd (k6On_front H hplan a b τ hb hL) g hg
    (by rw [Y.zx]; exact n3) _ sh8 hsh8 rfl (D.sent.arrayOf.getD 24 #[]) F hF
    (by rw [Y.next]; exact n1) (by rw [Y.ns]; exact n2) Y.free hlk.2 hrows (by
      obtain ⟨L, e1, e2, e3⟩ := hlk.1
      rw [e1]
      show (L.link == x8.link && L.arrayOf == D.sent.arrayOf.getD 24 #[]) = true
      rw [e2, e3, hl8]
      simp)
  rw [Sound.mgAll_pub, First.pubAll_lookIn D.pubD Mg.pub 24 8 true hsort8]
  show First.Look.lookInC (First.Look.K3Data.of Wp D.sent) 24 true b.1.2 = true
  rw [First.Look.lookInC_is]
  unfold First.Look.k3LookInAt
  rw [hp8]
  exact K

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.made_lookIn
