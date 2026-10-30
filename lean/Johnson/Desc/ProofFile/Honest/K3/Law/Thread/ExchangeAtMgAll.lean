-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/ExchangeAtMgAll.lean: the honest side of the kind
"lookup" (K3): TWO PREMISES ON THE FILLING of Honest/K3/Law/Thread/ExchangeAll.lean and
ExchangeHeadAll.lean, AT THE LIBRARY'S ONE FILLING OF THE TABLE OF JOINTS (`mgAll`,
Johnson/Desc/Sound/MgAll.lean). Theorems with proofs; no definition.

  `headSuffices_mgAll`   `HeadSuffices` (Honest/K3/Law/Thread/ExchangeHead.lean): that filling lays
                         a guard on the witness's cells in front of the head's arm: the arm gives
                         the field all the more
  `formsT_mgAll`         the field formsT has the text that `all_attention`, `all_layers`,
                         `all_head` ask, at that filling's own letters: the library's own equation
  `formsT_at_mgAll`      the theorem that spends that premise, called there

Each holds at every data and every filling beneath. The first is CONDITIONAL ON the head's place
being there: a test on the public data; no instance of that hypothesis is exhibited in this file.
The like for the field forms: Honest/K3/Law/Thread/FormsAtMgAll.lean. For `K3At`: the library's own
`k3At_mgAll` (Johnson/Desc/Sound/MgAt/K3At.lean).

Limits. Nothing on which data a thread's letters lay.
Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ExchangeHead
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ExchangeField
import Johnson.Desc.Sound.MgAllAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Law.Exchange
open VerifiableInference.Desc (Strs Wit)
open VerifiableInference.Desc.First (Meaning)
open VerifiableInference.Desc.Kinds.Head.Law (headAt)
open VerifiableInference.Desc.Sound
open VerifiableInference.OnPublicFiles

local notation "PlaceL" => VerifiableInference.Desc.First.Look.Place

variable {Xi P Tok : Type} {rows cols nR : Nat} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X) (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))

/-- **The library's one filling meets `HeadSuffices`**, at its own sizes, policy, addresses and
requests. CONDITIONAL ON the head's place being there; no instance of that hypothesis is exhibited
in this file. -/
theorem headSuffices_mgAll {x : PlaceL} (hx : headAt X = some x) :
    @HeadSuffices (k3SizesAt X) (k3PolicyAt X) P (CellsQ rows cols) Tok X 𝔇.sent 𝔇.l3 (k3AdrAt X)
      𝔇.rq x (mgAll 𝔇 Mg) := by
  letI := k3SizesAt X
  letI := k3PolicyAt X
  intro r hr a y w h
  letI := 𝔇.rq a.1
  unfold worthHead at h
  rcases hr with rfl | rfl | rfl
  · rw [mgAll_worth_head_planes 𝔇 Mg hx]
    rw [if_pos rfl] at h
    exact fun _ => h
  · rw [mgAll_worth_head_keys 𝔇 Mg hx]
    rw [if_neg (by decide), if_pos rfl] at h
    exact fun _ => h
  · rw [mgAll_worth_head_rider 𝔇 Mg hx]
    rw [if_neg (by decide), if_neg (by decide), if_pos rfl] at h
    exact fun _ => h

/-- The field formsT of the library's one filling has the text that is asked. -/
theorem formsT_mgAll : (mgAll 𝔇 Mg).formsT = fun m k r a y w =>
    (∀ p ∈ 𝔇.runs m k r,
      formsTQ (𝔇.Rd m) 𝔇.St ((fun m => 𝔇.N.sent m 0) m) p.1 p.2 a.2
        (seatTab 𝔇.cs 𝔇.arr 𝔇.ms w)) ∧ (r = "weights" → 𝔇.wt m a y w) :=
  mgAll_formsT 𝔇 Mg

/-- So `formsT_field` (Honest/K3/Law/Thread/ExchangeField.lean), to which `all_attention`,
`all_layers` and `all_head` hand their premise on the field as it stands, can be called at that
equation. -/
theorem formsT_at_mgAll (m pc piece : Nat)
    (hr : 𝔇.runs m pc "objects" = [(piece, "objects"), (piece, "guests")])
    (a : P × VerifiableInference.Desc.First.S) (y : Strs) (v : Wit (CellsQ rows cols) Tok MsgT)
    (h1 : formsTQ (𝔇.Rd m) 𝔇.St (𝔇.N.sent m 0) piece "objects" a.2 (seatTab 𝔇.cs 𝔇.arr 𝔇.ms v))
    (h2 : formsTQ (𝔇.Rd m) 𝔇.St (𝔇.N.sent m 0) piece "guests" a.2 (seatTab 𝔇.cs 𝔇.arr 𝔇.ms v)) :
    (mgAll 𝔇 Mg).formsT m pc "objects" a y v :=
  formsT_field (mgAll 𝔇 Mg) 𝔇.runs 𝔇.Rd 𝔇.St (fun m => 𝔇.N.sent m 0) (seatTab 𝔇.cs 𝔇.arr 𝔇.ms) 𝔇.wt
    (formsT_mgAll 𝔇 Mg) m pc piece hr a y v h1 h2

#print axioms ProofFile.Honest.K3.Law.Exchange.headSuffices_mgAll
#print axioms ProofFile.Honest.K3.Law.Exchange.formsT_mgAll
#print axioms ProofFile.Honest.K3.Law.Exchange.formsT_at_mgAll

end ProofFile.Honest.K3.Law.Exchange
