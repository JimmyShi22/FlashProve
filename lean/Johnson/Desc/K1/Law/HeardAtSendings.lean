-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/HeardAtSendings.lean: hheard: IN FRONT OF THE OUTPUT HEAD's TWO LATER SENDINGS
(numbers 342 and 344) THE HEAD's READER ANSWERS: the premise of the laws hwt_whole | hwtR_of
(WtAt24.lean | WtBackAtReads.lean), off the form InAt of the table's promise, at any meaning whose
public tests at the two items are the composed meaning's; and at K1's top's wider meaning mw1.
Four theorems: calls.

  hheard_342 · hheard_344        heard_of_ownT | heard_of_own
                                 (Johnson/Desc/Kinds/Law/WeightHeardOfPub.lean)
                                 after ownT_held_342 | own_held_344 (OwnHeldAtSendings.lean).
  hheard_342_mw1 · hheard_344_mw1  at Mw := mw1 N' D' dk (mgAll D Mg): the equation of tests is rfl.
LEFT: those laws' own three: hreaders (segment 24's readers are the link's) · hown (the claim's
three runs) · K (K6States).
What is not claimed. That the three can be met. Nothing on soundness.

-/
import Johnson.Desc.K1.Law.OwnHeldAtSendings
import Johnson.Desc.K1.Law.K01FiftyR
import Johnson.Desc.Kinds.Law.WeightHeardOfPub

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1
open VerifiableInference.OnPublicFiles.Flat (GE)
open VerifiableInference.Desc (Link Claim Strs Wit)
open VerifiableInference.Desc.First (S Meaning Numbers flatPlacesOf)
open VerifiableInference.Desc.K9 (readersOfLink statesOfLink)
open VerifiableInference.Desc.Sound (MsgT linksFull MgData mgAll)
open VerifiableInference.Desc.Kinds VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Head.Law VerifiableInference.Desc.Kinds.Head.Law.AtTable

variable {Xi P Tok : Type} {rows cols nR : ℕ} {Wp : OnBytes.Model.Verify.Public}
  (D : MgData Xi P Tok rows cols nR Wp)
  (Mg : Meaning P (Wit (Fin rows → Fin cols → GE) Tok MsgT))

/-- **In front of 342 the head's reader answers.** -/
theorem hheard_342 {Lk : Link S Claim} {P8 : K8.ReadsQuiet.PH} {small : S → Option K9.Read}
    {l6 piece6 : ℕ}
    (hreaders : D.Rd 24 = readersOfLink ⟨small, k6Silent P8 (statesOfLink Lk)⟩ Lk)
    (hown : D.runs 24 4 "own" = [(3, "norm"), (3, "policy"), (3, "logits")])
    (K : K6States Wp.hS (readsOf Wp) (parOf Wp.hS (workOf Wp)) l6 piece6 (statesOfLink Lk) 3)
    (N : Numbers) (Mw : Meaning P (Wit (Fin rows → Fin cols → GE) Tok MsgT))
    (hp : ∀ x, Mw.pub (.formsInT 24 4 "own") x = (mgAll D Mg).pub (.formsInT 24 4 "own") x) :
    ∀ x y, InAt N Mw linksFull (flatPlacesOf linksFull true) (noL 24 false) x y →
      ∃ H, (seatAt Wp.hS (readsOf Wp)).heard x.2 = some H :=
  fun x y h => heard_of_ownT D Mg hreaders hown K x ((hp x).symm.trans (ownT_held_342 N Mw x y h))

/-- **In front of 344 the head's reader answers.** -/
theorem hheard_344 {Lk : Link S Claim} {P8 : K8.ReadsQuiet.PH} {small : S → Option K9.Read}
    {l6 piece6 : ℕ}
    (hreaders : D.Rd 24 = readersOfLink ⟨small, k6Silent P8 (statesOfLink Lk)⟩ Lk)
    (hown : D.runs 24 4 "own" = [(3, "norm"), (3, "policy"), (3, "logits")])
    (K : K6States Wp.hS (readsOf Wp) (parOf Wp.hS (workOf Wp)) l6 piece6 (statesOfLink Lk) 3)
    (N : Numbers) (Mw : Meaning P (Wit (Fin rows → Fin cols → GE) Tok MsgT))
    (hp : ∀ x, Mw.pub (.formsIn 24 4 "own") x = (mgAll D Mg).pub (.formsIn 24 4 "own") x) :
    ∀ x y, InAt N Mw linksFull (flatPlacesOf linksFull true) (noL 24 true) x y →
      ∃ H, (seatAt Wp.hS (readsOf Wp)).heard x.2 = some H :=
  fun x y h => heard_of_own D Mg hreaders hown K x ((hp x).symm.trans (own_held_344 N Mw x y h))

theorem hheard_342_mw1 {Lk : Link S Claim} {P8 : K8.ReadsQuiet.PH} {small : S → Option K9.Read}
    {l6 piece6 : ℕ}
    (hreaders : D.Rd 24 = readersOfLink ⟨small, k6Silent P8 (statesOfLink Lk)⟩ Lk)
    (hown : D.runs 24 4 "own" = [(3, "norm"), (3, "policy"), (3, "logits")])
    (K : K6States Wp.hS (readsOf Wp) (parOf Wp.hS (workOf Wp)) l6 piece6 (statesOfLink Lk) 3)
    (N N' : Numbers) {nR' : ℕ} (D' : K13.Law.DataK13 P (Wit (Fin rows → Fin cols → GE) Tok MsgT)
        nR')
    (dk : K12.Door.K12Data) :
    ∀ x y, InAt N (mw1 N' D' dk (mgAll D Mg)) linksFull (flatPlacesOf linksFull true) (noL 24
        false) x y →
      ∃ H, (seatAt Wp.hS (readsOf Wp)).heard x.2 = some H :=
  hheard_342 D Mg hreaders hown K N _ fun _ => rfl

theorem hheard_344_mw1 {Lk : Link S Claim} {P8 : K8.ReadsQuiet.PH} {small : S → Option K9.Read}
    {l6 piece6 : ℕ}
    (hreaders : D.Rd 24 = readersOfLink ⟨small, k6Silent P8 (statesOfLink Lk)⟩ Lk)
    (hown : D.runs 24 4 "own" = [(3, "norm"), (3, "policy"), (3, "logits")])
    (K : K6States Wp.hS (readsOf Wp) (parOf Wp.hS (workOf Wp)) l6 piece6 (statesOfLink Lk) 3)
    (N N' : Numbers) {nR' : ℕ} (D' : K13.Law.DataK13 P (Wit (Fin rows → Fin cols → GE) Tok MsgT)
        nR')
    (dk : K12.Door.K12Data) :
    ∀ x y, InAt N (mw1 N' D' dk (mgAll D Mg)) linksFull (flatPlacesOf linksFull true) (noL 24
        true) x y →
      ∃ H, (seatAt Wp.hS (readsOf Wp)).heard x.2 = some H :=
  hheard_344 D Mg hreaders hown K N _ fun _ => rfl

end VerifiableInference.Desc.K1
