-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/WeightHeardOfPub.lean: "THE HEAD's SEAT's READER heard ANSWERS" FROM THE YES
OF ONE PUBLIC TEST OF THE COMPOSED MEANING, AT A PLAIN PAIR: no promise of the table, no border, no
frame, no strings. Theorems. Cut out of Johnson/Desc/Kinds/Law/WeightHeardAt.lean's heard_at_T and
heard_at_F: their proofs behind "have hpub", to the letter. For a caller that calls it at its
own states.

What is proved (namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable). Under hreaders, hown and
K, as in heard_at_T | heard_at_F:
  **heard_of_ownT**   (mgAll D Mg).pub (.formsInT 24 4 "own") x = true implies that (seatAt Wp.hS
          (readsOf Wp)).heard x.2 answers.
  **heard_of_own**    the like at .formsIn 24 4 "own".
  heard_at_T_again, heard_at_F_again   heard_at_T's and heard_at_F's statements once more, proved by
          calls of the two: to show the fit.

Every letter under "there is": H: pinned by the reader's equation.
What it does not say. That the public test says yes anywhere. hreaders, hown (equations on the
meaning's parameters) and K (K6States: on the IOP as written in Lean) are premises. Nothing on
soundness.

-/
import Johnson.Desc.Kinds.Law.WeightHeardAt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable

open OnBytes
open OnBytes.Maker OnBytes.Flat Johnson.Pack
open VerifiableInference.OnPublicFiles.Flat (GE)
open VerifiableInference.Desc.First (S Item Meaning)
open VerifiableInference.Desc.K9 (RunOf readerOf readersOfLink statesOfLink formsInT formsIn)
open VerifiableInference.Desc.Sound (Piece Frame MsgT onQ openQ linksFull MgData mgAll
  onParts_of_on)

/-- The driver's list of places, at the full chain. -/
local notation "PS" => First.flatPlacesOf linksFull true

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {Wp : OnBytes.Model.Verify.Public}
  (D : MgData Xi P Tok rows cols nR Wp)
  (Mg : Meaning P (Wit (Fin rows → Fin cols → GE) Tok MsgT)) {Fr : Frame}

set_option quotPrecheck false in
/-- The composed meaning. -/
local notation "MGA" => mgAll D Mg

/-- **From the yes of the public test tied to the claim with the tables not yet laid.** -/
theorem heard_of_ownT {Lk : Link S Claim} {P8 : K8.ReadsQuiet.PH} {small : S → Option K9.Read}
    {l6 piece6 : ℕ}
    (hreaders : D.Rd 24 = readersOfLink ⟨small, k6Silent P8 (statesOfLink Lk)⟩ Lk)
    (hown : D.runs 24 4 "own" = [(3, "norm"), (3, "policy"), (3, "logits")])
    (K : K6States Wp.hS (readsOf Wp) (parOf Wp.hS (workOf Wp)) l6 piece6 (statesOfLink Lk) 3)
    (x : P × S) (hpub : (MGA).pub (.formsInT 24 4 "own") x = true) :
    ∃ H, (seatAt Wp.hS (readsOf Wp)).heard x.2 = some H := by
  have h1 : formsInT (D.Rd 24) (D.N.sent 24 0) 3 "norm" x.2 = true :=
    List.all_eq_true.1 hpub (3, "norm") (by rw [hown]; simp)
  rw [hreaders] at h1
  obtain ⟨R, hR⟩ := answers_of_formsInT _ _ _ _ _ h1
  exact heard_of_reader K P8 small x.2 R hR

/-- **From the yes of the public test tied to the claim behind it.** -/
theorem heard_of_own {Lk : Link S Claim} {P8 : K8.ReadsQuiet.PH} {small : S → Option K9.Read}
    {l6 piece6 : ℕ}
    (hreaders : D.Rd 24 = readersOfLink ⟨small, k6Silent P8 (statesOfLink Lk)⟩ Lk)
    (hown : D.runs 24 4 "own" = [(3, "norm"), (3, "policy"), (3, "logits")])
    (K : K6States Wp.hS (readsOf Wp) (parOf Wp.hS (workOf Wp)) l6 piece6 (statesOfLink Lk) 3)
    (x : P × S) (hpub : (MGA).pub (.formsIn 24 4 "own") x = true) :
    ∃ H, (seatAt Wp.hS (readsOf Wp)).heard x.2 = some H := by
  have h0 : (if D.ah 3 "norm" = true then
      K9.formsInA (D.Rd 24) (D.N.sent 24) (D.N.group 24) 3 "norm" x.2
      else formsIn (D.Rd 24) (D.N.group 24) 3 "norm" x.2) = true :=
    List.all_eq_true.1 hpub (3, "norm") (by rw [hown]; simp)
  have h1 : formsIn (D.Rd 24) (D.N.group 24) 3 "norm" x.2 = true := h0
  rw [hreaders] at h1
  obtain ⟨R, hR⟩ := answers_of_formsIn _ _ _ _ _ h1
  exact heard_of_reader K P8 small x.2 R hR

/-- heard_at_T's statement, by a call of heard_of_ownT. -/
theorem heard_at_T_again {Lk : Link S Claim} {P8 : K8.ReadsQuiet.PH}
    {small : S → Option K9.Read} {l6 piece6 : ℕ}
    (hreaders : D.Rd 24 = readersOfLink ⟨small, k6Silent P8 (statesOfLink Lk)⟩ Lk)
    (hown : D.runs 24 4 "own" = [(3, "norm"), (3, "policy"), (3, "logits")])
    (K : K6States Wp.hS (readsOf Wp) (parOf Wp.hS (workOf Wp)) l6 piece6 (statesOfLink Lk) 3)
    (k : ℕ) (hopen : Item.formsT 24 4 "own" ∈ openQ linksFull PS k) (a : (P × S) × Fr.E.Str)
    (ha : onQ (Fr := Fr) D.N MGA linksFull PS (fun a => a) k a) (hm : a.1.2.failed = none) :
    ∃ H, (seatAt Wp.hS (readsOf Wp)).heard a.1.2 = some H :=
  heard_of_ownT D Mg hreaders hown K a.1
    ((onParts_of_on D.N MGA linksFull PS (fun a => a) k a ha hm).pub _
      (List.mem_append_right _ (List.mem_flatMap.2 ⟨_, hopen, List.mem_singleton.2 rfl⟩)))

/-- heard_at_F's statement, by a call of heard_of_own. -/
theorem heard_at_F_again {Lk : Link S Claim} {P8 : K8.ReadsQuiet.PH}
    {small : S → Option K9.Read} {l6 piece6 : ℕ}
    (hreaders : D.Rd 24 = readersOfLink ⟨small, k6Silent P8 (statesOfLink Lk)⟩ Lk)
    (hown : D.runs 24 4 "own" = [(3, "norm"), (3, "policy"), (3, "logits")])
    (K : K6States Wp.hS (readsOf Wp) (parOf Wp.hS (workOf Wp)) l6 piece6 (statesOfLink Lk) 3)
    (k : ℕ) (hopen : Item.forms 24 4 "own" ∈ openQ linksFull PS k) (a : (P × S) × Fr.E.Str)
    (ha : onQ (Fr := Fr) D.N MGA linksFull PS (fun a => a) k a) (hm : a.1.2.failed = none) :
    ∃ H, (seatAt Wp.hS (readsOf Wp)).heard a.1.2 = some H :=
  heard_of_own D Mg hreaders hown K a.1
    ((onParts_of_on D.N MGA linksFull PS (fun a => a) k a ha hm).pub _
      (List.mem_append_right _ (List.mem_flatMap.2 ⟨_, hopen, List.mem_singleton.2 rfl⟩)))

end

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.heard_of_ownT
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.heard_of_own
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.heard_at_T_again
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.heard_at_F_again
