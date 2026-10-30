-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No real place is shown at which all premises hold together.
Johnson/Top/H/Keep/FormsObjectsDigits.lean: The kind "lookup" (K3): AT THE LOOKUP ON THE
APPROXIMATE RANGE PROOF's DIGITS: FROM THE TABLE OF JOINTS' ITEM "the forms of the run objects are
worth 0", AT ITS FILLING AND A LINK's READERS, TO THE FIRST ITEM OF THE LOOKUP's ROW OUT AT THE
CALLER's OWN READING OF THE PLACES (digNu): THE EQUATION ON THE MASK ROW IS PAID. One statement: a
joining of Johnson/Top/H/Keep/FormsObjectsLink.lean's forms_objects_bare and
Johnson/Desc/First/Look/K3DigitsMask.lean's digits_maskRow.

OBJECT: Meaning.forms at meaningForms; K3OutRows at digNu.
Used by Johnson/Desc/Sound/MgAt/K3DigitsObj.lean.
LETTERS: x, tl, D, rad, seatT, arr, ms: the digits' row's; the filling's Rd, runs, St, after, N, wt,
  rw, ah, Mg; m, pc, pr; H, l; claim; pass.
Compiled with the whole library.

Main name:
  digits_fObj.

Limits. PREMISES THAT STAY: hA: the maker of claims is plain · hB: a public Bool on the plan: every
mask up to the planned number of slots has a seat in the digits' list · hrun · hah · hlink · hfind
| hpass: as in FormsObjectsLink.lean. ASKED IN THE CONCLUSION, OF THE VERIFIER's STATE, BEYOND WHAT
THE ROW's fObj ASKS TODAY: its part has MaskOk (five clauses on its frame, book, statement and
ledger, and on the table's list of members) · the rows of what was heard are bare.

Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.Keep.FormsObjectsLink
import Johnson.Desc.First.Look.K3DigitsMask

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model OnBytes.Params
open OnBytes.Road.Rows (Bare)
open VerifiableInference.Desc (Wit Claim Link Strs)
open VerifiableInference.Desc.First (S Meaning Numbers)
open VerifiableInference.Desc.K3 (seatDigits)
open VerifiableInference.Desc.K9 (Readers segAt? readersOfLink statesOfLink LinkHoles)
open VerifiableInference.Desc.Sound (Mem MsgT Stated meaningForms forms_objects_bare)
open VerifiableInference.Desc.First.Look

section
variable {P Cells Tok : Type} (x : Desc.First.Look.Place) (tl : HTailF2) (D : Sent)
  (rad : OracleShape → ℕ) (seatT : Fin (digList x D rad).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
  (ms : List Mem) (Rd : ℕ → Readers) (runs : ℕ → ℕ → String → List (ℕ × String)) (St : Stated)
  (after : ℕ → S → Except String S) (N : Numbers)
  (wt : ℕ → P × S → Strs → Wit Cells Tok MsgT → Prop) (rw : ℕ → S → Bool)
  (ah : ℕ → String → Bool)

theorem digits_fObj (Mg : Meaning P (Wit Cells Tok MsgT)) (m pc pr : ℕ) (H : LinkHoles)
    (l : Link S Claim) (claim : Aff → Claim) (hA : AtS2 (seatDigits claim))
    (hB : maskB D (digList x D rad) x.link x.arrays.ns = true)
    (hrun : (pr, "objects") ∈ runs m pc "objects") (hah : ah pr "objects" = false)
    (hlink : Rd m = readersOfLink H l) (pass : S → S → Prop)
    (hpass : ∀ t G, pass t (t.putFork G))
    (hfind : ∃ nm run, (statesOfLink l pr).find? (fun r => r.1 == "objects") = some (nm, run) ∧
      RunOver pass run (objectsRun (seatDigits claim))) :
    ∀ (z : P) (s : S) (y : Strs) (w : Wit Cells Tok MsgT),
      (meaningForms D.codes arr ms Rd runs St after N wt rw ah Mg).forms m pc "objects" (z, s) y
        w →
      (∀ a, segAt? s = some a → MaskOk x D rad seatT ms (N.group m) a) →
      ∀ g F', (seatDigits claim).fork s = some F' → (seatDigits claim).heard s = some g →
        (∀ f ∈ g.rows.toList, Bare f) →
        K3OutRows tl.f9 5 x.F.next (digNu x tl D rad seatT arr w) Reading.gl g F' :=
  forms_objects_bare D.codes arr ms Rd runs St after N wt rw ah Mg m pc pr H l (seatDigits claim)
    hA tl.f9 5 x.F.next (fun w => digNu x tl D rad seatT arr w)
    (MaskOk x D rad seatT ms (N.group m)) hrun hah hlink pass hpass hfind
    (fun a w j M hj => digits_maskRow x tl D rad seatT arr ms (N.group m) hB a M w j hj)

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.digits_fObj
