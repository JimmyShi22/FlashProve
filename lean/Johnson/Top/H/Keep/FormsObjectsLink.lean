-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No real place is shown at which all premises hold together.
Johnson/Top/H/Keep/FormsObjectsLink.lean: The kind "lookup" (K3): THE PREMISE "the item forms m pc
objects gives the first item of the lookup's row out" OF THE LOOKUPS' ROWS AT THE TABLE OF JOINTS,
AT THE TABLE's FILLING AND A LINK's READERS: THE SECOND FORM: nothing is asked of the link's second
hole any more: in its place: the rows of what was heard name no entry; and the equation on the mask
row is asked only at parts with a property Ok (a letter). One statement with its proof.

OBJECT: Meaning.forms at meaningForms (Johnson/Desc/Sound/BordersForms.lean);
  K3OutRows.
Used by Johnson/Top/H/Keep/FormsObjectsDigits.lean.
LETTERS: the filling's cs, arr, ms, Rd, runs, St, after, N, wt, rw, ah, Mg; m, pc, pr; H, l, seat;
  h, lm, first; nu; Ok; pass.
Compiled with the whole library.

Main name:
  forms_objects_bare.

Limits. IT OVERTAKES forms_objects_link (Johnson/Top/H/Keep/FormsObjectsAt.lean), whose premise hs
(the hole is silent at "objects") need not hold at the head's link. PREMISES THAT STAY: hrun · hah
· hlink · hA as there · hfind | hpass: the run that the link states under "objects" says yes
wherever the bare run does and its wrapper's guard passes, and that guard passes where the state is
turned by putFork alone · hDict: the one equation on the mask row, at parts with Ok. ASKED IN THE
CONCLUSION, OF THE VERIFIER's STATE: its part has Ok · the rows of what was heard are bare (behind
the block's yes: Johnson/Top/H/Keep/RowsBare.lean).

Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.Sound.BordersForms
import Johnson.Top.H.Keep.FormsInObjects

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes OnBytes.Model
open OnBytes.Road.Rows (Bare)
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers Comp S)
open VerifiableInference.Desc.K9 (Readers segAt? readersOfLink statesOfLink LinkHoles)

section
variable (cs : OnBytes.Codes) {P Cells Tok : Type} (arr : ℕ → ℕ → ℕ) (ms : List Mem)
  (Rd : ℕ → Readers) (runs : ℕ → ℕ → String → List (ℕ × String)) (St : Stated)
  (after : ℕ → First.S → Except String First.S) (N : Numbers)
  (wt : ℕ → P × First.S → Strs → Wit Cells Tok MsgT → Prop) (rw : ℕ → First.S → Bool)
  (ah : ℕ → String → Bool)

theorem forms_objects_bare (Mg : Meaning P (Wit Cells Tok MsgT)) (m pc pr : ℕ)
    (H : LinkHoles) (l : Link S Claim) (seat : K3.Seat S Claim) (hA : OnPublicFiles.AtS2 seat)
    (h : Forest.Shape) (lm first : ℕ) (ν : Wit Cells Tok MsgT → _root_.Fo.Pl → GQ)
    (Ok : K9.Part → Prop)
    (hrun : (pr, "objects") ∈ runs m pc "objects") (hah : ah pr "objects" = false)
    (hlink : Rd m = readersOfLink H l)
    (pass : S → S → Prop) (hpass : ∀ t G, pass t (t.putFork G))
    (hfind : ∃ nm run, (statesOfLink l pr).find? (fun r => r.1 == "objects") = some (nm, run) ∧
      OnPublicFiles.RunOver pass run (OnPublicFiles.objectsRun seat))
    (hDict : ∀ a w j, Ok a → j < a.F.ns →
      (dataQ (N.group m) a (seatTab cs arr ms w)).mask j = ν w (.mask j)) :
    ∀ (z : P) (s : S) (y : Strs) (w : Wit Cells Tok MsgT),
      (meaningForms cs arr ms Rd runs St after N wt rw ah Mg).forms m pc "objects" (z, s) y w →
      (∀ a, segAt? s = some a → Ok a) →
      ∀ g F', seat.fork s = some F' → seat.heard s = some g → (∀ f ∈ g.rows.toList, Bare f) →
        OnPublicFiles.K3OutRows h lm first (ν w) Reading.gl g F' := by
  intro z s y w hf hOk g F' hF hg hb
  have h1 := hf.1 (pr, "objects") hrun
  have hn : ¬ ah (pr, "objects").1 (pr, "objects").2 = true := by
    show ¬ ah pr "objects" = true
    rw [hah]
    exact Bool.false_ne_true
  rw [if_neg hn] at h1
  have hF' : s.fork? = some F' := (hA.fork s).symm.trans hF
  have hans : (Rd m).forms pr "objects" s = some { forms := g.rows.toList, late := [] } := by
    rw [hlink]
    exact OnPublicFiles.link_answers H l pr (by decide)
      (OnPublicFiles.objects_answers seat hA pass hpass hfind hF' hg hb)
  refine formsQ_objects_outRows (Rd m) (N.group m) pr seat.heard h lm first (ν w)
    (seatTab cs arr ms w) s (fun R g' hR hg' => ?_) (fun a j ha hj => hDict a w j (hOk a ha) hj) h1
    g F' hF' hg
  obtain rfl : g = g' := Option.some.inj (hg.symm.trans hg')
  obtain rfl := Option.some.inj (hans.symm.trans hR)
  exact ⟨rfl, fun f hm => hm⟩

end

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.forms_objects_bare
