-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K8/Honest/SmallBackAt9.lean: THE SMALLNESS TEST: FROM THE LAW's SENTENCE `SmallAt` BACK
TO THE FIELD "forms" OF THE COMPOSED MEANING AT THE RUN "small": the other way of the library's
`small_at9` (Johnson/Desc/First/K8/FormsAt9.lean). One theorem; no definition; none of the library's
goals.

  **`forms_small_of_smallAt`**   the segment m has a sort and a link · the map of names at the run
                   "small" is the one run (4 + o, "K8.equations") · the state has a record of the
                   test and the caller's list of tables is the record's own · THE PUBLIC TEST
                   `formsInA` SAYS YES AT THE STATE, at that run · SmallAt at `cellsAhead` ⊢
                   (mgAll 𝔇 Mg).forms m (5 + o) "small" (z, s) y w
HOW. `mgAll_forms` (Johnson/Desc/Sound/MgAll.lean) · `reader_small`
(Johnson/Desc/Sound/MgAt/SmallRun.lean) · `formsQA_of_smallAt`
(Johnson/Desc/K8/Honest/SmallBack.lean).
NO OPTION IS RAISED, NO INSTANCE TAKEN AWAY. ONE `decide`, on two written strings.
Limits. An implication: none of its premises is paid here. Nothing on the digits.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.K8.Honest.SmallBack
import Johnson.Desc.First.K8.FormsAt9

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest

open OnBytes OnBytes.Model VerifiableInference.Desc VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Meaning runsOf)
open VerifiableInference.Desc.First.K8 (SmallAt cellsAhead)

variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X) (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))

/-- **The law's sentence gives the field "forms" at the run "small".** -/
theorem forms_small_of_smallAt (m o : ℕ) (sub : ModelPart) (hsub : 𝔇.links[m]? = some sub)
    (hr : runsOf sub (5 + o) "small" = [(4 + o, "K8.equations")]) (l : Link First.S Claim)
    (hl : 𝔇.lk m = some l) (z : P) (s : First.S) (y : Strs)
    (w : Wit (CellsQ rows cols) Tok MsgT) {tl : HTailF2} (ht : s.tl? = some tl)
    (hf : s.funs? = some tl.funs)
    (hin : K9.formsInA (𝔇.Rd m) (𝔇.N.sent m) (𝔇.N.group m) (4 + o) "K8.equations" s = true)
    (h : SmallAt (cellsAhead 𝔇.cs 𝔇.arr 𝔇.ms 𝔇.N m (z, s)) s w) :
    (mgAll 𝔇 Mg).forms m (5 + o) "small" (z, s) y w := by
  rw [mgAll_forms]
  refine ⟨fun p hp => ?_, fun e => absurd e (by decide)⟩
  have hp' : p = (4 + o, "K8.equations") := by
    unfold MgData.runs at hp
    rw [runsAt_of 𝔇.links m sub hsub, hr] at hp
    exact List.mem_singleton.1 hp
  rw [hp']
  have ha : 𝔇.ah (4 + o) "K8.equations" = true := rfl
  rw [if_pos ha]
  exact formsQA_of_smallAt 𝔇.cs 𝔇.arr 𝔇.ms 𝔇.N m z s (𝔇.Rd m) (4 + o) "K8.equations" ht hf
    (reader_small 𝔇 m l hl (4 + o) s) w hin h

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.forms_small_of_smallAt
