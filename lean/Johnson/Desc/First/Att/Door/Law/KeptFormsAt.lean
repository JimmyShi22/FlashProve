-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
-- Johnson/Desc/First/Att/Door/Law/KeptFormsAt.lean: KIND K5: K5AtMg's FIELD keptForms (Johnson/Desc/First/Att/K05AtMg.lean: the public tests tied to the items that stay open ride over the block's lay) AT ANY MEANING Mg WITH Mg.pub = pubAll D base (mgAll_pub, Johnson/Desc/Sound/MgAll.lean, := rfl; the halves with code). Mathlib beneath.
-- HOW IT SHRINKS. By the table's text ONE tied test is met at the kind's border beside the index's two (which K5Fill has): formsInT m 2 "objects": the lookup argument's run "objects" (hO: EVALUATED at two written lists of links, not proved). That test rides over the lay by formsInT_kept (Johnson/Desc/First/Att/K05FormsKept.lean) UNDER TWO FACTS ON THE READER OF THAT RUN, each under the field's own guards (the promise in front · no mark · an open attention segment · the hearing's return):
--   hRo: the reader answers alike at the verifier's state in front of and behind the kind's lay · hlo: the slots that its answer names as late lie below the ledger's next free slot.
-- WHOSE: K5's FILES WITH THE LOOKUPS' FILES: the run is the lookups'; the lay is K5's.
import Johnson.Desc.First.PubAllAt
import Johnson.Desc.First.Att.K05FormsKept
import Johnson.Desc.First.Att.K05T2

set_option autoImplicit false

namespace H2K5.Door
open OnBytes OnBytes.Model
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Att.P (behind hear Heard onAt_pub fork_front sized_of_B formsInT_kept)

theorem keptForms_at {Pp W : Type} (D : PubData) (base : Pub → Pp × S → Bool) (Mg : Meaning Pp W) (hpub : Mg.pub = pubAll D base)
    (N : Numbers) (links : List ModelPart) (pl : Place) (O : List Item) (Q : List Pub) (Fr : Frame) (m : Nat)
    (own : Params.AttentionRounds) (hled : Pub.ledger m ∈ Q)
    (hO : ∀ i ∈ O, (rowOf links pl).ins.contains i = false → i ≠ .pinI → ∀ q ∈ tiesOf i, q = .formsInT m 2 "objects")
    (hRo : ∀ π : Pp, ∀ (s : S) (y : Fr.E.Str) (att : AttOwn) (hd : Heard) (G : Fork) (rs : List Fmt.RoundView),
      onAt N Mg links (some pl) O Q (π, s) (strsOf Fr y) → s.failed = none → s.here = .att att →
      hear own (att.F, rs, 0) = some (hd, G, [], 0) → ∀ p ∈ D.runs m 2 "objects",
        (D.Rd m).forms p.1 p.2 (behind s att hd G) = (D.Rd m).forms p.1 p.2 s)
    (hlo : ∀ π : Pp, ∀ (s : S) (y : Fr.E.Str) (att : AttOwn), onAt N Mg links (some pl) O Q (π, s) (strsOf Fr y) →
      s.failed = none → s.here = .att att → ∀ p ∈ D.runs m 2 "objects", ∀ R, (D.Rd m).forms p.1 p.2 s = some R →
        ∀ x ∈ R.late, x.1 < att.F.next) :
    ∀ π : Pp, ∀ (s : S) (y : Fr.E.Str) (att : AttOwn) (hd : Heard) (G : Fork) (rs : List Fmt.RoundView),
      onAt N Mg links (some pl) O Q (π, s) (strsOf Fr y) → s.failed = none → s.here = .att att →
      hear own (att.F, rs, 0) = some (hd, G, [], 0) →
      ∀ i ∈ O, (rowOf links pl).ins.contains i = false → i ≠ .pinI → ∀ q ∈ tiesOf i,
        Mg.pub q (π, s) = true → Mg.pub q (π, behind s att hd G) = true := by
  intro π s y att hd G rs hon hu e hh i hi h1 h2 q hq hv
  obtain rfl := hO i hi h1 h2 q hq
  have hz : s.fork?.any K3.sizedB = true := by
    have := onAt_pub hon hu _ hled
    rwa [hpub] at this
  rw [fork_front e] at hz
  rw [hpub, pubAll_formsInT] at hv ⊢
  refine List.all_eq_true.2 fun p hp => ?_
  exact formsInT_kept (D.Rd m) (D.N.sent m 0) p.1 p.2 e hh (sized_of_B hz) (hRo π s y att hd G rs hon hu e hh p hp)
    (hlo π s y att hon hu e p hp) (List.all_eq_true.1 hv p hp)

#print axioms keptForms_at

end H2K5.Door
