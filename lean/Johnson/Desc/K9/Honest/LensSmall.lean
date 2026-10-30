-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K9/Honest/LensSmall.lean (kind K9): EACH RUN's OWN NUMBER OF CLAIMS, WITH "=": the library's five small
bounds (Johnson/Desc/First/Link/Law/SmallBounds.lean: "at most") in the arm in which the reader returns. Over the sealed
library alone. Statements and proofs, after the library's, line by line; beyond "=" each takes the premise that its
reader returns, where the library's bound takes none or asks it under "∀"; no goal is stated.
  `pickLen_eq`   "planes" and "join": under the lookups' promise on the fixed part (`K3Ok`), where what was heard and
      the snapshot are there: the number is n
  `objLen_eq`   "objects": under the same: the number is Forest.lins of the shape of what was heard
  `lenFront_eq`   the feed-forward kind's run "front": where what is fixed holds that kind's own structure o, at o's
      layout: frontB
  `lenK6_eq`, `lenJoin_eq`   the head's three runs and its join: where the run's forms are there: the library's lenK6 of
      the name; 1
WHAT IS NOT CLAIMED. That a reader returns anywhere: each "… = some …" is a premise. No member; `pickLen_eq` and
`objLen_eq` are called by Honest/K9/LensLook.lean, the three others by Honest/K9/LensRuns.lean. Nothing on any property.

-/
import Johnson.Desc.First.Link.Law.SmallBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.StillRun
open VerifiableInference.Desc.K4Run (lenFront)
open VerifiableInference.Desc.K9Asks (frontB)
open VerifiableInference.Desc.LinkJoin (ends_rows Q)
open VerifiableInference.OnPublicFiles (K3Ok Stood pick pick_spec pick_some objLen pickLen)
open VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Head.Law

variable {α : Type}

/-- "planes" and "join", where what was heard and the snapshot are there. -/
theorem pickLen_eq (hd : α → Option Forest.Heard) (lm jLK n : ℕ) {q : α × Option Pub9}
    (K : K3Ok hd lm jLK q) {g : Forest.Heard} {u : Pub9} (hg : hd q.1 = some g) (hu : q.2 = some u) :
    pickLen hd lm jLK n q = n := by
  obtain ⟨rs, e⟩ := pick_some hd lm jLK K hg hu
  unfold pickLen
  rw [e]

/-- **"objects"**, where what was heard and the snapshot are there. -/
theorem objLen_eq (hd : α → Option Forest.Heard) (lm jLK : ℕ) {q : α × Option Pub9}
    (K : K3Ok hd lm jLK q) {g : Forest.Heard} {u : Pub9} (hg : hd q.1 = some g) (hu : q.2 = some u) :
    objLen hd lm jLK q = Forest.lins g.shape := by
  obtain ⟨rs, e⟩ := pick_some hd lm jLK K hg hu
  obtain ⟨_, ok, _⟩ := K g u hg hu
  unfold objLen
  rw [e]
  exact ends_rows g.shape ok lm jLK rs

/-- **The layers' run "front"**, where the state holds its own. -/
theorem lenFront_eq {β : Type} (p4 : OnBytes.Desc.First.K4.Par) {q : Q β} {y : Layer.Lay}
    {g : ℕ} (hk : p4.k3Runs = true) (hg : p4.g = g) {o : _} (e : q.1.own = some o) (ho : o.v.y = y) :
    lenFront p4 (·.own) q = frontB y g := by
  unfold lenFront
  show (match q.1.own with
    | some o => OnBytes.Desc.First.K4.frontLen (!p4.k3Runs) p4.g o
    | none => 0) = frontB y g
  rw [e]
  show OnBytes.Desc.First.K4.frontLen (!p4.k3Runs) p4.g o = _
  rw [hk, hg]
  unfold OnBytes.Desc.First.K4.frontLen frontB
  rw [ho]
  rfl

variable (h : OnBytes.Model.Head.Shape) (iU3 : ℕ) (p : Par) (kap : α → Option Seen)

/-- **The head's three runs**, where the forms are there. -/
theorem lenK6_eq (name : String) {q : α × Option Pub9} {l : List Aff} (e : fsK6 h iU3 p kap name q = some l) :
    lenStill (fsK6 h iU3 p kap name) q = lenK6 name := by
  unfold lenStill
  rw [e]
  show l.length = _
  unfold fsK6 at e
  split at e
  · rename_i z u _ _
    have e' : formsOf h iU3 p name z u.F = some l := e
    unfold formsOf at e'
    obtain ⟨v, _, lk⟩ := Option.bind_eq_some_iff.mp e'
    letI := v.1
    letI := v.2.1
    letI := v.2.2
    exact lens_K6 name l lk
  · exact nomatch e

/-- **The head's join**, where the forms are there. -/
theorem lenJoin_eq {q : α × Option Pub9} {l : List Aff} (e : fsJoin h iU3 p kap q = some l) :
    lenStill (fsJoin h iU3 p kap) q = 1 := by
  unfold lenStill
  rw [e]
  show l.length = _
  unfold fsJoin at e
  split at e
  · rename_i z u _ _
    obtain ⟨v, _, hm⟩ := Option.bind_eq_some_iff.mp e
    obtain ⟨g, _, rfl⟩ := Option.map_eq_some_iff.mp hm
    rfl
  · exact nomatch e

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.pickLen_eq
#print axioms ProofFile.Honest.K9.objLen_eq
#print axioms ProofFile.Honest.K9.lenFront_eq
#print axioms ProofFile.Honest.K9.lenK6_eq
#print axioms ProofFile.Honest.K9.lenJoin_eq
