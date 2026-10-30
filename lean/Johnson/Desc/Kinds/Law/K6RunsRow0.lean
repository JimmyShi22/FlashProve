-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6RunsRow0.lean: EVERY ENTRY THAT A FORM OF THE OUTPUT HEAD'S RUNS OF CLAIMS
NAMES, AS THESE FORMS ARE READ OFF WHAT IS FIXED IN FRONT OF THE BATCHING (Law/RunsStillAtS.lean:
fsK6; Law/JoinRunAtS.lean: fsJoin), STANDS IN ROW 0 OF THE ARRAY OF THE READS, AT A COLUMN BELOW ITS
WIDTH (Law/K6FormsInT.lean: Row0). Wanted by other files, for their list of conditions in front of
the batching. Statements and proofs.

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law).
  TabsBelow iU3 z U K3: A NAMED PREMISE: the ledger U has an array number iU3, of width K3, and each
      table that z shows ends at or below K3.
  sees_fork: a state that shows (z, U) has no other open ledger than U.
  letters_row0: at the letters that are read at (z, U): the reads' entries have Row0, what is held
      as heard names no entry, and the plan's two facts on sizes.
  fsK6_row0: THE FIRST STATEMENT: at every name.
  fsJoin_row0: THE SECOND.

By lettersOf_some, lettersAt_ok, ready_at_letters (Law/RunsStill.lean),
entriesRow0_of_reads (Law/SilentAnswers.lean), claims_row0, keyVector_row0 (Law/K6FormsInT.lean),
heardBare_of_hear, sizes_of_plan (Law/K6Claims.lean), joinForm_has (Law/KeysHave.lean): the walk of
k6_formsInT's own proof, at what is fixed in front.
PREMISES, BY NAME: hok: the plan's test accepts · hsz: the plan's sizes are the shape's (at parOf h
w: by definition) · hR: K6Ready · hT: TabsBelow · for the join alone hbare: the lookup's last claim
names no entry.
What it does not say. That any premise holds at a reached state. Nothing on the merge's row form.
Nothing on soundness.
-/
import Johnson.Desc.Kinds.Law.JoinRunAtS
import Johnson.Desc.Kinds.Law.SilentAnswers

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E zeroE)
open OnBytes.Model (Fork Aff)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K9L

/-- **A named premise**: the ledger has the array of the reads, of width K3, and each table that is
shown ends at or below that width. -/
def TabsBelow (iU3 : Nat) (z : Seen) (U : Fork) (K3 : Nat) : Prop :=
  (∃ tr, U.trees[iU3]? = some tr ∧ tr.K = K3) ∧
    ∀ tt, z.t = some tt → ∀ y ∈ tt.tab, y.2.1 + y.2.2 ≤ K3

/-- A state that shows (z, U) has no other open ledger than U. -/
theorem sees_fork {s : S} {z : Seen} {U F : Fork} (hs : Sees s z U) (hF : s.fork? = some F) :
    F = U := by
  obtain ⟨o, ho, hU, -⟩ := hs
  unfold S.fork? at hF
  rw [ho] at hF
  by_cases hop : o.opened = true
  · simp only [hop, if_true, Option.some.injEq] at hF
    exact hF.symm.trans hU
  · simp [hop] at hF

variable {α : Type} (h : OnBytes.Model.Head.Shape) (iU3 : Nat) (p : Par)

/-- **At the letters that are read at (z, U).** -/
theorem letters_row0 (hok : p.ok = true) (hsz : p.sizes = sizesOf h) {z : Seen} {U : Fork}
    {K3 : Nat} (hR : K6Ready h iU3 p z U) (hT : TabsBelow iU3 z U K3)
    {v : Given × Behind × Places} (hv : lettersOf h iU3 p z U = some v) :
    (letI := v.1
     letI := v.2.1
     EntriesRow0 iU3 K3 v.2.2.final v.2.2.head) ∧
    (letI := v.1
     letI := v.2.1
     HeardBare) ∧
    (letI := v.1
     Norm.S2 ∣ Norm.d) ∧
    (letI := v.1
     JVa ≤ JV) := by
  obtain ⟨F0, G, rs, hW, hh, -⟩ := ready_at_letters h iU3 p hR hv
  obtain ⟨s0, hs0, e0⟩ := lettersOf_some h iU3 p hv
  obtain ⟨H', x, k1, -, k3, k4⟩ := lettersAt_ok h iU3 p e0
  obtain ⟨hd, hJ⟩ := sizes_of_plan p (seatAt h iU3) s0 v.1 hok k1
  obtain ⟨⟨tr0, htr0, hK0⟩, hTab⟩ := hT
  have hzt : ∀ o, s0.here = .head o → z.t = o.t := by
    intro o ho
    obtain ⟨o', ho', -, hz⟩ := hs0
    rw [ho] at ho'
    injection ho' with e
    rw [hz, e]
  obtain ⟨F, tr, hF, htr, hRow⟩ := entriesRow0_of_reads h iU3 s0 x k3 (by
    intro o tt F tr ho ht hF htr y hy
    obtain rfl := sees_fork hs0 hF
    obtain rfl : tr0 = tr := Option.some.inj (htr0.symm.trans htr)
    rw [hK0]
    exact hTab tt ((hzt o ho).trans ht) y hy)
  obtain rfl := sees_fork hs0 hF
  obtain rfl : tr0 = tr := Option.some.inj (htr0.symm.trans htr)
  have hs1 : v.1.sizes = sizesOf h := by
    obtain ⟨zz, y, e⟩ := given_form k1
    rw [e]
    exact hsz
  have e5 : v.2.2 = ⟨x.1, x.2⟩ := by rw [k4]
  have hB : (letI := v.1
    letI := v.2.1
    HeardBare) := by
    letI := v.1
    exact heardBare_of_hear hW hh
  refine ⟨?_, hB, hd, hJ⟩
  show @EntriesRow0 v.1.sizes iU3 K3 v.2.2.final v.2.2.head
  rw [e5, hs1, ← hK0]
  exact hRow

/-- **THE FIRST STATEMENT**: the forms of a run of the head's own, read off what is fixed in
front. -/
theorem fsK6_row0 (kap : α → Option Seen) (hok : p.ok = true) (hsz : p.sizes = sizesOf h)
    (q : α × Option Pub9) (z : Seen) (u : Pub9) (hz : kap q.1 = some z) (hu : q.2 = some u)
    (K3 : Nat) (hR : K6Ready h iU3 p z u.F) (hT : TabsBelow iU3 z u.F K3) (name : String)
    (l : List Aff) (hl : fsK6 h iU3 p kap name q = some l) : ∀ f ∈ l, Row0 iU3 K3 f := by
  unfold fsK6 at hl
  rw [hz, hu] at hl
  have hl' : formsOf h iU3 p name z u.F = some l := hl
  unfold formsOf at hl'
  obtain ⟨v, hv, lk⟩ := Option.bind_eq_some_iff.mp hl'
  obtain ⟨hRow, hB, hd, -⟩ := letters_row0 h iU3 p hok hsz hR hT hv
  intro f hf
  letI := v.1
  letI := v.2.1
  letI := v.2.2
  exact claims_row0 hRow hB hd name l lk f hf

/-- **THE SECOND STATEMENT**: the one form of "join", read off what is fixed in front. -/
theorem fsJoin_row0 (kap : α → Option Seen) (hok : p.ok = true) (hsz : p.sizes = sizesOf h)
    (q : α × Option Pub9) (z : Seen) (u : Pub9) (hz : kap q.1 = some z) (hu : q.2 = some u)
    (K3 : Nat) (hR : K6Ready h iU3 p z u.F) (hT : TabsBelow iU3 z u.F K3)
    (hbare : ∀ g, z.lookHeard = some g → g.cEnd.ents = #[])
    (l : List Aff) (hl : fsJoin h iU3 p kap q = some l) : ∀ f ∈ l, Row0 iU3 K3 f := by
  unfold fsJoin at hl
  rw [hz, hu] at hl
  have hl' : ((lettersOf h iU3 p z u.F).bind fun v =>
      (if z.opened then z.lookHeard else none).map fun g =>
        [Came.joinForm g (keyVectorsAt v)]) = some l := hl
  obtain ⟨v, hv, hm⟩ := Option.bind_eq_some_iff.mp hl'
  obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.mp hm
  have hg' : z.lookHeard = some g := by
    by_cases ho : z.opened = true
    · simpa [ho] using hg
    · simp [ho] at hg
  obtain ⟨hRow, hB, hd, hJ⟩ := letters_row0 h iU3 p hok hsz hR hT hv
  intro f hf
  obtain rfl := List.mem_singleton.mp hf
  refine joinForm_has (kept_row0 iU3 K3) g (keyVectorsAt v) (fun c hc => ?_)
    (row0_bare (hbare g hg'))
  have hlen : c < v.1.calls.length := by
    simpa [keyVectorsAt] using hc
  letI := v.1
  letI := v.2.1
  letI := v.2.2
  unfold keyVectorsAt
  rw [Came.getD_map_toArray v.1.calls _ c hlen (Aff.ofConst zeroE) (0, [])]
  exact keyVector_row0 hRow hB hd hJ _ _

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.sees_fork
#print axioms VerifiableInference.Desc.Kinds.Head.Law.letters_row0
#print axioms VerifiableInference.Desc.Kinds.Head.Law.fsK6_row0
#print axioms VerifiableInference.Desc.Kinds.Head.Law.fsJoin_row0
