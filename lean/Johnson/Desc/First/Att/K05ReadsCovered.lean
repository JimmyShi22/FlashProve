-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05ReadsCovered.lean: kind K5: `reads_covered_K05`
(Johnson/Desc/First/Att/Claims/Covered.lean) with its two premises paid: every entry of the array of
tables that a form gathered by "first" or "second" names is entry number x < nW of that array, from
the returns of the kind's own functions and Said (or the hearing's own return at a sized ledger).

Main names:
  `reads_covered_said`: leftP, pointsOf, tablesP, firstRun and secondRun have returned, at one record
    i, and Said holds of what was heard: then every gathered form is Cov i.iU3 K nW. LenIn by
    `len_in` (Claims/Covered.lean); RowsCov by `rows_cov`
    (Johnson/Desc/First/Att/K05RowsCov.lean), `leftP_spec` and `points_are`.
  `reads_covered_heard`: the same with Said drawn from the hearing's own return at a sized ledger
    (`hear_said`, Johnson/Desc/First/Att/K5SaidAll.lean).
  `not_cov_beyond`: a control: the form that names entry number nW itself is not Cov.
Why Said is asked: a row is made of the heard record's start form; in a record that no hearing has
made, that form could name any entry.
Limits: the key forms that "keys" hands on are not spoken of. Where a run does not return the
statement holds for nothing: that the runs return at the plans that run is not shown in this file
or in what it imports. Nothing is said on whether a read is true.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05RowsCov

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model OnBytes.Model.Road
open VerifiableInference.Desc.Part
open K5Law (Cov)

/-- **Every gathered form names entries of the tables' part alone**, from the kind's own returns. -/
theorem reads_covered_said {i : Runs.In} {zk : Array (Array E)} {h : Heard} {l : Left} {F G : Fork}
    {x : Params.AttentionRounds} {L : Lists} {K nW : ℕ} {mats : Array (ℕ × ℕ)} {lk : LookIn}
    {l₁ l₂ : List Aff} {j : Runs.JoinsP}
    (hl : leftP i.g zk h F = some l) (hs : Said x h G L) (hp : pointsOf i.g zk h l = some i.p)
    (ht : tablesP i.g mats nW lk i.p = some i.t)
    (h1 : Runs.firstRun i K = some (l₁, j)) (h2 : Runs.secondRun i K = some l₂) :
    ∀ f ∈ l₁ ++ l₂, Cov i.iU3 K nW f :=
  K5Law.reads_covered_K05 (K5Law.len_in ht) (rows_cov (leftP_spec hl) hs (K5Law.points_are hp)) h1 h2

/-- The same from the hearing's own return. -/
theorem reads_covered_heard {i : Runs.In} {zk : Array (Array E)} {h : Heard} {l : Left}
    {F0 F G : Fork} {x : Params.AttentionRounds} {rs rest : List Fmt.RoundView} {lead : ℕ} {K nW : ℕ}
    {mats : Array (ℕ × ℕ)} {lk : LookIn} {l₁ l₂ : List Aff} {j : Runs.JoinsP}
    (hh : hear x (F0, rs, 0) = some (h, G, rest, lead)) (hz : Sized F0)
    (hl : leftP i.g zk h F = some l) (hp : pointsOf i.g zk h l = some i.p)
    (ht : tablesP i.g mats nW lk i.p = some i.t)
    (h1 : Runs.firstRun i K = some (l₁, j)) (h2 : Runs.secondRun i K = some l₂) :
    ∀ f ∈ l₁ ++ l₂, Cov i.iU3 K nW f := by
  obtain ⟨L, _, _, _, hs, _, _⟩ := hear_said hh hz
  exact reads_covered_said hl hs hp ht h1 h2

/-- A control: the form that names entry number nW is not covered. -/
theorem not_cov_beyond (iU3 K nW : ℕ) : ¬ Cov iU3 K nW (Aff.ent iU3 (nW / K) (nW % K)) := by
  intro h
  obtain ⟨x, hx, _, h2, h3⟩ := h ({ tree := iU3, row := nW / K, idx := nW % K, coef := oneE } : Ent)
    (by show _ ∈ [({ tree := iU3, row := nW / K, idx := nW % K, coef := oneE } : Ent)]
        exact List.mem_singleton.2 rfl)
  have e : x = nW := by
    have a := Nat.div_add_mod x K
    have b := Nat.div_add_mod nW K
    simp only at h2 h3
    rw [← h2, ← h3] at a
    omega
  omega

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.reads_covered_said
#print axioms VerifiableInference.Desc.First.Att.P.reads_covered_heard
#print axioms VerifiableInference.Desc.First.Att.P.not_cov_beyond
