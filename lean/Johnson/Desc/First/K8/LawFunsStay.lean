-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/LawFunsStay.lean: THE SMALLNESS TEST, ITS FIRST HALF: THE BLOCK OF THE DRAW
LEAVES THE CLOSED LIST OF TABLES, AND WHAT THE LINK'S KIND HAS HEARD, AS THEY WERE.

"The closed list is what the link's kind has heard" is a fact on the carried record that is laid
where the list is closed and is spent behind the draw. So it has to ride through the block of the
draw, in both directions. Here:
  `putTl_own`, `putTl_funs`: laying a record of the smallness test leaves what a layers' link's own
    rounds returned (`S.own?`) and the tables as the claims take them (`S.funs?`).
  `hear_leaves_own`, `hear_leaves_funs`: so the kind's block leaves both.
  `hear_leaves_list`: the kind's block leaves the record's own list of tables and its mark "closed".
  `FunsAre s`: where a link is open and its list is closed, the list is what `S.funs?` gives.
    `OwnFunsAre s`: the like at a layers' link, against `S.own?`'s tables.
  `hear_funsAre`, `hear_ownFunsAre`: **at a yes of the block each holds behind if and only if it
    holds in front.**
Statements and proofs.
Limits. That either fact holds anywhere is not said: it is a law on the block that closes the list.

-/
import Johnson.Desc.First.K8.LawLeaves
import Johnson.Desc.First.K8.HearMeans

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8

open OnBytes.Model

theorem putTl_own (s : S) (tl : HTailF2) : (s.putTl tl).own? = s.own? := by
  unfold S.putTl S.own?
  cases h : s.here with
  | head a => by_cases ho : a.opened <;> simp [h, ho]
  | _ => simp [h]

theorem putTl_funs (s : S) (tl : HTailF2) : (s.putTl tl).funs? = s.funs? := by
  unfold S.putTl S.funs?
  cases h : s.here with
  | head a => by_cases ho : a.opened <;> simp [h, ho]
  | _ => simp [h]

theorem hear_leaves_own {Cl : Type} (p : Par) : (approximateRangeProofDrawKind (Cl := Cl) atS p).Leaves S.own? :=
  hear_leaves _ putTl_own p

theorem hear_leaves_funs {Cl : Type} (p : Par) : (approximateRangeProofDrawKind (Cl := Cl) atS p).Leaves S.funs? :=
  hear_leaves _ putTl_funs p

/-- The kind's block leaves the record's own list of tables and its mark "closed". -/
theorem hear_leaves_list {Cl : Type} (p : Par) :
    (approximateRangeProofDrawKind (Cl := Cl) atS p).Leaves fun s => s.tl?.map fun tl => (tl.funClosed, tl.funs) := by
  intro s rs gs s' hd
  obtain ⟨r, rfl⟩ := decide_one atS p s s' rs gs hd
  obtain ⟨tl, ht, hm⟩ := (decide_atS_iff p s s' r gs).1 hd
  rw [hm.2.2.2.2.2.2.2.2]
  beta_reduce
  rw [putTl_tl s tl _ ht, ht]
  rfl

/-- Where a link is open and its list is closed, the list is what the claims take. -/
def FunsAre (s : S) : Prop :=
  ∀ tl, s.tl? = some tl → tl.funClosed = true → s.funs? = some tl.funs

/-- The like at a layers' link, against what its own rounds returned. -/
def OwnFunsAre (s : S) : Prop :=
  ∀ tl o, s.tl? = some tl → s.own? = some o → tl.funClosed = true → tl.funs = o.funs

/-- Both facts read the three readings alone. -/
theorem funsAre_congr {s s' : S}
    (h1 : (s'.tl?.map fun tl => (tl.funClosed, tl.funs)) =
      s.tl?.map fun tl => (tl.funClosed, tl.funs))
    (h2 : s'.funs? = s.funs?) (h : FunsAre s) : FunsAre s' := by
  intro tl' ht' hc'
  rw [ht'] at h1
  cases ht : s.tl? with
  | none => rw [ht] at h1; simp at h1
  | some tl =>
    rw [ht] at h1
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    rw [h2, h1.2]
    exact h tl ht (h1.1 ▸ hc')

theorem ownFunsAre_congr {s s' : S}
    (h1 : (s'.tl?.map fun tl => (tl.funClosed, tl.funs)) =
      s.tl?.map fun tl => (tl.funClosed, tl.funs))
    (h2 : s'.own? = s.own?) (h : OwnFunsAre s) : OwnFunsAre s' := by
  intro tl' o ht' ho' hc'
  rw [ht'] at h1
  cases ht : s.tl? with
  | none => rw [ht] at h1; simp at h1
  | some tl =>
    rw [ht] at h1
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    rw [h1.2]
    exact h tl o ht (h2 ▸ ho') (h1.1 ▸ hc')

/-- **At a yes of the block the fact holds behind if and only if it holds in front.** -/
theorem hear_funsAre {Cl : Type} (p : Par) (s s' : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (hd : (approximateRangeProofDrawKind (Cl := Cl) atS p).decide s rs gs = .ok s') :
    FunsAre s' ↔ FunsAre s :=
  ⟨funsAre_congr (hear_leaves_list p s rs gs s' hd).symm (hear_leaves_funs p s rs gs s' hd).symm,
    funsAre_congr (hear_leaves_list p s rs gs s' hd) (hear_leaves_funs p s rs gs s' hd)⟩

theorem hear_ownFunsAre {Cl : Type} (p : Par) (s s' : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (hd : (approximateRangeProofDrawKind (Cl := Cl) atS p).decide s rs gs = .ok s') :
    OwnFunsAre s' ↔ OwnFunsAre s :=
  ⟨ownFunsAre_congr (hear_leaves_list p s rs gs s' hd).symm (hear_leaves_own p s rs gs s' hd).symm,
    ownFunsAre_congr (hear_leaves_list p s rs gs s' hd) (hear_leaves_own p s rs gs s' hd)⟩

end VerifiableInference.Desc.First.K8

#print axioms VerifiableInference.Desc.First.K8.hear_leaves_own
#print axioms VerifiableInference.Desc.First.K8.hear_leaves_funs
#print axioms VerifiableInference.Desc.First.K8.hear_leaves_list
#print axioms VerifiableInference.Desc.First.K8.hear_funsAre
#print axioms VerifiableInference.Desc.First.K8.hear_ownFunsAre
