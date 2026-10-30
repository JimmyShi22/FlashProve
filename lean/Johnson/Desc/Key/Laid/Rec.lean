-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Key/Laid/Rec.lean: the yes of the shared chain's "(rec_gamma)" gives `RecLaid`
(Johnson/Desc/Key/Laid/RecDef.lean). Theorems.

Main names.
  `addRowsFrom_eq` | `addRowsP_eq`: the plain ground's adding of a list of rows, its yes read back:
    the record behind is the record in front but for its statement; the messages and the codes are
    as they were; the group's open rows are those in front and then the list; every other group is
    as it was.
  `laid_rec`: `laysRec p d rs = some d'` gives all of `RecLaid`'s fields.
  `recLaid_irrefl`: `RecLaid` holds of no record and itself: G_u has a member more behind.

Limits. Of joinP's eight tests nothing is carried here. Of the function `laysRec`; of the block that
decides by it: Johnson/Desc/Key/Laid/AtBlocks.lean. Of the form "a yes gives". Nothing on soundness
or on hiding.
-/
import Johnson.Desc.Key.Laid.RecDef
import Johnson.Desc.Key.Laid.Joined
import Johnson.Desc.Key.Laid.GroundYes

set_option autoImplicit false
set_option relaxedAutoImplicit false

open OnBytes OnBytes.Slice
open Desc.Plain (DState Par)
open VerifiableInference.Desc.Ground (addRowP addRowsP addRowsFrom ok)
open _root_.Desc.K14 (St laysRec laysRecL)
open _root_.Desc.K14.Law (recRows)

namespace VerifiableInference.Desc.Key

theorem withRow_groupOff' (S : Statement) (g : Nat) (r : Row) (i : Nat) (h : g ≠ i) :
    (withRow S g r).groups[i]? = S.groups[i]? := by
  simp [withRow, Array.getElem?_modify, h]

/-- The ground's adding of a list of rows, read back. -/
theorem addRowsFrom_eq {L : Type} (g : Nat) : ∀ (rows : List Row) (d d' : DState L) (G : Group),
    addRowsFrom g rows d = some d' → d.st.groups[g]? = some G →
    d'.loc = d.loc ∧ d'.book = d.book ∧ d'.roots = d.roots ∧ d'.opened = d.opened ∧
      d'.st.codes = d.st.codes ∧ d'.st.oracles = d.st.oracles ∧
      d'.st.groups.size = d.st.groups.size ∧
      d'.st.groups[g]? = some { G with rows := G.rows ++ rows.toArray } ∧
      ∀ i : Nat, i ≠ g → d'.st.groups[i]? = d.st.groups[i]?
  | [], d, d', G, h, hG => by
    obtain rfl := Option.some.inj h
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, fun _ _ => rfl⟩
    rw [hG]
    simp
  | row :: l, d, d', G, h, hG => by
    unfold addRowsFrom at h
    obtain ⟨d1, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    have e1 := addRowP_eq _ _ _ _ h1
    have s1 : d1.st = withRow d.st g row := by rw [e1]
    have hG1 : d1.st.groups[g]? = some { G with rows := G.rows.push row } := by
      rw [s1]
      exact withRow_group _ _ _ _ hG
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := addRowsFrom_eq g l d1 d' _ h2 hG1
    refine ⟨by rw [a1, e1], by rw [a2, e1], by rw [a3, e1], by rw [a4, e1], by rw [a5, s1]; rfl,
      by rw [a6, s1]; rfl, by rw [a7, s1]; simp [withRow], ?_, fun i hi => ?_⟩
    · rw [a8]
      simp
    · rw [a9 i hi, s1]
      exact withRow_groupOff' _ _ _ _ (Ne.symm hi)

theorem addRowsP_eq {L : Type} (d d' : DState L) (g : Nat) (rows : List Row) (G : Group)
    (h : addRowsP d g rows = some d') (hG : d.st.groups[g]? = some G) :
    d'.loc = d.loc ∧ d'.book = d.book ∧ d'.roots = d.roots ∧ d'.opened = d.opened ∧
      d'.st.codes = d.st.codes ∧ d'.st.oracles = d.st.oracles ∧
      d'.st.groups.size = d.st.groups.size ∧
      d'.st.groups[g]? = some { G with rows := G.rows ++ rows.toArray } ∧
      ∀ i : Nat, i ≠ g → d'.st.groups[i]? = d.st.groups[i]? := by
  unfold addRowsP at h
  split at h
  · exact addRowsFrom_eq g rows d d' G h hG
  · cases h

/-- **The yes of "(rec_gamma)" gives RecLaid.** -/
theorem laid_rec (p : Par) (d d' : St) (rs : List Fmt.RoundView) (h : laysRec p d rs = some d') :
    ∃ GU rows, RecLaid p d d' GU rows := by
  unfold laysRec at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨u0, hg, d1, hj, rows, hm, ha⟩ := h
  have hok : ok (laysRecL p d.loc) = true := by
    by_contra hne
    simp [guard, hne] at hg
  simp only [ok, laysRecL, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    beq_iff_eq] at hok
  obtain ⟨t1, t2, t3⟩ := hok
  obtain ⟨GU, gU, _, e1⟩ := joinP_eq _ _ _ _ _ hj
  have s1 : d1.st = withMessageInGroup d.st d.loc.gU d.loc.oU.oracle false GU := by rw [e1]
  have g1 : d1.st.groups[d.loc.gU]? = some (entered GU d.loc.oU.oracle false) := by
    rw [s1]
    exact joined_groupAt _ _ _ _ _ gU
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := addRowsP_eq _ _ _ _ _ ha g1
  refine ⟨GU, rows, by rw [a1, e1], by rw [a2, e1], by rw [a3, e1], by rw [a4, e1],
    by rw [a5, s1]; rfl, by rw [a6, s1]; simp [withMessageInGroup], t1, t2, t3, ?_, ?_,
    by rw [a7, s1]; simp [withMessageInGroup], gU, a8, ?_, hm,
    fun hI => Means.addRowsP_keeps ha (Means.joinP_keeps hj hI)⟩
  · intro x hx
    rw [a6, s1]
    exact joined_same _ _ _ _ _ x hx
  · intro o ho
    rw [a6, s1]
    exact joined_other _ _ _ _ _ _ (Ne.symm ho)
  · intro i hi
    rw [a9 i hi, s1]
    exact joined_groupOff _ _ _ _ _ _ (Ne.symm hi)

/-- RecLaid holds of no record and itself: G_u has a member more behind. -/
theorem recLaid_irrefl (p : Par) (d : St) (GU : Group) (rows : List Row) :
    ¬ RecLaid p d d GU rows := by
  intro h
  have e := Option.some.inj (h.gU.symm.trans h.gU')
  have t0 := congrArg (fun G : Group => G.members.size) e
  have t : GU.members.size = (entered GU d.loc.oU.oracle false).members.size := t0
  rw [entered_size] at t
  omega

end VerifiableInference.Desc.Key
