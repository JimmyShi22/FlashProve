-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/Carry.lean: what a constraint says of words does not turn where the statement
grows; and what (fold)'s two constraints mean at the two proximity tests, each test at its own
state.

A constraint that names messages of a statement T alone says of words the same at every statement
that has grown out of T (says_grows): the tables that it is on are the same, and it has the
coefficient 0 on every later message. A constraint that has been added names such messages alone
(there_of_addRowP).
Main names: coefficient_off, tableSize_grows, value_grows, says_grows, there_of_addRowP, Reaches
(from a state to the state at a group's test: the statement has grown, and THAT group's list of
constraints has grown at its end alone), foldSaysAt.

What is not claimed. That a run reaches the tests so (Reaches) is a premise; behind the begin of a
group's test its list is taken out, so Reaches ends in front of that begin. Nothing on soundness.

-/
import Johnson.Desc.K14.Law.LocSound
import Johnson.Desc.GrowsGround
import Johnson.Desc.Own.RowsAgree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open OnBytes.Model (Reading)
open OnBytes.Means (Words)
open VerifiableInference.Desc (Grows)
open VerifiableInference.Desc.Ground

variable {K : Type} [Field K] (ρ : Reading K)

/-- A sum of terms that are all 0. -/
theorem sum_map_zero {α : Type} (l : List α) (f : α → K) (h : ∀ a ∈ l, f a = 0) :
    (l.map f).sum = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, h a List.mem_cons_self,
      ih fun b hb => h b (List.mem_cons_of_mem _ hb), add_zero]

/-- A constraint has the coefficient 0 on every message that it does not name. -/
theorem coefficient_off (r : Row) (o : Nat) (h : o ∉ r.oracles) (pt : Part) (i : Nat) :
    ρ.val (r.coefficient o pt i) = 0 := by
  simp only [Row.oracles, List.mem_append, Array.toList_map, List.mem_map, not_or, not_exists,
    not_and] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  rw [Row.coefficient_val, sum_map_zero, sum_map_zero, sum_map_zero, sum_map_zero]
  · simp
  · intro f hf; rw [if_neg fun e => h4 f hf e.1]
  · intro w hw; rw [if_neg fun e => h3 w hw e.1]
  · intro u hu; rw [if_neg fun e => h2 u hu e.1]
  · intro t ht; rw [if_neg fun e => h1 t ht e.1]

/-- A table of a message that is there keeps its size where the statement grows. -/
theorem tableSize_grows (T T' : Statement) (g : Grows T T') (o : Nat) (ho : o < T.oracles.size)
    (pt : Part) : Means.tableSize T' o pt = Means.tableSize T o pt := by
  obtain ⟨x, hx⟩ : ∃ x, T.oracles[o]? = some x := ⟨T.oracles[o], by simp [ho]⟩
  obtain ⟨x', hx', gx⟩ := g.2.2 o x hx
  simp [Means.tableSize, Statement.has, Statement.tableBits, Statement.rowBits,
    Statement.placeBits, hx, hx', gx.1, g.1]

/-- No message is lost where the statement grows. -/
theorem size_grows (T T' : Statement) (g : Grows T T') : T.oracles.size ≤ T'.oracles.size := by
  by_contra h
  have h0 : T'.oracles.size < T.oracles.size := by omega
  obtain ⟨x', hx', _⟩ := g.2.2 T'.oracles.size T.oracles[T'.oracles.size] (by simp [h0])
  have := (Array.getElem?_eq_some_iff.1 hx').1
  omega

/-- **A constraint on messages of T, applied to words, gives the same at every statement that has
grown out of T.** -/
theorem value_grows (T T' : Statement) (g : Grows T T') (r : Row)
    (hr : ∀ o ∈ r.oracles, o < T.oracles.size) (m : Words K) :
    Means.value ρ T' r m = Means.value ρ T r m := by
  unfold Means.value
  rw [← Finset.sum_subset (Finset.range_mono (size_grows T T' g))]
  · refine Finset.sum_congr rfl fun o ho => ?_
    unfold Means.onTable
    rw [tableSize_grows T T' g o (Finset.mem_range.1 ho),
      tableSize_grows T T' g o (Finset.mem_range.1 ho)]
  · intro o _ ho
    have hoff : o ∉ r.oracles := fun h => ho (Finset.mem_range.2 (hr o h))
    unfold Means.onTable
    rw [Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero]
    · intro i _; rw [coefficient_off ρ r o hoff, zero_mul]
    · intro i _; rw [coefficient_off ρ r o hoff, zero_mul]

/-- So it says the same of words. -/
theorem says_grows (T T' : Statement) (g : Grows T T') (r : Row)
    (hr : ∀ o ∈ r.oracles, o < T.oracles.size) (m : Words K) :
    Means.Says ρ T' r m ↔ Means.Says ρ T r m := by
  unfold Means.Says
  rw [value_grows ρ T T' g r hr m]

/-- A constraint that has been added names messages that are there alone. -/
theorem there_of_addRowP (d d' : St) (g : Nat) (row : Row) (h : addRowP d g row = some d') :
    ∀ o ∈ row.oracles, o < d.st.oracles.size := by
  unfold addRowP at h
  split at h
  · rename_i hok
    simp only [ok, rowL, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hok
    obtain ⟨hG, _, _, h1, h2, h3, h4, _⟩ := hok
    obtain ⟨G, hG'⟩ := Option.isSome_iff_exists.1 hG
    simp only [hG', VerifiableInference.Desc.Ground.has, Option.map_some, Option.getD_some,
      Array.all_eq_true_iff_forall_mem, Bool.and_eq_true,
      ← VerifiableInference.Desc.Own.placeFits_agrees, Blk.placeOk] at h1 h2 h3 h4
    intro o ho
    simp only [Row.oracles, List.mem_append, Array.toList_map, List.mem_map,
      Array.mem_toList_iff] at ho
    rcases ho with ((⟨t, ht, rfl⟩ | ⟨u, hu, rfl⟩) | ⟨w, hw, rfl⟩) | ⟨f, hf, rfl⟩
    · exact lt_of_has _ _ _ (h1 t ht).2.1.1.2
    · exact lt_of_has _ _ _ (h2 u hu).1.1.2
    · exact lt_of_has _ _ _ (h3 w hw).2.1.1.2
    · exact lt_of_has _ _ _ (h4 f hf).1.1.1.2
  · cases h

/-- From a state to the state at a group's test: the statement has grown, and that group's list of
constraints has grown at its end alone. -/
structure Reaches (d e : St) (g : Nat) : Prop where
  grows : Grows d.st e.st
  later : Later d e g

/-- A state that is onward reaches, at every group. -/
theorem Reaches.refl (d : St) (g : Nat) : Reaches d d g := ⟨Grows.refl _, ⟨[], by simp⟩⟩

/-- **What (fold)'s two constraints mean at the two tests**, each test at its own state. -/
theorem foldSaysAt (p : Par) (d d' eU eO : St) (r : Fmt.RoundView) (m : Words K)
    (hS : p.S.sharedSplitNeeded = true) (h : split p d [r] = some d')
    (hO : Reaches d' eO d.loc.gOmega) (hU : Reaches d' eU d.loc.gU)
    (sO : Means.AllSay ρ eO.st (rowsOn eO d.loc.gOmega) m)
    (sU : Means.AllSay ρ eU.st (rowsOn eU d.loc.gU) m)
    (hP : Placed d'.st p.S d.loc (linLayOmega d.st.codes p.S)) :
    FoldEq p.S ((d.loc.psiSh.take p.S.kLo).map ρ.val) (d.loc.zFd.map ρ.val)
      (omegaOf d.loc (linLayOmega d.st.codes p.S) m) (uOf d.loc m) := by
  obtain ⟨row, x, G, kappa, d₁, d₂, hf, hx, hG, hok, hk, h2, h3⟩ := split_inv p d d' r hS h
  have hne : d.loc.gOmega ≠ d.loc.gU := by
    simp only [ok, splitL, List.all_cons, Bool.and_eq_true, bne_iff_ne] at hok
    exact hok.1
  have rO : rowsOn d' d.loc.gOmega = rowsOn d d.loc.gOmega ++
      [onOmega row G.members d.loc.oSp kappa (E.ofTriple x)] := by
    rw [rowsOn_addRowP_other d₂ d' _ _ _ h3 hne.symm, rowsOn_addRowP_same d₁ d₂ _ _ h2,
      rowsOn_takeMaskP d d₁ _ _ _ hk]
  have rU : rowsOn d' d.loc.gU = rowsOn d d.loc.gU ++
      [onU row G.members d.loc.oSp kappa (E.ofTriple x)] := by
    rw [rowsOn_addRowP_same d₂ d' _ _ h3, rowsOn_addRowP_other d₁ d₂ _ _ _ h2 hne,
      rowsOn_takeMaskP d d₁ _ _ _ hk]
  obtain ⟨mO, hmO⟩ := hO.later
  obtain ⟨mU, hmU⟩ := hU.later
  have g2 := addRowP_grows d₁ d₂ _ _ h2
  have g3 := addRowP_grows d₂ d' _ _ h3
  have tA : ∀ o ∈ (onOmega row G.members d.loc.oSp kappa (E.ofTriple x)).oracles,
      o < d'.st.oracles.size := fun o ho =>
    lt_of_lt_of_le (there_of_addRowP d₁ d₂ _ _ h2 o ho) (size_grows _ _ (g2.trans g3))
  have tB : ∀ o ∈ (onU row G.members d.loc.oSp kappa (E.ofTriple x)).oracles,
      o < d'.st.oracles.size := fun o ho =>
    lt_of_lt_of_le (there_of_addRowP d₂ d' _ _ h3 o ho) (size_grows _ _ g3)
  have ha := (says_grows ρ d'.st eO.st hO.grows _ tA m).1 (sO _ (by rw [hmO, rO]; simp))
  have hb := (says_grows ρ d'.st eU.st hU.grows _ tB m).1 (sU _ (by rw [hmU, rU]; simp))
  exact (foldMeansW ρ d'.st p.S d.loc _ row hf hP m).1
    (says_of_add ρ d'.st _ _ row (split_coefficient ρ row G.members d.loc.oSp kappa _)
      (split_target ρ row G.members d.loc.oSp kappa _) m ha hb)

end Desc.K14.Law
