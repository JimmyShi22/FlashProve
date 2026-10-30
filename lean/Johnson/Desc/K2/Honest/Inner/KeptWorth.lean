-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Inner/KeptWorth.lean: WHAT A FORM ON A KEPT MEMBER's TABLE, CARRIED OVER BY A
CODE SWITCH (`switchAddKept`, OnBytes/Iop/Cs.lean), IS WORTH ON THE HONEST NEW MESSAGES: the form on
the member's own entries. On the copy it reads all places but the pad's; at the pad's places it
reads the OLD pad, which lies in the carrying message's rest. Statements and proofs.

  `kept_fits`, `kept_target`, `kept_code`   the member's shape and its copy's, as the program's test
                    on the target ties them; there is a target for each; its code is the old one
  `size_copy`       the size of a copy's main table
  `Lists.sum_range_getD`  a sum over a list's numbers is the sum over the list
  `worth_on_copy`   a piece that stands on one copy alone
  `pad_inside`, `pad_fits`   a place of a member's pad lies in a real row, inside the table; the old
                    pad lies inside the rest
  `worth_kept`      the form on the member's own entries

By: `addKept_new`, `addKept_g`, `addKept_other` (OnBytes/Slice/BlkCsKept.lean); `padPlaces_nodup`,
`pad_index_at` (Johnson/Top/H/SwitchPads.lean, SwitchKeptRec.lean); Inner/RestIsPartsProof.lean.

Limits. Nothing on any property.

-/
import Johnson.Desc.K2.Honest.Inner.RowWorth

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest
open OnBytes
open OnBytes.Slice (GE rdE coefAt formAt stretchAt)
open OnBytes.Means (Words tableSize)
open Johnson.Prover.Send (Rows)
open Finset (range)

variable {S : Statement} {old : SingleRows} {T : SwitchTarget} {g : Nat} {anew : Array Nat}
  {W : Left} {V : Nat → Rows}

/-- The member's shape and its copy's. -/
theorem kept_fits (A : AtSwitch S old T g anew W V) (a : Nat) (s : OracleShape) (k : KeptTarget)
    (hs : (sizesAt S old T).kept[a]? = some s) (hk : T.kept.toList[a]? = some k) :
    _root_.Tw.K2.KeptFits S.codes s k.shape := by
  have hs' : ((switchKept old).toList.map fun o => (S.oracles.getD o default).shape)[a]? =
      some s := hs
  rw [List.getElem?_map] at hs'
  obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.1 hs'
  have hz : (o, k) ∈ (switchKept old).toList.zip T.kept.toList := by
    apply List.mem_of_getElem? (i := a)
    rw [List.getElem?_zip_eq_some]
    exact ⟨ho, hk⟩
  have hm : (o, k) ∈ (switchKept old).zip T.kept := by
    rw [← Array.mem_toList_iff, Array.toList_zip]
    exact hz
  exact A.target.keptShapes _ hm

/-- There is a target for each kept member. -/
theorem kept_target (A : AtSwitch S old T g anew W V) (a : Nat) (s : OracleShape)
    (hs : (sizesAt S old T).kept[a]? = some s) : ∃ k, T.kept.toList[a]? = some k := by
  have ha : a < (sizesAt S old T).kept.length := (List.getElem?_eq_some_iff.1 hs).1
  have e : (sizesAt S old T).kept.length = (switchKept old).size := by
    show ((switchKept old).toList.map _).length = _
    rw [List.length_map, Array.length_toList]
  have hk : a < T.kept.toList.length := by
    have := A.target.keptCount
    rw [Array.length_toList]
    omega
  exact ⟨_, List.getElem?_eq_getElem hk⟩

/-- The member's code is the old main code. -/
theorem kept_code (A : AtSwitch S old T g anew W V) (a : Nat) (s : OracleShape)
    (hs : (sizesAt S old T).kept[a]? = some s) : s.code = old.code := by
  have hs' : ((switchKept old).toList.map fun o => (S.oracles.getD o default).shape)[a]? =
      some s := hs
  rw [List.getElem?_map] at hs'
  obtain ⟨o', ho', rfl⟩ := Option.map_eq_some_iff.1 hs'
  exact A.fits.keptCode o' (List.mem_of_getElem? ho')

/-- The size of a copy's main table. -/
theorem size_copy (A : AtSwitch S old T g anew W V) (a : Nat) (s : OracleShape) (o : Nat)
    (hs : (sizesAt S old T).kept[a]? = some s) (ho : anew.toList[a]? = some o) :
    tableSize S o .main =
      2 ^ (ceilLog2 s.mainRows + (S.codes.base.getD old.code default).logEll) := by
  obtain ⟨k, hk⟩ := kept_target A a s hs
  have K := kept_fits A a s k hs hk
  have hk' : T.kept[a]? = some k := by rw [← Array.getElem?_toList]; exact hk
  have ho' : anew[a]? = some o := by rw [← Array.getElem?_toList]; exact ho
  have hc := A.seated.copies a k hk'
  rw [ho'] at hc
  obtain ⟨x, hx, hxs⟩ := Option.map_eq_some_iff.1 hc
  have hpos : 0 < k.shape.mainRows := A.keptPos k (List.mem_of_getElem? hk)
  rw [size_main S o x hx (by rw [hxs]; exact hpos), hxs, K.rows]
  have e : (S.codes.base.getD k.shape.code default).logEll =
      (S.codes.base.getD old.code default).logEll := by
    show ceilLog2 _ = ceilLog2 _
    rw [K.length, kept_code A a s hs]
  rw [e]

/-- A sum over a list's numbers is the sum over the list. -/
theorem Lists.sum_range_getD {α : Type} (F : α → GE) (d : α) : ∀ l : List α,
    ∑ q ∈ range l.length, F (l.getD q d) = (l.map F).sum
  | [] => by simp
  | x :: l => by
    rw [List.length_cons, Finset.sum_range_succ', List.map_cons, List.sum_cons,
      ← Lists.sum_range_getD F d l, add_comm]
    rfl

/-- A piece that stands on one copy alone. -/
theorem worth_on_copy (A : AtSwitch S old T g anew W V) (o : Nat) (ho : o ∈ anew.toList)
    (f : Nat → GE) :
    worthOf S (newWords (sizesAt S old T) g anew V) g anew
        (fun o' q J => if o == o' && q == .main then f J else 0) =
      ∑ J ∈ range (tableSize S o .main),
        f J * newWords (sizesAt S old T) g anew V o .main J := by
  have hap := A.seated.apart
  rw [List.cons_append, List.nodup_cons, List.nodup_append] at hap
  have hne : (o == g) = false := by
    simp only [beq_eq_false_iff_ne]
    exact fun e => hap.1 (List.mem_append_left _ (e ▸ ho))
  unfold worthOf
  simp only [hne, Bool.false_and, Bool.false_eq_true, if_false, zero_mul, Finset.sum_const_zero,
    zero_add]
  rw [Lists.sum_single _ anew.toList o hap.2.1 ho]
  · simp
  · intro y _ hy
    have : (o == y) = false := by
      simp only [beq_eq_false_iff_ne]
      exact fun e => hy e.symm
    simp [this]

/-- A place of a kept member's pad: in a real row, inside the table. -/
theorem pad_inside (A : AtSwitch S old T g anew W V) (a : Nat) (s : OracleShape)
    (hs : (sizesAt S old T).kept[a]? = some s) (p : PadPlace) (hp : p ∈ padPlaces S.codes s) :
    p.index % 2 ^ ceilLog2 s.mainRows < s.mainRows ∧
      p.index < 2 ^ (ceilLog2 s.mainRows + (S.codes.base.getD old.code default).logEll) := by
  obtain ⟨k, hk⟩ := kept_target A a s hs
  have K := kept_fits A a s k hs hk
  have hpos : 0 < s.mainRows := by
    rw [← K.rows]
    exact A.keptPos k (List.mem_of_getElem? hk)
  obtain ⟨place, h1, h2⟩ := Johnson.Top.H.pad_index_at S.codes s K.oldBare hpos p hp
  rw [kept_code A a s hs] at h1
  have hR := SwitchPlaces.le_two_pow_ceilLog2' s.mainRows
  have hm : p.index % 2 ^ ceilLog2 s.mainRows = s.mainRows - 1 := by
    rw [h2, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  have hd : p.index / 2 ^ ceilLog2 s.mainRows = place := by
    rw [h2, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt (by omega),
      Nat.zero_add]
  refine ⟨by omega, ?_⟩
  exact VerifiableInference.Desc.First.K2Hands.lt_pow_of _ _ s.mainRows _ _ (by omega) hR
    (by rw [hd]; exact h1) (SwitchPlaces.le_two_pow_ceilLog2' _)

/-- The old pad lies inside the rest. -/
theorem pad_fits (A : AtSwitch S old T g anew W V) (a : Nat) (s : OracleShape)
    (hs : (sizesAt S old T).kept[a]? = some s) :
    (switchParts S old).oldPadAt.getD a 0 + (padPlaces S.codes s).length ≤
      (rest (sizesAt S old T) W).length := by
  have hs' : ((switchKept old).toList.map fun o => (S.oracles.getD o default).shape)[a]? =
      some s := hs
  rw [List.getElem?_map] at hs'
  obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.1 hs'
  have ha : a < (switchKept old).size := by
    have := (List.getElem?_eq_some_iff.1 ho).1
    rwa [Array.length_toList] at this
  have e : (switchKept old)[a] = o := by
    have h2 := (List.getElem?_eq_some_iff.1 ho).2
    rw [Array.getElem_toList] at h2
    exact h2
  have h := (Johnson.Top.H.parts_laws S old).2 a ha
  rw [e] at h
  rw [(restIsParts S old T W A.target.masks A.fits).1]
  exact h

/-- **A form on a kept member's table, carried over.** -/
theorem worth_kept (A : AtSwitch S old T g anew W V) (a : Nat) (s : OracleShape) (o : Nat)
    (hs : (sizesAt S old T).kept[a]? = some s) (ho : anew.toList[a]? = some o) (c : Form) :
    worthOf S (newWords (sizesAt S old T) g anew V) g anew
        (coefAt (switchAddKept {} (padPlaces S.codes s) o g .main (SwitchPlaces.make S.codes T)
          ((switchParts S old).oldPadAt.getD a 0) c)) =
      ∑ J ∈ range (2 ^ (ceilLog2 s.mainRows + (S.codes.base.getD old.code default).logEll)),
        formAt c J * (W.kept a).entryIn s J := by
  have hap := A.seated.apart
  rw [List.cons_append, List.nodup_cons, List.nodup_append] at hap
  have hmem : o ∈ anew.toList := List.mem_of_getElem? ho
  have hne : o ≠ g := fun e => hap.1 (List.mem_append_left _ (e ▸ hmem))
  have hnd := Johnson.Top.H.padPlaces_nodup S.codes s
  have hsplit : worthOf S (newWords (sizesAt S old T) g anew V) g anew
      (coefAt (switchAddKept {} (padPlaces S.codes s) o g .main (SwitchPlaces.make S.codes T)
        ((switchParts S old).oldPadAt.getD a 0) c)) =
      worthOf S (newWords (sizesAt S old T) g anew V) g anew (fun o' q J =>
        (if o == o' && q == .main then
          (if J ∈ (padPlaces S.codes s).map (·.index) then 0 else formAt c J) else 0) +
        (if g == o' && T.rest.part == q then
          stretchAt (SwitchPlaces.make S.codes T) ((switchParts S old).oldPadAt.getD a 0)
            (padPlaces S.codes s).length
            (fun t => formAt c ((padPlaces S.codes s).getD t default).index) J else 0)) := by
    apply worthOf_congr
    · intro J _
      rw [OnBytes.Slice.addKept_g _ _ _ _ _ _ _ _ hne J, OnBytes.Slice.coefAt_empty, A.restMain]
      have : (o == g) = false := by simpa using hne
      simp [this]
    · intro o' ho' J _
      have hg' : (g == o') = false := by
        simp only [beq_eq_false_iff_ne]
        exact fun e => hap.1 (List.mem_append_left _ (e ▸ ho'))
      by_cases e : o' = o
      · subst e
        rw [OnBytes.Slice.addKept_new _ _ _ _ _ _ _ _ hne hnd J, OnBytes.Slice.coefAt_empty]
        simp [hg']
      · rw [OnBytes.Slice.addKept_other _ _ _ _ _ _ _ _ o' .main (fun h => e h.1)
          (fun h => by simp [h.1] at hg') J, OnBytes.Slice.coefAt_empty]
        have : (o == o') = false := by
          simp only [beq_eq_false_iff_ne]
          exact fun h => e h.symm
        simp [this, hg']
  rw [hsplit, worthOf_add, worth_on_copy A o hmem, worth_stretch A _ _ _ (pad_fits A a s hs),
    size_copy A a s o hs ho]
  have hrest : ∑ t ∈ range (padPlaces S.codes s).length,
      formAt c ((padPlaces S.codes s).getD t default).index *
        (rest (sizesAt S old T) W).getD ((switchParts S old).oldPadAt.getD a 0 + t) zeroG =
      (((padPlaces S.codes s).map (·.index)).map fun J =>
        formAt c J * (W.kept a).entryIn s J).sum := by
    rw [List.map_map, ← Lists.sum_range_getD _ default]
    apply Finset.sum_congr rfl
    intro t ht
    have ht' := Finset.mem_range.1 ht
    have hp : (padPlaces S.codes s)[t]? = some ((padPlaces S.codes s).getD t default) := by
      rw [List.getD_eq_getElem _ _ ht', List.getElem?_eq_getElem ht']
    have h6 := (restIsParts S old T W A.target.masks A.fits).2.2.2.2.2 a s t _ hs hp
    have hin := (pad_inside A a s hs _ (List.mem_of_getElem? hp)).1
    show _ = formAt c _ * (W.kept a).entryIn s _
    unfold Held.entryIn
    rw [if_pos hin]
    congr 1
  rw [hrest]
  apply kept_worth _ _ hnd
  · intro J hJ
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hJ
    exact (pad_inside A a s hs p hp).2
  · intro J hJ hn
    apply word_copy A a s o hs ho J hJ
    intro hm
    obtain ⟨p, hp, e⟩ := List.mem_map.1 hm
    exact hn (List.mem_map.2 ⟨p, (List.mem_filter.1 hp).1, e⟩)

end VerifiableInference.Desc.K2.Honest

#print axioms VerifiableInference.Desc.K2.Honest.size_copy
#print axioms VerifiableInference.Desc.K2.Honest.worth_on_copy
#print axioms VerifiableInference.Desc.K2.Honest.worth_kept
