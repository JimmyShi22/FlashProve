-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/KeyLaw/GroupSays.lean: THE ROWS THAT THE KIND'S OWN ROUTINES MAKE FOR A
GROUP (K3Key.lean: rowOfAff, rowOfPlane, groupRows, at the verifier program's Wf.planesAt) say their
claims of words EXACTLY IF the typed lookup's rows (rowsF, read) hold of the entries that are read
off these words. At the level of values: no condition on how a coefficient is laid.

Main names:
  typed_iff: a typed row holds of entries tied to words exactly if its value at the words is its
    target.
  plane_value: the row "target, then the planes' term, then the mask form", applied to words.
  says_iff_aff, says_iff_plane: one row of either kind.
  groupRows_iff: ALL ROWS OF A LOOKUP.

Limits. Tied, TablesFit, that the homes stand inside the statement's mask tables, and that every
claim on the planes has mu + d pairs (one for each variable of the table of bits) are premises.
Soundness spends the arrow from the rows' claims to the typed rows.

-/
import Johnson.Desc.First.Look.KeyLaw.SaysAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3.KeyLaw
open OnBytes OnBytes.Slice Finset
open OnBytes.Model (Fork Aff Reading)
open OnBytes.Params (WfLookup WfPublic)
open Lk6 (Dat)
open Lk6.Mid (RowF rdRow)

variable {A : Dat GE} {sl : Slot → A.J} {μ : A.J → GE} {w : Means.Words GE} {x : WfPublic}
  {codes : Codes} {i : ℕ} {hs : List Slot}

/-- Turning the coefficients leaves the mask entries. -/
theorem negMasks_slots {m : MaskForm} {L : List Slot} (h : ∀ p ∈ m, p.1 ∈ L) :
    ∀ p ∈ negMasks m, p.1 ∈ L := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
  exact h q hq

/-- **A typed row holds of entries tied to words exactly if its value at the words is its target.**
-/
theorem typed_iff (hr : A.pl ≤ 2 ^ A.mu) (hTd : Tied A sl μ w x codes i hs) (l : WfLookup)
    (hi : x.lookups[i]? = some l) (hpl : Wf.planesOf l = A.pl) (r : RowF)
    (hms : ∀ p ∈ r.masks, p.1 ∈ hs) :
    (rdRow A sl r).Holds μ ↔
      valueF A.mu A.d r (fun s => w s.oracle .mask s.index)
        (fun t j => Planes.bitsOf x codes i (w x.messageId .main) t j) = r.target := by
  have e : valueF A.mu A.d r (fun s => μ (sl s)) (fun t j => if j < A.pl then μ (A.bAt t j) else 0)
      =
      valueF A.mu A.d r (fun s => w s.oracle .mask s.index)
        fun t j => Planes.bitsOf x codes i (w x.messageId .main) t j := by
    refine valueF_congr A.mu A.d _ (fun p hp => hTd.mask p.1 (hms p hp)) fun j hj t ht => ?_
    by_cases hjp : j < A.pl
    · rw [if_pos hjp]
      exact hTd.bit t ht j hjp
    · rw [if_neg hjp]
      exact (bitsOf_none x codes i l hi _ t j (by rw [hpl]; exact Nat.le_of_not_lt hjp)).symm
  unfold Cb.LdLkp.Row.Holds
  rw [typed_value A sl μ hr, e]
  exact Iff.rfl

/-- The row "target, then the planes' term, then the mask form", applied to words. -/
theorem plane_value (St : Statement) (hT : TablesFit St x codes) (l : WfLookup)
    (hi : x.lookups[i]? = some l) (hl : Wf.lookupOk Wf.fBits l = true)
    (hh : ((Wf.layout x.lookups (Planes.codeOf x codes).ell).head?.any fun b =>
      decide (2 ^ b.bits ≤ (Planes.codeOf x codes).ell)) = true)
    (m : MaskForm) (sc : E) (ps : List (E × E)) (t : E) (hm : MasksIn St m)
    (hps : ps.length = l.mu + l.d) :
    Means.value Reading.gl St
        ((Wf.planesAt x codes i { target := t } { scalar := sc, pairs := ps }).addMasks m) w =
      valueF l.mu l.d ⟨readForm m, [(readE sc, pairsF ps)], readE t⟩
        (fun s => w s.oracle .mask s.index)
        fun t j => Planes.bitsOf x codes i (w x.messageId .main) t j := by
  have e := value_terms St w x codes i hT l hi hl hh [(sc, ps)] { target := t }
    (fun a ha => by rw [List.mem_singleton.1 ha]; exact hps)
  rw [value_addMasks St w m _ hm]
  have e' : Means.value Reading.gl St
      (Wf.planesAt x codes i { target := t } { scalar := sc, pairs := ps }) w = _ := e
  rw [e', value_bare, zero_add]
  unfold valueF readForm
  simp only [List.map_map, List.map_cons, List.map_nil]
  rw [add_comm]
  rfl

variable (St : Statement) (hr : A.pl ≤ 2 ^ A.mu) (hTd : Tied A sl μ w x codes i hs)
  (hT : TablesFit St x codes) (l : WfLookup) (hi : x.lookups[i]? = some l)
  (hl : Wf.lookupOk Wf.fBits l = true)
  (hh : ((Wf.layout x.lookups (Planes.codeOf x codes).ell).head?.any fun b =>
    decide (2 ^ b.bits ≤ (Planes.codeOf x codes).ell)) = true)
  (hmu : l.mu = A.mu) (hd : l.d = A.d) (hpl : Wf.planesOf l = A.pl)
  {F : Fork} {homeA : Array Slot} {home : ℕ → Slot} (hA : HomeArr homeA home)
  (hhs : ∀ s ∈ homeA.toList, s ∈ hs)
  (hIn : ∀ s ∈ homeA.toList, s.oracle < St.oracles.size ∧
    s.index < Means.tableSize St s.oracle .mask)
include hr hTd hi hpl hA hhs hIn

/-- **A claim that reads hidden values alone.** -/
theorem says_iff_aff {a : Aff} {R : GRow} (h : rowOfAff F homeA a = some R) :
    Means.Says Reading.gl St R w ↔ (rdRow A sl (rowA F home a)).Holds μ := by
  unfold rowOfAff at h
  cases hy : maskSide F homeA a with
  | none => rw [hy] at h; cases h
  | some y =>
    rw [hy] at h
    obtain rfl := Option.some.inj h
    have hsl : ∀ p ∈ negMasks y.1, p.1 ∈ homeA.toList := negMasks_slots (maskSide_slots hy)
    rw [← rowA_reads hA hy, typed_iff hr hTd l hi hpl _ (fun p hp => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      exact hhs _ (hsl q hq))]
    unfold Means.Says
    rw [value_addMasks St w _ _ (fun p hp => hIn _ (hsl p hp)), value_bare, zero_add,
      Lk6.Mid.target_addMasks]
    unfold valueF readForm
    simp only [List.map_map, List.map_nil, List.sum_nil, add_zero]
    exact Iff.rfl

include hT hl hh hmu hd

/-- **A claim that reads the planes.** -/
theorem says_iff_plane (turned : Bool) {c : PlaneClaim} {R : GRow}
    (hc : c.pairs.length = l.mu + l.d)
    (h : rowOfPlane (Wf.planesAt x codes i) F homeA turned c = some R) :
    Means.Says Reading.gl St R w ↔ (rdRow A sl (rowP F home turned c)).Holds μ := by
  unfold rowOfPlane at h
  cases hy : maskSide F homeA c.lead with
  | none => rw [hy] at h; cases h
  | some y =>
    rw [hy] at h
    obtain rfl := Option.some.inj h
    have hs0 := maskSide_slots hy
    have hsl : ∀ p ∈ negMasks y.1, p.1 ∈ homeA.toList := negMasks_slots hs0
    rw [← rowP_reads hA hy turned]
    cases turned with
    | true =>
      simp only [if_true]
      rw [typed_iff hr hTd l hi hpl _ (fun p hp => by
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
        exact hhs _ (hsl q hq))]
      unfold Means.Says
      rw [plane_value St hT l hi hl hh _ _ _ _ (fun p hp => hIn _ (hsl p hp)) hc,
        Lk6.Mid.target_addMasks, Planes.planesAt_target, hmu, hd]
      exact Iff.rfl
    | false =>
      simp only [Bool.false_eq_true, if_false]
      rw [typed_iff hr hTd l hi hpl _ (fun p hp => by
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
        exact hhs _ (hs0 q hq))]
      unfold Means.Says
      rw [plane_value St hT l hi hl hh _ _ _ _ (fun p hp => hIn _ (hs0 p hp)) hc,
        Lk6.Mid.target_addMasks, Planes.planesAt_target, hmu, hd]
      exact Iff.rfl

/-- **All rows of a lookup.** -/
theorem groupRows_iff {objects : List Aff} {planes : List PlaneClaim} {rows : List GRow}
    (hc : ∀ c ∈ planes, c.pairs.length = l.mu + l.d)
    (h : groupRows (Wf.planesAt x codes i) F homeA objects planes = some rows) :
    Means.AllSay Reading.gl St rows w ↔
      Cb.LdLkp.RowsHold ((rowsF F home objects planes).map (rdRow A sl)) μ := by
  have aff := @says_iff_aff A sl μ w x codes i hs St hr hTd l hi hpl F homeA home hA hhs hIn
  have pln := @says_iff_plane A sl μ w x codes i hs St hr hTd hT l hi hl hh hmu hd hpl F homeA home
    hA hhs hIn
  unfold groupRows at h
  unfold rowsF
  match planes, hg : objects.getLast?, h, hc with
  | [leaves, value, counts], some bits, h, hc =>
    simp only at h ⊢
    cases h0 : objects.dropLast.mapM (rowOfAff F homeA) with
    | none => simp [h0] at h
    | some front =>
      cases h1 : rowOfPlane (Wf.planesAt x codes i) F homeA true leaves with
      | none => simp [h0, h1] at h
      | some r1 =>
        cases h2 : rowOfAff F homeA bits with
        | none => simp [h0, h1, h2] at h
        | some r2 =>
          cases h3 : rowOfPlane (Wf.planesAt x codes i) F homeA false value with
          | none => simp [h0, h1, h2, h3] at h
          | some r3 =>
            cases h4 : rowOfPlane (Wf.planesAt x codes i) F homeA true counts with
            | none => simp [h0, h1, h2, h3, h4] at h
            | some r4 =>
              simp only [h0, h1, h2, h3, h4, Option.bind_eq_bind, Option.bind_some,
                Option.pure_def, Option.some.injEq] at h
              subst h
              have e1 := pln true (hc leaves (by simp)) h1
              have e2 := aff h2
              have e3 := pln false (hc value (by simp)) h3
              have e4 := pln true (hc counts (by simp)) h4
              have ef : ∀ (os : List Aff) (fr : List GRow), os.mapM (rowOfAff F homeA) = some fr →
                  ((∀ R ∈ fr, Means.Says Reading.gl St R w) ↔
                    ∀ a ∈ os, (rdRow A sl (rowA F home a)).Holds μ) := by
                intro os
                induction os with
                | nil =>
                  intro fr hfr
                  cases hfr
                  simp
                | cons a os ih =>
                  intro fr hfr
                  rw [List.mapM_cons] at hfr
                  cases ha : rowOfAff F homeA a with
                  | none => simp [ha] at hfr
                  | some Ra =>
                    cases hos : os.mapM (rowOfAff F homeA) with
                    | none => simp [ha, hos] at hfr
                    | some fr' =>
                      simp only [ha, hos, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
                        Option.some.injEq] at hfr
                      subst hfr
                      simp only [List.forall_mem_cons]
                      rw [aff ha, ih fr' hos]
              unfold Means.AllSay Cb.LdLkp.RowsHold
              simp only [List.map_append, List.map_map, List.map_cons, List.map_nil,
                List.forall_mem_append, List.forall_mem_cons, List.forall_mem_map,
                List.not_mem_nil, false_imp_iff, implies_true, and_true, Function.comp]
              rw [ef _ _ h0, e1, e2, e3, e4]

end VerifiableInference.Desc.K3.KeyLaw

#print axioms VerifiableInference.Desc.K3.KeyLaw.typed_iff
#print axioms VerifiableInference.Desc.K3.KeyLaw.says_iff_aff
#print axioms VerifiableInference.Desc.K3.KeyLaw.says_iff_plane
#print axioms VerifiableInference.Desc.K3.KeyLaw.groupRows_iff
