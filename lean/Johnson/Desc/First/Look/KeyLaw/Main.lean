-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/KeyLaw/Main.lean: the two relations in which the kind's rows and claims,
read, are compared with the course's in one world of mask entries, and small lemmas for the joining
of the stretches (Hear.lean, Back.lean, Out.lean).

Main names:
  EvEq W x y: two rows have the same terms on the table of bits, and "mask form - target" has the
    same value in the world W. KeyEq W x y: two claims on leaves: the same point and value; the mask
    forms have the same value in W.
  evEq_rowA, keyEq_of: from the relations of Step.lean to these two.
  ordIs_table, ordIs_keys, ok_orders: the levels' orders. eqPairs_read, down_getD, snoc_inv: lists.

Limits. One world W of mask entries.

-/
import Johnson.Desc.First.Look.KeyLaw.Pat
import OnBytes.Tie.Pv.Lookup.Ends.PortA

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3.KeyLaw
open OnBytes OnBytes.Slice OnBytes.K.Kc
open OnBytes.Model (Fork Aff Psc RoundName RoundForm Reading World eqTab orderDefault ofNat)
open OnBytes.PscRun (took Later Sized Filled Ran)
open First.Prod (wholeStandIn Whole Carried)
open Lk6 (Dat Pub)
open Lk6.PortSim (noClaim sBits sLeaves byVarF joinF)
open Lk6.Mid (Dt Cs RowF pscC eqPairsF cLevels ordFirst ordDown cKey cKeys cHead cParts cJoin
  cTable cClo cZero cBits cntRowF chnC course dtOf)

/-- The same terms on the bits; "mask form - target" has the same value in W. -/
def EvEq (W : PscF.World) (x y : RowF) : Prop :=
  x.maps = y.maps ∧ W.form x.masks - x.target = W.form y.masks - y.target

/-- The same point and value; the mask forms have the same value in W. -/
def KeyEq (W : PscF.World) (x y : PscF.PointClaim) : Prop :=
  x.point = y.point ∧ x.value = y.value ∧ W.form x.masks = W.form y.masks

variable {W : PscF.World} {home : ℕ → Slot}

theorem evEq_rowA {G : Fork} {a : Aff} {r : RowF} (h : RowIs W home G a r) :
    EvEq W (rowA G home a) r := by
  refine ⟨h.1.symm, ?_⟩
  have := h.2.2 G (Later.refl G)
  rw [hidV_eq] at this
  show W.form (PscF.scaleForm (-1) (mfOf G home a)) - -valOf G a = _
  rw [PscF.World.form_scale, ← this]
  ring

theorem keyEq_of {G : Fork} {k : Array E × Aff} {c : PscF.PointClaim} (h : RC W home G k.2 c)
    (hp : c.point = k.1.toList.reverse.map readE) : KeyEq W (keyF G home k) c := by
  have h1 : valOf G k.2 = c.value := (pubV_eq G k.2).symm.trans h.pub
  refine ⟨hp.symm, h1, ?_⟩
  have := h.hid
  rw [hidV_eq, h1] at this
  show W.form (mfOf G home k.2) = _
  linear_combination -this

theorem St.ledger {D : Dt} {F G : Fork} {t : Tape} {s : Cs} {pat : List Bool} {rows : List Aff}
    (h : St W home D F t s pat rows) (l : Later F G) (hn : G.next = F.next) :
    St W home D G t s pat rows :=
  ⟨⟨l.sized h.base.sized, h.base.rounds⟩, by rw [hn]; exact h.al, h.rows.later l⟩

theorem orderOk_down (m : ℕ) : First.Prod.orderOk m (orderDefault m) = true := by
  unfold First.Prod.orderOk orderDefault
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq, List.mem_range,
    List.length_reverse, List.length_range, List.mem_reverse, true_and]
  refine ⟨fun b hb => hb, fun b hb => ?_⟩
  rw [List.count_reverse]
  exact List.count_eq_one_of_mem List.nodup_range (List.mem_range.2 hb)

theorem ordIs_table (D : Dt) (more : ℕ) : ∀ n l, OrdIs D false more orderDefault n l
  | 0, _ => trivial
  | n + 1, l => ⟨rfl, orderOk_down _, ordIs_table D more n (l + 1)⟩

/-- The orders of a part's key tree, from the face's test and from FaceIs. -/
theorem ordIs_keys (D : Dt) (orders : ℕ → List ℕ) (v : ℕ)
    (ho : ∀ m, orders m = if m + 1 = v then ordFirst D.S.order m else ordDown m)
    (hok : ∀ i < v, First.Prod.orderOk i (orders i) = true) :
    ∀ n l, l + n = v → OrdIs D true 0 orders n l
  | 0, _, _ => trivial
  | n + 1, l, h => by
    refine ⟨?_, ?_, ordIs_keys D orders v ho hok n (l + 1) (by omega)⟩
    · rw [Nat.zero_add, ho l]
      by_cases hn : n = 0
      · subst hn
        rw [if_pos (by simp), if_pos (by omega)]
      · rw [if_neg (by simpa using hn), if_neg (by omega)]
    · rw [Nat.zero_add]
      exact hok l (by omega)


theorem snoc_inv {α β : Type} {R : α → β → Prop} {l1 : List α} {l2 : List β} {a : α} {b : β}
    (h : List.Forall₂ R (l1 ++ [a]) (l2 ++ [b])) : List.Forall₂ R l1 l2 ∧ R a b := by
  have := List.rel_reverse h
  rw [List.reverse_append, List.reverse_append] at this
  obtain ⟨h1, h2⟩ := List.forall₂_cons.1 this
  exact ⟨by simpa using List.rel_reverse h2, h1⟩

/-- From the highest variable down, the members of a list: the list turned. -/
theorem down_getD {α : Type} (d : α) : ∀ l : List α,
    (ordDown l.length).map (fun t => l.getD t d) = l.reverse := by
  intro l
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l a ih =>
    rw [List.length_append, List.length_singleton, ordDown_succ, List.map_cons,
      List.reverse_append, List.reverse_singleton, List.singleton_append]
    congr 1
    · simp
    · rw [← ih]
      refine List.map_congr_left fun t ht => ?_
      have : t < l.length := by
        unfold ordDown at ht
        simpa using ht
      rw [List.getD_append _ _ _ _ this]

theorem eqPairs_read (m : ℕ) (z : Array E) (hz : z.size = m) :
    pairsF (eqPairs m z) = eqPairsF (z.toList.reverse.map readE) := by
  unfold pairsF eqPairs eqPairsF
  rw [List.map_map, List.map_map]
  apply List.ext_getElem
  · simp [hz]
  · intro i h1 h2
    have hi : i < m := by simpa using h1
    simp only [List.getElem_map, List.getElem_range, Function.comp]
    have e : z.toList.reverse[i]'(by simpa [hz] using hi) = z.getD (m - 1 - i) zeroE := by
      rw [← List.getD_eq_getElem _ zeroE, rev_getD _ _ _ (by simpa [hz] using hi),
        Array.length_toList, hz, arr_getD]
    rw [e, readE_sub, readE_one]

/-- The face's test gives each part's orders. -/
theorem ok_orders {f : Face} (hok : f.ok = true) (q : ℕ) (hq : q < f.parts.length) :
    ∀ i < f.parts.getD q 0, First.Prod.orderOk i (f.orders q i) = true := by
  unfold Face.ok at hok
  simp only [Bool.and_eq_true] at hok
  have h := hok.2
  rw [List.all_eq_true] at h
  have hm : (f.parts.getD q 0, q) ∈ f.parts.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?]
    simp [List.getD_eq_getElem?_getD, hq]
  have h2 := h _ hm
  unfold First.Prod.runOk at h2
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h2
  intro i hi
  have := h2.2 i hi
  rwa [Nat.zero_add] at this

end VerifiableInference.Desc.K3.KeyLaw

#print axioms VerifiableInference.Desc.K3.KeyLaw.evEq_rowA
#print axioms VerifiableInference.Desc.K3.KeyLaw.keyEq_of
#print axioms VerifiableInference.Desc.K3.KeyLaw.ordIs_keys
#print axioms VerifiableInference.Desc.K3.KeyLaw.eqPairs_read
#print axioms VerifiableInference.Desc.K3.KeyLaw.ok_orders
