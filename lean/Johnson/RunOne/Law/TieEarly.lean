-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/TieEarly.lean: WHAT AN
EARLIER LOOKUP HAS LEFT IN THE RECORD, IN TWO LANGUAGES: the links' rows say of lookup k's rows and
claims on the keys: AllSay, and the pending rows hold (Early: JoinKeyD.lean); the key file's table
says: the items rows k and kclaims k (Johnson/Desc/Key/KeyMeaning.lean). Each gives the other, at
one witness.

Main names:
  rows_of_allSay, allSay_of_rows: the item rows k ⇔ AllSay at the riding part's statement, where the
    record's rows have OffTables (OffWalk.lean).
  kclaims_of_pend, pend_of_kclaims: the item kclaims k ⇔ the pending rows hold.
  rows_agree, kclaims_agree: the two items pass from one pinned witness to another (TieAgree.lean);
    the second where the record's claims on keys name the statement's messages alone (KeysLow).

Object: the links' rows' and the table's sentences on the record.
User: TieClaimL1.lean, TieClaimLayer.lean and TieFrontLayer.lean.
Letters: X · R (its letter same: "read alike") · p₀, i, s: the riding part of a record · u: a
witness.

Limits. Nothing on soundness.

-/
import Johnson.RunOne.Law.OffWalk
import Johnson.RunOne.Law.TieTensor
import Johnson.RunOne.Law.TieAgree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.TieEarly
open OnBytes OnBytes.Params OnBytes.Slice
open OnBytes.Model (Reading)
open VerifiableInference.Desc
open VerifiableInference.Desc.K3.KeyLaw
open VerifiableInference.Desc.Key (Xi FirstState Source KRead valOf matOf mkOf)
open Johnson.RunOne.KeyRows1 (plan₁ meaning₁At)
open Johnson.RunOne.Law.RideKeyD
open Johnson.RunOne.Law.JoinKeyD
open Johnson.RunOne.Law.LinkAtPlan
open Johnson.RunOne.Law.TieStated
open Johnson.RunOne.Law.TieRows
open Johnson.RunOne.Law.TieTensor
open Johnson.RunOne.Law.TieKeys
open Johnson.RunOne.Law.OffWalk
open Johnson.RunOne.Law.TieAgree

variable {Cells Mm : Type} {X : Source} {R : KRead Cells Mm}

/-- The links' sentence on an earlier lookup's rows gives the table's item. -/
theorem rows_of_allSay (hsame : R.same = fun a b => readE a = readE b) (k : ℕ) (p₀ : Xi) (i : ℕ)
    (s : FirstState) (y : Strs) (u : Wit Cells Unit Mm) (ho : RowsOff s) (rows : List Row)
    (h1 : s.base.rows[k]? = some rows) (hne : rows ≠ [])
    (h2 : Means.AllSay Reading.gl (stm (stK p₀ i s)) rows (wdT X R u)) :
    (meaning₁At X.Y.k.oneTime R).rows k (p₀, s) y u := by
  refine ⟨rows, h1, hne, ?_⟩
  rw [hsame]
  exact (allSay_iff s.d.st (valOf (plan₁ X.Y.k.oneTime) R u) rows
    (ho rows (List.mem_of_getElem? h1))).2 ((allSay_same Reading.gl (stm_same p₀ i s) rows _).1 h2)

/-- And back. -/
theorem allSay_of_rows (hsame : R.same = fun a b => readE a = readE b) (k : ℕ) (p₀ : Xi) (i : ℕ)
    (s : FirstState) (y : Strs) (u : Wit Cells Unit Mm) (ho : RowsOff s)
    (h : (meaning₁At X.Y.k.oneTime R).rows k (p₀, s) y u) :
    ∃ rows, s.base.rows[k]? = some rows ∧
      Means.AllSay Reading.gl (stm (stK p₀ i s)) rows (wdT X R u) := by
  obtain ⟨rows, h1, -, h2⟩ := h
  rw [hsame] at h2
  exact ⟨rows, h1, (allSay_same Reading.gl (stm_same p₀ i s) rows _).2
    ((allSay_iff s.d.st (valOf (plan₁ X.Y.k.oneTime) R u) rows
      (ho rows (List.mem_of_getElem? h1))).1 h2)⟩

/-- The links' sentence on an earlier lookup's claims on the keys gives the table's item. -/
theorem kclaims_of_pend (hsame : R.same = fun a b => readE a = readE b) (k : ℕ) (p₀ : Xi)
    (s : FirstState) (y : Strs) (u : Wit Cells Unit Mm) (L : WfLookup)
    (hL : X.Y.k.oneTime.ranges.lookups[k]? = some L) (keys : List Lkp.Keys)
    (h1 : s.base.keys[k]? = some keys) (hlen : L.parts.length ≤ keys.length)
    (h2 : Pend (Wf.matrixOf X.Y.k.oneTime.lin) L keys (wdT X R u)
      (cutM (Wf.matrixOf X.Y.k.oneTime.lin) (mxT X R u))) :
    (meaning₁At X.Y.k.oneTime R).kclaims k (p₀, s) y u := by
  refine ⟨L, (L.parts.zip keys).map fun x => Wf.pendingRow (Wf.matrixOf X.Y.k.oneTime.lin) L x.1 x.2
    (Wf.eqPlaces (Wf.matrixOf X.Y.k.oneTime.lin) x.2.point), hL, ?_, ?_, ?_⟩
  · show (s.base.keys[k]?).bind (Johnson.RunOne.KeyReaders.pendingOf X.Y.k.oneTime k) = _
    rw [h1]
    show Johnson.RunOne.KeyReaders.pendingOf X.Y.k.oneTime k keys = _
    unfold Johnson.RunOne.KeyReaders.pendingOf
    rw [hL]
    rfl
  · rw [List.length_map, List.length_zip, Nat.min_eq_left hlen]
  · intro x hx
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hq
    obtain ⟨e1, e2⟩ := List.getElem?_zip_eq_some.1 hj
    have h3 := h2 j q.1 e1
    have e3 : keys.getD j default = q.2 := by rw [List.getD_eq_getElem?_getD, e2]; rfl
    rw [e3] at h3
    rw [hsame]
    exact (tensorRow_iff_cut _ _ _ _).2 h3

/-- And back. -/
theorem pend_of_kclaims (hsame : R.same = fun a b => readE a = readE b) (k : ℕ) (p₀ : Xi)
    (s : FirstState) (y : Strs) (u : Wit Cells Unit Mm) (L : WfLookup)
    (hL : X.Y.k.oneTime.ranges.lookups[k]? = some L)
    (h : (meaning₁At X.Y.k.oneTime R).kclaims k (p₀, s) y u) :
    ∃ keys, s.base.keys[k]? = some keys ∧ Pend (Wf.matrixOf X.Y.k.oneTime.lin) L keys (wdT X R u)
      (cutM (Wf.matrixOf X.Y.k.oneTime.lin) (mxT X R u)) := by
  obtain ⟨L', ks, a1, a2, a3, a4⟩ := h
  obtain rfl : L' = L := Option.some.inj (a1.symm.trans hL)
  have a2' : (s.base.keys[k]?).bind (Johnson.RunOne.KeyReaders.pendingOf X.Y.k.oneTime k) = some ks
      := a2
  obtain ⟨keys, b1, b2⟩ := Option.bind_eq_some_iff.1 a2'
  unfold Johnson.RunOne.KeyReaders.pendingOf at b2
  rw [hL] at b2
  obtain rfl := Option.some.inj b2
  rw [List.length_map, List.length_zip] at a3
  refine ⟨keys, b1, fun j p hp => ?_⟩
  have hj : j < L'.parts.length := (List.getElem?_eq_some_iff.1 hp).1
  have hjk : j < keys.length := by omega
  have e2 : keys[j]? = some (keys.getD j default) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjk]
    rfl
  have hz : (L'.parts.zip keys)[j]? = some (p, keys.getD j default) :=
    List.getElem?_zip_eq_some.2 ⟨hp, e2⟩
  have h4 := a4 _ (List.mem_map.2 ⟨_, List.mem_of_getElem? hz, rfl⟩)
  rw [hsame] at h4
  exact (tensorRow_iff_cut _ _ _ _).1 h4

/-! ## From one pinned witness to another -/

theorem formAt_congr (mk mk' : Slot → E) : ∀ (f : MaskForm) (a : E),
    (∀ q ∈ f, mk q.1 = mk' q.1) →
    f.foldl (fun s x => addE s (mulE x.2 (mk x.1))) a =
      f.foldl (fun s x => addE s (mulE x.2 (mk' x.1))) a
  | [], _, _ => by simp only [List.foldl_nil]
  | x :: f, a, h => by
    rw [List.foldl_cons, List.foldl_cons, h x List.mem_cons_self]
    exact formAt_congr mk mk' f _ fun q hq => h q (List.mem_cons_of_mem _ hq)

/-- The item rows k at two witnesses that agree. -/
theorem rows_agree {w w' : Wit Cells Unit Mm} (h : Agree R w w') (k : ℕ) (a : Xi × FirstState)
    (h3 : a.2.d.st.oracles.size = 3) (y : Strs) (hx : (meaning₁At X.Y.k.oneTime R).rows k a y w) :
    (meaning₁At X.Y.k.oneTime R).rows k a y w' := by
  obtain ⟨rs, h1, h2, h4⟩ := hx
  exact ⟨rs, h1, h2, fun r hr => (rowHolds_val R.same _ _ _
    (fun o ho => valOf_agree X.Y.k.oneTime h o (by rw [← h3]; exact ho)) r).1 (h4 r hr)⟩

/-- The item kclaims k at two witnesses that agree, where the record's claims on keys name the
statement's messages alone. -/
theorem kclaims_agree {w w' : Wit Cells Unit Mm} (h : Agree R w w') (k : ℕ) (a : Xi × FirstState)
    (h3 : a.2.d.st.oracles.size = 3) (hlow : KeysLow a.2) (y : Strs)
    (hx : (meaning₁At X.Y.k.oneTime R).kclaims k a y w) : (meaning₁At X.Y.k.oneTime R).kclaims k a y
        w' := by
  obtain ⟨L, ks, a1, a2, a3, a4⟩ := hx
  refine ⟨L, ks, a1, a2, a3, fun x hxk => ?_⟩
  have a2' : (a.2.base.keys[k]?).bind (Johnson.RunOne.KeyReaders.pendingOf X.Y.k.oneTime k) = some
      ks := a2
  obtain ⟨keys, b1, b2⟩ := Option.bind_eq_some_iff.1 a2'
  unfold Johnson.RunOne.KeyReaders.pendingOf at b2
  obtain ⟨L', -, b3⟩ := Option.map_eq_some_iff.1 b2
  subst b3
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hxk
  have hc : q.2 ∈ keys := (List.of_mem_zip hq).2
  have h4 := a4 _ hxk
  unfold VerifiableInference.Desc.Key.TensorRowHolds VerifiableInference.Desc.Key.formAt at h4 ⊢
  rw [← matOf_agree X.Y.k.oneTime h, ← formAt_congr (mkOf (plan₁ X.Y.k.oneTime) R w) (mkOf (plan₁
      X.Y.k.oneTime) R w') _ _
    fun z hz => by
      show valOf (plan₁ X.Y.k.oneTime) R w z.1.oracle .mask z.1.index =
        valOf (plan₁ X.Y.k.oneTime) R w' z.1.oracle .mask z.1.index
      rw [valOf_agree X.Y.k.oneTime h z.1.oracle (by
        rw [← h3]
        exact hlow keys (List.mem_of_getElem? b1) q.2 hc z hz)]]
  exact h4

end Johnson.RunOne.Law.TieEarly

#print axioms Johnson.RunOne.Law.TieEarly.rows_of_allSay
#print axioms Johnson.RunOne.Law.TieEarly.allSay_of_rows
#print axioms Johnson.RunOne.Law.TieEarly.kclaims_of_pend
#print axioms Johnson.RunOne.Law.TieEarly.pend_of_kclaims
#print axioms Johnson.RunOne.Law.TieEarly.rows_agree
#print axioms Johnson.RunOne.Law.TieEarly.kclaims_agree
