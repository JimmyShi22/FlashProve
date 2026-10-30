-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/KeyLaw/KeyClaim.lean: THE CLAIMS ON THE PARTS' KEYS: each part's typed claim
on its keys holds of the entries exactly if the pending row on the matrix holds that the verifier
program's own routines (Lkp.keysOf, Wf.pendingRow) make of the claim which the kind's routine
keyClaims (K3Key.lean) makes of what was heard.

Main names:
  lowPt_ptTop: a point by variable, laid with the top bit first and read back.
  key_claim_iff: one part: the typed claim read off a claim on the leaves, and the pending row.
  mapM_getD: what mapM returns, member by member.
  KeysAre: the typed lookup's keys are the keys that the matrix holds (Leaves.key), part by part.
  keys_iff_rec: ALL PARTS, at what a record holds: a ledger, a table of homes, a hearing.

Limits. The matrix M is a letter, and so is the world W of mask entries; that the entries are read
off W at the homes, KeysAre, and the number and sizes of the hearing's points are premises.

-/
import Johnson.Desc.First.Look.KeyLaw.SaysAt
import OnBytes.Tie.Pv.KeyLookup.KeysBridgePort
import OnBytes.Tie.Pv.KeyLookup.PubOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3.KeyLaw
open OnBytes OnBytes.Slice
open OnBytes.Model (Fork Aff)
open OnBytes.Params (WfLookup WfPart)
open Lk6 (Dat pubOf)
open Lk6.PortSim (rdMF)
open Lk6.Mid (rdCl)

/-- A point by variable, laid with the top bit first and read back. -/
theorem lowPt_ptTop (v : ℕ) (l : List GE) (h : l.length = v) :
    Lk6.lowPt v (Lk6.Lev.ptTop v l) = l := by
  unfold Lk6.lowPt Lk6.Lev.ptTop
  apply List.ext_getElem
  · simp [h]
  · intro n h1 h2
    have hn : n < v := by simpa using h1
    simp only [List.getElem_map, List.getElem_range]
    rw [if_pos (by omega), show v - 1 - (v - 1 - n) = n by omega, List.getD_eq_getElem _ _ h2]

/-- **One part.** -/
theorem key_claim_iff {A : Dat GE} {sl : Slot → A.J} {μ : A.J → GE} (W : PscF.World)
    (m : Wf.Matrix) (l : WfLookup) (id i : ℕ) (p : WfPart) (θ α : E) (M : ℕ → ℕ → GE)
    (c : PointClaim) (hl : Wf.lookupOk Wf.fBits l = true) (hm : Wf.fitsMatrix m l = true)
    (hp : l.parts[i]? = some p) (hz : c.point.length = m.kCol + p.logPlaces)
    (hW : ∀ q ∈ c.masks, μ (sl q.1) = W.mask q.1) :
    (rdCl A sl (readE α) (m.kCol + p.logPlaces) (readPC c)).Holds (m.kCol + p.logPlaces)
        (Leaves.key (Leaves.lkOf l (Leaves.padOf id m l θ)) M m.kCol p.runs) μ ↔
      (Leaves.readTRow (Wf.pendingRow m l p (Lkp.keysOf (Wf.lookupOf id m l) θ α i c)
        (Wf.eqPlaces m c.point))).Holds W M m.rows m.kCol := by
  refine Lk6.claim_iff_pending m l id i p θ α W M c _ μ hl hm hp ?_ rfl ?_
  · exact lowPt_ptTop _ _ (by rw [← hz]; exact List.length_map _)
  · show ∑ j, (- rdMF sl (readForm c.masks) j) * μ j = _
    simp only [neg_mul, Finset.sum_neg_distrib]
    rw [sum_rdMF A sl μ]
    congr 1
    unfold PscF.World.form readForm
    rw [List.map_map, List.map_map]
    refine congrArg List.sum (List.map_congr_left fun q hq => ?_)
    show readE q.2 * μ (sl q.1) = readE q.2 * W.mask q.1
    rw [hW q hq]

/-- What mapM returns, member by member. -/
theorem mapM_getD {α β : Type} (f : α → Option β) : ∀ (l : List α) (r : List β), l.mapM f = some r →
    r.length = l.length ∧ ∀ (i : ℕ) (h : i < l.length) (d : β), f l[i] = some (r.getD i d)
  | [], r, h => by
    cases h
    exact ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | a :: l, r, h => by
    rw [List.mapM_cons] at h
    cases ha : f a with
    | none => rw [ha] at h; cases h
    | some b =>
      cases hl : l.mapM f with
      | none => rw [ha, hl] at h; cases h
      | some bs =>
        rw [ha, hl] at h
        cases h
        obtain ⟨r1, r2⟩ := mapM_getD f l bs hl
        refine ⟨by simp [r1], fun i hi d => ?_⟩
        cases i with
        | zero => exact ha
        | succ i => exact r2 i (by simpa using hi) d

/-- The typed lookup's keys are the keys that the matrix holds, part by part. -/
def KeysAre (A : Dat GE) (st : A.St) (μ : A.J → GE) (id : ℕ) (m : Wf.Matrix) (l : WfLookup)
    (M : ℕ → ℕ → GE) : Prop :=
  ∀ (i : ℕ) (p : WfPart), l.parts[i]? = some p →
    A.key st μ i = Leaves.key (Leaves.lkOf l (Leaves.padOf id m l zeroE)) M m.kCol p.runs

/-- **All parts, at what a record holds.** -/
theorem keys_iff_rec {K : Fork} {homeA : Array Slot} {home : ℕ → Slot} (hA : HomeArr homeA home)
    {g : HeardG} {keys : List Lkp.Keys} (id : ℕ) (m : Wf.Matrix) (l : WfLookup)
    (h5 : keyClaims (Wf.lookupOf id m l) K homeA g = some keys) (hth : g.theta = zeroE)
    (k1 : g.keys.length = l.parts.length)
    (k2 : ∀ q < l.parts.length, (g.keys.getD q (#[], {})).1.size =
      (l.parts.map fun p => p.logPlaces + m.kCol).getD q 0)
    (A : Dat GE) (sl : Slot → A.J) (st : A.St) (hP : A.toPub = pubOf (Wf.lookupOf id m l))
    (hlo : Wf.lookupOk Wf.fBits l = true) (hfm : Wf.fitsMatrix m l = true)
    (μ : A.J → GE) (W : PscF.World) (M : ℕ → ℕ → GE)
    (hW : ∀ s ∈ homeA.toList, μ (sl s) = W.mask s) (hK : KeysAre A st μ id m l M) :
    keys.length = l.parts.length ∧
      ((∀ j : Fin A.m, (rdCl A sl (readE g.alpha) (A.v j)
          (keyF K home (g.keys.getD j (#[], {})))).Holds (A.v j) (A.key st μ j) μ) ↔
        ∀ (j : ℕ) (p : WfPart), l.parts[j]? = some p →
          (Leaves.readTRow (Wf.pendingRow m l p (keys.getD j default)
            (Wf.eqPlaces m (keys.getD j default).point))).Holds W M m.rows m.kCol) := by
  unfold keyClaims at h5
  obtain ⟨q1, q2⟩ := mapM_getD _ _ keys h5
  have hlen : keys.length = l.parts.length := by rw [q1, List.length_zipIdx, k1]
  have hm' : A.m = l.parts.length := by
    show A.toPub.parts.length = _
    rw [hP]
    exact List.length_map _
  have one : ∀ (j : ℕ) (p : WfPart), l.parts[j]? = some p →
      ((rdCl A sl (readE g.alpha) (A.v j) (keyF K home (g.keys.getD j (#[], {})))).Holds (A.v j)
          (A.key st μ j) μ ↔
        (Leaves.readTRow (Wf.pendingRow m l p (keys.getD j default)
          (Wf.eqPlaces m (keys.getD j default).point))).Holds W M m.rows m.kCol) := by
    intro j p hp
    have hj : j < l.parts.length := (List.getElem?_eq_some_iff.1 hp).1
    have hjk : j < g.keys.zipIdx.length := by
      rw [List.length_zipIdx, k1]
      exact hj
    have hq := q2 j hjk default
    have hz : g.keys.zipIdx[j] = (g.keys.getD j (#[], {}), j) := by
      rw [List.getElem_zipIdx, Nat.zero_add, List.getD_eq_getElem]
    rw [hz] at hq
    cases hy : maskSide K homeA (g.keys.getD j (#[], {})).2 with
    | none =>
      simp only [hy, Option.map_none] at hq
      cases hq
    | some y =>
      simp only [hy, Option.map_some] at hq
      have hkey := Option.some.inj hq
      have hv : A.v j = m.kCol + p.logPlaces := by
        show A.toPub.parts.getD j 0 = _
        rw [hP]
        show (l.parts.map fun p => p.logPlaces + m.kCol).getD j 0 = _
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, hp]
        exact Nat.add_comm _ _
      have hsize : (g.keys.getD j (#[], {})).1.toList.reverse.length = m.kCol + p.logPlaces := by
        rw [List.length_reverse, Array.length_toList, k2 j hj, List.getD_eq_getElem?_getD,
          List.getElem?_map, hp]
        exact Nat.add_comm _ _
      rw [← hkey, hv, hK j p hp, ← keyF_reads hA hy, hth]
      exact key_claim_iff W m l id j p zeroE g.alpha M
        ⟨(g.keys.getD j (#[], {})).1.toList.reverse, y.1, y.2⟩ hlo hfm hp hsize
        fun q hq' => hW q.1 (maskSide_slots hy q hq')
  refine ⟨hlen, ?_, ?_⟩
  · intro hall j p hp
    have hj : j < A.m := by
      rw [hm']
      exact (List.getElem?_eq_some_iff.1 hp).1
    exact (one j p hp).1 (hall ⟨j, hj⟩)
  · intro hall j
    have hj : j.val < l.parts.length := by
      rw [← hm']
      exact j.isLt
    exact (one j.val l.parts[j.val] (List.getElem?_eq_getElem hj)).2
      (hall j.val _ (List.getElem?_eq_getElem hj))

end VerifiableInference.Desc.K3.KeyLaw

#print axioms VerifiableInference.Desc.K3.KeyLaw.key_claim_iff
#print axioms VerifiableInference.Desc.K3.KeyLaw.keys_iff_rec
