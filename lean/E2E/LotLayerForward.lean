-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LotLayerForward.lean: THE LAYER OF ROWS OF A KEY FILE's LOOKUP, READ FORWARD: the table's three sentences in front of the layer
(forms l "objects", worth l "planes", worth l "keys": Johnson/Desc/Key/KeyK3Items.lean) and the layer's own yes give the
table's two sentences behind it (rows l, kclaims l: Johnson/Desc/Key/KeyMeaning.lean), AT ONE AND THE SAME WITNESS, whatever it
is. The forward twin of the library's LayerTie, which is stated backward and proved nowhere.

  out_paid        what is read of a ledger as the typed lookup's out does not see which debts are marked
  rows_some       the layer's rows are not none
  layer_forward   THE LAW

By what: calls alone. The library went round LayerTie through the typed lookup, by laws that go both ways; here their forward
halves are spent: done_of_sentences (Johnson/RunOne/Law/TieDone.lean: the three sentences give A.Done) · closed_of_paid
(PlanesPaid.lean: the layer's ledger is the sentences' closed ledger with debts marked) · doneD_iff (AtKeyD.lean: A.Done ⟺ the
rows say their claims and the pending rows hold) · allSay_iff, off_rowsInOrder, kclaims_of_pend (TieRows.lean, OffWalk.lean,
TieEarly.lean) · at the typed lookup without a letter (datK, tiedK, keysAreK: Johnson/Desc/First/Look/KeyLaw/Closed.lean).

The premises. hsame: two machine elements are the same where they read alike. hW, hid, hla: public tests on the plan. hInv, hH:
the record's half in front of the layer (Inv, HeardOk: Johnson/RunOne/Law/SeatsKeyD.lean, KeyLaw/SeatK3.lean). hd: the layer's
yes. f1, f2, f3: the three sentences.

Limits. It moves truth from three sentences to two: that the three hold of anything is not shown. No round, no challenge, no
prover. Nothing on soundness, completeness, hiding or binding.
-/
import Johnson.RunOne.Law.TieFrontLayer
import Johnson.RunOne.Law.TieEarly
import Johnson.RunOne.Law.TiePlanes

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.FirstH.Lots
open OnBytes OnBytes.Params OnBytes.Slice
open OnBytes.Model (Fork Reading)
open VerifiableInference.Desc
open VerifiableInference.Desc.K3 VerifiableInference.Desc.K3.KeyLaw
open VerifiableInference.Desc.Key (Xi FirstState Claim Source KRead closedAt mkOf matOf valOf
  lookupSeat lookupPlace layer rowsInOrder layerOrder rowOfClaim)
open Johnson.RunOne.KeyRows1 (plan₁ meaning₁At)
open Johnson.RunOne.Law.AtKeyD
open Johnson.RunOne.Law.SeatsKeyD
open Johnson.RunOne.Law.JoinKeyD
open Johnson.RunOne.Law.LinkAtPlan
open Johnson.RunOne.Law.LinkAtFK (look_at)
open Johnson.RunOne.Law.TieStated
open Johnson.RunOne.Law.TieRows
open Johnson.RunOne.Law.TieKeys
open Johnson.RunOne.Law.TieEarly
open Johnson.RunOne.Law.TieDone
open Johnson.RunOne.Law.OffWalk
open Johnson.RunOne.Law.PlanesPaid
open Lk6 (Dat pubOf)

/-- The out does not see which debts are marked. -/
theorem out_paid (A : Dat GE) (sl : Slot → A.J) (st : A.St) (G : Fork) (home : ℕ → Slot)
    (g : HeardG) (pl : List PlaneClaim) (a : ℕ) :
    outOf A sl st (G.paid a) home g pl = outOf A sl st G home g pl := rfl

/-- The layer's rows are not none. -/
theorem rows_some {planesAt : Row → Tensor → Row} {tab : List (Bool × ℕ × Bool)} {F : Fork}
    {home : Array Slot} {cls : List Claim} {rows : List Row}
    (h : rowsInOrder planesAt tab F home cls = some rows) : rows ≠ [] := by
  unfold rowsInOrder at h
  simp only at h
  split at h
  · cases h
  · rename_i hc
    rintro rfl
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, not_not] at hc
    cases tab with
    | nil =>
      have h0 : cls.length = 0 := hc.2.symm
      have e : cls = [] := List.length_eq_zero_iff.1 h0
      rw [e] at hc
      exact absurd hc.1 (by decide)
    | cons t tab =>
      rw [List.mapM_cons] at h
      obtain ⟨a, -, h⟩ := Option.bind_eq_some_iff.1 (show Option.bind _ _ = some [] from h)
      obtain ⟨l, -, h⟩ := Option.bind_eq_some_iff.1 (show Option.bind _ _ = some [] from h)
      cases h

section
variable {Cells Mm : Type} {X : Source} {R : KRead Cells Mm}

set_option maxHeartbeats 1600000 in
/-- **THE LAYER, READ FORWARD.** -/
theorem layer_forward (hsame : R.same = fun a b => readE a = readE b)
    (hW : Wf.admitted X.Y.k.oneTime.codes X.Y.k.oneTime.ranges (Wf.matrixOf X.Y.k.oneTime.lin) =
      true)
    (hid : X.Y.k.oneTime.ranges.messageId = 1)
    (hla : ((Wf.layout X.Y.k.oneTime.ranges.lookups
      (Planes.codeOf X.Y.k.oneTime.ranges X.Y.k.oneTime.codes).ell).head?.any
      fun b => decide (2 ^ b.bits ≤ (Planes.codeOf X.Y.k.oneTime.ranges X.Y.k.oneTime.codes).ell)) =
        true)
    {i : ℕ} (hi : i < X.Y.k.oneTime.ranges.lookups.length) {oL kL : List ℕ} {idxN : ℕ}
    {set : Setting} {b0 : Block FirstState Claim} {before : List (ℕ × ℕ)} {bits : ℕ}
    {s s' : FirstState} {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))}
    (hInv : Inv X.Y.k.oneTime i X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin)
      (Lof X.Y.k.oneTime i) oL kL idxN s)
    (hH : HeardOk lookupSeat (lookupPlace set i (Wf.lookupOf X.Y.k.oneTime.ranges.messageId
      (Wf.matrixOf X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime i))) s)
    (hd : (layer X.Y.k.oneTime set i (Wf.lookupOf X.Y.k.oneTime.ranges.messageId
        (Wf.matrixOf X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime i))
      (claimsIn [b0, lookupKind lookupSeat before bits [] (lookupPlace set i
              (Wf.lookupOf X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin)
                (Lof X.Y.k.oneTime i)))]
        [(1, "objects"), (1, "planes"), (1, "guests")])).decide s rs gs = .ok s')
    (p₀ : Xi) (y y' : Strs) (v : Wit Cells Unit Mm)
    (f1 : (meaning₁At X.Y.k.oneTime R).forms i "objects" (p₀, s) y v)
    (f2 : (meaning₁At X.Y.k.oneTime R).worth i "planes" (p₀, s) y v)
    (f3 : (meaning₁At X.Y.k.oneTime R).worth i "keys" (p₀, s) y v) :
    (meaning₁At X.Y.k.oneTime R).rows i (p₀, s') y' v ∧
      (meaning₁At X.Y.k.oneTime R).kclaims i (p₀, s') y' v := by
  have t0 := tests_at hW hi
  have hadm := Lk6.adm_of_tests X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) _
    t0.2.1 t0.2.2
  obtain ⟨hhome, hfit, hrl, hkl, -⟩ := hInv
  obtain ⟨G, g, hG, hg, -, -, hth, k1, k2⟩ := hH
  have hG : s.base.fork = some G := hG
  have hg : s.base.heard = some g := hg
  obtain ⟨cls, t, F, g', rows, keys, c1, c2, c3, c4, c5, rfl⟩ := layerD_law hd
  obtain ⟨pl, H', u, p1, rfl, rfl⟩ := claimsD_law hG hg c1
  obtain rfl : H'.paid g.owedPlanes = F := Option.some.inj c2
  obtain rfl : g = g' := Option.some.inj (hg.symm.trans c3)
  obtain ⟨G', hc, rfl⟩ := closed_of_paid p1
  -- the three sentences, at the record's own terms
  obtain ⟨-, Sg1, g1, G1, a1, a2, a3, fo⟩ := f1
  obtain ⟨Sg2, L2, g2, G2, b1, b2, b3, b4, wp⟩ := f2
  obtain ⟨Sg3, L3, g3, G3, d1, d2, d3, d4, wk⟩ := f3
  have e0 : VerifiableInference.Desc.Key.lkpOf (plan₁ X.Y.k.oneTime) X.Y.k.oneTime.ranges i = some
      (Wf.lookupOf X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin)
        (Lof X.Y.k.oneTime i)) := look_at X.Y.k.oneTime i hi
  obtain rfl := Option.some.inj (a1.symm.trans e0)
  obtain rfl := Option.some.inj (b1.symm.trans e0)
  obtain rfl := Option.some.inj (d1.symm.trans e0)
  obtain rfl := Option.some.inj (b2.symm.trans t0.1)
  obtain rfl := Option.some.inj (d2.symm.trans t0.1)
  have eg1 : g1 = g := Option.some.inj (a2.symm.trans hg)
  have eg2 : g2 = g := Option.some.inj (b3.symm.trans hg)
  have eg3 : g3 = g := Option.some.inj (d3.symm.trans hg)
  have eG1 : G1 = G := Option.some.inj (a3.symm.trans hG)
  have eG2 : G2 = G := Option.some.inj (b4.symm.trans hG)
  have eG3 : G3 = G := Option.some.inj (d4.symm.trans hG)
  have wp' := (wp.resolve_right fun h => absurd h.1 (by decide)).2
  have wk' := (wk.resolve_left fun h => absurd h.1 (by decide)).2
  rw [hsame, eg1, eG1] at fo
  rw [hsame, eg2, eG2] at wp'
  rw [hsame, eg3, eG3] at wk'
  have hK : KeysAre (datK Unit X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin)
      (Lof X.Y.k.oneTime i) s.base.home.toList) ()
      (msgK Unit X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin)
        (Lof X.Y.k.oneTime i) s.base.home.toList X.Y.k.oneTime.ranges X.Y.k.oneTime.codes i
        (wdT X R v) (mxT X R v))
      X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime i)
      (cutM (Wf.matrixOf X.Y.k.oneTime.lin) (mxT X R v)) := by
    have hk := keysAreK (T := Unit) (id := X.Y.k.oneTime.ranges.messageId)
      (m := Wf.matrixOf X.Y.k.oneTime.lin) (l := Lof X.Y.k.oneTime i) (hs := s.base.home.toList) ()
      (msgK Unit X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin)
        (Lof X.Y.k.oneTime i) s.base.home.toList X.Y.k.oneTime.ranges X.Y.k.oneTime.codes i
        (wdT X R v) (mxT X R v))
    rw [matOf_cut] at hk
    exact hk
  have k2' : ∀ q < (Lof X.Y.k.oneTime i).parts.length, (g.keys.getD q (#[], {})).1.size =
      ((Lof X.Y.k.oneTime i).parts.map fun p =>
        p.logPlaces + (Wf.matrixOf X.Y.k.oneTime.lin).kCol).getD q 0 := fun q hq =>
    k2 q (lt_of_lt_of_eq hq (List.length_map _).symm)
  obtain ⟨cl, G'', hc', hDone⟩ := done_of_sentences
    (A := datK Unit X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin)
      (Lof X.Y.k.oneTime i) s.base.home.toList)
    (sl := slK Unit X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin)
      (Lof X.Y.k.oneTime i) s.base.home.toList)
    (μ := msgK Unit X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin)
      (Lof X.Y.k.oneTime i) s.base.home.toList X.Y.k.oneTime.ranges X.Y.k.oneTime.codes i
      (wdT X R v) (mxT X R v))
    (w := wdT X R v) (x := X.Y.k.oneTime.ranges) (codes := X.Y.k.oneTime.codes) (i := i)
    (homeA := s.base.home) hadm (tiedK _ _ _ _ _ _ _ _ _ _) (Lof X.Y.k.oneTime i) t0.1
    (mkOf (plan₁ X.Y.k.oneTime) R v) (fun _ _ => rfl) () X.Y.k.oneTime.ranges.messageId
    (Wf.matrixOf X.Y.k.oneTime.lin) (matOf (plan₁ X.Y.k.oneTime) R v) rfl t0.2.1 t0.2.2 hK
    (VerifiableInference.Desc.Key.bitVec X.Y.k.oneTime.ranges X.Y.k.oneTime.codes i
      fun j => R.val (R.of v 1) .main j)
    (fun n _ => by
      have e := Johnson.RunOne.Law.TiePlanes.read_bitVecL X.Y.k.oneTime.ranges X.Y.k.oneTime.codes
        i (fun j => R.val (R.of v 1) .main j) n
      rw [hid]
      exact e)
    g G k2' fo wp' wk'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hc'.symm.trans hc))
  rw [filterL, List.length_map] at c4
  have hd' := doneD_iff X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin)
    (Lof X.Y.k.oneTime i) c4 c5 (planesG_three p1) (planesG_pairs p1) hth
    (by rw [k1]; exact List.length_map _) k2'
    (datK Unit X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin)
      (Lof X.Y.k.oneTime i) s.base.home.toList)
    (slK Unit X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin)
      (Lof X.Y.k.oneTime i) s.base.home.toList) () rfl hadm t0.2.1 t0.2.2
    (msgK Unit X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin)
      (Lof X.Y.k.oneTime i) s.base.home.toList X.Y.k.oneTime.ranges X.Y.k.oneTime.codes i
      (wdT X R v) (mxT X R v))
    (wdT X R v) s.d.st (cutM (Wf.matrixOf X.Y.k.oneTime.lin) (mxT X R v))
    (tiedK _ _ _ _ _ _ _ _ _ _) hfit.1 (by rw [hhome]; exact hfit.2) t0.1 hla hK
  obtain ⟨hAll, hPend⟩ := hd'.2.1 hDone
  refine ⟨⟨rows, ?_, rows_some c4, ?_⟩, ?_⟩
  · show (s.base.rows ++ [rows])[i]? = some rows
    rw [← hrl, List.getElem?_concat_length]
  · rw [hsame]
    refine (allSay_iff s.d.st (valOf (plan₁ X.Y.k.oneTime) R v) rows ?_).2 hAll
    refine off_rowsInOrder (St := s.d.st) (fun z hz => ((by rw [hhome]; exact hfit.2 :
      ∀ z ∈ s.base.home.toList, z.oracle < s.d.st.oracles.size ∧
        z.index < Means.tableSize s.d.st z.oracle .mask) z hz).2) X.Y.k.oneTime.ranges
      X.Y.k.oneTime.codes i ?_ _ _ rows c4
    refine has_of_lt (i := 0) ?_
    rw [hfit.1.size]
    exact Nat.pow_pos (by omega)
  · refine kclaims_of_pend hsame i p₀ _ y' v (Lof X.Y.k.oneTime i) t0.1 keys ?_
      (Nat.le_of_eq hd'.1.symm) hPend
    show (s.base.keys ++ [keys])[i]? = some keys
    rw [← hkl, List.getElem?_concat_length]

end

end AtPublicFiles.FirstH.Lots

#print axioms AtPublicFiles.FirstH.Lots.out_paid
#print axioms AtPublicFiles.FirstH.Lots.rows_some
#print axioms AtPublicFiles.FirstH.Lots.layer_forward
