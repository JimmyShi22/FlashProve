-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Ends/HeadBack.lean: the bridge at the output head read backwards: from the library's
clause "every key of the nine families is an entry of its table" to "the keys of every call of the
head's lookup lie in the call's table", at the calls callsH (Johnson/Road/Ends/HeadInSeam.lean).

Main theorems:
  recAt_of_layout: in a layout that the verifier's function returns, every call has a record in the
    lookup's shape, with the library's table for the call's kind.
  row_of_inLut, t0_cast: an entry of the library's table is a row of the record, cast; so is the
    padding key.
  colH_some, kvH_none, kvH_some: what colH has found, and what kvH is in either case.
  inTables_of_headKeys: under the premises of headBridge_of_layout: HeadKeys gives
    (callsH …).InTables.
  headKeys_iff_inTables, headKeys_iff_forIn: so the two are equivalent, and so are HeadKeys and the
    clause ForInH (Johnson/Road/Ends/HeadForIn.lean).
  headOrd_iff_forIn: the head is in order (Hd.HeadOrdLB, Johnson/Road/HeadL5BL.lean) if and only if
    its meaning without the clause on keys holds (HeadR0, Johnson/Road/Lane5SplitH.lean) and the
    clause ForInH holds.
How, column by column: a column that no segment lists holds the padding key, which is a row
(pad_inLut, Johnson/Road/HeadSumMet.lean); in a listed column stands an entry of a family below the
family's length (SegsFit), whose key is the library's (key_segH), at HD0 divided by 2^23.

Limits: equivalences between statements on integer matrices, and no more. That either side holds is
not shown here. HeadR0 reads no weight: the product with the output matrix stands in the clause
ForInH (the head of Johnson/Road/Ends/HeadInSeam.lean, "What the bridge holds"). How a field element
is lifted to an integer is not said. Mh and Wz are letters. K is kvH, a term of this library: that
the vector whose extension the verifier's key forms evaluate is kvH is not shown in these files.
What ReqFits reads at the last position: the head of Johnson/Road/Ends/HeadInSeam.lean. The
reference sizes. Nothing on a form or a protocol. The other limits of
Johnson/Road/Ends/HeadInSeam.lean hold here too.

-/
import Johnson.Road.HeadSumMet
import Johnson.Road.Ends.HeadForIn

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd

open OnBytes.Ends
open OnBytes.Model (Seg Call WsLay WsShape wsLayOf)
open OnBytes.Model.Layer (Lay)
open OnBytes.Model.Head (Border)
open OnBytes.Model.Verify (borderOf)
open Inst.Model (NormPar Mat ppref AcceptancePolicy Instance Lut)
open Inst.Model.Head (InLut nT)
open Inst.Model.Layout (kRef)

/-- The two lists of the nine names agree. -/
theorem nameH_nameOf (s : Inst.Model.Head.Fam) : nameH s = nameOf s := by cases s <;> rfl

/-- Every call has a record in the lookup's shape, with the library's table for its kind. -/
theorem recAt_of_layout {R : Model.Head.Run} (hy : Model.Head.layout R.h tauFCw = .ok R.L)
    (hF : R.h.famF = 24) (hs : R.h.digSh = 8) (hT : R.h.tabS = 4) {q : ℕ}
    (hq : q < R.L.calls.size) :
    ∃ c0 : Call, R.L.fs.calls[q]? = some c0 ∧ IsLut c0 (tabL R q) ∧ kN R.L.fs q = c0.k := by
  have hq' : q < R.L.cl.size := by
    rw [(clN_of_layout hy).1]
    exact hq
  have e1 : R.L.cl[q]? = some (R.L.cl.getD q default) := by simp [Array.getD, hq']
  obtain ⟨cd, hcd, _, hl⟩ := isLut_of_layout hy hF hs hT e1
  have e2 : R.L.calls.getD q default = cd := by
    have e3 : R.L.calls[q]? = some (R.L.calls.getD q default) := by simp [Array.getD, hq]
    rw [e3] at hcd
    exact Option.some.inj hcd
  have e4 : R.L.fs.calls[q]? = some (R.L.cl.getD q default) := by
    rw [fsCalls_of_layout hy]
    exact e1
  refine ⟨R.L.cl.getD q default, e4, ?_, ?_⟩
  · unfold tabL
    rw [e2]
    exact hl
  · unfold kN
    rw [e4]
    rfl

/-- An entry of the library's table is a row of the record, cast. -/
theorem row_of_inLut {fs : Model.Forest.Shape} {q : ℕ} {c0 : Call} {T : Lut}
    (hc0 : fs.calls[q]? = some c0) (hl : IsLut c0 T) {v : Cb.Gl.E} (hv : InLut T v) :
    ∃ u < 2 ^ c0.k, v = ((tauN fs q u : ℕ) : Cb.Gl.E) := by
  obtain ⟨u, hu, rfl⟩ := hv
  obtain ⟨m, hm1, hm2⟩ := hl.row u hu
  refine ⟨u, by rw [hl.rows]; exact hu, ?_⟩
  have ht : tauN fs q u = (c0.tauAt u).toNat := by
    unfold tauN
    rw [hc0]
    rfl
  rw [ht, hm1, word_castH, ← hm2, Int.cast_natCast]

/-- The padding key of the record, cast, is the library's. -/
theorem t0_cast {fs : Model.Forest.Shape} {q : ℕ} {c0 : Call} {T : Lut}
    (hc0 : fs.calls[q]? = some c0) (hl : IsLut c0 T) :
    ((tauN fs q (t0N fs q) : ℕ) : Cb.Gl.E) = ((T.pad : ℤ) : Cb.Gl.E) := by
  obtain ⟨m, hm1, hm2⟩ := hl.pad
  have e : tauN fs q (t0N fs q) = (c0.tauAt c0.t0).toNat := by
    unfold tauN t0N
    rw [hc0]
    rfl
  rw [e, hm1, word_castH, ← hm2, Int.cast_natCast]

/-- What colH has found is an entry of a segment of the call. -/
theorem colH_some {L : Model.Head.HL} {q j a : ℕ} {sn : String}
    (h : H.colH L q j = some (sn, a)) :
    ∃ g ∈ (L.calls.getD q default).segs, g.name = sn ∧ a < g.pos.size := by
  unfold H.colH at h
  obtain ⟨g0, hg0, h0⟩ := List.exists_of_findSome?_eq_some h
  cases hx0 : g0.pos.findIdx? (· == j) with
  | none =>
    rw [hx0] at h0
    cases h0
  | some x0 =>
    rw [hx0] at h0
    have e : (g0.name, x0) = (sn, a) := Option.some.inj h0
    obtain ⟨hi, _, _⟩ := Array.findIdx?_eq_some_iff_getElem.1 hx0
    obtain ⟨e1, e2⟩ := Prod.mk.inj e
    exact ⟨g0, hg0, e1, e2 ▸ hi⟩

section Kv

variable {K : Type} [Field K]

/-- In a column that no segment lists kvH is the padding key. -/
theorem kvH_none (P : H.PubH) (cell : H.NameH → K) {q X : ℕ}
    (hc : H.colH P.L q (X / P.h.T) = none) :
    H.kvH P cell q X = ((tauN P.L.fs q (t0N P.L.fs q) : ℕ) : K) := by
  unfold H.kvH H.kvOf
  rw [hc]

/-- In a listed column kvH is the key of the entry that stands there. -/
theorem kvH_some (P : H.PubH) (cell : H.NameH → K) {q X a : ℕ} {sn : String}
    (hc : H.colH P.L q (X / P.h.T) = some (sn, a)) :
    H.kvH P cell q X = H.segH P cell sn a (X % P.h.T) := by
  unfold H.kvH H.kvOf
  rw [hc]

end Kv

section Back

variable {R : Model.Head.Run} (hy : Model.Head.layout R.h tauFCw = .ok R.L) (hFu : FullH R.h)
  (hF : R.h.famF = 24) (hT : R.h.tabS = 4) (hs : R.h.digSh = 8) {np : NormPar}
  (hKF : R.h.KF = np.K) {y : Lay} (hnl : (borderOf y).nl = 5) {s : WsShape}
  (Z : SizedW s ppref) {lay : WsLay} (hlay : wsLayOf s true kRef = .ok lay) {pol : AcceptancePolicy}
  {x : Instance ppref} (Rq : ReqFits R HeadSizes.ref (Inst.Model.Head.Req.of pol x)) (Wz : Mat)
  (Mh : Mats ℤ)

include hy hFu hF hT hs hKF hnl Z hlay Rq

/-- **From the library's clause on the head's keys to the calls' tables.** -/
theorem inTables_of_headKeys (HK : L5.HeadKeys R.h R.L y np pol Wz x Mh) :
    (callsH R (borderOf y) lay Mh Wz).InTables := by
  intro q hq X _
  have hq0 : q < R.L.calls.size := hq
  obtain ⟨c0, hc0, hl, hk⟩ := recAt_of_layout hy hF hs hT hq0
  have hTT : R.h.T = nT := by
    unfold Model.Head.Shape.T
    rw [hFu.lt]
    rfl
  have Ti := tiesH_of (np := np) (laid_ref hy hFu.lt hFu.d hFu.V rfl rfl) Rq hFu.XL hKF hs hnl
    (Inst.Model.Head.Req.of_ok pol x)
    (fun k v hk hv => wH_read Z hlay R (borderOf y) Mh Wz hk hv)
  show ∃ u < 2 ^ kN R.L.fs q, H.kvH (pubH R (borderOf y) lay) (readH Mh Wz) q X =
    ((tauN R.L.fs q u : ℕ) : Cb.Gl.E)
  rw [hk]
  cases hc : H.colH R.L q (X / R.h.T) with
  | none =>
    rw [kvH_none (pubH R (borderOf y) lay) (readH Mh Wz) hc]
    show ∃ u < 2 ^ c0.k, ((tauN R.L.fs q (t0N R.L.fs q) : ℕ) : Cb.Gl.E) = _
    rw [t0_cast hc0 hl]
    exact row_of_inLut hc0 hl (pad_inLut _)
  | some p =>
    obtain ⟨sn, a⟩ := p
    obtain ⟨g, hg, hname, ha⟩ := colH_some hc
    obtain ⟨f, e1, e2, e3⟩ := segsFit_of_layout hy hFu.lt hFu.d hFu.V hFu.XL q g hg
    have ha' : a < Inst.Model.Head.len f := by
      refine Nat.lt_of_lt_of_le ?_ e2
      rw [← sizes_of_layout hy q g hg]
      exact ha
    have hi : X % R.h.T < nT := by
      rw [hTT]
      exact Nat.mod_lt _ (by decide)
    have hsn : sn = nameOf f := by rw [← hname, e1, nameH_nameOf]
    rw [kvH_some (pubH R (borderOf y) lay) (readH Mh Wz) hc, hsn]
    show ∃ u < 2 ^ c0.k, H.segH (pubH R (borderOf y) lay) (readH Mh Wz) (nameOf f) a
      (X % R.h.T) = _
    rw [Ti.key_segH f a (X % R.h.T) (by cases f <;> exact ha') hi]
    have hE := (Down.inLut_iff (algebraMap Cb.Gl.F Cb.Gl.E) (algebraMap Cb.Gl.F Cb.Gl.E).injective
      (Policy.LedgerHead.tableOf f)
      (Down.ledgerKey_map (algebraMap Cb.Gl.F Cb.Gl.E) np
        (Inst.Model.Layout.weightsOf ppref kRef Wz).H (Inst.Model.Head.Req.of pol x)
        (cellsH R.h R.L (borderOf y) Mh) f a (X % R.h.T))).2 (HK f a (X % R.h.T) ha' hi)
    have h1 : InLut (lutOfL f) (keyOfL (H.iw (pubH R (borderOf y) lay)) np
        ((cellsH R.h R.L (borderOf y) Mh).cast Cb.Gl.E)
        (fun j v => (((Inst.Model.Layout.weightsOf ppref kRef Wz).H j v : ℤ) : Cb.Gl.E))
        (Inst.Model.Head.Req.of pol x) f a (X % R.h.T)) := by
      cases f
      case HD0 => exact (Down.hd0_ledger (iw_gl R (borderOf y) lay hs) np _ _ _ a _).1 hE
      all_goals exact hE
    have ht : tabL R q = lutOfL f := by
      unfold tabL
      rw [e3]
      exact lutOf_kindL f
    rw [← kvOf_name, kvOf_keyOfL]
    exact row_of_inLut hc0 (ht ▸ hl) h1

/-- **The two clauses are equivalent.** -/
theorem headKeys_iff_inTables :
    L5.HeadKeys R.h R.L y np pol Wz x Mh ↔ (callsH R (borderOf y) lay Mh Wz).InTables :=
  ⟨inTables_of_headKeys hy hFu hF hT hs hKF hnl Z hlay Rq Wz Mh,
    headBridge_of_layout hy hFu hF hT hs hKF hnl Z hlay Rq Wz Mh⟩

/-- The library's clause on the head's keys is the clause ForInH. -/
theorem headKeys_iff_forIn :
    L5.HeadKeys R.h R.L y np pol Wz x Mh ↔ ForInH R (callsH R (borderOf y) lay Mh Wz).K :=
  (headKeys_iff_inTables hy hFu hF hT hs hKF hnl Z hlay Rq Wz Mh).trans
    (forInH_iff_inTables hy (borderOf y) lay Mh Wz).symm

/-- **The head is in order if and only if its meaning without the clause on keys holds and the
clause ForInH holds.** -/
theorem headOrd_iff_forIn :
    HeadOrdLB R.h R.L y np pol Wz x Mh ↔
      L5.HeadR0 R.h R.L y np pol x Mh ∧ ForInH R (callsH R (borderOf y) lay Mh Wz).K :=
  L5.headOrdLB_iff_split.trans
    (and_congr_right fun _ => headKeys_iff_forIn hy hFu hF hT hs hKF hnl Z hlay Rq Wz Mh)

end Back

end OnBytes.Road.Hd

#print axioms OnBytes.Road.Hd.inTables_of_headKeys
#print axioms OnBytes.Road.Hd.headKeys_iff_inTables
#print axioms OnBytes.Road.Hd.headKeys_iff_forIn
#print axioms OnBytes.Road.Hd.headOrd_iff_forIn
