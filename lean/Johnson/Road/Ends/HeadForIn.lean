-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Ends/HeadForIn.lean: the letters of callsH (Johnson/Road/Ends/HeadInSeam.lean) are the
lookup's own record's: the number of calls, the number of a call's keys and the rows of its table,
as the typed lookup reads them off the verifier's record (FoNums.nOf, kOf, tauN,
OnBytes/Tie/Pv/Lookup/Port/FoNums.lean), are those that callsH takes from the head's layout.

The typed lookup asks of whoever calls it: for every k below fs.NC, the caller's key vector of call
k lies in the table of call k, with 2^n keys, 2^k rows and the rows read off the record fs.calls[k].
ForInH R K is that clause at the head's lookup, for key vectors K.

Main definitions and theorems:
  fsNC_of_layout: in a layout that the verifier's function returns, the lookup's shape has as many
    calls as the layout.
  ForInH R K; kN_eq: kN (OnBytes/Tie/Pv/Lookup/Ends/Joint.lean) is FoNums.kOf, by reflexivity.
  forInH_iff_inTables: ForInH R (the key vectors of callsH) is (callsH R b lay Mh Wz).InTables.
  headKeys_of_forIn: so, under the premises of headBridge_of_layout, ForInH gives the library's
    clause on the head's keys (HeadKeys, Johnson/Road/Lane5SplitH.lean).

Limits: ForInH has the form of the in-claim of OnBytes/Tie/Pv/Lookup/Port/ShiftQPort.lean at the
numbers of FoNums; nothing here compiles it together with that claim. Its K is a letter; where it is
used, K is kvH, a term of this library. Else as in Johnson/Road/Ends/HeadInSeam.lean.

-/
import OnBytes.Tie.Pv.Lookup.Port.FoNums
import Johnson.Road.FormsKeysShape
import Johnson.Road.Ends.HeadInSeam

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd

open OnBytes.Ends
open OnBytes.Model (WsLay WsShape wsLayOf)
open OnBytes.Model.Layer (Lay)
open OnBytes.Model.Head (Border)
open OnBytes.Model.Verify (borderOf)
open Inst.Model (NormPar Mat ppref AcceptancePolicy Instance)
open Inst.Model.Layout (kRef)

/-- The lookup's shape has as many calls as the layout. -/
theorem fsNC_of_layout {h : Model.Head.Shape} {tauFC : Array F} {L : Model.Head.HL}
    (hy : Model.Head.layout h tauFC = .ok L) : L.fs.NC = L.calls.size := by
  unfold Model.Head.layout at hy
  obtain ⟨-, hy⟩ := ok_of_needed hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨L0, -, hy⟩ := ok_of_bind hy
  obtain ⟨cs, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, hy⟩ := ok_of_needed hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨fs, hfs, hy⟩ := ok_of_bind hy
  obtain ⟨-, hy⟩ := ok_of_needed hy
  obtain ⟨kb, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨pub, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, hy⟩ := ok_of_needed hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  cases hy
  show fs.NC = cs.toArray.size
  rw [(shape_calls hfs).2, lookups_eq]
  simp

/-- The number of a call's rows: two texts of one reading. -/
theorem kN_eq : kN = FoNums.kOf := rfl

/-- What the typed lookup asks of its caller's key vectors K, at the head's lookup. -/
def ForInH (R : Model.Head.Run) (K : ℕ → ℕ → Cb.Gl.E) : Prop :=
  ∀ k < R.L.fs.NC, Cb.Lkp.InTable (FoNums.nOf R.L.fs k) (kN R.L.fs k) (K k)
    (fun t => ((FoNums.tauN R.L.fs k t : ℕ) : Cb.Gl.E))

/-- **The clause ForInH is "every call's keys lie in its table" at callsH.** -/
theorem forInH_iff_inTables {R : Model.Head.Run} {tauFC : Array F}
    (hy : Model.Head.layout R.h tauFC = .ok R.L) (b : Border) (lay : WsLay) (Mh : Mats ℤ)
    (Wz : Mat) :
    ForInH R (callsH R b lay Mh Wz).K ↔ (callsH R b lay Mh Wz).InTables := by
  have hNC := fsNC_of_layout hy
  have hcl := fsCalls_of_layout hy
  have hn : ∀ k < R.L.calls.size,
      FoNums.nOf R.L.fs k = (R.L.calls.getD k default).lJ + R.h.lt := by
    intro k hk
    unfold FoNums.nOf
    rw [hcl]
    exact (clN_of_layout hy).2 k hk
  have ht : ∀ k < R.L.calls.size, ∀ t, FoNums.tauN R.L.fs k t = tauN R.L.fs k t := by
    intro k hk t
    have hk' : k < R.L.fs.calls.size := by
      rw [hcl, (clN_of_layout hy).1]
      exact hk
    unfold FoNums.tauN tauN
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk']
    rfl
  constructor
  · intro h k hk
    have hk0 : k < R.L.calls.size := hk
    have h1 := h k (by rw [hNC]; exact hk0)
    rw [hn k hk0] at h1
    intro X hX
    obtain ⟨u, hu, e⟩ := h1 X hX
    have e' : (callsH R b lay Mh Wz).K k X = ((FoNums.tauN R.L.fs k u : ℕ) : Cb.Gl.E) := e
    refine ⟨u, hu, ?_⟩
    show (callsH R b lay Mh Wz).K k X = ((tauN R.L.fs k u : ℕ) : Cb.Gl.E)
    rw [e', ht k hk0]
  · intro h k hk
    have hk0 : k < R.L.calls.size := by rw [hNC] at hk; exact hk
    have h1 := h k hk0
    rw [hn k hk0]
    intro X hX
    obtain ⟨u, hu, e⟩ := h1 X hX
    have e' : (callsH R b lay Mh Wz).K k X = ((tauN R.L.fs k u : ℕ) : Cb.Gl.E) := e
    refine ⟨u, hu, ?_⟩
    show (callsH R b lay Mh Wz).K k X = ((FoNums.tauN R.L.fs k u : ℕ) : Cb.Gl.E)
    rw [e', ht k hk0]

/-- **From the clause ForInH to the library's clause on the head's keys.** -/
theorem headKeys_of_forIn {R : Model.Head.Run}
    (hy : Model.Head.layout R.h tauFCw = .ok R.L) (hFu : FullH R.h) (hF : R.h.famF = 24)
    (hT : R.h.tabS = 4) (hs : R.h.digSh = 8) {np : NormPar} (hKF : R.h.KF = np.K) {y : Lay}
    (hnl : (borderOf y).nl = 5) {s : WsShape} (Z : SizedW s ppref) {lay : WsLay}
    (hlay : wsLayOf s true kRef = .ok lay) {pol : AcceptancePolicy} {x : Instance ppref}
    (Rq : ReqFits R HeadSizes.ref (Inst.Model.Head.Req.of pol x)) (Wz : Mat) (Mh : Mats ℤ)
    (I : ForInH R (callsH R (borderOf y) lay Mh Wz).K) :
    L5.HeadKeys R.h R.L y np pol Wz x Mh :=
  headBridge_of_layout hy hFu hF hT hs hKF hnl Z hlay Rq Wz Mh
    ((forInH_iff_inTables hy (borderOf y) lay Mh Wz).1 I)

end OnBytes.Road.Hd

#print axioms OnBytes.Road.Hd.fsNC_of_layout
#print axioms OnBytes.Road.Hd.forInH_iff_inTables
#print axioms OnBytes.Road.Hd.headKeys_of_forIn
