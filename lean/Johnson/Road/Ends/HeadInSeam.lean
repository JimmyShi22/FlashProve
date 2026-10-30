-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Ends/HeadInSeam.lean: the bridge from the calls of the output head's lookup to the
library's clause on the head's keys ("HeadBridge", Johnson/Road/Lane5SplitH.lean), as a theorem, for
every layout that the verifier's function returns at the library's sizes.

The calls are written for this library over the verifier's records: callsH R b lay Mh Wz: as many
calls as the layout has; call q has 2^(lJ + lt) keys: the key vector kvH
(OnBytes/Tie/Pv/Lookup/Ends/H.lean), a term of this library, which no function of the verifier's
returns, at the reading of names in the integer matrices Mh (behind the head's sub-proof) and Wz
(the committed matrix); its table has the rows of the verifier's record of the call.

WHAT THE BRIDGE HOLDS. In the library's head every rounded product is checked by a key, and the
product is formed inside the key. So the clause on keys holds the product with the output matrix:
the margin of two logits stands in the key of HD0, and a logit is the sum over the channels of the
normalised activation times the weight. kvH forms these sums from the cells of Mh and the digits in
Wz (H.lg, H.wH). The bridge is therefore no renaming of tables: it says that kvH is the library's
formula at these cells and these weights (key_segH, wH_read), and that the tables are the library's.
The other part of the head's meaning (HeadR0, Johnson/Road/Lane5SplitH.lean) reads no weight.

Main theorems:
  fsCalls_of_layout: the lookup's shape holds the layout's records of the calls.
  sizes_of_layout: every segment of every call lists one column for each entry.
  callAt_of_layout: CallAt (Johnson/Road/Ends/HeadIn.lean) for every call that has a segment, at the
    library's table for the call's kind.
  headBridge_of_layout: HeadBridge R.h R.L y np pol Wz x Mh (callsH R (borderOf y) lay Mh Wz).
Its premises, all public but the last: Head.layout has returned R.L on the shape R.h and the clamp's
table tauFCw; the nine numbers FullH; F = 24, sT = 4, sh = 8; the final normalisation's shift is
np's; the stream has five limbs; the shape of the weights agrees with the reference parameters and
wsLayOf has returned lay at the library's number of column bits; ReqFits: the run's covered
positions, positions with a cost and checked tokens are the request's. ReqFits reads R.x.win, which
at the last position, if that is covered, is the token that the prover has named (Head.winOf): at a
run it holds of the request whose y is that token (reqFits_of_instance, Johnson/Road/HeadLaid.lean).
That this token is the reply that the caller was given is not said here.

Limits: an implication and no more: that the keys lie in their tables is not shown. Mh and Wz are
letters: how a field element is lifted to an integer is not said here. The reference sizes. The
converse: Johnson/Road/Ends/HeadBack.lean. That HeadR0 and the clause hold together of some Mh, Wz
and request: Johnson/Road/Ends/HeadWit.lean (all weights 0), Johnson/Road/Ends/HeadWitTrue.lean
(every true request); neither is shown in this file. K is kvH, a term of this library: that the
vector whose extension the verifier's key forms evaluate is kvH is not shown in these files. That
callsH's number of calls, numbers of keys and rows are those that a lookup reads off its own record:
Johnson/Road/Ends/HeadForIn.lean.

-/
import Johnson.Road.Lane5SplitH
import Johnson.Road.HeadLinkL
import Johnson.Road.HeadCallsLaid
import Johnson.Road.HeadFound
import Johnson.Road.HeadPoint
import Johnson.Road.Ends.HeadIn
import Johnson.Road.Ends.HeadTies

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

/-- The lookup's shape holds the layout's records of the calls. -/
theorem fsCalls_of_layout {h : Model.Head.Shape} {tauFC : Array F} {L : Model.Head.HL}
    (hy : Model.Head.layout h tauFC = .ok L) : L.fs.calls = L.cl := by
  unfold Model.Head.layout at hy
  obtain ⟨-, hy⟩ := ok_of_needed hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨L0, -, hy⟩ := ok_of_bind hy
  obtain ⟨cs, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, hy⟩ := ok_of_needed hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨fs, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, hy⟩ := ok_of_needed hy
  obtain ⟨kb, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨pub, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, hy⟩ := ok_of_needed hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  cases hy
  rfl

/-- Every segment of every call lists one column for each entry. -/
theorem sizes_of_layout {h : Model.Head.Shape} {tauFC : Array F} {R : Model.Head.Run}
    (hy : Model.Head.layout h tauFC = .ok R.L) (q : ℕ) :
    ∀ g ∈ (R.L.calls.getD q default).segs, g.pos.size = g.n := by
  have A := admittedH_of_layout hy
  obtain ⟨cs, hc, _, hL⟩ := A.calls
  obtain ⟨c1, _⟩ := callsOf_spec hc
  by_cases hq : q < cs.length
  · have hg : R.L.calls.getD q default = cs[q] := by
      rw [hL]
      exact toArray_getD_some (List.getElem?_eq_getElem hq) default
    obtain ⟨name, kind, asks, fl, e1, e2⟩ := c1 cs[q] (List.getElem_mem hq)
    rw [hg, e1, place_segs_eq]
    intro g hgm
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hgm
    exact (segAt_rising asks (fun a ha => by
      obtain ⟨x, f1, f2⟩ := e2 a ha
      rw [f2]
      exact segments_lt A x (List.mem_of_find?_eq_some f1)) z hz).1
  · have hg : R.L.calls.getD q default = default := by
      rw [hL]
      simp [Array.getD, hq]
    rw [hg]
    intro g hgm
    exact absurd hgm List.not_mem_nil

/-- **The calls of the head's lookup**, at the reading in integer matrices. -/
def callsH (R : Model.Head.Run) (b : Border) (lay : WsLay) (Mh : Mats ℤ) (Wz : Mat) :
    L5.CallsAt where
  NC := R.L.calls.size
  n := fun q => (R.L.calls.getD q default).lJ + R.h.lt
  k := fun q => kN R.L.fs q
  K := H.kvH (pubH R b lay) (readH Mh Wz)
  T := fun q u => ((tauN R.L.fs q u : ℕ) : Cb.Gl.E)

/-- The verifier's factor under HD0 is the inverse of 2^23. -/
theorem iw_gl (R : Model.Head.Run) (b : Border) (lay : WsLay) (hsh : R.h.digSh = 8) :
    (H.iw (pubH R b lay) : Cb.Gl.E) * 2 ^ 23 = 1 := by
  show ((2 : Cb.Gl.E) ^ (R.h.digSh + 15))⁻¹ * 2 ^ 23 = 1
  rw [hsh]
  exact inv_mul_cancel₀ (pow_ne_zero _ two_ne_zero_gl)

/-- What is asked of a call, of a layout that the verifier returns. -/
theorem callAt_of_layout {R : Model.Head.Run} (hy : Model.Head.layout R.h tauFCw = .ok R.L)
    (hF : R.h.famF = 24) (hs : R.h.digSh = 8) (hT : R.h.tabS = 4) {q : ℕ}
    (hg : ∃ g, g ∈ (R.L.calls.getD q default).segs) :
    CallAt R R.L.calls.size (fun q => (R.L.calls.getD q default).lJ + R.h.lt)
      (fun q => kN R.L.fs q) (tabL R) q := by
  have hq : q < R.L.calls.size := by
    by_contra hn
    have e : R.L.calls.getD q default = default := by simp [Array.getD, hn]
    obtain ⟨g, hgm⟩ := hg
    rw [e] at hgm
    exact absurd hgm List.not_mem_nil
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
  refine ⟨hq, ⟨R.L.cl.getD q default, e4, ?_, ?_⟩, ?_⟩
  · unfold tabL
    rw [e2]
    exact hl
  · show kN R.L.fs q = _
    unfold kN
    rw [e4]
    rfl
  · show (R.L.calls.getD q default).J * R.h.T ≤ 2 ^ ((R.L.calls.getD q default).lJ + R.h.lt)
    rw [cols_of_layout hy hq, pow_add]
    exact le_refl _

/-- **The bridge from the head's calls to the library's clause on keys.** -/
theorem headBridge_of_layout {R : Model.Head.Run}
    (hy : Model.Head.layout R.h tauFCw = .ok R.L) (hFu : FullH R.h) (hF : R.h.famF = 24)
    (hT : R.h.tabS = 4) (hs : R.h.digSh = 8) {np : NormPar} (hKF : R.h.KF = np.K) {y : Lay}
    (hnl : (borderOf y).nl = 5) {s : WsShape} (Z : SizedW s ppref) {lay : WsLay}
    (hlay : wsLayOf s true kRef = .ok lay) {pol : AcceptancePolicy} {x : Instance ppref}
    (Rq : ReqFits R HeadSizes.ref (Inst.Model.Head.Req.of pol x)) (Wz : Mat) (Mh : Mats ℤ) :
    L5.HeadBridge R.h R.L y np pol Wz x Mh (callsH R (borderOf y) lay Mh Wz) := by
  intro I f a i ha hi
  have hTT : R.h.T = Inst.Model.Head.nT := by
    unfold Model.Head.Shape.T
    rw [hFu.lt]
    rfl
  exact headKeys_of_inTable (R := R) (P := pubH R (borderOf y) lay) rfl rfl hTT
    (tiesH_of (laid_ref hy hFu.lt hFu.d hFu.V rfl rfl) Rq hFu.XL hKF hs hnl
      (Inst.Model.Head.Req.of_ok pol x)
      (fun k v hk hv => wH_read Z hlay R (borderOf y) Mh Wz hk hv))
    (iw_gl R (borderOf y) lay hs)
    (callsFitL_of_layout hy hFu.lt hFu.d hFu.V hFu.XL rfl rfl
      (tabs_of_layout hy (segsFit_of_layout hy hFu.lt hFu.d hFu.V hFu.XL)) _ np _ _ _)
    (w := fun q => Classical.choose (marks_of_layout hy q))
    (fun q => Classical.choose_spec (marks_of_layout hy q))
    (sizes_of_layout hy)
    (fun q hg => callAt_of_layout hy hF hs hT hg)
    (fun q hq => I q hq) f a i ha hi

end OnBytes.Road.Hd

#print axioms OnBytes.Road.Hd.fsCalls_of_layout
#print axioms OnBytes.Road.Hd.sizes_of_layout
#print axioms OnBytes.Road.Hd.callAt_of_layout
#print axioms OnBytes.Road.Hd.headBridge_of_layout
