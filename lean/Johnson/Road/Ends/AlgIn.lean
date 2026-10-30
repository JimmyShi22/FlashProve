-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Ends/AlgIn.lean: from keys in the verifier's table to the library's clause on the keys,
one call at a time.
G.lean is OnBytes/Tie/Pv/Lookup/Ends/G.lean: a file of terms written for these files over the
verifier's records; no function of the verifier returns them.
States: (callKey_of_inTable) if all keys of G.lean's key vector of call q lie in the verifier's
table of that call (the library's Cb.Lkp.InTable, at the table fun u => tauN P.y.fo q u), then every
entry of THE LIBRARY's key vector of call cc, below its length, is the image of an entry of the
library's table lut tb cc: the clause «key» of LayerOrd (Johnson/Road/FormsKeysLinkL.lean), one call
at a time.
How: AlgKey.lean's keyVec_kvG; Hd.IsLut (Johnson/Road/HeadTabs.lean): the verifier's record of the
call has the library's table, row by row (here a premise; AlgTabs.lean draws it, at tbRef, from a
test that walks through all rows).
Under: TiesG; TiesW at tbG P and wOfG; AgreeW D w wOfG; AgreeT D tb (tbG P) L0; f = 2 fe; a head has
a width; CallFits, SegFits; cd is P's call q; as many tokens; the lookup's record of call q is c0,
which has the library's table; that table has 2^Tq rows; n is the library's a_c; k is c0's. The
padding key is concluded (padG_of_isLut).
Does not say: that the keys do lie in their tables; anything on identities or on smallness.
-/
import Cb.Gen.LkpAlg
import Cm.SegAlg
import Johnson.Road.HeadTabs
import Johnson.Road.Ends.AlgKey

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Alg

open OnBytes.Ends
open OnBytes.Model (Seg CallD Call)
open OnBytes.Model.Layer (Env)
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim Cell Fam LW aC lut keyVec)

/-- The word of a number, as a number, reads in the library's extension field as the number. -/
theorem word_cast (n : ℕ) :
    (((Model.fOfNat n).toNat : ℕ) : Cb.Gl.E) = ((n : ℕ) : Cb.Gl.E) := by
  have e : Model.fOfNat n = Fmt.Fld.two.red n := rfl
  have h : Slice.toF (Model.fOfNat n) = (n : Cb.Gl.F) := by rw [e, Slice.toF_red]
  have h' : (((Model.fOfNat n).toNat : ℕ) : Cb.Gl.F) = (n : Cb.Gl.F) := h
  calc (((Model.fOfNat n).toNat : ℕ) : Cb.Gl.E)
      = algebraMap Cb.Gl.F Cb.Gl.E (((Model.fOfNat n).toNat : ℕ) : Cb.Gl.F) :=
        (map_natCast _ _).symm
    _ = algebraMap Cb.Gl.F Cb.Gl.E (n : Cb.Gl.F) := by rw [h']
    _ = ((n : ℕ) : Cb.Gl.E) := map_natCast _ _

/-- G.lean's padding key of a call whose record has the library's table is the library's. -/
theorem padG_of_isLut {fo : Model.Forest.Shape} {q : ℕ} {c0 : Call} {T : Inst.Model.Lut}
    (hc0 : fo.calls[q]? = some c0) (hL : Hd.IsLut c0 T) :
    ((tauN fo q (t0N fo q) : ℕ) : Cb.Gl.E) = ((T.pad : ℤ) : Cb.Gl.E) := by
  obtain ⟨m, hm1, hm2⟩ := hL.pad
  have e : tauN fo q (t0N fo q) = (c0.tauAt c0.t0).toNat := by
    unfold tauN t0N
    rw [hc0]
    rfl
  rw [e, hm1, word_cast, ← hm2, Int.cast_natCast]

variable [scl : Scl] {v : Env} {D : Dim} {t : Cell → Cb.Gl.E} {P : Model.Layer.Pub} {g : ℕ}
  {cell : G.NameG → Cb.Gl.E}

/-- **From «the keys of kvG lie in the verifier's table» to the library's clause, at one call.** -/
theorem callKey_of_inTable {tb : Tables} {L0 : ℕ} {w : ℕ → LW Cb.Gl.E} (T : TiesG P g cell D t)
    (Wt : TiesW P g cell D t (tbG P) L0 (wOfG P g cell)) (A : AgreeW D w (wOfG P g cell))
    (B : AgreeT D tb (tbG P) L0) (hffe : D.f = D.fe + D.fe) (hch : 0 < D.P.ch) {q : ℕ}
    {cd : CallD} {weighed : Array Bool} {cc : Fin 8}
    {fam : Seg → Fam} (C : CallFits v D cd weighed cc fam)
    (HS : ∀ s ∈ cd.segs, SegFits v D cd.lJ s (fam s))
    (hcd : P.y.calls.getD q default = cd) (hT : P.y.T = D.T)
    {c0 : Call} (hc0 : P.y.fo.calls[q]? = some c0) (hL : Hd.IsLut c0 (lut tb cc)) {Tq : ℕ}
    (hrows : (lut tb cc).rows = 2 ^ Tq) {n k : ℕ} (hn : n = aC D cc) (hk : k = c0.k)
    (hIn : Cb.Lkp.InTable n k (G.kvG P g cell q)
      (fun u => ((tauN P.y.fo q u : ℕ) : Cb.Gl.E)))
    (X : ℕ) (hX : X < 2 ^ aC D cc) :
    ∃ u ∈ (Cm.Seg.tabOf (lut tb cc) Tq : Cb.Tab Cb.Gl.F).set,
      keyVec D t tb L0 w cc X = algebraMap Cb.Gl.F Cb.Gl.E u := by
  obtain ⟨u, hu, e⟩ := hIn X (by rw [hn]; exact hX)
  have ht : tauN P.y.fo q u = (c0.tauAt u).toNat := by
    unfold tauN
    rw [hc0]
    rfl
  have hu' : u < (lut tb cc).rows := by
    rw [← hL.rows, ← hk]
    exact hu
  obtain ⟨m, hm1, hm2⟩ := hL.row u hu'
  refine ⟨(((lut tb cc).row u : ℤ) : Cb.Gl.F),
    (Cm.Seg.mem_tabOf_iff hrows _).mpr ⟨u, hu', rfl⟩, ?_⟩
  rw [keyVec_kvG T Wt A B hffe hch C HS hcd hT (padG_of_isLut hc0 hL) X hX, e]
  show ((tauN P.y.fo q u : ℕ) : Cb.Gl.E) = _
  rw [ht, hm1, word_cast, map_intCast, ← hm2, Int.cast_natCast]

#print axioms callKey_of_inTable

end OnBytes.Road.Alg
