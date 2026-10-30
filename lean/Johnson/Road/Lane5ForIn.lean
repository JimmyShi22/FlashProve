-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Lane5ForIn.lean

At a caller of the lookup whose key vectors are kvA (no such caller is written in this library),
and under five public premises, the second clause of the lookup's own in-joint is equivalent to
the library's clause on looked-up values.

The lookup's block claims before itself (Cb.Fo.forIn, OnBytes/Tie/Pv/Lookup/Forest/FoHole.lean,
which is Port.jIn, OnBytes/Tie/Pv/Lookup/Shift/ShiftQLay.lean, written out there): the caller's
own joint R0, and for every c below h.NC: InTable (Port.nOf h c) (Port.kOf h c) (the caller's key
vector of call c) (the rows of call c's table off the verifier's record).
This file imports none of these files. The three readings of the record are typed, with the bodies
that they have there by a reading, in Johnson/Road/Lane5Rec.lean ("nF", "tauF") and
OnBytes/Tie/Pv/Lookup/Ends/Joint.lean ("kN": the same body as kOf). So at a caller whose layout
has L.K st μ q i := kvA S fs (fun x => μ (nm x)) q i, that clause is "ForInA S fs cell" at cell :=
fun x => μ (nm x), by unfolding; nothing here compiles the two together.

Main definitions and theorems:
* "ForInA S fs cell".
* "SameCalls S fs": the lookup's shape has four calls, and they are the shape's own calls' records.
  Public. "sameCalls_of_hid": from shapeHid's equation, which gives its third line (calls_of_hid,
  Lane5KvAll.lean), and two equations between numbers, which stay premises in this file. A theorem
  at the usual call list: sameCalls_of_usual, Johnson/Road/Lane5SameCalls.lean; all five premises
  of forInA_iff_keys together there: forInA_iff_keys_of_usual. The usual call list (UsualCalls,
  Lane5AttLaid.lean) is no test of the verifier: the verifier takes other call lists.
* "forInA_iff_inTables": ForInA is (callsC S fs cell).InTables (Lane5KeysIff.lean).
* **"forInA_iff_keys"**: under NumsA, LaidA, TabsEq, InsideA, SameCalls: ForInA S fs cell ↔ KeysC S
  cell. So with R0 := the link's meaning without its clause on looked-up values:
  (R0 and the lookup's second clause) ↔ (R0 and that clause): the equivalence that the seam before
  the lookup asks.

What the clause weighs. kvA (OnBytes/Tie/Pv/Lookup/Ends/A.lean) is a term written for this library
over the verifier's records; the verifier holds no key vector. The keys of calls 1 and 2 are
formed from products of cells: the scores (query times key) and the accumulators (softmax weight
times value; denominator times output). So "every call's keys lie in its table", at kvA, holds all
of attention's products, and the part without the lookup clause is thin: small cells, index bits,
the row maximum, the denominator. The equivalence moves that weight; it does not carry it.
-/
import Johnson.Road.Lane5KvAll
import Johnson.Road.Lane5Rec

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open OnBytes.Ends OnBytes.Ends.A
open OnBytes.Attention (Shape ACall)

/-- **The second clause of the lookup's own in-joint, at attention's key vectors.** -/
def ForInA (S : Shape) (fs : Model.Forest.Shape) (cell : NameA → Cb.Gl.E) : Prop :=
  ∀ k < fs.NC, Cb.Lkp.InTable (nF fs k) (kN fs k) (kvA S fs cell k)
    (fun t => ((tauF fs k t : ℕ) : Cb.Gl.E))

/-- **The lookup's shape has the shape's own four calls.** Public. -/
structure SameCalls (S : Shape) (fs : Model.Forest.Shape) : Prop where
  NC : fs.NC = 4
  size : S.calls.size = 4
  calls : fs.calls = S.calls.map fun k => k.call

variable {S : Shape} {fs : Model.Forest.Shape}

/-- A call of the lookup's shape, below 4. -/
theorem SameCalls.callAt (H : SameCalls S fs) {k : ℕ} (hk : k < 4) :
    fs.calls[k]? = some (S.calls.getD k default).call := by
  have hs : k < S.calls.size := by rw [H.size]; exact hk
  rw [H.calls, Array.getElem?_map, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hs]
  rfl

/-- **The lookup's clause is "every call's keys lie in its table" in Lane5Split.lean's letters.** -/
theorem forInA_iff_inTables (H : SameCalls S fs) (cell : NameA → Cb.Gl.E) :
    ForInA S fs cell ↔ (callsC S fs cell).InTables := by
  have hn : ∀ k < 4, nF fs k = (S.calls.getD k default).call.n := by
    intro k hk
    unfold nF
    rw [H.callAt hk]
    rfl
  have ht : ∀ k < 4, ∀ t, tauF fs k t = tauN fs k t := by
    intro k hk t
    unfold tauF tauN
    rw [Array.getD_eq_getD_getElem?, H.callAt hk]
    rfl
  constructor
  · intro h k hk
    have hk4 : k < 4 := hk
    have h1 := h k (by rw [H.NC]; exact hk4)
    rw [hn k hk4] at h1
    intro b hb
    obtain ⟨u, hu, e⟩ := h1 b hb
    have e' : kvA S fs cell k b = ((tauF fs k u : ℕ) : Cb.Gl.E) := e
    refine ⟨u, hu, ?_⟩
    show kvA S fs cell k b = ((tauN fs k u : ℕ) : Cb.Gl.E)
    rw [e', ht k hk4]
  · intro h k hk
    have hk4 : k < 4 := by rw [H.NC] at hk; exact hk
    have h1 := h k hk4
    rw [hn k hk4]
    intro b hb
    obtain ⟨u, hu, e⟩ := h1 b hb
    have e' : kvA S fs cell k b = ((tauN fs k u : ℕ) : Cb.Gl.E) := e
    refine ⟨u, hu, ?_⟩
    show kvA S fs cell k b = ((tauF fs k u : ℕ) : Cb.Gl.E)
    rw [e', ht k hk4]

/-- **The lookup's clause at attention is the library's clause on looked-up values.** -/
theorem forInA_iff_keys (N : NumsA S) {cs : Fin 4 → ACall} (L : LaidA S cs) (T : TabsEq S fs)
    (hin : InsideA S cs) (H : SameCalls S fs) (cell : NameA → Cb.Gl.E) :
    ForInA S fs cell ↔ KeysC S cell :=
  (forInA_iff_inTables H cell).trans (keys_iff N L T hin cell)

/-- SameCalls from shapeHid's equation and two equations between numbers, which stay premises here
(theorems at the usual call list: sameCalls_of_usual, Johnson/Road/Lane5SameCalls.lean). -/
theorem sameCalls_of_hid {lid : ℕ} {cf : Attention.Cfg}
    (h : Attention.shapeHid lid cf = Except.ok (S, fs)) (h1 : fs.NC = 4)
    (h2 : S.calls.size = 4) : SameCalls S fs :=
  ⟨h1, h2, calls_of_hid h⟩

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.forInA_iff_inTables
#print axioms OnBytes.Road.L5.forInA_iff_keys
#print axioms OnBytes.Road.L5.sameCalls_of_hid
