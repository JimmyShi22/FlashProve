-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Lane5BridgeA.lean

THE BRIDGE AT ATTENTION, PROVED: if every key of the four key vectors kvA, a term written for this
library over the verifier's records (OnBytes/Tie/Pv/Lookup/Ends/A.lean), at the cells of the integer
matrices Z, is a row of the verifier's own table of its call, then the lookup clause of "the
attention link is in order" holds ("AttKeys", Lane5SplitA.lean). So the link's meaning without its
lookup clause, and "every call's keys lie in its table" AT THESE KEY VECTORS, give that link 2 g + 1
is in order. What stays open lies in that word: see "Not claimed".

Main definitions and theorems:
* "callsA S fs Z": the letters of the lookup's calls ("CallsAt", Lane5Split.lean): NC = 4; n c of
  the shape's call c; k c, T c of the lookup's shape fs (Joint.lean's kN, tauN); K c := kvA S fs
  (cellZ Z) c, over the protocol's field.
* "TabsA S fs": every row of the verifier's table of call c, read in the prime field, is a row of
  the library's table of call c at the letters made from the shape; and the pieces of call c fit
  into its 2^n keys. Public. A premise here; a theorem at what the verifier's shapeHid returns, at
  one shift, ldh = 7, kFD = 16, S = 12, rx = 8 (tabsA_of_hid, Lane5AttHid.lean, with three premises
  on the calls; tabsA_of_usual, Lane5AttSeam.lean, at the call list of four lines); a test with its
  theorem: Lane5KvCheck.lean; the runs: Lane5KvWit.lean.
* **"attBridge"**: under "NumsA", "LaidA", "TabsA": "AttBridge S Z (callsA S fs Z)".
* **"linkOK_of_attCalls"**: the seam, at the reference sizes. "splitA_of_attCalls": the same in
  SplitA's letters, UNDER "AttR0" as a hypothesis of the theorem (SplitA's own premise is not used).

How: kvA = keyVec below "used" (Lane5KvVec.lean), in the protocol's field; the library's key_cast:
the looked-up values over a ring are the images of those over the integers; the map from the prime
field into the protocol's field is one-to-one.

Not claimed: "InTables" for a proof that a verifier accepts; that the cells behind a proof are
integers' images; anything at other call lists than the usual one (four calls, one shift). The
verifier admits configurations with another call list or several shifts in a group.
K is kvA, that term. That the vector whose extension the verifier's key form evaluates is kvA is
shown (OnBytes/Tie/Pv/Lookup/Ends/AlgAW.lean: algW_KR, algW_KFD, algW_R16, algW_WH) only under the
premise rule of these theorems: each slot of the world that a key form reads holds the extension
of its cells (for the scores and accumulators: of the products) at the key point. That file is not
imported here.
S and fs are independent letters here: n is read off S; k and the tables off fs. That fs has S's
own calls' records is SameCalls (Lane5ForIn.lean); its third line is a theorem at what shapeHid
returns (calls_of_hid); its two numbers are premises there, and theorems at the usual call list
(sameCalls_of_usual, Johnson/Road/Lane5SameCalls.lean), which is no test of the verifier.
-/
import Johnson.Road.Lane5SplitA
import Johnson.Road.Lane5KvVec

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open OnBytes.Ends OnBytes.Ends.A
open OnBytes.Attention (ACall)
open Inst.Model (ppref Instance Mat AcceptancePolicy tbRef)
open Inst.Model.AttSeg

/-- **The letters of the lookup's calls at attention.** -/
def callsA (S : Attention.Shape) (fs : Model.Forest.Shape) (Z : Zs) : CallsAt where
  NC := 4
  n := fun c => (S.calls.getD c default).call.n
  k := fun c => kN fs c
  K := fun c => kvA S fs (cellZ Z : NameA → Cb.Gl.E) c
  T := fun c u => ((tauN fs c u : ℕ) : Cb.Gl.E)

/-- **The verifier's tables hold no row that the library's lack, and the pieces fit.** Public. -/
structure TabsA (S : Attention.Shape) (fs : Model.Forest.Shape) : Prop where
  row : ∀ (c : Fin 4) (u : ℕ), u < 2 ^ kN fs c.val →
    ∃ ι : ℕ, ι < (lut (scl := sclOf S) (dimOf S) (tbOf S) c).rows ∧
      ((tauN fs c.val u : ℕ) : Cb.Gl.F) =
        (((lut (scl := sclOf S) (dimOf S) (tbOf S) c).row ι : ℤ) : Cb.Gl.F)
  room : ∀ c : Fin 4, (dimOf S).used c ≤ 2 ^ (S.calls.getD c.val default).call.n

/-- **The bridge at attention.** -/
theorem attBridge {S : Attention.Shape} (N : NumsA S) {cs : Fin 4 → ACall} (L : LaidA S cs)
    {fs : Model.Forest.Shape} (T : TabsA S fs) (Z : Zs) : AttBridge S Z (callsA S fs Z) := by
  intro I c X hX
  obtain ⟨u, hu, e⟩ := I c.val c.isLt X (lt_of_lt_of_le hX (T.room c))
  obtain ⟨ι, hι, er⟩ := T.row c u hu
  refine ⟨ι, hι, ?_⟩
  apply (algebraMap Cb.Gl.F Cb.Gl.E).injective
  have e1 : kvA S fs (cellZ Z : NameA → Cb.Gl.E) c.val X = ((tauN fs c.val u : ℕ) : Cb.Gl.E) := e
  have e2 := congrArg (algebraMap Cb.Gl.F Cb.Gl.E) er
  rw [map_natCast, map_intCast] at e2
  rw [key_cast, map_intCast, map_intCast, ← e2, ← e1, kvA_eq_keyVec N L fs Z c X hX, key_cast]

/-- **The seam before the lookup of attention of group g, with the bridge proved.** -/
theorem linkOK_of_attCalls {S : Attention.Shape} {g : ℕ} (hg : g < 12) (hS : AttSized S)
    {s : Cm.Scales} (hsh : (s.kap (4 * g)).sh = S.cf.sh.getD 0 0)
    (hE : ∀ ι : ℕ, ι < S.u0 → ((S.Tt.getD ι 0 : ℕ) : ℤ) = tbRef.Exp ι) (N : NumsA S)
    {cs : Fin 4 → ACall} (L : LaidA S cs) {fs : Model.Forest.Shape} (T : TabsA S fs) {Z : Zs}
    (pol : AcceptancePolicy) (Wz : Mat) (x : Instance ppref) (R : AttR0 S Z)
    (I : (callsA S fs Z).InTables) :
    LinkOK Cm.Seg.Hd.main (Policy.segPol s pol) Wz x (2 * g + 1) (attMx S g Z) :=
  linkOK_of_attSplit hg hS hsh hE pol Wz x (attBridge N L T Z) R I

/-- **So, under AttR0, the seam of Lane5Split.lean holds there.** SplitA's own premise LinkR0 is not
used. -/
theorem splitA_of_attCalls {S : Attention.Shape} {g : ℕ} (hg : g < 12) (hS : AttSized S)
    {s : Cm.Scales} (hsh : (s.kap (4 * g)).sh = S.cf.sh.getD 0 0)
    (hE : ∀ ι : ℕ, ι < S.u0 → ((S.Tt.getD ι 0 : ℕ) : ℤ) = tbRef.Exp ι) (N : NumsA S)
    {cs : Fin 4 → ACall} (L : LaidA S cs) {fs : Model.Forest.Shape} (T : TabsA S fs) {Z : Zs}
    (pol : AcceptancePolicy) (Wz : Mat) (x : Instance ppref) (R : AttR0 S Z) (A : ℕ → Mx)
    (hA : A (2 * g + 1) = attMx S g Z) :
    SplitA s pol Wz x A g (callsA S fs Z) :=
  splitA_of_att hg hS hsh hE pol Wz x (attBridge N L T Z) R A hA

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.attBridge
#print axioms OnBytes.Road.L5.linkOK_of_attCalls
#print axioms OnBytes.Road.L5.splitA_of_attCalls
