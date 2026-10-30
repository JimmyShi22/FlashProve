-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/LookAtClaims.lean

Under the premises named below, every member of the list Fo.claimsOf
(OnBytes/Tie/Pv/Lookup/Forest/FoClaims.lean) of a lookup's claims is 0 at the rounds rsF
(Johnson/HonestTrace/LookDefs.lean): at the lookups of the calls of a group of layers, of attention
and of the output head, and at the 25 such lookups of the full size.

Main definition: "ClaimsZero h lm jLK kv θ al ν C": every member of Fo.claimsOf h lm jLK at the
rounds rsF h lm jLK kv θ al ν C and the reading ν is 0, where the caller's values are the planes'
column sums Fo.colsK and Cb.Fo.Pin.pinColK of ν and the extensions keysAt of the key vectors kv
(Johnson/Top/H/K3RowOut.lean). It is the conclusion of claims_hon
(Johnson/HonestTrace/LookClaimsHon.lean).

Main theorems. "The side premises" are: ν reads, at every place .cell r c inside the planes' rows
and columns, the cell (r, c) of the sub-proof's planes' matrix; ν .zero = 0; θ = 0 where the
lookup's shape has one call; C.Fits at the shape's v and d.
* "claimsZero_G", "claimsZero_A", "claimsZero_H": under the premises of lawG, lawA, lawH
  (Johnson/HonestTrace/CountsLayers.lean, CountsAttention.lean, CountsHead.lean) and the side
  premises, ClaimsZero holds at the sub-proof's lookup shape, key vectors and planes' rows.
* "claimsZero_layers", "claimsZero_att", "claimsZero_head": if LookPub X, MeetsAll X i x T and
  PlanesLaid X i x T hold (Johnson/HonestTrace/Full.lean, FullPlanes.lean), then under the side
  premises ClaimsZero holds at group g < 12, at the attention sub-proof of group g < 12, and at the
  head, with key vectors and planes read from T's lists.

Limits. All premises are assumed, not proved, in this file. What ν reads at the places .mask j, the
number jLK, al and the elements in C's lists, whose lengths C.Fits fixes, are arbitrary arguments.
The premise on θ asks nothing where a lookup has several calls. At the two example sets' shapes the
lookups of the layers, of attention and of the head have 8, 4 and 6 calls, by the lines call, callA
and callH of their parameter files; for attention in the goals' scope the 4 is a theorem
("sameCalls_in_scope", Johnson/Goal/Meaning/AttForInScope.lean). rsF is a term of this library; no
statement compares it with a prover's program. The lookups of the smallness tests' digits are not
covered. At a layers' sub-proof the protocol has no claim of its own for the join
(docs/format/11-1-machinery.md, "The join"); the list's last member is stated here all the same.

Not claimed: that a verifier accepts these rounds; that the list's members are the forms which a
verifier adds to a sub-proof's equation; completeness of the protocol; anything on what the rounds
show of the keys.

-/
import Johnson.HonestTrace.LookClaimsHon
import Johnson.HonestTrace.LookAtFull

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace.Look

open OnBytes.Model OnBytes.Ends
open OnBytes.Model.Layer (layout)
open OnBytes.Road (Switches)
open OnBytes.Ends.H (NameH PubH)

section
variable {K : Type} [Field K]

open VerifiableInference.OnPublicFiles in
/-- Every member of Fo.claimsOf h lm jLK at the rounds rsF h lm jLK kv θ al ν C and the reading ν is
0; the caller's values are colsK and pinColK of ν and keysAt of kv. -/
def ClaimsZero (h : Forest.Shape) (lm jLK : ℕ) (kv : ℕ → ℕ → K) (θ al : K)
    (ν : _root_.Fo.Pl → K) (C : Chal K) : Prop :=
  ∀ y ∈ _root_.Fo.claimsOf h lm jLK (rsF h lm jLK kv θ al ν C) ν
    (_root_.Fo.colsK h lm (_root_.Fo.endsOf h lm jLK (rsF h lm jLK kv θ al ν C)).zb0 ν)
    (_root_.Fo.colsK h lm (_root_.Fo.endsOf h lm jLK (rsF h lm jLK kv θ al ν C)).zb1 ν)
    (Cb.Fo.Pin.pinColK lm ν) (keysAt h lm jLK kv (rsF h lm jLK kv θ al ν C)), y = 0

variable [DecidableEq K]

/-- Under the premises of premF_G (Johnson/HonestTrace/LookAt.lean): ClaimsZero at P.y.fo, lmb and
the key vectors G.kvG P g cell. -/
theorem claimsZero_G {h : Layer.Shape} {pc : List (List String)} (P : Layer.Pub)
    (hy : layout h pc = .ok P.y) (S : Switches h) (g : ℕ) (cell : G.NameG → K)
    (hin : ∀ c < P.y.fo.NC, Cb.Lkp.InTable (FoNums.nOf P.y.fo c) (FoNums.kOf P.y.fo c)
      (G.kvG P g cell c) (tabOf K P.y.fo c))
    (hb : LaidB P g cell) (jLK : ℕ) (ν : _root_.Fo.Pl → K)
    (hν : ∀ r < 2 ^ P.y.h.lmb, ∀ c < P.y.fo.NC * 2 ^ (P.y.fo.kT + 5 - P.y.h.lmb),
      ν (.cell r c) = cell (.cell (G.iB P.y) r c))
    (h0 : ν .zero = 0) (θ al : K) (h1 : FoNums.several P.y.fo = false → θ = 0) (C : Chal K)
    (hC : C.Fits P.y.fo.v P.y.fo.d 5) :
    ClaimsZero P.y.fo P.y.h.lmb jLK (G.kvG P g cell) θ al ν C :=
  claims_hon _ _ _ _ _ _ _ _ (premF_G P hy S g cell hin hb jLK ν hν h0 θ al h1 C hC)

/-- Under the premises of premF_A: ClaimsZero at fs, lmb and the key vectors A.kvA S fs cell. -/
theorem claimsZero_A {lid : ℕ} {cf : Attention.Cfg} {S : Attention.Shape} {fs : Forest.Shape}
    (hs : Attention.shapeHid lid cf = Except.ok (S, fs)) (cell : NameA → K)
    (hin : ∀ c < fs.NC, Cb.Lkp.InTable (FoNums.nOf fs c) (FoNums.kOf fs c)
      (Ends.A.kvA S fs cell c) (tabOf K fs c))
    (hb : LaidBA S fs cell) (jLK : ℕ) (ν : _root_.Fo.Pl → K)
    (hν : ∀ r < 2 ^ S.cf.lmb, ∀ c < fs.NC * 2 ^ (fs.kT + 5 - S.cf.lmb),
      ν (.cell r c) = cell ⟨S.cf.NAs + 2, r, c⟩)
    (h0 : ν .zero = 0) (θ al : K) (h1 : FoNums.several fs = false → θ = 0) (C : Chal K)
    (hC : C.Fits fs.v fs.d 5) : ClaimsZero fs S.cf.lmb jLK (Ends.A.kvA S fs cell) θ al ν C :=
  claims_hon _ _ _ _ _ _ _ _ (premF_A hs cell hin hb jLK ν hν h0 θ al h1 C hC)

/-- Under the premises of premF_H: ClaimsZero at P.L.fs, lmbH and the key vectors H.kvH P cell. -/
theorem claimsZero_H {tau : Array F} (P : PubH) (hy : Head.layout P.h tau = .ok P.L)
    (cell : NameH → K)
    (hin : ∀ c < P.L.fs.NC, Cb.Lkp.InTable (FoNums.nOf P.L.fs c) (FoNums.kOf P.L.fs c)
      (Ends.H.kvH P cell c) (tabOf K P.L.fs c))
    (hfill : FillerIsPad P cell) (hb : LaidBH P cell) (jLK : ℕ) (ν : _root_.Fo.Pl → K)
    (hν : ∀ r < 2 ^ P.h.lmbH, ∀ c < P.L.fs.NC * 2 ^ (P.L.fs.kT + 5 - P.h.lmbH),
      ν (.cell r c) = cell (.cell (P.h.NHf + 2) r c))
    (h0 : ν .zero = 0) (θ al : K) (h1 : FoNums.several P.L.fs = false → θ = 0) (C : Chal K)
    (hC : C.Fits P.L.fs.v P.L.fs.d 5) :
    ClaimsZero P.L.fs P.h.lmbH jLK (Ends.H.kvH P cell) θ al ν C :=
  claims_hon _ _ _ _ _ _ _ _ (premF_H P hy cell hin hfill hb jLK ν hν h0 θ al h1 C hC)

end

section Full
open Inst.Model
open OnBytes.Road
open OnBytes.Road.L5 (cellZ)
open OnBytes.Road.Alg (cellMW)
open OnBytes.Road.Hd (readH)

variable {X : Model.Verify.Public} {i : Cm.Idx} {x : Instance ppref} {T : Tr}

/-- Under the premises of premF_layers (Johnson/HonestTrace/LookAtFull.lean): ClaimsZero at the
lookup of the calls of group g. -/
theorem claimsZero_layers (Q : LookPub X) (M : MeetsAll X i x T) (L : PlanesLaid X i x T) {g : ℕ}
    (hg : g < 12) (jLK : ℕ) (ν : _root_.Fo.Pl → Cb.Gl.E)
    (hν : ∀ r < 2 ^ X.y.h.lmb, ∀ c < X.y.fo.NC * 2 ^ (X.y.fo.kT + 5 - X.y.h.lmb),
      ν (.cell r c) = cellMW (T (2 * g)) i.mat (.cell (Ends.G.iB X.y) r c))
    (h0 : ν .zero = 0) (θ al : Cb.Gl.E) (h1 : FoNums.several X.y.fo = false → θ = 0)
    (C : Chal Cb.Gl.E) (hC : C.Fits X.y.fo.v X.y.fo.d 5) :
    ClaimsZero X.y.fo X.y.h.lmb jLK (Ends.G.kvG X.layers g (cellMW (T (2 * g)) i.mat)) θ al ν C :=
  claims_hon _ _ _ _ _ _ _ _ (premF_layers Q M L hg jLK ν hν h0 θ al h1 C hC)

/-- Under the premises of premF_att: ClaimsZero at the lookup of the calls of the attention
sub-proof of group g. -/
theorem claimsZero_att (Q : LookPub X) (M : MeetsAll X i x T) (L : PlanesLaid X i x T) {g : ℕ}
    (hg : g < 12) (jLK : ℕ) (ν : _root_.Fo.Pl → Cb.Gl.E)
    (hν : ∀ r < 2 ^ (Hd.shapeA X g).cf.lmb,
      ∀ c < (fsAt X g).NC * 2 ^ ((fsAt X g).kT + 5 - (Hd.shapeA X g).cf.lmb),
      ν (.cell r c) =
        (cellZ (T (2 * g + 1)) : NameA → Cb.Gl.E) ⟨(Hd.shapeA X g).cf.NAs + 2, r, c⟩)
    (h0 : ν .zero = 0) (θ al : Cb.Gl.E) (h1 : FoNums.several (fsAt X g) = false → θ = 0)
    (C : Chal Cb.Gl.E) (hC : C.Fits (fsAt X g).v (fsAt X g).d 5) :
    ClaimsZero (fsAt X g) (Hd.shapeA X g).cf.lmb jLK
      (Ends.A.kvA (Hd.shapeA X g) (fsAt X g) (cellZ (T (2 * g + 1)))) θ al ν C :=
  claims_hon _ _ _ _ _ _ _ _ (premF_att Q M L hg jLK ν hν h0 θ al h1 C hC)

/-- Under the premises of premF_head: ClaimsZero at the lookup of the calls of the output head. -/
theorem claimsZero_head (Q : LookPub X) (M : MeetsAll X i x T) (L : PlanesLaid X i x T)
    (jLK : ℕ) (ν : _root_.Fo.Pl → Cb.Gl.E)
    (hν : ∀ r < 2 ^ X.hS.lmbH, ∀ c < X.HLy.fs.NC * 2 ^ (X.HLy.fs.kT + 5 - X.hS.lmbH),
      ν (.cell r c) = readH (T 24) i.mat (.cell (X.hS.NHf + 2) r c))
    (h0 : ν .zero = 0) (θ al : Cb.Gl.E) (h1 : FoNums.several X.HLy.fs = false → θ = 0)
    (C : Chal Cb.Gl.E) (hC : C.Fits X.HLy.fs.v X.HLy.fs.d 5) :
    ClaimsZero X.HLy.fs X.hS.lmbH jLK (Ends.H.kvH (pubHAt X x) (readH (T 24) i.mat)) θ al ν C :=
  claims_hon _ _ _ _ _ _ _ _ (premF_head Q M L jLK ν hν h0 θ al h1 C hC)

end Full

end OnBytes.HonestTrace.Look

#print axioms OnBytes.HonestTrace.Look.claimsZero_G
#print axioms OnBytes.HonestTrace.Look.claimsZero_A
#print axioms OnBytes.HonestTrace.Look.claimsZero_H
#print axioms OnBytes.HonestTrace.Look.claimsZero_layers
#print axioms OnBytes.HonestTrace.Look.claimsZero_att
#print axioms OnBytes.HonestTrace.Look.claimsZero_head
