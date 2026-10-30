-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/LookAtFull.lean

PremF (Johnson/HonestTrace/LookDefs.lean), the premises of the statements on the rounds rsF of a
sub-proof's lookup, at the lookups of the calls of the 25 sub-proofs at the full size, for any
family T of lists of integer matrices that meets the bundles of Johnson/HonestTrace/Full.lean and
Johnson/HonestTrace/FullPlanes.lean.

"The side premises" are: ν reads, at every place .cell r c inside the planes' rows and columns, the
cell (r, c) of the sub-proof's planes' matrix in T; ν .zero = 0; θ = 0 where the lookup's shape has
one call; C.Fits at the shape's v and d.

Main theorems: "premF_layers", "premF_att", "premF_head": if LookPub X, MeetsAll X i x T and
PlanesLaid X i x T hold, then under the side premises PremF holds at group g < 12, at the attention
sub-proof of group g < 12, and at the head, with the library's key vectors read from T's lists.

Limits. LookPub, MeetsAll and PlanesLaid are assumed, not proved, in this file; where they are
concluded is said in the files that define them. jLK, al, what ν reads at the places .mask j and
.key c i, and the elements in C's lists, whose lengths C.Fits fixes, are arbitrary arguments. The
premise on θ asks nothing where a lookup has several calls. At the two example sets' shapes the
lookups of the layers, of attention and of the head have 8, 4 and 6 calls, by the lines call, callA
and callH of their parameter files; for attention in the goals' scope the 4 is a theorem
("sameCalls_in_scope", Johnson/Goal/Meaning/AttForInScope.lean). The lookups of the smallness tests'
digits are not among the 25.

Not claimed: anything on what follows from PremF; that a prover commits to these matrices.

-/
import Johnson.HonestTrace.FullPlanes
import Johnson.HonestTrace.LookAt

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace.Look

open Inst.Model
open OnBytes.Road
open OnBytes.Road.L5 (cellZ)
open OnBytes.Road.Alg (cellMW)
open OnBytes.Road.Hd (readH)
open OnBytes.Ends (NameA)

variable {X : Model.Verify.Public} {i : Cm.Idx} {x : Instance ppref} {T : Tr}

/-- If LookPub X, MeetsAll X i x T and PlanesLaid X i x T hold and g < 12: if ν reads, inside the
planes' rows and columns, the cells of matrix number G.iB X.y of the list T (2 g), and 0 at .zero; θ
is 0 where the shape has one call; and C.Fits holds: then PremF holds at X.y.fo, lmb and the key
vectors G.kvG of group g read from that list. -/
theorem premF_layers (Q : LookPub X) (M : MeetsAll X i x T) (L : PlanesLaid X i x T) {g : ℕ}
    (hg : g < 12) (jLK : ℕ) (ν : _root_.Fo.Pl → Cb.Gl.E)
    (hν : ∀ r < 2 ^ X.y.h.lmb, ∀ c < X.y.fo.NC * 2 ^ (X.y.fo.kT + 5 - X.y.h.lmb),
      ν (.cell r c) = cellMW (T (2 * g)) i.mat (.cell (Ends.G.iB X.y) r c))
    (h0 : ν .zero = 0) (θ al : Cb.Gl.E) (h1 : FoNums.several X.y.fo = false → θ = 0)
    (C : Chal Cb.Gl.E) (hC : C.Fits X.y.fo.v X.y.fo.d 5) :
    PremF X.y.fo X.y.h.lmb jLK (Ends.G.kvG X.layers g (cellMW (T (2 * g)) i.mat)) θ al ν C := by
  obtain ⟨pc, hy⟩ := Q.lay
  exact premF_G X.layers hy Q.sw g _ (inTable_of_forInG (M.keysG g hg X.layers.tokv))
    (L.layers g hg) jLK ν hν h0 θ al h1 C hC

/-- If LookPub X, MeetsAll X i x T and PlanesLaid X i x T hold and g < 12: if ν reads, inside the
planes' rows and columns, the cells of matrix number NAs + 2 of the list T (2 g + 1), and 0 at
.zero; θ is 0 where the shape has one call; and C.Fits holds: then PremF holds at fsAt X g, lmb and
the key vectors A.kvA of group g's attention sub-proof read from that list. -/
theorem premF_att (Q : LookPub X) (M : MeetsAll X i x T) (L : PlanesLaid X i x T) {g : ℕ}
    (hg : g < 12) (jLK : ℕ) (ν : _root_.Fo.Pl → Cb.Gl.E)
    (hν : ∀ r < 2 ^ (Hd.shapeA X g).cf.lmb,
      ∀ c < (fsAt X g).NC * 2 ^ ((fsAt X g).kT + 5 - (Hd.shapeA X g).cf.lmb),
      ν (.cell r c) =
        (cellZ (T (2 * g + 1)) : NameA → Cb.Gl.E) ⟨(Hd.shapeA X g).cf.NAs + 2, r, c⟩)
    (h0 : ν .zero = 0) (θ al : Cb.Gl.E) (h1 : FoNums.several (fsAt X g) = false → θ = 0)
    (C : Chal Cb.Gl.E) (hC : C.Fits (fsAt X g).v (fsAt X g).d 5) :
    PremF (fsAt X g) (Hd.shapeA X g).cf.lmb jLK
      (Ends.A.kvA (Hd.shapeA X g) (fsAt X g) (cellZ (T (2 * g + 1)))) θ al ν C := by
  obtain ⟨lid, cf, hs⟩ := Q.att g hg
  exact premF_A hs _ (inTable_of_forInA (M.keysA g hg).1) (L.att g hg) jLK ν hν h0 θ al h1 C hC

/-- If LookPub X, MeetsAll X i x T and PlanesLaid X i x T hold: if ν reads, inside the planes' rows
and columns, the cells of matrix number NHf + 2 of the list T 24, and 0 at .zero; θ is 0 where the
shape has one call; and C.Fits holds: then PremF holds at X.HLy.fs, lmbH and the key vectors H.kvH
of the head, read from that list at the public data of the request x. -/
theorem premF_head (Q : LookPub X) (M : MeetsAll X i x T) (L : PlanesLaid X i x T) (jLK : ℕ)
    (ν : _root_.Fo.Pl → Cb.Gl.E)
    (hν : ∀ r < 2 ^ X.hS.lmbH, ∀ c < X.HLy.fs.NC * 2 ^ (X.HLy.fs.kT + 5 - X.hS.lmbH),
      ν (.cell r c) = readH (T 24) i.mat (.cell (X.hS.NHf + 2) r c))
    (h0 : ν .zero = 0) (θ al : Cb.Gl.E) (h1 : FoNums.several X.HLy.fs = false → θ = 0)
    (C : Chal Cb.Gl.E) (hC : C.Fits X.HLy.fs.v X.HLy.fs.d 5) :
    PremF X.HLy.fs X.hS.lmbH jLK (Ends.H.kvH (pubHAt X x) (readH (T 24) i.mat)) θ al ν C := by
  obtain ⟨tau, hy⟩ := Q.head
  exact premF_H (pubHAt X x) hy _
    (M.keysH (Hd.runReq (runAt X) x) rfl rfl (Hd.reqFits_runReq _ _ x))
    (fillerIsPad_of_JV (pubHAt X x) hy Q.JV _) L.head jLK ν hν h0 θ al h1 C hC

end OnBytes.HonestTrace.Look

#print axioms OnBytes.HonestTrace.Look.premF_layers
#print axioms OnBytes.HonestTrace.Look.premF_att
#print axioms OnBytes.HonestTrace.Look.premF_head
