-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/FullFacts.lean

The lookups of the calls of the 25 sub-proofs at the full size (twelve groups of layers, twelve
attention sub-proofs, the output head): three equations on keys and planes, in which no challenge
occurs but θ, the element that keeps the calls apart, and the point of comparison al, at any family
T of lists of integer matrices that meets the bundles of Johnson/HonestTrace/Full.lean and
Johnson/HonestTrace/FullPlanes.lean.

Main definitions:
* "ThreeFacts h kv bits lm ν": for all θ and al, Z = a_pad (P_1^2 G_0), in the terms zRoot, aPad,
  pChain, gRoot of Johnson/HonestTrace/CountsProducts.lean; every x = ν (.cell r c) with r below
  2^lm and c below NC 2^(kT + 5 - lm) has x (x - 1) = 0; and Cb.Fo.Pin.countK h lm
  (Cb.Fo.Pin.pinColK lm ν) = 0 (OnBytes/Tie/Pv/Lookup/Forest/FoPin.lean).
* "AllFacts X i x T": ThreeFacts at each of the 25 lookups, at the library's key vectors and bits
  read from T's lists, for every reading ν of the places Fo.Pl whose cells, at these rows and
  columns, are the cells of the sub-proof's planes' matrix in T.

Main theorems:
* "facts_layers", "facts_att", "facts_head": if LookPub X, MeetsAll X i x T and PlanesLaid X i x T
  hold, ThreeFacts holds at group g < 12, at the attention sub-proof of group g < 12, and at the
  head, for every such ν. "facts_all": so AllFacts X i x T holds.
* "facts_theTrace": if PlanesIn X, LookPub X and MeetsAll X i x (theTrace X i x) hold, then AllFacts
  X i x (theTrace X i x).

Limits. LookPub, PlanesIn, MeetsAll and PlanesLaid are assumed, not proved, in this file; where they
are concluded is said in the files that define them. The sizes are the reference sizes of these
bundles. Keys, bits and readers are this library's terms. AllFacts stands, as PlanesLaid does, at
X.layers (no request's tokens) and at pubHAt X x (placeholders in three fields of the covered
positions; x.w for the checked token at all positions); Johnson/HonestTrace/FullPlanesRun.lean shows
what of these the key vectors, tables and planes read, but carries AllFacts itself to no run's data.
Of the claims of the byte format's page docs/format/11-1-machinery.md the third equation is LP2; the
first two are what the format's "tie step 0" and its test of the bits are about; they are not the
claims LK0, LK(31 + v + dL) and LP1, which read further challenges and the mask row; this file says
nothing of these or of any other claim.

Not claimed: that a prover sends these values or commits to these matrices; that a verifier accepts;
completeness of the protocol.

-/
import Johnson.HonestTrace.FullPlanes
import Johnson.HonestTrace.CountsLayersFacts
import Johnson.HonestTrace.CountsAttentionFacts
import Johnson.HonestTrace.CountsHeadFacts

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace

open Inst.Model
open OnBytes.Road
open OnBytes.Road.L5 (cellZ)
open OnBytes.Road.Alg (cellMW)
open OnBytes.Road.Hd (readH)
open OnBytes.Ends (NameA)

/-- The conclusion of facts_plane (Johnson/HonestTrace/CountsProducts.lean), for all θ and al, as
one proposition: at the shape h, the key vectors kv, the bits, 2^lm rows and the reading ν of the
places. -/
def ThreeFacts (h : Model.Forest.Shape) (kv bits : ℕ → ℕ → Cb.Gl.E) (lm : ℕ)
    (ν : _root_.Fo.Pl → Cb.Gl.E) : Prop :=
  (∀ θ al : Cb.Gl.E, zRoot h kv θ al =
      aPad h θ al * (pChain h bits θ al 1 ^ 2 * gRoot h bits θ al 0)) ∧
    (∀ r < 2 ^ lm, ∀ c < h.NC * 2 ^ (h.kT + 5 - lm), ν (.cell r c) * (ν (.cell r c) - 1) = 0) ∧
    Cb.Fo.Pin.countK h lm (Cb.Fo.Pin.pinColK lm ν) = 0

/-- ThreeFacts at each of the 25 lookups of the calls, at the key vectors and bits read from T's
lists, for every reading ν whose cells are the cells of the sub-proof's planes' matrix in T. -/
def AllFacts (X : Model.Verify.Public) (i : Cm.Idx) (x : Instance ppref) (T : Tr) : Prop :=
  (∀ g < 12, ∀ ν : _root_.Fo.Pl → Cb.Gl.E,
    (∀ r < 2 ^ X.y.h.lmb, ∀ c < X.y.fo.NC * 2 ^ (X.y.fo.kT + 5 - X.y.h.lmb),
      ν (.cell r c) = cellMW (T (2 * g)) i.mat (.cell (Ends.G.iB X.y) r c)) →
    ThreeFacts X.y.fo (Ends.G.kvG X.layers g (cellMW (T (2 * g)) i.mat))
      (fun u j => Ends.G.bitsG X.y (cellMW (T (2 * g)) i.mat) (u * 32 + j)) X.y.h.lmb ν) ∧
  (∀ g < 12, ∀ ν : _root_.Fo.Pl → Cb.Gl.E,
    (∀ r < 2 ^ (Hd.shapeA X g).cf.lmb,
      ∀ c < (fsAt X g).NC * 2 ^ ((fsAt X g).kT + 5 - (Hd.shapeA X g).cf.lmb),
      ν (.cell r c) =
        (cellZ (T (2 * g + 1)) : NameA → Cb.Gl.E) ⟨(Hd.shapeA X g).cf.NAs + 2, r, c⟩) →
    ThreeFacts (fsAt X g) (Ends.A.kvA (Hd.shapeA X g) (fsAt X g) (cellZ (T (2 * g + 1))))
      (fun u j => Ends.A.bitsA (Hd.shapeA X g) (fsAt X g) (cellZ (T (2 * g + 1))) (u * 32 + j))
      (Hd.shapeA X g).cf.lmb ν) ∧
  ∀ ν : _root_.Fo.Pl → Cb.Gl.E,
    (∀ r < 2 ^ X.hS.lmbH, ∀ c < X.HLy.fs.NC * 2 ^ (X.HLy.fs.kT + 5 - X.hS.lmbH),
      ν (.cell r c) = readH (T 24) i.mat (.cell (X.hS.NHf + 2) r c)) →
    ThreeFacts X.HLy.fs (Ends.H.kvH (pubHAt X x) (readH (T 24) i.mat))
      (fun u j => Ends.H.bitsH X.hS X.HLy.fs (readH (T 24) i.mat) (u * 32 + j)) X.hS.lmbH ν

section Laws
variable {X : Model.Verify.Public} {i : Cm.Idx} {x : Instance ppref} {T : Tr}

/-- If LookPub X, MeetsAll X i x T and PlanesLaid X i x T hold and g < 12: for every ν that reads,
at every place .cell r c inside the planes' rows and columns, the cell (r, c) of matrix number G.iB
X.y of the group's list T (2 g), ThreeFacts holds at the lookup of the calls of group g. -/
theorem facts_layers (Q : LookPub X) (M : MeetsAll X i x T) (L : PlanesLaid X i x T) {g : ℕ}
    (hg : g < 12) (ν : _root_.Fo.Pl → Cb.Gl.E)
    (hν : ∀ r < 2 ^ X.y.h.lmb, ∀ c < X.y.fo.NC * 2 ^ (X.y.fo.kT + 5 - X.y.h.lmb),
      ν (.cell r c) = cellMW (T (2 * g)) i.mat (.cell (Ends.G.iB X.y) r c)) :
    ThreeFacts X.y.fo (Ends.G.kvG X.layers g (cellMW (T (2 * g)) i.mat))
      (fun u j => Ends.G.bitsG X.y (cellMW (T (2 * g)) i.mat) (u * 32 + j)) X.y.h.lmb ν := by
  obtain ⟨pc, hy⟩ := Q.lay
  have K := inTable_of_forInG (M.keysG g hg X.layers.tokv)
  have C := fun θ al => factsG X.layers hy Q.sw g _ K (L.layers g hg) ν hν θ al
  exact ⟨fun θ al => (C θ al).1, (C 0 0).2.1, (C 0 0).2.2⟩

/-- If LookPub X, MeetsAll X i x T and PlanesLaid X i x T hold and g < 12: for every ν that reads,
at every place .cell r c inside the planes' rows and columns, the cell (r, c) of matrix number NAs +
2 of the list T (2 g + 1), ThreeFacts holds at the lookup of the calls of the attention sub-proof
of group g. -/
theorem facts_att (Q : LookPub X) (M : MeetsAll X i x T) (L : PlanesLaid X i x T) {g : ℕ}
    (hg : g < 12) (ν : _root_.Fo.Pl → Cb.Gl.E)
    (hν : ∀ r < 2 ^ (Hd.shapeA X g).cf.lmb,
      ∀ c < (fsAt X g).NC * 2 ^ ((fsAt X g).kT + 5 - (Hd.shapeA X g).cf.lmb),
      ν (.cell r c) =
        (cellZ (T (2 * g + 1)) : NameA → Cb.Gl.E) ⟨(Hd.shapeA X g).cf.NAs + 2, r, c⟩) :
    ThreeFacts (fsAt X g) (Ends.A.kvA (Hd.shapeA X g) (fsAt X g) (cellZ (T (2 * g + 1))))
      (fun u j => Ends.A.bitsA (Hd.shapeA X g) (fsAt X g) (cellZ (T (2 * g + 1))) (u * 32 + j))
      (Hd.shapeA X g).cf.lmb ν := by
  obtain ⟨lid, cf, hs⟩ := Q.att g hg
  have K := inTable_of_forInA (M.keysA g hg).1
  have C := fun θ al => factsA hs _ K (L.att g hg) ν hν θ al
  exact ⟨fun θ al => (C θ al).1, (C 0 0).2.1, (C 0 0).2.2⟩

/-- If LookPub X, MeetsAll X i x T and PlanesLaid X i x T hold: for every ν that reads, at every
place .cell r c inside the planes' rows and columns, the cell (r, c) of matrix number NHf + 2 of the
list T 24, ThreeFacts holds at the lookup of the calls of the output head. -/
theorem facts_head (Q : LookPub X) (M : MeetsAll X i x T) (L : PlanesLaid X i x T)
    (ν : _root_.Fo.Pl → Cb.Gl.E)
    (hν : ∀ r < 2 ^ X.hS.lmbH, ∀ c < X.HLy.fs.NC * 2 ^ (X.HLy.fs.kT + 5 - X.hS.lmbH),
      ν (.cell r c) = readH (T 24) i.mat (.cell (X.hS.NHf + 2) r c)) :
    ThreeFacts X.HLy.fs (Ends.H.kvH (pubHAt X x) (readH (T 24) i.mat))
      (fun u j => Ends.H.bitsH X.hS X.HLy.fs (readH (T 24) i.mat) (u * 32 + j)) X.hS.lmbH ν := by
  obtain ⟨tau, hy⟩ := Q.head
  have K := M.keysH (Hd.runReq (runAt X) x) rfl rfl (Hd.reqFits_runReq _ _ x)
  have C := fun θ al => factsH (pubHAt X x) hy _ K
    (fillerIsPad_of_JV (pubHAt X x) hy Q.JV _) L.head ν hν θ al
  exact ⟨fun θ al => (C θ al).1, (C 0 0).2.1, (C 0 0).2.2⟩

/-- If LookPub X, MeetsAll X i x T and PlanesLaid X i x T hold, then AllFacts X i x T. -/
theorem facts_all (Q : LookPub X) (M : MeetsAll X i x T) (L : PlanesLaid X i x T) :
    AllFacts X i x T :=
  ⟨fun _ hg ν hν => facts_layers Q M L hg ν hν, fun _ hg ν hν => facts_att Q M L hg ν hν,
    fun ν hν => facts_head Q M L ν hν⟩

/-- If PlanesIn X, LookPub X and MeetsAll X i x (theTrace X i x) hold, then
AllFacts X i x (theTrace X i x). -/
theorem facts_theTrace (F : PlanesIn X) (Q : LookPub X) (M : MeetsAll X i x (theTrace X i x)) :
    AllFacts X i x (theTrace X i x) :=
  facts_all Q M (planesLaid_theTrace F Q i x)

end Laws

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.facts_layers
#print axioms OnBytes.HonestTrace.facts_att
#print axioms OnBytes.HonestTrace.facts_head
#print axioms OnBytes.HonestTrace.facts_all
#print axioms OnBytes.HonestTrace.facts_theTrace
