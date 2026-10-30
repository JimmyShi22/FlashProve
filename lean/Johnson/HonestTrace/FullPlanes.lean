-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/FullPlanes.lean

The full-size trace with its planes: the matrices b, bA and bH of the 25 sub-proofs hold the bits of
the multiplicities of the trace's own lookup keys, and at them the relation after the challenge
(Cb.Lkp.MidP) holds of each sub-proof's lookup on its own calls.

The setting. Johnson/HonestTrace/Full.lean makes, at the public part X of the verifier's stage, an
index i and a request x, the 25 lists of integer matrices "trFull X pl i x": sub-proof 2 g is the
group g of layers, 2 g + 1 the attention of group g, 24 the output head. The matrix of the planes,
number "bNo X k" of list k, is a letter pl there, cut to the shape of that matrix in X's plan.
Johnson/HonestTrace/CountsLayers.lean, CountsAttention.lean and CountsHead.lean define the planes of
a sub-proof from a reading of its cells: bG, bA, bH. This file puts the two together. The keys are
read from the trace with 0 for all planes ("trBase"), and their planes are laid in ("theTrace").
Under LookPub X no key reads a cell of the planes' matrix, and under PlanesIn X the cut keeps every
cell of the planes, so the planes that lie in theTrace are the planes of theTrace's own keys
("PlanesLaid", "planesLaid_theTrace"). Cb.Gl.E, the field of all readings here, is the library's
challenge field F[x] / (x^3 - 2) over the integers modulo 2^64 - 2^32 + 1 (Cb/Gl/GlField.lean).

Main definitions:
* "fsAt X g", "pubHAt X x": the numbers of the lookup of attention's group g; what the head's keys
  read of public data, at the request x.
* "planesOf": the planes of lists of matrices, as integers 0 and 1, by the sub-proof's number, row
  and column. "trBase", "plOf", "theTrace".
* "PlanesIn X": in the plan of each of the 25 sub-proofs, every row below 2^lm and every column
  below NC 2^(kT + 5 - lm) is inside the shape of the planes' matrix. (Where NC is 0 this asks
  nothing. The subtraction is that of natural numbers, as in "plane_outside",
  Johnson/HonestTrace/Counts.lean.)
* "PlanesLaid X i x T": the readings of the lists of T meet LaidB, LaidBA and LaidBH: at the rows
  below 2^lm and the columns below NC 2^(kT + 5 - lm), the planes' matrix of each list holds the
  planes of the list's own reading.
* "LookPub X": nine premises on the public part X, which the laws of the three kinds of sub-proof
  ask.
* "runAt X": a value of the head's run with X's shape, layout, border and plan, through which
  "midP_head" calls the field keysH of MeetsAll.

Main theorems:
* "planesOf_01": planesOf has the values 0 and 1.
* "planesIn_of_public": where publicOf returns X and X has plans for the 12 groups of layers and of
  attention: PlanesIn X. "planesIn_of_layersHead", "lookPub_of_public": PlanesIn X, and LookPub X,
  where publicOf returns X and Hd.LayersHeadAt X holds (for LookPub X also: scalesHeld returns).
* "cellMW_theTrace", "cellZ_theTrace", "readH_theTrace": under PlanesIn X, for g below 12, the
  reading of list 2 g, 2 g + 1 or 24 of theTrace is the reading of the same list of trBase with bG,
  bA or bH laid over it.
* "theTrace_outside_layers", "theTrace_outside_att", "theTrace_outside_head": from row 2^lm on and
  from column NC 2^(kT + 5 - lm) on, the planes' matrix of a list of theTrace is 0.
* "planesLaid_theTrace": under PlanesIn X and LookPub X: PlanesLaid X i x (theTrace X i x), for
  every index i and every request x.
* "midP_layers", "midP_att", "midP_head": for every family T of lists with MeetsAll X i x T
  (Johnson/HonestTrace/Full.lean) and PlanesLaid X i x T, under LookPub X: Cb.Lkp.MidP at all
  elements θ and al of Cb.Gl.E, of the sub-proof's joint key vector, joint table, public padding and
  planes' bits, with the keys and the bits read from T.

Limits. The full size alone: Instance ppref, 12 groups, the numbers of Hd.LayersHeadAt. The field is
Cb.Gl.E. The definitions are specifications, not programs to run (Johnson/HonestTrace/Counts.lean,
Limits). PlanesIn is a bound from below: a plan's matrix may have more rows and columns, and
theTrace holds 0 in these further cells ("theTrace_outside_layers", "theTrace_outside_att",
"theTrace_outside_head"). From k = 25 on the theorems of this file say of planesOf's values only
that they are 0 or 1 (planesOf_01) and, at an odd k, that they are bA's formula at group k / 2
(planesOf_att); trFull cuts them to 0, since X's plans have no list there. planesLaid_theTrace asks
nothing of the request; the premise that every key is a row of its table enters with MeetsAll, in
the three laws. Of a sub-proof's two lookups this file speaks of the one on the sub-proof's own
calls, not of the smallness test's. The statements stand at X.layers, which holds no request's
tokens, and at pubHAt X x, whose covered positions Hd.covReq x have placeholders in three fields and
whose checked tokens are x.w at all 1,024 positions, while a run of the Lean verifier has { X.layers
with tokv := t }, its own covered positions and its own checked tokens.
Johnson/HonestTrace/FullPlanesRun.lean shows that the key vectors, tables and planes read neither
the tokens nor these three fields, and the checked tokens at covered positions alone; so the
statements hold at { X.layers with tokv := t } and, where X.hS.T = 1,024, at Hd.pubH of every value
of Head.Run with X's shape and layout that fits the request (Hd.ReqFits).

Not claimed: that the key vectors, tables and bits of OnBytes/Tie/Pv/Lookup/Ends/G.lean, A.lean and
H.lean are what the verifier computes or tests; that a prover commits to these matrices; that the
C++ prover chooses these rows; that a proof made from this trace is accepted; anything on a claim, a
round, a mask or a message; that MeetsAll holds of theTrace (at public files in the goals' scope and
a served request: Johnson/Goal/HonestTrace/FullPlanesInScope.lean).

-/
import Johnson.HonestTrace.Full
import Johnson.HonestTrace.CountsAttentionAt
import Johnson.HonestTrace.CountsLayersAt
import Johnson.HonestTrace.CountsLayersSkip
import Johnson.HonestTrace.CountsHeadSkip
import Johnson.HonestTrace.CountsHeadAt
import Johnson.Road.Ends.HeadTies
import Johnson.Road.Ends.HeadWit
import Johnson.Road.HeadL5Pub
import Johnson.Road.HeadCallsLaid
import Johnson.Road.HeadDict
import Johnson.Road.Lane5AttSeamPub
import OnBytes.Tie.Pv.Lookup.Ends.FoPlaneMatPub
import OnBytes.Tie.Pv.Lookup.Ends.FoPlaneMatPubG

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace

open Inst.Model
open OnBytes.Road
open OnBytes.Road.L5 (cellZ Zs)
open OnBytes.Road.Alg (cellMW)
open OnBytes.Road.Hd (readH)
open OnBytes.Ends (NameA)
open OnBytes.Model.Layer (matIx)
open OnBytes.Model.Verify (borderOf layerShape)
open OnBytes.Model.Layer (layout scalesHeld)

/-! ## The planes of 25 lists -/

/-- The numbers of the lookup of the attention sub-proof of group g: the field fs of the plan
X.A[g]; the default value if X has no such plan. -/
def fsAt (X : Model.Verify.Public) (g : ℕ) : Model.Forest.Shape :=
  ((X.A[g]?).map (·.fs)).getD default

/-- What the head's key vectors read of public data, at the public part X and the request x: the
head's shape and layout, the border of the stream's matrix, the covered positions Hd.covReq x, the
tokens x.w at the 1,024 positions, and the layout of the committed weights. -/
def pubHAt (X : Model.Verify.Public) (x : Instance ppref) : Ends.H.PubH :=
  ⟨X.hS, X.HLy, borderOf X.y, Hd.covReq x, (Array.range 1024).map x.w, X.layers.wsLay⟩

/-- The planes of lists L of integer matrices, as integers, by the sub-proof's number k, row and
column: at k = 24, bH at the reading readH (L 24) Wi; at every other even k, bG of group k / 2 at
the reading cellMW (L k) Wi; at an odd k, bA of group k / 2 at the reading cellZ (L k). The readings
are over the field Cb.Gl.E. The 25 sub-proofs have the numbers 0 to 24; from k = 25 on the theorems
of this file say of the formula's values only that they are 0 or 1 and, at an odd k, that they are
bA's formula at group k / 2. -/
noncomputable def planesOf (X : Model.Verify.Public) (x : Instance ppref) (Wi : Mat)
    (L : Tr) : ℕ → ℕ → ℕ → ℤ := fun k r c =>
  if k = 24 then ((bH (pubHAt X x) (readH (L 24) Wi) r c : ℕ) : ℤ)
  else if k % 2 = 0 then ((bG X.layers (k / 2) (cellMW (L k) Wi) r c : ℕ) : ℤ)
  else ((bA (Hd.shapeA X (k / 2)) (fsAt X (k / 2)) (cellZ (L k) : NameA → Cb.Gl.E) r c : ℕ) : ℤ)

/-- The full-size trace with 0 for all planes. -/
noncomputable def trBase (X : Model.Verify.Public) (i : Cm.Idx) (x : Instance ppref) : Tr :=
  trFull X (fun _ _ _ => 0) i x

/-- The planes of the full-size trace: planesOf at the lists of trBase and the weights i.mat. -/
noncomputable def plOf (X : Model.Verify.Public) (i : Cm.Idx)
    (x : Instance ppref) : ℕ → ℕ → ℕ → ℤ :=
  planesOf X x i.mat (trBase X i x)

/-- **The full-size trace with its planes**: trFull with plOf for the planes. -/
noncomputable def theTrace (X : Model.Verify.Public) (i : Cm.Idx)
    (x : Instance ppref) : Tr :=
  trFull X (plOf X i x) i x

/-- In the plan of each of the 25 sub-proofs of X, every row below 2^lm and column below NC 2^(kT +
5 - lm) lies inside the shape of the planes' matrix, number bNo X k of the list; lm, NC and kT are
the sub-proof's own numbers. -/
structure PlanesIn (X : Model.Verify.Public) : Prop where
  /-- the matrix b of each group of layers -/
  layers : ∀ g < 12, ∀ r c, r < 2 ^ X.y.h.lmb →
    c < X.y.fo.NC * 2 ^ (X.y.fo.kT + 5 - X.y.h.lmb) → InShape X (2 * g) (bNo X (2 * g)) r c
  /-- the matrix bA of each group's attention -/
  att : ∀ g < 12, ∀ r c, r < 2 ^ (Hd.shapeA X g).cf.lmb →
    c < (fsAt X g).NC * 2 ^ ((fsAt X g).kT + 5 - (Hd.shapeA X g).cf.lmb) →
    InShape X (2 * g + 1) (bNo X (2 * g + 1)) r c
  /-- the matrix bH of the head -/
  head : ∀ r c, r < 2 ^ X.hS.lmbH → c < X.HLy.fs.NC * 2 ^ (X.HLy.fs.kT + 5 - X.hS.lmbH) →
    InShape X 24 (bNo X 24) r c

/-! ## Numbers -/

/-- For g below 12 the planes' number in the list of sub-proof 2 g is G.iB of X's layout. -/
theorem bNoL (X : Model.Verify.Public) {g : ℕ} (hg : g < 12) :
    bNo X (2 * g) = Ends.G.iB X.layers.y := bNo_even X hg


section
variable (X : Model.Verify.Public) (x : Instance ppref) (Wi : Mat) (L : Tr)

/-- For g below 12, planesOf at sub-proof 2 g is bG of group g at the reading of list 2 g. -/
theorem planesOf_layers {g : ℕ} (hg : g < 12) (r c : ℕ) :
    planesOf X x Wi L (2 * g) r c =
      ((bG X.layers g (cellMW (L (2 * g)) Wi) r c : ℕ) : ℤ) := by
  unfold planesOf
  rw [if_neg (by omega), if_pos (by omega), show 2 * g / 2 = g by omega]

/-- planesOf at sub-proof 2 g + 1 is bA of group g at the reading of list 2 g + 1. -/
theorem planesOf_att (g r c : ℕ) :
    planesOf X x Wi L (2 * g + 1) r c =
      ((bA (Hd.shapeA X g) (fsAt X g) (cellZ (L (2 * g + 1)) : NameA → Cb.Gl.E) r c : ℕ) : ℤ) := by
  unfold planesOf
  rw [if_neg (by omega), if_neg (by omega), show (2 * g + 1) / 2 = g by omega]

/-- planesOf at sub-proof 24 is bH at the reading of list 24. -/
theorem planesOf_head (r c : ℕ) :
    planesOf X x Wi L 24 r c =
      ((bH (pubHAt X x) (readH (L 24) Wi) r c : ℕ) : ℤ) := if_pos rfl

/-- Every value of planesOf is 0 or 1. -/
theorem planesOf_01 (k r c : ℕ) :
    planesOf X x Wi L k r c = 0 ∨ planesOf X x Wi L k r c = 1 := by
  have cast01 : ∀ {n : ℕ}, n = 0 ∨ n = 1 → ((n : ℕ) : ℤ) = 0 ∨ ((n : ℕ) : ℤ) = 1 := by
    rintro n (h | h) <;> simp [h]
  unfold planesOf
  split_ifs
  · exact cast01 (plane_01 _ _ _ _ _)
  · exact cast01 (plane_01 _ _ _ _ _)
  · exact cast01 (plane_01 _ _ _ _ _)

end

/-! ## The trace outside and at its planes -/

/-- At a number a of list k that is not the planes' number, trFull is the same for all pl. -/
theorem trFull_off (X : Model.Verify.Public) (pl pl' : ℕ → ℕ → ℕ → ℤ) (i : Cm.Idx)
    (x : Instance ppref) {k a : ℕ} (ha : a ≠ bNo X k) :
    trFull X pl i x k a = trFull X pl' i x k a := by
  funext r c
  by_cases h : InShape X k a r c
  · rw [trFull_cells X pl i x h ha, trFull_cells X pl' i x h ha]
  · rw [trFull_out X pl i x h, trFull_out X pl' i x h]

/-- If pl k is 0 at every row and column that is not inside the shape of the planes' matrix of
sub-proof k, then that matrix of trFull X pl i x is pl k, at all rows and columns. -/
theorem trFull_planes_all (X : Model.Verify.Public) (pl : ℕ → ℕ → ℕ → ℤ) (i : Cm.Idx)
    (x : Instance ppref) {k : ℕ} (h0 : ∀ r c, ¬ InShape X k (bNo X k) r c → pl k r c = 0) :
    trFull X pl i x k (bNo X k) = pl k := by
  funext r c
  by_cases h : InShape X k (bNo X k) r c
  · exact trFull_planes X pl i x h
  · rw [trFull_out X pl i x h, h0 r c h]

/-! ## The planes' matrices lie inside the shapes -/

/-- If mats is the list of matrices in the plan of sub-proof k, and its entry a has m rows with m /
2^lm = 1 and at least cols columns, then every row below 2^lm and column below cols is inside the
shape of entry a. -/
theorem inShape_of_test {X : Model.Verify.Public} {k : ℕ} {mats : Array Model.TMat}
    (e : planMats X k = mats) {a lm cols r c : ℕ} (h1 : (mats.getD a {}).m / 2 ^ lm = 1)
    (h2 : cols ≤ (mats.getD a {}).k) (hr : r < 2 ^ lm) (hc : c < cols) : InShape X k a r c := by
  have hm : 2 ^ lm ≤ (mats.getD a {}).m := by
    by_contra hlt
    rw [Nat.div_eq_of_lt (Nat.lt_of_not_le hlt)] at h1
    exact absurd h1 (by norm_num)
  have ha : a < mats.size := by
    by_contra hge
    have e0 : mats.getD a {} = {} := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (Nat.le_of_not_lt hge)]
      rfl
    rw [e0] at hm
    exact absurd hm (Nat.not_le.2 (Nat.two_pow_pos lm))
  unfold InShape
  rw [e]
  exact ⟨ha, lt_of_lt_of_le hr hm, lt_of_lt_of_le hc h2⟩

/-- Where publicOf returns X, and X has a plan G[g] and a plan A[g] for every g below 12: PlanesIn
X. The three tests Fo.planeMatB, Fo.planeMatAB and Fo.planeMatHB (under OnBytes/Tie/Pv/Lookup/Ends/)
say true at everything that publicOf returns, and PlanesIn is read off them. -/
theorem planesIn_of_public {pol KL : ByteArray} {lay : Option ByteArray}
    {X : Model.Verify.Public} (h : Model.Verify.publicOf pol KL lay = .ok X)
    (hG : ∀ g < 12, ∃ P, X.G[g]? = some P) (hA : ∀ g < 12, ∃ P, X.A[g]? = some P) :
    PlanesIn X := by
  refine ⟨fun g hg r c hr hc => ?_, fun g hg r c hr hc => ?_, fun r c hr hc => ?_⟩
  · obtain ⟨P, hP⟩ := hG g hg
    have t := Fo.PlaneMatG.public_planeMatB h g P hP
    simp only [Fo.planeMatB, Bool.and_eq_true, decide_eq_true_eq] at t
    have e : planMats X (2 * g) = P.tl.mats := by
      unfold planMats
      rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), show 2 * g / 2 = g by omega, hP]
      rfl
    rw [bNoL X hg]
    exact inShape_of_test e t.1.2 t.2 hr hc
  · obtain ⟨P, hP⟩ := hA g hg
    have t := Fo.PlaneMat.public_planeMatAB h g P hP
    simp only [Fo.planeMatAB, Bool.and_eq_true, decide_eq_true_eq] at t
    have e : planMats X (2 * g + 1) = P.mats := by
      unfold planMats
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
        show (2 * g + 1) / 2 = g by omega, hP]
      rfl
    have eS : Hd.shapeA X g = P.S := by
      unfold Hd.shapeA
      rw [hP]
      rfl
    have eF : fsAt X g = P.fs := by
      unfold fsAt
      rw [hP]
      rfl
    rw [bNo_odd X g]
    rw [eS] at hr hc ⊢
    rw [eF] at hc
    exact inShape_of_test e t.1.2 t.2 hr hc
  · have t := Fo.PlaneMat.public_planeMatHB h
    simp only [Fo.planeMatHB, Bool.and_eq_true, decide_eq_true_eq] at t
    have e : planMats X 24 = X.H.tl.mats := by
      unfold planMats
      rw [if_neg (by omega), if_pos rfl]
    rw [bNo_head X]
    exact inShape_of_test e t.1.2 t.2 hr hc

/-! ## Readers of lists with the planes laid in -/

/-- If the list Z' of integer matrices is the list Z outside number G.iB P.y, and holds there bG of
the reading of Z, then the reading of Z' is the reading of Z with bG laid over it. -/
theorem cellMW_withBG (P : Model.Layer.Pub) (g : ℕ) (Wi : Mat) {Z Z' : Mats ℤ}
    (h1 : ∀ a, a ≠ Ends.G.iB P.y → Z' a = Z a)
    (h2 : ∀ r c, Z' (Ends.G.iB P.y) r c = ((bG P g (cellMW Z Wi) r c : ℕ) : ℤ)) :
    cellMW Z' Wi = withBG P g (cellMW Z Wi) := by
  funext n
  cases n with
  | w r c => rfl
  | cell m r c =>
    show ((Z' m r c : ℤ) : Cb.Gl.E) =
      if m = Ends.G.iB P.y then ((bG P g (cellMW Z Wi) r c : ℕ) : Cb.Gl.E)
      else ((Z m r c : ℤ) : Cb.Gl.E)
    by_cases hm : m = Ends.G.iB P.y
    · subst hm
      rw [if_pos rfl, h2, Int.cast_natCast]
    · rw [if_neg hm, h1 m hm]

/-- If the list Z' of integer matrices is the list Z outside number NHf + 2, and holds there bH of
the reading of Z, then the reading of Z' is the reading of Z with bH laid over it. -/
theorem readH_withBH (P : Ends.H.PubH) (Wz : Mat) {Z Z' : Mats ℤ}
    (h1 : ∀ a, a ≠ P.h.NHf + 2 → Z' a = Z a)
    (h2 : ∀ r c, Z' (P.h.NHf + 2) r c = ((bH P (readH Z Wz) r c : ℕ) : ℤ)) :
    readH Z' Wz = withBH P (readH Z Wz) := by
  funext n
  cases n with
  | w r c => rfl
  | cell m r c =>
    show ((Z' m r c : ℤ) : Cb.Gl.E) =
      if m = P.h.NHf + 2 then ((bH P (readH Z Wz) r c : ℕ) : Cb.Gl.E)
      else ((Z m r c : ℤ) : Cb.Gl.E)
    by_cases hm : m = P.h.NHf + 2
    · subst hm
      rw [if_pos rfl, h2, Int.cast_natCast]
    · rw [if_neg hm, h1 m hm]

/-! ## The trace's planes are the planes of the trace's own keys -/

section Laid
variable {X : Model.Verify.Public} (F : PlanesIn X) (i : Cm.Idx) (x : Instance ppref)
include F

/-- Under PlanesIn X, for g below 12: the reading of list 2 g of theTrace is the reading of list 2 g
of trBase with bG laid over it. -/
theorem cellMW_theTrace {g : ℕ} (hg : g < 12) :
    cellMW (theTrace X i x (2 * g)) i.mat =
      withBG X.layers g (cellMW (trBase X i x (2 * g)) i.mat) := by
  refine cellMW_withBG X.layers g i.mat
    (fun a ha => trFull_off X _ _ i x (by rw [bNoL X hg]; exact ha)) (fun r c => ?_)
  rw [← bNoL X hg]
  unfold theTrace
  rw [trFull_planes_all X _ i x (fun r c hn => ?_)]
  · exact planesOf_layers X x i.mat _ hg r c
  · show planesOf X x i.mat _ (2 * g) r c = 0
    rw [planesOf_layers X x i.mat _ hg r c]
    have ho : 2 ^ X.y.h.lmb ≤ r ∨ X.y.fo.NC * 2 ^ (X.y.fo.kT + 5 - X.y.h.lmb) ≤ c := by
      by_contra hc
      rw [not_or, Nat.not_le, Nat.not_le] at hc
      exact hn (F.layers g hg r c hc.1 hc.2)
    exact congrArg Nat.cast (plane_outside _ _ _ ho)

/-- Under PlanesIn X, for g below 12: the reading of list 2 g + 1 of theTrace is the reading of list
2 g + 1 of trBase with bA laid over it. -/
theorem cellZ_theTrace {g : ℕ} (hg : g < 12) :
    (cellZ (theTrace X i x (2 * g + 1)) : NameA → Cb.Gl.E) =
      withBA (Hd.shapeA X g) (fsAt X g) (cellZ (trBase X i x (2 * g + 1))) := by
  refine cellZ_withBA _ _
    (fun a ha => trFull_off X _ _ i x (by rw [bNo_odd X g]; exact ha)) (fun r c => ?_)
  rw [← bNo_odd X g]
  unfold theTrace
  rw [trFull_planes_all X _ i x (fun r c hn => ?_)]
  · exact planesOf_att X x i.mat _ g r c
  · show planesOf X x i.mat _ (2 * g + 1) r c = 0
    rw [planesOf_att X x i.mat _ g r c]
    have ho : 2 ^ (Hd.shapeA X g).cf.lmb ≤ r ∨
        (fsAt X g).NC * 2 ^ ((fsAt X g).kT + 5 - (Hd.shapeA X g).cf.lmb) ≤ c := by
      by_contra hc
      rw [not_or, Nat.not_le, Nat.not_le] at hc
      exact hn (F.att g hg r c hc.1 hc.2)
    exact congrArg Nat.cast (plane_outside _ _ _ ho)

/-- Under PlanesIn X: the reading of list 24 of theTrace is the reading of list 24 of trBase with bH
laid over it. -/
theorem readH_theTrace :
    readH (theTrace X i x 24) i.mat =
      withBH (pubHAt X x) (readH (trBase X i x 24) i.mat) := by
  refine readH_withBH (pubHAt X x) i.mat
    (fun a ha => trFull_off X _ _ i x (by rw [bNo_head X]; exact ha)) (fun r c => ?_)
  show theTrace X i x 24 (X.hS.NHf + 2) r c = _
  rw [← bNo_head X]
  unfold theTrace
  rw [trFull_planes_all X _ i x (fun r c hn => ?_)]
  · exact planesOf_head X x i.mat _ r c
  · show planesOf X x i.mat _ 24 r c = 0
    rw [planesOf_head X x i.mat _ r c]
    have ho : 2 ^ X.hS.lmbH ≤ r ∨ X.HLy.fs.NC * 2 ^ (X.HLy.fs.kT + 5 - X.hS.lmbH) ≤ c := by
      by_contra hc
      rw [not_or, Nat.not_le, Nat.not_le] at hc
      exact hn (F.head r c hc.1 hc.2)
    exact congrArg Nat.cast (plane_outside _ _ _ ho)

omit F in
/-- For g below 12: from row 2^lmb on and from column NC 2^(kT + 5 - lmb) on, the planes' matrix of
list 2 g of theTrace is 0. -/
theorem theTrace_outside_layers {g : ℕ} (hg : g < 12) {r c : ℕ}
    (ho : 2 ^ X.y.h.lmb ≤ r ∨ X.y.fo.NC * 2 ^ (X.y.fo.kT + 5 - X.y.h.lmb) ≤ c) :
    theTrace X i x (2 * g) (bNo X (2 * g)) r c = 0 := by
  by_cases h : InShape X (2 * g) (bNo X (2 * g)) r c
  · unfold theTrace
    rw [trFull_planes X _ i x h]
    show planesOf X x i.mat _ (2 * g) r c = 0
    rw [planesOf_layers X x i.mat _ hg r c]
    exact congrArg Nat.cast (plane_outside _ _ _ ho)
  · exact trFull_out X _ i x h

omit F in
/-- From row 2^lmb on and from column NC 2^(kT + 5 - lmb) on, the planes' matrix of list 2 g + 1 of
theTrace is 0; lmb, NC and kT are those of the attention of group g. -/
theorem theTrace_outside_att (g : ℕ) {r c : ℕ}
    (ho : 2 ^ (Hd.shapeA X g).cf.lmb ≤ r ∨
      (fsAt X g).NC * 2 ^ ((fsAt X g).kT + 5 - (Hd.shapeA X g).cf.lmb) ≤ c) :
    theTrace X i x (2 * g + 1) (bNo X (2 * g + 1)) r c = 0 := by
  by_cases h : InShape X (2 * g + 1) (bNo X (2 * g + 1)) r c
  · unfold theTrace
    rw [trFull_planes X _ i x h]
    show planesOf X x i.mat _ (2 * g + 1) r c = 0
    rw [planesOf_att X x i.mat _ g r c]
    exact congrArg Nat.cast (plane_outside _ _ _ ho)
  · exact trFull_out X _ i x h

omit F in
/-- From row 2^lmbH on and from column NC 2^(kT + 5 - lmbH) on, the planes' matrix of list 24 of
theTrace is 0. -/
theorem theTrace_outside_head {r c : ℕ}
    (ho : 2 ^ X.hS.lmbH ≤ r ∨ X.HLy.fs.NC * 2 ^ (X.HLy.fs.kT + 5 - X.hS.lmbH) ≤ c) :
    theTrace X i x 24 (bNo X 24) r c = 0 := by
  by_cases h : InShape X 24 (bNo X 24) r c
  · unfold theTrace
    rw [trFull_planes X _ i x h]
    show planesOf X x i.mat _ 24 r c = 0
    rw [planesOf_head X x i.mat _ r c]
    exact congrArg Nat.cast (plane_outside _ _ _ ho)
  · exact trFull_out X _ i x h

/-- Under PlanesIn X, for g below 12: if KeysSkipB holds at the reading of list 2 g of trBase, then
the reading of list 2 g of theTrace meets LaidB. -/
theorem laidB_theTrace {g : ℕ} (hg : g < 12)
    (hk : KeysSkipB X.layers g (cellMW (trBase X i x (2 * g)) i.mat)) :
    LaidB X.layers g (cellMW (theTrace X i x (2 * g)) i.mat) := by
  rw [cellMW_theTrace F i x hg]
  exact withBG_laid _ _ _ hk

/-- Under PlanesIn X, for g below 12: if shapeHid returns (Hd.shapeA X g, fsAt X g) at some cap and
configuration, then the reading of list 2 g + 1 of theTrace meets LaidBA. -/
theorem laidBA_theTrace {g : ℕ} (hg : g < 12) {lid : ℕ} {cf : Attention.Cfg}
    (hs : Attention.shapeHid lid cf = Except.ok (Hd.shapeA X g, fsAt X g)) :
    LaidBA (Hd.shapeA X g) (fsAt X g)
      (cellZ (theTrace X i x (2 * g + 1)) : NameA → Cb.Gl.E) := by
  rw [cellZ_theTrace F i x hg]
  exact withBA_laid hs _

/-- Under PlanesIn X: if KeysSkipBH holds at the reading of list 24 of trBase, then the reading of
list 24 of theTrace meets LaidBH. -/
theorem laidBH_theTrace
    (hk : KeysSkipBH (pubHAt X x) (readH (trBase X i x 24) i.mat)) :
    LaidBH (pubHAt X x) (readH (theTrace X i x 24) i.mat) := by
  rw [readH_theTrace F i x]
  exact withBH_laid _ _ hk

end Laid

/-! ## The relation after the challenge (MidP) at a trace that holds its own planes -/

/-- In each of the 25 lists of T the planes' matrix holds, at the rows below 2^lm and the columns
below NC 2^(kT + 5 - lm), the planes of the list's own reading:
LaidB at the 12 groups of layers, LaidBA at the 12 groups of attention, LaidBH at the head. The
weights are i.mat, the head's public data are those of the request x, the field is Cb.Gl.E. -/
structure PlanesLaid (X : Model.Verify.Public) (i : Cm.Idx) (x : Instance ppref) (T : Tr) :
    Prop where
  /-- the groups of layers -/
  layers : ∀ g < 12, LaidB X.layers g (cellMW (T (2 * g)) i.mat)
  /-- the groups' attention -/
  att : ∀ g < 12,
    LaidBA (Hd.shapeA X g) (fsAt X g) (cellZ (T (2 * g + 1)) : NameA → Cb.Gl.E)
  /-- the head -/
  head : LaidBH (pubHAt X x) (readH (T 24) i.mat)

/-- What the laws of the three kinds of sub-proof ask of the public part X: Layer.layout returns X.y
at X's shape of the layers; that shape meets Switches, scalesHeld returns at it, it has p4 = true
and an even dh; X.y has 12 groups; for every g below 12 shapeHid returns (Hd.shapeA X g, fsAt X g)
at some cap and configuration; Head.layout returns X.HLy at X.hS; and the head's layout has JV = V.
-/
structure LookPub (X : Model.Verify.Public) : Prop where
  /-- the layers' layout is what the verifier's function returns -/
  lay : ∃ pc, layout (layerShape X.P) pc = .ok X.y
  /-- the layers' switches -/
  sw : Switches (layerShape X.P)
  /-- the verifier's test on the scales returns -/
  sc : scalesHeld (layerShape X.P) X.layers.sc = .ok ()
  /-- twelve groups of layers -/
  groups : X.y.NGr = 12
  /-- the proof covers attention -/
  p4 : (layerShape X.P).p4 = true
  /-- the width of a head is even -/
  dh : (layerShape X.P).dh % 2 = 0
  /-- each attention sub-proof's shape and lookup are what the verifier's function returns -/
  att : ∀ g < 12, ∃ lid cf, Attention.shapeHid lid cf = Except.ok (Hd.shapeA X g, fsAt X g)
  /-- the head's layout is what the verifier's function returns -/
  head : ∃ tau, Model.Head.layout X.hS tau = .ok X.HLy
  /-- the vocabulary has no filler entries -/
  JV : X.HLy.JV = X.hS.V

/-- **The planes in the trace are the planes of the trace's own keys.** Under PlanesIn X and LookPub
X, for every index i and every request x: PlanesLaid X i x (theTrace X i x). -/
theorem planesLaid_theTrace {X : Model.Verify.Public} (F : PlanesIn X) (Q : LookPub X)
    (i : Cm.Idx) (x : Instance ppref) : PlanesLaid X i x (theTrace X i x) := by
  obtain ⟨pc, hy⟩ := Q.lay
  obtain ⟨tau, hyH⟩ := Q.head
  have hk := keysSkipBH (pubHAt X x) hyH (readH (trBase X i x 24) i.mat)
  refine ⟨fun g hg => laidB_theTrace F i x hg
    (keysSkipB (P := X.layers) hy Q.sw Q.sc (lt_of_lt_of_eq hg Q.groups.symm) Q.p4 Q.dh _),
    fun g hg => ?_, laidBH_theTrace F i x hk⟩
  obtain ⟨lid, cf, hs⟩ := Q.att g hg
  exact laidBA_theTrace F i x hg hs

/-- A value of the head's run with the shape, the layout, the border and the plan of X, and
placeholders in the fields that hold what a run receives and draws. -/
def runAt (X : Model.Verify.Public) : Model.Head.Run :=
  ⟨X.hS, X.HLy, borderOf X.y, X.H, default,
    ⟨#[], default, #[], #[], 0, #[], default, 0, #[], default, default, default, #[], 0, 0⟩,
    default, 0⟩

section Public
variable {pol KL : ByteArray} {lay : Option ByteArray} {X : Model.Verify.Public}

/-- Where publicOf returns X and Hd.LayersHeadAt X holds: for every g below 12, X has a plan G[g],
and a plan A[g], and shapeHid returns (Hd.shapeA X g, fsAt X g) at some cap and configuration. -/
theorem plans_there (h : Model.Verify.publicOf pol KL lay = .ok X) (B : Hd.LayersHeadAt X) :
    (∀ g < 12, ∃ P, X.G[g]? = some P) ∧
      ∀ g < 12, ∃ P lid cf, X.A[g]? = some P ∧
        Attention.shapeHid lid cf = Except.ok (Hd.shapeA X g, fsAt X g) := by
  refine ⟨fun g hg => ?_, fun g hg => ?_⟩
  · obtain ⟨sc, rope, wsLay, V, tokv, set, hP, hG⟩ := Hd.public_plans h
    obtain ⟨hsz, -⟩ := Hd.plan_labels hP hG
    exact ⟨_, Array.getElem?_eq_getElem (by rw [hsz, B.groups]; exact hg)⟩
  · obtain ⟨Ag, lines, cf, hA, eS, -, hh, -⟩ :=
      L5.hid_of_public h B.p4 (by rw [B.groups]; exact hg)
    have eF : fsAt X g = Ag.fs := by
      unfold fsAt
      rw [hA]
      rfl
    exact ⟨Ag, _, cf, hA, by rw [← eS, eF]; exact hh⟩

/-- Where publicOf returns X and Hd.LayersHeadAt X holds: PlanesIn X. -/
theorem planesIn_of_layersHead (h : Model.Verify.publicOf pol KL lay = .ok X)
    (B : Hd.LayersHeadAt X) : PlanesIn X :=
  planesIn_of_public h (plans_there h B).1 fun g hg => by
    obtain ⟨P, -, -, hP, -⟩ := (plans_there h B).2 g hg
    exact ⟨P, hP⟩

/-- Where publicOf returns X, Hd.LayersHeadAt X holds and scalesHeld returns at X's shape of the
layers and X's scales: LookPub X. -/
theorem lookPub_of_public (h : Model.Verify.publicOf pol KL lay = .ok X) (B : Hd.LayersHeadAt X)
    (hs : scalesHeld (layerShape X.P) X.layers.sc = .ok ()) : LookPub X where
  lay := ⟨_, B.lay⟩
  sw := B.switches
  sc := hs
  groups := B.groups
  p4 := B.p4
  dh := by
    rw [← B.sized.ch]
    rfl
  att := fun g hg => by
    obtain ⟨-, lid, cf, -, hh⟩ := (plans_there h B).2 g hg
    exact ⟨lid, cf, hh⟩
  head := ⟨_, B.head⟩
  JV := by
    have e := (Hd.full_lens (R := runAt X) B.head B.full.lt B.full.V B.full.XL).1
    exact e.trans B.full.V.symm

end Public

section Laws
variable {X : Model.Verify.Public} {i : Cm.Idx} {x : Instance ppref} {T : Tr}

/-- Under LookPub X, MeetsAll X i x T and PlanesLaid X i x T, for g below 12 and all θ and al of
Cb.Gl.E: Cb.Lkp.MidP holds of the joint key vector, the joint table, the public padding and the
planes' bits of the group g of layers, with the keys and the bits read from list 2 g of T. -/
theorem midP_layers (Q : LookPub X) (M : MeetsAll X i x T) (L : PlanesLaid X i x T) {g : ℕ}
    (hg : g < 12) (θ al : Cb.Gl.E) :
    Cb.Lkp.MidP X.y.fo.v X.y.fo.d 5 32 (Ends.G.keyG X.layers g (cellMW (T (2 * g)) i.mat) θ)
      (Ends.G.tabG X.layers θ) (FoNums.pads X.y.fo)
      (fun u j => Ends.G.bitsG X.y (cellMW (T (2 * g)) i.mat) (u * 32 + j)) al := by
  obtain ⟨pc, hy⟩ := Q.lay
  exact lawG_forInG X.layers hy Q.sw g _ _ (M.keysG g hg X.layers.tokv) (L.layers g hg) θ al

/-- Under LookPub X, MeetsAll X i x T and PlanesLaid X i x T, for g below 12 and all θ and al of
Cb.Gl.E: Cb.Lkp.MidP holds of the joint key vector, the joint table, the public padding and the
planes' bits of the attention of group g, with the keys and the bits read from list 2 g + 1 of T. -/
theorem midP_att (Q : LookPub X) (M : MeetsAll X i x T) (L : PlanesLaid X i x T) {g : ℕ}
    (hg : g < 12) (θ al : Cb.Gl.E) :
    Cb.Lkp.MidP (fsAt X g).v (fsAt X g).d 5 32
      (Ends.A.keyA (Hd.shapeA X g) (fsAt X g) (cellZ (T (2 * g + 1))) θ)
      (Ends.A.tabA (fsAt X g) θ) (FoNums.pads (fsAt X g))
      (fun u j => Ends.A.bitsA (Hd.shapeA X g) (fsAt X g) (cellZ (T (2 * g + 1))) (u * 32 + j))
      al := by
  obtain ⟨lid, cf, hs⟩ := Q.att g hg
  exact lawA_forInA hs _ (M.keysA g hg).1 (L.att g hg) θ al

/-- Under LookPub X, MeetsAll X i x T and PlanesLaid X i x T, for all θ and al of Cb.Gl.E:
Cb.Lkp.MidP holds of the joint key vector, the joint table, the public padding and the planes' bits
of the head, with the keys and the bits read from list 24 of T. -/
theorem midP_head (Q : LookPub X) (M : MeetsAll X i x T) (L : PlanesLaid X i x T)
    (θ al : Cb.Gl.E) :
    Cb.Lkp.MidP X.HLy.fs.v X.HLy.fs.d 5 32 (Ends.H.keyH (pubHAt X x) (readH (T 24) i.mat) θ)
      (Ends.H.tabH (pubHAt X x) θ) (FoNums.pads X.HLy.fs)
      (fun u j => Ends.H.bitsH X.hS X.HLy.fs (readH (T 24) i.mat) (u * 32 + j)) al := by
  obtain ⟨tau, hy⟩ := Q.head
  have K := M.keysH (Hd.runReq (runAt X) x) rfl rfl (Hd.reqFits_runReq _ _ x)
  exact lawH (pubHAt X x) hy _ K (fillerIsPad_of_JV (pubHAt X x) hy Q.JV _) L.head θ al

end Laws

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.bNoL
#print axioms OnBytes.HonestTrace.planesOf_layers
#print axioms OnBytes.HonestTrace.planesOf_att
#print axioms OnBytes.HonestTrace.planesOf_head
#print axioms OnBytes.HonestTrace.planesOf_01
#print axioms OnBytes.HonestTrace.trFull_off
#print axioms OnBytes.HonestTrace.trFull_planes_all
#print axioms OnBytes.HonestTrace.inShape_of_test
#print axioms OnBytes.HonestTrace.planesIn_of_public
#print axioms OnBytes.HonestTrace.cellMW_withBG
#print axioms OnBytes.HonestTrace.readH_withBH
#print axioms OnBytes.HonestTrace.cellMW_theTrace
#print axioms OnBytes.HonestTrace.cellZ_theTrace
#print axioms OnBytes.HonestTrace.readH_theTrace
#print axioms OnBytes.HonestTrace.theTrace_outside_layers
#print axioms OnBytes.HonestTrace.theTrace_outside_att
#print axioms OnBytes.HonestTrace.theTrace_outside_head
#print axioms OnBytes.HonestTrace.laidB_theTrace
#print axioms OnBytes.HonestTrace.laidBA_theTrace
#print axioms OnBytes.HonestTrace.laidBH_theTrace
#print axioms OnBytes.HonestTrace.planesLaid_theTrace
#print axioms OnBytes.HonestTrace.plans_there
#print axioms OnBytes.HonestTrace.planesIn_of_layersHead
#print axioms OnBytes.HonestTrace.lookPub_of_public
#print axioms OnBytes.HonestTrace.midP_layers
#print axioms OnBytes.HonestTrace.midP_att
#print axioms OnBytes.HonestTrace.midP_head
