-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/PointCounts.lean: "LIN point": THE TWO SORTS OF LOST POINTS APART, each with
its own count, and what a yes gives at a point that is of neither sort: for whoever counts the key's
sort once and the slot's sort once a slot.

Johnson/Desc/K14/Law/PointGood.lean joins the two sorts into one lost set for ONE statement. For a
batch of N statements that share the key that joined count, taken N times, counts the key's sort N
times over. Here nothing is joined:
  BadO            the slot's sort, of one slot's data (the row weights g, the other vector V) and
                  the matrix: V is not g applied to the matrix, and yet (Dot)'s equation with the
                  matrix holds at the point. It reads no witness and no pin.
  cnt_badO        no more than kCol |K| ^ (kCol - 1) points are of that sort.
  GuardK, cnt_guardK   the key's sort: a property B of the point's high part, WITH A GUARD (B holds
                  of no more than ef values): no more than ef |K| ^ kLo points, whatever B is: so
                  the count holds at every key, also at one of no statement inside the promise.
  VIs.bits        the claim in front with the matrix's columns named by their bits.
  shape1, shape2, shape_hands   the book-keeping in front of and behind the block as two tests on
                  the record; a yes hands the first on to the second.
  point_yes       **what a yes of the chain's own first block gives**: the written round reads as a
                  point psi; "LIN point" has led from the record in front to that behind; and at
                  every witness: if the high part of psi is not bad for the key, then near, RecAll
                  and DotU of the message to come give that the stored table decodes, and (Dot)'s
                  equation with the matrix at psi: so VIs, or psi is of the slot's sort at that
                  witness's other vector.

What is not claimed. No law in the form of a game for N statements is stated here: these are its
parts. cnt_badO COUNTS AT ONE FIXED V; point_yes speaks of each witness's own other vector: WHOEVER
JOINS THE TWO OWES THAT V IS FIXED BEFORE THE POINT IS DRAWN: that all witnesses that the statement
in front pins have one other vector (hdetV in PointGood.lean: a premise there, paid by nobody).
BadKey, Dec and Tab are letters with the premise hgood, as in PointGood.lean (paid at the library's
notions in PointKey.lean and PointKey2.lean). No soundness of a verifier.

-/
import Johnson.Desc.K14.Law.PointGood

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat
open OnBytes.Means (Words)
open VerifiableInference.Desc (Grows Block noDigest)
open VerifiableInference.Desc.Sound (Frame Piece)
open Iop.IOR (drawRound)

/-- (Dot)'s equation with the matrix itself, at a point. -/
def DotTrue {K : Type} [Field K] (S : LinShape) (g : Nat → K) (Tab : Nat → Nat → K) (V : Nat → K)
    (psi : Fin S.kCol → K) : Prop :=
  ∑ c ∈ Finset.range (2 ^ S.kCol), eqK (List.ofFn psi) c * V c =
    ∑ y ∈ Finset.range S.matrixRows, g y *
      ∑ c ∈ Finset.range (2 ^ S.kCol), eqK (List.ofFn psi) c * matOf S.kLo Tab y c

/-- **The slot's sort of lost points.** -/
def BadO {K : Type} [Field K] (S : LinShape) (g : Nat → K) (Tab : Nat → Nat → K) (V : Nat → K)
    (psi : Fin S.kCol → K) : Prop :=
  ¬ VIs S g Tab V ∧ DotTrue S g Tab V psi

/-- No more than kCol |K| ^ (kCol - 1) points are of the slot's sort. -/
theorem cnt_badO {K : Type} [Field K] [Fintype K] (S : LinShape) (g : Nat → K)
    (Tab : Nat → Nat → K) (V : Nat → K) :
    cnt (BadO S g Tab V) ≤ S.kCol * Fintype.card K ^ (S.kCol - 1) := by
  by_cases hn : VIs S g Tab V
  · rw [cnt_false fun psi hq => hq.1 hn]
    exact Nat.zero_le _
  · have hgap : ∃ c < 2 ^ S.kCol, V c ≠
        ∑ y ∈ Finset.range S.matrixRows, g y * matOf S.kLo Tab y c := by
      unfold VIs at hn
      push Not at hn
      exact hn
    exact le_trans (cnt_mono fun psi hq => hq.2) (le_trans
      (le_of_eq (@cnt_eq_card_filter _ _ _ fun _ => Classical.propDecidable _))
      (dotTrueCatches S.matrixRows S.kCol (matOf S.kLo Tab) g V hgap))

/-- **The key's sort of lost points, with a guard**: the property B of the point's high part holds
of no more than ef values, and of this point's high part. So the count below asks nothing of B. -/
def GuardK {K : Type} [Finite K] (kLo v ef : Nat) (B : (Fin v → K) → Prop)
    (psi : Fin (kLo + v) → K) : Prop :=
  cnt B ≤ ef ∧ B (gamOf kLo v psi)

/-- No more than ef |K| ^ kLo points are of the key's sort with the guard, WHATEVER B IS. -/
theorem cnt_guardK {K : Type} [Field K] [Fintype K] (kLo v ef : Nat) (B : (Fin v → K) → Prop) :
    cnt (GuardK kLo v ef B) ≤ ef * Fintype.card K ^ kLo := by
  by_cases h : cnt B ≤ ef
  · exact le_trans (cnt_mono fun psi hq => hq.2)
      (le_trans (cnt_high kLo v B) (Nat.mul_le_mul_right _ h))
  · rw [cnt_false fun psi hq => h hq.1]
    exact Nat.zero_le _

/-- The claim in front of "LIN point" with the matrix's columns named by their bits and the sum over
the rows' own type: the form in which the kind that laid (Eval) reads it. -/
theorem VIs.bits {K : Type} [Field K] {S : LinShape} {g : Nat → K} {Tab : Nat → Nat → K}
    {V : Nat → K} (h : VIs S g Tab V) :
    ∀ e < 2 ^ S.kCol, V e = ∑ i : Fin S.matrixRows,
      g i.val * matOf S.kLo Tab i.val (numOf S.kCol (bitsOf S.kCol e)) := by
  intro e he
  rw [numOf_bitsOf _ _ he, h e he,
    Fin.sum_univ_eq_sum_range (fun y => g y * matOf S.kLo Tab y e) S.matrixRows]

/-- The book-keeping in front of "LIN point", as a test: the key fits the stored table's shape. -/
def shape1 (p : Par) (d : St) : Bool := d.loc.key.fits p.S.fold.index

/-- The book-keeping behind "LIN point", as a test: and the point noted has kCol coordinates. -/
def shape2 (p : Par) (d : St) : Bool := shape1 p d && d.loc.psiSh.length == p.S.kCol

variable {W : Type} {F : Frame}

/-- **What a yes of the chain's own first block gives.** -/
theorem point_yes (rg : W → Words GE) (wv : W → Nat → GE) (P : P14)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (g : Nat → GE) (e' : Nat)
    (base : Nat) (d : RDT) {ns a0 : Nat} (hd : SendsDraws (toRD d) ns P.par.S.kCol 0 a0)
    (BadKey : St × F.E.Str → (Fin P.par.S.fold.index.v → GE) → Prop)
    (Tab : St × F.E.Str → Nat → Nat → GE) (Dec : St × F.E.Str → Prop) (e : Nat)
    (a : St × F.E.Str)
    (hgood : ∀ (x : St) (m : Words GE) (gam : Fin P.par.S.fold.index.v → GE),
      ¬ BadKey a gam →
      (gamma P.par.S x.loc).map OnBytes.Model.Reading.gl.val = List.ofFn gam →
      x.loc.key = a.1.loc.key → x.st.codes = a.1.st.codes →
      NearAt OnBytes.Model.Reading.gl P.par x m (tabOf a.2) e' →
      RecAll OnBytes.Model.Reading.gl P.par x m →
      Dec a ∧ UIsFold P.par.S.matrixRows P.par.S.kLo P.par.S.fold.index.v (Tab a) (List.ofFn gam)
        (uOf x.loc m))
    (τ : Tr (uLT (ckP .two) (vecPiece (W := W) (F := F) b1 base d P.par.S.kCol e).ds))
    (b : St × F.E.Str)
    (hout : (vecPiece (W := W) (F := F) b1 base d P.par.S.kCol e).ior.red.out a τ = some b) :
    ∃ τ' : Tr [drawRound (Fin P.par.S.kCol → GE)],
      (vecMaps d P.par.S.kCol).carry.tr τ = some τ' ∧
      (∃ rs, linPoint P.par a.1 rs = some b.1) ∧
      b.1.loc.psiSh.map OnBytes.Model.Reading.gl.val = List.ofFn τ'.2.1 ∧
      ∀ w, ¬ BadKey a (gamOf P.par.S.kLo P.par.S.fold.index.v τ'.2.1) →
        NearAt OnBytes.Model.Reading.gl P.par (withNext P.par b.1) (rg w) (tabOf b.2) e' →
        RecAll OnBytes.Model.Reading.gl P.par (withNext P.par b.1) (rg w) →
        DotUAt P.par.S g (withNext P.par b.1).loc (rg w) (wv w) →
        Dec a ∧ DotTrue P.par.S g (Tab a) (wv w) τ'.2.1 := by
  obtain ⟨hy, gs, hdc⟩ := piece_yes _ a τ b hout
  have k1 := point_of_blocks P b1 b2 b3 b4 b5 b6 b7 b8 hbl _ _ gs _ hdc
  obtain ⟨r, hr, hpsi, hkeyE, hor, hco⟩ := linPoint_inv _ _ _ _ k1
  have ht := piece_tests _ a τ b hout
  simp only [sTests, Bool.and_eq_true] at ht
  have hp : (vecMaps d P.par.S.kCol).pass τ = true := (vecMaps_pass d _ τ).trans ht.1.1
  obtain ⟨m, c, ⟨⟩⟩ := τ
  have hr' : [noDigest (shownAt d m c)] = [r] := hr
  obtain rfl := (List.cons.inj hr').1
  have hsh := drawn_shown hd m c
  have e1 : (withNext P.par b.1).loc.psiSh.map OnBytes.Model.Reading.gl.val =
      List.ofFn (gVec P.par.S.kCol _ (valsOf (toRD d) c)) := by
    show b.1.loc.psiSh.map _ = _
    rw [hpsi]
    exact hsh
  refine ⟨_, (vecMaps d P.par.S.kCol).tr_of_pass (m, c, ()) hp, ⟨_, k1⟩, e1,
    fun w hnb hnear hrec hdot => ?_⟩
  have eg : (gamma P.par.S (withNext P.par b.1).loc).map OnBytes.Model.Reading.gl.val =
      List.ofFn (gamOf P.par.S.kLo P.par.S.fold.index.v
        (gVec P.par.S.kCol _ (valsOf (toRD d) c))) := by
    unfold gamma
    rw [List.map_drop, e1]
    exact drop_ofFn P.par.S.kLo P.par.S.fold.index.v _
  have et : ((withNext P.par b.1).loc.psiSh.take P.par.S.kLo).map
      OnBytes.Model.Reading.gl.val = List.ofFn (loOf P.par.S.kLo P.par.S.fold.index.v
        (gVec P.par.S.kCol _ (valsOf (toRD d) c))) := by
    rw [List.map_take, e1]
    exact take_ofFn P.par.S.kLo P.par.S.fold.index.v _
  have eapp : List.ofFn (loOf P.par.S.kLo P.par.S.fold.index.v
        (gVec P.par.S.kCol _ (valsOf (toRD d) c))) ++
      List.ofFn (gamOf P.par.S.kLo P.par.S.fold.index.v
        (gVec P.par.S.kCol _ (valsOf (toRD d) c))) =
      List.ofFn (gVec P.par.S.kCol _ (valsOf (toRD d) c)) := by
    rw [← take_ofFn, ← drop_ofFn]
    exact List.take_append_drop _ _
  rw [hy, tabOf_imp] at hnear
  have hnb' : ¬ BadKey a (gamOf P.par.S.kLo P.par.S.fold.index.v
      (gVec P.par.S.kCol _ (valsOf (toRD d) c))) := hnb
  obtain ⟨hdec, hU⟩ := hgood (withNext P.par b.1) (rg w) _ hnb' eg hkeyE hco hnear hrec
  unfold DotUAt at hdot
  rw [et, e1, ← eapp] at hdot
  have hfin := dotTrue_of P.par.S.matrixRows P.par.S.kLo P.par.S.fold.index.v (Tab a) _ _ g
    (uOf (withNext P.par b.1).loc (rg w)) (wv w) (by simp) hU hdot
  rw [eapp] at hfin
  exact ⟨hdec, hfin⟩

/-- A yes of the chain's own first block hands the first test on to the second. -/
theorem shape_hands (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (base : Nat) (d : RDT) {ns a0 : Nat}
    (hd : SendsDraws (toRD d) ns P.par.S.kCol 0 a0) (e : Nat) (a : St × F.E.Str)
    (τ : Tr (uLT (ckP .two) (vecPiece (W := W) (F := F) b1 base d P.par.S.kCol e).ds))
    (b : St × F.E.Str)
    (hout : (vecPiece (W := W) (F := F) b1 base d P.par.S.kCol e).ior.red.out a τ = some b)
    (h : shape1 P.par a.1 = true) : shape2 P.par b.1 = true := by
  obtain ⟨_, gs, hdc⟩ := piece_yes _ a τ b hout
  have k1 := point_of_blocks P b1 b2 b3 b4 b5 b6 b7 b8 hbl _ _ gs _ hdc
  obtain ⟨r, hr, hpsi, hkeyE, _, _⟩ := linPoint_inv _ _ _ _ k1
  obtain ⟨m, c, ⟨⟩⟩ := τ
  have hr' : [noDigest (shownAt d m c)] = [r] := hr
  obtain rfl := (List.cons.inj hr').1
  have hl := congrArg List.length (drawn_shown hd m c)
  rw [List.length_map, List.length_ofFn, ← hpsi] at hl
  unfold shape2 shape1 at *
  rw [hkeyE, h, hl]
  simp

end Desc.K14.Law
