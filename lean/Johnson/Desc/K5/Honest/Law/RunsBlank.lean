-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/RunsBlank.lean: THE WAYS BACK FROM THREE SHAPES TO VALUES OF THE TYPES
THAT AN ATTENTION SEGMENT's RUNS OF CLAIMS READ: the same numbers, flags and marks; zeros of these
sizes. As the ways back of Johnson/Desc/First/Shape/Tail.lean (AffSh.blank, HeardAll.blank).
Definitions, and statements with their proofs.

Main names:
  `sumBlank`, `sumSh_blank`   a masked sumcheck's hearing
  `heard5Blank`, `heard5Sh_blank`   what an attention link's own rounds hand on
  `ledRowBlank`, `ledTreeBlank`, `ledBlank`   the ledger
  `led_got`, `led_sized`, `led_K`, `fork_K`, `led_owed`   what the runs read of the blank ledger is
    what the shape says
  `look_zk`   the blank of what the lookup returned has key points of the shape's lengths

Limits. A variable of a sumcheck comes back plain, whatever it was: the shape keeps its degree
alone. A name of an owed claim comes back empty. An array comes back without the mark that its
commitment was received, whatever the shape says; of the ledger only the statements named above are
shown. No statement says that a shape comes from a state.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.First.Shape.AttOwn
import Johnson.Desc.First.Shape.Tail

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Honest
open OnBytes OnBytes.Model
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Shape (AffSh affSh affSh_blank SumSh sumSh Heard5Sh heard5Sh
  RowSh TreeSh LedSh ledSh HeardAll)

/-- Zeros. -/
def zerosOf (n : Nat) : Array E := Array.replicate n zeroE

theorem zerosOf_size (n : Nat) : (zerosOf n).size = n := Array.size_replicate

/-! ## 1 A sumcheck's hearing -/

/-- **The way back.** -/
def sumBlank (s : SumSh) : MaskedSum.Heard :=
  { start := s.start.blank, target := zeroE, eps := zeroE, claim := zeroE, first := s.first
    vars := s.degrees.map MaskedSum.Var.plain, r := List.replicate s.r zeroE, sEnd := s.sEnd }

theorem sumSh_blank (s : SumSh) : sumSh (sumBlank s) = s := by
  obtain ⟨a, f, d, r, e⟩ := s
  show SumSh.mk (affSh (AffSh.blank a)) f ((d.map MaskedSum.Var.plain).map (·.d))
    (List.replicate r zeroE).length e = _
  rw [affSh_blank, List.map_map, List.length_replicate]
  have : (fun v : MaskedSum.Var => v.d) ∘ MaskedSum.Var.plain = id := rfl
  rw [this, List.map_id]

/-! ## 2 What the link's own rounds hand on -/

/-- **The way back.** -/
def heard5Blank (H : Heard5Sh) : P.Heard :=
  { remainders := H.remainders.toArray
    scores := (H.scores.map fun o => (o.1, sumBlank o.2)).toArray
    five := H.five, bits := H.bits, two := H.two, division := sumBlank H.division
    gam := zerosOf H.gam, values := H.values, below := sumBlank H.below, on := sumBlank H.on
    point := zerosOf H.point, maxima := H.maxima, om := zerosOf H.om
    atIndex := sumBlank H.atIndex, om' := zerosOf H.om', key := sumBlank H.key
    om'' := zerosOf H.om'', cells := sumBlank H.cells }

theorem heard5Sh_blank (H : Heard5Sh) : heard5Sh (heard5Blank H) = H := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18⟩ := H
  show Heard5Sh.mk a1 ((a2.map fun o => (o.1, sumBlank o.2)).map fun o => (o.1, sumSh o.2)) a3 a4 a5
    (sumSh (sumBlank a6)) (zerosOf a7).size a8 (sumSh (sumBlank a9)) (sumSh (sumBlank a10))
    (zerosOf a11).size a12 (zerosOf a13).size (sumSh (sumBlank a14)) (zerosOf a15).size
    (sumSh (sumBlank a16)) (zerosOf a17).size (sumSh (sumBlank a18)) = _
  have e2 : (a2.map fun o => (o.1, sumBlank o.2)).map (fun o => (o.1, sumSh o.2)) = a2 := by
    rw [List.map_map]
    refine (List.map_congr_left fun o _ => ?_).trans (List.map_id a2)
    show (o.1, sumSh (sumBlank o.2)) = o
    rw [sumSh_blank]
  rw [e2]
  simp only [sumSh_blank, zerosOf_size]

/-! ## 3 The ledger -/

def ledRowBlank (r : RowSh) : HRow :=
  { coef := zerosOf r.coef, L := zerosOf r.entries, L0 := r.col0, rowForm := r.form
    rowOnes := r.ones, rowFirst := r.first }

def ledTreeBlank (T : TreeSh) : HTree :=
  { name := T.name, kind := if T.symbols then .symbols else .table, R := T.R, K := T.K
    rows := (T.rows.map ledRowBlank).toArray }

/-- **The way back.** -/
def ledBlank (L : LedSh) : Fork :=
  { ns := L.ns, vp := zerosOf L.shown, mf := zerosOf L.factors, gotF := L.got.toArray
    owed := (L.owed.map fun b => ({ what := "", added := b } : Owed)).toArray
    planClaimsF := L.planClaims, trees := (L.trees.map ledTreeBlank).toArray, next := L.next
    LS := zerosOf L.coefs, nClaim := L.claims, thetaDrawnF := L.drawn, kapMapF := L.handed.toArray
    doorShutF := L.shut }

/-- The marks. -/
theorem led_got (L : LedSh) : (ledSh (ledBlank L)).got = L.got := rfl

/-- The three sizes and the number of slots. -/
theorem led_sized (L : LedSh) :
    (ledSh (ledBlank L)).ns = L.ns ∧ (ledSh (ledBlank L)).shown = L.shown ∧
      (ledSh (ledBlank L)).factors = L.factors :=
  ⟨rfl, zerosOf_size _, zerosOf_size _⟩

/-- An array's number of columns. -/
theorem led_K (L : LedSh) (i : Nat) :
    ((ledBlank L).trees[i]?).map (·.K) = (L.trees[i]?).map TreeSh.K := by
  show (((L.trees.map ledTreeBlank).toArray)[i]?).map (·.K) = _
  rw [List.getElem?_toArray, List.getElem?_map]
  cases L.trees[i]? <;> rfl

/-- So at a ledger. -/
theorem fork_K (F : Fork) (i : Nat) :
    (F.trees[i]?).map (·.K) = ((ledSh F).trees[i]?).map TreeSh.K := by
  show _ = ((F.trees.toList.map VerifiableInference.Desc.First.Shape.treeSh)[i]?).map TreeSh.K
  rw [List.getElem?_map, Array.getElem?_toList]
  cases F.trees[i]? <;> rfl

/-- The owed claims' marks. -/
theorem led_owed (L : LedSh) : (ledSh (ledBlank L)).owed = L.owed := by
  show ((L.owed.map fun b => ({ what := "", added := b } : Owed)).map (·.added)) = _
  rw [List.map_map]
  exact List.map_id _

/-! ## 4 What the lookup returned -/

/-- The blank's key points have the shape's lengths. -/
theorem look_zk (K : HeardAll) : K.blank.zk.toList.map (·.size) = K.zk := by
  show ((K.zk.map fun n => Array.replicate n zeroE).map (·.size)) = _
  rw [List.map_map]
  have : ((fun z : Array E => z.size) ∘ fun n => Array.replicate n zeroE) = id := by
    funext n
    exact Array.size_replicate
  rw [this, List.map_id]

end H2K5.Honest

#print axioms H2K5.Honest.zerosOf_size
#print axioms H2K5.Honest.sumSh_blank
#print axioms H2K5.Honest.heard5Sh_blank
#print axioms H2K5.Honest.led_got
#print axioms H2K5.Honest.led_sized
#print axioms H2K5.Honest.led_K
#print axioms H2K5.Honest.fork_K
#print axioms H2K5.Honest.led_owed
#print axioms H2K5.Honest.look_zk
