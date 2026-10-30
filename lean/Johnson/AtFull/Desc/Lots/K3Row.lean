-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Desc/Lots/K3Row.lean: THE LOT OF THE KIND "LOOKUP" (K3Lot.lot): ITS ROW: UNDER
HYPOTHESES BY FIELD ON WHAT THE LOT READS OF THE PUBLIC PART Z, ITS FIFTY SUB-PROTOCOLS' SKELETONS
ARE THE WRITTEN ONES. Definitions with code; theorems. No scope, no head, no opening is spent.
  `viewOf strp x`: what a skeleton reads of a lookup's place: name · link · the calls (their tables
    taken out where strp) · the numbers of padding keys · the cap · the first slot · the number of
    slots · the planes' rows. `viewW i d`: the written one.
  `Reads Z`: THE HYPOTHESES, BY FIELD.
  `num_at`, `piece_at`, `sk_at`.
  `k3_row_at`: **((K3Lot.lot Z).blocks G).map skel = k3RowsW**. (The left side is the field blocks
    of another file's `lotSk G (K3Lot.lot Z)`, Johnson/Desc/ProofFile/Law/Skel/SkelFaults.lean, by
    that definition's text.)
THE ONE PREMISE THAT IS NO EQUATION WITH A WRITTEN VALUE: at the 25 lookups on the calls: "every
call of the place passes the test on a call" (`callOk`): three calls of each such place bear a table
of 65,536 rows, which that test reads whole and no written value can hold. Behind it nothing of a
skeleton reads a table (K3Strip.lean).
Limits. Whether any public files meet `Reads` is not said here (a run at the goals' term
VerifierAndGoals.storedPublicFiles holds each field against the lot's own values: a harness, not shown
here). Nothing on soundness.

-/
import Johnson.AtFull.Desc.Lots.K3NumC
import Johnson.AtFull.Desc.Lots.K3NumD

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Lots.K3
open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.K3 (pieceAt isHead quietAt)
open VerifiableInference.Desc.First.Look (P lookAt placeAt beforeAt laidAt padKeyAt callOk)
open Johnson.AtFull.ProofRows.K3 (strip)
open ProofFile.Sk (Skel skel)

/-- What a skeleton reads of a lookup's place. -/
def viewOf (strp : Bool) (x : First.Look.Place) :
    String × Nat × Array Call × Array Nat × Nat × Nat × Nat × Nat :=
  (x.name, x.link, if strp then x.calls.map strip else x.calls, x.pub, x.lid, x.F.next, x.ns, x.lm)

/-- The written one. -/
def viewW (i : Nat) (d : Bool) : String × Nat × Array Call × Array Nat × Nat × Nat × Nat × Nat :=
  (nameW i d, i, callsW (sortOf i) d, pubW (sortOf i) d, 28, firstW (sortOf i) d, nsW (sortOf i),
    lmW (sortOf i) d)

/-- **THE HYPOTHESES, BY FIELD OF WHAT THE LOT READS.** -/
structure Reads (Z : ProofFile.Pub) : Prop where
  links : Z.first.shape.link.length = 25
  p4 : Z.p.X.p4 = true
  groups : Z.p.X.NGr = 12
  setting : Params.settingOf Z.p.X.P.frame = setW
  calls : ∀ i < 25, ∃ x, lookAt Z.p.X i false = some x ∧ viewOf true x = viewW i false ∧
    x.calls.all callOk = true
  digits : ∀ i < 25, ∃ x, lookAt Z.p.X i true = some x ∧ viewOf false x = viewW i true
  before : ∀ i < 25, ∀ d, beforeAt Z.first.codes Z.first.shape i d = some (beforeW i d)
  laid : ∀ i < 25, ∀ d, laidAt Z.p.X i d = some (pubW (sortOf i) d)
  key : ∀ i < 25, ∀ d, padKeyAt Z.p.X i d = some true
  quiet : ∀ i < 25, ∀ d, (quietAt Z.p.X i d).isSome = quietW i d
  caller : ∀ i < 25, (K3Lot.readersAt Z.p.X i).isSome = callerW i

theorem num_at (i : Nat) (d : Bool) :
    numOf (coreW (sortOf i) d) (pubW (sortOf i) d) = (nW (sortOf i) d, true) := by
  unfold sortOf
  split
  · cases d
    · exact num_c3
    · exact num_d3
  · split
    · cases d
      · exact num_c1
      · exact num_d1
    · split
      · cases d
        · exact num_c0
        · exact num_d0
      · cases d
        · exact num_c2
        · exact num_d2

theorem piece_at {X : Verify.Public} (h4 : X.p4 = true) (hN : X.NGr = 12) (i : Nat) (d : Bool) :
    pieceAt X i d = pieceW i d := by
  unfold pieceAt isHead pieceW
  rw [h4, hN]
  rfl

/-- The skeleton of the kind's own sub-protocol, of name, link and the two numbers. -/
theorem skOwn_num (p : P) (piece : Nat) (sent : List (Nat × Nat)) (laid : Array Nat) (key : Bool) :
    skOwn p piece sent
        (K3.planOk (S := First.S) (Cl := Claim) p laid [] && K3.Law.fitsVia p && key) =
      { name := p.name, place := ⟨1, some p.link, piece, .K3⟩, nRounds := (numOf p laid).1
        nOracles := (numOf p laid).1, told := [], before := sent
        planOk := (numOf p laid).2 && key, claims := ["objects", "guests"], after := [] } := rfl

/-- The two numbers read neither name nor link. -/
theorem numOf_core (p : P) (laid : Array Nat) :
    numOf p laid =
      numOf
        { name := "", set := p.set, link := 0, digits := false, calls := p.calls, pub := p.pub
          lid := p.lid, first := p.first, ns := p.ns, lm := p.lm } laid := rfl

/-- **One row.** -/
theorem sk_at {Z : ProofFile.Pub} (R : Reads Z) {i : Nat} (hi : i < 25) (d : Bool) :
    skAt Z.p.X Z.first.codes Z.first.shape (K3Lot.readersAt Z.p.X i).isSome i d =
      some (rowW i d) := by
  have key : ∃ p : P, placeAt Z.p.X i d = some p ∧ p.name = nameW i d ∧ p.link = i ∧
      ∀ sent k, skOwn p (pieceW i d) sent
        (K3.planOk (S := First.S) (Cl := Claim) p (pubW (sortOf i) d) [] && K3.Law.fitsVia p && k) =
        { name := nameW i d, place := ⟨1, some i, pieceW i d, .K3⟩, nRounds := nW (sortOf i) d
          nOracles := nW (sortOf i) d, told := [], before := sent, planOk := k
          claims := ["objects", "guests"], after := [] } := by
    cases d with
    | false =>
      obtain ⟨x, hx, hv, hOk⟩ := R.calls i hi
      obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ :
          x.name = nameW i false ∧ x.link = i ∧ x.calls.map strip = callsW (sortOf i) false ∧
          x.pub = pubW (sortOf i) false ∧ x.lid = 28 ∧ x.F.next = firstW (sortOf i) false ∧
          x.ns = nsW (sortOf i) ∧ x.lm = lmW (sortOf i) false := by
        simpa [viewOf, viewW, Prod.mk.injEq] using hv
      refine ⟨P.ofPlace (Params.settingOf Z.p.X.P.frame) false x, ?_, e1, e2, fun sent k => ?_⟩
      · unfold placeAt
        rw [hx]
        rfl
      · rw [skOwn_strip (p := P.ofPlace (Params.settingOf Z.p.X.P.frame) false x) hOk, skOwn_num,
          numOf_core]
        show ({ name := x.name, place := ⟨1, some x.link, pieceW i false, .K3⟩
                nRounds := (numOf ⟨"", Params.settingOf Z.p.X.P.frame, 0, false, x.calls.map strip,
                  x.pub, x.lid, x.F.next, x.ns, x.lm⟩ (pubW (sortOf i) false)).1
                nOracles := (numOf ⟨"", Params.settingOf Z.p.X.P.frame, 0, false,
                  x.calls.map strip, x.pub, x.lid, x.F.next, x.ns, x.lm⟩ (pubW (sortOf i) false)).1
                told := [], before := sent
                planOk := (numOf ⟨"", Params.settingOf Z.p.X.P.frame, 0, false, x.calls.map strip,
                  x.pub, x.lid, x.F.next, x.ns, x.lm⟩ (pubW (sortOf i) false)).2 && k
                claims := ["objects", "guests"], after := [] } : Skel) = _
        rw [R.setting, e1, e2, e3, e4, e5, e6, e7, e8]
        show ({ name := nameW i false, place := ⟨1, some i, pieceW i false, .K3⟩
                nRounds := (numOf (coreW (sortOf i) false) (pubW (sortOf i) false)).1
                nOracles := (numOf (coreW (sortOf i) false) (pubW (sortOf i) false)).1
                told := [], before := sent
                planOk := (numOf (coreW (sortOf i) false) (pubW (sortOf i) false)).2 && k
                claims := ["objects", "guests"], after := [] } : Skel) = _
        rw [num_at]
        simp
    | true =>
      obtain ⟨x, hx, hv⟩ := R.digits i hi
      obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ :
          x.name = nameW i true ∧ x.link = i ∧ x.calls = callsW (sortOf i) true ∧
          x.pub = pubW (sortOf i) true ∧ x.lid = 28 ∧ x.F.next = firstW (sortOf i) true ∧
          x.ns = nsW (sortOf i) ∧ x.lm = lmW (sortOf i) true := by
        simpa [viewOf, viewW, Prod.mk.injEq] using hv
      refine ⟨P.ofPlace (Params.settingOf Z.p.X.P.frame) true x, ?_, e1, e2, fun sent k => ?_⟩
      · unfold placeAt
        rw [hx]
        rfl
      · rw [skOwn_num, numOf_core]
        show ({ name := x.name, place := ⟨1, some x.link, pieceW i true, .K3⟩
                nRounds := (numOf ⟨"", Params.settingOf Z.p.X.P.frame, 0, false, x.calls,
                  x.pub, x.lid, x.F.next, x.ns, x.lm⟩ (pubW (sortOf i) true)).1
                nOracles := (numOf ⟨"", Params.settingOf Z.p.X.P.frame, 0, false,
                  x.calls, x.pub, x.lid, x.F.next, x.ns, x.lm⟩ (pubW (sortOf i) true)).1
                told := [], before := sent
                planOk := (numOf ⟨"", Params.settingOf Z.p.X.P.frame, 0, false, x.calls,
                  x.pub, x.lid, x.F.next, x.ns, x.lm⟩ (pubW (sortOf i) true)).2 && k
                claims := ["objects", "guests"], after := [] } : Skel) = _
        rw [R.setting, e1, e2, e3, e4, e5, e6, e7, e8]
        show ({ name := nameW i true, place := ⟨1, some i, pieceW i true, .K3⟩
                nRounds := (numOf (coreW (sortOf i) true) (pubW (sortOf i) true)).1
                nOracles := (numOf (coreW (sortOf i) true) (pubW (sortOf i) true)).1
                told := [], before := sent
                planOk := (numOf (coreW (sortOf i) true) (pubW (sortOf i) true)).2 && k
                claims := ["objects", "guests"], after := [] } : Skel) = _
        rw [num_at]
        simp
  obtain ⟨p, hp, -, -, hsk⟩ := key
  unfold skAt
  rw [hp, R.before i hi d, R.laid i hi d, R.key i hi d, R.quiet i hi d, R.caller i hi,
    piece_at R.p4 R.groups]
  show some (dress (quietW i d) (!d && callerW i) i (pieceW i d) (skOwn p (pieceW i d) (beforeW i d)
    (K3.planOk (S := First.S) (Cl := Claim) p (pubW (sortOf i) d) [] && K3.Law.fitsVia p &&
      true))) = _
  rw [hsk]
  rfl

/-- **THE LOT's ROW.** -/
theorem k3_row_at {Z : ProofFile.Pub} (R : Reads Z) (G : ProofFile.Ground) :
    ((K3Lot.lot Z).blocks G).map skel = k3RowsW := by
  rw [lot_skel]
  unfold K3Lot.addresses k3RowsW
  rw [R.links]
  have e : ∀ x ∈ ((List.range 25).flatMap fun i => [false, true].map fun dg =>
      (i, dg, (⟨1, some i, pieceAt Z.p.X i dg, .K3⟩ : VerifiableInference.Desc.Place))),
      skAt Z.p.X Z.first.codes Z.first.shape (K3Lot.readersAt Z.p.X x.1).isSome x.1 x.2.1 =
        some (rowW x.1 x.2.1) := by
    intro x hx
    obtain ⟨i, hi, hx⟩ := List.mem_flatMap.1 hx
    obtain ⟨dg, -, rfl⟩ := List.mem_map.1 hx
    exact sk_at R (List.mem_range.1 hi) dg
  rw [List.filterMap_congr e]
  simp [List.filterMap_flatMap]

end Johnson.AtFull.Lots.K3

#print axioms Johnson.AtFull.Lots.K3.num_at
#print axioms Johnson.AtFull.Lots.K3.piece_at
#print axioms Johnson.AtFull.Lots.K3.sk_at
#print axioms Johnson.AtFull.Lots.K3.k3_row_at
#print axioms Johnson.AtFull.Lots.K3.skOwn_num
#print axioms Johnson.AtFull.Lots.K3.numOf_core
