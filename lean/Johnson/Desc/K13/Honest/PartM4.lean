-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Honest/PartM4.lean: kind K13's sub-protocol behind W's commitment (`rowsB`,
Johnson/Desc/K13/Kind.lean) AT EVERY LENS: when its decision accepts, and what the shape of the part
behind is. Definitions with code, and statements with their proofs.

The kind's sub-protocols are written over a lens X into a state of any type T (`Lens`, Kind.lean):
they read the structure `Part` that `X.get?` yields and write a `Part` back with `X.set`. So `rowsB`
at X is one text on the `Part` between the two; the law is stated of that text, once; a lens is an
instance. No law on the lens is asked. Johnson/Desc/K13/Honest/ShapeM4Ready.lean has the law at the
first chain's state of the proof file's IOP and its lens `atS`; its lemmas are called here, at a
state that is made of the part (`stateOfPart`): that state stands in the proofs, in
`sh4_stateOfPart` and in `valsPart_eq`, and in no other statement.
The form of the laws: premises on the part's shape, and the named tests on values: then the text
returns, and the shape behind is a function with code of the shape in front.
Main names:
  `rowsPart`: the text of `rowsB` on the part. `rowsB_is_part`: **at every lens `rowsB` is that text
    between `get?` and `set`.**
  `partSh4`: the part's shape: an `Sh4` (ShapeDefs.lean). ITS FLAG "THE CHAIN STANDS AT ITS END" IS
    THE CONSTANT true: a part does not say where the chain stands. So the first clause of `ready4`
    is idle at every `partSh4`: NO TEST ON THE SHAPE STANDS FOR THE PREMISE `X.get? t = some p`.
  `stepPart`: the update: `step4`, but the count that is owed stays: on the part `rowsB` leaves it;
    the lens `atS` hands it on as "none where none waits".
  `SamePartBut`: what the text leaves of the part: all fields but `lin` and `d`.
  `rowsPart_carries`: wherever the text returns, the shape behind is the update of the shape in
    front, and the other fields stay.
  `rowsPart_returns`: **the law on the shape alone**: the guards `ready4` and the two clauses on
    pads `pads4` accept at the part's shape: then the text returns, whatever the field elements in
    the part. `rowsPart_returns_vals`: the law with the one named test on values (`valsPart`) in the
    stead of the two clauses. `valsPart` has a text of its own on the part's fields; `valsPart_eq`:
    it is `vals4` (ShapeM4Ready.lean) at the state that is made of the part.
  `rowsB_returns_at`, `rowsB_returns_vals_at`: **the two laws at any lens.**

What is not claimed. The converse of a law: the guards are shown to be enough, not needed. That they
accept at any state of a run. Nothing on what `X.get?` yields behind `X.set`: that is a law on the
lens, and it is not asked here. The field `decide` alone is treated: not `Block.step`, not the test
on the plan; where the sub-protocol is laid behind guards, these stand outside. Nothing on W's
commitment. "Accepts" is `Block.decide`'s answer `.ok` and no more. Nothing on soundness or on
hiding.

-/
import Johnson.Desc.K13.Honest.ShapeM4Ready

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Honest
open OnBytes OnBytes.Slice
open OnBytes.Params (LinShape)
open VerifiableInference.Desc.First (S rowOfClaim)
open VerifiableInference.Desc.K13.Law

/-! ## The text on the part -/

/-- **The text of `rowsB` on the part.** -/
def rowsPart (P : Where) (p : Part) : Ans Part := do
  let l ← there "K13.claim-laid" p.lin
  let o ← rows P.lin l.claim p.ids p.d
  pure { p with lin := some o.1, d := o.2 }

/-- **At every lens `rowsB` is that text between `get?` and `set`.** -/
theorem rowsB_is_part {T Cl : Type} (X : Lens T) (P : Where) (t : T) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) :
    (rowsB (Cl := Cl) X P).decide t rs gs =
      (X.part t).bind fun p => (rowsPart P p).map (X.set t) := by
  show (do
    let s ← X.part t
    let l ← there "K13.claim-laid" s.lin
    let o ← rows P.lin l.claim s.ids s.d
    pure (X.set t { s with lin := some o.1, d := o.2 }) : Ans T) = _
  cases X.part t with
  | error e => rfl
  | ok p =>
    show (do
      let l ← there "K13.claim-laid" p.lin
      let o ← rows P.lin l.claim p.ids p.d
      pure (X.set t { p with lin := some o.1, d := o.2 }) : Ans T) = (rowsPart P p).map (X.set t)
    unfold rowsPart
    cases there "K13.claim-laid" p.lin with
    | error e => rfl
    | ok l =>
      show (do
        let o ← rows P.lin l.claim p.ids p.d
        pure (X.set t { p with lin := some o.1, d := o.2 }) : Ans T) =
          (do
            let o ← rows P.lin l.claim p.ids p.d
            pure { p with lin := some o.1, d := o.2 } : Ans Part).map (X.set t)
      cases rows P.lin l.claim p.ids p.d <;> rfl

/-- Where the text returns: a claim is laid, the text `rows` returns, and the part behind is the
part in front with what `rows` lays. -/
theorem rowsPart_ok {P : Where} {p p' : Part} (h : rowsPart P p = .ok p') :
    ∃ (l : LinFirst) (o : LinFirst × St), p.lin = some l ∧
      rows P.lin l.claim p.ids p.d = .ok o ∧ p' = { p with lin := some o.1, d := o.2 } := by
  simp only [rowsPart, Law.bind_ok, Law.there_ok, Law.pure_ok] at h
  obtain ⟨l, hl, o, ho, rfl⟩ := h
  exact ⟨l, o, hl, ho, rfl⟩

/-- And the way back. -/
theorem rowsPart_of {P : Where} {p : Part} {l : LinFirst} {o : LinFirst × St}
    (hl : p.lin = some l) (ho : rows P.lin l.claim p.ids p.d = .ok o) :
    rowsPart P p = .ok { p with lin := some o.1, d := o.2 } := by
  simp only [rowsPart, Law.bind_ok, Law.there_ok, Law.pure_ok]
  exact ⟨l, hl, o, ho, rfl⟩

/-! ## The part's shape, and the update -/

/-- **The part's shape.** The flag "the chain stands at its end" is the constant true: a part does
not say where the chain stands; that the lens yields a part is a premise of its own. -/
def partSh4 (p : Part) : Sh4 := ⟨true, p.ids, p.lin.map laidSh, p.owed, stSh p.d.st⟩

/-- **The update on the part's shape**: `step4`, but the count that is owed stays. -/
def stepPart (Sh : LinShape) (h : Sh4) : Sh4 := { step4 Sh h with owed := h.owed }

/-- What the text leaves of the part. -/
def SamePartBut (p p' : Part) : Prop :=
  p'.owed = p.owed ∧ p'.heard = p.heard ∧ p'.indexMasks = p.indexMasks ∧ p'.pile = p.pile ∧
    p'.msg = p.msg ∧ p'.ids = p.ids

/-- **Wherever the text returns, the shape behind is the update of the shape in front**, and the
other fields stay. -/
theorem rowsPart_carries {P : Where} {p p' : Part} (h : rowsPart P p = .ok p') :
    partSh4 p' = stepPart P.lin (partSh4 p) ∧ SamePartBut p p' := by
  obtain ⟨l, o, hl, ho, rfl⟩ := rowsPart_ok h
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨e1, e2⟩ := rows_sh ho
  show Sh4.mk true p.ids (some (laidSh o.1)) p.owed (stSh o.2.st) = _
  rw [e1, e2]
  unfold stepPart step4 partSh4
  rw [hl]
  by_cases hn : P.lin.ownSplitNeeded = true
  · simp only [Option.map_some, if_pos hn]
    rfl
  · simp only [Option.map_some, if_neg hn]
    rfl

/-! ## The laws on the part -/

/-- A state of the proof file's first chain with the part's fields laid in: a device of the proofs
below, through which the lemmas of ShapeM4Ready.lean are called. -/
def stateOfPart (p : Part) : S :=
  { S.blank with st := p.d.st, rowsOwed := p.owed, here := .mem ⟨p.msg, p.ids, p.lin⟩ }

theorem sh4_stateOfPart (p : Part) : sh4 (stateOfPart p) = partSh4 p := rfl

/-- **The one named test on values**, on the part: the row that is made, as (Eval) is, of the row
that the library reads off the part's claim has the coefficient 0 at every place of every message's
pad. It reads field elements of the part: the claim's point and its masks' coefficients. -/
def valsPart (Sh : LinShape) (p : Part) : Bool :=
  match p.lin with
  | some l =>
    (List.range p.d.st.oracles.size).all fun o =>
      (((p.d.st.oracles[o]?).map (·.pad)).getD []).all fun q =>
        VerifiableInference.Desc.Own.allZero
          ((evalOf (rowOfClaim l.claim) ((p.ids[0]?).getD noId)
            (linLayW p.d.st.codes Sh)).coefficient o q.1 q.2)
  | none => false

/-- It is `vals4` (ShapeM4Ready.lean) at the state that is made of the part. -/
theorem valsPart_eq (Sh : LinShape) (p : Part) : valsPart Sh p = vals4 Sh (stateOfPart p) := rfl

/-- From `SentAtM4` at the part's fields to the text's return. -/
theorem rowsPart_of_sent {P : Where} {p : Part} {l : LinFirst} {row : TensorRow} {w : ℕ}
    (hl : p.lin = some l) (hrow : l.claim = memberClaim row)
    (H : SentAtM4 P.lin row p.ids p.d.st w) : ∃ p', rowsPart P p = .ok p' := by
  obtain ⟨o, ho, _⟩ := rows_accepts (d := p.d) H
  exact ⟨_, rowsPart_of hl (by rw [hrow]; exact ho)⟩

/-- **THE LAW ON THE SHAPE ALONE**: the guards and the two clauses on pads accept at the part's
shape: then the text returns, whatever the field elements in the part; the shape behind is the
update of the shape in front; the other fields stay. -/
theorem rowsPart_returns {P : Where} {p : Part} (h : ready4 P.lin (partSh4 p) = true)
    (hq : pads4 P.lin (partSh4 p) = true) :
    ∃ p', rowsPart P p = .ok p' ∧ partSh4 p' = stepPart P.lin (partSh4 p) ∧ SamePartBut p p' := by
  have h' : ready4 P.lin (sh4 (stateOfPart p)) = true := h
  have hq' : pads4 P.lin (sh4 (stateOfPart p)) = true := hq
  obtain ⟨a, l, hs, hl⟩ := laid_of_ready h'
  obtain rfl : (⟨p.msg, p.ids, p.lin⟩ : First.MemOwn) = a := First.Here.mem.inj hs
  obtain ⟨hrow, H⟩ := sent_of_ready hs hl h' (pad_of_pads hs hl h' hq')
  obtain ⟨p', hp'⟩ := rowsPart_of_sent (P := P) (p := p) hl hrow H
  exact ⟨p', hp', rowsPart_carries hp'⟩

/-- **THE LAW WITH THE TEST ON VALUES**: the guards accept at the part's shape, the named test on
values passes at the part: the same conclusion. -/
theorem rowsPart_returns_vals {P : Where} {p : Part} (h : ready4 P.lin (partSh4 p) = true)
    (hv : valsPart P.lin p = true) :
    ∃ p', rowsPart P p = .ok p' ∧ partSh4 p' = stepPart P.lin (partSh4 p) ∧ SamePartBut p p' := by
  have h' : ready4 P.lin (sh4 (stateOfPart p)) = true := h
  obtain ⟨a, l, hs, hl⟩ := laid_of_ready h'
  obtain rfl : (⟨p.msg, p.ids, p.lin⟩ : First.MemOwn) = a := First.Here.mem.inj hs
  have hv' : vals4 P.lin (stateOfPart p) = true := (valsPart_eq P.lin p).symm.trans hv
  obtain ⟨hrow, H⟩ := sent_of_ready hs hl h' (pad_of_vals hs hl hv')
  obtain ⟨p', hp'⟩ := rowsPart_of_sent (P := P) (p := p) hl hrow H
  exact ⟨p', hp', rowsPart_carries hp'⟩

/-! ## At any lens -/

/-- From a return of the text to the decision's acceptance, at any lens. -/
theorem rowsB_of_part {T Cl : Type} (X : Lens T) (P : Where) {t : T} {p p' : Part}
    (hp : X.get? t = some p) (h : rowsPart P p = .ok p') (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) :
    (rowsB (Cl := Cl) X P).decide t rs gs = .ok (X.set t p') := by
  have e : X.part t = .ok p := by
    unfold Lens.part
    rw [hp]
    rfl
  rw [rowsB_is_part, e]
  show (rowsPart P p).map (X.set t) = _
  rw [h]
  rfl

/-- **THE LAW ON THE SHAPE ALONE, AT ANY LENS.** -/
theorem rowsB_returns_at {T Cl : Type} (X : Lens T) (P : Where) {t : T} {p : Part}
    (hp : X.get? t = some p) (h : ready4 P.lin (partSh4 p) = true)
    (hq : pads4 P.lin (partSh4 p) = true) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) :
    ∃ p', (rowsB (Cl := Cl) X P).decide t rs gs = .ok (X.set t p') ∧
      partSh4 p' = stepPart P.lin (partSh4 p) ∧ SamePartBut p p' := by
  obtain ⟨p', h1, h2⟩ := rowsPart_returns h hq
  exact ⟨p', rowsB_of_part X P hp h1 rs gs, h2⟩

/-- **THE LAW WITH THE TEST ON VALUES, AT ANY LENS.** -/
theorem rowsB_returns_vals_at {T Cl : Type} (X : Lens T) (P : Where) {t : T} {p : Part}
    (hp : X.get? t = some p) (h : ready4 P.lin (partSh4 p) = true)
    (hv : valsPart P.lin p = true) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) :
    ∃ p', (rowsB (Cl := Cl) X P).decide t rs gs = .ok (X.set t p') ∧
      partSh4 p' = stepPart P.lin (partSh4 p) ∧ SamePartBut p p' := by
  obtain ⟨p', h1, h2⟩ := rowsPart_returns_vals h hv
  exact ⟨p', rowsB_of_part X P hp h1 rs gs, h2⟩

/-- **Wherever the decision accepts, at any lens**: the state behind is `X.set` of a part whose
shape is the update of the shape of the part in front. -/
theorem rowsB_carries_at {T Cl : Type} (X : Lens T) (P : Where) {t t' : T} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : (rowsB (Cl := Cl) X P).decide t rs gs = .ok t') :
    ∃ p p', X.get? t = some p ∧ t' = X.set t p' ∧ rowsPart P p = .ok p' ∧
      partSh4 p' = stepPart P.lin (partSh4 p) ∧ SamePartBut p p' := by
  obtain ⟨p, l, o, hp, hl, ho, rfl⟩ := rowsB_ok X P h
  have h1 := rowsPart_of (P := P) hl ho
  exact ⟨p, _, hp, rfl, h1, rowsPart_carries h1⟩

end VerifiableInference.Desc.K13.Honest

#print axioms VerifiableInference.Desc.K13.Honest.rowsB_is_part
#print axioms VerifiableInference.Desc.K13.Honest.rowsPart_ok
#print axioms VerifiableInference.Desc.K13.Honest.rowsPart_of
#print axioms VerifiableInference.Desc.K13.Honest.rowsPart_carries
#print axioms VerifiableInference.Desc.K13.Honest.sh4_stateOfPart
#print axioms VerifiableInference.Desc.K13.Honest.valsPart_eq
#print axioms VerifiableInference.Desc.K13.Honest.rowsPart_of_sent
#print axioms VerifiableInference.Desc.K13.Honest.rowsPart_returns
#print axioms VerifiableInference.Desc.K13.Honest.rowsPart_returns_vals
#print axioms VerifiableInference.Desc.K13.Honest.rowsB_of_part
#print axioms VerifiableInference.Desc.K13.Honest.rowsB_returns_at
#print axioms VerifiableInference.Desc.K13.Honest.rowsB_returns_vals_at
#print axioms VerifiableInference.Desc.K13.Honest.rowsB_carries_at
