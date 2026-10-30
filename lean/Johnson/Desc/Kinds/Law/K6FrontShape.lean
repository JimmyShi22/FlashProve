-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6FrontShape.lean: FOUR MORE SENTENCES THAT THE TABLE'S PROMISE IN FRONT OF
THE OUTPUT HEAD'S OWN ROUNDS (border 341 of the full chain) SAYS OF THE VERIFIER'S STATE, AT THE
COMPOSED MEANING mgAll D Mg. Statements and proofs. Beside Law/K6FrontSays.lean and
Law/K6WideFront.lean.

What is said (a: a statement inside the promise at border 341 whose state bears no mark).
  shape_front        the promise's clause on where the chain stands (First.shapeAt), at this place.
  **rows_front**     no count of rows waits: First.Tape.RowsOwed.noneWaits a.1.2.rowsOwed = true.
  **link_front**     a segment is open, and its number is 24.
  **linkArr_front**  and its list of arrays is the public one; and nothing is heard yet of the
      lookup argument on the digits (both: the public item linkFresh 24).
  **oneRow_front**   the open ledger's array of the reads is there, has one row, and has just
      Wp.H.nU.getD 2 0 columns (under hX and hB, as in Law/K6WideFront.lean).

Every letter under "there is": L (pinned by the state's reader link?); G (by fork?); tr (by the
ledger's list of arrays at the number of the reads' array).
What it does not say. That any statement is inside the promise. The full chain alone. Nothing on
soundness.
-/
import Johnson.Desc.Kinds.Law.K6WideFront

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law.AtFold

open OnBytes
open OnBytes.Maker OnBytes.Flat Johnson.Pack
open VerifiableInference.OnPublicFiles.Flat (GE)
open VerifiableInference.Desc.First (S Meaning pubFit)
open VerifiableInference.Desc.First.FillSent (treesAt looksOf treeLook)
open VerifiableInference.Desc.Sound (Frame MsgT onQ linksFull MgData mgAll)

variable {Xi P Tok : Type} {rows cols nR : ℕ} {Wp : OnBytes.Model.Verify.Public}
  (D : MgData Xi P Tok rows cols nR Wp)
  (Mg : Meaning P (Wit (Fin rows → Fin cols → GE) Tok MsgT)) (Fr : Frame)

set_option quotPrecheck false in
/-- The composed meaning. -/
local notation "MGA" => mgAll D Mg

/-- The driver's list of places, at the full chain. -/
local notation "PS" => First.flatPlacesOf linksFull true

/-- **Where the chain stands.** -/
theorem shape_front (hp : PS[341]? = some placeK6) (a : (P × S) × Fr.E.Str)
    (ha : onQ (Fr := Fr) D.N MGA linksFull PS (fun a => a) 341 a) (hm : a.1.2.failed = none) :
    First.shapeAt linksFull (some placeK6) a.1.2 = true := by
  have h := (Sound.onParts_of_on D.N MGA linksFull PS (fun a => a) 341 a ha hm).shape
  rw [hp] at h
  exact h

/-- **No count of rows waits.** -/
theorem rows_front (hp : PS[341]? = some placeK6) (a : (P × S) × Fr.E.Str)
    (ha : onQ (Fr := Fr) D.N MGA linksFull PS (fun a => a) 341 a) (hm : a.1.2.failed = none) :
    First.Tape.RowsOwed.noneWaits a.1.2.rowsOwed = true := by
  have h := shape_front D Mg Fr hp a ha hm
  unfold First.shapeAt at h
  simp only [Bool.and_eq_true, Bool.or_eq_true] at h
  have hw : First.mayWait linksFull placeK6 = false := by decide
  have h1 : a.1.2.noneWaits = true := h.1.2.resolve_right (by rw [hw]; exact Bool.false_ne_true)
  unfold First.S.noneWaits at h1
  cases e : a.1.2.rowsOwed with
  | none => rfl
  | some r =>
    rw [e] at h1
    exact h1

/-- **A segment is open, and its number is 24.** -/
theorem link_front (hfit : pubFit (MGA).more linksFull PS = true) (hp : PS[341]? = some placeK6)
    (a : (P × S) × Fr.E.Str) (ha : onQ (Fr := Fr) D.N MGA linksFull PS (fun a => a) 341 a)
    (hm : a.1.2.failed = none) : ∃ L, a.1.2.link? = some L ∧ L.link = 24 := by
  obtain ⟨L, hL, _⟩ := any_some (sentIs_front D Mg Fr hfit hp a ha hm)
  have h := shape_front D Mg Fr hp a ha hm
  unfold First.shapeAt at h
  simp only [Bool.and_eq_true] at h
  have h2 := h.2
  rw [hL] at h2
  have h3 : (placeK6.link == some L.link) = true := h2
  have h4 : (some 24 : Option ℕ) = some L.link := eq_of_beq h3
  exact ⟨L, hL, (Option.some.inj h4).symm⟩

/-- **The open segment's number and its list of arrays; and nothing is heard yet of the lookup
argument on the digits.** -/
theorem linkArr_front (hfit : pubFit (MGA).more linksFull PS = true)
    (hp : PS[341]? = some placeK6) (a : (P × S) × Fr.E.Str)
    (ha : onQ (Fr := Fr) D.N MGA linksFull PS (fun a => a) 341 a) (hm : a.1.2.failed = none) :
    (∃ L, a.1.2.link? = some L ∧ L.link = 24 ∧ L.arrayOf = D.sent.arrayOf.getD 24 #[]) ∧
      (a.1.2.tl?.bind (·.heard)).isNone = true := by
  obtain ⟨L, hL, h24⟩ := link_front D Mg Fr hfit hp a ha hm
  have hfr := fresh_front D Mg Fr hfit hp a ha hm
  unfold VerifiableInference.OnPublicFiles.linkFreshB at hfr
  rw [Bool.and_eq_true, hL] at hfr
  exact ⟨⟨L, hL, h24, eq_of_beq hfr.2⟩, hfr.1⟩

/-- **The array of the reads: one row, and the planned number of columns.** -/
theorem oneRow_front {pol KL : ByteArray} {lay : Option ByteArray}
    (hX : OnBytes.Model.Verify.publicOf pol KL lay = .ok Wp)
    (hB : treesAt D.built 24 = looksOf Wp.H.Fp)
    (hfit : pubFit (MGA).more linksFull PS = true) (hp : PS[341]? = some placeK6)
    (a : (P × S) × Fr.E.Str) (ha : onQ (Fr := Fr) D.N MGA linksFull PS (fun a => a) 341 a)
    (hm : a.1.2.failed = none) :
    ∃ G tr, a.1.2.fork? = some G ∧ G.trees[readsOf Wp]? = some tr ∧ tr.R = 1 ∧
      tr.K = Wp.H.nU.getD 2 0 := by
  obtain ⟨G, hG, e⟩ := any_some (treesAre_front D Mg Fr hfit hp a ha hm)
  have e1 : G.trees.toList.map treeLook = looksOf Wp.H.Fp :=
    (of_decide_eq_true e).trans hB
  obtain ⟨hpos, hK, hR, _⟩ := ReadsArray.public_array hX
  have h0 : readsOf Wp = 0 := by
    have h3 : Wp.H.tl.ix.U.getD 2 none = some 0 := ReadsNamed.public_third hX
    unfold readsOf
    rw [h3]
    rfl
  have hT : Wp.H.Fp.trees[0]? = some (Wp.H.Fp.trees.getD 0 {}) := by
    rw [Array.getElem?_eq_getElem hpos, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem hpos]
    rfl
  have e0 : (G.trees[0]?).map treeLook =
      (Wp.H.Fp.trees[0]?).map fun T => (T.R, T.K, T.rows.toList.map fun r => (r.L0, T.K)) := by
    have e2 := congrArg (fun l => l[0]?) e1
    unfold looksOf at e2
    simpa only [List.getElem?_map, Array.getElem?_toList] using e2
  rw [hT] at e0
  rw [h0]
  cases hg : G.trees[0]? with
  | none =>
    rw [hg] at e0
    cases e0
  | some tr =>
    rw [hg] at e0
    have e3 := Option.some.inj e0
    exact ⟨G, tr, hG, hg, (congrArg (fun x => x.1) e3).trans hR,
      (congrArg (fun x => x.2.1) e3).trans hK⟩

end VerifiableInference.Desc.Kinds.Head.Law.AtFold

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtFold.rows_front
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtFold.link_front
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtFold.linkArr_front
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtFold.oneRow_front
