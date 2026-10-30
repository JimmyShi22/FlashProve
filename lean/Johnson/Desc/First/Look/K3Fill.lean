-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/K3Fill.lean (in two layers: the door's name «frame.liveIs», which
leaves the table's door, has a thin layer of its own): the kind "lookup" (K3): its layer of the
filling of the table of joints' meaning: fillK3 X D : Meaning P W → Meaning P W, for both of a
segment's lookups: pub is the layer's half with code (pubK3,
Johnson/Desc/First/Look/K3FillCode.lean: no Mathlib) over what was there; pubP says what the lookup
on the calls left; every other item and field, the door among them, is left as it was. And
fillK3Live X D: the thin layer: pub at the one name, and the door's liveMore merged into more: it
turns pub and more alone. And, at these terms, for every Mg, the premises of the lookups' row
theorems that speak of pub, pubP or more, as lemmas. No soundness is claimed.

Main names.
  K3Data.of X D: the layer's data out of the public parameters and the plan's data.
  fillK3 X D Mg. fillK3Live X D Mg.
  (i) fillK3_pub: (fillK3 X D Mg).pub = pubK3 (K3Data.of X D) Mg.pub: by the make.
  The bridges, each by rfl: lookInC_is, lookOutC_is, linkFreshC_is, liveIsC_is: the code's four
    Bools are k3LookInAt, k3OnOutAt (K3BoolsAt.lean), linkFreshB (K3CallsKeeps.lean), liveIsB
    (K3LiveIs.lean): the Bools that have run and of which the laws speak.
  (ii) the rows' premises: at fillK3: fLook_fill, fOut_fill (both sorts) · fFresh_fill · fLeft_fill
    · fLeftP_fill, fLeftOnP_fill · at fillK3Live: fLive_fill · hAsk_fill; and the values item by
    item: fill_lookIn, fill_lookOut, fill_linkFresh, fill_left, fill_leftOn, fill_pubP_left,
    fill_pubP_leftOn, fill_more · fill_live, fillLive_more, fillLive_pubP.
  (iii) fill_pub_other, fill_pubP_other, fillLive_other: every other item is left as it was.
Not claimed by these layers: ledger · freeAbove · unheard (the
table's own layer) · look · callerIn (the callers') · formsIn, formsInT, totalIn · inOrder. worth:
K3FillWorth.lean.
Object. No sub-protocol's text: Meaning (Johnson/Desc/First/Borders.lean) at the lookups' own Bools
and items.
User. The table's files' composed term (fillK3); whoever lays the name «frame.liveIs» over it
(fillK3Live); K3At (K3At.lean).
Letters. X (the public parameters), D : Sent (the plan's data), Mg (the layers beneath).
Is it empty? Definitions and equations: no premise. At these terms nothing has run.

Compiled with the whole library.
Limits. The sort of a piece is read off K3.pieceAt X; the table counts 2 + o and 7 + o off its list
of segments: that the two agree is asked where the rows are called.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3FillCode
import Johnson.Desc.First.Look.K3BoolsAt
import Johnson.Desc.First.Look.K3LiveIs
import Johnson.Desc.First.Look.K3CallsKeeps
import Johnson.Desc.First.Look.K3CallsAddress
import Johnson.Desc.First.Look.K3LeftItem

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Look
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (ModelPart Pub More Meaning moreItem shift)
open VerifiableInference.OnPublicFiles (linkFreshB k3LeftItem k3LeftItemAt k3LeftOnItem k3LeftOnItemAt)

/-- The layer's data out of the public parameters and the plan's data. -/
def K3Data.of (X : Verify.Public) (D : Sent) : K3Data :=
  { X := X, shape := D.shape, layout := D.layout, arrayOf := D.arrayOf }

/-- **K3's LAYER OF THE FILLING.** -/
def fillK3 {P W : Type} (X : Verify.Public) (D : Sent) (Mg : Meaning P W) : Meaning P W :=
  { Mg with
    pub := pubK3 (K3Data.of X D) Mg.pub
    pubP := fun q a =>
      match q with
      | .left m => k3LeftItemAt X m a.2
      | .leftOn m => k3LeftOnItemAt X m a.2
      | q => Mg.pubP q a }

/-- **THE THIN LAYER FOR THE DOOR's NAME "frame.liveIs"**: it turns pub and more alone. -/
def fillK3Live {P W : Type} (X : Verify.Public) (D : Sent) (Mg : Meaning P W) : Meaning P W :=
  { Mg with
    pub := pubK3Live (K3Data.of X D) Mg.pub
    more := Mg.more.merge liveMore }

section
variable {P W : Type} (X : Verify.Public) (D : Sent) (Mg : Meaning P W)

/-! ## (i) The layer's pub is its half with code -/

theorem fillK3_pub : (fillK3 X D Mg).pub = pubK3 (K3Data.of X D) Mg.pub := rfl

/-! ## The code's four Bools are the laws' -/

theorem lookInC_is (m : Nat) (dg : Bool) (s : First.S) :
    lookInC (K3Data.of X D) m dg s = k3LookInAt X D m dg s := rfl

theorem lookOutC_is (m : Nat) (dg : Bool) (s : First.S) :
    lookOutC (K3Data.of X D) m dg s = k3OnOutAt X m dg s := rfl

theorem linkFreshC_is (m : Nat) (s : First.S) :
    linkFreshC (K3Data.of X D) m s = linkFreshB (D.arrayOf.getD m #[]) s := rfl

theorem liveIsC_is (s : First.S) : liveIsC (K3Data.of X D) s = liveIsB D s := rfl

/-! ## The sort of a piece -/

theorem sort_digits (m : Nat) : k3SortAt X m (Desc.K3.pieceAt X m true) = some true := by
  simp [k3SortAt]

theorem sort_calls (m : Nat) : k3SortAt X m (Desc.K3.pieceAt X m false) = some false := by
  unfold k3SortAt Desc.K3.pieceAt
  split <;> simp

theorem sort_at (m : Nat) (dg : Bool) : k3SortAt X m (Desc.K3.pieceAt X m dg) = some dg := by
  cases dg
  · exact sort_calls X m
  · exact sort_digits X m

/-! ## The layer's values -/

theorem fill_lookIn (m : Nat) (dg : Bool) (a : P × First.S) :
    (fillK3 X D Mg).pub (.lookIn m (Desc.K3.pieceAt X m dg)) a = k3LookInAt X D m dg a.2 := by
  show (match k3SortAt X m (Desc.K3.pieceAt X m dg) with
    | some dg => lookInC (K3Data.of X D) m dg a.2
    | none => Mg.pub (.lookIn m (Desc.K3.pieceAt X m dg)) a) = _
  rw [sort_at]
  rfl

theorem fill_lookOut (m : Nat) (dg : Bool) (a : P × First.S) :
    (fillK3 X D Mg).pub (.lookOut m (Desc.K3.pieceAt X m dg)) a = k3OnOutAt X m dg a.2 := by
  show (match k3SortAt X m (Desc.K3.pieceAt X m dg) with
    | some dg => lookOutC (K3Data.of X D) m dg a.2
    | none => Mg.pub (.lookOut m (Desc.K3.pieceAt X m dg)) a) = _
  rw [sort_at]
  rfl

theorem fill_linkFresh (m : Nat) (a : P × First.S) :
    (fillK3 X D Mg).pub (.linkFresh m) a = linkFreshB (D.arrayOf.getD m #[]) a.2 := rfl

theorem fill_left (m : Nat) (a : P × First.S) : (fillK3 X D Mg).pub (.left m) a = true := rfl

theorem fill_leftOn (m : Nat) (a : P × First.S) : (fillK3 X D Mg).pub (.leftOn m) a = true := rfl

theorem fill_live (m : Nat) (a : P × First.S) :
    (fillK3Live X D Mg).pub (liveItem m) a = liveIsB D a.2 := by
  show (if ("frame.liveIs" == "frame.liveIs") = true then liveIsC (K3Data.of X D) a.2
    else Mg.pub (.more (some m) "frame.liveIs") a) = _
  simp
  rfl

theorem fill_pubP_left (m : Nat) (a : P × First.S) :
    (fillK3 X D Mg).pubP (.left m) a = k3LeftItemAt X m a.2 := rfl

theorem fill_pubP_leftOn (m : Nat) (a : P × First.S) :
    (fillK3 X D Mg).pubP (.leftOn m) a = k3LeftOnItemAt X m a.2 := rfl

theorem fill_more : (fillK3 X D Mg).more = Mg.more := rfl

theorem fillLive_more : (fillK3Live X D Mg).more = Mg.more.merge liveMore := rfl

theorem fillLive_pubP : (fillK3Live X D Mg).pubP = Mg.pubP := rfl

/-- The thin layer leaves every other item as it was. -/
theorem fillLive_other (q : Pub) (a : P × First.S) (h : k3LiveItem q = false) :
    (fillK3Live X D Mg).pub q a = Mg.pub q a := by
  cases q with
  | more sg name =>
    cases sg with
    | none => rfl
    | some m =>
      have e : (name == "frame.liveIs") = false := h
      show (if (name == "frame.liveIs") = true then liveIsC (K3Data.of X D) a.2
        else Mg.pub (.more (some m) name) a) = _
      rw [e]
      rfl
  | _ => rfl

/-! ## (iii) Every other item is left as it was -/

theorem fill_pub_other (q : Pub) (a : P × First.S) (h : k3Item (K3Data.of X D) q = false) :
    (fillK3 X D Mg).pub q a = Mg.pub q a := by
  cases q with
  | lookIn m pc =>
    have e : k3SortAt X m pc = none := by simpa [k3Item, K3Data.of] using h
    show (match k3SortAt X m pc with
      | some dg => lookInC (K3Data.of X D) m dg a.2
      | none => Mg.pub (.lookIn m pc) a) = _
    rw [e]
  | lookOut m pc =>
    have e : k3SortAt X m pc = none := by simpa [k3Item, K3Data.of] using h
    show (match k3SortAt X m pc with
      | some dg => lookOutC (K3Data.of X D) m dg a.2
      | none => Mg.pub (.lookOut m pc) a) = _
    rw [e]
  | linkFresh m => simp [k3Item] at h
  | left m => simp [k3Item] at h
  | leftOn m => simp [k3Item] at h
  | _ => rfl

theorem fill_pubP_other (q : Pub) (a : P × First.S) (h1 : ∀ m, q ≠ .left m)
    (h2 : ∀ m, q ≠ .leftOn m) : (fillK3 X D Mg).pubP q a = Mg.pubP q a := by
  cases q with
  | left m => exact absurd rfl (h1 m)
  | leftOn m => exact absurd rfl (h2 m)
  | _ => rfl

/-! ## (ii) The rows' premises at the term -/

/-- **fLook | pubIn**: the item lookIn at the term gives k3LookIn at the place's own parameters. -/
theorem fLook_fill (m : Nat) (dg : Bool) {x : Place} (hlook : lookAt X m dg = some x) (z : P)
    (s : First.S)
    (h : (fillK3 X D Mg).pub (.lookIn m (Desc.K3.pieceAt X m dg)) (z, s) = true) :
    k3LookIn (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) dg x)
      (D.arrayOf.getD x.link #[]) s = true := by
  rw [fill_lookIn] at h
  unfold k3LookInAt placeAt at h
  rw [hlook] at h
  rw [VerifiableInference.OnPublicFiles.lookAt_link hlook]
  exact h

/-- **fOut**: k3OnOut at the place's own parameters gives the item lookOut at the term. -/
theorem fOut_fill (m : Nat) (dg : Bool) {x : Place} (hlook : lookAt X m dg = some x) (z : P)
    (s : First.S)
    (h : Desc.K3.k3OnOut (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) dg x) s = true) :
    (fillK3 X D Mg).pub (.lookOut m (Desc.K3.pieceAt X m dg)) (z, s) = true := by
  rw [fill_lookOut]
  unfold k3OnOutAt placeAt
  rw [hlook]
  exact h

/-- **fLive.** -/
theorem fLive_fill (m : Nat) (z : P) (s : First.S) :
    (fillK3Live X D Mg).pub (liveItem m) (z, s) = true ↔ LiveIs D s := by
  rw [fill_live]
  exact liveIsB_iff D s

/-- **fFresh.** -/
theorem fFresh_fill (m : Nat) (z : P) (s : First.S) :
    (fillK3 X D Mg).pub (.linkFresh m) (z, s) = true ↔
      linkFreshB (D.arrayOf.getD m #[]) s = true := Iff.rfl

/-- **fLeft.** -/
theorem fLeft_fill (m : Nat) (z : P) (s : First.S) :
    (fillK3 X D Mg).pub (.left m) (z, s) = true := rfl

/-- **fLeftP.** -/
theorem fLeftP_fill (m : Nat) {x : Place} (hlook : lookAt X m false = some x) (z : P)
    (s : First.S)
    (h : k3LeftItem (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) false x) s) :
    (fillK3 X D Mg).pubP (.left m) (z, s) :=
  ⟨_, by unfold placeAt; rw [hlook]; rfl, h⟩

/-- The like for leftOn. -/
theorem fLeftOnP_fill (m : Nat) {x : Place} (hlook : lookAt X m false = some x) (z : P)
    (s : First.S)
    (h : k3LeftOnItem (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) false x) s) :
    (fillK3 X D Mg).pubP (.leftOn m) (z, s) :=
  ⟨_, by unfold placeAt; rw [hlook]; rfl, h⟩

/-- **hAsk**: the thin layer's door asks liveName at both lookups' places. -/
theorem hAsk_fill (links : List ModelPart) (a : Desc.Place) (i : Nat) (sub : ModelPart)
    (hl : a.link = some i) (hs : links[i]? = some sub)
    (hp : a.piece = 2 + shift sub ∨ a.piece = 7 + shift sub) :
    liveName i ∈ ((fillK3Live X D Mg).more.rows links a).asks := by
  refine List.mem_append_right _ ?_
  rcases hp with hp | hp <;> cases sub <;> simp [liveMore, liveAskers, shift, hl, hs, hp]

end

end VerifiableInference.Desc.First.Look

#print axioms VerifiableInference.Desc.First.Look.fillK3_pub
#print axioms VerifiableInference.Desc.First.Look.lookInC_is
#print axioms VerifiableInference.Desc.First.Look.linkFreshC_is
#print axioms VerifiableInference.Desc.First.Look.liveIsC_is
#print axioms VerifiableInference.Desc.First.Look.fill_pub_other
#print axioms VerifiableInference.Desc.First.Look.fillLive_other
#print axioms VerifiableInference.Desc.First.Look.fLook_fill
#print axioms VerifiableInference.Desc.First.Look.fOut_fill
#print axioms VerifiableInference.Desc.First.Look.fLive_fill
#print axioms VerifiableInference.Desc.First.Look.fLeftP_fill
#print axioms VerifiableInference.Desc.First.Look.hAsk_fill
