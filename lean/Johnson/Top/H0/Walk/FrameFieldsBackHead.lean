-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Walk/FrameFieldsBackHead.lean: THE EIGHT SENTENCES AT THE COMPOSED MEANING
(`mgAll 𝔇 Mg`), WITH THE OUTPUT HEAD's SEGMENT's PARTS AMONG THEM.

Why. FrameFieldsBack.lean says nothing of the parts that `ownAt X` names: "every digit lies in the
digits' table", AND EVERY PART AT THE OUTPUT HEAD's SEGMENT. But the head's segment's four parts are
open from the chain's start until the head's own sub-protocols close them: so "no item that is open
behind is one that own names" cannot be met at 50 of the frame's 51 borders (found
by an evaluation of the table at the written list). Nothing false was proved there; the premise was
empty at these places. Here own names the digits' part alone, at the price of one named premise more
on a parameter.

What is said.
  `ownDigits`: the one part of which nothing is said: "every digit lies in the digits' table".
  `HeadBack 𝔇 R`: THE PREMISE: the output head's parts' sentence (𝔇.headPart, a parameter) goes back
    over R.
  `fieldsBack_head`: **`FieldsBack (mgAll 𝔇 Mg) ownDigits low R` from `RelReads`, `ParamsRead` and
    `HeadBack`.** The field "constr": `constrQAt_back_any`, called
    (Johnson/Desc/Sound/ConstrRidesHead.lean); the seven other fields and the mark:
    FrameFieldsBack.lean's.
  `paramsRead_same`: at a step that leaves the verifier's state three of the four of `ParamsRead`
    hold outright.
  `fieldsBack_same_head`, `fieldsBack_front_head`, `fieldsBack_laid_head`: at such a step, at the
    chain's front, at "laid": under `CarryBack` and `HeadBack`.
  `fieldsBack_cleared_head`, `fieldsBack_clear_row_head`: at an accepting "cleared", and at the
    "cleared" of a row of `framesOf`: under `ReadKept`, `CarryBack` and `HeadBack`.
  `OpenFitD O' Op`, `HeadStays 𝔇 base`, `stringsRide_head`: `StringsRide N (mgAll 𝔇 Mg) base O Op`
    (FrameRides.lean) with the third clause on the open items at `ownDigits`.

Limits. `HeadBack`, `HeadStays`, `CarryBack`, `CarryStays`, `ReadKept` are premises on parameters
that are letters in the composed meaning: owed by whoever fills
them; THAT ANY REAL FILLING HAS THEM IS NOT SHOWN HERE. That no item "constr m lookDigits" is open
at a border is a fact on the table: owed. No soundness statement.

-/
import Johnson.Top.H0.Walk.FrameStringsRide
import Johnson.Desc.Sound.ConstrRidesHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.Walk.Tied
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Strs)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S Item Meaning Numbers)
open VerifiableInference.Desc.First.Pend (pendingRowO)
open VerifiableInference.OnPublicFiles (headLink)

/-- The one part of a segment's relation of which nothing is said. -/
def ownDigits : Nat → VerifiableInference.Desc.First.Part → Bool := fun _ p => p == .lookDigits

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (VerifiableInference.Desc.Wit (CellsQ rows cols) Tok MsgT))

/-- **The premise on 𝔇.headPart**: it goes back over R. -/
def HeadBack (R : P × S → Strs → P × S → Strs → Prop) : Prop :=
  ∀ p i, GoesBack R (𝔇.headPart p i)

/-- **THE EIGHT SENTENCES, THE OUTPUT HEAD's SEGMENT's PARTS AMONG THEM.** -/
theorem fieldsBack_head (low : Nat → Prop) (R : P × S → Strs → P × S → Strs → Prop)
    (hR : RelReads low R) (hP : ParamsRead 𝔇 low R) (hH : HeadBack 𝔇 R) :
    FieldsBack (mgAll 𝔇 Mg) ownDigits low R :=
  { fieldsBack_mgAll 𝔇 Mg low R hR hP with
    constr := fun m p ho => by
      have h1 : p ≠ .lookDigits := by
        intro e
        subst e
        simp [ownDigits] at ho
      rw [mgAll_constr]
      refine constrQAt_back_any (headLink X) 𝔇.put (oneDec 𝔇.decT 𝔇.H) 𝔇.headPart 𝔇.digitsPart m p
        h1 R (fun a y b y' h => hP.req a y b y' h) (fun a y b y' h => ?_) (hH p)
      show 𝔇.decT y.cell a = 𝔇.decT y'.cell b
      rw [show y'.cell = y.cell from funext (hR.cell a y b y' h)]
      exact hP.dec a y b y' h _ }

/-- At a step that leaves the verifier's state: three of the four hold outright. -/
theorem paramsRead_same (rel : S → S → Prop) (hrel : ∀ s t, rel s t → t = s) (base : Nat)
    (In : P × S → Strs → Prop) (hc : CarryBack 𝔇 rel base In) :
    ParamsRead 𝔇 (fun j => j < base) (StepRel rel base In) := by
  have hb : ∀ (a : P × S) (y : Strs) (b : P × S) (y' : Strs),
      StepRel rel base In a y b y' → b = a := fun a y b y' h => Prod.ext h.1 (hrel _ _ h.2.1)
  refine ⟨?_, ?_, ?_, hc⟩
  · intro a y b y' h
    rw [hb a y b y' h]
  · intro a y b y' h c
    rw [hb a y b y' h]
  · intro a y b y' h x _ _
    rw [hb a y b y' h]

/-- **At a step that leaves the verifier's state.** -/
theorem fieldsBack_same_head (rel : S → S → Prop) (hrel : ∀ s t, rel s t → t = s) (base : Nat)
    (In : P × S → Strs → Prop) (hc : CarryBack 𝔇 rel base In)
    (hH : HeadBack 𝔇 (StepRel rel base In)) :
    FieldsBack (mgAll 𝔇 Mg) ownDigits (fun j => j < base) (StepRel rel base In) :=
  fieldsBack_head 𝔇 Mg _ _
    (relReads_step _ base In fun s t e => by rw [hrel s t e]; exact SameRead.refl s)
    (paramsRead_same 𝔇 rel hrel base In hc) hH

/-- The chain's front. -/
theorem fieldsBack_front_head (base : Nat) (In : P × S → Strs → Prop)
    (hc : CarryBack 𝔇 (Yes .ok) base In) (hH : HeadBack 𝔇 (StepRel (Yes .ok) base In)) :
    FieldsBack (mgAll 𝔇 Mg) ownDigits (fun j => j < base) (StepRel (Yes .ok) base In) :=
  fieldsBack_same_head 𝔇 Mg _ (fun _ _ h => (Except.ok.inj h).symm) base In hc hH

/-- "link m: laid". -/
theorem fieldsBack_laid_head (m : Nat) (base : Nat) (In : P × S → Strs → Prop)
    (hc : CarryBack 𝔇 (Yes (layFront m)) base In)
    (hH : HeadBack 𝔇 (StepRel (Yes (layFront m)) base In)) :
    FieldsBack (mgAll 𝔇 Mg) ownDigits (fun j => j < base) (StepRel (Yes (layFront m)) base In) :=
  fieldsBack_same_head 𝔇 Mg _ (fun s t h => (laidAdds m s t h).1) base In hc hH

/-- **At an accepting "cleared".** -/
theorem fieldsBack_cleared_head (L : LinkPub) (counts : S → Except String Unit)
    (left : S → Option WsForkOut) (lay : WsLay) (lin : Params.LinShape) (base : Nat)
    (In : P × S → Strs → Prop) (H : ReadKept 𝔇 base)
    (hc : CarryBack 𝔇 (Yes (clearWith L counts left
      fun im w n os => pendingRowO lay im w n lin os)) base In)
    (hH : HeadBack 𝔇 (StepRel (Yes (clearWith L counts left
      fun im w n os => pendingRowO lay im w n lin os)) base In)) :
    FieldsBack (mgAll 𝔇 Mg) ownDigits (fun j => j < base) (StepRel (Yes (clearWith L counts left
      fun im w n os => pendingRowO lay im w n lin os)) base In) :=
  fieldsBack_head 𝔇 Mg _ _
    (relReads_step _ base In fun s t h => sameRead_cleared L counts left lay lin s t h)
    (paramsRead_of_kept 𝔇 _ (fun s t h => kept_cleared L counts left lay lin s t h) base In H hc)
    hH

/-- **At the "cleared" of a row of the frame's own list.** -/
theorem fieldsBack_clear_row_head {built : Array Stages.LinkH} {first : Params.First}
    {W : Verify.Public} {fs : List Seat.LinkFrame} {f : Seat.LinkFrame} {l : Nat}
    (h : Seat.framesOf built first W = .ok fs) (hf : fs[l]? = some f) (base : Nat)
    (In : P × S → Strs → Prop) (H : ReadKept 𝔇 base) (hc : CarryBack 𝔇 (Yes f.clear) base In)
    (hH : HeadBack 𝔇 (StepRel (Yes f.clear) base In)) :
    FieldsBack (mgAll 𝔇 Mg) ownDigits (fun j => j < base) (StepRel (Yes f.clear) base In) := by
  obtain ⟨L, counts, left, e⟩ : ∃ L counts left,
      f.clear = clearWith L counts left (Seat.rowOf W first) := by
    rcases Seat.framesOf_arms h hf with ⟨Y, -, -, e⟩ | ⟨-, Y, hp, Q, -, -, -, -, -, -, e⟩ |
      ⟨-, Y, hp, Q, -, -, -, -, -, -, e⟩ | ⟨-, Y, hp, Q, -, -, -, -, -, -, e⟩
    · subst e
      exact ⟨_, _, _, rfl⟩
    · exact ⟨_, _, _, e⟩
    · exact ⟨_, _, _, e⟩
    · exact ⟨_, _, _, e⟩
  rw [e] at hc hH ⊢
  exact fieldsBack_cleared_head 𝔇 Mg L counts left W.layers.wsLay first.lin base In H hc hH

/-! ### the strings' half -/

/-- Three facts on every item that is open behind, the third at `ownDigits`. -/
def OpenFitD (O : List Item) (Op : Item → Prop) : Prop :=
  ∀ i, Op i → i ∈ O ∧ i.part = none ∧ notOwn ownDigits i

/-- The premise on 𝔇.headPart at one state: it goes back over `Stays`. -/
def HeadStays (base : Nat) : Prop :=
  ∀ p i a y y' w, Stays base y y' → 𝔇.headPart p i a y' w → 𝔇.headPart p i a y w

/-- **THE STRINGS' HALF, THE OUTPUT HEAD's SEGMENT's PARTS AMONG THE ITEMS.** -/
theorem stringsRide_head {N : Numbers} {O O' : List Item} {Op : Item → Prop} {base : Nat}
    (hl : LowAt N O base) (hl' : LowAt N O' base) (hO : OpenFitD O' Op)
    (hc : CarryStays 𝔇 base) (hH : HeadStays 𝔇 base) :
    StringsRide N (mgAll 𝔇 Mg) base O Op where
  decodes := (stringsRide_three 𝔇 Mg hl).1
  shown := (stringsRide_three 𝔇 Mg hl).2.1
  noColl := (stringsRide_three 𝔇 Mg hl).2.2
  items a y y' w i hy hop h := by
    have H := fieldsBack_same_head 𝔇 Mg (fun s t => t = s) (fun _ _ e => e) base
      (fun _ _ => True)
      (fun m a y b y' w hr hb => by
        obtain rfl : b = a := Prod.ext hr.1 hr.2.1
        exact hc m b y y' w hr.2.2.1 hb)
      (fun p i a y b y' w hr hb => by
        obtain rfl : b = a := Prod.ext hr.1 hr.2.1
        exact hH p i b y y' w hr.2.2.1 hb)
    exact items_of_fields (N := N) (Op := Op) ownDigits (fun j => j < base) H
      (fun i hi => ⟨(hO i hi).2.1, (hO i hi).2.2, lowItem_of_lowAt hl' (hO i hi).1⟩)
      a.1 a.2 a.2 y y' w i rfl hy trivial hop h

end

#print axioms fieldsBack_head
#print axioms paramsRead_same
#print axioms fieldsBack_same_head
#print axioms fieldsBack_front_head
#print axioms fieldsBack_laid_head
#print axioms fieldsBack_cleared_head
#print axioms fieldsBack_clear_row_head
#print axioms stringsRide_head

end Johnson.Desc.First.Walk.Tied
