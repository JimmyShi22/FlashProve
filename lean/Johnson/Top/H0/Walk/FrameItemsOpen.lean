-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Walk/FrameItemsOpen.lean: THE FIELD "items" OF `LettersRide` (FrameTied.lean) AT THE
COMPOSED MEANING (`mgAll 𝔇 Mg`), WITH THE TWO PARAMETERS THAT HAVE A SENTENCE's VERY TYPE
ASKED ONLY WHERE THEIR ITEM IS OPEN.

Why. `FieldsBack` (Johnson/Desc/Sound/ItemsRide.lean) asks its field "carry" at EVERY segment m, and
`HeadBack` (FrameFieldsBackHead.lean) asks the output head's sentence at EVERY part, whether the
item is open at the border or not. A filling of 𝔇.cr1 that is false where its way into the
verifier's state refuses may go back at the segments whose item is open and fail at another: the
premise would then be unpayable, and the rule empty, for the sake of an item that nobody asks about.

What is said.
  `CarryOpen 𝔇 Op R`: 𝔇.cr1 m goes back over R at the m whose item "carry m" is open behind.
  `HeadOpen 𝔇 Op R`: 𝔇.headPart p goes back over R at the parts p whose item at the output head's
    segment is open behind.
  `Read3 𝔇 low R`: the three other premises of `ParamsRead` (FrameFieldsBack.lean), alone.
  `holds_back_open`: **every item that is open behind goes back over R**, from `RelReads`, `Read3`,
    `CarryOpen`, `HeadOpen` and the three facts on the open items (no part of a segment of its own;
    not the digits' part; its pins' trees have `low`). How: the arms "carry" and "constr" by hand
    (the second: `constrQAt_back`, `constrQAt_back_any`, called); every other arm reads neither
    parameter: it is `holds_back` at the composed meaning with these two set to "true", which is the
    same sentence there by definition.
  `items_open`: the field "items", to the letter, at `StepRel rel base In`.
  `read3_same`, `read3_of_kept`: `Read3` at a step that leaves the state: outright; at a step that
    gives `Kept`: from `ReadKept`.
  `items_same_open`, `items_cleared_open`, `items_clear_row_open`: the field at the frame's steps.

Limits. `CarryOpen`, `HeadOpen`, `ReadKept` are premises on parameters that are letters:
THAT ANY REAL FILLING HAS THEM IS NOT SHOWN HERE. The three facts on the open items are facts on
the table and the plan's numbers: owed. No soundness statement.

-/
import Johnson.Top.H0.Walk.FrameFieldsBackHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.Walk.Tied
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Strs)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S Item Meaning Numbers)
open VerifiableInference.Desc.First.Pend (pendingRowO)
open VerifiableInference.OnPublicFiles (headLink)

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (VerifiableInference.Desc.Wit (CellsQ rows cols) Tok MsgT))

/-- 𝔇.cr1 goes back at the segments whose item is open behind. -/
def CarryOpen (Op : Item → Prop) (R : P × S → Strs → P × S → Strs → Prop) : Prop :=
  ∀ m, Op (.carry m) → GoesBack R (𝔇.cr1 m)

/-- 𝔇.headPart goes back at the parts whose item at the output head's segment is open behind. -/
def HeadOpen (Op : Item → Prop) (R : P × S → Strs → P × S → Strs → Prop) : Prop :=
  ∀ p, Op (.constr (headLink X) p) → ∀ i, GoesBack R (𝔇.headPart p i)

/-- The three premises on the readers, alone. -/
structure Read3 (low : Nat → Prop) (R : P × S → Strs → P × S → Strs → Prop) : Prop where
  req : ∀ a y b y', R a y b y' → 𝔇.H.req a = 𝔇.H.req b
  dec : ∀ a y b y', R a y b y' → ∀ c, 𝔇.decT c a = 𝔇.decT c b
  smp : ∀ a y b y', R a y b y' → ∀ x ∈ 𝔇.ms, low (x.1.seat x.2).1 →
    𝔇.smp a x.1 x.2 = 𝔇.smp b x.1 x.2

/-- **EVERY ITEM THAT IS OPEN BEHIND GOES BACK.** -/
theorem holds_back_open (N : Numbers) (Op : Item → Prop) (low : Nat → Prop)
    (R : P × S → Strs → P × S → Strs → Prop) (hR : RelReads low R) (h3 : Read3 𝔇 low R)
    (hc : CarryOpen 𝔇 Op R) (hH : HeadOpen 𝔇 Op R)
    (hO : ∀ i, Op i → i.part = none ∧ notOwn ownDigits i ∧ lowItem N low i) :
    ∀ i, Op i → GoesBack R (i.holds N (mgAll 𝔇 Mg)) := by
  intro i hi
  obtain ⟨hp, ho, hl⟩ := hO i hi
  have F : FieldsBack
      (mgAll { 𝔇 with cr1 := fun _ _ _ _ => True, headPart := fun _ _ _ _ _ => True } Mg)
      ownDigits low R :=
    fieldsBack_head _ Mg low R hR ⟨h3.req, h3.dec, h3.smp, fun _ _ _ _ _ _ _ _ => trivial⟩
      fun _ _ _ _ _ _ _ _ _ => trivial
  cases i with
  | carry m =>
    show GoesBack R ((mgAll 𝔇 Mg).carry m)
    rw [mgAll_carry]
    exact hc m hi
  | constr m p =>
    have ho' : (p == .lookDigits) = false := ho
    have h1 : p ≠ .lookDigits := by
      intro e
      subst e
      simp at ho'
    have hdec : ∀ a y b y', R a y b y' →
        (oneDec 𝔇.decT 𝔇.H).dec a y = (oneDec 𝔇.decT 𝔇.H).dec b y' := by
      intro a y b y' h
      show 𝔇.decT y.cell a = 𝔇.decT y'.cell b
      rw [show y'.cell = y.cell from funext (hR.cell a y b y' h)]
      exact h3.dec a y b y' h _
    show GoesBack R ((mgAll 𝔇 Mg).constr m p)
    rw [mgAll_constr]
    by_cases hm : m = headLink X
    · subst hm
      exact constrQAt_back_any (headLink X) 𝔇.put (oneDec 𝔇.decT 𝔇.H) 𝔇.headPart 𝔇.digitsPart _ p
        h1 R (fun a y b y' h => h3.req a y b y' h) hdec (hH p hi)
    · exact constrQAt_back (headLink X) 𝔇.put (oneDec 𝔇.decT 𝔇.H) 𝔇.headPart 𝔇.digitsPart m p h1
        hm R (fun a y b y' h => h3.req a y b y' h) hdec
  | pin m t => exact holds_back N _ ownDigits low R F (.pin m t) hp ho hl
  | pinKept m => exact holds_back N _ ownDigits low R F (.pinKept m) hp ho hl
  | pinI => exact holds_back N _ ownDigits low R F .pinI hp ho hl
  | pinV => exact holds_back N _ ownDigits low R F .pinV hp ho hl
  | pinW => exact holds_back N _ ownDigits low R F .pinW hp ho hl
  | row m c => exact holds_back N _ ownDigits low R F (.row m c) hp ho hl
  | pile => exact holds_back N _ ownDigits low R F .pile hp ho hl
  | pileOne => exact holds_back N _ ownDigits low R F .pileOne hp ho hl
  | wrow => exact holds_back N _ ownDigits low R F .wrow hp ho hl
  | unmarked => exact holds_back N _ ownDigits low R F .unmarked hp ho hl
  | tie m => cases hp
  | forms m k r => cases hp
  | formsT m k r => cases hp
  | worth m k r => cases hp
  | wo m => cases hp
  | totalB m => cases hp
  | total m => cases hp

/-- **The field "items" of `LettersRide`, to the letter.** -/
theorem items_open (N : Numbers) (Op : Item → Prop) (rel : S → S → Prop) (base : Nat)
    (In : P × S → Strs → Prop) (hrel : ∀ s t, rel s t → SameRead s t)
    (h3 : Read3 𝔇 (fun j => j < base) (StepRel rel base In))
    (hc : CarryOpen 𝔇 Op (StepRel rel base In)) (hH : HeadOpen 𝔇 Op (StepRel rel base In))
    (hO : ∀ i, Op i → i.part = none ∧ notOwn ownDigits i ∧ lowItem N (fun j => j < base) i) :
    ∀ p s t y y' w i, rel s t → Stays base y y' → In (p, s) y → Op i →
      i.holds N (mgAll 𝔇 Mg) (p, t) y' w → i.holds N (mgAll 𝔇 Mg) (p, s) y w :=
  fun p s t y y' w i hr hy hI hop h =>
    holds_back_open 𝔇 Mg N Op _ _ (relReads_step rel base In hrel) h3 hc hH hO i hop (p, s) y
      (p, t) y' w ⟨rfl, hr, hy, hI⟩ h

theorem read3_same (rel : S → S → Prop) (hrel : ∀ s t, rel s t → t = s) (base : Nat)
    (In : P × S → Strs → Prop) : Read3 𝔇 (fun j => j < base) (StepRel rel base In) := by
  have hb : ∀ (a : P × S) (y : Strs) (b : P × S) (y' : Strs),
      StepRel rel base In a y b y' → b = a := fun a y b y' h => Prod.ext h.1 (hrel _ _ h.2.1)
  refine ⟨?_, ?_, ?_⟩
  · intro a y b y' h
    rw [hb a y b y' h]
  · intro a y b y' h c
    rw [hb a y b y' h]
  · intro a y b y' h x _ _
    rw [hb a y b y' h]

theorem read3_of_kept (rel : S → S → Prop) (hrel : ∀ s t, rel s t → Kept s t) (base : Nat)
    (In : P × S → Strs → Prop) (H : ReadKept 𝔇 base) :
    Read3 𝔇 (fun j => j < base) (StepRel rel base In) where
  req a y b y' h := by
    obtain ⟨p, s⟩ := a
    obtain ⟨p', t⟩ := b
    obtain rfl : p' = p := h.1
    exact H.req p' s t (hrel _ _ h.2.1)
  dec a y b y' h c := by
    obtain ⟨p, s⟩ := a
    obtain ⟨p', t⟩ := b
    obtain rfl : p' = p := h.1
    exact H.dec p' s t c (hrel _ _ h.2.1)
  smp a y b y' h x hx hl := by
    obtain ⟨p, s⟩ := a
    obtain ⟨p', t⟩ := b
    obtain rfl : p' = p := h.1
    exact H.smp p' s t (hrel _ _ h.2.1) x hx hl

/-- At a step that leaves the verifier's state (the chain's front: `Yes .ok`; "laid":
`Yes (layFront m)`, by `laidAdds`). -/
theorem items_same_open (N : Numbers) (Op : Item → Prop) (rel : S → S → Prop)
    (hrel : ∀ s t, rel s t → t = s) (base : Nat) (In : P × S → Strs → Prop)
    (hc : CarryOpen 𝔇 Op (StepRel rel base In)) (hH : HeadOpen 𝔇 Op (StepRel rel base In))
    (hO : ∀ i, Op i → i.part = none ∧ notOwn ownDigits i ∧ lowItem N (fun j => j < base) i) :
    ∀ p s t y y' w i, rel s t → Stays base y y' → In (p, s) y → Op i →
      i.holds N (mgAll 𝔇 Mg) (p, t) y' w → i.holds N (mgAll 𝔇 Mg) (p, s) y w :=
  items_open 𝔇 Mg N Op rel base In (fun s t e => by rw [hrel s t e]; exact SameRead.refl s)
    (read3_same 𝔇 rel hrel base In) hc hH hO

/-- At an accepting "cleared". -/
theorem items_cleared_open (N : Numbers) (Op : Item → Prop) (L : LinkPub)
    (counts : S → Except String Unit) (left : S → Option WsForkOut) (lay : WsLay)
    (lin : Params.LinShape) (base : Nat) (In : P × S → Strs → Prop) (H : ReadKept 𝔇 base)
    (hc : CarryOpen 𝔇 Op (StepRel (Yes (clearWith L counts left
      fun im w n os => pendingRowO lay im w n lin os)) base In))
    (hH : HeadOpen 𝔇 Op (StepRel (Yes (clearWith L counts left
      fun im w n os => pendingRowO lay im w n lin os)) base In))
    (hO : ∀ i, Op i → i.part = none ∧ notOwn ownDigits i ∧ lowItem N (fun j => j < base) i) :
    ∀ p s t y y' w i,
      Yes (clearWith L counts left fun im w n os => pendingRowO lay im w n lin os) s t →
      Stays base y y' → In (p, s) y → Op i →
      i.holds N (mgAll 𝔇 Mg) (p, t) y' w → i.holds N (mgAll 𝔇 Mg) (p, s) y w :=
  items_open 𝔇 Mg N Op _ base In (fun s t h => sameRead_cleared L counts left lay lin s t h)
    (read3_of_kept 𝔇 _ (fun s t h => kept_cleared L counts left lay lin s t h) base In H) hc hH hO

/-- At the "cleared" of a row of the frame's own list. -/
theorem items_clear_row_open (N : Numbers) (Op : Item → Prop) {built : Array Stages.LinkH}
    {first : Params.First} {W : Verify.Public} {fs : List Seat.LinkFrame} {f : Seat.LinkFrame}
    {l : Nat} (h : Seat.framesOf built first W = .ok fs) (hf : fs[l]? = some f) (base : Nat)
    (In : P × S → Strs → Prop) (H : ReadKept 𝔇 base)
    (hc : CarryOpen 𝔇 Op (StepRel (Yes f.clear) base In))
    (hH : HeadOpen 𝔇 Op (StepRel (Yes f.clear) base In))
    (hO : ∀ i, Op i → i.part = none ∧ notOwn ownDigits i ∧ lowItem N (fun j => j < base) i) :
    ∀ p s t y y' w i, Yes f.clear s t → Stays base y y' → In (p, s) y → Op i →
      i.holds N (mgAll 𝔇 Mg) (p, t) y' w → i.holds N (mgAll 𝔇 Mg) (p, s) y w := by
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
  exact items_cleared_open 𝔇 Mg N Op L counts left W.layers.wsLay first.lin base In H hc hH hO

end

#print axioms holds_back_open
#print axioms items_open
#print axioms items_same_open
#print axioms items_cleared_open
#print axioms items_clear_row_open

end Johnson.Desc.First.Walk.Tied
