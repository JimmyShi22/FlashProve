-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/CallsG.lean: K01_law: SIX CALLS, EACH ENDING AT THE LETTER OF A BINDER OF THE TOP (k01_law, Johnson/Desc/K1/Law/K01Law.lean) AT ONE (l, hl, d, X, arrs): hSmp_at · hPub_at · aForms_at · aConstr_at · aRow_at · hg_at.
WHAT EACH LEAVES IS SORTED:
  LaidK1    **what the composed meaning's constant gives**: equations on the meaning Mg and on the letters of its data: at mgAt (Johnson/P5J/MgAtConst.lean) each by rfl or a line
  BoolsK1   **the named Bools on the plan**: each field with its line «a theorem in scope» | «a row of the door's thirteen rows (GLOSSARY.md, "entry tests")» | «[kernel] once the door is closed»
  and WHAT FITS NEITHER stays a named premise of the one theorem that spends it: THE TRUE DEBT:
     hRd (ReadersStay) · hl (the reader's one answer)      each open run's kind's files: «Respects»; K1's half stands in K1/Law/ReadersStayAt.lean
     hwt                                                   the letter wt at an open "weights" item
     hmeet (AheadMeets)                                    OWN#: "frame.sentIs" | "frame.sentIs1" (as reported)
     hreq · hhead · hdig                                   the model's relation's letters H.req · headPart · digitsPart go back over the sub-protocol's accept
     hrest                                                 the public items that hPub_of does not pay
THE MEMBERS: ‹Class›_blkL: the lot's own sub-protocol at (l, d) is a member of each class that the called files ask (KeepsKeeper · LaterSend · LaterSeated · LaterGrows · LaterRows · LaterGroup), by cases on d.
THE TOP's LETTER Cells IS FIXED HERE: Cells := Sound.CellsQ rows cols (aConstr_of asks it; at mgAt it is that).
IT CALLS, AND RETYPES NONE: hSmp_of (CallsD.lean, over smpLeft_named, SmpNamedEarlierMessages.lean) · hPub_of (PubAtLaterCall.lean) · aForms_of (AFormsOf.lean) · aConstr_of (AConstrOf.lean) · hg_of (GroupIsAt.lean) · hseg_full (FormsAtFifty.lean) · aRow_of (RowAtLater.lean, over five further files) · Book.placed_of_fits (Johnson/Desc/Book/BookFits.lean).
Nothing on soundness.
-/
import Johnson.Desc.K1.Law.CallsD
import Johnson.Desc.K1.Law.FillsK1
import Johnson.Desc.K1.Law.AFormsOf
import Johnson.Desc.K1.Law.AConstrOf
import Johnson.Desc.K1.Law.RowAtLater
import Johnson.Desc.K1.Law.GroupIsAt
import Johnson.Desc.K1.Law.CallsE
import Johnson.Desc.K1.Law.FormsAtFifty
import Johnson.Desc.K13.Law.SigDecodes
import Johnson.Desc.Book.BookFits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open OnBytes.Maker Cb Johnson.Pack
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers More PubData pubAll flatPlacesOf
  rowSays wordsAtFirst)
open VerifiableInference.Desc.Sound (Mem MsgT linksFull smpNamed Stated CellsQ)
open VerifiableInference.Desc.K13.Law (openAt)
open OnBytes.Model.Stages (LinkH)
open IM (k1Ix k1Reads)

/-! ## The members -/

section
variable (Z : ProofFile.Pub) (G₀ : ProofFile.Ground) (l : ℕ) (d : Bool) (X : LinkH) (arrs : Option (List ℕ))

theorem two_blkL : (blkL Z G₀ l d X arrs).rounds.length = 2 := by
  cases d with
  | true => rfl
  | false => exact rounds_k1Reads _ _ _ _ _ _

theorem keepsKeeper_blkL : KeepsKeeper (blkL Z G₀ l d X arrs) := by
  cases d with
  | true => exact keepsKeeper_laterAt _ _ _ _ _ _
  | false => exact keepsKeeper_k1Reads _ _ _ _ _ _

theorem laterSend_blkL : LaterSend (parL Z G₀ l d) (blkL Z G₀ l d X arrs) := by
  cases d with
  | true => exact laterSend_laterAt _ _ _ _ _ _
  | false => exact laterSend_k1Reads _ _ _ _ _ _

theorem laterGrows_blkL : LaterGrows (blkL Z G₀ l d X arrs) := by
  cases d with
  | true => exact laterGrows_laterAt _ _ _ _ _ _
  | false => exact laterGrows_k1Reads _ _ _ _ _ _

theorem laterRows_blkL : LaterRows (parL Z G₀ l d) (blkL Z G₀ l d X arrs) := by
  cases d with
  | true => exact laterRows_laterAt _ _ _ _ _ _
  | false => exact laterRows_k1Reads _ _ _ _ _ _

theorem laterGroup_blkL : LaterGroup (blkL Z G₀ l d X arrs) := by
  cases d with
  | true => exact laterGroup_laterAt _ _ _ _ _ _
  | false => exact laterGroup_k1Reads _ _ _ _ _ _

theorem momL_lt : momL d < 3 := by cases d <;> decide

end

/-! ## The two structures -/

/-- A test on the state: where a link is open, its frame's group number is the plan's for that link. -/
def groupAllB (N : Numbers) (s : S) : Bool :=
  s.link?.all fun L => L.check.frame.group == N.groupAt L.link

/-- A test on the state: where a link is open, its frame's shape is the plan's. -/
def liveShapeB (sh : Params.ReqShape) (s : S) : Bool :=
  s.link?.all fun L => decide (L.check.frame.shape = sh)

/-- Both. (What K1's later sendings spend of the open link's frame; each a field of FoldFacts: groupIs · liveShape.) -/
def liveB (N : Numbers) (sh : Params.ReqShape) (s : S) : Bool := groupAllB N s && liveShapeB sh s

/-- liveB, and one more test on the state, a letter: for a fact on reached states that a payer of a law on a step wants inside the promise (so: «where the output head's tables are laid, they are the reads' quiet step's own»). -/
def liveX (N : Numbers) (sh : Params.ReqShape) (xb : S → Bool) (s : S) : Bool := liveB N sh s && xb s

section
variable {Pp Xi Tok : Type} {rows cols : ℕ} {XV : Model.Verify.Public}

/-- The Bool halves' data as the composed term lays them (FillsK1.pub's right side). -/
abbrev dK (Dp : PubData) (_D3 : First.Look.Sent) : PubData := Dp

/-- **WHAT THE COMPOSED MEANING's CONSTANT GIVES.** gI l · gB l: the named public item on the open link's group at segment l ("K9.groupIs (l)") and its Bool · fI · fB: the item on the book ("K12.bookFits") and its Bool. -/
structure LaidK1 (N : Numbers) (Dp : PubData) (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
    (smp : Pp × S → (s : Sound.Sending) → (i : Fin s.l.length) → Option ((sigOf Dp.cs s.l).om i).Smp)
    (ms : List Mem) (decT : (ℕ → Option (ℕ × List UInt64)) → Pp × S → Option (CellsQ rows cols))
    (shape : Params.ReqShape) (layout : Params.ReqLayout) (io0 : Pp × S → Bool)
    (pb : Pub → Pp × S → Bool) (X3 : OnBytes.Model.Verify.Public) (D3 : First.Look.Sent)
    (MgP : Meaning Pp (Wit (CellsQ rows cols) Tok MsgT)) (seats : List (ℕ × ℕ)) (St : Stated)
    (after : ℕ → S → Except String S)
    (wt : ℕ → Pp × S → Strs → Wit (CellsQ rows cols) Tok MsgT → Prop) (rwB : ℕ → S → Bool) (hd : ℕ)
    (put : P5J.TReq → Fin Inst.Model.ppref.V → P5J.TReq)
    (H : P5J.HidAt XV Pp (Wit (CellsQ rows cols) Tok MsgT) rows cols)
    (headPart : P5J.TPart → Sound.IdxQ → Pp × S → Strs → Wit (CellsQ rows cols) Tok MsgT → Prop)
    (digitsPart : ℕ → Pp × S → Strs → Wit (CellsQ rows cols) Tok MsgT → Prop)
    (fI : Pub) (fB : TreeBook → Bool)
    (Mg0 Mg : Meaning Pp (Wit (CellsQ rows cols) Tok MsgT)) : Prop where
  /-- the ten equations of K1/Law/FillsK1.lean: at mgAll by rfl -/
  fills : FillsK1 Dp G arr smp ms decT shape layout io0 pb X3 D3 MgP Mg
  /-- the table's numbers are the data's -/
  num : Dp.N = N
  /-- the reader of OOD samples is the named one (smpNamed, Johnson/Desc/Sound/SmpNamed.lean) -/
  smp : smp = smpNamed Dp.cs seats
  /-- mgAll_row -/
  row : Mg.row = rowSays N (wordsAtFirst arr)
  /-- mgAll_forms -/
  forms : Mg.forms =
    (Sound.meaningForms Dp.cs arr ms Dp.Rd Dp.runs St after Dp.N wt rwB Dp.ah Mg0).forms
  /-- mgAll_constr -/
  constr : Mg.constr = P5J.constrQAt hd put (Sound.oneDec decT H) headPart digitsPart
  /-- what "in order" says beside inOrderK13 holds «the open link's frame's group number is the plan's»: AT THE WIDER MEANING a conjunct laid for it; its payer along the verifier's run: FoldFacts.groupIs (group_open, Johnson/IMR/GroupRest.lean) -/
  ioLive : ∀ a, io0 a = true → liveB N shape a.2 = true
  /-- the item on the book says Book.BookFits (Johnson/Desc/Book/BookFits.lean) of the state's book (bookFitsB_iff, Johnson/Desc/Sound/BookTestsLaw.lean) -/
  fits : ∀ a, Mg.pub fI a = fB a.2.book
  fitsSays : ∀ B, fB B = true ↔ Book.BookFits B

/-- **THE NAMED Bools ON THE PLAN, AND THE FACTS ON THE CLOSED DOOR.** -/
structure BoolsK1 (N : Numbers) (Dp : PubData) (seats : List (ℕ × ℕ)) (Z : ProofFile.Pub)
    (G₀ : ProofFile.Ground) (M : More) (fI : Pub) : Prop where
  /-- A ROW OF THE DOOR's THIRTEEN ROWS (GLOSSARY.md, "entry tests"), or a theorem from bookFit with «placesAre»: every tenant whose pin is open in front has its number in seats below the plan's count of messages in front of the place -/
  idx : ∀ l, l < 25 → ∀ d : Bool,
    ∀ u ∈ First.sampledIn N (openAt linksFull (flatPlacesOf linksFull true) (noL l d)),
      seats.idxOf u < N.msgsAt (flatPlacesOf linksFull true)[noL l d]?
  /-- [KERNEL] once the door is closed: the door makes no «formsIn» -/
  noForms : ∀ l, l < 25 → ∀ d : Bool,
    noFormsB M linksFull (flatPlacesOf linksFull true) (noL l d) = true
  /-- [KERNEL] once the door is closed: the item on the book is open in front of the place -/
  fitsOpen : ∀ l, l < 25 → ∀ d : Bool,
    fI ∈ (First.pubSets M linksFull (flatPlacesOf linksFull true))[noL l d]?.getD [] ++
      First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l d))

variable {N : Numbers} {Dp : PubData} {G : FileDescription Xi} {arr : ℕ → ℕ → ℕ}
  {smp : Pp × S → (s : Sound.Sending) → (i : Fin s.l.length) → Option ((sigOf Dp.cs s.l).om i).Smp}
  {ms : List Mem} {decT : (ℕ → Option (ℕ × List UInt64)) → Pp × S → Option (CellsQ rows cols)}
  {shape : Params.ReqShape} {layout : Params.ReqLayout} {io0 : Pp × S → Bool}
  {pb : Pub → Pp × S → Bool} {X3 : OnBytes.Model.Verify.Public} {D3 : First.Look.Sent}
  {MgP : Meaning Pp (Wit (CellsQ rows cols) Tok MsgT)} {seats : List (ℕ × ℕ)} {St : Stated}
  {after : ℕ → S → Except String S}
  {wt : ℕ → Pp × S → Strs → Wit (CellsQ rows cols) Tok MsgT → Prop} {rwB : ℕ → S → Bool} {hd : ℕ}
  {put : P5J.TReq → Fin Inst.Model.ppref.V → P5J.TReq}
  {H : P5J.HidAt XV Pp (Wit (CellsQ rows cols) Tok MsgT) rows cols}
  {headPart : P5J.TPart → Sound.IdxQ → Pp × S → Strs → Wit (CellsQ rows cols) Tok MsgT → Prop}
  {digitsPart : ℕ → Pp × S → Strs → Wit (CellsQ rows cols) Tok MsgT → Prop}
  {fI : Pub} {fB : TreeBook → Bool}
  {Mg0 Mg : Meaning Pp (Wit (CellsQ rows cols) Tok MsgT)} {Z : ProofFile.Pub} {G₀ : ProofFile.Ground}

/-! ## The six -/

/-- **hSmp.** Nothing is left beside the two structures. -/
theorem hSmp_at
    (hL : LaidK1 N Dp G arr smp ms decT shape layout io0 pb X3 D3 MgP seats St after wt rwB hd put H
      headPart digitsPart fI fB Mg0 Mg)
    (hB : BoolsK1 N Dp seats Z G₀ Mg.more fI) (l : ℕ) (hl : l < 25) (d : Bool) (X : LinkH)
    (arrs : Option (List ℕ)) :
    SmpLeft Dp.cs (blkL Z G₀ l d X arrs)
      (InAt N Mg linksFull (flatPlacesOf linksFull true) (noL l d)) smp ms
      (First.sampledIn N (openAt linksFull (flatPlacesOf linksFull true) (noL l d))) := by
  rw [hL.smp]
  exact hSmp_of Dp.cs seats N Mg ms Z G₀ l d X arrs (hB.idx l hl d)

/-- **hg.** Off the promise's own two clauses: the open link's number is the place's (shapeAt), and "in order". Nothing is left beside LaidK1. -/
theorem hg_at
    (hL : LaidK1 N Dp G arr smp ms decT shape layout io0 pb X3 D3 MgP seats St after wt rwB hd put H
      headPart digitsPart fI fB Mg0 Mg) (l : ℕ) (hl : l < 25) (d : Bool) (z : Pp) :
    ∀ (s : S) y, InAt N Mg linksFull (flatPlacesOf linksFull true) (noL l d) (z, s) y →
      ∀ Lk, s.link? = some Lk → Lk.check.frame.group = N.groupAt l := by
  intro s y hIn Lk hLk
  obtain ⟨⟨_, hr⟩, hm⟩ := hIn
  rcases hr with hx | ⟨h1, _, _, _⟩
  · exact absurd hm hx
  simp only [Bool.and_eq_true] at h1
  have hsh : First.shapeAt linksFull (flatPlacesOf linksFull true)[noL l d]? s = true := h1.1.1.1.1.1
  have hio : Mg.inOrder (z, s) = true := h1.1.1.2
  rw [hL.fills.inOrder, Bool.and_eq_true] at hio
  have hlv := hL.ioLive _ hio.1
  unfold liveB at hlv
  rw [Bool.and_eq_true] at hlv
  have hgA := hlv.1
  have hp : (flatPlacesOf linksFull true)[noL l d]? = some (IM.k1PlaceL l d) := place_fifty l hl d
  rw [hp] at hsh
  unfold First.shapeAt at hsh
  unfold groupAllB at hgA
  simp only [Bool.and_eq_true] at hsh
  have a1 := hsh.2
  have hLk' : (z, s).2.link? = some Lk := hLk
  rw [hLk, Option.all_some] at a1
  rw [hLk', Option.all_some] at hgA
  have e1 : (IM.k1PlaceL l d).link = some Lk.link := eq_of_beq a1
  have e2 : (IM.k1PlaceL l d).link = some l := by cases d <;> rfl
  have e3 : Lk.link = l := Option.some.inj (e1.symm.trans e2)
  rw [eq_of_beq hgA, e3]

/-- «The open link's frame's shape is the plan's», off the promise's "in order". -/
theorem hshape_at
    (hL : LaidK1 N Dp G arr smp ms decT shape layout io0 pb X3 D3 MgP seats St after wt rwB hd put H
      headPart digitsPart fI fB Mg0 Mg) (links : List ModelPart) (ps : List Place) (k : ℕ) (z : Pp) :
    ∀ (s : S) y, InAt N Mg links ps k (z, s) y →
      ∀ Lk, s.link? = some Lk → Lk.check.frame.shape = shape := by
  intro s y hIn Lk hLk
  obtain ⟨⟨_, hr⟩, hm⟩ := hIn
  rcases hr with hx | ⟨h1, _, _, _⟩
  · exact absurd hm hx
  simp only [Bool.and_eq_true] at h1
  have hio : Mg.inOrder (z, s) = true := h1.1.1.2
  rw [hL.fills.inOrder, Bool.and_eq_true] at hio
  have hlv := hL.ioLive _ hio.1
  unfold liveB at hlv
  rw [Bool.and_eq_true] at hlv
  have hsA := hlv.2
  unfold liveShapeB at hsA
  have hLk' : (z, s).2.link? = some Lk := hLk
  rw [hLk', Option.all_some] at hsA
  exact of_decide_eq_true hsA

/-- **aRow.** Nothing is left beside the two structures. -/
theorem aRow_at
    (hL : LaidK1 N Dp G arr smp ms decT shape layout io0 pb X3 D3 MgP seats St after wt rwB hd put H
      headPart digitsPart fI fB Mg0 Mg)
    (hB : BoolsK1 N Dp seats Z G₀ Mg.more fI) (l : ℕ) (hl : l < 25) (d : Bool) (X : LinkH)
    (arrs : Option (List ℕ)) (base : ℕ) :
    ∀ (x x' : Pp × S) y y' w m cl, YesOf (blkL Z G₀ l d X arrs) x x' →
      InAt N Mg linksFull (flatPlacesOf linksFull true) (noL l d) x y → KeptBelow base y y' →
      Item.row m cl ∈ openAt linksFull (flatPlacesOf linksFull true) (noL l d) →
      Mg.row m cl x' y' w → Mg.row m cl x y w := by
  intro x x' y y' w m cl hy hIn _ _ h0
  have hf : fB x.2.book = true := by
    rw [← hL.fits x]
    exact inAt_pub hIn fI (hB.fitsOpen l hl d)
  exact aRow_of hL.fills N hL.row (laterRows_blkL Z G₀ l d X arrs) (two_blkL Z G₀ l d X arrs)
    linksFull (flatPlacesOf linksFull true) (noL l d) x x' y y' w m cl hy hIn
    (fun o u hu => Book.placed_of_fits ((hL.fitsSays _).1 hf) o u hu) h0

/-- **aConstr.** LEFT: hreq · hhead · hdig: on the model's relation's letters. -/
theorem aConstr_at
    (hL : LaidK1 N Dp G arr smp ms decT shape layout io0 pb X3 D3 MgP seats St after wt rwB hd put H
      headPart digitsPart fI fB Mg0 Mg)
    (hBlind : K13.Law.DecBlind decT) (l : ℕ) (d : Bool) (X : LinkH) (arrs : Option (List ℕ))
    (base : ℕ)
    (hreq : ∀ x x', YesOf (blkL Z G₀ l d X arrs) x x' → H.req x' = H.req x)
    (hhead : ∀ x x' y y' w p i, YesOf (blkL Z G₀ l d X arrs) x x' →
      InAt N Mg linksFull (flatPlacesOf linksFull true) (noL l d) x y → KeptBelow base y y' →
      Item.constr hd p ∈ openAt linksFull (flatPlacesOf linksFull true) (noL l d) →
      headPart p i x' y' w → headPart p i x y w)
    (hdig : ∀ x x' y y' w m, YesOf (blkL Z G₀ l d X arrs) x x' →
      InAt N Mg linksFull (flatPlacesOf linksFull true) (noL l d) x y → KeptBelow base y y' →
      Item.constr m .lookDigits ∈ openAt linksFull (flatPlacesOf linksFull true) (noL l d) →
      digitsPart m x' y' w → digitsPart m x y w) :
    ∀ (x x' : Pp × S) y y' w m p, YesOf (blkL Z G₀ l d X arrs) x x' →
      InAt N Mg linksFull (flatPlacesOf linksFull true) (noL l d) x y → KeptBelow base y y' →
      Item.constr m p ∈ openAt linksFull (flatPlacesOf linksFull true) (noL l d) →
      Mg.constr m p x' y' w → Mg.constr m p x y w :=
  aConstr_of decT hd put H headPart digitsPart N Mg hL.constr linksFull
    (flatPlacesOf linksFull true) (noL l d) (blkL Z G₀ l d X arrs) base
    (fun x x' c hy => hBlind.same hy.1 c) hreq hhead hdig

/-- **aForms.** LEFT: hl (the reader's one answer) · hwt · hmeet (AheadMeets). -/
theorem aForms_at
    (hL : LaidK1 N Dp G arr smp ms decT shape layout io0 pb X3 D3 MgP seats St after wt rwB hd put H
      headPart digitsPart fI fB Mg0 Mg)
    (l : ℕ) (d : Bool) (X : LinkH) (arrs : Option (List ℕ)) (base : ℕ)
    (hl' : ∀ x x' y m j r, YesOf (blkL Z G₀ l d X arrs) x x' →
      InAt N Mg linksFull (flatPlacesOf linksFull true) (noL l d) x y →
      Item.forms m j r ∈ openAt linksFull (flatPlacesOf linksFull true) (noL l d) →
      ∀ p ∈ Dp.runs m j r, (Dp.Rd m).forms p.1 p.2 x'.2 = (Dp.Rd m).forms p.1 p.2 x.2)
    (hwt : ∀ x x' y y' w m j, YesOf (blkL Z G₀ l d X arrs) x x' →
      InAt N Mg linksFull (flatPlacesOf linksFull true) (noL l d) x y → KeptBelow base y y' →
      Item.forms m j "weights" ∈ openAt linksFull (flatPlacesOf linksFull true) (noL l d) →
      wt m x' y' w → wt m x y w)
    (hmeet : ∀ x x' y m j r, YesOf (blkL Z G₀ l d X arrs) x x' →
      InAt N Mg linksFull (flatPlacesOf linksFull true) (noL l d) x y →
      Item.forms m j r ∈ openAt linksFull (flatPlacesOf linksFull true) (noL l d) →
      ∀ p ∈ Dp.runs m j r, Dp.ah p.1 p.2 = true →
      AheadMeets (N.sent m) (N.group m) (idsOf (parL Z G₀ l d) x.2.st.oracles.size).toList x.2
        x'.2) :
    ∀ (x x' : Pp × S) y y' w m k r, YesOf (blkL Z G₀ l d X arrs) x x' →
      InAt N Mg linksFull (flatPlacesOf linksFull true) (noL l d) x y → KeptBelow base y y' →
      Item.forms m k r ∈ openAt linksFull (flatPlacesOf linksFull true) (noL l d) →
      Mg.forms m k r x' y' w → Mg.forms m k r x y w := by
  obtain rfl := hL.num
  exact aForms_of (dK Dp D3) pb arr ms St after wt rwB Mg0 Mg hL.fills.pub hL.forms linksFull
    (flatPlacesOf linksFull true) (noL l d) (parL Z G₀ l d) (blkL Z G₀ l d X arrs)
    (laterSend_blkL Z G₀ l d X arrs) (laterGrows_blkL Z G₀ l d X arrs) (two_blkL Z G₀ l d X arrs)
    base hl' hwt hmeet

/-- **hPub.** hP: the row's own test on the plan (hP_of, CallsC.lean). LEFT: hRd (ReadersStay) · hrest (the items that hPub_of does not pay). -/
theorem hPub_at
    (hL : LaidK1 N Dp G arr smp ms decT shape layout io0 pb X3 D3 MgP seats St after wt rwB hd put H
      headPart digitsPart fI fB Mg0 Mg)
    (hB : BoolsK1 N Dp seats Z G₀ Mg.more fI) (l : ℕ) (hl : l < 25) (d : Bool) (X : LinkH)
    (arrs : Option (List ℕ))
    (hP : laterSeatsB N (parL Z G₀ l d) l (momL d)
      (N.treesAt (flatPlacesOf linksFull true)[noL l d]?) = true)
    (hRd : ∀ x x' y m j r, YesOf (blkL Z G₀ l d X arrs) x x' →
      InAt N Mg linksFull (flatPlacesOf linksFull true) (noL l d) x y →
      (Pub.formsIn m j r ∈
          (First.pubSets Mg.more linksFull (flatPlacesOf linksFull true))[noL l d]?.getD [] ++
            First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l d)) ∨
        Pub.formsInT m j r ∈
          (First.pubSets Mg.more linksFull (flatPlacesOf linksFull true))[noL l d]?.getD [] ++
            First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l d))) →
      ReadersStay (dK Dp D3) m j r x.2 x'.2)
    (hrest : ∀ x x' y q, YesOf (blkL Z G₀ l d X arrs) x x' →
      InAt N Mg linksFull (flatPlacesOf linksFull true) (noL l d) x y →
      q ∈ (First.pubSets Mg.more linksFull (flatPlacesOf linksFull true))[noL l d]?.getD [] ++
        First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l d)) →
      q ∈ (First.pubSets Mg.more linksFull (flatPlacesOf linksFull true))[noL l d + 1]?.getD [] ++
        First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l d + 1)) →
      sevenItem q = false → Mg.pub q x' = true) :
    ∀ x x' y q, YesOf (blkL Z G₀ l d X arrs) x x' →
      InAt N Mg linksFull (flatPlacesOf linksFull true) (noL l d) x y →
      q ∈ (First.pubSets Mg.more linksFull (flatPlacesOf linksFull true))[noL l d]?.getD [] ++
        First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l d)) →
      q ∈ (First.pubSets Mg.more linksFull (flatPlacesOf linksFull true))[noL l d + 1]?.getD [] ++
        First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l d + 1)) →
      Mg.pub q x' = true := by
  obtain rfl := hL.num
  exact hPub_of (dK Dp D3) pb Mg hL.fills.pub linksFull (flatPlacesOf linksFull true) (noL l d)
    (parL Z G₀ l d) (blkL Z G₀ l d X arrs) (keepsKeeper_blkL Z G₀ l d X arrs)
    (laterSend_blkL Z G₀ l d X arrs) (two_blkL Z G₀ l d X arrs)
    l (momL d) (momL_lt d) hP (hseg_full Mg.more l hl d (hB.noForms l hl d)) hRd hrest

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.hSmp_at
#print axioms VerifiableInference.Desc.K1.hg_at
#print axioms VerifiableInference.Desc.K1.aRow_at
#print axioms VerifiableInference.Desc.K1.aConstr_at
#print axioms VerifiableInference.Desc.K1.aForms_at
#print axioms VerifiableInference.Desc.K1.hPub_at
