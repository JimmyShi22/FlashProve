-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Goal/Conditions/KeyAtTheSeat.lean: at the closed term VerifierAndGoals.theDescription, WITH THE KEY
FILE's SEAT LAID (Johnson/Goal/Description/KeyFold.lean: Key.keyDataAndDecisionAtFixedDigest): the row KeySound
(RowsAtTheRecord.lean) from ONE premise: the 21 laws that are left of the key file's 35, with their
letters and the facts beside them, at the seat's one description. Through keySound_the_of_seat
(KeyAtTheRule.lean): that the named decision is the description's own run, how the description was
made, that its data are the record's, and that the key file's request tree has one leaf, are no
premises here.

Main names.
  dk_the: where protocolDataWellFormed says yes the record's data of the key file, set to the frame's depth, are
    the seat's data.
  descAt_made: what the key file's maker read stays in hand.
  The21HandedAtSeat Z: what is owed at our tables at Z, at letters: The21Handed
    (Johnson/Top/Fire/Code/KeyPublicAtSeat.lean): the tables' reading, seats and reader are the
    payer's to name.
  keySound_of_handed: KeySound from The21HandedAtSeat, asked where protocolDataWellFormed says yes: the stronger of
    the two theorems here.
  The21AtSeat Z: what is owed at our tables at Z: The21AtBase (Johnson/Top/Fire/Code/KeyAtBase.lean)
    at the name's claims and coding at Z, at the one description that the seat holds, at the
    record's data: the 21 laws at the tables' written reading, seats and reader, and ten fields
    beside them; six public facts (the three chains' first blocks, the two lookups, the block that
    sends W, the ten blocks of the shared chain) are handed to the payer, not asked. The payer
    holds besides all that the seat's equation hands: how the description was made, that its data
    are the record's, its own tests on the plan and the two beside them, the yes of every test of
    the key file's door, and that the record's plan is the maker's.
  keySound_at_seat: KeySound from The21AtSeat, asked where protocolDataWellFormed says yes: by keySound_of_handed
    and handedAtSeat_of_base: it takes more than that theorem.
  The21AtNameAtSeat Z: the same with The21AtName (Johnson/Top/Fire/Code/KeyAtName.lean): seven
    letters more are written: those that the name's own configuration forces; beside the 21 laws
    six fields are left.
  keySound_at_name: KeySound from The21AtNameAtSeat: by keySound_at_seat and atSeat_of_name.
  The21AtPinAtSeat Z: the same with The21AtPin (Johnson/Top/Fire/Code/KeyAtPin.lean): one public
    equation (the record's data of the key file are the written data) in the place of the four
    facts on bases; beside the 21 laws three fields are left.
  keySound_at_pin: KeySound from The21AtPinAtSeat: by keySound_at_name and atName_of_pin.
  pin_at_seat: that equation, in scope, where protocolDataWellFormed says yes: by laid_data_written
    (Johnson/Goal/Numbers/KeySeatLaidAt.lean), over the key file's door with its second test.
  The21LastAtSeat Z: the same with The21Last: the equation is paid; beside the 21 laws two fields
    are left.
  keySound_at_last: KeySound from The21LastAtSeat: by keySound_at_pin and pin_at_seat.
  The21TabAtSeat Z: the same with The21Tab (Johnson/Top/Fire/Code/KeyAtTab.lean): the letter tab is
    written (the base word of each entry of a decoded table) and the first border's last field is
    paid; beside the 21 laws one field is left.
  keySound_at_tab: KeySound from The21TabAtSeat: by keySound_at_last and last_of_tab_at_seat.
  The21OffAtSeat Z: the same with The21Off (Johnson/Top/Fire/Code/KeyAtOff.lean): the two letters
    off₂ | off₃ are written (the tables' own member at the full size's numbers of trees): beside
    the 21 laws no field is left.
  keySound_at_off: KeySound from The21OffAtSeat: by keySound_at_tab and tab_of_off.
  The19OffAtSeat Z: the same with The19Off (Johnson/Top/Fire/Code/KeyAt19.lean): rows 1.0 and 1.1
    are laid in by two theorems: nineteen laws are left.
  keySound_at_19: KeySound from The19OffAtSeat: by keySound_at_off and off_of_19.
  RestAtSeat Z: the same with RestOff paidNow (Johnson/Top/Fire/Code/KeyAtRest.lean): the rows of
    ONE LIST are laid in, each by a theorem, one line a row; the rows that are
    not in the list are owed.
  keySound_at_rest: KeySound from RestAtSeat: by keySound_at_off and off_of_rest. As the list grows
    this name stays.
Object: the row KeySound; the seat's value through kseat_name. User:
KeyAtTheSeatWritten.lean (keySound_at_off, pin_at_seat). Letters: none.

Limits. A joining: nothing of the key file's soundness is shown: each of the nine premises is the
whole of what is then left. RestOff paidNow, the lightest to list, is the laws of the rows outside
the list, all open, at one set of two letters (enc · rad), with one statement that stands for an
inhabitant; the tables' reading, seats, reader, the stored table's matrix and the two maps on trees'
numbers are written terms; the seats and these maps' numerals are the full size's, typed by hand. No
member of any of the eight is known. (Where
this and lean/THEOREM.md differ, the page holds.) Where protocolDataWellFormed says no the row asks nothing. The description
stands at a fixed digest, and the seat's names here are those at the second hash function: no proof
in this file unfolds it. No hash stands in what the first border reads: a record's seed is its
datum. Nothing on hiding.

-/
import Johnson.Goal.Conditions.KeyAtTheRule
import Johnson.Top.Fire.Code.KeyAt19
import Johnson.Top.Fire.Code.KeyAtRest
import Johnson.Goal.Numbers.KeySeatLaidAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped ENNReal

namespace VerifierAndGoals.AtTheName
open VerifierAndGoals VerifierAndGoals.Fit FlashProve FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker
open _root_.Run
open VerifiableInference.Desc
open VerifiableInference.Desc.Key (Xi keyInstanceOfOutOfDomainSample Source LaterPlaces descriptionFromSource descAt descriptionFromPlan madeAt
    sourceOf
  rangesNumbers laterPlaces fixedDigest)

/-- Data that stand at a depth are left as they are when they are set to it. -/
theorem at_self (D : WholeD) (a : ℕ) (h : D.a = a) : D.at a = D := by
  cases D
  subst h
  rfl

/-- **Where `protocolDataWellFormed` says yes the record's data of the key file are the seat's.** -/
theorem dk_the (Z : PublicFiles) (hl : protocolDataWellFormed (asDescriptionFiles Z) = true) :
    (dataAtFiles flashProveData Z).DK.at frS.P.T.a = theKeyData (asDescriptionFiles Z) := by
  have e : (dataAtFiles flashProveData Z).DK = theKeyData (asDescriptionFiles Z) := by
    rw [builtS_live flashProveData Z hl]
    rfl
  rw [e]
  exact at_self _ _ (theLive_depth (asDescriptionFiles Z) hl).1

/-- What the maker read stays in hand. -/
theorem descAt_made (X₀ : OnBytes.Model.Verify.Public) (lay cfg : ByteArray) (G : FileDescription Xi)
    (h : descAt X₀ lay cfg = .ok G) :
    ∃ (m : Johnson.G.OfPlan.Made) (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces),
      madeAt X₀ lay cfg = .ok m ∧ sourceOf m = .ok X ∧ rangesNumbers m = .ok N ∧
        laterPlaces m = .ok P ∧ G = descriptionFromSource X N P := by
  have h' : (madeAt X₀ lay cfg).bind (fun m => descriptionFromPlan m) = .ok G := h
  cases hm : madeAt X₀ lay cfg with
  | error e =>
    rw [hm] at h'
    cases h'
  | ok m =>
    rw [hm] at h'
    have h'' : descriptionFromPlan m = .ok G := h'
    unfold descriptionFromPlan at h''
    split at h''
    · rename_i X N P hS hN hP
      injection h'' with e
      exact ⟨m, X, N, P, rfl, hS, hN, hP, e.symm⟩
    all_goals cases h''

/-- **What is owed at our tables AT THE SEAT, at one Z, AT LETTERS**: at the one description that
the seat holds: what the key file's maker returns at what `publicOfO` reads of Z's three files at
the second hash function, at Z's layout file and at the fixed digest. The payer holds all that the
seat's equation hands: how it was made, that its data are the record's, its own tests on the plan,
its two tests beside them, the yes of every test of the key file's door, and that the record's plan
is the maker's. The tables' reading, seats and reader are the payer's to name. -/
def The21HandedAtSeat (Z : PublicFiles) : Prop :=
  ∀ (X₀ : OnBytes.Model.Verify.Public) (m : Johnson.G.OfPlan.Made) (X : Source) (N : H2U.PlaceNums)
    (P : LaterPlaces),
    VerifiableInference.PlanWritten.publicOfO OnBytes.secondHashFunction Z.pol Z.KL (some Z.lay) = .ok X₀ →
    madeAt X₀ Z.lay fixedDigest = .ok m → sourceOf m = .ok X → rangesNumbers m = .ok N →
    laterPlaces m = .ok P →
    (descriptionFromSource X N P).data "key file" = .ok ((dataAtFiles flashProveData Z).DK.at frS.P.T.a) →
    (descriptionFromSource X N P).planOk = true → (descriptionFromSource X N P).wantedOk = true → (descriptionFromSource X N P).owedOk = true →
    (∀ t ∈ Key.lawsAsk X₀ Z.lay m (descriptionFromSource X N P) (theKeyData (asDescriptionFiles Z)), t.2 = true) →
    (dataAtFiles flashProveData Z).G = bigReq m.p →
    LPFD.The21Handed (dataAtFiles flashProveData Z).A (dataAtFiles flashProveData Z).E X N P (dataAtFiles flashProveData Z).DK

/-- **THE ROW KeySound FROM ONE PREMISE, AT LETTERS**: the 21 laws with their letters at the seat's
one description. Through `keySound_the_of_seat` (KeyAtTheRule.lean), which calls the seat's
equation `kseat_name` and pays the depth from `protocolDataWellFormed`. -/
theorem keySound_of_handed
    (the21 : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true → The21HandedAtSeat Z) :
    KeySound :=
  keySound_the_of_seat fun Z hs hl X₀ m X' N' P' hX₀ hm hF hp hw ho ha hD hG _ b hb er hd hε => by
    obtain ⟨m', X, N, P, hm', hX, hN, hP, e⟩ := descAt_made X₀ Z.lay fixedDigest _ hF
    obtain rfl : m' = m := Except.ok.inj (hm'.symm.trans hm)
    rw [e] at hp hw ho ha hD er
    rw [← dk_the Z hl] at hD
    have base := LPFD.keyDebtCap_of_letters (dataAtFiles flashProveData Z).A (dataAtFiles flashProveData Z).E X N P
      (dataAtFiles flashProveData Z).DK hD
      (LPFD.letters_of_handed _ _ _ hs (Johnson.RunOne.Law.ReadAtO.readOf_publicOfO hX₀) hm hX hp
        (the21 Z hs hl X₀ m' X N P hX₀ hm hX hN hP hD hp hw ho ha hG))
    exact LPFD.keySound_of_debt (descriptionFromSource X N P) keyInstanceOfOutOfDomainSample (dataAtFiles flashProveData Z).A (dataAtFiles flashProveData Z).E
      (dataAtFiles flashProveData Z).DK _ "key file"
      (LPFD.keyDebt_of_cap _ keyInstanceOfOutOfDomainSample _ _ _ _ hε "key file"
        (VerifiableInference.Desc.Sound.sealLast_of_planOk _ hp) base)
      hb er ((dataAtFiles flashProveData Z).inputFieldsAtReadings theC0 theM0) hd rfl

/-- **The same AT THE WRITTEN TERMS**: the tables' reading, seats and reader are the
written terms (Johnson/Top/Fire/Code/KeyAtBase.lean); the payer holds the same facts. -/
def The21AtSeat (Z : PublicFiles) : Prop :=
  ∀ (X₀ : OnBytes.Model.Verify.Public) (m : Johnson.G.OfPlan.Made) (X : Source) (N : H2U.PlaceNums)
    (P : LaterPlaces),
    VerifiableInference.PlanWritten.publicOfO OnBytes.secondHashFunction Z.pol Z.KL (some Z.lay) = .ok X₀ →
    madeAt X₀ Z.lay fixedDigest = .ok m → sourceOf m = .ok X → rangesNumbers m = .ok N →
    laterPlaces m = .ok P →
    (descriptionFromSource X N P).data "key file" = .ok ((dataAtFiles flashProveData Z).DK.at frS.P.T.a) →
    (descriptionFromSource X N P).planOk = true → (descriptionFromSource X N P).wantedOk = true → (descriptionFromSource X N P).owedOk = true →
    (∀ t ∈ Key.lawsAsk X₀ Z.lay m (descriptionFromSource X N P) (theKeyData (asDescriptionFiles Z)), t.2 = true) →
    (dataAtFiles flashProveData Z).G = bigReq m.p →
    LPFD.The21AtBase (dataAtFiles flashProveData Z).A (dataAtFiles flashProveData Z).E X N P (dataAtFiles flashProveData Z).DK

/-- What is owed at the written terms gives what is owed at letters. -/
theorem handedAtSeat_of_base (Z : PublicFiles) (h : The21AtSeat Z) : The21HandedAtSeat Z :=
  fun X₀ m X N P hX₀ hm hX hN hP hD hp hw ho ha hG =>
    LPFD.handed_of_base _ _ _ _ _ _ (h X₀ m X N P hX₀ hm hX hN hP hD hp hw ho ha hG)

/-- **THE ROW KeySound FROM ONE PREMISE, AT THE WRITTEN TERMS.** It takes MORE than
`keySound_of_handed`, which stands beside it for a payer with other letters. -/
theorem keySound_at_seat
    (the21 : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true → The21AtSeat Z) : KeySound :=
  keySound_of_handed fun Z hs hl => handedAtSeat_of_base Z (the21 Z hs hl)

/-- **The same AT THE SEVEN LETTERS THAT THE NAME FORCES**: the record, its reading off an instance,
the decoded table, its decoder and the event "the record does not single one table out" are the
configuration's own (Johnson/Top/Fire/Code/KeyAtName.lean); the payer holds the same facts. -/
def The21AtNameAtSeat (Z : PublicFiles) : Prop :=
  ∀ (X₀ : OnBytes.Model.Verify.Public) (m : Johnson.G.OfPlan.Made) (X : Source) (N : H2U.PlaceNums)
    (P : LaterPlaces),
    VerifiableInference.PlanWritten.publicOfO OnBytes.secondHashFunction Z.pol Z.KL (some Z.lay) = .ok X₀ →
    madeAt X₀ Z.lay fixedDigest = .ok m → sourceOf m = .ok X → rangesNumbers m = .ok N →
    laterPlaces m = .ok P →
    (descriptionFromSource X N P).data "key file" = .ok ((dataAtFiles flashProveData Z).DK.at frS.P.T.a) →
    (descriptionFromSource X N P).planOk = true → (descriptionFromSource X N P).wantedOk = true → (descriptionFromSource X N P).owedOk = true →
    (∀ t ∈ Key.lawsAsk X₀ Z.lay m (descriptionFromSource X N P) (theKeyData (asDescriptionFiles Z)), t.2 = true) →
    (dataAtFiles flashProveData Z).G = bigReq m.p →
    LPFD.The21AtName (dataAtFiles flashProveData Z).A (dataAtFiles flashProveData Z).E X N P (dataAtFiles flashProveData Z).DK

/-- What is owed at the name's seven gives what is owed at the written terms. -/
theorem atSeat_of_name (Z : PublicFiles) (h : The21AtNameAtSeat Z) : The21AtSeat Z :=
  fun X₀ m X N P hX₀ hm hX hN hP hD hp hw ho ha hG =>
    LPFD.base_of_name _ _ _ _ _ _ (h X₀ m X N P hX₀ hm hX hN hP hD hp hw ho ha hG)

/-- **THE ROW KeySound FROM ONE PREMISE, AT THE NAME's SEVEN.** It takes more than
`keySound_at_seat`, which takes more than `keySound_of_handed`: both stand beside it. -/
theorem keySound_at_name
    (the21 : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true → The21AtNameAtSeat Z) :
    KeySound :=
  keySound_at_seat fun Z hs hl => atSeat_of_name Z (the21 Z hs hl)

/-- **The same WITH ONE PUBLIC EQUATION IN THE PLACE OF THE FOUR FACTS ON BASES**: the record's data
of the key file are the written data (Johnson/Top/Fire/Code/KeyAtPin.lean); the payer holds the same
facts. -/
def The21AtPinAtSeat (Z : PublicFiles) : Prop :=
  ∀ (X₀ : OnBytes.Model.Verify.Public) (m : Johnson.G.OfPlan.Made) (X : Source) (N : H2U.PlaceNums)
    (P : LaterPlaces),
    VerifiableInference.PlanWritten.publicOfO OnBytes.secondHashFunction Z.pol Z.KL (some Z.lay) = .ok X₀ →
    madeAt X₀ Z.lay fixedDigest = .ok m → sourceOf m = .ok X → rangesNumbers m = .ok N →
    laterPlaces m = .ok P →
    (descriptionFromSource X N P).data "key file" = .ok ((dataAtFiles flashProveData Z).DK.at frS.P.T.a) →
    (descriptionFromSource X N P).planOk = true → (descriptionFromSource X N P).wantedOk = true → (descriptionFromSource X N P).owedOk = true →
    (∀ t ∈ Key.lawsAsk X₀ Z.lay m (descriptionFromSource X N P) (theKeyData (asDescriptionFiles Z)), t.2 = true) →
    (dataAtFiles flashProveData Z).G = bigReq m.p →
    LPFD.The21AtPin (dataAtFiles flashProveData Z).A (dataAtFiles flashProveData Z).E X N P (dataAtFiles flashProveData Z).DK

/-- In scope, what is owed with the equation gives what is owed at the name's seven. -/
theorem atName_of_pin (Z : PublicFiles) (hs : InScope Z = true) (h : The21AtPinAtSeat Z) :
    The21AtNameAtSeat Z :=
  fun X₀ m X N P hX₀ hm hX hN hP hD hp hw ho ha hG =>
    LPFD.name_of_pin _ _ _ hs (Johnson.RunOne.Law.ReadAtO.readOf_publicOfO hX₀) hm hX hp hw
      (h X₀ m X N P hX₀ hm hX hN hP hD hp hw ho ha hG)

/-- **THE ROW KeySound FROM ONE PREMISE, WITH THE EQUATION.** The lightest debt to list; the three
elder theorems stand beside it. -/
theorem keySound_at_pin
    (the21 : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true → The21AtPinAtSeat Z) :
    KeySound :=
  keySound_at_name fun Z hs hl => atName_of_pin Z hs (the21 Z hs hl)

/-- **THE EQUATION, AT THE SEAT**: in scope, where `protocolDataWellFormed` says yes, the record's data of the key
file are the written data: by `laid_data_written`
(Johnson/Goal/Numbers/KeySeatLaidAt.lean), which rests on the second test of the key file's door. -/
theorem pin_at_seat (Z : PublicFiles) (hs : InScope Z = true) (hl : protocolDataWellFormed (asDescriptionFiles Z) = true) :
    (dataAtFiles flashProveData Z).DK.at frS.P.T.a = Johnson.G.writtenKFull := by
  obtain ⟨K, -, -, hK, -, -⟩ := theLive_made (asDescriptionFiles Z) hl
  rw [dk_the Z hl, theKeyData_ok hK]
  exact VerifiableInference.PlanWritten.laid_data_written (r := K.2) hs hK

/-- **The same WITH THE EQUATION PAID**: beside the 21 laws two fields are left. -/
def The21LastAtSeat (Z : PublicFiles) : Prop :=
  ∀ (X₀ : OnBytes.Model.Verify.Public) (m : Johnson.G.OfPlan.Made) (X : Source) (N : H2U.PlaceNums)
    (P : LaterPlaces),
    VerifiableInference.PlanWritten.publicOfO OnBytes.secondHashFunction Z.pol Z.KL (some Z.lay) = .ok X₀ →
    madeAt X₀ Z.lay fixedDigest = .ok m → sourceOf m = .ok X → rangesNumbers m = .ok N →
    laterPlaces m = .ok P →
    (descriptionFromSource X N P).data "key file" = .ok ((dataAtFiles flashProveData Z).DK.at frS.P.T.a) →
    (descriptionFromSource X N P).planOk = true → (descriptionFromSource X N P).wantedOk = true → (descriptionFromSource X N P).owedOk = true →
    (∀ t ∈ Key.lawsAsk X₀ Z.lay m (descriptionFromSource X N P) (theKeyData (asDescriptionFiles Z)), t.2 = true) →
    (dataAtFiles flashProveData Z).G = bigReq m.p →
    LPFD.The21Last (dataAtFiles flashProveData Z).A (dataAtFiles flashProveData Z).E X N P (dataAtFiles flashProveData Z).DK

/-- **THE ROW KeySound FROM ONE PREMISE, WITH THE EQUATION PAID.** The lightest debt to list; the
four elder theorems stand beside it. -/
theorem keySound_at_last
    (the21 : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true → The21LastAtSeat Z) :
    KeySound :=
  keySound_at_pin fun Z hs hl X₀ m X N P hX₀ hm hX hN hP hD hp hw ho ha hG =>
    ⟨pin_at_seat Z hs hl, the21 Z hs hl X₀ m X N P hX₀ hm hX hN hP hD hp hw ho ha hG⟩

/-- **The same WITH THE LETTER tab WRITTEN AND THE FIRST BORDER's LAST FIELD PAID**
(Johnson/Top/Fire/Code/KeyAtTab.lean): beside the 21 laws one field is left. -/
def The21TabAtSeat (Z : PublicFiles) : Prop :=
  ∀ (X₀ : OnBytes.Model.Verify.Public) (m : Johnson.G.OfPlan.Made) (X : Source) (N : H2U.PlaceNums)
    (P : LaterPlaces),
    VerifiableInference.PlanWritten.publicOfO OnBytes.secondHashFunction Z.pol Z.KL (some Z.lay) = .ok X₀ →
    madeAt X₀ Z.lay fixedDigest = .ok m → sourceOf m = .ok X → rangesNumbers m = .ok N →
    laterPlaces m = .ok P →
    (descriptionFromSource X N P).data "key file" = .ok ((dataAtFiles flashProveData Z).DK.at frS.P.T.a) →
    (descriptionFromSource X N P).planOk = true → (descriptionFromSource X N P).wantedOk = true → (descriptionFromSource X N P).owedOk = true →
    (∀ t ∈ Key.lawsAsk X₀ Z.lay m (descriptionFromSource X N P) (theKeyData (asDescriptionFiles Z)), t.2 = true) →
    (dataAtFiles flashProveData Z).G = bigReq m.p →
    LPFD.The21Tab X N P (dataAtFiles flashProveData Z).DK

/-- In scope, what is owed at the written tab gives what is left when the bases are gone: the name's
claims are the claims on requests at the reference numbers. -/
theorem last_of_tab_at_seat (Z : PublicFiles) (hs : InScope Z = true) (h : The21TabAtSeat Z) :
    The21LastAtSeat Z :=
  fun X₀ m X N P hX₀ hm hX hN hP hD hp hw ho ha hG =>
    LPFD.last_of_tab _ hs (Johnson.RunOne.Law.ReadAtO.readOf_publicOfO hX₀) hm hX hp _
      (dataAtFiles flashProveData Z).E (h X₀ m X N P hX₀ hm hX hN hP hD hp hw ho ha hG)

/-- **THE ROW KeySound FROM ONE PREMISE, WITH THE FIRST BORDER PAID.** The lightest debt to list;
the five elder theorems stand beside it. -/
theorem keySound_at_tab
    (the21 : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true → The21TabAtSeat Z) :
    KeySound :=
  keySound_at_last fun Z hs hl => last_of_tab_at_seat Z hs (the21 Z hs hl)

/-- **The same WITH THE TWO LETTERS off₂ | off₃ WRITTEN** (Johnson/Top/Fire/Code/KeyAtOff.lean):
THE 21 LAWS AND NOTHING BESIDE THEM. -/
def The21OffAtSeat (Z : PublicFiles) : Prop :=
  ∀ (X₀ : OnBytes.Model.Verify.Public) (m : Johnson.G.OfPlan.Made) (X : Source) (N : H2U.PlaceNums)
    (P : LaterPlaces),
    VerifiableInference.PlanWritten.publicOfO OnBytes.secondHashFunction Z.pol Z.KL (some Z.lay) = .ok X₀ →
    madeAt X₀ Z.lay fixedDigest = .ok m → sourceOf m = .ok X → rangesNumbers m = .ok N →
    laterPlaces m = .ok P →
    (descriptionFromSource X N P).data "key file" = .ok ((dataAtFiles flashProveData Z).DK.at frS.P.T.a) →
    (descriptionFromSource X N P).planOk = true → (descriptionFromSource X N P).wantedOk = true → (descriptionFromSource X N P).owedOk = true →
    (∀ t ∈ Key.lawsAsk X₀ Z.lay m (descriptionFromSource X N P) (theKeyData (asDescriptionFiles Z)), t.2 = true) →
    (dataAtFiles flashProveData Z).G = bigReq m.p →
    LPFD.The21Off X N P (dataAtFiles flashProveData Z).DK

/-- **THE ROW KeySound FROM THE 21 LAWS ALONE**, at two letters (enc · rad). The six elder theorems
stand beside it. -/
theorem keySound_at_off
    (the21 : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true → The21OffAtSeat Z) :
    KeySound :=
  keySound_at_tab fun Z hs hl X₀ m X N P hX₀ hm hX hN hP hD hp hw ho ha hG =>
    LPFD.tab_of_off (the21 Z hs hl X₀ m X N P hX₀ hm hX hN hP hD hp hw ho ha hG)

/-- **The same WITH ROWS 1.0 AND 1.1 LAID IN** (Johnson/Top/Fire/Code/KeyAt19.lean): NINETEEN
LAWS. -/
def The19OffAtSeat (Z : PublicFiles) : Prop :=
  ∀ (X₀ : OnBytes.Model.Verify.Public) (m : Johnson.G.OfPlan.Made) (X : Source) (N : H2U.PlaceNums)
    (P : LaterPlaces),
    VerifiableInference.PlanWritten.publicOfO OnBytes.secondHashFunction Z.pol Z.KL (some Z.lay) = .ok X₀ →
    madeAt X₀ Z.lay fixedDigest = .ok m → sourceOf m = .ok X → rangesNumbers m = .ok N →
    laterPlaces m = .ok P →
    (descriptionFromSource X N P).data "key file" = .ok ((dataAtFiles flashProveData Z).DK.at frS.P.T.a) →
    (descriptionFromSource X N P).planOk = true → (descriptionFromSource X N P).wantedOk = true → (descriptionFromSource X N P).owedOk = true →
    (∀ t ∈ Key.lawsAsk X₀ Z.lay m (descriptionFromSource X N P) (theKeyData (asDescriptionFiles Z)), t.2 = true) →
    (dataAtFiles flashProveData Z).G = bigReq m.p →
    LPFD.The19Off X N P (dataAtFiles flashProveData Z).DK

/-- **THE ROW KeySound FROM NINETEEN LAWS**, at two letters (enc · rad). The seven elder theorems
stand beside it. -/
theorem keySound_at_19
    (the19 : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true → The19OffAtSeat Z) :
    KeySound :=
  keySound_at_off fun Z hs hl X₀ m X N P hX₀ hm hX hN hP hD hp hw ho ha hG =>
    LPFD.off_of_19 _ hs (Johnson.RunOne.Law.ReadAtO.readOf_publicOfO hX₀) hm hX hp hD
      (the19 Z hs hl X₀ m X N P hX₀ hm hX hN hP hD hp hw ho ha hG)

/-- **The same WITH THE ROWS OF ONE LIST LAID IN** (Johnson/Top/Fire/Code/KeyAtRest.lean):
the rows of the list LPFD.paidNow are struck; the others are owed. -/
def RestAtSeat (Z : PublicFiles) : Prop :=
  ∀ (X₀ : OnBytes.Model.Verify.Public) (m : Johnson.G.OfPlan.Made) (X : Source) (N : H2U.PlaceNums)
    (P : LaterPlaces),
    VerifiableInference.PlanWritten.publicOfO OnBytes.secondHashFunction Z.pol Z.KL (some Z.lay) = .ok X₀ →
    madeAt X₀ Z.lay fixedDigest = .ok m → sourceOf m = .ok X → rangesNumbers m = .ok N →
    laterPlaces m = .ok P →
    (descriptionFromSource X N P).data "key file" = .ok ((dataAtFiles flashProveData Z).DK.at frS.P.T.a) →
    (descriptionFromSource X N P).planOk = true → (descriptionFromSource X N P).wantedOk = true → (descriptionFromSource X N P).owedOk = true →
    (∀ t ∈ Key.lawsAsk X₀ Z.lay m (descriptionFromSource X N P) (theKeyData (asDescriptionFiles Z)), t.2 = true) →
    (dataAtFiles flashProveData Z).G = bigReq m.p →
    LPFD.RestOff LPFD.paidNow X N P (dataAtFiles flashProveData Z).DK

/-- **The row KeySound from the laws of the rows outside the list**, at two letters (enc · rad). The
list grows by a line a row; this theorem's name and text stay. The elder theorems stand beside it.
-/
theorem keySound_at_rest
    (rest : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true → RestAtSeat Z) :
    KeySound :=
  keySound_at_off fun Z hs hl X₀ m X N P hX₀ hm hX hN hP hD hp hw ho ha hG =>
    LPFD.off_of_rest _ hs (Johnson.RunOne.Law.ReadAtO.readOf_publicOfO hX₀) hm hX hp hw hD
      (pin_at_seat Z hs hl) (rest Z hs hl X₀ m X N P hX₀ hm hX hN hP hD hp hw ho ha hG)

end VerifierAndGoals.AtTheName

#print axioms VerifierAndGoals.AtTheName.dk_the
#print axioms VerifierAndGoals.AtTheName.The21HandedAtSeat
#print axioms VerifierAndGoals.AtTheName.keySound_of_handed
#print axioms VerifierAndGoals.AtTheName.The21AtSeat
#print axioms VerifierAndGoals.AtTheName.handedAtSeat_of_base
#print axioms VerifierAndGoals.AtTheName.keySound_at_seat
#print axioms VerifierAndGoals.AtTheName.The21AtNameAtSeat
#print axioms VerifierAndGoals.AtTheName.atSeat_of_name
#print axioms VerifierAndGoals.AtTheName.keySound_at_name
#print axioms VerifierAndGoals.AtTheName.The21AtPinAtSeat
#print axioms VerifierAndGoals.AtTheName.atName_of_pin
#print axioms VerifierAndGoals.AtTheName.keySound_at_pin
#print axioms VerifierAndGoals.AtTheName.pin_at_seat
#print axioms VerifierAndGoals.AtTheName.The21LastAtSeat
#print axioms VerifierAndGoals.AtTheName.keySound_at_last
#print axioms VerifierAndGoals.AtTheName.The21TabAtSeat
#print axioms VerifierAndGoals.AtTheName.last_of_tab_at_seat
#print axioms VerifierAndGoals.AtTheName.keySound_at_tab
#print axioms VerifierAndGoals.AtTheName.The21OffAtSeat
#print axioms VerifierAndGoals.AtTheName.keySound_at_off
#print axioms VerifierAndGoals.AtTheName.The19OffAtSeat
#print axioms VerifierAndGoals.AtTheName.keySound_at_19
#print axioms VerifierAndGoals.AtTheName.RestAtSeat
#print axioms VerifierAndGoals.AtTheName.keySound_at_rest
