-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- src_promise TAKES A SET I OF MEMBERS, in its premise on the record and in its conclusion (a chain's record need not hold every member's message at once).
/-
Johnson/Desc/Key/KeyFillSrc.lean: THE FILLING WITH THE SAMPLE READ OFF A MESSAGE's OWN RECORD. famG (Johnson/Desc/Key/KeyFillFam.lean) takes the sample by a letter seedIs i on the chain's WHOLE record, at the member of the seat. The tables' one reading (BaseSt,
Johnson/RunOne/KeyOneReading.lean) fixes another form: the tenant's number in the witness (arr) ↦ a statement's message ↦ a letter sm that is handed the statement's codes, THE STATEMENT's number of the message and the message's own record: NEITHER THE SEAT NOR THE TABLES' NUMBER.
Here, free of the tables' states: a reading of that form whose arr | lay | enc | rad | meets are famG's, and the theorems of the filling at it.
  famArr · famArr_seat     one number, one seat: the tenant at member i's seat bears num i
  ShapesApart · smFam      sm, filled: at the codes cs: THE MEMBER IS TOLD BY THE RECORD's SHAPE (so the family's shapes must differ pairwise); some sample with rowIs, by choice. rowIs i o x ρ v: a letter: the record x, as message number o, spells the seed ρ and the answers v
  mkG · smpOf · seedIsS    the reading with famG's five fields and any smp · src a k: which (codes, number, record) is read for the witness's message k at the record a · the tie that it gives on whole records
  smp_eq                   AT A RECORD THAT HOLDS THE MEMBER's MESSAGE AT ITS SHAPE AND AT cs, the sample at the seat is famG's at the tie seedIsS: the two choices are one term, the predicates being equal AS PREDICATES
  uniq_seedIsS             (uniq) of the tie from (uniq) of rowIs
  src_seals · src_lays     SealReads | LaysReads at that reading, at every member
  src_promise              PIN ∧ hasSmp ∧ NoColl AT THE SEATS OF A SET I OF MEMBERS: those whose message the record holds: at the rule's own oracles, at the laying by the pad's places, at that reading. ONE y', ONE witness serve all members whatever I is
OBJECT: none: a filling of letters · USER: Johnson/RunOne/KeyFillBase.lean · LETTERS: cs · l · seat · num · rowIs · src · decT · recOf.
NOT SAID: rowIs off a real record's rows (left to other files), its (uniq), or that a sending's block lays a message's answers there. AT A FAMILY WITH ONE SHAPE TWICE smFam NAMES ONE OF THE TWO: smp_eq fails at the other. At l := [] all is true for nothing.
Nothing on soundness.
-/
import Johnson.Desc.Key.KeyFillLay
import Johnson.Desc.Key.KeyFillFamLays

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Key.Fill
open VerifiableInference.Desc VerifiableInference.Desc.Sound
open Cb Johnson.Pack OnBytes.Slice Prob OnBytes.Maker

theorem dite_choose_congr {α β : Type} (p q : α → Prop) (h : p = q) (f : α → β) [Decidable (∃ z, p z)] [Decidable (∃ z, q z)] :
    (if h' : ∃ z, p z then some (f h'.choose) else none) = (if h' : ∃ z, q z then some (f h'.choose) else none) := by
  subst h
  by_cases hz : ∃ z, p z
  · rw [dif_pos hz, dif_pos hz]
  · rw [dif_neg hz, dif_neg hz]

variable (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ)) (seat : Fin l.length → ℕ × ℕ) (num : Fin l.length → ℕ)
  (rowIs : ∀ i : Fin l.length, ℕ → OnBytes.Oracle → (OmAt cs l i).Z.D → ((OmAt cs l i).Z.S → GE) → Prop)

open Classical in
/-- One number, one seat. -/
def famArr : ℕ → ℕ → ℕ := fun j t => if h : ∃ i : Fin l.length, seat i = (j, t) then num h.choose else 0

theorem famArr_seat (hinj : Function.Injective seat) (i : Fin l.length) : famArr l seat num (seat i).1 (seat i).2 = num i := by
  classical
  have h : ∃ i' : Fin l.length, seat i' = ((seat i).1, (seat i).2) := ⟨i, rfl⟩
  show (if h : ∃ i' : Fin l.length, seat i' = ((seat i).1, (seat i).2) then num h.choose else 0) = _
  rw [dif_pos h, choose_seat l seat hinj i h]

/-- The family's shapes differ pairwise. -/
def ShapesApart : Prop := ∀ i i' : Fin l.length, (l.get i).1 = (l.get i').1 → i = i'

open Classical in
/-- **sm, filled**: the member by the record's shape. -/
def smFam : OnBytes.Codes → ℕ → OnBytes.Oracle → Option (Σ i : Fin l.length, (OmAt cs l i).Smp) := fun c o x =>
  if c = cs then
    (if h : ∃ i : Fin l.length, (l.get i).1 = x.shape then
      (if h' : ∃ z : (OmAt cs l h.choose).Smp, rowIs h.choose o x z.1 z.2 then some ⟨h.choose, h'.choose⟩ else none) else none)
  else none

open Classical in
theorem smFam_spec (hap : ShapesApart l) (i : Fin l.length) (o : ℕ) (x : OnBytes.Oracle) (hx : x.shape = (l.get i).1) :
    smFam cs l rowIs cs o x = if h' : ∃ z : (OmAt cs l i).Smp, rowIs i o x z.1 z.2 then some (⟨i, h'.choose⟩ : Σ i : Fin l.length, (OmAt cs l i).Smp) else none := by
  have h : ∃ i' : Fin l.length, (l.get i').1 = x.shape := ⟨i, hx.symm⟩
  show (if cs = cs then
    (if h : ∃ i' : Fin l.length, (l.get i').1 = x.shape then
      (if h' : ∃ z : (OmAt cs l h.choose).Smp, rowIs h.choose o x z.1 z.2 then some (⟨h.choose, h'.choose⟩ : Σ i : Fin l.length, (OmAt cs l i).Smp) else none) else none)
    else none) = _
  rw [if_pos rfl, dif_pos h]
  have hc : h.choose = i := hap _ _ (h.choose_spec.trans hx)
  generalize h.choose = i' at hc
  subst hc
  rfl

variable {A Cells Rec : Type} (arr : ℕ → ℕ → ℕ) (lay : ℕ → ℕ → Tab → Tab → Tab) (decT : (ℕ → Option (ℕ × List UInt64)) → Rec → Option Cells) (recOf : A → Option Rec)
  (src : A → ℕ → Option (OnBytes.Codes × ℕ × OnBytes.Oracle))

/-- The reading with famG's arr | lay | enc | rad | meets | decT | recOf and any smp. -/
def mkG (smp : A → ℕ → ℕ → Option (Σ i : Fin l.length, (OmAt cs l i).Smp)) : Reading A Cells Tab (Σ i : Fin l.length, (OmAt cs l i).Smp) Rec :=
  { famG cs l seat (fun _ _ _ _ => False) arr lay decT recOf with smp := smp }

/-- The sample in the tables' form: the tenant's number ↦ a record ↦ sm. -/
def smpOf : A → ℕ → ℕ → Option (Σ i : Fin l.length, (OmAt cs l i).Smp) := fun a j t => (src a (arr j t)).bind fun q => smFam cs l rowIs q.1 q.2.1 q.2.2

/-- The tie on whole records that it gives. -/
def seedIsS (i : Fin l.length) (a : A) (ρ : (OmAt cs l i).Z.D) (v : (OmAt cs l i).Z.S → GE) : Prop :=
  ∃ o x, src a (num i) = some (cs, o, x) ∧ x.shape = (l.get i).1 ∧ rowIs i o x ρ v

open Classical in
theorem fam_smp_form (seedIs : ∀ i : Fin l.length, A → (OmAt cs l i).Z.D → ((OmAt cs l i).Z.S → GE) → Prop) (hinj : Function.Injective seat) (i : Fin l.length) (a : A) :
    (famG cs l seat seedIs arr lay decT recOf).smp a (seat i).1 (seat i).2 =
      if h' : ∃ z : (OmAt cs l i).Smp, seedIs i a z.1 z.2 then some (⟨i, h'.choose⟩ : Σ i : Fin l.length, (OmAt cs l i).Smp) else none := by
  have h : ∃ i' : Fin l.length, seat i' = ((seat i).1, (seat i).2) := ⟨i, rfl⟩
  show (if h : ∃ i' : Fin l.length, seat i' = ((seat i).1, (seat i).2) then
      (if h' : ∃ z : (OmAt cs l h.choose).Smp, seedIs h.choose a z.1 z.2 then some (⟨h.choose, h'.choose⟩ : Σ i : Fin l.length, (OmAt cs l i).Smp) else none) else none) = _
  rw [dif_pos h]
  have hc := choose_seat l seat hinj i h
  generalize h.choose = i' at hc
  subst hc
  rfl

/-- **The sample at the seat is famG's at the tie seedIsS.** -/
theorem smp_eq (hinj : Function.Injective seat) (hap : ShapesApart l) (harr : ∀ i, arr (seat i).1 (seat i).2 = num i) (i : Fin l.length) (a : A) (o : ℕ) (x : OnBytes.Oracle)
    (hsrc : src a (num i) = some (cs, o, x)) (hx : x.shape = (l.get i).1) :
    smpOf cs l rowIs arr src a (seat i).1 (seat i).2 = (famG cs l seat (seedIsS cs l num rowIs src) arr lay decT recOf).smp a (seat i).1 (seat i).2 := by
  classical
  rw [fam_smp_form cs l seat arr lay decT recOf _ hinj i a]
  show ((src a (arr (seat i).1 (seat i).2)).bind fun q => smFam cs l rowIs q.1 q.2.1 q.2.2) = _
  rw [harr i, hsrc]
  show smFam cs l rowIs cs o x = _
  rw [smFam_spec cs l rowIs hap i o x hx]
  have hp : (fun z : (OmAt cs l i).Smp => rowIs i o x z.1 z.2) = fun z : (OmAt cs l i).Smp => seedIsS cs l num rowIs src i a z.1 z.2 := by
    funext z
    refine propext ⟨fun h => ⟨o, x, hsrc, hx, h⟩, ?_⟩
    rintro ⟨o', x', h1, _, h3⟩
    have e := Option.some.inj (hsrc.symm.trans h1)
    have e1 : o = o' := congrArg (fun q => q.2.1) e
    have e2 : x = x' := congrArg (fun q => q.2.2) e
    subst e1
    subst e2
    exact h3
  exact dite_choose_congr _ _ hp fun z => (⟨i, z⟩ : Σ i : Fin l.length, (OmAt cs l i).Smp)

theorem uniq_seedIsS (i : Fin l.length)
    (uniqR : ∀ o x ρ v ρ' v', rowIs i o x ρ v → rowIs i o x ρ' v' → (OmAt cs l i).Z.val ρ = (OmAt cs l i).Z.val ρ' ∧ v = v') :
    ∀ (a : A) ρ v ρ' v', seedIsS cs l num rowIs src i a ρ v → seedIsS cs l num rowIs src i a ρ' v' → (OmAt cs l i).Z.val ρ = (OmAt cs l i).Z.val ρ' ∧ v = v' := by
  rintro a ρ v ρ' v' ⟨o, x, h1, _, h3⟩ ⟨o', x', h1', _, h3'⟩
  have e := Option.some.inj (h1.symm.trans h1')
  have e1 : o = o' := congrArg (fun q => q.2.1) e
  have e2 : x = x' := congrArg (fun q => q.2.2) e
  subst e1
  subst e2
  exact uniqR o x ρ v ρ' v' h3 h3'

variable {XI Y' : Type} (F : FileDescription XI) (str : Y' → Strs)

/-- **THE UPPER HALF at the reading in the tables' form, at every member.** -/
def src_seals (hinj : Function.Injective seat) (hap : ShapesApart l) (harr : ∀ i, arr (seat i).1 (seat i).2 = num i) (i : Fin l.length)
    (hlog : ∀ o, F.oracleAt (seat i).1 = some o → o.logLength = aOf cs (l.get i).1) (hm : (l.get i).1.mainRows = 0 ∨ (cMain cs (l.get i).1).a = aOf cs (l.get i).1)
    (uniqR : ∀ o x ρ v ρ' v', rowIs i o x ρ v → rowIs i o x ρ' v' → (OmAt cs l i).Z.val ρ = (OmAt cs l i).Z.val ρ' ∧ v = v') :
    SealReads F (mkG cs l seat arr lay decT recOf (smpOf cs l rowIs arr src)) str
      (fun y' => (OmAt cs l i).InList (symsW cs (l.get i).1 (l.get i).2 (wordOf F (str y') (seat i).1 (seat i).2)))
      (OmAt cs l i).Z.val (seedIsS cs l num rowIs src i) (seat i).1 (seat i).2 where
  toU := toU cs (l.get i).1 (l.get i).2
  has := fun a ρ y hs => by
    obtain ⟨o, x, h1, h2, _⟩ := id hs
    show (smpOf cs l rowIs arr src a (seat i).1 (seat i).2).isSome = true
    rw [smp_eq cs l seat num rowIs arr lay decT recOf src hinj hap harr i a o x h1 h2]
    exact (fam_seals cs l seat (seedIsS cs l num rowIs src) arr lay decT recOf hinj F str i hlog hm (uniq_seedIsS cs l num rowIs src i uniqR)).has a ρ y hs
  inj := fun a y' o z m m' _ _ hM hM' he => by
    obtain ⟨⟨_, hE, _⟩, _⟩ := hM
    obtain ⟨⟨_, hE', _⟩, _⟩ := hM'
    exact toU_inj cs _ _ (fam_enc (o := o) cs l seat (seedIsS cs l num rowIs src) arr lay decT recOf hinj i hE).1 (fam_enc (o := o) cs l seat (seedIsS cs l num rowIs src) arr lay decT recOf hinj i hE').1 he
  mem := fun a y' o z m ρ y ho hz hs hM => by
    obtain ⟨o', x, h1, h2, _⟩ := id hs
    exact (fam_seals cs l seat (seedIsS cs l num rowIs src) arr lay decT recOf hinj F str i hlog hm (uniq_seedIsS cs l num rowIs src i uniqR)).mem a y' o z m ρ y ho
      ((smp_eq cs l seat num rowIs arr lay decT recOf src hinj hap harr i a o' x h1 h2).symm.trans hz) hs hM

/-- **THE LOWER HALF at that reading, at every member.** -/
def src_lays (hinj : Function.Injective seat) (hap : ShapesApart l) (harr : ∀ i, arr (seat i).1 (seat i).2 = num i) (i : Fin l.length)
    (hlog : ∀ o, F.oracleAt (seat i).1 = some o → o.logLength = aOf cs (l.get i).1) (hm : (l.get i).1.mainRows = 0 ∨ (cMain cs (l.get i).1).a = aOf cs (l.get i).1)
    (uniqR : ∀ o x ρ v ρ' v', rowIs i o x ρ v → rowIs i o x ρ' v' → (OmAt cs l i).Z.val ρ = (OmAt cs l i).Z.val ρ' ∧ v = v')
    (told : (F.oracleAt (seat i).1).isSome = true) :
    LaysReads F (mkG cs l seat arr lay decT recOf (smpOf cs l rowIs arr src)) str
      (fun y' => (OmAt cs l i).InList (symsW cs (l.get i).1 (l.get i).2 (wordOf F (str y') (seat i).1 (seat i).2)))
      (OmAt cs l i).Z.val (seedIsS cs l num rowIs src i) (fun y' => Sound.ShownAt F cs l seat (str y') i) (seat i).1 (seat i).2 (toU cs (l.get i).1 (l.get i).2) where
  ofU := ofU cs (l.get i).1 (l.get i).2
  sec := fun _ u _ => toU_ofU cs (l.get i).1 (l.get i).2 u
  told := told
  mem := fun a y' o z u ρ y ho hz hs hsh hc => by
    obtain ⟨o', x, h1, h2, _⟩ := id hs
    exact (fam_lays cs l seat (seedIsS cs l num rowIs src) arr lay decT recOf hinj F str i hlog hm (uniq_seedIsS cs l num rowIs src i uniqR) told).mem a y' o z u ρ y ho
      ((smp_eq cs l seat num rowIs arr lay decT recOf src hinj hap harr i a o' x h1 h2).symm.trans hz) hs hsh hc

/-- **PIN AND ITS PROMISE AT THE SEATS OF A SET I OF MEMBERS, AT THE RULE's OWN ORACLES, AT THE LAYING BY THE PAD's PLACES, AT THE READING IN THE TABLES' FORM.** I: the members whose message the record a holds. -/
theorem src_promise (I : Fin l.length → Prop) (Fr : Frame) (hinj : Function.Injective seat) (hap : ShapesApart l) (hnum : Function.Injective num) (harr : ∀ i, arr (seat i).1 (seat i).2 = num i)
    (hS : SeatFits F cs l seat) (hFr : FrameHolds cs l seat Fr)
    (uniqR : ∀ i o x ρ v ρ' v', rowIs i o x ρ v → rowIs i o x ρ' v' → (OmAt cs l i).Z.val ρ = (OmAt cs l i).Z.val ρ' ∧ v = v')
    (hB : allMeet cs l = true) (y₀ : Fr.E.Str) (a : A) (m₀ : ∀ i : Fin l.length, (OmAt cs l i).Msg)
    (r₀ : ∀ i : Fin l.length, (OmAt cs l i).Rnd) (ρ : ∀ i : Fin l.length, (OmAt cs l i).Z.D)
    (hsend : ∀ i, Sendable cs (l.get i).1 (l.get i).2 (m₀ i, r₀ i)) (hs : ∀ i, I i → seedIsS cs l num rowIs src i a (ρ i) ((OmAt cs l i).Z.val (ρ i) (m₀ i))) (c₀ : Cells) :
    ∃ (W : Wit Cells Unit Tab) (y' : Fr.E.Str), y'.1 = y₀.1 ∧ ∀ i : Fin l.length, I i →
      PIN F (mkG cs l seat arr (famLay cs l seat) decT recOf (smpOf cs l rowIs arr src)) (seat i).1 (seat i).2 a (strsOf Fr y') W ∧
      hasSmp (mkG cs l seat arr (famLay cs l seat) decT recOf (smpOf cs l rowIs arr src)) (seat i).1 (seat i).2 a = true ∧
      NoColl F (mkG cs l seat arr (famLay cs l seat) decT recOf (smpOf cs l rowIs arr src)) (seat i).1 (seat i).2 a (strsOf Fr y') := by
  choose f hf using fun i => sent_of cs (l.get i).1 (l.get i).2 (m₀ i, r₀ i) (hsend i)
  obtain ⟨y', h1, hy⟩ := exists_oracles cs l seat F Fr hinj hS hFr y₀ f
  obtain ⟨W, hW⟩ := (fam_hW_iff cs l seat (seedIsS cs l num rowIs src) arr decT recOf hinj c₀ () _).2
    (agreeOff_of_apart cs l seat arr (fun i => ofU cs (l.get i).1 (l.get i).2 (m₀ i)) fun i i' e => hnum (by rw [← harr i, ← harr i', e]))
  refine ⟨W, y', h1, fun i hi => ?_⟩
  obtain ⟨hsh, _, hsy⟩ := hy i
  obtain ⟨o, _, ho, _, hlog, _, _, hm, _, _⟩ := hS i
  have hL : ∀ o', F.oracleAt (seat i).1 = some o' → o'.logLength = aOf cs (l.get i).1 := fun o' ho' => by
    obtain rfl : o' = o := Option.some.inj (ho'.symm.trans ho)
    exact hlog
  have hw : (OmAt cs l i).upW (symsW cs (l.get i).1 (l.get i).2 (wordOf F (strsOf Fr y') (seat i).1 (seat i).2)) = (OmAt cs l i).C.enc (m₀ i) (r₀ i) := by
    rw [hsy]
    exact hf i
  have hu := uniq_seedIsS cs l num rowIs src i (uniqR i)
  obtain ⟨hh, hn⟩ := fam_noColl_honest cs l seat F (seedIsS cs l num rowIs src) arr (famLay cs l seat) decT recOf hinj i hL hm hu _ _ (allMeet_sound cs l hB i) a (strsOf Fr y')
    (m₀ i) (r₀ i) (ρ i) _ (hs i hi) hw
  obtain ⟨z, hz⟩ := Option.isSome_iff_exists.1 hh
  have hM := fam_honest_member cs l seat F (seedIsS cs l num rowIs src) arr (famLay cs l seat) decT recOf hinj i hL hm hu a (strsOf Fr y') o z (m₀ i) (r₀ i) (ρ i) ho hz (hs i hi) hsh hw
  obtain ⟨o', x, e1, e2, _⟩ := id (hs i hi)
  have heq := smp_eq cs l seat num rowIs arr (famLay cs l seat) decT recOf src hinj hap harr i a o' x e1 e2
  refine ⟨⟨o, z, ho, heq.trans hz, ?_⟩, ?_, fun o z ho hz m m' hm hm' => hn o z ho (heq.symm.trans hz) m m' hm hm'⟩
  · show Member F (famG cs l seat (seedIsS cs l num rowIs src) arr (famLay cs l seat) decT recOf) o (seat i).1 (seat i).2 (strsOf Fr y') z
      (msgOf (famG cs l seat (seedIsS cs l num rowIs src) arr (famLay cs l seat) decT recOf) W (seat i).1 (seat i).2)
    rw [hW i]
    exact hM
  · show (smpOf cs l rowIs arr src a (seat i).1 (seat i).2).isSome = true
    rw [heq]
    exact hh

end VerifiableInference.Desc.Key.Fill

#print axioms VerifiableInference.Desc.Key.Fill.famArr_seat
#print axioms VerifiableInference.Desc.Key.Fill.smFam_spec
#print axioms VerifiableInference.Desc.Key.Fill.fam_smp_form
#print axioms VerifiableInference.Desc.Key.Fill.smp_eq
#print axioms VerifiableInference.Desc.Key.Fill.uniq_seedIsS
#print axioms VerifiableInference.Desc.Key.Fill.src_seals
#print axioms VerifiableInference.Desc.Key.Fill.src_lays
#print axioms VerifiableInference.Desc.Key.Fill.src_promise
