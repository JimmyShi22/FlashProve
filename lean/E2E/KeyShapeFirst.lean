--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyShapeFirst.lean: THE KEY FILE'S FIRST CHAIN, CUT IN TWO: STRUCTURE | VALUES: THE SHAPE, ITS
READER, AND FOUR SUB-PROTOCOLS OF A LOOKUP'S LINK. The cut is
Johnson/Desc/ProofFile/Honest/Thread/Shape.lean's: a verifier's state is read onto its SHAPE
(numbers, flags, lists of these; no field element); each sub-protocol's tests on the structure are
written as a function g of the shape alone; what is left are its named tests on values. Owed at
each: (B1) where its step accepts and g returns, g returns the shape behind; (B2) where g returns
and the named tests on values pass, its decision returns. Definitions, statements and proofs.
NOTHING IS SHOWN OF ANY PROVER: no completeness.

THE SHAPE. `Sh₁ Bk := CoreSh × LocSh Bk`. `CoreSh` (Johnson/Desc/Ground/Shape/Core.lean): statement,
book of trees and count of roots without a field element and without a row's summands. `LocSh Bk`:
the chain's six named numbers and flags, one mark on the statement (tidy), what is left of the
lookups' structure (`LookSh`), and the shape Bk of what the chain's back half writes (a type
parameter; its reader reads the rows on the table, what W's sending announces, the numbers sent with
W and the linear claim's first part alone: `BackOf`). The reader `sh₁ Q bk` is taken at the chain's
public values and the setting (`Pub1`). `LookSh`: the open ledger's shape (`LedSh`,
Johnson/Desc/First/Shape/Parts.lean), held until the lookup's claims are gathered · what is
left of what was heard (`HeardSh`) · the hidden values' homes (slots: two numbers each) · a count of
rows for each lookup · of each claim on a part's keys the slots that its mask form names
(`keysSlots`, E2E/KeyShapeKeys.lean) · two marks.

THE FOUR MARKS. Each is meant AS A MARK THAT THE SUB-PROTOCOLS CARRY: g asks it and hands it on or
lays it, and NEVER COMPUTES IT in a run on shapes; the readers are for the laws alone. WHICH VALUES
THE READERS READ:
  tidy (`stTidyB`, Johnson/Desc/Ground/Shape/Marks.lean): at one spot, said in that file's head.
  plain (`plainRowB`: every row that the lookups have written is `LookupShapedRow`, E2E/KeyRowsFit.lean):
  kinds, places, indices,
    numbers of variables; of a term's vector the test `tensorInOrder`, which compares a written-out
    variable's pair with (1, 1): idle at these rows, which have no written-out variable.
  keysOk (`keysB`, E2E/KeyShapeKeys.lean): lengths and lists of numbers of variables: no value.
  the mark on what was heard (`heardB`): the ten facts `Left` (E2E/KeyLookupAround.lean) and `Off`
  of the rows' forms and of the three
    claims' leads: counts, marks in the ledger, and which slots a form names. ITS READER RUNS THE
    LIBRARY'S `planesG`, which computes with field elements; that its returning hangs on no value is
    BY READING: no theorem says it.

What is shown here.
  `plainRowB_iff`, `zip_homesFrom`, `homesFrom_split`, `off_of_B`, `offB_of`: the tests' meanings; a
    list of homes, one for each mark, is made of its members by their marks.
  `takeMasks_tidy`: the taking of several mask entries keeps the mark on the statement.
  `both_of_exact`: ONE EXACT LEMMA GIVES BOTH FORMS: if, where g returns at a state's shape, the run
    returns a state of the shape that g returns, then (B1r) and (B2r) hold, with no test on values.
  **`laid_exact`** (`gLaid`), **`behind_exact`**, **`cleared_exact`** (`gCleared`),
    **`caller_exact`** (`gCaller`; `freshLed`, `ledSh_fresh`): such lemmas for a link's three own
    steps and for the sub-protocol in front of a lookup's rounds. NONE OF THE FOUR NEEDS A TEST ON
    VALUES.

Limits.
- The two sendings, the lookup's own sub-protocol, the sub-protocol behind its rounds and the
  chain's back half are not here ("rng.0.rows": E2E/KeyShapeLayRows.lean). No shape's run is
  evaluated.
- `gCaller` asks the mark tidy, which the sub-protocol itself does not ask: sufficient, not
  necessary.
- That a shape is blind to what is sent and sampled is so by type for field elements alone.
- Nothing on completeness, on soundness or on what is hidden.


-/
import E2E.KeyRowsFit
import E2E.KeyShapeKeys
import Johnson.Desc.Ground.Shape.Marks
import Johnson.Desc.Ground.Shape.More
import Johnson.Desc.First.Shape.Parts
import Johnson.Desc.ProofFile.Honest.Thread.ShapeJoin

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.KeyShape
open OnBytes
open OnBytes.Model (Fork Aff)
open ProofFile.Honest (CarriesR ReturnsR)
open VerifiableInference.Desc (Block named need Key.quietAt)
open VerifiableInference.Desc.K3
open VerifiableInference.Desc.Key
open VerifiableInference.Desc.Ground (takeMaskP takeMasksInto takeMasksP)
open VerifiableInference.Desc.Ground.Sh
open VerifiableInference.Desc.First.Shape (LedSh ledSh)
open _root_.Desc.Plain (DState)
open AtPublicFiles.KeyLookup AtPublicFiles.RowsFit

/-! ## 1. The public numbers -/

/-- The lookups' own message's number. -/
abbrev msgOf (one : Params.OneTime) : ℕ := one.ranges.messageId

/-- The entries of the own message's mask table. -/
def sizeB (one : Params.OneTime) : ℕ :=
  2 ^ (ceilLog2 one.ranges.message.shape.maskRows +
    (one.codes.mask.getD one.ranges.message.shape.maskCode default).logEll)

/-- The first entry of its pad. -/
def padP (one : Params.OneTime) : ℕ := padFirst one.codes one.ranges.message.shape

/-- The index bits of its main table. -/
def bitsV (one : Params.OneTime) : ℕ :=
  ceilLog2 one.ranges.message.shape.mainRows +
    (one.codes.base.getD one.ranges.message.shape.code default).logEll

/-- Lookup number i. -/
def lookAt (one : Params.OneTime) (i : ℕ) : Lookup := (lookupsOf one).getD i default

/-! ## 2. The marks' tests -/

/-- A mask entry of the own message, inside its table and in front of its pad. -/
def ownOk (one : Params.OneTime) (h : Slot) : Bool :=
  h.oracle == msgOf one && decide (h.index < sizeB one) && decide (h.index < padP one)

/-- Every hidden value has a home, and each that is not marked for the index-mask message lies on
the own message, inside its table and in front of its pad. -/
def homesB (one : Params.OneTime) (f : Face) (home : List Slot) : Bool :=
  home.length == f.slots && ((fromKeys f).zip home).all fun p => p.1 || ownOk one p.2

/-- The test for `LookupShapedRow`. -/
def plainRowB (msg B P V : ℕ) (r : Row) : Bool :=
  r.kind == .plain && r.runs.isEmpty && r.forms.isEmpty &&
    (r.units.toList.all fun u =>
      u.oracle == msg && u.part == .mask && decide (u.index < B) && decide (u.index < P)) &&
    r.terms.toList.all fun t =>
      t.oracle == msg && t.part == .main && VerifiableInference.Desc.Own.tensorInOrder t.v &&
        t.v.vars == V

theorem plainRowB_iff {msg B P V : ℕ} {r : Row} :
    plainRowB msg B P V r = true ↔ LookupShapedRow msg B P V r := by
  unfold plainRowB
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    Array.isEmpty_iff]
  constructor
  · rintro ⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩
    exact ⟨a, b, c, fun u hu => ⟨(d u hu).1.1.1, (d u hu).1.1.2, (d u hu).1.2, (d u hu).2⟩,
      fun t ht => ⟨(e t ht).1.1.1, (e t ht).1.1.2, (e t ht).1.2, (e t ht).2⟩⟩
  · rintro ⟨a, b, c, d, e⟩
    exact ⟨⟨⟨⟨a, b⟩, c⟩,
        fun u hu => ⟨⟨⟨(d u hu).1, (d u hu).2.1⟩, (d u hu).2.2.1⟩, (d u hu).2.2.2⟩⟩,
      fun t ht => ⟨⟨⟨(e t ht).1, (e t ht).2.1⟩, (e t ht).2.2.1⟩, (e t ht).2.2.2⟩⟩

/-- What is marked false lies among o. -/
theorem zip_homesFrom (c : Slot → Bool) : ∀ (bs : List Bool) (o k : List Slot),
    (∀ s ∈ o, c s = true) → ((bs.zip (homesFrom bs o k)).all fun p => p.1 || c p.2) = true
  | [], _, _, _ => rfl
  | false :: _, [], _, _ => rfl
  | true :: _, _, [], _ => rfl
  | false :: bs, s :: o, k, h => by
    show ((false || c s) && ((bs.zip (homesFrom bs o k)).all fun p => p.1 || c p.2)) = true
    rw [zip_homesFrom c bs o k fun t ht => h t (List.mem_cons_of_mem _ ht),
      h s List.mem_cons_self]
    rfl
  | true :: bs, [], s :: k, h => by
    show ((true || c s) && ((bs.zip (homesFrom bs [] k)).all fun p => p.1 || c p.2)) = true
    rw [zip_homesFrom c bs [] k h]
    rfl
  | true :: bs, a :: o, s :: k, h => by
    show ((true || c s) && ((bs.zip (homesFrom bs (a :: o) k)).all fun p => p.1 || c p.2)) = true
    rw [zip_homesFrom c bs (a :: o) k h]
    rfl

/-- A list of homes, one for each mark, is made of its members by their marks. -/
theorem homesFrom_split (c : Slot → Bool) : ∀ (bs : List Bool) (l : List Slot),
    l.length = bs.length → ((bs.zip l).all fun p => p.1 || c p.2) = true →
    ∃ o k, homesFrom bs o k = l ∧ ∀ s ∈ o, c s = true
  | [], [], _, _ => ⟨[], [], rfl, fun _ h => absurd h List.not_mem_nil⟩
  | [], _ :: _, h, _ => by cases h
  | _ :: _, [], h, _ => by cases h
  | false :: bs, s :: l, hl, h => by
    have h' : ((false || c s) && ((bs.zip l).all fun p => p.1 || c p.2)) = true := h
    rw [Bool.and_eq_true, Bool.false_or] at h'
    obtain ⟨o, k, e, ho⟩ := homesFrom_split c bs l (Nat.succ.inj hl) h'.2
    refine ⟨s :: o, k, ?_, fun t ht => ?_⟩
    · show s :: homesFrom bs o k = _
      rw [e]
    · rcases List.mem_cons.1 ht with rfl | ht
      · exact h'.1
      · exact ho t ht
  | true :: bs, s :: l, hl, h => by
    have h' : ((true || c s) && ((bs.zip l).all fun p => p.1 || c p.2)) = true := h
    rw [Bool.and_eq_true] at h'
    obtain ⟨o, k, e, ho⟩ := homesFrom_split c bs l (Nat.succ.inj hl) h'.2
    refine ⟨o, s :: k, ?_, ho⟩
    cases o with
    | nil => show s :: homesFrom bs [] k = _; rw [e]
    | cons a o => show s :: homesFrom bs (a :: o) k = _; rw [e]

/-- The test for `Off`. -/
def offB (f : Face) (lo : ℕ) (a : Aff) : Bool :=
  a.slots.toList.all fun x => markAt f lo x.1 == false

theorem off_of_B {f : Face} {lo : ℕ} {a : Aff} (h : offB f lo a = true) : Off f lo a := fun x hx =>
  eq_of_beq (List.all_eq_true.1 h x hx)

theorem offB_of {f : Face} {lo : ℕ} {a : Aff} (h : Off f lo a) : offB f lo a = true :=
  List.all_eq_true.2 fun x hx => beq_iff_eq.2 (h x hx)

/-! ## 3. The shape -/

/-- **What is left of what a lookup's sub-protocol has heard.** mark: THE MARK (`heardB`). rows: the
number of the forms of rows. keys: for each claim on a part's keys: its point's length, and the
slots that its form names. -/
structure HeardSh where
  mark : Bool
  rows : ℕ
  keys : List (ℕ × List ℕ)

/-- **What is left of the lookups' structure** (`LookupRecord`, Johnson/Desc/Key/Link.lean). led: no
ledger is open; or one is, with its shape UNTIL THE LOOKUP'S CLAIMS ARE GATHERED, without it behind.
home: the hidden values' homes. rows: a count for each lookup. plain, keysOk: TWO MARKS. keys: of
each claim on a part's keys the slots that its mask form names. -/
structure LookSh where
  led : Option (Option LedSh)
  heard : Option HeardSh
  home : List Slot
  rows : List ℕ
  plain : Bool
  keys : List (List (List Slot))
  keysOk : Bool

/-- **The first chain's named values.** Bk: the shape of what the chain's back half writes. -/
structure LocSh (Bk : Type) where
  owed : Option ℕ
  sent : List ℕ
  idx : ℕ
  grp : ℕ
  rider : Option ℕ
  atEnd : Bool
  tidy : Bool
  look : LookSh
  back : Bk

/-- The public values at which the reader is taken. -/
structure Pub1 where
  one : Params.OneTime
  set : Params.Setting

variable (Q : Pub1)

/-- The lookup that is open, or comes next. -/
def curAt (s : FirstState) : Lookup := lookAt Q.one s.base.keys.length

/-- A ledger is open, in front of the gathering of the lookup's claims. -/
def stageOpen (s : FirstState) : Bool :=
  match s.base.fork, s.base.heard with
  | some _, none => true
  | some F, some g => unpaidG (F.paid g.owedObjects) g.owedPlanes
  | none, _ => false

/-- THE MARK ON WHAT WAS HEARD: the ten facts `Left` (E2E/KeyLookupAround.lean); and no form of the
rows, and no lead of the three claims on the planes, names a slot that is marked for the index-mask
message. -/
def heardB (s : FirstState) (g : HeardG) : Bool :=
  match s.base.fork with
  | none => false
  | some G =>
    let p := lookupPlace Q.set s.base.keys.length (curAt Q s)
    leftB p g G && g.rows.toList.all (offB p.face 0) &&
      match planesG p.face g (G.paid g.owedObjects) [] with
      | none => false
      | some y => y.1.all fun c => offB p.face 0 c.lead

def heardSh (s : FirstState) (g : HeardG) : HeardSh :=
  ⟨heardB Q s g, g.rows.size, g.keys.map fun k => (k.1.size, k.2.slots.toList.map (·.1))⟩

def lookSh (s : FirstState) : LookSh :=
  { led := s.base.fork.map fun F => if stageOpen s then some (ledSh F) else none
    heard := s.base.heard.map (heardSh Q s)
    home := s.base.home.toList
    rows := s.base.rows.map (·.length)
    plain := s.base.rows.flatten.all
      (plainRowB (msgOf Q.one) (sizeB Q.one) (padP Q.one) (bitsV Q.one))
    keys := AtPublicFiles.AtFiles.keysSlots s.base.keys
    keysOk := AtPublicFiles.AtFiles.keysB (Wf.matrixOf Q.one.lin) Q.one.ranges.lookups s.base.keys }

/-- What the chain's back half writes. -/
abbrev BackOf : Type := List TensorRow × Array OracleNotice × Array ℕ × Option LinFirst

variable {Bk : Type} (bk : BackOf → Bk)

def locSh (s : FirstState) : LocSh Bk :=
  { owed := s.owed, sent := s.sent.toList, idx := s.idx, grp := s.grp, rider := s.rider
    atEnd := s.atEnd, tidy := stTidyB s.d.st, look := lookSh Q s
    back := bk (s.pile, s.msgW, s.ids, s.lin) }

/-- **The first chain's shape.** -/
abbrev Sh₁ (Bk : Type) : Type := CoreSh × LocSh Bk

/-- **The reader.** -/
def sh₁ (s : FirstState) : Sh₁ Bk := (shD s.d, locSh Q bk s)

/-! ## 4. Several mask entries keep the mark -/

section Masks
variable {L : Type}

theorem takeMasksInto_tidy (o : ℕ) : ∀ (n : ℕ) (d d' : DState L) (acc : Array ℕ) (l : List ℕ),
    takeMasksInto o n d acc = some (l, d') → stTidyB d.st = true → stTidyB d'.st = true
  | 0, d, d', acc, l, h, ht => by
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact ht
  | n + 1, d, d', acc, l, h, ht => by
    unfold takeMasksInto at h
    cases e : takeMaskP d o with
    | none => rw [e] at h; cases h
    | some y =>
      obtain ⟨i, d₁⟩ := y
      rw [e] at h
      exact takeMasksInto_tidy o n d₁ d' (acc.push i) l h (takeMask_tidy d d₁ o i e ht)

/-- The taking of several mask entries keeps the mark on the statement. -/
theorem takeMasks_tidy {d d' : DState L} {o n : ℕ} {l : List ℕ}
    (h : takeMasksP d o n = some (l, d')) (ht : stTidyB d.st = true) : stTidyB d'.st = true :=
  takeMasksInto_tidy o n d d' #[] l h ht

end Masks

/-! ## 5. From one exact lemma to the two forms -/

/-- Where the guards return [and the named tests pass] the run returns a state of the shape that the
guards return: then both forms hold. -/
theorem both_of_exact {S Sh : Type} {sh : S → Sh} {f : S → Except String S}
    {g : Sh → Except String Sh}
    (h : ∀ s t, g (sh s) = .ok t → ∃ s', f s = .ok s' ∧ sh s' = t) :
    CarriesR sh f g ∧ ReturnsR sh f g fun _ => true :=
  ⟨fun s s' t hf hg => by
      obtain ⟨s'', e, r⟩ := h s t hg
      rw [e] at hf
      obtain rfl := Except.ok.inj hf
      exact r.symm,
    fun s t hg _ => by
      obtain ⟨s', e, -⟩ := h s t hg
      exact ⟨s', e⟩⟩

/-! ## 6. A link's three steps of its own -/

section Link
variable (i : ℕ) (x : Lookup)

/-- "laid", on the shape. -/
def gLaid (a : Sh₁ Bk) : Except String (Sh₁ Bk) :=
  if a.2.look.led.isNone then .ok a else .error "a lookup's link: a ledger is open"

theorem laid_exact (s : FirstState) (t : Sh₁ Bk) (h : gLaid (sh₁ Q bk s) = .ok t) :
    ∃ s', (lookupLink Q.one Q.set i x).lay s = .ok s' ∧ sh₁ Q bk s' = t := by
  unfold gLaid at h
  split at h
  · rename_i hn
    obtain rfl := Except.ok.inj h
    have hf : s.base.fork = none := by
      have hn' : (s.base.fork.map fun F => if stageOpen s then some (ledSh F) else none).isNone =
        true := hn
      cases hk : s.base.fork with
      | none => rfl
      | some F => rw [hk] at hn'; cases hn'
    exact ⟨s, link_lay Q.one Q.set i x hf, rfl⟩
  · cases h

/-- "behind the batching", on the shape: nothing is asked, nothing turns. -/
theorem behind_exact (s : FirstState) (t : Sh₁ Bk)
    (h : (Except.ok (sh₁ Q bk s) : Except String (Sh₁ Bk)) = .ok t) :
    ∃ s', (lookupLink Q.one Q.set i x).runBehind s = .ok s' ∧ sh₁ Q bk s' = t :=
  ⟨s, link_behind Q.one Q.set i x s, Except.ok.inj h⟩

/-- "cleared", on the shape. -/
def gCleared (a : Sh₁ Bk) : Except String (Sh₁ Bk) :=
  .ok (a.1, { a.2 with look := { a.2.look with led := none, heard := none, home := [] } })

theorem cleared_exact (s : FirstState) (t : Sh₁ Bk) (h : gCleared (sh₁ Q bk s) = .ok t) :
    ∃ s', (lookupLink Q.one Q.set i x).clear s = .ok s' ∧ sh₁ Q bk s' = t :=
  ⟨_, link_clear Q.one Q.set i x s, Except.ok.inj h⟩

end Link

/-! ## 7. The sub-protocol in front of a lookup's rounds -/

/-- The shape of the fresh ledger with n slots, written. -/
def freshLed (n : ℕ) : LedSh :=
  LedSh.mk n n n (List.replicate n false) [] 0 [] 0 n 0 false [] false

theorem ledSh_fresh (n : ℕ) : ledSh (({} : Fork).slots n) = freshLed n := by
  simp [ledSh, freshLed, Fork.slots]

/-- "caller", on the shape: lookup number i. -/
def gCaller (i : ℕ) (a : Sh₁ Bk) : Except String (Sh₁ Bk) :=
  let f := faceOfLkp (lookAt Q.one i)
  if a.2.tidy && a.2.look.led.isNone && a.2.look.keys.length == i then
    match takeMasksS a.1 (msgOf Q.one) (f.slots - 2 * f.parts.length) with
    | none => .error "the caller: the own message's ledger"
    | some o =>
      match takeMasksS o.2 a.2.idx (2 * f.parts.length) with
      | none => .error "the caller: the index-mask message's ledger"
      | some k =>
        if (homesFrom (fromKeys f) (o.1.map fun j => ⟨msgOf Q.one, j⟩)
              (k.1.map fun j => ⟨a.2.idx, j⟩)).length == f.slots then
          .ok (k.2, { a.2 with look := { a.2.look with
            led := some (some (freshLed f.slots)), heard := none
            home := homesFrom (fromKeys f) (o.1.map fun j => ⟨msgOf Q.one, j⟩)
              (k.1.map fun j => ⟨a.2.idx, j⟩) } })
        else .error "the caller: a hidden value has no home"
  else .error "the caller: a ledger is open, or the lookups do not come in their order"

theorem caller_exact (i : ℕ) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64)))
    (s : FirstState) (t : Sh₁ Bk) (h : gCaller Q i (sh₁ Q bk s) = .ok t) :
    ∃ s', (caller Q.one i (lookAt Q.one i)).decide s rs gs = .ok s' ∧ sh₁ Q bk s' = t := by
  unfold gCaller at h
  dsimp only at h
  split at h
  case isFalse => cases h
  rename_i h0
  simp only [Bool.and_eq_true, beq_iff_eq] at h0
  obtain ⟨⟨ht, hn⟩, hk⟩ := h0
  have ht' : stTidyB s.d.st = true := ht
  have hf : s.base.fork = none := by
    have hn' : (s.base.fork.map fun F => if stageOpen s then some (ledSh F) else none).isNone =
      true := hn
    cases hq : s.base.fork with
    | none => rfl
    | some F => rw [hq] at hn'; cases hn'
  have hk' : s.base.keys.length = i := by
    have : (AtPublicFiles.AtFiles.keysSlots s.base.keys).length = i := hk
    unfold AtPublicFiles.AtFiles.keysSlots at this
    rwa [List.length_map] at this
  cases e1 : takeMasksS (sh₁ Q bk s).1 (msgOf Q.one) ((faceOfLkp (lookAt Q.one i)).slots -
      2 * (faceOfLkp (lookAt Q.one i)).parts.length) with
  | none => rw [e1] at h; cases h
  | some o =>
    rw [e1] at h
    dsimp only at h
    obtain ⟨⟨l₁, d₁⟩, p1⟩ := takeMasks_returns s.d _ _ _ e1
    have c1 := takeMasks_carries _ _ _ _ _ p1
    have t1 := takeMasks_tidy p1
    have c1' : takeMasksS (sh₁ Q bk s).1 _ _ = some (l₁, shD d₁) := c1
    rw [e1] at c1'
    obtain rfl := Option.some.inj c1'
    cases e2 : takeMasksS (shD d₁) (sh₁ Q bk s).2.idx
        (2 * (faceOfLkp (lookAt Q.one i)).parts.length) with
    | none => rw [e2] at h; cases h
    | some k =>
      rw [e2] at h
      dsimp only at h
      obtain ⟨⟨l₂, d₂⟩, p2⟩ := takeMasks_returns d₁ _ _ _ e2
      have c2 := takeMasks_carries _ _ _ _ _ p2
      have t2 := takeMasks_tidy p2
      rw [e2] at c2
      obtain rfl := Option.some.inj c2
      split at h
      case isFalse => cases h
      rename_i h3
      have hs := beq_iff_eq.1 h3
      obtain rfl := Except.ok.inj h
      have p2' : takeMasksP d₁ s.idx (2 * (faceOfLkp (lookAt Q.one i)).parts.length) =
        some (l₂, d₂) := p2
      have hs' : (homes (faceOfLkp (lookAt Q.one i))
          (l₁.map fun j => (⟨Q.one.ranges.messageId, j⟩ : Slot))
          (l₂.map fun j => (⟨s.idx, j⟩ : Slot))).size = (faceOfLkp (lookAt Q.one i)).slots := by
        unfold homes
        rw [List.size_toArray]
        exact hs
      have hd : (caller Q.one i (lookAt Q.one i)).decide s rs gs = .ok
          { s with
            d := d₂
            base := { s.base with
              fork := some (({} : Fork).slots (faceOfLkp (lookAt Q.one i)).slots), heard := none
              home := homes (faceOfLkp (lookAt Q.one i))
                (l₁.map fun j => ⟨Q.one.ranges.messageId, j⟩) (l₂.map fun j => ⟨s.idx, j⟩) } } := by
        simp only [caller, Key.quietAt, hf, hk', p1, p2', hs', named, need, Option.isNone_none,
          beq_self_eq_true, bind, Except.bind, pure, Except.pure, if_true]
      refine ⟨_, hd, ?_⟩
      unfold sh₁ locSh lookSh
      simp only [Option.map_some, Option.map_none, ledSh_fresh, t2 (t1 ht'), ht', stageOpen, homes,
        if_true]

end AtPublicFiles.KeyShape

#print axioms AtPublicFiles.KeyShape.plainRowB_iff
#print axioms AtPublicFiles.KeyShape.homesFrom_split
#print axioms AtPublicFiles.KeyShape.takeMasks_tidy
#print axioms AtPublicFiles.KeyShape.laid_exact
#print axioms AtPublicFiles.KeyShape.cleared_exact
#print axioms AtPublicFiles.KeyShape.caller_exact
