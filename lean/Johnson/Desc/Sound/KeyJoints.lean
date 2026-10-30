-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/KeyJoints.lean: THE FORM OF A ROW OF THE TABLE OF JOINTS AT THE KEY FILE, and
how rows and seats are laid in a row.

The setting. Johnson/Desc/Sound/KeyDecides.lean takes a chain as one value `SL`: blocks in a row,
each with its stretch, its proved typed block, its maps, and in front of it a reading and an
invariant. A table of joints has one row for each border, written once, so that what stands behind
one block is what stands in front of the next BY CONSTRUCTION; and a kind's files lay that kind's
blocks between two rows without seeing the others.

What is said.
  `JointRow S F`: ONE ROW: what the carried record and the oracles MEAN at a border: J, a typed
    joint of the library (its condition: what is promised; its relation: what is claimed); rd, the
    reading of a statement of the chain as a statement of J; inv, the invariant of the carried
    record that the typed side does not know.
  `JointRow.on`, `JointRow.rel`: the condition and the relation at the border, WRITTEN from the row.
  `Seat A B`: one block between two rows, with its stretch, its proved typed block and its maps.
    `Seat.Law`: all that is asked of it. `Seat.sl`: the seat as a row of one block.
  `SL.app`: two rows of blocks behind each other. `SL.laws_app`, `SL.held_app`, `SL.pieces_app`,
    `SL.rd0_app`, `SL.rdZ_app`, `SL.inv0_app`, `SL.invZ_app`: what is asked of the whole is what is
    asked of the two, where they meet at one row.
  `JointRow.first`: THE KEY FILE'S FIRST ROW, written: the joint `jWf` ("no collision at the
    record's seed"; "decodes with the record"), at the reading that takes the instance out of the
    record's first part by an inverse of the public part. `first_reads`: at the file's own first
    statements it gives back the instance and the stored table. `onImage`: THE GUARD that belongs in
    the invariant of a row that reads so: the first part is some instance's public part;
    `onImage_first`, `onImage_keep`, `first_guard`.
  `Seat.ofEnd`, `Seat.ofEnd_law`, `Seat.ofEnd_held`, `Seat.ofEnd_below`: A CHAIN'S END as a seat
    between a row and the same row with "the record has passed the chain's own clauses" laid into
    its invariant: all that is asked of it holds.

Limits. Forms, and the two kinds of rows that are the key file's own. No other row is filled.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.PassLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.ChainEnd
open _root_.Run (ckP)
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString)

variable {S Cl : Type} {F : Frame}

/-! ## 1 A row, a seat -/

/-- **One row of the table of joints.** -/
structure JointRow (S : Type) (F : Frame) : Type 1 where
  /-- the typed joint: what is promised (its condition) and what is claimed (its relation) -/
  J : JK
  /-- a statement of the chain, read as a statement of the joint -/
  rd : S × F.E.Str → J.X × J.E.Str
  /-- what holds of the carried record besides, and the typed side does not know -/
  inv : S × F.E.Str → Prop

/-- The condition at the border. -/
def JointRow.on (A : JointRow S F) (a : S × F.E.Str) : Prop := A.J.on (A.rd a) ∧ A.inv a

/-- The relation at the border: the typed relation, read, has a witness. -/
def JointRow.rel (A : JointRow S F) (a : S × F.E.Str) : Prop := ∃ w, A.J.relR (A.rd a) w

/-- **One block between two rows.** -/
structure Seat (Cl : Type) (A B : JointRow S F) : Type 1 where
  b : Block S Cl
  base : ℕ
  ds : List RDT
  back : List Fmt.RoundView := []
  k : BK A.J B.J
  M : Maps ds k.R.red.shape

/-- **All that is asked of a seat**: the typed block is good; the out-joint's witnesses are not
empty; the maps are in order; the rounds put back hold no word above the prime; the block's one law.
-/
def Seat.Law {A B : JointRow S F} (s : Seat Cl A B) : Prop :=
  s.k.Good ∧ Nonempty B.J.W ∧ s.M.OK ∧ viewWordsBelowPrime ⟨s.back, []⟩ = true ∧
    DecideLaw s.b s.base s.ds s.back s.k s.M A.rd B.rd A.inv B.inv

/-- The seat as a row of one block. -/
def Seat.sl {A B : JointRow S F} (s : Seat Cl A B) : SL S Cl F A.J B.J :=
  .cons A.rd A.inv s.b s.base s.ds s.back s.k s.M (.nil B.rd B.inv)

theorem Seat.sl_laws {A B : JointRow S F} (s : Seat Cl A B) : s.sl.Laws ↔ s.Law :=
  ⟨fun h => h.1, fun h => ⟨h, trivial⟩⟩

theorem Seat.sl_held {A B : JointRow S F} (s : Seat Cl A B) (εs : ℝ≥0∞) :
    s.sl.Held εs ↔ s.M.Held εs s.k.err :=
  ⟨fun h => h.1, fun h => ⟨h, trivial⟩⟩

/-! ## 2 Rows of blocks behind each other -/

namespace SL

/-- Two rows of blocks behind each other. The reading and the invariant at the joint where they meet
are the second's. -/
def app : {A B Z : JK} → SL S Cl F A B → SL S Cl F B Z → SL S Cl F A Z
  | _, _, _, .nil _ _, m => m
  | _, _, _, .cons rd inv b base ds back k M l, m => .cons rd inv b base ds back k M (l.app m)

theorem rd0_app {A B Z : JK} (l : SL S Cl F A B) (m : SL S Cl F B Z) (h : l.rdZ = m.rd0) :
    (l.app m).rd0 = l.rd0 := by
  cases l with
  | nil rd inv => exact h.symm
  | cons rd inv b base ds back k M l => rfl

theorem inv0_app {A B Z : JK} (l : SL S Cl F A B) (m : SL S Cl F B Z) (h : l.invZ = m.inv0) :
    (l.app m).inv0 = l.inv0 := by
  cases l with
  | nil rd inv => exact h.symm
  | cons rd inv b base ds back k M l => rfl

theorem rdZ_app {A B Z : JK} (l : SL S Cl F A B) (m : SL S Cl F B Z) :
    (l.app m).rdZ = m.rdZ := by
  induction l with
  | nil rd inv => rfl
  | cons rd inv b base ds back k M l ih => exact ih m

theorem invZ_app {A B Z : JK} (l : SL S Cl F A B) (m : SL S Cl F B Z) :
    (l.app m).invZ = m.invZ := by
  induction l with
  | nil rd inv => rfl
  | cons rd inv b base ds back k M l ih => exact ih m

theorem pieces_app (W : Type) {A B Z : JK} (l : SL S Cl F A B) (m : SL S Cl F B Z) :
    (l.app m).pieces W = l.pieces W ++ m.pieces W := by
  induction l with
  | nil rd inv => rfl
  | cons rd inv b base ds back k M l ih => exact congrArg (List.cons _) (ih m)

/-- **What is asked of the whole is what is asked of the two**, where they meet at one row. -/
theorem laws_app {A B Z : JK} (l : SL S Cl F A B) (m : SL S Cl F B Z) (hr : l.rdZ = m.rd0)
    (hi : l.invZ = m.inv0) (hl : l.Laws) (hm : m.Laws) : (l.app m).Laws := by
  induction l with
  | nil rd inv => exact hm
  | cons rd inv b base ds back k M l ih =>
    obtain ⟨⟨h1, h2, h3, h4, h5⟩, h6⟩ := hl
    refine ⟨⟨h1, h2, h3, h4, ?_⟩, ih m hr hi h6 hm⟩
    rw [rd0_app l m hr, inv0_app l m hi]
    exact h5

theorem held_app (εs : ℝ≥0∞) {A B Z : JK} (l : SL S Cl F A B) (m : SL S Cl F B Z)
    (hl : l.Held εs) (hm : m.Held εs) : (l.app m).Held εs := by
  induction l with
  | nil rd inv => exact hm
  | cons rd inv b base ds back k M l ih => exact ⟨hl.1, ih m hl.2 hm⟩

end SL

/-! ## 3 The key file's own rows -/

/-- **The key file's first row.** P: the instance's public part; pub: how it is made of the
instance; rec₀: the reading's value at a first part that is no instance's public part; inv: the
invariant of the first record. -/
def JointRow.first {a : ℕ} (Kc : ConfLetters a) {D : WholeD} {all : List LeftT} {key : ℕ → ℕ}
    {ft : ℕ} {P S' : Type} (pub : Kc.conf.Rec → P) (rec₀ : Kc.conf.Rec)
    (inv : (P × S') × (frameAt (D.at a) all key ft).E.Str → Prop) :
    JointRow (P × S') (frameAt (D.at a) all key ft) where
  J := jWf Kc.conf
  rd := fun b => (rdPub Kc pub rec₀ b.1, b.2.1)
  inv := inv

/-- At the file's own first statements it gives back the instance and the stored table. -/
theorem first_reads {a : ℕ} (Kc : ConfLetters a) {D : WholeD} {all : List LeftT} {key : ℕ → ℕ}
    {ft : ℕ} {P S' : Type} (pub : Kc.conf.Rec → P) (hpub : Function.Injective pub)
    (rec₀ : Kc.conf.Rec) (inv : (P × S') × (frameAt (D.at a) all key ft).E.Str → Prop)
    (rec : Kc.conf.Rec) (s : S') (y : (frameAt (D.at a) all key ft).E.Str) :
    (JointRow.first Kc pub rec₀ inv).rd ((pub rec, s), y) = (rec, y.1) :=
  congrArg (fun r => (r, y.1)) (@Function.leftInverse_invFun _ _ ⟨rec₀⟩ pub hpub rec)

/-- **The guard of the first row**: the carried record's first part IS some instance's public part.
`JointRow.first` reads the instance by an inverse of `pub`, which gives the fixed rec₀ at a first
part that is no instance's public part: THERE A LAW WOULD SPEAK OF rec₀, a record that has nothing
to do with the statement. So the guard belongs in the invariant of every row that reads the instance
so: it holds at the file's own first statements (`onImage_first`); a block that leaves the first
part as it is keeps it (`onImage_keep`: every lifted block does); and under it the record read is
the one whose public part stands in the statement (`first_guard`). -/
def onImage {R P S' Y : Type} (pub : R → P) (b : (P × S') × Y) : Prop := ∃ rec, b.1.1 = pub rec

theorem onImage_first {R P S' Y : Type} (pub : R → P) (rec : R) (s : S') (y : Y) :
    onImage pub ((pub rec, s), y) := ⟨rec, rfl⟩

theorem onImage_keep {R P S' Y : Type} (pub : R → P) (b b' : (P × S') × Y) (h : b'.1.1 = b.1.1)
    (hb : onImage pub b) : onImage pub b' := hb.imp fun _ e => h.trans e

theorem first_guard {a : ℕ} (Kc : ConfLetters a) {D : WholeD} {all : List LeftT} {key : ℕ → ℕ}
    {ft : ℕ} {P S' : Type} (pub : Kc.conf.Rec → P) (hpub : Function.Injective pub)
    (rec₀ : Kc.conf.Rec) (inv : (P × S') × (frameAt (D.at a) all key ft).E.Str → Prop)
    (b : (P × S') × (frameAt (D.at a) all key ft).E.Str) (hb : onImage pub b) :
    pub ((JointRow.first Kc pub rec₀ inv).rd b).1 = b.1.1 := by
  obtain ⟨rec, e⟩ := hb
  show pub (@Function.invFun _ _ ⟨rec₀⟩ pub b.1.1) = b.1.1
  rw [e, @Function.leftInverse_invFun _ _ ⟨rec₀⟩ pub hpub rec]

/-- The row behind a chain's end: the same joint and reading; the invariant holds besides that the
record has passed the chain's own clauses. -/
def JointRow.passed (A : JointRow S F) (asks : S → Clauses) : JointRow S F :=
  { A with inv := fun a => A.inv a ∧ ∀ c ∈ asks a.1, c.2 = true }

/-- **A chain's end as a seat.** -/
def Seat.ofEnd (A : JointRow S F) (chain piece : ℕ) (sealed : Bool)
    (inFront : List Fmt.DeclaredRound) (asks : S → Clauses) (base : ℕ) (ds : List RDT)
    (back : List Fmt.RoundView) : Seat Cl A (A.passed asks) where
  b := ChainEnd.chainEnd chain piece sealed inFront asks
  base := base
  ds := ds
  back := back
  k := BK.pass A.J
  M := Maps.skips ds

theorem Seat.ofEnd_law (A : JointRow S F) (chain piece : ℕ) (sealed : Bool)
    (inFront : List Fmt.DeclaredRound) (asks : S → Clauses) (base : ℕ) (ds : List RDT)
    (back : List Fmt.RoundView) (hW : Nonempty A.J.W) (hnd : (F.all.map (·.no)).Nodup)
    (hrd : ReadsBelow base A.rd) (hinv : ReadsBelow base A.inv)
    (hback : viewWordsBelowPrime ⟨back, []⟩ = true) :
    (Seat.ofEnd (Cl := Cl) A chain piece sealed inFront asks base ds back).Law :=
  ⟨BK.pass_good A.J, hW, Maps.ok_skips ds, hback,
    chainEnd_law_asks chain piece sealed inFront asks base ds back A.J A.rd A.inv hnd hrd hinv⟩

theorem Seat.ofEnd_held (A : JointRow S F) (chain piece : ℕ) (sealed : Bool)
    (inFront : List Fmt.DeclaredRound) (asks : S → Clauses) (base : ℕ) (ds : List RDT)
    (back : List Fmt.RoundView) (εs : ℝ≥0∞) :
    (Seat.ofEnd (Cl := Cl) A chain piece sealed inFront asks base ds back).M.Held εs
      (Seat.ofEnd (Cl := Cl) A chain piece sealed inFront asks base ds back).k.err :=
  Maps.held_skips εs ds

/-- The written counts of a chain's end's seat are shares of at most every εs: it counts nothing. -/
theorem Seat.ofEnd_below (A : JointRow S F) (chain piece : ℕ) (sealed : Bool)
    (inFront : List Fmt.DeclaredRound) (asks : S → Clauses) (base : ℕ) (ds : List RDT)
    (back : List Fmt.RoundView) (εs : ℝ≥0∞) :
    Err.Below ((Seat.ofEnd (Cl := Cl) A chain piece sealed inFront asks base ds back).M.err
      (Seat.ofEnd (Cl := Cl) A chain piece sealed inFront asks base ds back).k.err) εs :=
  (Maps.skips ds).below_err (Maps.ok_skips ds) _ (Maps.held_skips εs ds)

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.Seat.ofEnd_below
#print axioms VerifiableInference.Desc.Sound.first_guard
#print axioms VerifiableInference.Desc.Sound.SL.laws_app
#print axioms VerifiableInference.Desc.Sound.SL.held_app
#print axioms VerifiableInference.Desc.Sound.SL.pieces_app
#print axioms VerifiableInference.Desc.Sound.first_reads
#print axioms VerifiableInference.Desc.Sound.Seat.ofEnd_law
#print axioms VerifiableInference.Desc.Sound.Seat.ofEnd_held
