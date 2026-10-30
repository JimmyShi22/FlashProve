-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/LiftOwn.lean: A BLOCK's OWN LAW AT THE TABLE PASSES THE LIFT, AND THE LIFT BRINGS
THE REST OF THE RECORD IN. Two definitions, nine statements, written as `def … : Prop`, and their
proofs.

Why. A kind's law is proved at a piece over the part of the record that the block is typed at
(`Piece.Own`, Johnson/Desc/Sound/Spine.lean). The pieces of a description are LIFTED
(`Piece.lift`, Johnson/Desc/Sound/LiftRule.lean; `OfDesc`, Johnson/Desc/Sound/DescThree.lean: over
the public part and the chain's record). `LiftGoodIn` carries `GoodIn` up, at conditions and
relations that read the statement THROUGH THE PART alone. The table's items read more: a pin reads
the public part (a key's record), which the block never sees.

What is said. rest : S → Z: what the lifted block leaves as it is (premise: laying the part back
does not turn it; at a pair: the first half). THE LAW IS OWED AT THE PART, FOR EVERY VALUE z OF THE
REST, z A LETTER OF ITS CONDITIONS AND ITEMS: the block's text cannot read z, its law may name it.
Then the lifted block has the law at the whole record, with z read off the record. `LiftGoodInAt`:
so for `GoodIn`. `LiftOwn`: for `Piece.Own`. `LiftFrames`: for `Piece.Frames`. `EachOwnOfLift`: for
a row (`EachOwn`). WHERE THE EXTRACTOR READS THE REST TOO (a block that lays a part of the witness
by what the public part says): `Piece.liftAt`: the lifted block with an extractor e (rest a.1) at
the statement's part; `Piece.withExt`: a piece with another extractor. `LiftGoodInExt`,
`LiftOwnExt`, `LiftFramesExt`: the law is owed at the part for every z, AT THE EXTRACTOR e z. At e
:= fun _ => p.ext these are the first three. `OwnOfPart`, `FramesOfPart`: THE FORM FOR A GIVEN PIECE
q (of a tiling): if q's block is a lifted block and q's extractor reads the part and the rest, the
law at the part, at q's own stretch, rounds put back and errors, gives q's own law: no equation of
pieces is asked of the caller.

Limits. (1) `get`, `set` and `rest` obey three laws: premises; at a pair they hold by rfl. (2) "For
every z" is asked: also at values of the rest that no run reaches; a law that holds only at lawful z
takes that into its condition `on z`. (3) In the first four statements the extractor of the lifted
block reads the statement's part alone; in the three behind them the part and the rest: a piece
whose extractor is of neither form is not served. (4) `OwnOfPart` and `FramesOfPart` ask of the
given piece that its block IS a lifted block and that its extractor IS of that form: two premises,
owed piece by piece. (5) For `Block.lift` alone: nothing on `Block.liftPart`. (6) Those of
LiftRule.lean and Spine.lean: rules, whose premises are met by no block here.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.LiftRule
import Johnson.Desc.Sound.Spine

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString Doomed)

/-- **One law at the part for every value of the rest gives the law at the whole record.** -/
def LiftGoodInAt : Prop :=
  ∀ (S S₀ Z Cl W : Type) (C : CK) (F : Frame) (get : S → S₀) (set : S → S₀ → S) (rest : S → Z)
    (p : Piece C F S₀ Cl W) (on on' : Z → S₀ × F.E.Str → Prop)
    (R R' : Z → S₀ × F.E.Str → W → Prop),
    (∀ t s, get (set t s) = s) → (∀ t s s', set (set t s) s' = set t s') →
    (∀ t s, rest (set t s) = rest t) →
    (∀ z, p.GoodIn (on z) (on' z) (R z) (R' z)) →
    (p.lift get set).GoodIn (fun a => on (rest a.1) (atPart get a))
      (fun a => on' (rest a.1) (atPart get a)) (fun a w => R (rest a.1) (atPart get a) w)
      (fun a w => R' (rest a.1) (atPart get a) w)

/-- **A block's own law at the table passes the lift.** -/
def LiftOwn : Prop :=
  ∀ (S S₀ Z Cl W ι : Type) (C : CK) (F : Frame) (get : S → S₀) (set : S → S₀ → S) (rest : S → Z)
    (p : Piece C F S₀ Cl W) (on on' : Z → S₀ × F.E.Str → Prop)
    (means : Z → ι → S₀ × F.E.Str → W → Prop) (In Out : ι → Prop),
    (∀ t s, get (set t s) = s) → (∀ t s s', set (set t s) s' = set t s') →
    (∀ t s, rest (set t s) = rest t) →
    (∀ z, p.Own (on z) (on' z) (means z) In Out) →
    (p.lift get set).Own (fun a => on (rest a.1) (atPart get a))
      (fun a => on' (rest a.1) (atPart get a))
      (fun i a w => means (rest a.1) i (atPart get a) w) In Out

/-- What is owed for the items that ride past passes the lift. -/
def LiftFrames : Prop :=
  ∀ (S S₀ Z Cl W ι : Type) (C : CK) (F : Frame) (get : S → S₀) (set : S → S₀ → S) (rest : S → Z)
    (p : Piece C F S₀ Cl W) (on on' : Z → S₀ × F.E.Str → Prop)
    (means : Z → ι → S₀ × F.E.Str → W → Prop) (O In : ι → Prop),
    (∀ t s, get (set t s) = s) → (∀ t s s', set (set t s) s' = set t s') →
    (∀ t s, rest (set t s) = rest t) →
    (∀ z, p.Frames (on z) (on' z) (means z) O In) →
    (p.lift get set).Frames (fun a => on (rest a.1) (atPart get a))
      (fun a => on' (rest a.1) (atPart get a))
      (fun i a w => means (rest a.1) i (atPart get a) w) O In

/-- A row of blocks with both at the part, for every value of the rest: the lifted row has both. -/
def EachOwnOfLift : Prop :=
  ∀ (S S₀ Z Cl W ι : Type) (C : CK) (F : Frame) (get : S → S₀) (set : S → S₀ → S) (rest : S → Z)
    (on : Z → ℕ → S₀ × F.E.Str → Prop) (means : Z → ι → S₀ × F.E.Str → W → Prop)
    (In Out : ℕ → ι → Prop) (O₀ : ι → Prop) (k : ℕ) (l : List (Piece C F S₀ Cl W)),
    (∀ t s, get (set t s) = s) → (∀ t s s', set (set t s) s' = set t s') →
    (∀ t s, rest (set t s) = rest t) →
    (∀ z, EachOwn (on z) (means z) In Out O₀ k l) →
    EachOwn (fun j a => on (rest a.1) j (atPart get a))
      (fun i a w => means (rest a.1) i (atPart get a) w) In Out O₀ k
      (l.map (Piece.lift get set))

variable {S S₀ Z Cl W : Type} {C : CK} {F : Frame}

/-- A piece with another extractor. -/
def Piece.withExt (p : Piece C F S₀ Cl W) (e : S₀ × F.E.Str → Iop.Tr (uLT C p.ds) → W → W) :
    Piece C F S₀ Cl W :=
  ⟨p.b, p.base, p.ds, p.back, e, p.err⟩

/-- **A block with its stretch, lifted, its extractor reading the rest of the record too.** -/
def Piece.liftAt (get : S → S₀) (set : S → S₀ → S) (rest : S → Z) (p : Piece C F S₀ Cl W)
    (e : Z → S₀ × F.E.Str → Iop.Tr (uLT C p.ds) → W → W) : Piece C F S Cl W :=
  ⟨p.b.lift get set, p.base, p.ds, p.back, fun a τ w => e (rest a.1) (atPart get a) τ w, p.err⟩

/-- `LiftGoodInAt` where the extractor reads the rest too. -/
def LiftGoodInExt : Prop :=
  ∀ (S S₀ Z Cl W : Type) (C : CK) (F : Frame) (get : S → S₀) (set : S → S₀ → S) (rest : S → Z)
    (p : Piece C F S₀ Cl W) (e : Z → S₀ × F.E.Str → Iop.Tr (uLT C p.ds) → W → W)
    (on on' : Z → S₀ × F.E.Str → Prop) (R R' : Z → S₀ × F.E.Str → W → Prop),
    (∀ t s, get (set t s) = s) → (∀ t s s', set (set t s) s' = set t s') →
    (∀ t s, rest (set t s) = rest t) →
    (∀ z, (p.withExt (e z)).GoodIn (on z) (on' z) (R z) (R' z)) →
    (p.liftAt get set rest e).GoodIn (fun a => on (rest a.1) (atPart get a))
      (fun a => on' (rest a.1) (atPart get a)) (fun a w => R (rest a.1) (atPart get a) w)
      (fun a w => R' (rest a.1) (atPart get a) w)

/-- `LiftOwn` where the extractor reads the rest too. -/
def LiftOwnExt : Prop :=
  ∀ (S S₀ Z Cl W ι : Type) (C : CK) (F : Frame) (get : S → S₀) (set : S → S₀ → S) (rest : S → Z)
    (p : Piece C F S₀ Cl W) (e : Z → S₀ × F.E.Str → Iop.Tr (uLT C p.ds) → W → W)
    (on on' : Z → S₀ × F.E.Str → Prop)
    (means : Z → ι → S₀ × F.E.Str → W → Prop) (In Out : ι → Prop),
    (∀ t s, get (set t s) = s) → (∀ t s s', set (set t s) s' = set t s') →
    (∀ t s, rest (set t s) = rest t) →
    (∀ z, (p.withExt (e z)).Own (on z) (on' z) (means z) In Out) →
    (p.liftAt get set rest e).Own (fun a => on (rest a.1) (atPart get a))
      (fun a => on' (rest a.1) (atPart get a))
      (fun i a w => means (rest a.1) i (atPart get a) w) In Out

/-- `LiftFrames` where the extractor reads the rest too. -/
def LiftFramesExt : Prop :=
  ∀ (S S₀ Z Cl W ι : Type) (C : CK) (F : Frame) (get : S → S₀) (set : S → S₀ → S) (rest : S → Z)
    (p : Piece C F S₀ Cl W) (e : Z → S₀ × F.E.Str → Iop.Tr (uLT C p.ds) → W → W)
    (on on' : Z → S₀ × F.E.Str → Prop)
    (means : Z → ι → S₀ × F.E.Str → W → Prop) (O In : ι → Prop),
    (∀ t s, get (set t s) = s) → (∀ t s s', set (set t s) s' = set t s') →
    (∀ t s, rest (set t s) = rest t) →
    (∀ z, (p.withExt (e z)).Frames (on z) (on' z) (means z) O In) →
    (p.liftAt get set rest e).Frames (fun a => on (rest a.1) (atPart get a))
      (fun a => on' (rest a.1) (atPart get a))
      (fun i a w => means (rest a.1) i (atPart get a) w) O In

/-- **At a given piece**: q holds a lifted block, and its extractor reads the part and the rest:
then the law at the part, for every z, at the piece with q's own stretch, rounds put back and
errors, gives q's own law. -/
def OwnOfPart : Prop :=
  ∀ (S S₀ Z Cl W ι : Type) (C : CK) (F : Frame) (get : S → S₀) (set : S → S₀ → S) (rest : S → Z)
    (q : Piece C F S Cl W) (b₀ : Block S₀ Cl)
    (e : Z → S₀ × F.E.Str → Iop.Tr (uLT C q.ds) → W → W) (on on' : Z → S₀ × F.E.Str → Prop)
    (means : Z → ι → S₀ × F.E.Str → W → Prop) (In Out : ι → Prop),
    (∀ t s, get (set t s) = s) → (∀ t s s', set (set t s) s' = set t s') →
    (∀ t s, rest (set t s) = rest t) →
    q.b = b₀.lift get set → (∀ a τ w, q.ext a τ w = e (rest a.1) (atPart get a) τ w) →
    (∀ z, (⟨b₀, q.base, q.ds, q.back, e z, q.err⟩ : Piece C F S₀ Cl W).Own (on z) (on' z) (means z)
      In Out) →
    q.Own (fun a => on (rest a.1) (atPart get a)) (fun a => on' (rest a.1) (atPart get a))
      (fun i a w => means (rest a.1) i (atPart get a) w) In Out

/-- The like for the items that ride past. -/
def FramesOfPart : Prop :=
  ∀ (S S₀ Z Cl W ι : Type) (C : CK) (F : Frame) (get : S → S₀) (set : S → S₀ → S) (rest : S → Z)
    (q : Piece C F S Cl W) (b₀ : Block S₀ Cl)
    (e : Z → S₀ × F.E.Str → Iop.Tr (uLT C q.ds) → W → W) (on on' : Z → S₀ × F.E.Str → Prop)
    (means : Z → ι → S₀ × F.E.Str → W → Prop) (O In : ι → Prop),
    (∀ t s, get (set t s) = s) → (∀ t s s', set (set t s) s' = set t s') →
    (∀ t s, rest (set t s) = rest t) →
    q.b = b₀.lift get set → (∀ a τ w, q.ext a τ w = e (rest a.1) (atPart get a) τ w) →
    (∀ z, (⟨b₀, q.base, q.ds, q.back, e z, q.err⟩ : Piece C F S₀ Cl W).Frames (on z) (on' z)
      (means z) O In) →
    q.Frames (fun a => on (rest a.1) (atPart get a)) (fun a => on' (rest a.1) (atPart get a))
      (fun i a w => means (rest a.1) i (atPart get a) w) O In

/-! ## The proofs -/

theorem liftGoodInAt : LiftGoodInAt := by
  intro S S₀ Z Cl W C F get set rest p on on' R R' h1 h2 h3 h a ha
  refine Doomed.mono _ _ ?_ (h (rest a.1) (atPart get a) ha)
  intro τ hτ b hb
  rw [liftOut S S₀ Cl W C F get set p h1 h2 a τ] at hb
  obtain ⟨b₀, hb₀, rfl⟩ := Option.map_eq_some_iff.1 hb
  have e : atPart get ((set a.1 b₀.1, b₀.2) : S × F.E.Str) = b₀ := by
    show (get (set a.1 b₀.1), b₀.2) = b₀
    rw [h1]
  have r : rest (set a.1 b₀.1) = rest a.1 := h3 _ _
  obtain ⟨ho, hk⟩ := hτ b₀ hb₀
  refine ⟨?_, fun w hw => ?_⟩
  · show on' (rest (set a.1 b₀.1)) (atPart get (set a.1 b₀.1, b₀.2))
    rw [e, r]
    exact ho
  · have hw' : R' (rest (set a.1 b₀.1)) (atPart get (set a.1 b₀.1, b₀.2)) w := hw
    rw [e, r] at hw'
    exact hk w hw'

theorem liftOwn : LiftOwn := by
  intro S S₀ Z Cl W ι C F get set rest p on on' means In Out h1 h2 h3 h
  exact liftGoodInAt S S₀ Z Cl W C F get set rest p on on' (fun z => relAt (means z) In)
    (fun z => relAt (means z) Out) h1 h2 h3 h

theorem liftFrames : LiftFrames := by
  intro S S₀ Z Cl W ι C F get set rest p on on' means O In h1 h2 h3 h a τ b w i ha hb hb' hO hI hm
  rw [liftOut S S₀ Cl W C F get set p h1 h2 a τ] at hb
  obtain ⟨b₀, hb₀, rfl⟩ := Option.map_eq_some_iff.1 hb
  have e : atPart get ((set a.1 b₀.1, b₀.2) : S × F.E.Str) = b₀ := by
    show (get (set a.1 b₀.1), b₀.2) = b₀
    rw [h1]
  have r : rest (set a.1 b₀.1) = rest a.1 := h3 _ _
  have hb'' : on' (rest (set a.1 b₀.1)) (atPart get (set a.1 b₀.1, b₀.2)) := hb'
  have hm' : means (rest (set a.1 b₀.1)) i (atPart get (set a.1 b₀.1, b₀.2)) w := hm
  rw [e, r] at hb'' hm'
  exact h (rest a.1) (atPart get a) τ b₀ w i ha hb₀ hb'' hO hI hm'

theorem eachOwnOfLift : EachOwnOfLift := by
  intro S S₀ Z Cl W ι C F get set rest on means In Out O₀ k l h1 h2 h3
  induction l generalizing k with
  | nil => exact fun _ => trivial
  | cons p l ih =>
    intro h
    exact ⟨liftOwn S S₀ Z Cl W ι C F get set rest p (fun z => on z k) (fun z => on z (k + 1)) means
        (In k) (Out k) h1 h2 h3 (fun z => (h z).1),
      liftFrames S S₀ Z Cl W ι C F get set rest p (fun z => on z k) (fun z => on z (k + 1)) means
        (openAfter In Out O₀ k) (In k) h1 h2 h3 (fun z => (h z).2.1),
      ih (k + 1) (fun z => (h z).2.2)⟩

theorem liftGoodInExt : LiftGoodInExt := by
  intro S S₀ Z Cl W C F get set rest p e on on' R R' h1 h2 h3 h a ha
  refine Doomed.mono _ _ ?_ (h (rest a.1) (atPart get a) ha)
  intro τ hτ b hb
  have hb2 : (p.lift get set).ior.red.out a τ = some b := hb
  rw [liftOut S S₀ Cl W C F get set p h1 h2 a τ] at hb2
  obtain ⟨b₀, hb₀, rfl⟩ := Option.map_eq_some_iff.1 hb2
  have q : atPart get ((set a.1 b₀.1, b₀.2) : S × F.E.Str) = b₀ := by
    show (get (set a.1 b₀.1), b₀.2) = b₀
    rw [h1]
  have r : rest (set a.1 b₀.1) = rest a.1 := h3 _ _
  obtain ⟨ho, hk⟩ := hτ b₀ hb₀
  refine ⟨?_, fun w hw => ?_⟩
  · show on' (rest (set a.1 b₀.1)) (atPart get (set a.1 b₀.1, b₀.2))
    rw [q, r]
    exact ho
  · have hw' : R' (rest (set a.1 b₀.1)) (atPart get (set a.1 b₀.1, b₀.2)) w := hw
    rw [q, r] at hw'
    exact hk w hw'

theorem liftOwnExt : LiftOwnExt := by
  intro S S₀ Z Cl W ι C F get set rest p e on on' means In Out h1 h2 h3 h
  exact liftGoodInExt S S₀ Z Cl W C F get set rest p e on on' (fun z => relAt (means z) In)
    (fun z => relAt (means z) Out) h1 h2 h3 h

theorem liftFramesExt : LiftFramesExt := by
  intro S S₀ Z Cl W ι C F get set rest p e on on' means O In h1 h2 h3 h a τ b w i ha hb hb' hO hI
    hm
  have hb2 : (p.lift get set).ior.red.out a τ = some b := hb
  rw [liftOut S S₀ Cl W C F get set p h1 h2 a τ] at hb2
  obtain ⟨b₀, hb₀, rfl⟩ := Option.map_eq_some_iff.1 hb2
  have q : atPart get ((set a.1 b₀.1, b₀.2) : S × F.E.Str) = b₀ := by
    show (get (set a.1 b₀.1), b₀.2) = b₀
    rw [h1]
  have r : rest (set a.1 b₀.1) = rest a.1 := h3 _ _
  have hb'' : on' (rest (set a.1 b₀.1)) (atPart get (set a.1 b₀.1, b₀.2)) := hb'
  have hm' : means (rest (set a.1 b₀.1)) i (atPart get (set a.1 b₀.1, b₀.2)) w := hm
  rw [q, r] at hb'' hm'
  exact h (rest a.1) (atPart get a) τ b₀ w i ha hb₀ hb'' hO hI hm'

theorem ownOfPart : OwnOfPart := by
  intro S S₀ Z Cl W ι C F get set rest q
  obtain ⟨b, base, ds, back, ext, err⟩ := q
  dsimp only
  intro b₀ e on on' means In Out h1 h2 h3 hb hext h
  subst hb
  have he : ext = fun a τ w => e (rest a.1) (atPart get a) τ w := by
    funext a τ w
    exact hext a τ w
  subst he
  exact liftOwnExt S S₀ Z Cl W ι C F get set rest ⟨b₀, base, ds, back, fun _ _ w => w, err⟩ e on on'
    means In Out h1 h2 h3 h

theorem framesOfPart : FramesOfPart := by
  intro S S₀ Z Cl W ι C F get set rest q
  obtain ⟨b, base, ds, back, ext, err⟩ := q
  dsimp only
  intro b₀ e on on' means O In h1 h2 h3 hb hext h
  subst hb
  have he : ext = fun a τ w => e (rest a.1) (atPart get a) τ w := by
    funext a τ w
    exact hext a τ w
  subst he
  exact liftFramesExt S S₀ Z Cl W ι C F get set rest ⟨b₀, base, ds, back, fun _ _ w => w, err⟩ e on
    on' means O In h1 h2 h3 h


end VerifiableInference.Desc.Sound
