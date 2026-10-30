-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/QuietRows.lean: THE OWN LAWS OF A BLOCK WHOSE ROW IN A TABLE OF JOINTS IS EMPTY,
AND THE TWO SUCH ROWS OF THE LAST CHAIN's TABLE (Johnson/Desc/Last/BordersLast.lean: 1, the taken
trees' sources; 3, the chain's end). Definitions, statements written as `def … : Prop`, and their
proofs.

Why. The rule that joins a chain's blocks (`SpineRule`, Johnson/Desc/Sound/Spine.lean; at the last
chain: `LastJoin`, `LastJoinPlain`, Johnson/Desc/Sound/BordersLastQ.lean) asks of every block two
things: its own law between the items that its row closes and opens (`Piece.Own`), and that the
items that ride past it are kept (`Piece.Frames`). Two of the last chain's four rows hold no item.
Here what these two owe is brought down to what is left of it.

1 GENERAL IN THE TABLE.
  `OwnOfNoItem`: a block whose row CLOSES nothing has `Piece.Own` where the promise behind follows
    from the promise in front and its yes. No chance is spent: at every transcript.
  `ReadsBelowAt lo m`: what the claim m says of a statement reads the oracles' strings through the
    stored table and the trees below lo alone.
  `FramesOfQuiet`: a block that hands the record on as it is where it says yes inside the promise,
    and whose extractor is the identity, has `Piece.Frames` FOR THE OPEN ITEMS THAT READ BELOW ITS
    BASE. By the facts on the strings (`out_behind`, Johnson/Desc/Sound/SendLaw.lean;
    `cellStays`, `colStays`, Johnson/Desc/Sound/StringsStay.lean): called.
    NOT "FOR EVERY ITEM": behind a block the strings of the trees from its base on are what its
    stage leaves, not what stood in front: an item in letters that reads such a tree may turn.
  `FramesOfNoneOpen`: where nothing is open nothing is owed for what rides.
2 AT THE LAST CHAIN's TABLE.
  `ins_one`, `ins_three`: rows 1 and 3 close nothing and read nothing. `OpenAtOne`: at border 1 the
    three pins and "rows" are open, no more. `NoneOpenAtThree`: at border 3 nothing is open. By
    evaluation of the table's own lists (`openIsList`, Johnson/Desc/Sound/GlueSecondProofs.lean).
  `PinsReadBelow lo`: a condition on the meaning's letters: the three pins read below lo.
  **`RowOneOwed x`**: WHAT IS LEFT AT ROW 1, four things: same · idle · prom · pins.
  **`RowThreeOwed x`**: WHAT IS LEFT AT ROW 3, one thing: the promise at border 4 follows from the
    promise at border 3 and the end's yes. Neither "the record goes on as it is" nor "the extractor
    is the identity" is wanted there.
  **`rowOne`**, **`rowThree`**: they give the row's two conjuncts of `EachOwn`.
  `eachOwn_of_rows`: `EachOwn` at the table, of the two and of rows 0 and 2 as their files owe
    them.

WHO PAYS WHAT IS LEFT (nothing of it is shown here).
  same: the text's files' law on the sources' block ("yes just where the record goes on as it is
    and the sources are tied"), through what a piece's yes says of its block's decision.
  idle: the pieces' make: the extractors are letters of the cut; the table's row says "lays
    nothing".
  prom, at both rows: of the promise's five clauses three ride (the slot's own condition; no mark;
    the shared chain's promise on Omega while its pin is open): left to the table's own files.
    What is left are the book-keeping's Bools: at row 1 `PL.shape 2` from `PL.shape 1` and the yes;
    at row 3 `PL.shape 4` and `PL.nothingLeft` from `PL.shape 3` and the end's yes.
  pins: whoever fills the meaning's letters, with a test on the plan's numbers (the three tenants'
    trees lie below the block's base).

Every "there is", walked: none stands in a statement here.
Limits. RULES UNDER LETTERS: no block of the protocol is named, no row is closed. A block that
refuses all meets both lists for nothing. `PinsReadBelow` cannot be proved at letters. THAT THE
THREE TENANTS' TREES (W's, the index masks', Omega's) LIE BELOW THE BASE OF THE PIECE AT ROW 1 AT A
REAL PLAN IS NOT CHECKED HERE: they are sent by the two earlier chains, and a piece's base counts
trees through the whole file: so it is expected; if one lay at or above it, `RowOneOwed` could not
be met and `rowOne` would say nothing.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.BordersLastQProofs
import Johnson.Desc.Sound.StringsStay
import Johnson.Desc.Sound.SendLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString Doomed)
open VerifiableInference.Desc.Shared
open VerifiableInference.Desc.Last

/-! ## 1 General in the table -/

/-- **A block whose row closes nothing has its own law where the promise is kept.** -/
def OwnOfNoItem : Prop :=
  ∀ (S Cl W ι : Type) (C : CK) (F : Frame) (p : Piece C F S Cl W) (on on' : S × F.E.Str → Prop)
    (means : ι → S × F.E.Str → W → Prop) (In Out : ι → Prop),
    (∀ i, ¬ In i) → (∀ a τ b, on a → p.ior.red.out a τ = some b → on' b) →
    p.Own on on' means In Out

/-- What a claim says of a statement reads the oracles' strings through the stored table and the
trees below lo alone. -/
def ReadsBelowAt {S W : Type} {F : Frame} (lo : ℕ) (m : S × F.E.Str → W → Prop) : Prop :=
  ∀ (s : S) (y y' : F.E.Str) (w : W), (∀ x, cellAt F y' x = cellAt F y x) →
    (∀ j x, j < lo → colAt F y' j x = colAt F y j x) → m (s, y') w → m (s, y) w

/-- **A block that hands the record on as it is, with the idle extractor, keeps every item that
reads below its base.** -/
def FramesOfQuiet : Prop :=
  ∀ (S Cl W ι : Type) (C : CK) (F : Frame) (p : Piece C F S Cl W) (on on' : S × F.E.Str → Prop)
    (means : ι → S × F.E.Str → W → Prop) (O In : ι → Prop),
    (∀ a τ b, on a → p.ior.red.out a τ = some b → b.1 = a.1) → (∀ a τ w, p.ext a τ w = w) →
    (∀ i, O i → ¬ In i → ReadsBelowAt p.base (means i)) →
    p.Frames on on' means O In

/-- Where nothing is open nothing is owed for what rides. -/
def FramesOfNoneOpen : Prop :=
  ∀ (S Cl W ι : Type) (C : CK) (F : Frame) (p : Piece C F S Cl W) (on on' : S × F.E.Str → Prop)
    (means : ι → S × F.E.Str → W → Prop) (O In : ι → Prop),
    (∀ i, ¬ O i) → p.Frames on on' means O In

theorem ownOfNoItem : OwnOfNoItem := by
  intro S Cl W ι C F p on on' means In Out hIn hp a ha
  exact Doomed.of_forall _ _ fun τ b hb =>
    ⟨hp a τ b ha hb, fun _ _ i hi => absurd hi (hIn i)⟩

theorem framesOfQuiet : FramesOfQuiet := by
  intro S Cl W ι C F p on on' means O In hs hid hr a τ b w i ha hb _ hO hI hm
  rw [hid]
  have hb' : b = (a.1, behind C F p.base p.ds a.2 τ) :=
    Prod.ext (hs a τ b ha hb) (out_behind p a b τ hb)
  rw [hb'] at hm
  exact hr i hO hI a.1 a.2 (behind C F p.base p.ds a.2 τ) w
    (fun x => cellStays C F p.base p.ds a.2 τ x)
    (fun j x hj => colStays C F p.base p.ds a.2 τ j x hj) hm

theorem framesOfNoneOpen : FramesOfNoneOpen :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ hO _ _ _ _ i _ _ _ hi _ _ => absurd hi (hO i)

/-! ## 2 At the last chain's table -/

/-- Rows 1 and 3 close nothing and read nothing. -/
theorem ins_one (i : ItemL) : ¬ insQ₃ 1 i := fun h => nomatch h
theorem ins_three (i : ItemL) : ¬ insQ₃ 3 i := fun h => nomatch h

/-- What is open at border 1: the three pins and the rows. -/
def OpenAtOne : Prop :=
  ∀ i : ItemL, openAfter insQ₃ outsQ₃ (· ∈ startLast) 1 i →
    i = .pinI ∨ i = .pinV ∨ i = .pinO ∨ i = .rows

/-- Nothing is open at border 3. -/
def NoneOpenAtThree : Prop := ∀ i : ItemL, ¬ openAfter insQ₃ outsQ₃ (· ∈ startLast) 3 i

theorem openAtOne : OpenAtOne := by
  intro i h
  have h' := (openIsList ItemL insL₃ outsL₃ startLast 1 i).1 h
  have e : openL insL₃ outsL₃ startLast 1 = [.pinI, .pinV, .pinO, .rows] := by decide
  rw [e] at h'
  rcases List.mem_cons.1 h' with rfl | h'
  · exact Or.inl rfl
  rcases List.mem_cons.1 h' with rfl | h'
  · exact Or.inr (Or.inl rfl)
  rcases List.mem_cons.1 h' with rfl | h'
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (List.mem_singleton.1 h')))

theorem noneOpenAtThree : NoneOpenAtThree := by
  intro i h
  have h' := (openIsList ItemL insL₃ outsL₃ startLast 3 i).1 h
  have e : openL insL₃ outsL₃ startLast 3 = [] := by decide
  rw [e] at h'
  cases h'

section
variable {P S₁ S₂ S₃ Cl Wt : Type} {C : CK} {Fr : Frame} (N : NumbersS)
  (Mg : MeaningS S₂ (P × S₁) Wt) (ML : MeaningL S₃ Wt) (Pm : PromMeaning S₂)
  (PL : PromMeaningL S₂ S₃ (P × S₁)) (Oc : P × S₁ → Strs → Prop)

/-- **The three pins read the strings through the stored table and the trees below lo alone**: a
condition on the meaning's letters. -/
def PinsReadBelow (lo : ℕ) : Prop :=
  ∀ i : ItemL, i = .pinI ∨ i = .pinV ∨ i = .pinO →
    ∀ (p : P × S₁) (e : S₂) (s : S₃) (y y' : Strs) (w : Wt), (∀ x, y'.cell x = y.cell x) →
      (∀ j x, j < lo → y'.col j x = y.col j x) → i.holds N Mg ML p e s y' w →
      i.holds N Mg ML p e s y w

/-- **WHAT IS OWED AT ROW 1** (the taken trees' sources), of the piece x that stands there. -/
structure RowOneOwed (x : Piece C Fr ((P × S₁ × S₂) × S₃) Cl Wt) : Prop where
  /-- where it says yes inside the promise the record goes on as it is -/
  same : ∀ a τ b, onQ₃ N Mg Pm PL Oc 1 a → x.ior.red.out a τ = some b → b.1 = a.1
  /-- its extractor is the identity -/
  idle : ∀ a τ w, x.ext a τ w = w
  /-- the promise behind follows from the promise in front and its yes -/
  prom : ∀ a τ b, onQ₃ N Mg Pm PL Oc 1 a → x.ior.red.out a τ = some b → onQ₃ N Mg Pm PL Oc 2 b
  /-- the three pins read below its base -/
  pins : PinsReadBelow (S₃ := S₃) N Mg ML x.base

/-- **WHAT IS OWED AT ROW 3** (the chain's end), of the piece x that stands there: the promise
behind follows from the promise in front and its yes. -/
def RowThreeOwed (x : Piece C Fr ((P × S₁ × S₂) × S₃) Cl Wt) : Prop :=
  ∀ a τ b, onQ₃ N Mg Pm PL Oc 3 a → x.ior.red.out a τ = some b → onQ₃ N Mg Pm PL Oc 4 b

/-- **ROW 1's TWO CONJUNCTS OF `EachOwn`.** -/
theorem rowOne (x : Piece C Fr ((P × S₁ × S₂) × S₃) Cl Wt) (h : RowOneOwed N Mg ML Pm PL Oc x) :
    x.Own (onQ₃ N Mg Pm PL Oc 1) (onQ₃ N Mg Pm PL Oc 2) (meansQ₃ N Mg ML) (insQ₃ 1) (outsQ₃ 1) ∧
      x.Frames (onQ₃ N Mg Pm PL Oc 1) (onQ₃ N Mg Pm PL Oc 2) (meansQ₃ N Mg ML)
        (openAfter insQ₃ outsQ₃ (· ∈ startLast) 1) (insQ₃ 1) := by
  refine ⟨ownOfNoItem _ _ _ _ _ _ x _ _ _ _ _ ins_one h.prom,
    framesOfQuiet _ _ _ _ _ _ x _ _ _ _ _ h.same h.idle fun i hO _ s y y' w hc hl hm => ?_⟩
  rcases openAtOne i hO with rfl | rfl | rfl | rfl
  · exact h.pins .pinI (Or.inl rfl) _ _ _ (strsOf Fr y) (strsOf Fr y') w hc hl hm
  · exact h.pins .pinV (Or.inr (Or.inl rfl)) _ _ _ (strsOf Fr y) (strsOf Fr y') w hc hl hm
  · exact h.pins .pinO (Or.inr (Or.inr rfl)) _ _ _ (strsOf Fr y) (strsOf Fr y') w hc hl hm
  · exact hm

/-- **ROW 3's TWO CONJUNCTS OF `EachOwn`.** -/
theorem rowThree (x : Piece C Fr ((P × S₁ × S₂) × S₃) Cl Wt)
    (h : RowThreeOwed N Mg Pm PL Oc x) :
    x.Own (onQ₃ N Mg Pm PL Oc 3) (onQ₃ N Mg Pm PL Oc 4) (meansQ₃ N Mg ML) (insQ₃ 3) (outsQ₃ 3) ∧
      x.Frames (onQ₃ N Mg Pm PL Oc 3) (onQ₃ N Mg Pm PL Oc 4) (meansQ₃ N Mg ML)
        (openAfter insQ₃ outsQ₃ (· ∈ startLast) 3) (insQ₃ 3) :=
  ⟨ownOfNoItem _ _ _ _ _ _ x _ _ _ _ _ ins_three h,
    framesOfNoneOpen _ _ _ _ _ _ x _ _ _ _ _ noneOpenAtThree⟩

/-- **`EachOwn` AT THE TABLE, OF ITS FOUR ROWS**: the two quiet rows as above; rows 0 and 2 as they
are owed by their files. -/
theorem eachOwn_of_rows (x₀ x₁ x₂ x₃ : Piece C Fr ((P × S₁ × S₂) × S₃) Cl Wt)
    (h₀ : x₀.Own (onQ₃ N Mg Pm PL Oc 0) (onQ₃ N Mg Pm PL Oc 1) (meansQ₃ N Mg ML) (insQ₃ 0)
        (outsQ₃ 0) ∧
      x₀.Frames (onQ₃ N Mg Pm PL Oc 0) (onQ₃ N Mg Pm PL Oc 1) (meansQ₃ N Mg ML)
        (openAfter insQ₃ outsQ₃ (· ∈ startLast) 0) (insQ₃ 0))
    (h₁ : RowOneOwed N Mg ML Pm PL Oc x₁)
    (h₂ : x₂.Own (onQ₃ N Mg Pm PL Oc 2) (onQ₃ N Mg Pm PL Oc 3) (meansQ₃ N Mg ML) (insQ₃ 2)
        (outsQ₃ 2) ∧
      x₂.Frames (onQ₃ N Mg Pm PL Oc 2) (onQ₃ N Mg Pm PL Oc 3) (meansQ₃ N Mg ML)
        (openAfter insQ₃ outsQ₃ (· ∈ startLast) 2) (insQ₃ 2))
    (h₃ : RowThreeOwed N Mg Pm PL Oc x₃) :
    EachOwn (onQ₃ N Mg Pm PL Oc) (meansQ₃ N Mg ML) insQ₃ outsQ₃ (· ∈ startLast) 0
      [x₀, x₁, x₂, x₃] :=
  ⟨h₀.1, h₀.2, (rowOne N Mg ML Pm PL Oc x₁ h₁).1, (rowOne N Mg ML Pm PL Oc x₁ h₁).2, h₂.1, h₂.2,
    (rowThree N Mg ML Pm PL Oc x₃ h₃).1, (rowThree N Mg ML Pm PL Oc x₃ h₃).2, trivial⟩

end

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.ownOfNoItem
#print axioms VerifiableInference.Desc.Sound.framesOfQuiet
#print axioms VerifiableInference.Desc.Sound.framesOfNoneOpen
#print axioms VerifiableInference.Desc.Sound.openAtOne
#print axioms VerifiableInference.Desc.Sound.noneOpenAtThree
#print axioms VerifiableInference.Desc.Sound.rowOne
#print axioms VerifiableInference.Desc.Sound.rowThree
#print axioms VerifiableInference.Desc.Sound.eachOwn_of_rows
