-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/KeyDecides.lean: THE KEY FILE'S NAMED HYPOTHESIS ON SOUNDNESS FROM ONE LAW FOR
EACH BLOCK, IN THE BLOCK'S OWN WORDS: "where `decide` returns, the proved typed verifier puts out
the reading of what is left".

The setting. `CompilerSoundnessConditionStatements.keySound` asks soundness for a language, not knowledge soundness: no witness
is handed to anybody. So the relations at the boundaries can be read with their witnesses bound by
"there is": then no extractor has anything to keep, and a block's tie to a proved typed block
(Johnson/Desc/Sound/TypedRow.lean) loses its clause on extractors. With the library's reading of
written rounds as typed rounds (`Maps`, OnBytes/Flat/CarrySMaps.lean) the reading and the counts are
written too, and with Johnson/Desc/Sound/RunIsDecide.lean the block's yes is its own `decide`.

What is said.
  `PieceSim`, `goodOfSim`: a block whose yes gives, at an image of the transcript, the typed
    verifier's out-statement as the reading of the statement behind, is good between "the typed
    joint's relation has a witness", read, in front and behind.
  AN INVARIANT OF THE CARRIED RECORD AT EVERY JOINT (inv): a property of statements that the typed
    side does not know (a word heard earlier is below the prime; a list has its length; two copies
    agree). The condition at a boundary is "the typed condition, read, and inv". A block's law is
    asked under inv in front and has to give inv behind, at every transcript.
  `DecideLaw`: THE ONE LAW OF A BLOCK: at every statement with inv whose reading has the typed
    condition, and every transcript at which the stage's own tests pass, every word shown is below
    the prime and what is shown has the declared shape: if `decide` returns s', the typed verifier
    at `M.view τ` puts out the reading of (s', the oracles left), and that statement has the next
    inv. `simOfDecide`.
  `SL`: a chain's blocks in a row, each with its stretch, its proved typed block, the maps of its
    rounds and the reading of the statements in front of it. `SL.pieces`: the chain's pieces,
    WRITTEN: each holds `below b`; its errors are `M.err k.err`. `SL.on`, `SL.rel`: the conditions
    and relations, WRITTEN. `SL.Laws`: for each block: the typed block is good and its out-joint has
    a witness's type that is not empty; the maps are in order; the law. `SL.Held`: the typed counts
    are held.
  `KeyCoreOfDecides`, `keyCoreOfDecides` (ending in `KeyCore`, Johnson/Desc/Sound/KeyCore.lean:
    what the hypothesis says, without the letters that it does not read) and `KeySoundOfDecides`,
    `keySoundOfDecides` (ending in the hypothesis itself): three such rows from `jWf` to a last
    joint Z: with `Three.Fits`, `RowFit`, two seam equations (and inv carried across each seam),
    "the first reading gives back the instance and the table, and the first inv holds there", "where
    the file's last test says yes, the last joint's relation has a witness", one leaf in the key
    file's request tree: `CompilerSoundnessConditionStatements.keySound`.
Trials: `decideLaw_trial_yes`, `decideLaw_trial_other`: a `decide` that returns where the typed
  verifier refuses at the image, or puts out another statement, does not meet the law.

Limits. A rule: no kind's law is shown here. The maps are blind to the rounds before and to the
statement. The decision of which the conclusion speaks is the three folds of the blocks `below b`:
by `FoldBelow` (Johnson/Desc/Sound/ChainRule.lean) the test that every word shown is below the
prime, then the fold of the blocks b. Those of KeyRule.lean.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.PassTie
import Johnson.Desc.Sound.BelowOfPieces
import Johnson.Desc.Sound.KeyCore
import Johnson.Flat.CarrySWhole

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.OnPublicFiles OnBytes.RunA
open _root_.Run (ckP)
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString)
open _root_.Iop.Reduction (orOff)

/-! ## 1 A block's yes gives the typed verifier's out-statement -/

section
variable {S Cl W : Type} {C : CK} {F : Frame}

/-- There is a reading of the block's rounds as the typed block's along which the block's errors
bear the typed ones, and: where the block says yes, the transcript has an image at which the typed
verifier puts out the reading of the statement behind the block. iA, iB: the invariants of the
carried record in front of and behind the block: the law is asked under the first and gives the
second. -/
def PieceSim (p : Piece C F S Cl W) {A B : JK} (k : BK A B)
    (rdA : S × F.E.Str → A.X × A.E.Str) (rdB : S × F.E.Str → B.X × B.E.Str)
    (iA iB : S × F.E.Str → Prop) : Prop :=
  ∃ G : S × F.E.Str → CarryS (uLT C p.ds) k.R.red.shape,
    (∀ a, (G a).Fits k.err p.err) ∧
    ∀ a τ a', A.on (rdA a) → iA a → p.ior.red.out a τ = some a' →
      iB a' ∧ ∃ τ', (G a).tr τ = some τ' ∧ k.R.red.out (rdA a) τ' = some (rdB a')

/-- **Such a block is good** between "the typed joint's relation has a witness", read, in front and
behind, whatever its extractor is. -/
theorem goodOfSim (p : Piece C F S Cl W) {A B : JK} (k : BK A B)
    (rdA : S × F.E.Str → A.X × A.E.Str) (rdB : S × F.E.Str → B.X × B.E.Str)
    (iA iB : S × F.E.Str → Prop) (hk : k.Good)
    (hB : Nonempty B.W) (ht : PieceSim p k rdA rdB iA iB) :
    (p.bk (fun a => A.on (rdA a) ∧ iA a) (fun a => B.on (rdB a) ∧ iB a)
      (fun a _ => ∃ w, A.relR (rdA a) w) (fun a _ => ∃ w, B.relR (rdB a) w)).Good := by
  obtain ⟨G, hfit, hyes⟩ := ht
  refine ⟨⟨pointsT C p.ds⟩, stageIOR_isLocal C p.stage p.run, ?_⟩
  exact pieceOfProved S Cl W C F p (A.X × A.E.Str) (B.X × B.E.Str) A.W B.W k.R.red G k.err rdA
    (fun a => A.on (rdA a) ∧ iA a) A.on (fun a _ => ∃ w, A.relR (rdA a) w)
    (orOff (fun a => B.on (rdB a) ∧ iB a) (fun a _ => ∃ w, B.relR (rdB a) w)) A.relR
    (orOff B.on B.relR) k.ext hfit (fun _ h => h.1)
    (fun a τ a' w ha ho hw => by
      obtain ⟨hi, τ', h1, h2⟩ := hyes a τ a' ha.1 ha.2 ho
      rcases hw with ⟨w', hw'⟩ | hn
      · exact ⟨τ', rdB a', w', h1, h2, Or.inl hw', fun h => ⟨_, h⟩⟩
      · exact hB.elim fun w' =>
          ⟨τ', rdB a', w', h1, h2, Or.inr fun h => hn ⟨h, hi⟩, fun h => ⟨_, h⟩⟩)
    hk.know

end

/-! ## 2 The one law of a block -/

section
variable {S Cl : Type} {F : Frame}

/-- **The one law of a block**, in the block's own words. -/
def DecideLaw (b : Block S Cl) (base : ℕ) (ds : List RDT) (back : List Fmt.RoundView) {A B : JK}
    (k : BK A B) (M : Maps ds k.R.red.shape)
    (rdA : S × F.E.Str → A.X × A.E.Str) (rdB : S × F.E.Str → B.X × B.E.Str)
    (iA iB : S × F.E.Str → Prop) : Prop :=
  ∀ (s s' : S) (y : F.E.Str) (τ : Iop.Tr (uLT (ckP .two) ds)),
    A.on (rdA (s, y)) → iA (s, y) →
    sTests (ckP .two) (stg F base ds) y τ = true →
    viewWordsBelowPrime (sView (ckP .two) (stg F base ds) y τ) = true →
    Shown F.ft b ((sView (ckP .two) (stg F base ds) y τ).rounds ++ back)
      (sView (ckP .two) (stg F base ds) y τ).opened →
    b.decide s (((sView (ckP .two) (stg F base ds) y τ).rounds ++ back).map noDigest)
      (groupsAt F.ft b ((sView (ckP .two) (stg F base ds) y τ).rounds ++ back)
        (sView (ckP .two) (stg F base ds) y τ).opened) = .ok s' →
    iB (s', (y.1, sLeft (ckP .two) (stg F base ds) y τ)) ∧
      k.R.red.out (rdA (s, y)) (M.view τ) =
        some (rdB (s', (y.1, sLeft (ckP .two) (stg F base ds) y τ)))

/-- A block with its stretch, read along M as the typed block k: it holds `below b`; its errors are
the written counts that bear k's; its extractor hands the witness back. -/
def seatPiece (W : Type) (b : Block S Cl) (base : ℕ) (ds : List RDT) (back : List Fmt.RoundView)
    {A B : JK} (k : BK A B) (M : Maps ds k.R.red.shape) : Piece (ckP .two) F S Cl W :=
  (⟨b, base, ds, back, fun _ _ w => w, M.err k.err⟩ : Piece (ckP .two) F S Cl W).below

theorem simOfDecide (W : Type) (b : Block S Cl) (base : ℕ) (ds : List RDT) (back : List Fmt.RoundView)
    {A B : JK} (k : BK A B) (M : Maps ds k.R.red.shape)
    (rdA : S × F.E.Str → A.X × A.E.Str) (rdB : S × F.E.Str → B.X × B.E.Str)
    (iA iB : S × F.E.Str → Prop) (hM : M.OK) (hb : viewWordsBelowPrime ⟨back, []⟩ = true)
    (h : DecideLaw b base ds back k M rdA rdB iA iB) :
    PieceSim (seatPiece (F := F) W b base ds back k M) k rdA rdB iA iB := by
  refine ⟨fun _ => M.carry, fun _ => M.fits hM k.err, ?_⟩
  intro a τ a' ha hi ho
  obtain ⟨hw, ho'⟩ := Piece.below_out
    (⟨b, base, ds, back, fun _ _ w => w, M.err k.err⟩ : Piece (ckP .two) F S Cl W) hb a a' τ ho
  obtain ⟨h1, h2, h3, h4⟩ := (Piece.out_iff
    (⟨b, base, ds, back, fun _ _ w => w, M.err k.err⟩ : Piece (ckP .two) F S Cl W) a a' τ).1 ho'
  obtain ⟨s, y⟩ := a
  obtain ⟨s', y'⟩ := a'
  have hp : M.pass τ = true :=
    Maps.pass_of_passT M τ (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 h1).1).1
  have e1 := h s s' y τ ha hi h1 hw h2 h3
  have h4' : y' = (y.1, sLeft (ckP .two) (stg F base ds) y τ) := h4
  rw [h4']
  exact ⟨e1.1, M.view τ, M.tr_of_pass τ hp, e1.2⟩

/-- A `decide` that returns where the typed verifier refuses at the image does not meet the
law.
-/
theorem decideLaw_trial_yes (b : Block S Cl) (base : ℕ) (ds : List RDT) (back : List Fmt.RoundView)
    {A B : JK} (k : BK A B) (M : Maps ds k.R.red.shape)
    (rdA : S × F.E.Str → A.X × A.E.Str) (rdB : S × F.E.Str → B.X × B.E.Str)
    (iA iB : S × F.E.Str → Prop) (s s' : S) (y : F.E.Str) (τ : Iop.Tr (uLT (ckP .two) ds))
    (ha : A.on (rdA (s, y))) (hi : iA (s, y)) (h1 : sTests (ckP .two) (stg F base ds) y τ = true)
    (hw : viewWordsBelowPrime (sView (ckP .two) (stg F base ds) y τ) = true)
    (h2 : Shown F.ft b ((sView (ckP .two) (stg F base ds) y τ).rounds ++ back)
      (sView (ckP .two) (stg F base ds) y τ).opened)
    (h3 : b.decide s (((sView (ckP .two) (stg F base ds) y τ).rounds ++ back).map noDigest)
      (groupsAt F.ft b ((sView (ckP .two) (stg F base ds) y τ).rounds ++ back)
        (sView (ckP .two) (stg F base ds) y τ).opened) = .ok s')
    (hno : k.R.red.out (rdA (s, y)) (M.view τ) = none) :
    ¬ DecideLaw b base ds back k M rdA rdB iA iB := fun h => by
  have e := (h s s' y τ ha hi h1 hw h2 h3).2
  rw [hno] at e
  cases e

/-- Nor does one that leaves a record whose reading is not what the typed verifier puts out.
-/
theorem decideLaw_trial_other (b : Block S Cl) (base : ℕ) (ds : List RDT) (back : List Fmt.RoundView)
    {A B : JK} (k : BK A B) (M : Maps ds k.R.red.shape)
    (rdA : S × F.E.Str → A.X × A.E.Str) (rdB : S × F.E.Str → B.X × B.E.Str)
    (iA iB : S × F.E.Str → Prop) (s s' : S) (y : F.E.Str) (τ : Iop.Tr (uLT (ckP .two) ds))
    (ha : A.on (rdA (s, y))) (hi : iA (s, y)) (h1 : sTests (ckP .two) (stg F base ds) y τ = true)
    (hw : viewWordsBelowPrime (sView (ckP .two) (stg F base ds) y τ) = true)
    (h2 : Shown F.ft b ((sView (ckP .two) (stg F base ds) y τ).rounds ++ back)
      (sView (ckP .two) (stg F base ds) y τ).opened)
    (h3 : b.decide s (((sView (ckP .two) (stg F base ds) y τ).rounds ++ back).map noDigest)
      (groupsAt F.ft b ((sView (ckP .two) (stg F base ds) y τ).rounds ++ back)
        (sView (ckP .two) (stg F base ds) y τ).opened) = .ok s')
    (hne : k.R.red.out (rdA (s, y)) (M.view τ) ≠
      some (rdB (s', (y.1, sLeft (ckP .two) (stg F base ds) y τ)))) :
    ¬ DecideLaw b base ds back k M rdA rdB iA iB :=
  fun h => hne (h s s' y τ ha hi h1 hw h2 h3).2

/-! ## 3 A chain's blocks in a row, each at its seat -/

/-- **A chain's blocks in a row**, from the typed joint A to the typed joint Z: each block with its
stretch (base, ds, back), its proved typed block k, the maps M of its rounds, and, of the statements
in front of it, the reading rd and the invariant inv. -/
inductive SL (S Cl : Type) (F : Frame) : JK → JK → Type 1
  | nil {A : JK} (rd : S × F.E.Str → A.X × A.E.Str) (inv : S × F.E.Str → Prop) : SL S Cl F A A
  | cons {A B Z : JK} (rd : S × F.E.Str → A.X × A.E.Str) (inv : S × F.E.Str → Prop)
      (b : Block S Cl) (base : ℕ)
      (ds : List RDT) (back : List Fmt.RoundView) (k : BK A B) (M : Maps ds k.R.red.shape)
      (l : SL S Cl F B Z) : SL S Cl F A Z

namespace SL

/-- The readings at the first and at the last joint. -/
def rd0 : {A Z : JK} → SL S Cl F A Z → S × F.E.Str → A.X × A.E.Str
  | _, _, .nil rd _ => rd
  | _, _, .cons rd _ _ _ _ _ _ _ _ => rd
def rdZ : {A Z : JK} → SL S Cl F A Z → S × F.E.Str → Z.X × Z.E.Str
  | _, _, .nil rd _ => rd
  | _, _, .cons _ _ _ _ _ _ _ _ l => l.rdZ

/-- The invariants at the first and at the last joint. -/
def inv0 : {A Z : JK} → SL S Cl F A Z → S × F.E.Str → Prop
  | _, _, .nil _ inv => inv
  | _, _, .cons _ inv _ _ _ _ _ _ _ => inv
def invZ : {A Z : JK} → SL S Cl F A Z → S × F.E.Str → Prop
  | _, _, .nil _ inv => inv
  | _, _, .cons _ _ _ _ _ _ _ _ l => l.invZ

def len : {A Z : JK} → SL S Cl F A Z → ℕ
  | _, _, .nil _ _ => 0
  | _, _, .cons _ _ _ _ _ _ _ _ l => l.len + 1

/-- **The chain's pieces, written.** -/
def pieces (W : Type) : {A Z : JK} → SL S Cl F A Z → List (Piece (ckP .two) F S Cl W)
  | _, _, .nil _ _ => []
  | _, _, .cons _ _ b base ds back k M l => seatPiece W b base ds back k M :: l.pieces W

/-- **The condition at the boundary with the number i**: the typed joint's, read, and the invariant.
-/
def on : {A Z : JK} → SL S Cl F A Z → ℕ → S × F.E.Str → Prop
  | A, _, .nil rd inv, _ => fun a => A.on (rd a) ∧ inv a
  | A, _, .cons rd inv _ _ _ _ _ _ _, 0 => fun a => A.on (rd a) ∧ inv a
  | _, _, .cons _ _ _ _ _ _ _ _ l, i + 1 => l.on i

/-- **The relation at the boundary with the number i**: the typed joint's relation, read, has a
witness. -/
def rel (W : Type) : {A Z : JK} → SL S Cl F A Z → ℕ → S × F.E.Str → W → Prop
  | A, _, .nil rd _, _ => fun a _ => ∃ w, A.relR (rd a) w
  | A, _, .cons rd _ _ _ _ _ _ _ _, 0 => fun a _ => ∃ w, A.relR (rd a) w
  | _, _, .cons _ _ _ _ _ _ _ _ l, i + 1 => l.rel W i

/-- **What is asked of each block.** -/
def Laws : {A Z : JK} → SL S Cl F A Z → Prop
  | _, _, .nil _ _ => True
  | _, _, .cons (B := B) rd inv b base ds back k M l =>
    (k.Good ∧ Nonempty B.W ∧ M.OK ∧ viewWordsBelowPrime ⟨back, []⟩ = true ∧
      DecideLaw b base ds back k M rd l.rd0 inv l.inv0) ∧ l.Laws

/-- The typed blocks' counts, with the sampler's bias and the rounds' work, are shares of at most
εs.
-/
def Held (εs : ℝ≥0∞) : {A Z : JK} → SL S Cl F A Z → Prop
  | _, _, .nil _ _ => True
  | _, _, .cons _ _ _ _ _ _ k M l => M.Held εs k.err ∧ l.Held εs

theorem on_zero {A Z : JK} (L : SL S Cl F A Z) :
    L.on 0 = fun a => A.on (L.rd0 a) ∧ L.inv0 a := by
  cases L <;> rfl
theorem rel_zero (W : Type) {A Z : JK} (L : SL S Cl F A Z) :
    L.rel W 0 = fun a _ => ∃ w, A.relR (L.rd0 a) w := by
  cases L <;> rfl
theorem on_len {A Z : JK} (L : SL S Cl F A Z) :
    L.on L.len = fun a => Z.on (L.rdZ a) ∧ L.invZ a := by
  induction L with
  | nil rd inv => rfl
  | cons rd inv b base ds back k M l ih => exact ih
theorem rel_len (W : Type) {A Z : JK} (L : SL S Cl F A Z) :
    L.rel W L.len = fun a _ => ∃ w, Z.relR (L.rdZ a) w := by
  induction L with
  | nil rd inv => rfl
  | cons rd inv b base ds back k M l ih => exact ih
theorem pieces_len (W : Type) {A Z : JK} (L : SL S Cl F A Z) : (L.pieces W).length = L.len := by
  induction L with
  | nil rd inv => rfl
  | cons rd inv b base ds back k M l ih => exact congrArg (· + 1) ih

end SL

/-- **A chain whose blocks meet their laws meets the premise of the rule of composition.** -/
theorem eachGoodOfLaws (W : Type) : ∀ {A Z : JK} (L : SL S Cl F A Z), L.Laws →
    EachGood L.on (L.rel W) 0 (L.pieces W)
  | _, _, .nil _ _, _ => trivial
  | A, _, .cons rd inv b base ds back k M l, h => by
    refine ⟨?_, eachGood_shift _ _ _ 0 (eachGoodOfLaws W l h.2)⟩
    obtain ⟨hk, hB, hM, hb, hd⟩ := h.1
    have g := goodOfSim (seatPiece (F := F) W b base ds back k M) k rd l.rd0 inv l.inv0 hk hB
      (simOfDecide W b base ds back k M rd l.rd0 inv l.inv0 hM hb hd)
    show ((seatPiece (F := F) W b base ds back k M).bk (fun a => A.on (rd a) ∧ inv a) (l.on 0)
      (fun a _ => ∃ w, A.relR (rd a) w) (l.rel W 0)).Good
    rw [l.on_zero, l.rel_zero W]
    exact g

/-- Its pieces' errors are shares of at most εs where the typed counts are held. -/
theorem belowOfHeld (W : Type) (εs : ℝ≥0∞) : ∀ {A Z : JK} (L : SL S Cl F A Z), L.Laws →
    L.Held εs → ∀ q ∈ L.pieces W, Err.Below q.err εs
  | _, _, .nil _ _, _, _, _, hq => by cases hq
  | _, _, .cons _ _ b base ds back k M l, h, hh, q, hq => by
    rcases List.mem_cons.1 hq with rfl | hq'
    · exact M.below_err h.1.2.2.1 k.err hh.1
    · exact belowOfHeld W εs l h.2 hh.2 q hq'

end

theorem times_one : ∀ {s : Shape} (ε : Err s), Err.times 1 ε = ε
  | [], _ => rfl
  | _ :: _, (e, ε) => by
    show (1 * e, Err.times 1 ε) = (e, ε)
    rw [Nat.one_mul, times_one ε]

/-! ## 4 The key file -/

/-- **What the key file's hypothesis on soundness says (`KeyCore`), from one law for each block**,
at one leaf in the request tree. -/
def KeyCoreOfDecides : Prop :=
  ∀ (a : ℕ) (Kc : ConfLetters a) (DK : WholeD) (TFk TJk T3k : Type) (tFk : TFk)
    (tJk : TJk) (t3k : T3k) (silK : Kc.conf.Rec → TFk → TJk → T3k → Bool)
    (all : List LeftT) (S₁ S₂ S₃ X₁ X₂ Cl W : Type)
    (T : Three (ckP .two) (DK.at a) all Kc.conf.Rec S₁ S₂ S₃ X₁ X₂ Cl W) (J₁ J₂ Z : JK)
    (L₁ : SL S₁ Cl (frameAt (DK.at a) all (DK.at a).key₁ T.ft₁) (jWf Kc.conf) J₁)
    (L₂ : SL S₂ Cl (frameAt (DK.at a) all (DK.at a).key₂ T.ft₂) J₁ J₂)
    (L₃ : SL S₃ Cl (frameAt (DK.at a) all (DK.at a).key₃ T.ft₃) J₂ Z) (εs : ℝ≥0∞),
    T.p₁ :: T.l₁ = L₁.pieces W → T.p₂ :: T.l₂ = L₂.pieces W → T.p₃ :: T.l₃ = L₃.pieces W →
    T.Fits → L₁.Laws → L₂.Laws → L₃.Laws →
    (∀ rec y, L₁.rd0 (T.in₁ rec, (y, fun _ => [])) = (rec, y) ∧
      L₁.inv0 (T.in₁ rec, (y, fun _ => []))) →
    (∀ x b, L₂.rd0 (T.in₂ (T.out₁ x b.1), b.2) = L₁.rdZ b ∧
      (L₁.invZ b → L₂.inv0 (T.in₂ (T.out₁ x b.1), b.2))) →
    (∀ x b s, T.in₃ (T.out₂ x b.1) = some s → L₃.rd0 (s, b.2) = L₂.rdZ b ∧
      (L₂.invZ b → L₃.inv0 (s, b.2))) →
    (∀ x b, T.fin x b.1 = true → Z.on (L₃.rdZ b) → L₃.invZ b → ∃ w, Z.relR (L₃.rdZ b) w) →
    RowFit (DK.at a) all all →
    L₁.Held εs → L₂.Held εs → L₃.Held εs →
    KeyCore Kc DK tFk tJk t3k silK (runRow T.run₁ T.run₂ T.run₃) 1 εs

theorem keyCoreOfDecides : KeyCoreOfDecides := by
  intro a Kc DK TFk TJk T3k tFk tJk t3k silK
    all S₁ S₂ S₃ X₁ X₂ Cl W T J₁ J₂ Z L₁ L₂ L₃ εs e₁ e₂ e₃ hf w₁ w₂ w₃ hfirst hs₁ hs₂ hlast
    hfit d₁ d₂ d₃
  have n₁ : 1 + T.l₁.length = L₁.len := by
    have := congrArg List.length e₁
    rw [List.length_cons, L₁.pieces_len W] at this
    omega
  have n₂ : 1 + T.l₂.length = L₂.len := by
    have := congrArg List.length e₂
    rw [List.length_cons, L₂.pieces_len W] at this
    omega
  have n₃ : 1 + T.l₃.length = L₃.len := by
    have := congrArg List.length e₃
    rw [List.length_cons, L₃.pieces_len W] at this
    omega
  let Q : Places (DK.at a) all S₁ S₂ S₃ W :=
    ⟨L₁.on, L₁.rel W, L₂.on, L₂.rel W, L₃.on, L₃.rel W⟩
  have hgl : T.Glued Q :=
    { glue₁ := by
        intro x b w hm
        have h' : orOff (L₂.on 0) (L₂.rel W 0) (T.in₂ (T.out₁ x b.1), b.2) w := hm
        rw [L₂.on_zero, L₂.rel_zero W] at h'
        show orOff (L₁.on (1 + T.l₁.length)) (L₁.rel W (1 + T.l₁.length)) b w
        rw [n₁, L₁.on_len, L₁.rel_len W]
        have h2 : (∃ w', J₁.relR (L₂.rd0 (T.in₂ (T.out₁ x b.1), b.2)) w') ∨
            ¬ (J₁.on (L₂.rd0 (T.in₂ (T.out₁ x b.1), b.2)) ∧
              L₂.inv0 (T.in₂ (T.out₁ x b.1), b.2)) := h'
        rw [(hs₁ x b).1] at h2
        exact h2.imp id fun hn hc => hn ⟨hc.1, (hs₁ x b).2 hc.2⟩
      glue₂ := by
        intro x b w hm
        obtain ⟨s, hs, hm⟩ := hm
        have h' : orOff (L₃.on 0) (L₃.rel W 0) (s, b.2) w := hm
        rw [L₃.on_zero, L₃.rel_zero W] at h'
        show orOff (L₂.on (1 + T.l₂.length)) (L₂.rel W (1 + T.l₂.length)) b w
        rw [n₂, L₂.on_len, L₂.rel_len W]
        have h2 : (∃ w', J₂.relR (L₃.rd0 (s, b.2)) w') ∨
            ¬ (J₂.on (L₃.rd0 (s, b.2)) ∧ L₃.inv0 (s, b.2)) := h'
        rw [(hs₂ x b s hs).1] at h2
        exact h2.imp id fun hn hc => hn ⟨hc.1, (hs₂ x b s hs).2 hc.2⟩
      ends := by
        intro x b hb
        show orOff (L₃.on (1 + T.l₃.length)) (L₃.rel W (1 + T.l₃.length)) b T.wEnd
        rw [n₃, L₃.on_len, L₃.rel_len W]
        by_cases hc : Z.on (L₃.rdZ b) ∧ L₃.invZ b
        · exact Or.inl (hlast x b hb hc.1 hc.2)
        · exact Or.inr hc }
  exact keyCoreOfBlocks a Kc DK TFk TJk T3k tFk tJk t3k silK all S₁ S₂ S₃ X₁ X₂ Cl W T Q yes₂ yes₂
    yes₂ hf.shape₁ hf.shape₂ hf.shape₃ 1 εs hf
    (e₁ ▸ eachGoodOfLaws W L₁ w₁) (e₂ ▸ eachGoodOfLaws W L₂ w₂) (e₃ ▸ eachGoodOfLaws W L₃ w₃)
    hgl hfit
    (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ _ _ _ _ _ => rfl)
    (fun rec y h => by
      have h' : L₁.on 0 (T.in₁ rec, (y, fun _ => [])) →
          ∃ w, L₁.rel W 0 (T.in₁ rec, (y, fun _ => [])) w := h
      rw [L₁.on_zero, L₁.rel_zero W] at h'
      have h2 : Kc.conf.free (L₁.rd0 (T.in₁ rec, (y, fun _ => []))) ∧
          L₁.inv0 (T.in₁ rec, (y, fun _ => [])) →
          ∃ _ : W, ∃ u, Kc.conf.RwfR (L₁.rd0 (T.in₁ rec, (y, fun _ => []))) u := h'
      rw [(hfirst rec y).1] at h2
      exact (keyL_iff Kc rec y).2 fun hfr =>
        (h2 ⟨hfr, (hfirst rec y).2⟩).elim fun _ hw => hw.elim fun _ hu => hu)
    (belowOfPieces (ckP .two) (DK.at a) all Kc.conf.Rec S₁ S₂ S₃ X₁ X₂ Cl W TFk TJk T3k tFk tJk t3k
      T Q yes₂ yes₂ yes₂ hf.shape₁ hf.shape₂ hf.shape₃ 1 εs
      (e₁ ▸ belowOfHeld W εs L₁ w₁ d₁)
      (by
        intro q hq
        rw [times_one]
        exact (e₂ ▸ belowOfHeld W εs L₂ w₂ d₂) q hq)
      (e₃ ▸ belowOfHeld W εs L₃ w₃ d₃))

/-- **The key file's hypothesis on soundness itself**, at the three protocols of `filesOf` whose key
file's decision is the three folds in a row, at a wire whose key file's request tree has one leaf.
-/
def KeySoundOfDecides : Prop :=
  ∀ (a : ℕ) (Kc : ConfLetters a) (DK DP : WholeD) (TFk TJk T3k TFp TJp T3p : Type) (tFk : TFk)
    (tJk : TJk) (t3k : T3k) (tFp : TFp) (tJp : TJp) (t3p : T3p)
    (silK : Kc.conf.Rec → TFk → TJk → T3k → Bool)
    (silP : Kc.conf.X × Kc.conf.Rec → TFp → TJp → T3p → Bool)
    (runP : Kc.conf.X × Kc.conf.Rec → Fmt.View → Fmt.View → Fmt.View → Bool)
    (eL : LinkProtocolWithLeafCoding Kc.conf.Rec a) (N : ℕ) (early : Kc.conf.X → Kc.conf.X) (late : Option ℕ)
    (all : List LeftT) (S₁ S₂ S₃ X₁ X₂ Cl W : Type)
    (T : Three (ckP .two) (DK.at a) all Kc.conf.Rec S₁ S₂ S₃ X₁ X₂ Cl W) (J₁ J₂ Z : JK)
    (L₁ : SL S₁ Cl (frameAt (DK.at a) all (DK.at a).key₁ T.ft₁) (jWf Kc.conf) J₁)
    (L₂ : SL S₂ Cl (frameAt (DK.at a) all (DK.at a).key₂ T.ft₂) J₁ J₂)
    (L₃ : SL S₃ Cl (frameAt (DK.at a) all (DK.at a).key₃ T.ft₃) J₂ Z)
    (P : (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK (runRow T.run₁ T.run₂ T.run₃) silP
      runP eL N early late).Provers)
    (Tl : InnerCompilerInputFieldsOverThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK
                                      (runRow T.run₁ T.run₂ T.run₃) silP runP eL N early late) P)
    (U : SoundnessAnalysisFieldsOverThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK
                                       (runRow T.run₁ T.run₂ T.run₃) silP runP eL N early late) P),
    T.p₁ :: T.l₁ = L₁.pieces W → T.p₂ :: T.l₂ = L₂.pieces W → T.p₃ :: T.l₃ = L₃.pieces W →
    T.Fits → L₁.Laws → L₂.Laws → L₃.Laws →
    (∀ rec y, L₁.rd0 (T.in₁ rec, (y, fun _ => [])) = (rec, y) ∧
      L₁.inv0 (T.in₁ rec, (y, fun _ => []))) →
    (∀ x b, L₂.rd0 (T.in₂ (T.out₁ x b.1), b.2) = L₁.rdZ b ∧
      (L₁.invZ b → L₂.inv0 (T.in₂ (T.out₁ x b.1), b.2))) →
    (∀ x b s, T.in₃ (T.out₂ x b.1) = some s → L₃.rd0 (s, b.2) = L₂.rdZ b ∧
      (L₂.invZ b → L₃.inv0 (s, b.2))) →
    (∀ x b, T.fin x b.1 = true → Z.on (L₃.rdZ b) → L₃.invZ b → ∃ w, Z.relR (L₃.rdZ b) w) →
    RowFit (DK.at a) all all →
    Tl.W.depthReqT = 0 → L₁.Held U.εs → L₂.Held U.εs → L₃.Held U.εs →
    CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataOfThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK
                                                               (runRow T.run₁ T.run₂ T.run₃) silP runP eL N early late) P Tl U)

theorem keySoundOfDecides : KeySoundOfDecides := by
  intro a Kc DK DP TFk TJk T3k TFp TJp T3p tFk tJk t3k tFp tJp t3p silK silP runP eL N early late
    all S₁ S₂ S₃ X₁ X₂ Cl W T J₁ J₂ Z L₁ L₂ L₃ P Tl U e₁ e₂ e₃ hf w₁ w₂ w₃ hfirst hs₁ hs₂ hlast
    hfit hdep d₁ d₂ d₃
  rw [keySound_iff_core, hdep, pow_zero]
  exact keyCoreOfDecides a Kc DK TFk TJk T3k tFk tJk t3k silK all S₁ S₂ S₃ X₁ X₂ Cl W T J₁ J₂ Z L₁
    L₂ L₃ U.εs e₁ e₂ e₃ hf w₁ w₂ w₃ hfirst hs₁ hs₂ hlast hfit d₁ d₂ d₃

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.goodOfSim
#print axioms VerifiableInference.Desc.Sound.simOfDecide
#print axioms VerifiableInference.Desc.Sound.decideLaw_trial_yes
#print axioms VerifiableInference.Desc.Sound.decideLaw_trial_other
#print axioms VerifiableInference.Desc.Sound.eachGoodOfLaws
#print axioms VerifiableInference.Desc.Sound.belowOfHeld
#print axioms VerifiableInference.Desc.Sound.keyCoreOfDecides
#print axioms VerifiableInference.Desc.Sound.keySoundOfDecides
