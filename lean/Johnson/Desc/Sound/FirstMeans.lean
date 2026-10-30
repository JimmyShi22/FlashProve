-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/FirstMeans.lean: THE ROW "knows, at data whose first relation MEANS something":
from the table of joints. Definitions, statements written as `def … : Prop`, and their proofs.

Why. The top theorem's premise `knows` speaks of data whose first relation R₀ is a letter. What the
release needs is `knows` AT THE R₀ THAT SAYS "the witness's hidden values are a run of the integer
model on the request, with the committed weights". The table of joints has that relation in parts:
the items `constr m part`, all open at the chain's start, each closed by a kind's row; beside them
it holds what is pending there (the pins, the pile, no mark).

THE ROAD: THE WEAKER RELATION IS LAID INTO THE TABLE's OWN FIRST BOUNDARY. `frontAt R₀ R`: the
relations R with R₀ at boundary 0. `TieStart`: at the first boundary, inside the promise, "every
item that is open at the start holds" gives R₀. `EachGoodInFront`: a row that has `EachGoodIn` at R
has it at `frontAt R₀ R`, under that tie (a block's law may be weakened in front). `placesM`: a
file's conditions and relations: the first chain's := the table's, with R₀ in front; the other two
chains' are letters. `FirstChainMeans`: SO: every block's own law and the riding at the table
(`EachOwn`: THE KINDS'), with the tie, give `EachGoodIn` at `placesM`: JUST WHAT EVERY RULE
FOR A FILE ASKS OF THE FIRST CHAIN (`FileKnowsJOfGood` and the other rules at
a description): and the data that these rules make (`Three.snd`) then HAVE R₀, read at the chain's
first record, AS THEIR FIELD, by make. `FirstChainKnowsOf`: the clause for one statement, in the
library's own form.

Limits. (1) R₀ IS A LETTER HERE (meant: the integer model's `firstMeans` at what the witness hides);
`TieStart` is shown, as a theorem, in the upper storey, where `Meaning.constr` is filled by that
model's own clauses. At R₀ := fun _ _ => True it is free and the row says nothing. (2) A `constr`
that no row closes stays open to the chain's end, where nothing can pay it: `closesAll`
(Johnson/Desc/First/Borders.lean) is the test on the table. (3) The promise at the first boundary
(`onQ … 0`) is the row's condition: who pays it from the public tests:
Johnson/Desc/Sound/DescOn.lean [not in this library]. (4) What is claimed of what the chain hands on
must give what is
open at its end: `Three.Glue₁` at `placesM` (or the tie at the chains' ends, `tiedAt`): not shown
here.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.Sound.BordersQ
import Johnson.Desc.Sound.GoodInProofs
import Johnson.Desc.Sound.FileKnowsProof

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString Doomed)
open _root_.Iop.Reduction (orOff)
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers start)

/-- The relations R with R₀ at boundary 0. -/
def frontAt {A W : Type} (R₀ : A → W → Prop) (R : ℕ → A → W → Prop) : ℕ → A → W → Prop
  | 0 => R₀
  | k + 1 => R (k + 1)

/-- **A row's law may be weakened at its first boundary.** -/
def EachGoodInFront : Prop :=
  ∀ (S Cl W : Type) (C : CK) (F : Frame) (on : ℕ → S × F.E.Str → Prop)
    (R : ℕ → S × F.E.Str → W → Prop) (R₀ : S × F.E.Str → W → Prop) (p : Piece C F S Cl W)
    (l : List (Piece C F S Cl W)),
    (∀ a w, on 0 a → R 0 a w → R₀ a w) → EachGoodIn on R 0 (p :: l) →
    EachGoodIn on (frontAt R₀ R) 0 (p :: l)

theorem eachGoodIn_behind {S Cl W : Type} {C : CK} {F : Frame} (on : ℕ → S × F.E.Str → Prop)
    (R : ℕ → S × F.E.Str → W → Prop) (R₀ : S × F.E.Str → W → Prop)
    (l : List (Piece C F S Cl W)) :
    ∀ k, EachGoodIn on R (k + 1) l → EachGoodIn on (frontAt R₀ R) (k + 1) l := by
  induction l with
  | nil => exact fun _ _ => trivial
  | cons q l ih =>
    intro k h
    exact ⟨h.1, ih (k + 1) h.2⟩

theorem eachGoodInFront : EachGoodInFront := by
  intro S Cl W C F on R R₀ p l ht h
  refine ⟨fun a ha => ?_, eachGoodIn_behind on R R₀ l 0 h.2⟩
  refine Doomed.mono _ _ ?_ (h.1 a ha)
  intro τ hτ b hb
  exact ⟨(hτ b hb).1, fun w hw => ht a _ ha ((hτ b hb).2 w hw)⟩

section
variable {C : CK} {D : WholeD} {all : List LeftT} {Y P S₁ S₂ S₃ X₁ X₂ Cl W : Type}

/-- **The tie at the chain's first boundary**: inside the promise, what is open at the start gives
the first relation. ft: the number that the first chain's frame bears. -/
def TieStart (ft : ℕ) (N : Numbers) (Mg : Meaning P W) (links : List ModelPart) (ps : List Place)
    (get : S₁ → P × First.S) (R₀ : S₁ × (EAll D all).Str → W → Prop) : Prop :=
  ∀ a w, onQ (Fr := frameAt D all D.key₁ ft) N Mg links ps get 0 a →
    relQ (Fr := frameAt D all D.key₁ ft) N Mg links ps get 0 a w → R₀ a w

/-- **The file's conditions and relations: the first chain's from the table, with R₀ in front.** -/
def placesM (ft : ℕ) (N : Numbers) (Mg : Meaning P W) (links : List ModelPart) (ps : List Place)
    (get : S₁ → P × First.S) (R₀ : S₁ × (EAll D all).Str → W → Prop)
    (Q : Places D all S₁ S₂ S₃ W) : Places D all S₁ S₂ S₃ W :=
  { Q with
    on₁ := onQ (Fr := frameAt D all D.key₁ ft) N Mg links ps get
    R₁ := frontAt R₀ (relQ (Fr := frameAt D all D.key₁ ft) N Mg links ps get) }

end

/-- **THE ROW**: what every rule for a file asks of the first chain, at a first relation that means
something. -/
def FirstChainMeans : Prop :=
  ∀ (C : CK) (D : WholeD) (all : List LeftT) (Y P S₁ S₂ S₃ X₁ X₂ Cl W : Type)
    (T : Three C D all Y S₁ S₂ S₃ X₁ X₂ Cl W) (N : Numbers) (Mg : Meaning P W)
    (links : List ModelPart) (ps : List Place) (get : S₁ → P × First.S)
    (R₀ : S₁ × (EAll D all).Str → W → Prop) (Q : Places D all S₁ S₂ S₃ W),
    EachOwn (onQ (Fr := frameAt D all D.key₁ T.ft₁) N Mg links ps get) (meansQ N Mg get)
      (insQ links ps) (outsQ links ps) (· ∈ start links) 0 (T.p₁ :: T.l₁) →
    TieStart T.ft₁ N Mg links ps get R₀ →
    EachGoodIn (placesM T.ft₁ N Mg links ps get R₀ Q).on₁
      (placesM T.ft₁ N Mg links ps get R₀ Q).R₁ 0 (T.p₁ :: T.l₁)

theorem firstChainMeans : FirstChainMeans := by
  intro C D all Y P S₁ S₂ S₃ X₁ X₂ Cl W T N Mg links ps get R₀ Q ho hs
  exact eachGoodInFront S₁ Cl W C (frameAt D all D.key₁ T.ft₁) _ _ R₀ T.p₁ T.l₁ hs
    (jointsJoin S₁ Cl P W C (frameAt D all D.key₁ T.ft₁) N Mg links ps get (T.p₁ :: T.l₁) ho)

/-- A row with `EachGoodIn` has `EachGood`. -/
theorem eachGoodOfGoodIn {S Cl W : Type} {C : CK} {F : Frame} (on : ℕ → S × F.E.Str → Prop)
    (R : ℕ → S × F.E.Str → W → Prop) (l : List (Piece C F S Cl W)) :
    ∀ k, EachGoodIn on R k l → EachGood on R k l := by
  induction l with
  | nil => exact fun _ _ => trivial
  | cons p l ih =>
    intro k h
    exact ⟨goodOfGoodIn S Cl W C F p _ _ _ _ h.1, ih (k + 1) h.2⟩

/-- The clause for one statement, in the library's form: the first chain's reduction is knowledge
sound FROM R₀, READ AT THE CHAIN's FIRST RECORD: the data's own field. -/
def FirstChainKnowsOf : Prop :=
  ∀ (C : CK) (D : WholeD) (all : List LeftT) (Y P S₁ S₂ S₃ X₁ X₂ Cl W TF TJ T3 : Type) (tF : TF)
    (tJ : TJ) (t3 : T3) (T : Three C D all Y S₁ S₂ S₃ X₁ X₂ Cl W) (N : Numbers) (Mg : Meaning P W)
    (links : List ModelPart) (ps : List Place) (get : S₁ → P × First.S)
    (R₀ : S₁ × (EAll D all).Str → W → Prop) (Q : Places D all S₁ S₂ S₃ W)
    (okF : Y → TF → Bool) (okJ : X₁ → TJ → Bool) (ok3 : X₂ → T3 → Bool)
    (h₁ : (rowIOR T.p₁ T.l₁).shape = uLT C D.ds₁) (h₂ : (rowIOR T.p₂ T.l₂).shape = uLT C D.ds₂)
    (h₃ : (rowIOR T.p₃ T.l₃).shape = uLT C D.ds₃),
    T.Fits →
    EachOwn (onQ (Fr := frameAt D all D.key₁ T.ft₁) N Mg links ps get) (meansQ N Mg get)
      (insQ links ps) (outsQ links ps) (· ∈ start links) 0 (T.p₁ :: T.l₁) →
    TieStart T.ft₁ N Mg links ps get R₀ →
    T.Glue₁ (placesM T.ft₁ N Mg links ps get R₀ Q) →
    ((T.row tF tJ t3 okF okJ ok3).links
        (T.snd tF tJ t3 (placesM T.ft₁ N Mg links ps get R₀ Q) okF okJ ok3 h₁ h₂ h₃)).K₁.Know
      (fun a => onQ (Fr := frameAt D all D.key₁ T.ft₁) N Mg links ps get 0
        (T.in₁ a.1, (a.2, fun _ => [])))
      (fun a w => R₀ (T.in₁ a.1, (a.2, fun _ => [])) w)
      (T.mid₁ (placesM T.ft₁ N Mg links ps get R₀ Q))
      (fun a τ w => extOwn T.p₁ T.l₁ D.ds₁ h₁ T.d (T.in₁ a.1, (a.2, fun _ => [])) τ.2.2 w)
      (0, errOwn T.p₁ T.l₁ D.ds₁ h₁)

theorem firstChainKnowsOf : FirstChainKnowsOf := by
  intro C D all Y P S₁ S₂ S₃ X₁ X₂ Cl W TF TJ T3 tF tJ t3 T N Mg links ps get R₀ Q okF okJ ok3 h₁
    h₂ h₃ hf ho hs he
  exact file_know₁ tF tJ t3 T (placesM T.ft₁ N Mg links ps get R₀ Q) okF okJ ok3 h₁ h₂ h₃ hf
    (eachGoodOfGoodIn _ _ _ 0
      (firstChainMeans C D all Y P S₁ S₂ S₃ X₁ X₂ Cl W T N Mg links ps get R₀ Q ho hs)) he

/-- THE DATA HAVE R₀ AS THEIR FIELD, by make. -/
example {C : CK} {D : WholeD} {all : List LeftT} {Y P S₁ S₂ S₃ X₁ X₂ Cl W TF TJ T3 : Type}
    (tF : TF) (tJ : TJ) (t3 : T3) (T : Three C D all Y S₁ S₂ S₃ X₁ X₂ Cl W) (N : Numbers)
    (Mg : Meaning P W) (links : List ModelPart) (ps : List Place) (get : S₁ → P × First.S)
    (R₀ : S₁ × (EAll D all).Str → W → Prop) (Q : Places D all S₁ S₂ S₃ W) (okF : Y → TF → Bool)
    (okJ : X₁ → TJ → Bool) (ok3 : X₂ → T3 → Bool)
    (h₁ : (rowIOR T.p₁ T.l₁).shape = uLT C D.ds₁) (h₂ : (rowIOR T.p₂ T.l₂).shape = uLT C D.ds₂)
    (h₃ : (rowIOR T.p₃ T.l₃).shape = uLT C D.ds₃) (a : Y × (oneExternalString (2 ^ D.a) SgX).Str) (w : W) :
    (T.snd tF tJ t3 (placesM T.ft₁ N Mg links ps get R₀ Q) okF okJ ok3 h₁ h₂ h₃).R₀ a w =
      R₀ (T.in₁ a.1, (a.2, fun _ => [])) w := rfl

end VerifiableInference.Desc.Sound
