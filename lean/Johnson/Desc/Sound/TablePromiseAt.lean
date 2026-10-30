-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/TablePromiseAt.lean: TWO PREMISES OF THE JOINT OF THE FIRST AND THE SHARED CHAIN (Johnson/Desc/Sound/TieEnd.lean): (TP) "the table decodes with the record" gives the shared chain's promise on the table · (PW) the cells' pin at
the shared chain's first record gives it at the public part's: BOTH BROUGHT DOWN TO ONE EQUATION OF RECORDS, AT ONE DECODER. Definitions, two small lemmas, two statements written as def … : Prop, and their proofs.
Here the decoder is ONE letter D, read at two readers of a record.

THE DESIGN THAT IT FOLLOWS: the decoder of the first table's "decodes" and of both tables' cells' pins IS ONE: THE GUARDED DECODER: nothing at a collision; else what the
constrained minimum decodes to, if that holds an index (the library's ConfigurationWithOutOfDomainSample.D, Hiop/RecConf.lean). At an unguarded decoder "decodes" does not give "no collision".
  decAtRec D recOf: the tables' letter decT made of ONE decoder D (stored table, record ↦ cells) and a reader of THE RECORD in what the letter is handed.
  (KEY): THE ONE EQUATION: the record that the shared chain's first record holds is the record that the first table reads in what the first chain hands on: recOf₂ (start₂ a.1) = recOf (get a).
  TPAtKey, PWAtKey: (TP) and (PW) TO THE LETTER, where decodes, tablePromise and the two pins are filled by decAtRec D at the two readers: from (KEY), by rewriting.
  decGuard coll dcd held: the shape of a guarded decoder. decGuard_some: where it gives something there is no collision, and the decoder beneath gives something.
  noColl_of_promise: so the shared chain's promise on the table, at D := a guarded decoder, gives "no collision at the record's seed": what the point's law asks of it.

WHAT IS OWED. (KEY): by the make of start₂ and get: NOT SHOWN AT ANY DESCRIPTION. It runs over every a: it is payable where recOf reads the public part alone and start₂ lays that part's record into its first record. That D is the library's guarded
decoder at the typed data of the point's law (its err, eM, rank): the tie's to ask, by name. ONE RADIUS: if the point's law's radius and the top's one-time radius differ, two small steps are owed (on paper).
Limits. Rules under letters.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.TieEnd
import Johnson.Desc.Sound.OmegaCrosses
import Johnson.Desc.Sound.MeaningSig

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj Johnson.Pack
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc.Shared
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers)

/-- The stored table, as the tables of joints read it. -/
abbrev CellsOf : Type := ℕ → Option (ℕ × List UInt64)

/-- The tables' letter for a decoder, made of one decoder and a reader of the record. -/
def decAtRec {A Rec Cells : Type} (D : CellsOf → Rec → Option Cells) (recOf : A → Rec) :
    CellsOf → A → Option Cells := fun c a => D c (recOf a)

section
variable {A M Cells : Type} (coll : CellsOf → A → Prop) (dcd : CellsOf → A → Option M)
  (held : M → Option Cells)

open Classical in
/-- **A guarded decoder**: nothing at a collision. -/
def decGuard (c : CellsOf) (a : A) : Option Cells := if coll c a then none else (dcd c a).bind held

/-- Where a guarded decoder gives something there is no collision, and the decoder beneath it gives something. -/
theorem decGuard_some (c : CellsOf) (a : A) (h : (decGuard coll dcd held c a).isSome = true) :
    ¬ coll c a ∧ (dcd c a).isSome = true := by
  unfold decGuard at h
  by_cases hc : coll c a
  · rw [if_pos hc] at h
    cases h
  · rw [if_neg hc] at h
    refine ⟨hc, ?_⟩
    cases hd : dcd c a with
    | none =>
      rw [hd] at h
      cases h
    | some _ => rfl

end

/-- The promise on the table, at a guarded decoder, gives "no collision at the record's seed". -/
theorem noColl_of_promise {S₂ Rec M Cells : Type} (coll : CellsOf → Rec → Prop)
    (dcd : CellsOf → Rec → Option M) (held : M → Option Cells) (recOf₂ : S₂ → Rec) (s : S₂) (y : Strs)
    (h : decodesOf (decAtRec (decGuard coll dcd held) recOf₂) s y) :
    ¬ coll y.cell (recOf₂ s) ∧ (dcd y.cell (recOf₂ s)).isSome = true :=
  decGuard_some coll dcd held _ _ h

/-- **(TP), at one decoder, from the equation of records.** -/
def TPAtKey : Prop :=
  ∀ (C : CK) (D : WholeD) (all : List LeftT) (Y P P₀ S₁' S₂' S₃' X₁ X₂ Cl W Rec Cells : Type)
    (start₂ : P → S₂')
    (T : Three C D all Y (P × S₁') ((P × S₁') × S₂') ((P × S₁' × S₂') × S₃') X₁ X₂ Cl W)
    (get : P × S₁' → P₀ × First.S) (N₁ : Numbers) (Mg₁ : Meaning P₀ W) (Ns : NumbersS)
    (Pm : PromMeaning S₂') (Dc : CellsOf → Rec → Option Cells) (recOf : P₀ × First.S → Rec)
    (recOf₂ : S₂' → Rec),
    Mg₁.decodes = decodesOf (decAtRec Dc recOf) →
    Pm.tablePromise = decodesOf (decAtRec Dc recOf₂) →
    (∀ a : P × S₁', recOf₂ (start₂ a.1) = recOf (get a)) →
    ∀ b : (P × S₁') × (EAll D all).Str,
      Mg₁.decodes (get b.1) (strsOf (frameAt D all D.key₁ T.ft₁) b.2) →
      Pm.tablePromise (start₂ b.1.1) (strsOfAct (frameAt D all D.key₂ T.ft₂)
        ((actQ (tiedNumbers N₁ Ns) T.p₂ T.l₂ 0).2 ((b.1, start₂ b.1.1), b.2)))

/-- **(PW), at one decoder, from the equation of records.** -/
def PWAtKey : Prop :=
  ∀ (C : CK) (D : WholeD) (all : List LeftT) (Y P P₀ S₁' S₂' S₃' X₁ X₂ Cl Rec Cells Tok : Type)
    (start₂ : P → S₂')
    (T : Three C D all Y (P × S₁') ((P × S₁') × S₂') ((P × S₁' × S₂') × S₃') X₁ X₂ Cl
      (Wit Cells Tok MsgT))
    (get : P × S₁' → P₀ × First.S) (N₁ : Numbers) (Mg₁ : Meaning P₀ (Wit Cells Tok MsgT))
    (Ns : NumbersS) (Mg : MeaningS S₂' (P × S₁') (Wit Cells Tok MsgT))
    (Dc : CellsOf → Rec → Option Cells) (recOf : P₀ × First.S → Rec) (recOf₂ : S₂' → Rec),
    Mg₁.pinW = pinWOf (decAtRec Dc recOf) →
    Mg.pinT = pinWOf (decAtRec Dc recOf₂) →
    (∀ a : P × S₁', recOf₂ (start₂ a.1) = recOf (get a)) →
    ∀ (b : (P × S₁') × (EAll D all).Str) (w : Wit Cells Tok MsgT),
      Mg.pinT (start₂ b.1.1) (strsOfAct (frameAt D all D.key₂ T.ft₂)
        ((actQ (tiedNumbers N₁ Ns) T.p₂ T.l₂ 0).2 ((b.1, start₂ b.1.1), b.2))) w →
      Mg₁.pinW (get b.1) (strsOf (frameAt D all D.key₁ T.ft₁) b.2) w

theorem tpAtKey : TPAtKey := by
  intro C D all Y P P₀ S₁' S₂' S₃' X₁ X₂ Cl W Rec Cells start₂ T get N₁ Mg₁ Ns Pm Dc recOf recOf₂ hM hP
    hKey b h
  rw [hM] at h
  rw [hP]
  show (Dc _ (recOf₂ (start₂ b.1.1))).isSome = true
  rw [hKey b.1]
  exact h

theorem pwAtKey : PWAtKey := by
  intro C D all Y P P₀ S₁' S₂' S₃' X₁ X₂ Cl Rec Cells Tok start₂ T get N₁ Mg₁ Ns Mg Dc recOf recOf₂ hM hP
    hKey b w h
  rw [hP] at h
  rw [hM]
  have h' : Dc _ (recOf₂ (start₂ b.1.1)) = some w.cells := h
  rw [hKey b.1] at h'
  exact h'

-- A CONTROL: at an unguarded decoder the lemma's first half fails: something is decoded at a collision
example : ¬ ∀ (coll : CellsOf → Unit → Prop) (dcd : CellsOf → Unit → Option Unit) (c : CellsOf),
    (dcd c ()).isSome = true → ¬ coll c () :=
  fun h => h (fun _ _ => True) (fun _ _ => some ()) (fun _ => none) rfl trivial

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.decGuard_some
#print axioms VerifiableInference.Desc.Sound.noColl_of_promise
#print axioms VerifiableInference.Desc.Sound.tpAtKey
#print axioms VerifiableInference.Desc.Sound.pwAtKey
