-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/TablesGlues.lean: FOR THE PLAIN FORM's RULE FOR A FILE (Johnson/Desc/Plain/FileChains.lean: Glues: "three implications without any game, one at each chain's end"): ITS SECOND AND THIRD FIELD AT
THE TABLES OF JOINTS. Definitions, one small lemma, two statements written as def … : Prop, their proofs, and THE RECORD ITSELF AS A TERM (tablesGlues). "To the sign" is held by Lean: a value of
the type Glues is made of the first field and these two.

  L₁At a: there is a witness of which all that the shared chain's table has open at its first border holds, at the record that start₂ makes of a.
  L₂At a: the last chain has a first record of a, and there is a witness of which all that its table has open at its first border holds.
  stepQ₃ i a b: the last chain's relation for block number i: the promise behind, and "there is a witness behind" gives "there is one in front": THE SHADOWS (no token is at stake on this chain).
  GlueTwoAt (Glues.g₂ to the sign, at T.ofStarts): GENERAL IN THE SHARED CHAIN's RELATIONS Q₂: asked of them: each gives the table's promise behind and carries "there is a witness" back (the row
    shared_joint_count's stepAt | stepE (Johnson/Desc/Sound/StepE.lean) do: their second clause is "∀ w, … → … (ext …)"). From: the shared chain's length · (START) · (SH₃) · (PO→) · (PO←).
  GlueThreeAt (Glues.g₃ to the sign): from the last chain's length ALONE: behind its last block no item is open, so every witness will do there (T.wEnd).

  eachLeads_of_eachPlain, leadsThreeAt: THE FILE's DEBT AT THE LAST CHAIN IN THE PLAIN FORM (EachLeads on₃ Q₃ 0 (p₃ :: l₃)) AT on₃ := onQ₃, Q₃ := stepQ₃, FROM WHAT THE TABLE ASKS OF EACH BLOCK (EachOwn: its own law between the items that
    its row closes and opens; the items that ride are kept): by lastJoinPlain; the plain law of a block in EachPlain (Johnson/Desc/Sound/SpinePlain.lean) IS Leads (Johnson/Desc/Plain/Leads.lean) at "the promise behind, and true behind gives true in front", by unfolding.
  tablesGlues: A VALUE OF THE RECORD Glues at T.ofStarts, the places { Pl₀ with on₂ := onQ₂ …, Q₂, on₃ := onQ₃ …, Q₃ := stepQ₃ … }, L₁At, L₂At: from the first field (a premise, in the record's own words) and the two above.

Limits. Rules under letters, as Johnson/Desc/Sound/TablesGlued.lean. What is asked of Q₂ is asked at every number k, beyond the chain's length too. The first field (g₁) is other files' to show, from OnZeroOfEnd | RelEndOfZero (Johnson/Desc/Sound/TieEnd.lean).
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.TablesGlued
import Johnson.Desc.Plain.FileChains

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (oneExternalString)
open _root_.Iop.Reduction (steps)
open VerifiableInference.Desc.Shared
open VerifiableInference.Desc.Last
open VerifiableInference.Desc.Plain (steps_keeps PPlaces Glues EachLeads)

/-- Relations in a row may be weakened one by one. -/
theorem steps_imp {A : Type} (Q Q' : ℕ → A → A → Prop) (h : ∀ i a b, Q i a b → Q' i a b) :
    ∀ (n i : ℕ) (a c : A), steps Q i n a c → steps Q' i n a c
  | 0, i, a, c, hq => h i a c hq
  | n + 1, i, _, c, ⟨b, hb, hc⟩ => ⟨b, h i _ b hb, steps_imp Q Q' h n (i + 1) b c hc⟩

section
variable {C : CK} {D : WholeD} {all : List LeftT} {Y P S₁' S₂' S₃' X₁ X₂ Cl Wt : Type}
  (start₂ : P → S₂') (start₃ : P → S₁' → S₂' → Option S₃')
  (T : Three C D all Y (P × S₁') ((P × S₁') × S₂') ((P × S₁' × S₂') × S₃') X₁ X₂ Cl Wt) (N : NumbersS)
  (Mg : MeaningS S₂' (P × S₁') Wt) (ML : MeaningL S₃' Wt) (Pm : PromMeaning S₂')
  (PL : PromMeaningL S₂' S₃' (P × S₁')) (Oc : P × S₁' → Strs → Prop) (split : Bool)

/-- There is a witness of what the shared chain claims at its first border. -/
def L₁At (a : (P × S₁') × (EAll D all).Str) : Prop :=
  ∃ w, relQ₂ N Mg split T.p₂ T.l₂ 0 ((a.1, start₂ a.1.1), a.2) w

/-- The last chain has a first record, and there is a witness of what it claims at its first border. -/
def L₂At (a : (P × S₁' × S₂') × (EAll D all).Str) : Prop :=
  ∃ (s : (P × S₁' × S₂') × S₃') (w : Wt),
    (start₃ a.1.1 a.1.2.1 a.1.2.2).map (fun s => (a.1, s)) = some s ∧
      relQ₃ (Fr := frameAt D all D.key₃ T.ft₃) N Mg ML 0 (s, a.2) w

/-- The last chain's relation for block number i: the shadows. -/
def stepQ₃ (i : ℕ) (a b : ((P × S₁' × S₂') × S₃') × (EAll D all).Str) : Prop :=
  onQ₃ (Fr := frameAt D all D.key₃ T.ft₃) N Mg Pm PL Oc (i + 1) b ∧
    ((∃ w, relQ₃ (Fr := frameAt D all D.key₃ T.ft₃) N Mg ML (i + 1) b w) →
      ∃ w, relQ₃ (Fr := frameAt D all D.key₃ T.ft₃) N Mg ML i a w)

end

/-- **Glues.g₂ at the tables.** -/
def GlueTwoAt : Prop :=
  ∀ (C : CK) (D : WholeD) (all : List LeftT) (Y P S₁' S₂' S₃' X₁ X₂ Cl Wt : Type) (pub : Y → P)
    (start₁ : P → S₁') (start₂ : P → S₂') (start₃ : P → S₁' → S₂' → Option S₃')
    (T : Three C D all Y (P × S₁') ((P × S₁') × S₂') ((P × S₁' × S₂') × S₃') X₁ X₂ Cl Wt) (N : NumbersS)
    (Mg : MeaningS S₂' (P × S₁') Wt) (ML : MeaningL S₃' Wt) (Pm : PromMeaning S₂')
    (PL : PromMeaningL S₂' S₃' (P × S₁')) (Oc : P × S₁' → Strs → Prop) (split : Bool)
    (Q₂ : ℕ → ((P × S₁') × S₂') × (EAll D all).Str → ((P × S₁') × S₂') × (EAll D all).Str → Prop),
    (∀ k a b, Q₂ k a b → onQ₂ N Pm Oc split T.p₂ T.l₂ (k + 1) b ∧
      ((∃ w, relQ₂ N Mg split T.p₂ T.l₂ (k + 1) b w) → ∃ w, relQ₂ N Mg split T.p₂ T.l₂ k a w)) →
    1 + T.l₂.length = (sharedPlaces split).length →
    (∀ p s₁ s₂ s, start₃ p s₁ s₂ = some s → Mg.unmarked1 (p, s₁)) →
    (∀ (b : ((P × S₁') × S₂') × (EAll D all).Str) (s : S₃'),
      onQ₂ N Pm Oc split T.p₂ T.l₂ (1 + T.l₂.length) b → start₃ b.1.1.1 b.1.1.2 b.1.2 = some s →
      PL.shape 0 (b.1.1.1, b.1.1.2) b.1.2 s = true) →
    (∀ b : ((P × S₁') × S₂') × (EAll D all).Str,
      (PromS.noColl .oOmega).holds N Pm ((actQ N T.p₂ T.l₂ (1 + T.l₂.length)).2 b).1
        (strsOfAct (frameAt D all D.key₂ T.ft₂) ((actQ N T.p₂ T.l₂ (1 + T.l₂.length)).2 b)) →
      (PromS.noColl .oOmega).holds N Pm b.1.2 (strsOf (frameAt D all D.key₃ T.ft₃) b.2)) →
    (∀ (b : ((P × S₁') × S₂') × (EAll D all).Str) (w : Wt),
      (ItemS.pin .oOmega).holdsSh N Mg b.1.2 (strsOf (frameAt D all D.key₃ T.ft₃) b.2) w →
      muQ N Mg T.p₂ T.l₂ (.pin .oOmega) (1 + T.l₂.length)
        ((actQ N T.p₂ T.l₂ (1 + T.l₂.length)).2 b) w) →
    ∀ (a : (P × S₁') × (EAll D all).Str) (b : ((P × S₁') × S₂') × (EAll D all).Str),
      onQ₂ N Pm Oc split T.p₂ T.l₂ 0 ((T.ofStarts pub start₁ start₂ start₃).in₂ a.1, a.2) →
      steps Q₂ 0 T.l₂.length ((T.ofStarts pub start₁ start₂ start₃).in₂ a.1, a.2) b →
      (∀ s, (T.ofStarts pub start₁ start₂ start₃).in₃
          ((T.ofStarts pub start₁ start₂ start₃).out₂ a.1 b.1) = some s →
        onQ₃ (Fr := frameAt D all D.key₃ T.ft₃) N Mg Pm PL Oc 0 (s, b.2)) ∧
      (L₂At start₃ T N Mg ML ((T.ofStarts pub start₁ start₂ start₃).out₂ a.1 b.1, b.2) →
        L₁At start₂ T N Mg split a)

/-- **Glues.g₃ at the tables.** -/
def GlueThreeAt : Prop :=
  ∀ (C : CK) (D : WholeD) (all : List LeftT) (Y P S₁' S₂' S₃' X₁ X₂ Cl Wt : Type) (pub : Y → P)
    (start₁ : P → S₁') (start₂ : P → S₂') (start₃ : P → S₁' → S₂' → Option S₃')
    (T : Three C D all Y (P × S₁') ((P × S₁') × S₂') ((P × S₁' × S₂') × S₃') X₁ X₂ Cl Wt) (N : NumbersS)
    (Mg : MeaningS S₂' (P × S₁') Wt) (ML : MeaningL S₃' Wt) (Pm : PromMeaning S₂')
    (PL : PromMeaningL S₂' S₃' (P × S₁')) (Oc : P × S₁' → Strs → Prop),
    1 + T.l₃.length = lastPlaces.length →
    ∀ (a : (P × S₁' × S₂') × (EAll D all).Str) (s : (P × S₁' × S₂') × S₃')
      (b : ((P × S₁' × S₂') × S₃') × (EAll D all).Str),
      (T.ofStarts pub start₁ start₂ start₃).in₃ a.1 = some s →
      onQ₃ (Fr := frameAt D all D.key₃ T.ft₃) N Mg Pm PL Oc 0 (s, a.2) →
      steps (stepQ₃ T N Mg ML Pm PL Oc) 0 T.l₃.length (s, a.2) b →
      (T.ofStarts pub start₁ start₂ start₃).fin a.1 b.1 = true → L₂At start₃ T N Mg ML a

theorem glueTwoAt : GlueTwoAt := by
  intro C D all Y P S₁' S₂' S₃' X₁ X₂ Cl Wt pub start₁ start₂ start₃ T N Mg ML Pm PL Oc split Q₂ hQ hlen
    hStart hSh hPOf hPOb a b _ hst
  have hk := steps_keeps (onQ₂ N Pm Oc split T.p₂ T.l₂)
    (fun k x => ∃ w, relQ₂ N Mg split T.p₂ T.l₂ k x w) T.l₂.length 0 _ b
    (steps_imp Q₂ _ hQ T.l₂.length 0 _ b hst)
  rw [Nat.zero_add] at hk
  refine ⟨fun s hs => ?_, fun hL => ?_⟩
  · obtain ⟨s', hs', rfl⟩ := Option.map_eq_some_iff.1 hs
    exact onZero₃OfEnd₂ C D all Y P S₁' S₂' S₃' X₁ X₂ Cl Wt start₃ T N Mg ML Pm PL Oc split hlen hStart
      hSh hPOf b s' hk.1 hs'
  · obtain ⟨s, w, hs, hw⟩ := hL
    obtain ⟨s', hs', rfl⟩ := Option.map_eq_some_iff.1 hs
    exact hk.2 ⟨w, relEnd₂OfZero₃ C D all Y P S₁' S₂' S₃' X₁ X₂ Cl Wt start₃ T N Mg ML Pm PL Oc split hlen
      hStart hPOb b s' w hs' hw⟩

theorem glueThreeAt : GlueThreeAt := by
  intro C D all Y P S₁' S₂' S₃' X₁ X₂ Cl Wt pub start₁ start₂ start₃ T N Mg ML Pm PL Oc hlen a s b hs _
    hst _
  have hk := steps_keeps (onQ₃ (Fr := frameAt D all D.key₃ T.ft₃) N Mg Pm PL Oc)
    (fun k x => ∃ w, relQ₃ (Fr := frameAt D all D.key₃ T.ft₃) N Mg ML k x w) T.l₃.length 0 _ b hst
  rw [Nat.zero_add] at hk
  obtain ⟨w, hw⟩ := hk.2 ⟨T.wEnd, fun i hi => by
    have hi' : openAfter insQ₃ outsQ₃ (· ∈ startLast) (1 + T.l₃.length) i := hi
    rw [hlen] at hi'
    exact absurd hi' (endLast i)⟩
  exact ⟨s, w, hs, hw⟩

/-- The plain law along a row (`EachPlain`) is `EachLeads`, at the relations "the promise behind, and true behind gives true in front". -/
theorem eachLeads_of_eachPlain {S Cl W : Type} {C : CK} {F : Frame} (on T : ℕ → S × F.E.Str → Prop) :
    ∀ (l : List (Piece C F S Cl W)) (i : ℕ), EachPlain on T i l →
      EachLeads on (fun i a b => on (i + 1) b ∧ (T (i + 1) b → T i a)) i l
  | [], _, _ => trivial
  | _ :: l, i, h => ⟨h.1, fun _ _ _ hq => hq.1, eachLeads_of_eachPlain on T l (i + 1) h.2⟩

/-- **The file's debt at the last chain, in the plain form, from what the table asks of each block.** -/
theorem leadsThreeAt {C : CK} {D : WholeD} {all : List LeftT} {Y P S₁' S₂' S₃' X₁ X₂ Cl Wt : Type}
    (T : Three C D all Y (P × S₁') ((P × S₁') × S₂') ((P × S₁' × S₂') × S₃') X₁ X₂ Cl Wt) (N : NumbersS)
    (Mg : MeaningS S₂' (P × S₁') Wt) (ML : MeaningL S₃' Wt) (Pm : PromMeaning S₂')
    (PL : PromMeaningL S₂' S₃' (P × S₁')) (Oc : P × S₁' → Strs → Prop)
    (h : EachOwn (onQ₃ (Fr := frameAt D all D.key₃ T.ft₃) N Mg Pm PL Oc) (meansQ₃ N Mg ML) insQ₃ outsQ₃
      (· ∈ startLast) 0 (T.p₃ :: T.l₃)) :
    EachLeads (onQ₃ (Fr := frameAt D all D.key₃ T.ft₃) N Mg Pm PL Oc) (stepQ₃ T N Mg ML Pm PL Oc) 0
      (T.p₃ :: T.l₃) :=
  eachLeads_of_eachPlain _ _ _ 0
    (lastJoinPlain P S₁' S₂' S₃' Cl Wt C _ N Mg ML Pm PL Oc (T.p₃ :: T.l₃) h)

/-- **The record itself**, of its first field and the two at the tables. -/
theorem tablesGlues {C : CK} {D : WholeD} {all : List LeftT} {Y P S₁' S₂' S₃' X₁ X₂ Cl Wt : Type}
    (pub : Y → P) (start₁ : P → S₁') (start₂ : P → S₂') (start₃ : P → S₁' → S₂' → Option S₃')
    (T : Three C D all Y (P × S₁') ((P × S₁') × S₂') ((P × S₁' × S₂') × S₃') X₁ X₂ Cl Wt) (N : NumbersS)
    (Mg : MeaningS S₂' (P × S₁') Wt) (ML : MeaningL S₃' Wt) (Pm : PromMeaning S₂')
    (PL : PromMeaningL S₂' S₃' (P × S₁')) (Oc : P × S₁' → Strs → Prop) (split : Bool)
    (Pl₀ : PPlaces D all (P × S₁') ((P × S₁') × S₂') ((P × S₁' × S₂') × S₃'))
    (Q₂ : ℕ → ((P × S₁') × S₂') × (EAll D all).Str → ((P × S₁') × S₂') × (EAll D all).Str → Prop)
    (M : Y × (oneExternalString (2 ^ D.a) SgX).Str → (P × S₁') × (EAll D all).Str → Prop)
    (hg₁ : ∀ (x : Y) (y : (oneExternalString (2 ^ D.a) SgX).Str) (b : (P × S₁') × (EAll D all).Str),
      Pl₀.on₁ 0 ((T.ofStarts pub start₁ start₂ start₃).in₁ x, (y, fun _ => [])) →
      steps Pl₀.Q₁ 0 T.l₁.length ((T.ofStarts pub start₁ start₂ start₃).in₁ x, (y, fun _ => [])) b →
      onQ₂ N Pm Oc split T.p₂ T.l₂ 0 ((T.ofStarts pub start₁ start₂ start₃).in₂
          ((T.ofStarts pub start₁ start₂ start₃).out₁ x b.1), b.2) ∧
        (L₁At start₂ T N Mg split ((T.ofStarts pub start₁ start₂ start₃).out₁ x b.1, b.2) →
          M (x, y) ((T.ofStarts pub start₁ start₂ start₃).out₁ x b.1, b.2)))
    (hQ : ∀ k a b, Q₂ k a b → onQ₂ N Pm Oc split T.p₂ T.l₂ (k + 1) b ∧
      ((∃ w, relQ₂ N Mg split T.p₂ T.l₂ (k + 1) b w) → ∃ w, relQ₂ N Mg split T.p₂ T.l₂ k a w))
    (h₂ : 1 + T.l₂.length = (sharedPlaces split).length) (h₃ : 1 + T.l₃.length = lastPlaces.length)
    (hStart : ∀ p s₁ s₂ s, start₃ p s₁ s₂ = some s → Mg.unmarked1 (p, s₁))
    (hSh : ∀ (b : ((P × S₁') × S₂') × (EAll D all).Str) (s : S₃'),
      onQ₂ N Pm Oc split T.p₂ T.l₂ (1 + T.l₂.length) b → start₃ b.1.1.1 b.1.1.2 b.1.2 = some s →
      PL.shape 0 (b.1.1.1, b.1.1.2) b.1.2 s = true)
    (hPOf : ∀ b : ((P × S₁') × S₂') × (EAll D all).Str,
      (PromS.noColl .oOmega).holds N Pm ((actQ N T.p₂ T.l₂ (1 + T.l₂.length)).2 b).1
        (strsOfAct (frameAt D all D.key₂ T.ft₂) ((actQ N T.p₂ T.l₂ (1 + T.l₂.length)).2 b)) →
      (PromS.noColl .oOmega).holds N Pm b.1.2 (strsOf (frameAt D all D.key₃ T.ft₃) b.2))
    (hPOb : ∀ (b : ((P × S₁') × S₂') × (EAll D all).Str) (w : Wt),
      (ItemS.pin .oOmega).holdsSh N Mg b.1.2 (strsOf (frameAt D all D.key₃ T.ft₃) b.2) w →
      muQ N Mg T.p₂ T.l₂ (.pin .oOmega) (1 + T.l₂.length)
        ((actQ N T.p₂ T.l₂ (1 + T.l₂.length)).2 b) w) :
    Glues (T.ofStarts pub start₁ start₂ start₃)
      { Pl₀ with
        on₂ := onQ₂ N Pm Oc split T.p₂ T.l₂, Q₂ := Q₂
        on₃ := onQ₃ (Fr := frameAt D all D.key₃ T.ft₃) N Mg Pm PL Oc
        Q₃ := stepQ₃ T N Mg ML Pm PL Oc }
      M (L₁At start₂ T N Mg split) (L₂At start₃ T N Mg ML) :=
  ⟨hg₁,
    glueTwoAt C D all Y P S₁' S₂' S₃' X₁ X₂ Cl Wt pub start₁ start₂ start₃ T N Mg ML Pm PL Oc split Q₂ hQ h₂
      hStart hSh hPOf hPOb,
    glueThreeAt C D all Y P S₁' S₂' S₃' X₁ X₂ Cl Wt pub start₁ start₂ start₃ T N Mg ML Pm PL Oc h₃⟩

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.leadsThreeAt
#print axioms VerifiableInference.Desc.Sound.tablesGlues
#print axioms VerifiableInference.Desc.Sound.glueTwoAt
#print axioms VerifiableInference.Desc.Sound.glueThreeAt
