-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/KeyLang.lean: THE KEY FILE'S FIRST CONDITION AND FIRST RELATION, and that their
language is the language of the key file's named hypothesis on soundness.

The setting. `KeySoundOfBlocks` (Johnson/Desc/Sound/KeyRule.lean) ends in `CompilerSoundnessConditionStatements.keySound`: the
key file's protocol is round-by-round sound for "the stored table has a collision at the record's
seed, or decodes with the record". One of its premises, the binder `lang`, ties the relation at the
first boundary of the first chain to that language. The rule leaves that relation a parameter. Here
it is written, and the premise is proved.

What is written. A statement at the first boundary is the record that the verifier carries, with the
stored table and the file's trees. rd reads the key file's instance (a seed and the answers) out of
the carried record. `keyOn`: the stored table has no collision at the seed. `keyRel`: the stored
table decodes with the instance to an index; no witness is read. They are the condition and the
relation in front of the library's typed lists for a key file (`KObj.jWf`, Johnson/E/KObj/Obj.lean),
read along `keyStm`: so a typed block that is proved from that joint can be carried to the first
block of the first chain (`PieceGood`, Johnson/Desc/Sound/ChainRule.lean, at rd := `keyStm`).

Main names.
  `KeyL`: the language. `keyL_iff`: it is "no collision implies decodes".
  `LangAt`: the premise `lang` of `KeySoundOfBlocks`, to the letter. `LangIs`: the same as an
    equivalence: THE STATEMENT THAT IS MEANT.
  `keyStm`, `keyOn`, `keyRel`; `Places.keyFirst`: these two laid at the first boundary.
  `keyLangIs`: where rd reads back the instance from the first record, `LangIs` holds.
  `keyLangAt_of`: `LangAt` for every condition that is no narrower and every relation that is no
    wider.
  `keyLangIs_ofStarts`: at the filling that is meant (`Three.ofStarts`), for an injective public
    part. (That the program's key of a table, written of a record, is injective:
    `OnBytes.Slice.keyOf_injective`, OnBytes/Slice/KeyOfRecInj.lean.)
  (`KeySoundOfBlocks` with this premise and others gone: Johnson/Desc/Sound/KeyPaid.lean.)
Trials on silly members (section 4). `LangAt` speaks of no verifier; its silly members are
  relations. The relation that holds of everything, and the condition that holds of nothing, meet
  `LangAt` only if every table is in the language (`lang_trial_all`, `lang_trial_off`). THE RELATION
  WITHOUT A WITNESS MEETS `LangAt` (`lang_trial_none_meets_half`): so `LangAt` alone does not fix
  the first relation. It meets `LangIs` only if no table is in the language (`lang_trial_none`). A
  first record that forgets the instance meets `LangIs` only if the language does not read the
  instance (`lang_trial_forgets`).
  `member_of_laws`: under three laws of a configuration an honest table is in the language without a
  collision. `Toy`: a configuration with a table in the language and a table outside it.

Limits. Nothing on any block: that the first block is good from `keyRel` is owed where that block is
proved. Nothing on any verifier. The configuration is a letter: what "collision" and "decodes" say
is not looked at; that some table lies outside the language of the release's configuration is not
shown. The core of the proof is that of a theorem that is not in this library (`KObj.KThree.tie`,
Johnson/E/KObj/KeyThree.lean), which asks for a record of three typed lists and reads its
configuration alone.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.KeyRule
import OnBytes.Slice.KeyOfRecInj

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.OnPublicFiles OnBytes.RunA
open _root_.Run (ckP)
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString)
open _root_.Iop.Reduction (orOff)

/-! ## 1 The language -/

/-- **The key file's language**, as `CompilerSoundnessConditionStatements.keySound` has it: the stored table has a collision at
the record's seed, or decodes with the record. -/
def KeyL {a : ℕ} (Kc : ConfLetters a) (rec : Kc.conf.Rec) (y : Kc.conf.E0.Str) : Prop :=
  Kc.conf.coll y rec.1 ∨ Kc.conf.D y rec ≠ none

/-- The language is "a statement without a collision decodes": the library's condition and relation
in front of a key file's typed lists. -/
theorem keyL_iff {a : ℕ} (Kc : ConfLetters a) (rec : Kc.conf.Rec) (y : Kc.conf.E0.Str) :
    KeyL Kc rec y ↔ (Kc.conf.free (rec, y) → Kc.conf.RwfR (rec, y) ()) := by
  constructor
  · rintro (h | h) hf
    · exact absurd h hf
    · exact Option.isSome_iff_ne_none.2 h
  · intro h
    by_cases hc : Kc.conf.coll y rec.1
    · exact Or.inl hc
    · exact Or.inr (Option.isSome_iff_ne_none.1 (h hc))

section
variable {a : ℕ} (Kc : ConfLetters a) {DK : WholeD} {all : List LeftT}
  {S₁ S₂ S₃ X₁ X₂ Cl W : Type}

/-! ## 2 The premise, and the statement that is meant -/

/-- **The premise `lang` of `KeySoundOfBlocks`**, to the letter: if the first relation has a witness
at (the first record of rec, the stored table, no tree sent), or that statement is outside the first
condition, the table is in the language. -/
def LangAt (T : Three (ckP .two) (DK.at a) all Kc.conf.Rec S₁ S₂ S₃ X₁ X₂ Cl W)
    (Q : Places (DK.at a) all S₁ S₂ S₃ W) : Prop :=
  ∀ rec y, (Q.on₁ 0 (T.in₁ rec, (y, fun _ => [])) →
      ∃ w, Q.R₁ 0 (T.in₁ rec, (y, fun _ => [])) w) →
    Kc.conf.coll y rec.1 ∨ Kc.conf.D y rec ≠ none

/-- **The statement that is meant**: the first relation's language IS the key file's language. -/
def LangIs (T : Three (ckP .two) (DK.at a) all Kc.conf.Rec S₁ S₂ S₃ X₁ X₂ Cl W)
    (Q : Places (DK.at a) all S₁ S₂ S₃ W) : Prop :=
  ∀ rec y, (Q.on₁ 0 (T.in₁ rec, (y, fun _ => [])) →
      ∃ w, Q.R₁ 0 (T.in₁ rec, (y, fun _ => [])) w) ↔
    (Kc.conf.coll y rec.1 ∨ Kc.conf.D y rec ≠ none)

variable {Kc}

theorem LangIs.langAt {T : Three (ckP .two) (DK.at a) all Kc.conf.Rec S₁ S₂ S₃ X₁ X₂ Cl W}
    {Q : Places (DK.at a) all S₁ S₂ S₃ W} (h : LangIs Kc T Q) : LangAt Kc T Q :=
  fun rec y => (h rec y).1

variable (Kc)

/-! ## 3 The first condition and the first relation -/

/-- A statement at a boundary of the first chain, read as a statement of the key file's language:
the instance that rd reads out of the carried record, and the stored table. The trees are not read.
-/
def keyStm (rd : S₁ → Kc.conf.Rec) (b : S₁ × (EAll (DK.at a) all).Str) :
    Kc.conf.Rec × Kc.conf.E0.Str := (rd b.1, b.2.1)

/-- **The first condition**: the stored table has no collision at the record's seed. -/
def keyOn (rd : S₁ → Kc.conf.Rec) : S₁ × (EAll (DK.at a) all).Str → Prop :=
  fun b => Kc.conf.free (keyStm Kc rd b)

/-- **The first relation**: the stored table decodes with the record to an index of the index set.
The index is decoded by the statement: no witness is read. -/
def keyRel (rd : S₁ → Kc.conf.Rec) : S₁ × (EAll (DK.at a) all).Str → W → Prop :=
  fun b _ => Kc.conf.RwfR (keyStm Kc rd b) ()

/-- The two laid at the first boundary of the first chain; all other boundaries as they were. -/
def Places.keyFirst (Q : Places (DK.at a) all S₁ S₂ S₃ W) (rd : S₁ → Kc.conf.Rec) :
    Places (DK.at a) all S₁ S₂ S₃ W :=
  { Q with
    on₁ := fun i => if i = 0 then keyOn Kc rd else Q.on₁ i
    R₁ := fun i => if i = 0 then keyRel Kc rd else Q.R₁ i }

theorem keyFirst_on₁_zero (Q : Places (DK.at a) all S₁ S₂ S₃ W) (rd : S₁ → Kc.conf.Rec) :
    (Q.keyFirst Kc rd).on₁ 0 = keyOn Kc rd := by
  unfold Places.keyFirst
  dsimp only
  exact if_pos rfl
theorem keyFirst_R₁_zero (Q : Places (DK.at a) all S₁ S₂ S₃ W) (rd : S₁ → Kc.conf.Rec) :
    (Q.keyFirst Kc rd).R₁ 0 = keyRel Kc rd := by
  unfold Places.keyFirst
  dsimp only
  exact if_pos rfl

/-- `LangIs` reads the condition and the relation at the first boundary alone. -/
theorem LangIs.congr {T : Three (ckP .two) (DK.at a) all Kc.conf.Rec S₁ S₂ S₃ X₁ X₂ Cl W}
    {Q Q' : Places (DK.at a) all S₁ S₂ S₃ W} (h : LangIs Kc T Q) (hon : Q'.on₁ 0 = Q.on₁ 0)
    (hR : Q'.R₁ 0 = Q.R₁ 0) : LangIs Kc T Q' := by
  intro rec y
  rw [hon, hR]
  exact h rec y

/-- **`lang` for every first condition that is no narrower than `keyOn` and every first relation
that is no wider than `keyRel`**, at the file's own first statements. -/
theorem keyLangAt_of (T : Three (ckP .two) (DK.at a) all Kc.conf.Rec S₁ S₂ S₃ X₁ X₂ Cl W)
    (Q : Places (DK.at a) all S₁ S₂ S₃ W) (rd : S₁ → Kc.conf.Rec)
    (hrd : ∀ rec, rd (T.in₁ rec) = rec)
    (hon : ∀ rec y, keyOn (DK := DK) (all := all) Kc rd (T.in₁ rec, (y, fun _ => [])) →
      Q.on₁ 0 (T.in₁ rec, (y, fun _ => [])))
    (hR : ∀ rec y w, Q.R₁ 0 (T.in₁ rec, (y, fun _ => [])) w →
      keyRel (DK := DK) (all := all) Kc rd (T.in₁ rec, (y, fun _ => [])) w) : LangAt Kc T Q := by
  intro rec y h
  refine (keyL_iff Kc rec y).2 fun hf => ?_
  have hf' : keyOn (DK := DK) (all := all) Kc rd (T.in₁ rec, (y, fun _ => [])) := by
    show Kc.conf.free (rd (T.in₁ rec), y)
    rw [hrd]
    exact hf
  obtain ⟨w, hw⟩ := h (hon rec y hf')
  have h2 : Kc.conf.RwfR (rd (T.in₁ rec), y) () := hR rec y w hw
  rw [hrd] at h2
  exact h2

/-- **The first relation's language is the key file's language**, where rd reads the instance back
from the first record. -/
theorem keyLangIs (T : Three (ckP .two) (DK.at a) all Kc.conf.Rec S₁ S₂ S₃ X₁ X₂ Cl W)
    (Q : Places (DK.at a) all S₁ S₂ S₃ W) (rd : S₁ → Kc.conf.Rec)
    (hrd : ∀ rec, rd (T.in₁ rec) = rec) : LangIs Kc T (Q.keyFirst Kc rd) := by
  intro rec y
  rw [keyFirst_on₁_zero, keyFirst_R₁_zero]
  show (Kc.conf.free (rd (T.in₁ rec), y) → ∃ _ : W, Kc.conf.RwfR (rd (T.in₁ rec), y) ()) ↔ _
  rw [hrd]
  constructor
  · intro h
    exact (keyL_iff Kc rec y).2 fun hf => (h hf).elim fun _ h => h
  · intro h hf
    exact ⟨T.d, (keyL_iff Kc rec y).1 h hf⟩

/-- The premise of `KeySoundOfBlocks`, paid. -/
theorem keyLangAt (T : Three (ckP .two) (DK.at a) all Kc.conf.Rec S₁ S₂ S₃ X₁ X₂ Cl W)
    (Q : Places (DK.at a) all S₁ S₂ S₃ W) (rd : S₁ → Kc.conf.Rec)
    (hrd : ∀ rec, rd (T.in₁ rec) = rec) : LangAt Kc T (Q.keyFirst Kc rd) :=
  (keyLangIs Kc T Q rd hrd).langAt

/-! ## 4 Trials on silly members -/

/-- The relation that holds of everything meets `LangAt` only if every table is in the
language at every record. -/
theorem lang_trial_all (T : Three (ckP .two) (DK.at a) all Kc.conf.Rec S₁ S₂ S₃ X₁ X₂ Cl W)
    (Q : Places (DK.at a) all S₁ S₂ S₃ W) (hR : ∀ b w, Q.R₁ 0 b w) :
    LangAt Kc T Q ↔ ∀ rec y, KeyL Kc rec y :=
  ⟨fun h rec y => h rec y fun _ => ⟨T.d, hR _ _⟩, fun h rec y _ => h rec y⟩

/-- The condition that holds of nothing: the like. -/
theorem lang_trial_off (T : Three (ckP .two) (DK.at a) all Kc.conf.Rec S₁ S₂ S₃ X₁ X₂ Cl W)
    (Q : Places (DK.at a) all S₁ S₂ S₃ W) (hon : ∀ b, ¬ Q.on₁ 0 b) :
    LangAt Kc T Q ↔ ∀ rec y, KeyL Kc rec y :=
  ⟨fun h rec y => h rec y fun h' => absurd h' (hon _), fun h rec y _ => h rec y⟩

/-- THE RELATION WITHOUT A WITNESS, ON ALL STATEMENTS, MEETS `LangAt`: the premise alone does
not fix the first relation. (What then cannot be met is the first block's goodness: soundness for
the empty language.) -/
theorem lang_trial_none_meets_half
    (T : Three (ckP .two) (DK.at a) all Kc.conf.Rec S₁ S₂ S₃ X₁ X₂ Cl W)
    (Q : Places (DK.at a) all S₁ S₂ S₃ W) (hon : ∀ b, Q.on₁ 0 b) (hR : ∀ b w, ¬ Q.R₁ 0 b w) :
    LangAt Kc T Q :=
  fun _ _ h => (h (hon _)).elim fun w hw => absurd hw (hR _ w)

/-- It meets `LangIs` only if no table is in the language at any record. -/
theorem lang_trial_none (T : Three (ckP .two) (DK.at a) all Kc.conf.Rec S₁ S₂ S₃ X₁ X₂ Cl W)
    (Q : Places (DK.at a) all S₁ S₂ S₃ W) (hon : ∀ b, Q.on₁ 0 b) (hR : ∀ b w, ¬ Q.R₁ 0 b w) :
    LangIs Kc T Q ↔ ∀ rec y, ¬ KeyL Kc rec y :=
  ⟨fun h rec y hL => ((h rec y).2 hL (hon _)).elim fun w hw => absurd hw (hR _ w),
    fun h rec y => ⟨fun h' => (h' (hon _)).elim fun w hw => absurd hw (hR _ w),
      fun hL => absurd hL (h rec y)⟩⟩

/-- A FIRST RECORD THAT FORGETS THE INSTANCE: whatever the condition and the relation are,
`LangIs` forces the language to be the same at two instances with the same first record. So the
first chain's first record has to hold the instance, also where no block of that chain reads it. -/
theorem lang_trial_forgets (T : Three (ckP .two) (DK.at a) all Kc.conf.Rec S₁ S₂ S₃ X₁ X₂ Cl W)
    (Q : Places (DK.at a) all S₁ S₂ S₃ W) (h : LangIs Kc T Q) (rec rec' : Kc.conf.Rec)
    (he : T.in₁ rec = T.in₁ rec') (y : Kc.conf.E0.Str) : KeyL Kc rec y ↔ KeyL Kc rec' y := by
  have h1 := h rec y
  rw [he] at h1
  exact h1.symm.trans (h rec' y)

end

/-- Under three laws of a configuration (`ConfigurationWithOutOfDomainSample.Props`: an honest word with an honest record decodes
and has no collision; the pads are not read) an honest table decodes with its record, and has no
collision: the language has a member by its second clause. -/
theorem member_of_laws {a : ℕ} (Kc : ConfLetters a)
    (dcd_enc : ∀ m r s, Kc.conf.dcd (Kc.conf.enc m r) (s, Kc.conf.smp s m) = some m)
    (free_enc : ∀ m r s, ¬ Kc.conf.coll (Kc.conf.enc m r) s)
    (held_hold : ∀ i η, Kc.conf.held (Kc.conf.hold i η) = some i)
    (i : Kc.conf.I) (η : Kc.conf.Pad) (r : Kc.conf.Rnd) (s : Kc.conf.Seed) :
    ¬ Kc.conf.coll (Kc.conf.enc (Kc.conf.hold i η) r) s ∧
      Kc.conf.D (Kc.conf.enc (Kc.conf.hold i η) r) (s, Kc.conf.smp s (Kc.conf.hold i η)) =
        some i := by
  refine ⟨free_enc _ _ _, ?_⟩
  unfold Hiop.ConfigurationWithOutOfDomainSample.D
  rw [if_neg (free_enc _ _ _), dcd_enc, Option.bind_some, held_hold]

/-! ### A toy: the trials' right-hand sides can fail -/

namespace Toy

/-- A configuration with one seed and two answers: a table decodes with the answer `true` alone;
there is no collision. -/
def kc : ConfLetters 0 where
  I := Unit
  X := Unit
  Cells := Unit
  Ryes := fun _ _ _ => True
  Rno := fun _ _ _ => True
  Msg := Unit
  Rnd := Unit
  enc := fun _ _ _ => (0, [])
  Pad := Unit
  hold := fun _ _ => ()
  held := fun _ => some ()
  Seed := Unit
  Ans := Bool
  smp := fun _ _ => true
  coll := fun _ _ => False
  dcd := fun _ rec => if rec.2 then some () else none
  trace := fun _ _ => ()
  cells0 := ()

theorem inside (y : kc.conf.E0.Str) : KeyL kc ((), true) y := by
  refine Or.inr ?_
  have hc : ¬ kc.conf.coll y ((), true).1 := fun h => h
  unfold Hiop.ConfigurationWithOutOfDomainSample.D
  rw [if_neg hc]
  intro h
  have h' : (some () : Option Unit) = none := h
  cases h'

theorem outside (y : kc.conf.E0.Str) : ¬ KeyL kc ((), false) y := by
  rintro (h | h)
  · exact h
  · apply h
    have hc : ¬ kc.conf.coll y ((), false).1 := fun h => h
    unfold Hiop.ConfigurationWithOutOfDomainSample.D
    rw [if_neg hc]
    rfl

end Toy

/-! ## 5 At the filling that is meant -/

section
variable {a : ℕ} (Kc : ConfLetters a) {DK : WholeD} {all : List LeftT}
  {X₁ X₂ Cl W P S₁' S₂' S₃' : Type}

/-- The reader at the filling that is meant: the carried record's first part is the instance's
public part; an inverse of `pub` reads the instance out of it. rec₀: its value at a first part that
is no instance's public part. -/
def rdPub (pub : Kc.conf.Rec → P) (rec₀ : Kc.conf.Rec) : P × S₁' → Kc.conf.Rec :=
  fun s => @Function.invFun _ _ ⟨rec₀⟩ pub s.1

/-- **At the filling that is meant, with an injective public part, the first relation's language is
the key file's language.** -/
theorem keyLangIs_ofStarts (pub : Kc.conf.Rec → P) (hpub : Function.Injective pub)
    (rec₀ : Kc.conf.Rec) (start₁ : P → S₁') (start₂ : P → S₂')
    (start₃ : P → S₁' → S₂' → Option S₃')
    (T : Three (ckP .two) (DK.at a) all Kc.conf.Rec (P × S₁') ((P × S₁') × S₂')
      ((P × S₁' × S₂') × S₃') X₁ X₂ Cl W)
    (Q : Places (DK.at a) all (P × S₁') ((P × S₁') × S₂') ((P × S₁' × S₂') × S₃') W) :
    LangIs Kc (Three.ofStarts pub start₁ start₂ start₃ T) (Q.keyFirst Kc (rdPub Kc pub rec₀)) :=
  keyLangIs Kc _ Q _ fun rec => @Function.leftInverse_invFun _ _ ⟨rec₀⟩ pub hpub rec

end

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.keyL_iff
#print axioms VerifiableInference.Desc.Sound.keyLangAt_of
#print axioms VerifiableInference.Desc.Sound.keyLangIs
#print axioms VerifiableInference.Desc.Sound.keyLangAt
#print axioms VerifiableInference.Desc.Sound.lang_trial_all
#print axioms VerifiableInference.Desc.Sound.lang_trial_off
#print axioms VerifiableInference.Desc.Sound.lang_trial_none_meets_half
#print axioms VerifiableInference.Desc.Sound.lang_trial_none
#print axioms VerifiableInference.Desc.Sound.lang_trial_forgets
#print axioms VerifiableInference.Desc.Sound.member_of_laws
#print axioms VerifiableInference.Desc.Sound.Toy.inside
#print axioms VerifiableInference.Desc.Sound.Toy.outside
#print axioms VerifiableInference.Desc.Sound.keyLangIs_ofStarts
