-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- ShownAt of Johnson/Desc/Sound/MsgSig.lean is written Sound.ShownAt, to tell it from the tables' own Key.ShownAt.
/-
Johnson/Desc/Key/KeyFillFamLays.lean: THE FAMILY's LOWER HALF: KeyCandTie.LaysReads AT THE FILLING OVER A FAMILY OF SEATS (KeyFillFam.famG), AT EVERY MEMBER; and, with its upper half fam_seals, member_iff_cand AT THAT READING. What
KeyFillLays.lean (not in this library) has at fillG (one tenant, where every other PIN of a file is false) stands here at the reading that can bear a border.
  hlog_of_fits | hm_of_fits | told_of_fits   SeatFits (Johnson/Desc/Sound/MsgSig.lean) gives the three public premises, at every member
  fam_lays i             LaysReads F famG str (the library's list of the word read off the oracles) Z.val (seedIs i) (Sound.ShownAt) (seat i) (toU): A TERM AT EVERY MEMBER
  fam_member_iff_cand i  AT famG: a table is a member of the committed word's list that meets the record's sample JUST IF its image is a candidate of the library's and it is that candidate written back
  fam_cand_gives_pin i   a candidate of the library's gives PIN (Johnson/Desc/Msg.lean) at famG, at a witness whose table at the seat is the candidate written back
  …_of_fits              the three, with SeatFits in place of hlog | hm | told
OBJECT: none: a filling of letters · USER: Johnson/Desc/Key/KeyFillSrc.lean · LETTERS: cs · l · seat · seedIs · arr · lay · decT · recOf · F · str.
NOT SAID: who gives the candidates; that there is no collision; that SeatFits holds at a real description; seedIs is a letter under (uniq). At l := [] all is true for nothing.
Nothing on soundness.
-/
import Johnson.Desc.Key.KeyFillFam
import Johnson.Desc.Key.KeyCandTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Key.Fill
open VerifiableInference.Desc VerifiableInference.Desc.Sound
open Cb Johnson.Pack OnBytes.Slice

variable (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ)) (seat : Fin l.length → ℕ × ℕ)

section
variable {XI : Type} (F : FileDescription XI)

theorem hlog_of_fits (hS : SeatFits F cs l seat) (i : Fin l.length) : ∀ o, F.oracleAt (seat i).1 = some o → o.logLength = aOf cs (l.get i).1 := fun o' ho' => by
  obtain ⟨o, _, ho, _, hlog, _⟩ := hS i
  obtain rfl : o' = o := Option.some.inj (ho'.symm.trans ho)
  exact hlog

theorem hm_of_fits (hS : SeatFits F cs l seat) (i : Fin l.length) : (l.get i).1.mainRows = 0 ∨ (cMain cs (l.get i).1).a = aOf cs (l.get i).1 := by
  obtain ⟨_, _, _, _, _, _, _, hm, _⟩ := hS i
  exact hm

theorem told_of_fits (hS : SeatFits F cs l seat) (i : Fin l.length) : (F.oracleAt (seat i).1).isSome = true := by
  obtain ⟨o, _, ho, _⟩ := hS i
  rw [ho]
  rfl

end

variable {A Cells Rec : Type} (seedIs : ∀ i : Fin l.length, A → (OmAt cs l i).Z.D → ((OmAt cs l i).Z.S → GE) → Prop)
  (arr : ℕ → ℕ → ℕ) (lay : ℕ → ℕ → Tab → Tab → Tab) (decT : (ℕ → Option (ℕ × List UInt64)) → Rec → Option Cells) (recOf : A → Option Rec)
  (hinj : Function.Injective seat) {XI Y' : Type} (F : FileDescription XI) (str : Y' → Strs)
include hinj

/-- **THE LOWER HALF, AT EVERY MEMBER.** -/
def fam_lays (i : Fin l.length) (hlog : ∀ o, F.oracleAt (seat i).1 = some o → o.logLength = aOf cs (l.get i).1)
    (hm : (l.get i).1.mainRows = 0 ∨ (cMain cs (l.get i).1).a = aOf cs (l.get i).1)
    (uniq : ∀ a ρ v ρ' v', seedIs i a ρ v → seedIs i a ρ' v' → (OmAt cs l i).Z.val ρ = (OmAt cs l i).Z.val ρ' ∧ v = v')
    (told : (F.oracleAt (seat i).1).isSome = true) :
    LaysReads F (famG cs l seat seedIs arr lay decT recOf) str
      (fun y' => (OmAt cs l i).InList (symsW cs (l.get i).1 (l.get i).2 (wordOf F (str y') (seat i).1 (seat i).2)))
      (OmAt cs l i).Z.val (seedIs i) (fun y' => Sound.ShownAt F cs l seat (str y') i) (seat i).1 (seat i).2 (toU cs (l.get i).1 (l.get i).2) where
  ofU := ofU cs (l.get i).1 (l.get i).2
  sec := fun _ u _ => toU_ofU cs (l.get i).1 (l.get i).2 u
  told := told
  mem := fun a y' o z u ρ y ho hz hs hsh hc =>
    fam_member_of_cand cs l seat seedIs arr lay decT recOf hinj F i hlog hm uniq a (str y') o z u ρ y ho hz hs hsh hc

/-- **The pair pins the reading, at famG, at every member.** -/
theorem fam_member_iff_cand (i : Fin l.length) (hlog : ∀ o, F.oracleAt (seat i).1 = some o → o.logLength = aOf cs (l.get i).1)
    (hm : (l.get i).1.mainRows = 0 ∨ (cMain cs (l.get i).1).a = aOf cs (l.get i).1)
    (uniq : ∀ a ρ v ρ' v', seedIs i a ρ v → seedIs i a ρ' v' → (OmAt cs l i).Z.val ρ = (OmAt cs l i).Z.val ρ' ∧ v = v')
    (told : (F.oracleAt (seat i).1).isSome = true) {a : A} {y' : Y'} {o : Oracle} {z : Σ i : Fin l.length, (OmAt cs l i).Smp}
    {ρ : (OmAt cs l i).Z.D} {v : (OmAt cs l i).Z.S → GE} (ho : F.oracleAt (seat i).1 = some o)
    (hz : (famG cs l seat seedIs arr lay decT recOf).smp a (seat i).1 (seat i).2 = some z) (hse : seedIs i a ρ v)
    (hsh : Sound.ShownAt F cs l seat (str y') i) (m : Tab) :
    Member F (famG cs l seat seedIs arr lay decT recOf) o (seat i).1 (seat i).2 (str y') z m ↔
      Cb.Ood.Cand ((OmAt cs l i).InList (symsW cs (l.get i).1 (l.get i).2 (wordOf F (str y') (seat i).1 (seat i).2)))
        (OmAt cs l i).Z.val ρ v (toU cs (l.get i).1 (l.get i).2 m) ∧ ofU cs (l.get i).1 (l.get i).2 (toU cs (l.get i).1 (l.get i).2 m) = m :=
  member_iff_cand F (famG cs l seat seedIs arr lay decT recOf)
    (fam_seals cs l seat seedIs arr lay decT recOf hinj F str i hlog hm uniq)
    (fam_lays cs l seat seedIs arr lay decT recOf hinj F str i hlog hm uniq told) ho hz hse hsh m

/-- **A candidate of the library's gives the pin, at famG, at every member.** -/
theorem fam_cand_gives_pin (i : Fin l.length) (hlog : ∀ o, F.oracleAt (seat i).1 = some o → o.logLength = aOf cs (l.get i).1)
    (hm : (l.get i).1.mainRows = 0 ∨ (cMain cs (l.get i).1).a = aOf cs (l.get i).1)
    (uniq : ∀ a ρ v ρ' v', seedIs i a ρ v → seedIs i a ρ' v' → (OmAt cs l i).Z.val ρ = (OmAt cs l i).Z.val ρ' ∧ v = v')
    (told : (F.oracleAt (seat i).1).isSome = true) {a : A} {y' : Y'} {ρ : (OmAt cs l i).Z.D} {v : (OmAt cs l i).Z.S → GE} {u : (OmAt cs l i).Msg}
    {w : Wit Cells Unit Tab} (hse : seedIs i a ρ v) (hsh : Sound.ShownAt F cs l seat (str y') i)
    (hc : Cb.Ood.Cand ((OmAt cs l i).InList (symsW cs (l.get i).1 (l.get i).2 (wordOf F (str y') (seat i).1 (seat i).2))) (OmAt cs l i).Z.val ρ v u)
    (hw : msgOf (famG cs l seat seedIs arr lay decT recOf) w (seat i).1 (seat i).2 = ofU cs (l.get i).1 (l.get i).2 u) :
    PIN F (famG cs l seat seedIs arr lay decT recOf) (seat i).1 (seat i).2 a (str y') w :=
  cand_gives_pin F (famG cs l seat seedIs arr lay decT recOf)
    (fam_lays cs l seat seedIs arr lay decT recOf hinj F str i hlog hm uniq told)
    ((fam_seals cs l seat seedIs arr lay decT recOf hinj F str i hlog hm uniq).has a ρ v hse) hse hsh hc hw

/-! ## The same, with SeatFits in place of the three premises -/

/-- Both halves at every member, from SeatFits and (uniq). -/
def fam_seals_of_fits (hS : SeatFits F cs l seat)
    (uniq : ∀ i a ρ v ρ' v', seedIs i a ρ v → seedIs i a ρ' v' → (OmAt cs l i).Z.val ρ = (OmAt cs l i).Z.val ρ' ∧ v = v') (i : Fin l.length) :
    SealReads F (famG cs l seat seedIs arr lay decT recOf) str
      (fun y' => (OmAt cs l i).InList (symsW cs (l.get i).1 (l.get i).2 (wordOf F (str y') (seat i).1 (seat i).2)))
      (OmAt cs l i).Z.val (seedIs i) (seat i).1 (seat i).2 :=
  fam_seals cs l seat seedIs arr lay decT recOf hinj F str i (hlog_of_fits cs l seat F hS i) (hm_of_fits cs l seat F hS i) (uniq i)

def fam_lays_of_fits (hS : SeatFits F cs l seat)
    (uniq : ∀ i a ρ v ρ' v', seedIs i a ρ v → seedIs i a ρ' v' → (OmAt cs l i).Z.val ρ = (OmAt cs l i).Z.val ρ' ∧ v = v') (i : Fin l.length) :
    LaysReads F (famG cs l seat seedIs arr lay decT recOf) str
      (fun y' => (OmAt cs l i).InList (symsW cs (l.get i).1 (l.get i).2 (wordOf F (str y') (seat i).1 (seat i).2)))
      (OmAt cs l i).Z.val (seedIs i) (fun y' => Sound.ShownAt F cs l seat (str y') i) (seat i).1 (seat i).2 (toU cs (l.get i).1 (l.get i).2) :=
  fam_lays cs l seat seedIs arr lay decT recOf hinj F str i (hlog_of_fits cs l seat F hS i) (hm_of_fits cs l seat F hS i) (uniq i) (told_of_fits cs l seat F hS i)

end VerifiableInference.Desc.Key.Fill

#print axioms VerifiableInference.Desc.Key.Fill.hlog_of_fits
#print axioms VerifiableInference.Desc.Key.Fill.hm_of_fits
#print axioms VerifiableInference.Desc.Key.Fill.told_of_fits
#print axioms VerifiableInference.Desc.Key.Fill.fam_lays
#print axioms VerifiableInference.Desc.Key.Fill.fam_member_iff_cand
#print axioms VerifiableInference.Desc.Key.Fill.fam_cand_gives_pin
#print axioms VerifiableInference.Desc.Key.Fill.fam_seals_of_fits
#print axioms VerifiableInference.Desc.Key.Fill.fam_lays_of_fits
