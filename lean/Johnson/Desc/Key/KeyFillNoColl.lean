-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Key/KeyFillNoColl.lean: AT A WORD THAT IS A CODE WORD, NoColl (Johnson/Desc/Msg.lean) HOLDS AT THE FILLING OVER A FAMILY OF SEATS (KeyFillFam.famG): SO PIN AND THE PROMISE BESIDE IT CAN BE MET TOGETHER, AT ALL SEATS. Two things laid together: the library's
«at a radius below the distance the list of an encoding has one message» (Johnson/Top/Fam/BattShortInhabited.lean) and the bridge sealed_gives (Johnson/Desc/Key/KeySealTie.lean), at fam_seals.
  inJohnson_lt        InJohnson n d e → e < d: arithmetic alone
  rad_lt_of_meetsAt   the library's MeetsAt cs s e d L (what its Bool meetsB gives) → e < d
  noClash_honest      MeetsAt → upW f = C.enc m₀ r₀ → no seed has a collision in f's list
  fam_noColl_honest   at member i: a record that spells a sample (ANY answer), a committed word that reads as a code word ⟹ hasSmp ∧ NoColl. No «every leaf is shown» is asked
  fam_members_noColl  ONE y, ONE record: at every member a told tree, a sample, a Member, hasSmp and NoColl
  fam_promise_met     and PIN ∧ hasSmp ∧ NoColl at one witness whose tables at the seats are the messages' (a premise)
ONE e, NOT TWO: a member's encoding is within e of the word, and the word IS an encoding: so the difference of the two has weight ≤ e < d. M IS THE TABLE ALONE: nothing asks for one randomness.
OBJECT: none: a filling of letters · USER: Johnson/Desc/Key/KeyFillNoCollAt.lean · LETTERS: F · cs · l · seat · cell · seedIs · a · W.
NOT SAID: NoColl at a word that is not a code word (there two members may each be e away; that is what a sending's law prices); that a run of the programs lays such a word or record; SeatFits | MeetsAt at a real description. At l := [] all is true for nothing.
Nothing on soundness.
-/
import Johnson.Desc.Key.KeyFillSent
import Johnson.Pack.Check
import Johnson.Top.Fam.BattShortInhabited

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Key.Fill
open VerifiableInference.Desc VerifiableInference.Desc.Sound
open Cb Johnson.Pack OnBytes.Slice Prob

theorem inJohnson_lt {n d e : ℕ} (h : InJohnson n d e) : e < d := by
  by_contra hc
  have hde : d ≤ e := Nat.le_of_not_lt hc
  have h1 : n - e ≤ n - d := Nat.sub_le_sub_left hde n
  have h2 : (n - e) ^ 2 ≤ n * (n - d) :=
    calc (n - e) ^ 2 = (n - e) * (n - e) := pow_two _
      _ ≤ (n - d) * (n - d) := Nat.mul_le_mul h1 h1
      _ ≤ n * (n - d) := Nat.mul_le_mul_right _ (Nat.sub_le n d)
  exact absurd h (Nat.not_lt.2 h2)

variable (cs : OnBytes.Codes)

theorem rad_lt_of_meetsAt (s : OnBytes.OracleShape) (e d L : ℕ) (g : MeetsAt cs s e d L) : e < d := by
  rcases g.2 with h | h
  · have := h.1
    omega
  · exact inJohnson_lt h.2.2.2.1

/-- **No seed has a collision in the list of a code word.** -/
theorem noClash_honest (s : OnBytes.OracleShape) (e d L : ℕ) (g : MeetsAt cs s e d L) (f : (portOmZ cs s e).Str) (m₀ : (portOmZ cs s e).Msg) (r₀ : (portOmZ cs s e).Rnd)
    (hf : (portOmZ cs s e).upW f = (portOmZ cs s e).C.enc m₀ r₀) (ρ : (portOmZ cs s e).Z.D) : ¬ (portOmZ cs s e).Clash f ρ :=
  KObj.KBattShortF_inhabited_noClash (portOmZ cs s e) (port_laws cs s g.1.ok) (port_dist cs s g.1.ok d g.1.d1 g.1.d2) (rad_lt_of_meetsAt cs s e d L g) f (m₀, r₀) hf ρ

variable (l : List (OnBytes.OracleShape × ℕ)) (seat : Fin l.length → ℕ × ℕ) {XI : Type} (F : FileDescription XI)
  {A Cells Rec : Type} (seedIs : ∀ i : Fin l.length, A → (OmAt cs l i).Z.D → ((OmAt cs l i).Z.S → GE) → Prop)
  (arr : ℕ → ℕ → ℕ) (lay : ℕ → ℕ → Tab → Tab → Tab) (decT : (ℕ → Option (ℕ × List UInt64)) → Rec → Option Cells) (recOf : A → Option Rec)

/-- **R9: NoColl AT A WORD THAT READS AS A CODE WORD, at every member.** -/
theorem fam_noColl_honest (hinj : Function.Injective seat) (i : Fin l.length) (hlog : ∀ o, F.oracleAt (seat i).1 = some o → o.logLength = aOf cs (l.get i).1)
    (hm : (l.get i).1.mainRows = 0 ∨ (cMain cs (l.get i).1).a = aOf cs (l.get i).1)
    (uniq : ∀ a ρ v ρ' v', seedIs i a ρ v → seedIs i a ρ' v' → (OmAt cs l i).Z.val ρ = (OmAt cs l i).Z.val ρ' ∧ v = v')
    (d L : ℕ) (g : MeetsAt cs (l.get i).1 (l.get i).2 d L) (a : A) (y : Strs) (m₀ : (OmAt cs l i).Msg) (r₀ : (OmAt cs l i).Rnd) (ρ : (OmAt cs l i).Z.D)
    (v : (OmAt cs l i).Z.S → GE) (hs : seedIs i a ρ v)
    (hw : (OmAt cs l i).upW (symsW cs (l.get i).1 (l.get i).2 (wordOf F y (seat i).1 (seat i).2)) = (OmAt cs l i).C.enc m₀ r₀) :
    hasSmp (famG cs l seat seedIs arr lay decT recOf) (seat i).1 (seat i).2 a = true ∧ NoColl F (famG cs l seat seedIs arr lay decT recOf) (seat i).1 (seat i).2 a y :=
  sealed_gives F (famG cs l seat seedIs arr lay decT recOf) (fun y : Strs => y) _ _ (seedIs i) (seat i).1 (seat i).2
    (fam_seals cs l seat seedIs arr lay decT recOf hinj F (fun y : Strs => y) i hlog hm uniq) a y
    ⟨ρ, v, hs, noClash_honest cs _ _ d L g _ m₀ r₀ hw ρ⟩

/-- **ONE y, ONE RECORD: A MEMBER AND THE PROMISE AT EVERY SEAT.** -/
theorem fam_members_noColl (hinj : Function.Injective seat) (hS : SeatFits F cs l seat)
    (uniq : ∀ i a ρ v ρ' v', seedIs i a ρ v → seedIs i a ρ' v' → (OmAt cs l i).Z.val ρ = (OmAt cs l i).Z.val ρ' ∧ v = v')
    (hB : allMeet cs l = true) (cell : ℕ → Option (ℕ × List UInt64)) (a : A) (m₀ : ∀ i : Fin l.length, (OmAt cs l i).Msg)
    (r₀ : ∀ i : Fin l.length, (OmAt cs l i).Rnd) (ρ : ∀ i : Fin l.length, (OmAt cs l i).Z.D)
    (hsend : ∀ i, Sendable cs (l.get i).1 (l.get i).2 (m₀ i, r₀ i)) (hs : ∀ i, seedIs i a (ρ i) ((OmAt cs l i).Z.val (ρ i) (m₀ i))) :
    ∃ y : Strs, y.cell = cell ∧ ∀ i : Fin l.length,
      (∃ o z, F.oracleAt (seat i).1 = some o ∧ (famG cs l seat seedIs arr lay decT recOf).smp a (seat i).1 (seat i).2 = some z ∧
        Member F (famG cs l seat seedIs arr lay decT recOf) o (seat i).1 (seat i).2 y z (ofU cs (l.get i).1 (l.get i).2 (m₀ i))) ∧
      hasSmp (famG cs l seat seedIs arr lay decT recOf) (seat i).1 (seat i).2 a = true ∧
      NoColl F (famG cs l seat seedIs arr lay decT recOf) (seat i).1 (seat i).2 a y := by
  choose f hf using fun i => sent_of cs (l.get i).1 (l.get i).2 (m₀ i, r₀ i) (hsend i)
  obtain ⟨y, hcell, hy⟩ := exists_strs cs l seat F hinj hS cell f
  refine ⟨y, hcell, fun i => ?_⟩
  obtain ⟨hsh, _, hsy⟩ := hy i
  obtain ⟨o, _, ho, _, hlog, _, _, hm, _, _⟩ := hS i
  have hL : ∀ o', F.oracleAt (seat i).1 = some o' → o'.logLength = aOf cs (l.get i).1 := fun o' ho' => by
    obtain rfl : o' = o := Option.some.inj (ho'.symm.trans ho)
    exact hlog
  have hw : (OmAt cs l i).upW (symsW cs (l.get i).1 (l.get i).2 (wordOf F y (seat i).1 (seat i).2)) = (OmAt cs l i).C.enc (m₀ i) (r₀ i) := by
    rw [hsy]
    exact hf i
  obtain ⟨hh, hn⟩ := fam_noColl_honest cs l seat F seedIs arr lay decT recOf hinj i hL hm (uniq i) _ _ (allMeet_sound cs l hB i) a y (m₀ i) (r₀ i) (ρ i) _ (hs i) hw
  obtain ⟨z, hz⟩ := Option.isSome_iff_exists.1 hh
  exact ⟨⟨o, z, ho, hz, fam_honest_member cs l seat F seedIs arr lay decT recOf hinj i hL hm (uniq i) a y o z (m₀ i) (r₀ i) (ρ i) ho hz (hs i) hsh hw⟩, hh, hn⟩

/-- **PIN AND ITS PROMISE TOGETHER, AT ALL SEATS**, at a witness whose tables at the seats are the messages' (a premise: arr and lay are letters). -/
theorem fam_promise_met {Tok : Type} (hinj : Function.Injective seat) (hS : SeatFits F cs l seat)
    (uniq : ∀ i a ρ v ρ' v', seedIs i a ρ v → seedIs i a ρ' v' → (OmAt cs l i).Z.val ρ = (OmAt cs l i).Z.val ρ' ∧ v = v')
    (hB : allMeet cs l = true) (cell : ℕ → Option (ℕ × List UInt64)) (a : A) (m₀ : ∀ i : Fin l.length, (OmAt cs l i).Msg)
    (r₀ : ∀ i : Fin l.length, (OmAt cs l i).Rnd) (ρ : ∀ i : Fin l.length, (OmAt cs l i).Z.D)
    (hsend : ∀ i, Sendable cs (l.get i).1 (l.get i).2 (m₀ i, r₀ i)) (hs : ∀ i, seedIs i a (ρ i) ((OmAt cs l i).Z.val (ρ i) (m₀ i)))
    (W : Wit Cells Tok Tab) (hW : ∀ i, msgOf (famG cs l seat seedIs arr lay decT recOf) W (seat i).1 (seat i).2 = ofU cs (l.get i).1 (l.get i).2 (m₀ i)) :
    ∃ y : Strs, y.cell = cell ∧ ∀ i : Fin l.length, PIN F (famG cs l seat seedIs arr lay decT recOf) (seat i).1 (seat i).2 a y W ∧
      hasSmp (famG cs l seat seedIs arr lay decT recOf) (seat i).1 (seat i).2 a = true ∧
      NoColl F (famG cs l seat seedIs arr lay decT recOf) (seat i).1 (seat i).2 a y := by
  obtain ⟨y, hcell, hy⟩ := fam_members_noColl cs l seat F seedIs arr lay decT recOf hinj hS uniq hB cell a m₀ r₀ ρ hsend hs
  refine ⟨y, hcell, fun i => ?_⟩
  obtain ⟨⟨o, z, ho, hz, hM⟩, hh, hn⟩ := hy i
  refine ⟨⟨o, z, ho, hz, ?_⟩, hh, hn⟩
  rw [hW i]
  exact hM

end VerifiableInference.Desc.Key.Fill

#print axioms VerifiableInference.Desc.Key.Fill.inJohnson_lt
#print axioms VerifiableInference.Desc.Key.Fill.rad_lt_of_meetsAt
#print axioms VerifiableInference.Desc.Key.Fill.noClash_honest
#print axioms VerifiableInference.Desc.Key.Fill.fam_noColl_honest
#print axioms VerifiableInference.Desc.Key.Fill.fam_members_noColl
#print axioms VerifiableInference.Desc.Key.Fill.fam_promise_met
