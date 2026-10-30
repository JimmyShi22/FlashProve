-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Key/KeyFillFam.lean: THE FILLING OF THE PLAIN READING (Johnson/Desc/Msg.lean) BY THE LIBRARY's ORACLE MESSAGES, AT A FAMILY OF SEATS: the three letters of Johnson/Desc/Sound/MsgSig.lean: cs · l : List (OracleShape × ℕ) (shapes with their radii) ·
seat : Fin l.length → ℕ × ℕ (tree, tenant), INJECTIVE. Over Johnson/Desc/Key/KeyFill.lean's two hearts (inList_of_far · far_of_inList).
  famG               the reading: enc … j t m u := at SOME member i with seat i = (j, t): EncAt at i's shape and radius · rad := that member's radius (0 at no seat) · Smp := Σ i, the member's sample · smp := at the member of the seat: some
                     sample with seedIs i, by choice · meets … m z := z's member sits at (j, t) and the library's answers of the table at z's seed are z's
  fam_seals i        THE UPPER HALF AT EVERY MEMBER: a term of SealReads
  fam_member_of_cand THE LOWER HALF's HEART AT EVERY MEMBER
OBJECT: none: a filling of letters · USER: Johnson/Desc/Key/KeyFillStrs.lean · Johnson/Desc/Key/KeyFillFamLays.lean · LETTERS: cs · l · seat · seedIs.
Nothing on soundness.
-/
import Johnson.Desc.Key.KeyFill

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Key.Fill
open VerifiableInference.Desc VerifiableInference.Desc.Sound
open Cb Johnson.Pack OnBytes.Slice Prob

variable (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ)) (seat : Fin l.length → ℕ × ℕ)

/-- Member i's oracle message. -/
abbrev OmAt (i : Fin l.length) : OMsg GE := portOmZ cs (l.get i).1 (l.get i).2

variable {A Cells Rec : Type} (seedIs : ∀ i : Fin l.length, A → (OmAt cs l i).Z.D → ((OmAt cs l i).Z.S → GE) → Prop)
  (arr : ℕ → ℕ → ℕ) (lay : ℕ → ℕ → Tab → Tab → Tab) (decT : (ℕ → Option (ℕ × List UInt64)) → Rec → Option Cells) (recOf : A → Option Rec)

open Classical in
/-- **The filling at a family of seats.** -/
def famG : Reading A Cells Tab (Σ i : Fin l.length, (OmAt cs l i).Smp) Rec where
  arr := arr
  lay := lay
  enc := fun _ j t m u => ∃ i : Fin l.length, seat i = (j, t) ∧ EncAt cs (l.get i).1 (l.get i).2 m u
  rad := fun _ j t => if h : ∃ i : Fin l.length, seat i = (j, t) then (l.get h.choose).2 else 0
  meets := fun _ j t m z => seat z.1 = (j, t) ∧ (OmAt cs l z.1).Z.val z.2.1 (toU cs (l.get z.1).1 (l.get z.1).2 m) = z.2.2
  smp := fun a j t => if h : ∃ i : Fin l.length, seat i = (j, t) then
      (if h' : ∃ z : (OmAt cs l h.choose).Smp, seedIs h.choose a z.1 z.2 then some ⟨h.choose, h'.choose⟩ else none) else none
  decT := decT
  recOf := recOf

variable (hinj : Function.Injective seat)
include hinj

theorem choose_seat (i : Fin l.length) (h : ∃ i' : Fin l.length, seat i' = ((seat i).1, (seat i).2)) : h.choose = i :=
  hinj h.choose_spec

theorem fam_rad (o : Oracle) (i : Fin l.length) : (famG cs l seat seedIs arr lay decT recOf).rad o (seat i).1 (seat i).2 = (l.get i).2 := by
  classical
  have h : ∃ i' : Fin l.length, seat i' = ((seat i).1, (seat i).2) := ⟨i, rfl⟩
  show (if h : ∃ i' : Fin l.length, seat i' = ((seat i).1, (seat i).2) then (l.get h.choose).2 else 0) = _
  rw [dif_pos h, choose_seat l seat hinj i h]

theorem fam_smp_spec {a : A} (i : Fin l.length) {z : Σ i : Fin l.length, (OmAt cs l i).Smp}
    (hz : (famG cs l seat seedIs arr lay decT recOf).smp a (seat i).1 (seat i).2 = some z) : ∃ z' : (OmAt cs l i).Smp, z = ⟨i, z'⟩ ∧ seedIs i a z'.1 z'.2 := by
  classical
  have h : ∃ i' : Fin l.length, seat i' = ((seat i).1, (seat i).2) := ⟨i, rfl⟩
  have hz' : (if h : ∃ i' : Fin l.length, seat i' = ((seat i).1, (seat i).2) then
      (if h' : ∃ z : (OmAt cs l h.choose).Smp, seedIs h.choose a z.1 z.2 then some (⟨h.choose, h'.choose⟩ : Σ i : Fin l.length, (OmAt cs l i).Smp) else none) else none) = some z := hz
  rw [dif_pos h] at hz'
  have hc := choose_seat l seat hinj i h
  generalize h.choose = i' at hz' hc
  subst hc
  split at hz'
  · rename_i h'
    exact ⟨h'.choose, (Option.some.inj hz').symm, h'.choose_spec⟩
  · exact nomatch hz'

theorem fam_has {a : A} (i : Fin l.length) (z : (OmAt cs l i).Smp) (hs : seedIs i a z.1 z.2) :
    hasSmp (famG cs l seat seedIs arr lay decT recOf) (seat i).1 (seat i).2 a = true := by
  classical
  have h : ∃ i' : Fin l.length, seat i' = ((seat i).1, (seat i).2) := ⟨i, rfl⟩
  show (if h : ∃ i' : Fin l.length, seat i' = ((seat i).1, (seat i).2) then
      (if h' : ∃ z : (OmAt cs l h.choose).Smp, seedIs h.choose a z.1 z.2 then some (⟨h.choose, h'.choose⟩ : Σ i : Fin l.length, (OmAt cs l i).Smp) else none) else none).isSome = true
  rw [dif_pos h]
  have hc := choose_seat l seat hinj i h
  generalize h.choose = i' at hc
  subst hc
  rw [dif_pos ⟨z, hs⟩]
  rfl

theorem fam_enc {o : Oracle} (i : Fin l.length) {m : Tab} {u : ℕ → Option Sym}
    (h : (famG cs l seat seedIs arr lay decT recOf).enc o (seat i).1 (seat i).2 m u) : EncAt cs (l.get i).1 (l.get i).2 m u := by
  obtain ⟨i', hi, hE⟩ := h
  obtain rfl : i' = i := hinj hi
  exact hE

variable {XI Y' : Type} (F : FileDescription XI) (str : Y' → Strs)

/-- **THE UPPER HALF, AT EVERY MEMBER.** -/
def fam_seals (i : Fin l.length) (hlog : ∀ o, F.oracleAt (seat i).1 = some o → o.logLength = aOf cs (l.get i).1)
    (hm : (l.get i).1.mainRows = 0 ∨ (cMain cs (l.get i).1).a = aOf cs (l.get i).1)
    (uniq : ∀ a ρ v ρ' v', seedIs i a ρ v → seedIs i a ρ' v' → (OmAt cs l i).Z.val ρ = (OmAt cs l i).Z.val ρ' ∧ v = v') :
    SealReads F (famG cs l seat seedIs arr lay decT recOf) str
      (fun y' => (OmAt cs l i).InList (symsW cs (l.get i).1 (l.get i).2 (wordOf F (str y') (seat i).1 (seat i).2)))
      (OmAt cs l i).Z.val (seedIs i) (seat i).1 (seat i).2 where
  toU := toU cs (l.get i).1 (l.get i).2
  has := fun a ρ y hs => fam_has cs l seat seedIs arr lay decT recOf hinj i (ρ, y) hs
  inj := fun a y' o z m m' _ _ hM hM' he => by
    obtain ⟨⟨_, hE, _⟩, _⟩ := hM
    obtain ⟨⟨_, hE', _⟩, _⟩ := hM'
    exact toU_inj cs _ _ (fam_enc cs l seat seedIs arr lay decT recOf hinj i hE).1 (fam_enc cs l seat seedIs arr lay decT recOf hinj i hE').1 he
  mem := fun a y' o z m ρ y ho hz hs hM => by
    obtain ⟨⟨u, hE, hfar⟩, hmeets⟩ := hM
    rw [fam_rad cs l seat seedIs arr lay decT recOf hinj o i, hlog o ho] at hfar
    refine ⟨inList_of_far cs _ _ hm _ u m (fam_enc cs l seat seedIs arr lay decT recOf hinj i hE) hfar, ?_⟩
    obtain ⟨z', rfl, hz'⟩ := fam_smp_spec cs l seat seedIs arr lay decT recOf hinj i hz
    obtain ⟨e1, e2⟩ := uniq a ρ y z'.1 z'.2 hs hz'
    rw [e1, e2]
    exact hmeets.2

/-- **THE LOWER HALF's HEART, AT EVERY MEMBER.** -/
theorem fam_member_of_cand (i : Fin l.length) (hlog : ∀ o, F.oracleAt (seat i).1 = some o → o.logLength = aOf cs (l.get i).1)
    (hm : (l.get i).1.mainRows = 0 ∨ (cMain cs (l.get i).1).a = aOf cs (l.get i).1)
    (uniq : ∀ a ρ v ρ' v', seedIs i a ρ v → seedIs i a ρ' v' → (OmAt cs l i).Z.val ρ = (OmAt cs l i).Z.val ρ' ∧ v = v')
    (a : A) (y : Strs) (o : Oracle) (z : Σ i : Fin l.length, (OmAt cs l i).Smp) (u₀ : (OmAt cs l i).Msg) (ρ : (OmAt cs l i).Z.D) (v : (OmAt cs l i).Z.S → GE)
    (ho : F.oracleAt (seat i).1 = some o) (hz : (famG cs l seat seedIs arr lay decT recOf).smp a (seat i).1 (seat i).2 = some z) (hs : seedIs i a ρ v)
    (hsh : ∀ k, k < 2 ^ aOf cs (l.get i).1 → (wordOf F y (seat i).1 (seat i).2 k).isSome = true)
    (hc : Cb.Ood.Cand ((OmAt cs l i).InList (symsW cs (l.get i).1 (l.get i).2 (wordOf F y (seat i).1 (seat i).2))) (OmAt cs l i).Z.val ρ v u₀) :
    Member F (famG cs l seat seedIs arr lay decT recOf) o (seat i).1 (seat i).2 y z (ofU cs (l.get i).1 (l.get i).2 u₀) := by
  obtain ⟨hin, hval⟩ := hc
  obtain ⟨u, hE, hfar⟩ := far_of_inList cs _ _ hm _ hsh u₀ hin
  obtain ⟨z', rfl, hz'⟩ := fam_smp_spec cs l seat seedIs arr lay decT recOf hinj i hz
  obtain ⟨e1, e2⟩ := uniq a ρ v z'.1 z'.2 hs hz'
  refine ⟨⟨u, ⟨i, rfl, hE⟩, ?_⟩, rfl, ?_⟩
  · rw [fam_rad cs l seat seedIs arr lay decT recOf hinj o i, hlog o ho]
    exact hfar
  · show (OmAt cs l i).Z.val z'.1 (toU cs (l.get i).1 (l.get i).2 (ofU cs (l.get i).1 (l.get i).2 u₀)) = z'.2
    rw [toU_ofU, ← e1, ← e2]
    exact hval

end VerifiableInference.Desc.Key.Fill

#print axioms VerifiableInference.Desc.Key.Fill.fam_seals
#print axioms VerifiableInference.Desc.Key.Fill.fam_member_of_cand
