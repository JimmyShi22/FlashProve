-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeySmpWalk.lean: THEOREMS. **THE TWO-BORDER FORM: ON ONE HISTORY OF Key.descriptionFromSource, WHAT IS SEALED AT A BORDER IS SEALED AT EVERY LATER BORDER, AND ACROSS THE SEAM FROM CHAIN 1's END INTO CHAIN 3.** A record that is reached at border m + j has, ON ITS OWN HISTORY, a record
reached at border m, with the same handed part, and from that one's statement to its own K1.SmpStay holds: so SeedIs | Sealed (Johnson/Desc/K1/Law/SealStays.lean) are carried.
OBJECT. LPFD.Hist₁ | Hist₂ | Hist₃ (Key.descriptionFromSource X N P) D (Reached, Johnson/Top/Fire/Code/Reached.lean · RowsWoven.lean) · LPFD.Walked (ReachedWalk.lean). USER. The tables' files' member at a border behind the sending's (the premise hrec of member_fk_rec₁, Johnson/RunOne/KeyFillRecord.lean: SeedIs … a.2.d.st o ρ y). LETTERS. X · N · P · D; m · j · k;
x · x0 · a.
  walked_rel           along a walk of blocks that each keep R (reflexive, transitive): R from its start to its end. General: it names no kind
  reached_back         walked_of_reached WITH THE WALK's START NAMED AND REACHED: Reached … (m + j) x → ∃ x0, Reached … m x0 ∧ x0.1 = x.1 ∧ Walked (l.drop m) x0.2 j x.2
  hist₁_smp | ₂ | ₃    **planOk → Hist (m + j) x → ∃ x0, Hist m x0 ∧ x0.1 = x.1 ∧ SmpStay (the statement at x0) (the statement at x)**
  seedIs_later₁ | sealed_later₁   **THE CALL: … ∧ ∀ cs s o ρ y, SeedIs cs s x0.2.d.st o ρ y → SeedIs cs s x.2.d.st o ρ y**; the like for Sealed
  hist₃_from₁          **ACROSS THE SEAM: planOk → Hist₃ k a → SmpStay (chain 1's end's statement, as handed) (the statement at a)**
  hist₃_from_border₁   so from every border m + j = first.blocksInOrder.length of chain 1 · seedIs_into₃: SeedIs carried from there into chain 3
What is not claimed. From chain 2 into chain 3 (Omega comes by a copy: a new message). That SeedIs HOLDS at border m: the sending's law's. The WORD that a reader of the oracles returns: Sealed's f is an argument. Nothing on soundness.

-/
import Johnson.RunOne.KeySmpStay
import Johnson.Top.Fire.Code.ReachedWalk
import Johnson.Desc.K1.Law.SealStays

set_option autoImplicit false

namespace Johnson.RunOne.KeySmp

open OnBytes OnBytes.Params VerifiableInference.Desc.Key Johnson.RunOne.KeyKeeps
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Ground (By)
open VerifiableInference.Desc.Keeps (Decides)
open VerifiableInference.Desc.Sound (held)
open VerifiableInference.Desc.Plain (held_decide)
open VerifiableInference.Desc.Third (S₃)
open VerifiableInference.Desc.K1 (SmpStay SeedIs Sealed)
open LPFD (Reached Walked Hist₁ Hist₂ Hist₃)

section General
variable {Q S Cl : Type}

/-- **Along a walk of blocks that each keep R.** -/
theorem walked_rel (R : S → S → Prop) (hr : ∀ a, R a a) (ht : ∀ a b c, R a b → R b c → R a c) (bs : List (Block S Cl)) (hb : ∀ b ∈ bs, Decides R b) (d0 : S) :
    ∀ (k : ℕ) (a : S), Walked bs d0 k a → R d0 a
  | 0, a, h => by
    have e : a = d0 := h
    rw [e]
    exact hr d0
  | k + 1, a, h => by
    obtain ⟨a', b, rs, gs, hw, hk, hd⟩ := h
    exact ht _ _ _ (walked_rel R hr ht bs hb d0 k a' hw) (hb b (List.mem_of_getElem? hk) a' rs gs a hd)

/-- **The last j steps of a history, from a record that was itself reached, with the same handed part.** -/
theorem reached_back (ft : ℕ) (l : List (Block S Cl)) (st₀ : Q × S → Prop) (m : ℕ) :
    ∀ (j : ℕ) (x : Q × S), Reached ft (l.map held) st₀ (m + j) x → ∃ x0 : Q × S, Reached ft (l.map held) st₀ m x0 ∧ x0.1 = x.1 ∧ Walked (l.drop m) x0.2 j x.2
  | 0, x, h => ⟨x, h, rfl, rfl⟩
  | j + 1, x, h => by
    obtain ⟨a', b, rs, cols, hr, hb, hd, _⟩ := Reached.last (k := m + j) h
    rw [List.getElem?_map] at hb
    obtain ⟨b₀, hb₀, rfl⟩ := Option.map_eq_some_iff.1 hb
    obtain ⟨x0, h0, e0, hw⟩ := reached_back ft l st₀ m j a' hr
    have hh := held_decide b₀ a' _ _ x hd
    exact ⟨x0, h0, e0.trans hh.1.symm, a'.2, b₀, _, _, hw, by rw [List.getElem?_drop]; exact hb₀, hh.2⟩

end General

variable {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces}

theorem smp_refl {S : Type} (st : S → Statement) : ∀ a, By SmpStay st a a := fun _ => SmpStay.refl _
theorem smp_trans {S : Type} (st : S → Statement) : ∀ a b c, By SmpStay st a b → By SmpStay st b c → By SmpStay st a c := fun _ _ _ h k => SmpStay.trans h k

/-- **Chain 1: from border m to border m + j on one history.** -/
theorem hist₁_smp (hp : (descriptionFromSource X N P).planOk = true) (D : OnBytes.Maker.WholeD) (m j : ℕ) (x : (descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁) (h : Hist₁ (descriptionFromSource X N P) D (m + j) x) :
    ∃ x0 : (descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁, Hist₁ (descriptionFromSource X N P) D m x0 ∧ x0.1 = x.1 ∧ SmpStay (st₁ (show FirstState from x0.2)) (st₁ (show FirstState from x.2)) := by
  obtain ⟨x0, h0, e0, hw⟩ := reached_back _ (descriptionFromSource X N P).first.blocksInOrder _ m j x h
  exact ⟨x0, h0, e0, walked_rel (By SmpStay (st₁ (β := LookupRecord))) (smp_refl _) (smp_trans _) _ (fun b hb => flat_smpStay₁ hp b (List.mem_of_mem_drop hb)) _ j _ hw⟩

theorem hist₂_smp (hp : (descriptionFromSource X N P).planOk = true) (D : OnBytes.Maker.WholeD) (m j : ℕ) (x : ((descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁) × (descriptionFromSource X N P).S₂) (h : Hist₂ (descriptionFromSource X N P) D (m + j) x) :
    ∃ x0 : ((descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁) × (descriptionFromSource X N P).S₂, Hist₂ (descriptionFromSource X N P) D m x0 ∧ x0.1 = x.1 ∧ SmpStay (st₂ (show _root_.Desc.K14.St from x0.2)) (st₂ (show _root_.Desc.K14.St from x.2)) := by
  obtain ⟨x0, h0, e0, hw⟩ := reached_back _ (descriptionFromSource X N P).shared.blocksInOrder _ m j x h
  exact ⟨x0, h0, e0, walked_rel (By SmpStay st₂) (smp_refl _) (smp_trans _) _ (fun b hb => flat_smpStay₂ hp b (List.mem_of_mem_drop hb)) _ j _ hw⟩

theorem hist₃_smp (hp : (descriptionFromSource X N P).planOk = true) (D : OnBytes.Maker.WholeD) (m j : ℕ) (x : ((descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁ × (descriptionFromSource X N P).S₂) × (descriptionFromSource X N P).S₃) (h : Hist₃ (descriptionFromSource X N P) D (m + j) x) :
    ∃ x0 : ((descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁ × (descriptionFromSource X N P).S₂) × (descriptionFromSource X N P).S₃, Hist₃ (descriptionFromSource X N P) D m x0 ∧ x0.1 = x.1 ∧ SmpStay (st₃ (show S₃ from x0.2)) (st₃ (show S₃ from x.2)) := by
  obtain ⟨x0, h0, e0, hw⟩ := reached_back _ (descriptionFromSource X N P).second.blocksInOrder _ m j x h
  exact ⟨x0, h0, e0, walked_rel (By SmpStay st₃) (smp_refl _) (smp_trans _) _ (fun b hb => flat_smpStay₃ hp b (List.mem_of_mem_drop hb)) _ j _ hw⟩

/-- **The call: the sending kind's row at border m stands at border m + j.** -/
theorem seedIs_later₁ (hp : (descriptionFromSource X N P).planOk = true) (D : OnBytes.Maker.WholeD) (m j : ℕ) (x : (descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁) (h : Hist₁ (descriptionFromSource X N P) D (m + j) x) :
    ∃ x0 : (descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁, Hist₁ (descriptionFromSource X N P) D m x0 ∧ x0.1 = x.1 ∧
      ∀ cs s o ρ y, SeedIs cs s (show FirstState from x0.2).d.st o ρ y → SeedIs cs s (show FirstState from x.2).d.st o ρ y := by
  obtain ⟨x0, h0, e0, hs⟩ := hist₁_smp hp D m j x h
  exact ⟨x0, h0, e0, fun _ _ _ _ _ k => k.stays hs⟩

theorem sealed_later₁ (hp : (descriptionFromSource X N P).planOk = true) (D : OnBytes.Maker.WholeD) (m j : ℕ) (x : (descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁) (h : Hist₁ (descriptionFromSource X N P) D (m + j) x) :
    ∃ x0 : (descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁, Hist₁ (descriptionFromSource X N P) D m x0 ∧ x0.1 = x.1 ∧
      ∀ cs s e f o, Sealed cs s e f (show FirstState from x0.2).d.st o → Sealed cs s e f (show FirstState from x.2).d.st o := by
  obtain ⟨x0, h0, e0, hs⟩ := hist₁_smp hp D m j x h
  exact ⟨x0, h0, e0, fun _ _ _ _ _ k => k.stays hs⟩

/-- **Across the seam: from chain 1's end, as handed, to every record that chain 3 reaches.** -/
theorem hist₃_from₁ (hp : (descriptionFromSource X N P).planOk = true) (D : OnBytes.Maker.WholeD) (k : ℕ) (a : ((descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁ × (descriptionFromSource X N P).S₂) × (descriptionFromSource X N P).S₃) (h : Hist₃ (descriptionFromSource X N P) D k a) :
    SmpStay (st₁ (show FirstState from a.1.2.1)) (st₃ (show S₃ from a.2)) := by
  obtain ⟨x0, h0, e0, hs⟩ := hist₃_smp hp D 0 k a (by rw [Nat.zero_add]; exact h)
  have e : ((descriptionFromSource X N P).start₃ x0.1.1 x0.1.2.1 x0.1.2.2).toOption = some x0.2 := (show LPFD.st₃ (descriptionFromSource X N P) D x0 from h0).2
  cases hq : (descriptionFromSource X N P).start₃ x0.1.1 x0.1.2.1 x0.1.2.2 with
  | error w => rw [hq] at e; cases e
  | ok s =>
    rw [hq] at e
    have e' : s = x0.2 := Option.some.inj e
    rw [e'] at hq
    rw [← e0]
    exact (start₃_smp hq).trans hs

/-- **From a border of chain 1 into chain 3.** -/
theorem hist₃_from_border₁ (hp : (descriptionFromSource X N P).planOk = true) (D : OnBytes.Maker.WholeD) (m j : ℕ) (hm : m + j = (descriptionFromSource X N P).first.blocksInOrder.length) (k : ℕ)
    (a : ((descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁ × (descriptionFromSource X N P).S₂) × (descriptionFromSource X N P).S₃) (h : Hist₃ (descriptionFromSource X N P) D k a) :
    ∃ x0 : (descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁, Hist₁ (descriptionFromSource X N P) D m x0 ∧ x0.1 = a.1.1 ∧ SmpStay (st₁ (show FirstState from x0.2)) (st₃ (show S₃ from a.2)) := by
  have h1 := LPFD.hist₂_handed (descriptionFromSource X N P) D _ _ (LPFD.hist₃_handed (descriptionFromSource X N P) D k a h)
  obtain ⟨x0, h0, e0, hs⟩ := hist₁_smp hp D m j (a.1.1, a.1.2.1) (by rw [hm]; exact h1)
  exact ⟨x0, h0, e0, hs.trans (hist₃_from₁ hp D k a h)⟩

theorem seedIs_into₃ (hp : (descriptionFromSource X N P).planOk = true) (D : OnBytes.Maker.WholeD) (m j : ℕ) (hm : m + j = (descriptionFromSource X N P).first.blocksInOrder.length) (k : ℕ)
    (a : ((descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁ × (descriptionFromSource X N P).S₂) × (descriptionFromSource X N P).S₃) (h : Hist₃ (descriptionFromSource X N P) D k a) :
    ∃ x0 : (descriptionFromSource X N P).XiPub × (descriptionFromSource X N P).S₁, Hist₁ (descriptionFromSource X N P) D m x0 ∧ x0.1 = a.1.1 ∧
      ∀ cs s o ρ y, SeedIs cs s (show FirstState from x0.2).d.st o ρ y → SeedIs cs s (show S₃ from a.2).st o ρ y := by
  obtain ⟨x0, h0, e0, hs⟩ := hist₃_from_border₁ hp D m j hm k a h
  exact ⟨x0, h0, e0, fun _ _ _ _ _ q => q.stays hs⟩

end Johnson.RunOne.KeySmp
