-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/LateNames.lean: names, late entries and forms at which the library's three records
NormsOk, TermsOk and GatedOk (Cb/Pv/Lay/End/LayHEnd.lean, LayAll.lean) hold, but for their clauses
on sizes.

The theorem on the end of the chain of a layers' sub-proof's own rounds (lay_last_all) has free
letters: a type Nm of names, a finite type J₂ of late entries, which late entry has which name (Y),
how the names of the three shares lie in Nm (ιN, ιT, ιG), and a form for each name (fm). The three
records ask that the form of each name in range is what the late entry is meant to be, and that the
names in range are names of late entries.
LayAllMeet.lean keeps the three records as premises. Here they are filled.

Main names:
  `Nm3`: the three shares' names, side by side. `J3 N`: a kind and three numbers up to N.
  `lateOf N`: which late entry has which name; good: the name's numbers are at most N.
  `fmOf`: the form of each name: what the late entry is meant to be (normsFm, termsFm, gatedFm).
  `roomFor`: a number N that has room for all names in range.
  `normsOk_of`, `termsOk_of`, `gatedOk_of`: the three records, from their clauses on sizes alone.
Limits. A filling of letters: the forms are the library's own by definition, so the clauses hfm hold
by definition. The clauses on sizes stay premises. Nothing on a program's reads, on a run, on
soundness or on hiding.


-/
import Cb.Pv.Lay.End.LayAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open TWhole Cb Cb.Sub Cb.Pv.Lay Cb.Pv.Lay.At Cb.Pv.Lay.End Cb.Pv.Lay.End.Gated
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim lDd lF lFe)

/-- The names of the three shares, side by side. -/
abbrev Nm3 : Type := NormsNm ⊕ (TermsNm ⊕ GatedNm)

/-- The late entries: one of eleven kinds and three numbers up to N. -/
abbrev J3 (N : ℕ) : Type := Fin 11 × Fin (N + 1) × Fin (N + 1) × Fin (N + 1)

/-- A number as a number up to N; 0 if it is greater. -/
def clamp (N n : ℕ) : Fin (N + 1) := if h : n < N + 1 then ⟨n, h⟩ else 0

theorem clamp_val {N n : ℕ} (h : n ≤ N) : ((clamp N n : Fin (N + 1)) : ℕ) = n := by
  unfold clamp
  rw [dif_pos (Nat.lt_succ_of_le h)]

/-- The name of a late entry. -/
def nmOf (N : ℕ) (j : J3 N) : Nm3 :=
  match j.1.val with
  | 0 => .inl (.xi j.2.1 j.2.2.1 j.2.2.2)
  | 1 => .inl (.atP j.2.1 j.2.2.1)
  | 2 => .inl (.atR j.2.1 j.2.2.1)
  | 3 => .inl (.sel j.2.1 j.2.2.1)
  | 4 => .inr (.inl (.row j.2.1 j.2.2.1))
  | 5 => .inr (.inl (.sc j.2.1 j.2.2.1))
  | 6 => .inr (.inl (.sel j.2.1 j.2.2.1 j.2.2.2))
  | 7 => .inr (.inr (.s5 j.2.1 j.2.2.1 j.2.2.2))
  | 8 => .inr (.inr (.u5 j.2.1 j.2.2.1 j.2.2.2))
  | 9 => .inr (.inr (.s6 j.2.1 j.2.2.1 j.2.2.2))
  | _ => .inr (.inr (.u6 j.2.1 j.2.2.1 j.2.2.2))

/-- The late entry of a name. -/
def atOf (N : ℕ) : Nm3 → J3 N
  | .inl (.xi a b c) => (0, clamp N a, clamp N b, clamp N c)
  | .inl (.atP a b) => (1, clamp N a, clamp N b, 0)
  | .inl (.atR a b) => (2, clamp N a, clamp N b, 0)
  | .inl (.sel a b) => (3, clamp N a, clamp N b, 0)
  | .inr (.inl (.row a b)) => (4, clamp N a, clamp N b, 0)
  | .inr (.inl (.sc a b)) => (5, clamp N a, clamp N b, 0)
  | .inr (.inl (.sel a b c)) => (6, clamp N a, clamp N b, clamp N c)
  | .inr (.inr (.s5 a b c)) => (7, clamp N a, clamp N b, clamp N c)
  | .inr (.inr (.u5 a b c)) => (8, clamp N a, clamp N b, clamp N c)
  | .inr (.inr (.s6 a b c)) => (9, clamp N a, clamp N b, clamp N c)
  | .inr (.inr (.u6 a b c)) => (10, clamp N a, clamp N b, clamp N c)

/-- The name's numbers are at most N. -/
def goodOf (N : ℕ) : Nm3 → Prop
  | .inl (.xi a b c) => a ≤ N ∧ b ≤ N ∧ c ≤ N
  | .inl (.atP a b) => a ≤ N ∧ b ≤ N
  | .inl (.atR a b) => a ≤ N ∧ b ≤ N
  | .inl (.sel a b) => a ≤ N ∧ b ≤ N
  | .inr (.inl (.row a b)) => a ≤ N ∧ b ≤ N
  | .inr (.inl (.sc a b)) => a ≤ N ∧ b ≤ N
  | .inr (.inl (.sel a b c)) => a ≤ N ∧ b ≤ N ∧ c ≤ N
  | .inr (.inr (.s5 a b c)) => a ≤ N ∧ b ≤ N ∧ c ≤ N
  | .inr (.inr (.u5 a b c)) => a ≤ N ∧ b ≤ N ∧ c ≤ N
  | .inr (.inr (.s6 a b c)) => a ≤ N ∧ b ≤ N ∧ c ≤ N
  | .inr (.inr (.u6 a b c)) => a ≤ N ∧ b ≤ N ∧ c ≤ N

theorem nm_at (N : ℕ) : ∀ x : Nm3, goodOf N x → nmOf N (atOf N x) = x
  | .inl (.xi a b c), h => by
    show Sum.inl (NormsNm.xi (clamp N a).val (clamp N b).val (clamp N c).val) = _
    rw [clamp_val h.1, clamp_val h.2.1, clamp_val h.2.2]
  | .inl (.atP a b), h => by
    show Sum.inl (NormsNm.atP (clamp N a).val (clamp N b).val) = _
    rw [clamp_val h.1, clamp_val h.2]
  | .inl (.atR a b), h => by
    show Sum.inl (NormsNm.atR (clamp N a).val (clamp N b).val) = _
    rw [clamp_val h.1, clamp_val h.2]
  | .inl (.sel a b), h => by
    show Sum.inl (NormsNm.sel (clamp N a).val (clamp N b).val) = _
    rw [clamp_val h.1, clamp_val h.2]
  | .inr (.inl (.row a b)), h => by
    show Sum.inr (Sum.inl (TermsNm.row (clamp N a).val (clamp N b).val)) = _
    rw [clamp_val h.1, clamp_val h.2]
  | .inr (.inl (.sc a b)), h => by
    show Sum.inr (Sum.inl (TermsNm.sc (clamp N a).val (clamp N b).val)) = _
    rw [clamp_val h.1, clamp_val h.2]
  | .inr (.inl (.sel a b c)), h => by
    show Sum.inr (Sum.inl (TermsNm.sel (clamp N a).val (clamp N b).val (clamp N c).val)) = _
    rw [clamp_val h.1, clamp_val h.2.1, clamp_val h.2.2]
  | .inr (.inr (.s5 a b c)), h => by
    show Sum.inr (Sum.inr (GatedNm.s5 (clamp N a).val (clamp N b).val (clamp N c).val)) = _
    rw [clamp_val h.1, clamp_val h.2.1, clamp_val h.2.2]
  | .inr (.inr (.u5 a b c)), h => by
    show Sum.inr (Sum.inr (GatedNm.u5 (clamp N a).val (clamp N b).val (clamp N c).val)) = _
    rw [clamp_val h.1, clamp_val h.2.1, clamp_val h.2.2]
  | .inr (.inr (.s6 a b c)), h => by
    show Sum.inr (Sum.inr (GatedNm.s6 (clamp N a).val (clamp N b).val (clamp N c).val)) = _
    rw [clamp_val h.1, clamp_val h.2.1, clamp_val h.2.2]
  | .inr (.inr (.u6 a b c)), h => by
    show Sum.inr (Sum.inr (GatedNm.u6 (clamp N a).val (clamp N b).val (clamp N c).val)) = _
    rw [clamp_val h.1, clamp_val h.2.1, clamp_val h.2.2]

/-- Which late entry has which name. -/
def lateOf (N : ℕ) : LateLay Nm3 (J3 N) where
  nm := nmOf N
  at' := atOf N
  good := goodOf N
  ok := nm_at N

/-- A number with room for all names in range. B: the blocks of the stream; sG: the bits of a
feature in its block. -/
def roomFor (D : Dim) (B sG : ℕ) : ℕ :=
  D.nNu + B + D.ne + D.nx + 2 ^ D.lL + 2 * 2 ^ (D.lL - 1) + 2 ^ (lF D - sG) +
    2 * 2 ^ (lFe D - sG) + 99

/-- Each bound of a name in range is at most roomFor. -/
theorem room_bounds (D : Dim) (B sG : ℕ) :
    D.nNu ≤ roomFor D B sG ∧ 99 ≤ roomFor D B sG ∧ B ≤ roomFor D B sG ∧ D.ne ≤ roomFor D B sG ∧
      D.nx ≤ roomFor D B sG ∧ 2 ^ D.lL ≤ roomFor D B sG ∧ 2 * 2 ^ (D.lL - 1) ≤ roomFor D B sG ∧
      2 ^ (lF D - sG) ≤ roomFor D B sG ∧ 2 * 2 ^ (lFe D - sG) ≤ roomFor D B sG := by
  unfold roomFor
  generalize 2 ^ D.lL = p1
  generalize 2 ^ (D.lL - 1) = p2
  generalize 2 ^ (lF D - sG) = p3
  generalize 2 ^ (lFe D - sG) = p4
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

variable {E : Type} [Field E] [Fintype E] [scl : Scl] {M X : Type} (P : FullPar E M X)

/-- The form of each name: what the late entry is meant to be. -/
noncomputable def fmOf (zt : (tailF P).s7.Nx → ℕ → E) (b s sG : ℕ) (e : (tailF P).s7.Nx) :
    Nm3 → TWhole.Aff E P.J
  | .inl x => toAff (normsFm P.rd P.D (eAt P.toOwnPar P.wPart e (zt e)) (P.D.lL + 1) b s x)
  | .inr (.inl x) => toAff (termsFm P.rd P.D (termsEAt P.tp ((tailF P).b3 e).2).rt x)
  | .inr (.inr x) => toAff (gatedFm P.rd P.D
      (gatedEAt P.fp ((tailF P).b5 e).2 ((tailF P).b6 e).2) sG x)

variable (zt : (tailF P).s7.Nx → ℕ → E) (b s B sG : ℕ)

/-- NormsOk, from its three clauses on sizes. -/
theorem normsOk_of (hl : lDd P.D = b + s) (hd : P.D.d = B * 2 ^ s) (hB : B ≤ 2 ^ b) :
    NormsOk P.toOwnPar P.wPart (lateOf (roomFor P.D B sG)) Sum.inl (fmOf P zt b s sG) zt b s B where
  hl := hl
  hd := hd
  hB := hB
  hfm := fun _ _ _ => rfl
  gXi := fun ν l kh h1 h2 h3 => by
    show ν ≤ _ ∧ l ≤ _ ∧ kh ≤ _
    obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9⟩ := room_bounds P.D B sG
    refine ⟨?_, ?_, ?_⟩ <;> omega
  gP := fun ν n h1 h2 => by
    show ν ≤ _ ∧ n ≤ _
    obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9⟩ := room_bounds P.D B sG
    refine ⟨?_, ?_⟩ <;> omega
  gR := fun ν n h1 h2 => by
    show ν ≤ _ ∧ n ≤ _
    obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9⟩ := room_bounds P.D B sG
    refine ⟨?_, ?_⟩ <;> omega
  gS := fun l x h1 h2 => by
    show l ≤ _ ∧ x ≤ _
    obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9⟩ := room_bounds P.D B sG
    refine ⟨?_, ?_⟩ <;> omega

/-- TermsOk: no premise. -/
theorem termsOk_of :
    TermsOk P (lateOf (roomFor P.D B sG)) (fun x => Sum.inr (Sum.inl x)) (fmOf P zt b s sG) where
  hfm := fun _ _ _ => rfl
  gR := fun ν n h1 h2 => by
    show ν ≤ _ ∧ n ≤ _
    obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9⟩ := room_bounds P.D B sG
    refine ⟨?_, ?_⟩ <;> omega
  gC := fun l k h1 h2 => by
    show l ≤ _ ∧ k ≤ _
    obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9⟩ := room_bounds P.D B sG
    refine ⟨?_, ?_⟩ <;> omega
  gS := fun l x k h1 h2 h3 => by
    show l ≤ _ ∧ x ≤ _ ∧ k ≤ _
    obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9⟩ := room_bounds P.D B sG
    refine ⟨?_, ?_, ?_⟩ <;> omega

/-- GatedOk, from its four clauses on sizes. -/
theorem gatedOk_of (h1 : 1 ≤ P.D.lL) (hs1 : sG ≤ lF P.D) (hs2 : sG ≤ lFe P.D)
    (hfe : P.D.fe = 2 ^ lFe P.D) :
    GatedOk P (lateOf (roomFor P.D B sG)) (fun x => Sum.inr (Sum.inr x)) (fmOf P zt b s sG) sG where
  h1 := h1
  hs1 := hs1
  hs2 := hs2
  hfe := hfe
  hfm := fun _ _ _ => rfl
  hY :=
    { s5 := fun l hl i hi c hc => by
        show l ≤ _ ∧ i ≤ _ ∧ c ≤ _
        obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9⟩ := room_bounds P.D B sG
        refine ⟨?_, ?_, ?_⟩ <;> omega
      u5 := fun l hl i hi c hc => by
        show l ≤ _ ∧ i ≤ _ ∧ c ≤ _
        obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9⟩ := room_bounds P.D B sG
        refine ⟨?_, ?_, ?_⟩ <;> omega
      s6 := fun l hl i hi c hc => by
        show l ≤ _ ∧ 2 * i + 1 ≤ _ ∧ 2 ^ (lFe P.D - sG) + c ≤ _
        obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9⟩ := room_bounds P.D B sG
        refine ⟨?_, ?_, ?_⟩ <;> omega
      u6 := fun l hl i hi c hc => by
        show l ≤ _ ∧ 2 * i + 1 ≤ _ ∧ 2 ^ (lFe P.D - sG) + c ≤ _
        obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9⟩ := room_bounds P.D B sG
        refine ⟨?_, ?_, ?_⟩ <;> omega }

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.normsOk_of
#print axioms OnBytes.Road.K4.termsOk_of
#print axioms OnBytes.Road.K4.gatedOk_of
