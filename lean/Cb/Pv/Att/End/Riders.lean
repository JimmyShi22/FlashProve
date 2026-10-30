-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Att/End/Riders.lean: the further scalars of the first three sumchecks of an attention
sub-proof: which named scalar each is, the linear claims on them, and the verifier's claims that
give these.

Definitions, statements and proofs. Cb/Pv/Att/OwnSteps.lean leaves three linear claims on further
scalars free (LM, LD, LE). This file says what they are meant to be: the hidden value of each
further scalar that one claim ties to a table is the library's rule value of the scalar's name. It
writes the verifier's claims on these scalars as a ledger and shows that the ledger's pull-back
gives the linear claims.

Main names:
  nameM, nameD, nameE: the name (KSc in Inst/Model/Att/KeyForms.lean) of further scalar number j of
    the unit below the diagonal (with the six scalars of the two plane messages in front), of the
    unit on the diagonal, and of the denominator times the output; none where no single claim ties
    the scalar to a table (the two scores; ACC and ZO).
  nameM_lin, nameD_lin, nameE_lin: every name that they give is one that a single claim ties to a
    table (LinK).
  RuleAt name r kk z t m: the linear claim.
  linCl name r kk z: the verifier's claims, in the order of the scalars.
  linCl_rule: the ledger's pull-back gives RuleAt. linCl_in: the other way round.

Limits: which scalar is which follows a reading of the verifier on bytes
(OnBytes/Model/AttentionScores.lean, OnBytes/Model/AttentionDivide.lean); no theorem ties the two.
nameM is meant for two plane messages.


-/
import Cb.Pv.Att.End.Lin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Att.End
open TWhole Cb Cb.Sub Finset Blocks
open Inst.Model.AttSeg

/-- The seven scalars of a unit of the scores, of family u and region r: five planes, the row
maxima, the score. -/
def nameU (u : Fam) (r : Reg) : ℕ → Option KSc
  | 0 => some (.cell u 0)
  | 1 => some (.cell u 1)
  | 2 => some (.cell u 2)
  | 3 => some (.cell u 3)
  | 4 => some (.cell u 4)
  | 5 => some (.ms r)
  | _ => none

/-- The further scalars of the unit below the diagonal: three planes of family m1, three of d1, then
the unit's seven. -/
def nameM (j : ℕ) : Option KSc :=
  if j < 3 then some (.cell .m1 j) else if j < 6 then some (.cell .d1 (j - 3))
  else nameU .m2 .M (j - 6)

/-- The further scalars of the unit on the diagonal. -/
def nameD (j : ℕ) : Option KSc := nameU .d2 .D j

/-- The further scalars of the denominator times the output: ACC, ZO, ZC, RH, RHP, the lT bits of
the index, RH2, RHP2. -/
def nameE (D : Dim) (j : ℕ) : Option KSc :=
  if j < 2 then none else if j = 2 then some .zc else if j = 3 then some .rh
  else if j = 4 then some .rh' else if j < 5 + D.lT then some (.ib (j - 5))
  else if j = 5 + D.lT then some .rg else if j = 5 + D.lT + 1 then some .rg' else none

theorem nameU_lin (D : Dim) {u : Fam} (hu : IsPlane u) (r : Reg) {j : ℕ} {k : KSc}
    (h : nameU u r j = some k) : LinK D k := by
  match j, h with
  | 0, h => cases h; exact ⟨hu, by norm_num⟩
  | 1, h => cases h; exact ⟨hu, by norm_num⟩
  | 2, h => cases h; exact ⟨hu, by norm_num⟩
  | 3, h => cases h; exact ⟨hu, by norm_num⟩
  | 4, h => cases h; exact ⟨hu, by norm_num⟩
  | 5, h => cases h; exact trivial
  | n + 6, h => simp [nameU] at h

theorem nameM_lin (D : Dim) {j : ℕ} {k : KSc} (h : nameM j = some k) : LinK D k := by
  unfold nameM at h
  split at h
  · cases h
    exact ⟨trivial, by omega⟩
  · split at h
    · cases h
      exact ⟨trivial, by omega⟩
    · exact nameU_lin D (u := .m2) trivial _ h

theorem nameD_lin (D : Dim) {j : ℕ} {k : KSc} (h : nameD j = some k) : LinK D k :=
  nameU_lin D (u := .d2) trivial _ h

theorem nameE_lin (D : Dim) {j : ℕ} {k : KSc} (h : nameE D j = some k) : LinK D k := by
  unfold nameE at h
  split_ifs at h <;> first
    | (cases h; done)
    | (cases h; exact trivial)
    | (cases h; show _ < D.lT; omega)

variable {E : Type} [Field E] {J₁ J₂ : Type} [Fintype J₁] [Fintype J₂]
  [DecidableEq J₁] [DecidableEq J₂]

/-- The linear claim on n further scalars r with the mask entries at the places kk: the hidden value
of each named scalar is its rule value at the challenges p on the cells t. -/
def RuleAt (D : Dim) (C : Calls) (name : ℕ → Option KSc) {n : ℕ} (r : Fin n → E) (kk : Fin n → J₁)
    (p : Pub E) (t : Raw → E) (m : J₁ → E) : Prop :=
  ∀ (j : Fin n) (k : KSc), name j.val = some k → r j - m (kk j) = rv D C p t k

variable (cellJ : Raw → J₁) (D : Dim) (C : Calls) (ls lmS : ℕ) (Y : LateLay AttTab J₂)

/-- The verifier's claims on the named ones of n further scalars, in the order of the scalars. -/
def linCl (name : ℕ → Option KSc) {n : ℕ} (r : Fin n → E) (kk : Fin n → J₁) (z : ℕ → E) :
    TWhole.Ledger E (J₁ ⊕ J₂) :=
  (List.finRange n).filterMap fun j =>
    (name j.val).map fun k => linF (r j) (kk j) (rvF D C ls lmS Y z k)

/-- The ledger's pull-back gives the linear claim. -/
theorem linCl_rule (tb : AttTab → TabW E) (p : Pub E) (m : J₁ → E) (hls : ls ≤ D.ln)
    (hl : ∀ u : Fam, IsPlane u → lmS ≤ u.l D) (hT : LinTabs D C ls lmS tb p.z)
    (hG : LinGood D ls lmS Y) (name : ℕ → Option KSc)
    (hn : ∀ j k, name j = some k → LinK D k) {n : ℕ} (r : Fin n → E) (kk : Fin n → J₁)
    (h : ∀ f ∈ linCl (J₁ := J₁) D C ls lmS Y name r kk p.z,
      (pullF (lateA cellJ D ls lmS Y tb) f).Holds m) :
    RuleAt D C name r kk p (rdOf cellJ m) m := by
  intro j k hk
  have hm : linF (r j) (kk j) (rvF D C ls lmS Y p.z k) ∈
      linCl (J₁ := J₁) D C ls lmS Y name r kk p.z :=
    List.mem_filterMap.mpr ⟨j, List.mem_finRange j, by rw [hk]; rfl⟩
  rw [(linF_pull m _ _ _ _).mp (h _ hm)]
  exact rvF_val cellJ D C ls lmS Y tb p m hls hl hT hG k (hn _ _ hk)

/-- And the other way round. -/
theorem linCl_in (tb : AttTab → TabW E) (p : Pub E) (m : J₁ → E) (hls : ls ≤ D.ln)
    (hl : ∀ u : Fam, IsPlane u → lmS ≤ u.l D) (hT : LinTabs D C ls lmS tb p.z)
    (hG : LinGood D ls lmS Y) (name : ℕ → Option KSc)
    (hn : ∀ j k, name j = some k → LinK D k) {n : ℕ} (r : Fin n → E) (kk : Fin n → J₁)
    (h : RuleAt D C name r kk p (rdOf cellJ m) m) :
    ∀ f ∈ linCl (J₁ := J₁) D C ls lmS Y name r kk p.z,
      (pullF (lateA cellJ D ls lmS Y tb) f).Holds m := by
  intro f hf
  obtain ⟨j, -, hj⟩ := List.mem_filterMap.mp hf
  cases hk : name j.val with
  | none =>
    rw [hk] at hj
    cases hj
  | some k =>
    rw [hk] at hj
    obtain rfl : linF (r j) (kk j) (rvF D C ls lmS Y p.z k) = f := Option.some.inj hj
    rw [linF_pull, h j k hk]
    exact (rvF_val cellJ D C ls lmS Y tb p m hls hl hT hG k (hn _ _ hk)).symm

end Cb.Pv.Att.End

#print axioms Cb.Pv.Att.End.linCl_rule
#print axioms Cb.Pv.Att.End.linCl_in
