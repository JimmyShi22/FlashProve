-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/LookupRA.lean: the root test of a lookup argument on arrays that are in a sent vector.

In Blocks/LookupBlock.lean the prover sends the arrays U_π[θ], V_π[θ] of the root test as masked
scalars, in the first round of step 6 (`Lk.bUV`). A protocol that runs many lookup arguments may
instead commit to the arrays of all of them in one vector, sent before the first root test; the
implementation does so (its vector RA). Then the first round of step 6 is a bare challenge ϱ', and
the value forms of the arrays read entries of that vector. All that follows in step 6 (the
coefficients, the sumcheck, the deferred claims) mentions the value forms only, and is taken over
unchanged. Parameters: ru π θ, rv π θ: the forms that read U_π[θ], V_π[θ].
 * `Lk.bUVr`, `hUVr`, `coUVr`, `stUVr`: the round; `clean_bUVr`: the error is that of bUV (a point
   of σ coordinates); nothing is masked, nothing is sent. `Lk.RAh`: the vector holds the honest
   arrays; `c8r`: the relations before the root test; the one for the honest run includes `Lk.RAh`.
 * `Lk.co6r`, `Lk.st6r`, `props_st6r`: step 6 in this form, with `Stage.Props`, under hypotheses
   (among them N_T ≤ 2^σ, and that the pads of its sumcheck's rounds are used once), from c8r to the
   relations c10 after step 6.
 * `st6r_U_sub`: it masks with the pads of the rounds of its sumcheck only.
All theorems of this file on `L` take 2 ≠ 0 in E.
For a protocol that uses this file the arrays are not sent as masked scalars; in this it agrees with
the implementation. Limits: nothing on how the vector is
sent; that is left to the containing protocol.

Modelled on the steps `bUV`, `hUV`, `stUV` of Blocks/LookupBlock.lean, LookupHon.lean,
LookupStage.lean.
"The implementation" in this file's comments is not the released programs: what is said of it need
not hold of them (lean/LIMITS.md, L1).
-/
import Blocks.LookupStage
import Blocks.LookupFacts
import Blocks.LookupData
import Blocks.LookupSim
import Blocks.TameLookup
import Blocks.RngSmall
import Blocks.RngNums
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Blocks.Lk

open Iop Prob
open scoped ENNReal

variable {E Y Pd N : Type} [Field E] [NeZero (2 : E)] [Fintype E] [DecidableEq E]
  [Fintype N] [DecidableEq N] [Fintype Pd] [DecidableEq Pd] (L : Lk E Y Pd N)
  (T : Lk.Vecs E Y) (ru rv : ℕ → ℕ → Form N E)

/-! ## The round -/

def setUVr (x : LkX N E) (ϱ : Fin L.par.σ → E) : LkX N E :=
  { x with
    Uf := ru
    Vf := rv
    pr := nat ϱ }

/-- The verifier sends ϱ' and rejects if a coordinate is 0; the value forms of the arrays read the
sent vector. -/
@[reducible] def bUVr : Block (LkX N E) Y (LkX N E) Y :=
  Block.one (Block.chalRound E (Fin L.par.σ → E))
    (fun x ϱ _ => if nzT ϱ then some (L.setUVr ru rv x ϱ) else none) (fun y _ _ => y)

/-- Soundness of the block bUVr (ϱ'), for arrays that were fixed before, N_T ≤ 2^σ and 2 ≠ 0 in E.
-/
theorem clean_bUVr (hnt : L.par.NT ≤ 2 ^ L.par.σ) :
    (L.bUVr ru rv).Clean (L.R8 T) (L.R9a T) (L.par.σ * Fintype.card E ^ (L.par.σ - 1), ()) := by
  refine Block.clean_one (r := Block.chalRound E (Fin L.par.σ → E))
    (fun x y _ =>
      {ϱ | BadPtFam L.par.σ
        (L.par.dFam x.al (L.Zv x y) (L.Yv x y)
          (fun π θ => L.V y (ru π θ)) (fun π θ => L.V y (rv π θ))) ϱ})
    _ (fun x y m => cnt_badPtFam_le _ _) fun x y m ϱ xo hc hxo hRo => ?_
  by_cases hnz : nzT ϱ = true
  · rw [if_pos hnz] at hxo
    obtain rfl := Option.some.inj hxo
    obtain ⟨hled, hout, hfam⟩ := hRo
    exact ⟨hled,
      L.par.ident_of_dFam hnt (eq_zero_of_not_badPtFam hc (hfam (nat_ne_zero_of_nzT hnz))),
      hout⟩
  · rw [if_neg hnz] at hxo
    exact absurd hxo (by simp)

@[reducible] def hUVr : Hon (L.bUVr ru rv) Pd E (LkA E) (LkA E) :=
  Hon.one (fun _ _ => (fun e => Empty.elim e, fun k => Empty.elim k))
    (fun a ϱ => { a with pr := nat ϱ }) {ϱ | nzT ϱ = false} fun _ => ∅

/-- The sent vector holds the honest arrays. -/
def RAh (x : LkX N E) (y : Y) : Prop :=
  (∀ π < L.par.Pm, ∀ θ < L.par.NT, L.V y (ru π θ) = L.par.hU (L.par.Yt (T.B y) x.al) π θ) ∧
    ∀ π < L.par.Pm, ∀ θ < L.par.NT, L.V y (rv π θ) = L.par.hV (L.par.Yt (T.B y) x.al) π θ

theorem accOn_hUVr (U : Set Pd) :
    (L.hUVr ru rv).AccOn (fun a π x y => L.H8 T U a π x y ∧ L.RAh T ru rv x y) (L.H9 T U) :=
  Hon.accOn_one fun a π x y ϱ hi hb _ => by
    have hnz : nzT ϱ = true := by
      cases h : nzT ϱ
      · exact absurd h hb
      · rfl
    obtain ⟨⟨⟨⟨hl, q1, q2, q3, q4, q5, _, q7⟩, hrest⟩, hdeg⟩, hra⟩ := hi
    exact ⟨_, if_pos hnz, ⟨⟨⟨hl, q1, q2, q3, q4, q5, rfl, q7⟩, hrest⟩, hdeg⟩,
      hra, nat_ne_zero_of_nzT hnz⟩

theorem masked_hUVr : (L.hUVr ru rv).Masked (fun _ => True) ∅ ∅ (simNone _) :=
  Hon.masked_one_const _ _ fun _ _ _ => rfl

def coUVr : Core Pd E L.sX L.sX := ⟨L.bUVr ru rv, L.hUVr ru rv⟩

def stUVr : Stage Pd E L.sX L.sX :=
  ⟨L.coUVr ru rv, (ePt E L.par.σ, ()), ∅, ∅, simNone _, pPt E L.par.σ, 0⟩

/-- the relations before the root test: as c8, and for the honest run the sent vector holds the
honest arrays -/
@[reducible] def c8r : Cut Pd E L.sX :=
  ⟨L.R8 T, fun a π x y => L.H8 T L.allPads a π x y ∧ L.RAh T ru rv x y, fun _ => True⟩

theorem props_stUVr (hnt : L.par.NT ≤ 2 ^ L.par.σ) :
    (L.stUVr ru rv).Props (L.c8r T ru rv) (L.c9a T) where
  clean := L.clean_bUVr T ru rv hnt
  acc := L.accOn_hUVr T ru rv _
  masked := L.masked_hUVr ru rv
  keeps := fun _ _ _ => trivial
  prBad :=
    prRho_head_le (Block.chalRound E (Fin L.par.σ → E)) [] (fun ϱ => nzT ϱ = false) _ (cnt_nzT_le _)
  prWin := fun _ _ => prRho_empty _ fun _ h => h

/-! ## Step 6 in this form -/

def co6r : Core Pd E L.sX L.sX :=
  (L.coUVr ru rv).seq (L.coXi.seq (L.coRs.seq L.coRec))

/-- Step 6 on arrays in a sent vector, as a stage. -/
def st6r : Stage Pd E L.sX L.sX :=
  (L.stUVr ru rv).seq (L.stXi.seq (L.stRs.seq L.stRec))

theorem toCore_st6r : (L.st6r ru rv).toCore = L.co6r ru rv := rfl

theorem st6r_U_sub : (L.st6r ru rv).U ⊆ L.UG (6 ≤ ·) :=
  Set.union_subset (Set.empty_subset _)
    (Set.union_subset (Set.empty_subset _)
      (Set.union_subset (L.grp_sub_UG .rt trivial (by show 6 ≤ 6; omega)) (Set.empty_subset _)))

theorem st6r_D : (L.st6r ru rv).D = (L.st6r ru rv).U := rfl

/-- All properties of step 6 in this form, under hnt and 2 ≠ 0 in E. Of the places of the pads it
asks only that those of the rounds of its sumcheck are used once. -/
theorem props_st6r (hrt : L.scR.PlacesOnceOn (lkVars L.par.σ)) (hnt : L.par.NT ≤ 2 ^ L.par.σ) :
    (L.st6r ru rv).Props (L.c8r T ru rv) (L.c10 T) := by
  have pRs : L.stRs.Props (L.c9b T) (L.c9c T) :=
    Stage.Props.of_empty (S := L.stRs) (L.clean_bRs T)
      ((L.accOn_hRs T) (L.grp_subset (g := .rt) trivial)) (L.masked_hRs hrt) (fun _ _ _ => trivial)
      (L.prR.bad_sc (fun _ => rfl) _ _) fun _ => L.prR.win_sc _ _ _
  have p3 := pRs.seq (L.props_stRec T) (Set.disjoint_empty _) (Set.disjoint_empty _)
  have p2 := (L.props_stXi T).seq p3 (Set.empty_disjoint _) (Set.empty_disjoint _)
  exact (L.props_stUVr T ru rv hnt).seq p2 (Set.empty_disjoint _) (Set.empty_disjoint _)

theorem imp_st6r : ∀ y τ, (L.st6r ru rv).B.imp y τ = y :=
  imp_seq (S₁ := L.coUVr ru rv) (fun _ _ => rfl) <| imp_seq (S₁ := L.coXi) (fun _ _ => rfl) <|
  imp_seq (S₁ := L.coRs) (S₂ := L.coRec) (fun y τ => L.scR.imp_sc _ y τ) (fun _ _ => rfl)

/-- For 2 ≠ 0 in E, `st6r` adds 1 LIN, 3 Pm opened forms and 1 REL (LIN, REL, opened forms:
Blocks/Form.lean) to the honest prover's copy of the list of deferred claims, as step 6 does. -/
theorem adds_st6r : Adds (L.st6r ru rv) (1, 3 * L.par.Pm, 1) := fun a ρ => by
  have h := (Adds.seq (S₁ := L.stUVr ru rv) (d₁ := (0, 0, 0)) (fun _ _ => rfl) <|
      Adds.seq (S₁ := L.stXi) (d₁ := (0, 0, 0)) (fun _ _ => rfl) <|
      Adds.seq L.adds_stRs L.adds_stRec)
    a ρ
  refine h.trans ?_
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> first | (dsimp only; done) | (dsimp only; omega)

private theorem of_ite'' {α : Type} {c : Bool} {a xo : α}
    (h : (if c then some a else none) = some xo) : xo = a := by
  cases c
  · exact absurd h (by simp)
  · exact (Option.some.inj h).symm

theorem keeps_st6r : (L.st6r ru rv).B.Keeps k8 k8 :=
  Block.Keeps.seq (B₁ := L.bUVr ru rv) (f₂ := k8) (fun _ _ _ _ h => by rw [of_ite'' h]; rfl) <|
  Block.Keeps.seq (B₁ := L.bXi) (f₂ := k8) (fun _ _ _ _ h => by rw [← Option.some.inj h]) <|
  Block.Keeps.seq (B₁ := L.bRs) (B₂ := L.bRec) (f₂ := k8) (fun _ _ _ _ h => by
      obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp h
      rfl) fun _ _ _ _ h => by rw [of_ite'' h]

/-- For 2 ≠ 0 in E: without rejection, `st6r` keeps α, z, C_end, the forms and end points of the
leaf layer and of the bit layer (v4, p4, v5, p5), and ϱ6. -/
theorem pub_st6r {x xo : LkX N E} {ρ : Rho (L.st6r ru rv).B.shape}
    {p : Plains (L.st6r ru rv).B.shape} (h : (L.st6r ru rv).B.pub x ρ p = some xo) :
    xo.al = x.al ∧ xo.z = x.z ∧ xo.Cend = x.Cend ∧ xo.v4 = x.v4 ∧ xo.p4 = x.p4 ∧ xo.v5 = x.v5 ∧
    xo.p5 = x.p5 ∧ xo.p6 = x.p6 := by
  have hk := L.keeps_st6r ru rv x ρ p xo h
  simp only [Prod.mk.injEq] at hk
  exact hk

/-! ## Numbers: those of step 6 -/

theorem pBad_st6r : (L.st6r ru rv).pBad = L.st6.pBad := rfl
theorem pWin_st6r : (L.st6r ru rv).pWin = L.st6.pWin := rfl
theorem rounds_st6r : (L.st6r ru rv).rounds = L.st6.rounds := rfl
/-- For 2 ≠ 0 in E, step 6 has σ + 2 rounds. -/
theorem rounds_st6 : L.st6.rounds = L.par.σ + 2 := by
  have hR : L.stRs.rounds = L.par.σ := (SC.length_shape_sc L.scR _).trans (by simp [lkVars])
  unfold st6
  simp only [Stage.rounds_seq]
  rw [hR]
  show 1 + (1 + (L.par.σ + 0)) = _
  omega
theorem small_st6r {D : ℕ} (h : Small D L.st6.ε) : Small D (L.st6r ru rv).ε := h

/-! ## No vector is sent -/

section Track

variable (F : Type) [Field F] [Algebra F E]

def enc6r : EncData F E (L.co6r ru rv).B.shape :=
  EncData.app (s := (L.coUVr ru rv).B.shape) (REnc.none E F Empty (Fin L.par.σ → E), PUnit.unit) <|
  EncData.app (s := L.coXi.B.shape) (REnc.none E F Empty (Fin (2 * L.par.Pm) → E), PUnit.unit) <|
  EncData.app (s := L.coRs.B.shape)
    (t := L.coRec.B.shape) (SC.encSc L.scR F (lkVars L.par.σ)) PUnit.unit

def tk6r (ra : Reads F E L.sX) :
    (L.co6r ru rv).Track ra (Stage.readsX (LkX N E) (LkA E) ra) :=
  trackSame (L.co6r ru rv) (L.enc6r ru rv F) ra

theorem track6r_ok (ra : Reads F E L.sX) : (L.tk6r ru rv F ra).OK :=
  trackSame_ok _ _ _ (L.imp_st6r ru rv)

variable {F} {Q : Code.Enc F → ℕ → ℕ → Role → ℕ → Prop}

theorem all_track6r (ra : Reads F E L.sX) : (L.tk6r ru rv F ra).All Q :=
  EncData.All.app (s := (L.coUVr ru rv).B.shape)
      (d := (REnc.none E F Empty (Fin L.par.σ → E), PUnit.unit))
      ⟨fun e : Empty => e.elim, trivial⟩ <|
  EncData.All.app (s := L.coXi.B.shape)
      (d := (REnc.none E F Empty (Fin (2 * L.par.Pm) → E), PUnit.unit))
      ⟨fun e : Empty => e.elim, trivial⟩ <|
  EncData.All.app (s := L.coRs.B.shape)
    (t := L.coRec.B.shape) (d' := PUnit.unit) (SC.all_encSc L.scR _) trivial

end Track

/-! ## Data, simulator, tameness -/

section Data

variable (F : Type) [Field F] [Algebra F E] [FinEnum E]

def num6r : SNum (L.co6r ru rv).B.shape (L.enc6r ru rv F) :=
  SNum.app (s := (L.coUVr ru rv).B.shape) (d := (REnc.none E F Empty (Fin L.par.σ → E), PUnit.unit))
      (RNum.none F Empty (Fin L.par.σ → E), ()) <|
  SNum.app (s := L.coXi.B.shape) (d := (REnc.none E F Empty (Fin (2 * L.par.Pm) → E), PUnit.unit))
      (RNum.none F Empty (Fin (2 * L.par.Pm) → E), ()) <|
  SNum.app (s := L.coRs.B.shape) (t := L.coRec.B.shape) (d := SC.encSc L.scR F (lkVars L.par.σ))
    (d' := PUnit.unit) (SC.numSc L.scR (lkVars L.par.σ)) ()

def decUVr : (L.hUVr ru rv).Dec :=
  Hon.Dec.one _ _ _ _ (fun ϱ => inferInstanceAs (Decidable (nzT ϱ = false))) fun _ _ =>
    isFalse fun h => h

def dec6r : (L.co6r ru rv).H.Dec :=
  Hon.Dec.seq (H₁ := L.hUVr ru rv) (L.decUVr ru rv) <|
  Hon.Dec.seq (H₁ := L.hXi) L.decXi <|
  Hon.Dec.seq (H₁ := L.hRs) (H₂ := L.hRec) L.decRs L.decRec

def data6r (ra : Reads F E L.sX) : (L.co6r ru rv).Data (L.tk6r ru rv F ra) :=
  ⟨L.num6r ru rv F, L.dec6r ru rv⟩

end Data

def csUVr : CS Pd E L.sX L.sX := ⟨L.coUVr ru rv, simNone _⟩
def cs6r : CS Pd E L.sX L.sX := (L.csUVr ru rv).seq (L.csXi.seq (L.csRs.seq L.csRec))

theorem toCore_cs6r : (L.cs6r ru rv).toCore = L.co6r ru rv := rfl
theorem toCS_st6r : (L.st6r ru rv).toCS = L.cs6r ru rv := rfl

theorem tame_coUVr (n : ℕ × ℕ × ℕ) : (L.coUVr ru rv).Tame (IO n) (IO n) :=
  show (L.bUVr ru rv).Tame (L.hUVr ru rv).Bad _ _ from
    Block.Tame.oneIf (r := Block.chalRound E (Fin L.par.σ → E)) (fun ϱ => nzT ϱ)
      (fun x ϱ _ => L.setUVr ru rv x ϱ) _ fun _ _ _ h => h

theorem tame_co6r (n : ℕ × ℕ × ℕ) :
    (L.co6r ru rv).Tame (IO n) (IO (n.1 + 1, n.2.1 + 3 * L.par.Pm, n.2.2 + 1)) :=
  Core.Tame.seq (L.tame_coUVr ru rv n)
    (Core.Tame.seq (L.tame_coXi n) (Core.Tame.seq (L.tame_coRs n) (L.tame_coRec n)))

end Blocks.Lk
