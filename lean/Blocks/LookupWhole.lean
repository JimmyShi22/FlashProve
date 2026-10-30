-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/LookupWhole.lean: the whole lookup argument with a rider, as one stage.

A segment tests a further identity at coordinates of the end point z of the key side of its main
lookup argument. These are challenges of the last layer of the key side (Blocks/LookupSplit.lean),
which thus have a second role in soundness (a rider, Blocks/LookupRider.lean). A rider exists only
in the analysis: no message and no check is added. Here the five pieces are composed once:
   `Lk.stLookupR` σ d = st14a ≫ (stLast, with the larger errors) ≫ st14b ≫ st5 ≫ st6.
The protocol of the stage is `Lk.coLookupR` (`toCore_stLookupR`, by `rfl`). For 0 < D it consists of
the steps of the lookup argument (`Lk.coLookup`) in the same order, bracketed differently. That the
rounds are the same, one by one and in order, is neither stated nor proved in this library. That the
verifier's function, the implicit part and the honest prover agree is not stated as a theorem. For D
= 0 the protocol does not consist of these steps (co14a has no layer of the key side, coLast is the
layer number D - 1 = 0, while the lookup argument has none), and the theorems here on the
properties, the end point and the deferred claims, and `stLookupR_U_sub` on the pads, assume 0 < D.
All theorems here are stated for 2 ≠ 0 in E (the instance NeZero (2 : E)).

σ k is the coordinate of z that is substituted for the variable k of the rider (not L.par.σ, the
number of bits of a tree's index); d k bounds the degree of the rider in that variable. Where a
challenge has bad values from two sources, the error of the round is the maximum of the two
(Blocks/StageBoth.lean): a statement outside (R and K) is outside one of the two.
 * `Lk.props_stLookupR`: `Stage.Props`, under its hypotheses, from (c0, and G y is the zero
   function) to (c10, and G y is 0 at the point (x.z (σ k))_k). G y is a polynomial that depends on
   the implicit part only.
 * `stLookupR_U_sub`, `stLookupR_D`, `imp_stLookupR`, `adds_stLookupR`, `nz_of_pub_stLookupR`: pads,
   implicit part, the honest prover's copy of the list of deferred claims, end point.
 * `all_tkLookupR`: no vector is sent.

Notation:
 * key side: the forest of product trees over the leaves α - key (the head of
   Blocks/LookupRel.lean); z: `LkX.z`, the end of the key side (Blocks/LookupBlock.lean); `zf`:
   which coordinates of the end point z of the key side the verifier rejects at 0 (`LkPar.zf`).
 * `st14a`: α; the tree products and ϱ; the layers 0, .., D - 2 of the key side; `stLast`: the layer
   D - 1 of the key side; `st14b`: the end form and the end point are stored; the table side (the
   head of Blocks/LookupSplit.lean); `st5`: the degree check; `st6`: the root test
   (Blocks/LookupStage.lean).
 * `c0`, `c10`: `Cut`s (Blocks/Stage.lean): the relations before and after the lookup argument
   (`Lk.c0`, `Lk.c10`, Blocks/LookupStage.lean).
 * `UG` Q: the pads of the groups whose rank has the property Q; `rank`: zy 0, k 1, t 2, lf 3, bt 4,
   uv 5, rt 6 (Blocks/LookupStage.lean).
 * LIN(f): the affine form f has the value 0; REL: f is a sum of products of opened forms: the
   deferred claims (`Ledger`, Blocks/Form.lean; the head of Blocks/LookupStage.lean).
 * D, r, lp, NT: natural numbers, fields of `LkPar`: 2^D keys in a tree, NT trees, tables with 2^r
   entries, 2^lp bits for a multiplicity (Blocks/LookupRel.lean).
 * Pm: `LkPar.Pm` = 2^lp - 1: the number of the highest plane (Blocks/LookupRel.lean).

Limits: what the heads of Blocks/LookupStage.lean and Blocks/LookupHon.lean list as not said is not
said here either.

Terms: lean/GLOSSARY.md.
-/
import Blocks.LookupRider
import Blocks.LookupFacts
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Blocks.Lk

open Iop Prob Alg

variable {E Y Pd N : Type} [Field E] [NeZero (2 : E)] [Fintype E] [DecidableEq E] [Fintype N]
  [DecidableEq N] [Fintype Pd] [DecidableEq Pd] (L : Lk E Y Pd N) (T : Lk.Vecs E Y) {n : ℕ}
  (σ : Fin n → ℕ) (d : Fin n → ℕ)

/-- The protocol: for 0 < D the steps of the lookup argument, bracketed differently from
`Lk.coLookup`. For 0 < D its rounds are those of `Lk.coLookup`, one by one and in order (neither
stated nor proved in this library). The rider does not enter it. -/
def coLookupR : Core Pd E L.sL L.sX :=
  L.co14a.seq (L.coLast.seq (L.co14b.seq (L.co5.seq L.co6)))

/-- The lookup argument with a rider. -/
def stLookupR : Stage Pd E L.sL L.sX :=
  L.st14a.seq ((L.stLast.both ((L.bindsK (L.par.D - 1) σ).err d)).seq
    (L.st14b.seq (L.st5.seq L.st6)))

theorem toCore_stLookupR : (L.stLookupR σ d).toCore = L.coLookupR := rfl

/-! ## The pads, the implicit part -/

theorem stLookupR_U :
    (L.stLookupR σ d).U = L.st14a.U ∪ (L.stLast.U ∪ (L.st14b.U ∪ (∅ ∪ L.st6.U))) := rfl

theorem stLookupR_U_sub (hD : 0 < L.par.D) : (L.stLookupR σ d).U ⊆ L.allPads := by
  have h : ∀ Q, L.UG Q ⊆ L.allPads := fun Q _ ⟨g, _, hg, hp⟩ => ⟨g, hg, hp⟩
  rw [stLookupR_U]
  refine Set.union_subset ((L.st14a_U_sub.trans L.UA_sub_UG).trans (h _))
    (Set.union_subset ?_
      (Set.union_subset (L.st14b_U_sub.trans (h _))
        (Set.union_subset (Set.empty_subset _) (L.st6_U_sub.trans (h _)))))
  exact fun p hp => ⟨.k (L.par.D - 1), by show L.par.D - 1 < L.par.D; omega, hp⟩

theorem st6_D : L.st6.D = L.st6.U := rfl

theorem stLookupR_D : (L.stLookupR σ d).D = (L.stLookupR σ d).U := by
  show L.st14a.D ∪ (L.stLast.D ∪ (L.st14b.D ∪ (∅ ∪ L.st6.D))) =
    L.st14a.U ∪ (L.stLast.U ∪ (L.st14b.U ∪ (∅ ∪ L.st6.U)))
  rw [L.st14a_D, L.stLast_D, L.st14b_D, L.st6_D]

theorem imp_coLookupR : ∀ y τ, L.coLookupR.B.imp y τ = y :=
  imp_seq (S₁ := L.co14a) L.imp_st14a <|
  imp_seq (S₁ := L.coLast) L.imp_stLast <|
  imp_seq (S₁ := L.co14b) L.imp_st14b <|
  imp_seq (S₁ := L.co5) (S₂ := L.co6) (fun _ _ => rfl) L.imp_st6

theorem imp_stLookupR : ∀ y τ, (L.stLookupR σ d).B.imp y τ = y := L.imp_coLookupR

/-! ## The properties -/

variable {σ d}

/-- All properties of the lookup argument with a rider, under the hypotheses below and 2 ≠ 0 in
E. -/
theorem props_stLookupR {p : ℕ} [CharP E p] (hW : L.par.WF p) (hok : L.PadsOK) (hD : 0 < L.par.D)
    (hσ : Function.Injective σ) (hle : ∀ k, σ k ≤ L.par.D - 1 + L.par.σ)
    {G : Y → (Fin n → E) → E} (hG : ∀ y, DegLE d (G y)) :
    (L.stLookupR σ d).Props ((L.c0 T).and (fun _ y => ∀ z, G y z = 0) fun _ _ _ y => ∀ z, G y z = 0)
      ((L.c10 T).and (fun x y => G y (fun k => x.z (σ k)) = 0) fun _ _ x y =>
        G y (fun k => x.z (σ k)) = 0) := by
  -- the five pieces, each with the rider's relation added
  have pa := (L.props_st14a T hW hok).frame (K := fun _ y => ∀ z, G y z = 0)
    (K' := fun _ y => ∀ z, G y z = 0) (KH := fun _ _ _ y => ∀ z, G y z = 0)
    (KH' := fun _ _ _ y => ∀ z, G y z = 0) (fun _ y τ _ _ _ _ h => by rwa [L.imp_st14a] at h)
    (fun _ _ _ y _ _ _ _ _ _ h => by rwa [L.imp_st14a])
  have pl := L.props_stLast_rider T hW.ord hok hD hσ hle (G := fun _ y => G y)
    (fun _ y => hG y) fun _ _ _ _ => rfl
  have pb := (L.props_st14b T hok hW.nt).frame
    (K := fun x y => G y (fun k => x.pt (σ k)) = 0) (K' := fun x y => G y (fun k => x.z (σ k)) = 0)
    (KH := fun _ _ x y => G y (fun k => x.pt (σ k)) = 0)
    (KH' := fun _ _ x y => G y (fun k => x.z (σ k)) = 0)
    (fun x y τ xo hp _ _ h => by
      rw [L.imp_st14b, show xo.z = x.pt from L.keeps_after_key x _ _ xo hp] at h
      exact h)
    (fun _ _ x y _ xo _ hp _ _ h => by
      rw [L.imp_st14b]
      show G y (fun k => xo.z (σ k)) = 0
      rw [show xo.z = x.pt from L.keeps_after_key x _ _ xo hp]
      exact h)
  have p5 := (L.props_st5 T hW.nt).frame
    (K := fun x y => G y (fun k => x.z (σ k)) = 0) (K' := fun x y => G y (fun k => x.z (σ k)) = 0)
    (KH := fun _ _ x y => G y (fun k => x.z (σ k)) = 0)
    (KH' := fun _ _ x y => G y (fun k => x.z (σ k)) = 0)
    (fun x y τ xo hp _ _ h => by
      obtain ⟨ϱ, rfl⟩ := L.pub_st5 hp
      exact h)
    (fun _ _ x y _ xo _ hp _ _ h => by
      obtain ⟨ϱ, rfl⟩ := L.pub_st5 hp
      exact h)
  have p6 := (L.props_st6 T hok hW.nt).frame
    (K := fun x y => G y (fun k => x.z (σ k)) = 0) (K' := fun x y => G y (fun k => x.z (σ k)) = 0)
    (KH := fun _ _ x y => G y (fun k => x.z (σ k)) = 0)
    (KH' := fun _ _ x y => G y (fun k => x.z (σ k)) = 0)
    (fun x y τ xo hp _ _ h => by
      rw [L.imp_st6, (L.pub_st6 hp).2.1] at h
      exact h)
    (fun _ _ x y _ xo _ hp _ _ h => by
      rw [L.imp_st6]
      show G y (fun k => xo.z (σ k)) = 0
      rw [(L.pub_st6 hp).2.1]
      exact h)
  -- no two of them share a pad
  have u56 : (L.st5.seq L.st6).U ⊆ L.UG (5 ≤ ·) := Set.union_subset (Set.empty_subset _) L.st6_U_sub
  have ub : L.st14b.U ⊆ L.UG (fun m => 2 ≤ m ∧ m ≤ 4) :=
    Set.union_subset (Set.empty_subset _)
      (Set.union_subset (Set.empty_subset _)
        (Set.union_subset (L.stTab_sub.trans (L.UG_mono fun m h => by omega))
          (Set.union_subset (L.grp_sub_UG .lf trivial (by show 2 ≤ 3 ∧ 3 ≤ 4; omega))
            (Set.union_subset (Set.empty_subset _)
              (L.grp_sub_UG .bt trivial (by show 2 ≤ 4 ∧ 4 ≤ 4; omega))))))
  have db : Disjoint L.st14b.U (L.st5.seq L.st6).U :=
    (L.disj_UG hok (Q := fun m => 2 ≤ m ∧ m ≤ 4) (Q' := (5 ≤ ·)) fun m h => by omega).mono ub u56
  have q3 := pb.seq (p5.seq p6 (Set.empty_disjoint _) (Set.empty_disjoint _))
    db (by rw [L.st14b_D]; exact db)
  have u3 : (L.st14b.seq (L.st5.seq L.st6)).U ⊆ L.UG (2 ≤ ·) :=
    Set.union_subset L.st14b_U_sub (u56.trans (L.UG_mono fun m h => by omega))
  have dl : Disjoint L.stLast.U (L.st14b.seq (L.st5.seq L.st6)).U :=
    (L.disj_UG hok (Q := (· = 1)) (Q' := (2 ≤ ·)) fun m h => by omega).mono
      (L.grp_sub_UG (Q := (· = 1)) (.k (L.par.D - 1)) (by show L.par.D - 1 < L.par.D; omega) rfl) u3
  have q2 := pl.seq q3 dl dl
  have da : Disjoint L.st14a.U
      ((L.stLast.both ((L.bindsK (L.par.D - 1) σ).err d)).seq (L.st14b.seq (L.st5.seq L.st6))).U :=
    Set.disjoint_union_right.mpr ⟨L.disj_a_last hok hD,
      (L.disj_UG hok (Q := (· ≤ 1)) (Q' := (2 ≤ ·)) fun m h => by omega).mono
        (L.st14a_U_sub.trans L.UA_sub_UG) u3⟩
  exact pa.seq q2 da (by rw [L.st14a_D]; exact da)

/-! ## The deferred claims and the end point -/

variable (σ d)

/-- Under ho, hD and 2 ≠ 0 in E: no coordinate of z that the verifier checks is 0, whenever the
verifier does not reject. -/
theorem nz_of_pub_stLookupR (ho : L.par.OrdOK) (hD : 0 < L.par.D) {led : Ledger N E}
    {ρ : Rho (L.stLookupR σ d).B.shape} {p : Plains (L.stLookupR σ d).B.shape} {x : LkX N E}
    (h : (L.stLookupR σ d).B.pub led ρ p = some x) :
    ∀ t < L.par.D + L.par.σ, L.par.zf t = true → x.z t ≠ 0 := by
  have e1 : L.stLast.B.Ensures fun x =>
      ∀ t < L.par.D + L.par.σ, L.par.zf t = true → x.pt t ≠ 0 := fun x ρ p xo h => by
    obtain ⟨xo', h3, rfl⟩ := Option.map_eq_some_iff.mp h
    intro t ht hf
    refine (L.plK (L.par.D - 1)).pt_ne_zero
      (ho.kOrd _) h3 t (by show t < L.par.D - 1 + L.par.σ + 1; omega) ?_
    show L.par.kf (L.par.D - 1 + 1) t = true
    rw [show L.par.D - 1 + 1 = L.par.D by omega, L.par.kf_top]
    exact hf
  have k56 : (L.st5.B.seq L.st6.B).Keeps (fun x : LkX N E => x.z) (fun x => x.z) :=
    Block.Keeps.seq (f₂ := fun x : LkX N E => x.z)
      (fun x _ _ xo h => by obtain ⟨ϱ, rfl⟩ := L.pub_st5 h; rfl) fun x _ _ xo h => (L.pub_st6 h).2.1
  exact Block.Ensures.after L.st14a.B
    (Block.Ensures.kept (Q := fun z : ℕ → E => ∀ t < L.par.D + L.par.σ, L.par.zf t = true → z t ≠ 0)
      e1 (L.keeps_after_key.seq k56))
    led ρ p x h

/-- Under hD and 2 ≠ 0 in E: how many LIN, opened forms and REL the honest prover's copy of the list
of deferred claims gains. -/
theorem adds_stLookupR (hD : 0 < L.par.D) :
    Adds (L.stLookupR σ d)
      (3, 2 * (L.par.D + L.par.r + 2) + 3 * L.par.Pm, L.par.D + L.par.r + 3) := fun a ρ => by
  have h := (L.adds_st14a.seq
      (Adds.seq (S₁ := L.stLast.both ((L.bindsK (L.par.D - 1) σ).err d)) L.adds_stLast
        (L.adds_st14b.seq (L.adds_st5.seq L.adds_st6))))
    a ρ
  refine h.trans ?_
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> first | (dsimp only; done) | (dsimp only; omega)

/-! ## No vector is sent -/

section Track

variable (F : Type) [Field F] [Algebra F E]

def encLookupR : EncData F E L.coLookupR.B.shape :=
  EncData.app (s := L.co14a.B.shape) (L.enc14a F) <|
  EncData.app (s := L.coLast.B.shape) (encPl F (L.plK (L.par.D - 1))) <|
  EncData.app (s := L.co14b.B.shape) (L.enc14b F) <|
  EncData.app (s := L.co5.B.shape) (t := L.co6.B.shape) (L.enc5 F) (L.enc6 F)

/-- The tracking data of the protocol; they are the stage's too (`Stage.Track`,
Blocks/StageTrack.lean; `toCore_stLookupR`). -/
def tkLookupR (ra : Reads F E L.sL) :
    L.coLookupR.Track ra (Stage.readsX (LkX N E) (LkA E) ra) :=
  trackSame L.coLookupR (L.encLookupR F) ra

theorem tkLookupR_ok (ra : Reads F E L.sL) : (L.tkLookupR F ra).OK :=
  trackSame_ok _ _ _ L.imp_coLookupR

variable {F} {Q : Code.Enc F → ℕ → ℕ → Role → ℕ → Prop}

theorem all_tkLookupR (ra : Reads F E L.sL) : (L.tkLookupR F ra).All Q :=
  EncData.All.app (s := L.co14a.B.shape) (L.all_track14a ra) <|
  EncData.All.app (s := L.coLast.B.shape) (all_encPl (L.plK (L.par.D - 1))) <|
  EncData.All.app (s := L.co14b.B.shape) (L.all_track14b (Stage.readsX (LkX N E) (LkA E) ra)) <|
  EncData.All.app (s := L.co5.B.shape)
    (t := L.co6.B.shape) (d := L.enc5 F) ⟨fun e => e.elim, trivial⟩ L.all_enc6

end Track

end Blocks.Lk

