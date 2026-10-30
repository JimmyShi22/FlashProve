-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/LookupSplit.lean: steps 1 to 4 of the lookup argument as three stages.

The coordinates of the end point z of the key side (Blocks/LookupRel.lean) are the challenges of its
last product layer. A segment may test a further identity at some of them, so that these have a
second role in soundness (a rider, Blocks/LookupRider.lean). So the last layer has to be a separate
stage, between named relations:
   `Lk.st14a`  α; the tree products and ϱ; the layers 0, .., D - 2 of the key side
       from c0 to cK (D - 1)
   `Lk.stLast` the layer D - 1 of the key side (`Lk.stK` (D - 1))   from cK (D - 1) to cK D
   `Lk.st14b`  the end form and the end point are stored; the table side   from cK D to c7
 * `props_st14a`, `props_stLast`, `props_st14b`: `Stage.Props`; `props_split`: the three in a row
   have the properties of steps 1 to 4. Hypotheses: `LkPar.WF` at the characteristic p of E,
   `Lk.PadsOK`, 0 < D; 2 ≠ 0 in E is assumed throughout the file. For D = 0 the three stages are not
   steps 1 to 4: `stLast` is `stK` 0, a layer that `Lk.st14` has not.
 * `imp_st14a`, `imp_stLast`, `imp_st14b`: the implicit part is unchanged.
 * `adds_st14a`, `adds_stLast`, `adds_st14b`: how many claims the honest prover's copy of the list
   of deferred claims gains.
 * `track14a`, `trackLast`, `track14b`, with `all_track14a`, `all_trackLast`, `all_track14b`: no
   vector is sent.
The relations cK l (`Lk.RK` for soundness, `Lk.HK` for the honest run) say, among other things:
 (1) the list of deferred claims is true;
 (2) the sent tree products satisfy `LkPar.Ident` and those of the table side are the true ones
     (`Lk.FK`; for the honest run all are: `Lk.TZ`);
 (3) the running form has the value of the extension of level l of the key side at the running
     point.
For soundness they say (3) only under a premise (`Lk.KL`): no coordinate t of the running point with
`LkPar.kf` l t = true is 0; these are every t if l < D, and those with `LkPar.zf` t = true if l = D.
At cK D the running point x.pt is z and the running form x.C is C_end.

Notation: `T`: `Lk.Vecs E Y` (Blocks/LookupBlock.lean): the true vectors of a lookup argument: the
keys and the multiplicity bits, as functions of the implicit part; `Adds S d`
(Blocks/LookupStage.lean): the stage adds d = (LIN, opened forms, REL) claims to the honest prover's
copy of the list, whatever the verifier sends; `S.U`, `S.D`: sets of pads, fields of `Stage`
(Blocks/Stage.lean); `UG Q` (Blocks/LookupStage.lean): the pads of the groups whose rank has the
property Q (`rank`: the position of a group in the order of the messages); `Core.Track`
(Blocks/StageTrack.lean): the tracking data of a protocol (`d`: how it sends its vectors); `t.All Q`
(Blocks/StageSide.lean): every vector that the protocol sends has the property Q; `REnc.none`
(Blocks/BlockFront.lean): encoding data for a round without vectors; D, σ, r, lp, NT: natural
numbers, fields of `LkPar`: 2^D keys in a tree, NT trees, tables with 2^r entries, 2^lp bits for a
multiplicity; σ: the number of bits of a tree's index (Blocks/LookupRel.lean; σ: the head of
Blocks/LookupWhole.lean).
Limits: what the heads of Blocks/LookupStage.lean and Blocks/LookupHon.lean list as not said is not
said here either.
-/
import Blocks.LookupStage
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Blocks

open Iop Prob
open scoped ENNReal

namespace Lk

variable {E Y Pd N : Type} [Field E] [NeZero (2 : E)] [Fintype E] [DecidableEq E] [Fintype N]
  [DecidableEq N] [Fintype Pd] [DecidableEq Pd] (L : Lk E Y Pd N) (T : Lk.Vecs E Y)

/-- The protocols of the three stages. -/
def co14a : Core Pd E L.sL L.sX := L.coAl.seq (L.coZY.seq (L.coKey (L.par.D - 1) 0))
def coLast : Core Pd E L.sX L.sX := L.coK (L.par.D - 1)
def co14b : Core Pd E L.sX L.sX :=
  L.coKe.seq (L.coT0.seq ((L.coTab L.par.r 0).seq (L.coL.seq (L.coB0.seq L.coB))))

/-- Before the last layer of the key side. -/
def st14a : Stage Pd E L.sL L.sX := L.stAl.seq (L.stZY.seq (L.stKey (L.par.D - 1) 0))

/-- The last layer of the key side. Its round challenges and its ζ are the coordinates of z. -/
def stLast : Stage Pd E L.sX L.sX := L.stK (L.par.D - 1)

/-- After the key side. -/
def st14b : Stage Pd E L.sX L.sX :=
  L.stKe.seq (L.stT0.seq ((L.stTab L.par.r 0).seq (L.stL.seq (L.stB0.seq L.stB))))

theorem toCore_st14a : L.st14a.toCore = L.co14a := rfl
theorem toCore_stLast : L.stLast.toCore = L.coLast := rfl
theorem toCore_st14b : L.st14b.toCore = L.co14b := rfl

/-! ## The pads -/

/-- The pads of the groups before the last layer: Z, Y, and the layers l < D - 1 of the key side. -/
def UA : Set Pd := {p | p ∈ L.grp .zy ∨ ∃ l, l < L.par.D - 1 ∧ p ∈ L.grp (.k l)}

theorem st14a_U_sub : L.st14a.U ⊆ L.UA := by
  refine Set.union_subset (Set.empty_subset _)
    (Set.union_subset (fun p hp => Or.inl hp) fun p hp => ?_)
  obtain ⟨l', _, h2, h3⟩ := L.mem_stKey_U.mp hp
  exact Or.inr ⟨l', by omega, h3⟩

theorem stLast_U : L.stLast.U = L.grp (.k (L.par.D - 1)) := rfl

theorem st14b_U_sub : L.st14b.U ⊆ L.UG (2 ≤ ·) :=
  Set.union_subset (Set.empty_subset _)
    (Set.union_subset (Set.empty_subset _)
      (Set.union_subset (L.stTab_sub.trans (L.UG_mono fun m h => by omega))
        (Set.union_subset (L.grp_sub_UG .lf trivial (by show 2 ≤ 3; omega))
          (Set.union_subset (Set.empty_subset _)
            (L.grp_sub_UG .bt trivial (by show 2 ≤ 4; omega))))))

theorem st14a_D : L.st14a.D = L.st14a.U := by
  show ∅ ∪ (L.grp .zy ∪ (L.stKey (L.par.D - 1) 0).D) = ∅ ∪ (L.grp .zy ∪ (L.stKey (L.par.D - 1) 0).U)
  rw [L.stKey_D]

theorem stLast_D : L.stLast.D = L.stLast.U := rfl

theorem st14b_D : L.st14b.D = L.st14b.U := by
  show ∅ ∪ (∅ ∪ ((L.stTab L.par.r 0).D ∪ (L.grp .lf ∪ (∅ ∪ L.grp .bt)))) =
    ∅ ∪ (∅ ∪ ((L.stTab L.par.r 0).U ∪ (L.grp .lf ∪ (∅ ∪ L.grp .bt))))
  rw [L.stTab_D]

theorem UA_sub_UG : L.UA ⊆ L.UG (· ≤ 1) := by
  rintro p (hp | ⟨l, hl, hp⟩)
  · exact ⟨.zy, by show 0 ≤ 1; omega, trivial, hp⟩
  · exact ⟨.k l, le_rfl, by show l < L.par.D; omega, hp⟩

theorem disj_a_last (hok : L.PadsOK) (hD : 0 < L.par.D) : Disjoint L.st14a.U L.stLast.U := by
  refine Set.disjoint_left.mpr fun p hp hp' => ?_
  have hg : L.GOK (.k (L.par.D - 1)) := by show L.par.D - 1 < L.par.D; omega
  rcases L.st14a_U_sub hp with h | ⟨l, hl, h⟩
  · exact Set.disjoint_left.mp (hok.disj .zy (.k (L.par.D - 1)) trivial hg (by simp)) h hp'
  · exact Set.disjoint_left.mp
      (hok.disj (.k l) (.k (L.par.D - 1)) (by show l < L.par.D; omega)
        hg (fun he => by injection he; omega))
      h hp'

theorem disj_a_b (hok : L.PadsOK) : Disjoint L.st14a.U L.st14b.U :=
  (L.disj_UG hok (Q := (· ≤ 1)) (Q' := (2 ≤ ·)) fun m h => by omega).mono
    (L.st14a_U_sub.trans L.UA_sub_UG) L.st14b_U_sub

theorem disj_last_b (hok : L.PadsOK) (hD : 0 < L.par.D) : Disjoint L.stLast.U L.st14b.U :=
  (L.disj_UG hok (Q := (· = 1)) (Q' := (2 ≤ ·)) fun m h => by omega).mono
    (L.grp_sub_UG (Q := (· = 1)) (.k (L.par.D - 1)) (by show L.par.D - 1 < L.par.D; omega) rfl)
    L.st14b_U_sub

/-! ## The properties -/

theorem props_st14a {p : ℕ} [CharP E p] (hW : L.par.WF p) (hok : L.PadsOK) :
    L.st14a.Props (L.c0 T) ((L.cK T) (L.par.D - 1)) := by
  have h3 := (L.props_stKey T) hW.ord hok (L.par.D - 1) 0 (by omega)
  rw [Nat.zero_add] at h3
  have d2 : Disjoint (L.grp .zy)
      (L.stKey (L.par.D - 1) 0).U := Set.disjoint_left.mpr fun p hp hp' => by
    obtain ⟨l', _, h2, h4⟩ := L.mem_stKey_U.mp hp'
    exact Set.disjoint_left.mp
      (hok.disj .zy (.k l') trivial (by show l' < L.par.D; omega) (by simp)) hp h4
  exact (L.props_stAl T hW).seq
    ((L.props_stZY T hok hW.nt).seq h3 d2 d2) (Set.empty_disjoint _) (Set.empty_disjoint _)

theorem props_stLast (ho : L.par.OrdOK) (hok : L.PadsOK) (hD : 0 < L.par.D) :
    L.stLast.Props ((L.cK T) (L.par.D - 1)) (L.cK T L.par.D) := by
  have h := (L.props_stK T) ho hok (l := L.par.D - 1) (by omega)
  rwa [Nat.sub_add_cancel hD] at h

theorem props_st14b (hok : L.PadsOK) (hnt : L.par.NT ≤ 2 ^ L.par.σ) :
    L.st14b.Props (L.cK T L.par.D) (L.c7 T) := by
  have p8 : (L.stB0.seq L.stB).Props (L.c5 T) (L.c7 T) :=
    (L.props_stB0 T hnt).seq (L.props_stB T hok) (Set.empty_disjoint _) (Set.empty_disjoint _)
  have u8 : (L.stB0.seq L.stB).U ⊆ L.UG (4 ≤ ·) :=
    Set.union_subset (Set.empty_subset _) (L.grp_sub_UG .bt trivial (by show 4 ≤ 4; omega))
  have d7 : Disjoint (L.grp .lf) (L.stB0.seq L.stB).U :=
    (L.disj_UG hok (Q := (· = 3)) (Q' := (4 ≤ ·)) fun m h => by omega).mono
      (L.grp_sub_UG (Q := (· = 3)) .lf trivial rfl) u8
  have p7 := (L.props_stL T hok).seq p8 d7 d7
  have u7 : (L.stL.seq (L.stB0.seq L.stB)).U ⊆ L.UG (3 ≤ ·) :=
    Set.union_subset (L.grp_sub_UG .lf trivial (by show 3 ≤ 3; omega))
      (u8.trans (L.UG_mono fun m h => by omega))
  have d6 : Disjoint (L.stTab L.par.r 0).U (L.stL.seq (L.stB0.seq L.stB)).U :=
    (L.disj_UG hok (Q := (· = 2)) (Q' := (3 ≤ ·)) fun m h => by omega).mono L.stTab_sub u7
  have h6 := (L.props_stTab T) hok L.par.r 0 (by omega)
  rw [Nat.zero_add] at h6
  have p6 := h6.seq p7 d6 (by rw [L.stTab_D]; exact d6)
  exact (L.props_stKe T).seq
    ((L.props_stT0 T hnt).seq p6 (Set.empty_disjoint _) (Set.empty_disjoint _))
    (Set.empty_disjoint _) (Set.empty_disjoint _)

/-- Under hW at the characteristic p of E, hok, hD and 2 ≠ 0 in E, the three stages in a row have
the properties of steps 1 to 4. -/
theorem props_split {p : ℕ} [CharP E p] (hW : L.par.WF p) (hok : L.PadsOK) (hD : 0 < L.par.D) :
    (L.st14a.seq (L.stLast.seq L.st14b)).Props (L.c0 T) (L.c7 T) := by
  have h2 := (L.props_stLast T hW.ord hok hD).seq (L.props_st14b T hok hW.nt) (L.disj_last_b hok hD)
    (by rw [L.stLast_D]; exact L.disj_last_b hok hD)
  have d : Disjoint L.st14a.U (L.stLast.seq L.st14b).U :=
    Set.disjoint_union_right.mpr ⟨L.disj_a_last hok hD, L.disj_a_b hok⟩
  exact (L.props_st14a T hW hok).seq h2 d (by rw [L.st14a_D]; exact d)

/-! ## The implicit part, the deferred claims, the vectors -/

theorem imp_st14a : ∀ y τ, L.st14a.B.imp y τ = y :=
  imp_seq (S₁ := L.coAl) (fun _ _ => rfl) <|
  imp_seq (S₁ := L.coZY) (S₂ := L.coKey (L.par.D - 1) 0) (fun _ _ => rfl) (L.imp_stKey _ _)

theorem imp_stLast : ∀ y τ, L.stLast.B.imp y τ = y := fun y τ => (L.plK (L.par.D - 1)).imp_pl y τ

theorem imp_st14b : ∀ y τ, L.st14b.B.imp y τ = y :=
  imp_seq (S₁ := L.coKe) (fun _ _ => rfl) <|
  imp_seq (S₁ := L.coT0) (fun _ _ => rfl) <|
  imp_seq (S₁ := L.coTab L.par.r 0) (L.imp_stTab _ _) <|
  imp_seq (S₁ := L.coL) (fun y τ => L.plL.imp_pl y τ) <|
  imp_seq (S₁ := L.coB0) (S₂ := L.coB) (fun _ _ => rfl) (fun y τ => L.plB.imp_pl y τ)

theorem adds_st14a : Adds L.st14a (0, 2 * (L.par.D - 1), L.par.D - 1) := fun a ρ => by
  have h := (Adds.seq (S₁ := L.stAl) (d₁ := (0, 0, 0)) (fun _ _ => rfl) <|
      Adds.seq (S₁ := L.stZY) (d₁ := (0, 0, 0)) (fun _ _ => rfl) (L.adds_stKey (L.par.D - 1) 0))
    a ρ
  refine h.trans ?_
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> first | (dsimp only; done) | (dsimp only; omega)

theorem adds_stLast : Adds L.stLast (0, 2, 1) := L.adds_stK _

theorem adds_st14b : Adds L.st14b (2, 2 * (L.par.r + 2), L.par.r + 2) := fun a ρ => by
  have h := (Adds.seq (S₁ := L.stKe) (d₁ := (0, 0, 0)) (fun _ _ => rfl) <|
      Adds.seq (S₁ := L.stT0) (d₁ := (0, 0, 0)) (fun _ _ => rfl) <|
      Adds.seq (L.adds_stTab L.par.r 0) <|
      Adds.seq L.adds_stL <|
      Adds.seq (S₁ := L.stB0) (d₁ := (0, 0, 0)) (fun _ _ => rfl) L.adds_stB)
    a ρ
  refine h.trans ?_
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> first | (dsimp only; done) | (dsimp only; omega)

section Track

variable (F : Type) [Field F] [Algebra F E]

def enc14a : EncData F E L.co14a.B.shape :=
  EncData.app (s := L.coAl.B.shape) (REnc.none E F Empty E, PUnit.unit) <|
  EncData.app (s := L.coZY.B.shape) (t := (L.coKey (L.par.D - 1) 0).B.shape)
    (REnc.none E F L.KZY (Fin L.par.σ → E), PUnit.unit) (L.encKey F _ _)

def enc14b : EncData F E L.co14b.B.shape :=
  EncData.app (s := L.coKe.B.shape) PUnit.unit <|
  EncData.app (s := L.coT0.B.shape)
    (REnc.none E F Empty (Fin (L.par.σ + L.par.lp) → E), PUnit.unit) <|
  EncData.app (s := (L.coTab L.par.r 0).B.shape) (L.encTab F _ _) <|
  EncData.app (s := L.coL.B.shape) (encPl F L.plL) <|
  EncData.app (s := L.coB0.B.shape)
    (t := L.coB.B.shape) (REnc.none E F Empty (Fin L.par.gT → E), PUnit.unit) (encPl F L.plB)

def track14a (ra : Reads F E L.sL) :
    L.st14a.Track ra (Stage.readsX (LkX N E) (LkA E) ra) :=
  (show L.co14a.Track _ _ from trackSame L.co14a (L.enc14a F) ra)
def trackLast (ra : Reads F E L.sX) :
    L.stLast.Track ra (Stage.readsX (LkX N E) (LkA E) ra) :=
  (show L.coLast.Track _ _ from trackSame L.coLast (encPl F (L.plK (L.par.D - 1))) ra)
def track14b (ra : Reads F E L.sX) :
    L.st14b.Track ra (Stage.readsX (LkX N E) (LkA E) ra) :=
  (show L.co14b.Track _ _ from trackSame L.co14b (L.enc14b F) ra)

theorem track14a_ok (ra : Reads F E L.sL) : (L.track14a F ra).OK := trackSame_ok _ _ _ L.imp_st14a
theorem trackLast_ok (ra : Reads F E L.sX) : (L.trackLast F ra).OK :=
  trackSame_ok _ _ _ L.imp_stLast
theorem track14b_ok (ra : Reads F E L.sX) : (L.track14b F ra).OK := trackSame_ok _ _ _ L.imp_st14b

variable {F} {Q : Code.Enc F → ℕ → ℕ → Role → ℕ → Prop}

theorem all_track14a (ra : Reads F E L.sL) : (L.track14a F ra).All Q :=
  EncData.All.app (s := L.coAl.B.shape)
      (d := (REnc.none E F Empty E, PUnit.unit)) ⟨fun e => e.elim, trivial⟩ <|
  EncData.All.app (s := L.coZY.B.shape) (t := (L.coKey (L.par.D - 1) 0).B.shape)
    (d := (REnc.none E F L.KZY (Fin L.par.σ → E), PUnit.unit))
    ⟨fun e => e.elim, trivial⟩ (L.all_encKey _ _)

theorem all_trackLast (ra : Reads F E L.sX) : (L.trackLast F ra).All Q :=
  all_encPl (L.plK (L.par.D - 1))

theorem all_track14b (ra : Reads F E L.sX) : (L.track14b F ra).All Q :=
  EncData.All.app (s := L.coKe.B.shape) (d := PUnit.unit) trivial <|
  EncData.All.app (s := L.coT0.B.shape)
      (d := (REnc.none E F Empty (Fin (L.par.σ + L.par.lp) → E), PUnit.unit))
      ⟨fun e => e.elim, trivial⟩ <|
  EncData.All.app (s := (L.coTab L.par.r 0).B.shape) (L.all_encTab _ _) <|
  EncData.All.app (s := L.coL.B.shape) (all_encPl L.plL) <|
  EncData.All.app (s := L.coB0.B.shape) (t := L.coB.B.shape)
    (d := (REnc.none E F Empty (Fin L.par.gT → E), PUnit.unit))
    ⟨fun e => e.elim, trivial⟩ (all_encPl L.plB)

end Track

end Lk

end Blocks

