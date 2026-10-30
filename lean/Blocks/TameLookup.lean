-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/TameLookup.lean: whether the lookup argument's verifier rejects depends on its own randomness
only, for a well-formed list of deferred claims.

The notion: Blocks/Tame.lean. The list: `Ledger.Ord` (Blocks/TameBlocks.lean).
 * One statement for each step of the argument (`Lk.tame_coAl`, .., `tame_coRec`): a well-formed
   list stays well-formed, with the lengths that the step adds; for a well-formed list the verifier
   rejects exactly on the public set `Bad` of the step (a 0 in a coordinate of one of the four
   points of `coZY`, `coT0`, `coB0`, `coUV`, or in a challenge of a layer of the two trees, the leaf
   layer and the bit layer apart; of the last layer of the key side, whose challenges are the
   coordinates of the end point z, only in one that `LkPar.zf` names).
 * `Lk.addsL`: what the whole argument adds to the list: 3 LIN, 2 D + 2 r + 4 + 3 Pm opened forms, D
   + r + 3 REL.
 * `Lk.tame_coLookup`, `Lk.tame_coLookupR`: the whole argument, in its two forms (the second: for
   0 < D). So the checks of the list in its product layers and before its last REL never reject a
   well-formed list.
Notation: in the names of the steps: Al, α (step 1); ZY, the products, then a point (step 2 and the
start of 3); K, Key, Ke, the product tree over the keys (step 3); T0, T, Tab, the product tree over
the table, and L, B0, B, its leaf layer and bit layer (step 4); UV, Xi, Rs, Rec, the root test (step
6); `co5`: step 5; `co6`: step 6 (Blocks/LookupStage.lean, parts 3 and 5). `D`, `r`, `lp`, natural
numbers: 2^D keys in a tree, tables with 2^r entries (a shorter table is repeated), 2^lp bits for a
multiplicity; `σ`: a natural number, a field of `LkPar`; `Pm`: the number of the highest plane,
`2 ^ lp - 1`; `gT`: the number of variables of the leaves of the table side (`LkPar`,
Blocks/LookupRel.lean).
-/
import Blocks.TameBlocks
import Blocks.LookupWhole

set_option autoImplicit false

namespace Blocks.Lk

open Iop Prob Alg

variable {E Y Pd N : Type} [Field E] [NeZero (2 : E)] [Fintype E] [DecidableEq E] [Fintype N]
  [DecidableEq N] (L : Lk E Y Pd N) (n : ℕ × ℕ × ℕ)

/-- the property of the explicit part of the argument -/
abbrev IO (n : ℕ × ℕ × ℕ) (x : LkX N E) : Prop := x.led.Ord n

omit [NeZero (2 : E)] [DecidableEq E] [Fintype N] [DecidableEq N] in
theorem tame_coAl : L.coAl.Tame (fun led => led.Ord n) (IO n) :=
  show L.bAl.Tame L.hAl.Bad _ _
    from Block.Tame.oneAll (fun led al _ => LkX.init led al) _ fun _ _ _ h => h

omit [NeZero (2 : E)] [Fintype N] in
theorem tame_coZY : L.coZY.Tame (IO n) (IO n) :=
  show L.bZY.Tame L.hZY.Bad _ _
    from Block.Tame.oneIf (r := L.rZY) (fun ϱ => nzT ϱ)
      (fun x ϱ s => L.setZY x ϱ s) _ fun _ _ _ h => h

omit [NeZero (2 : E)] in
theorem tame_coK (l : ℕ) : (L.coK l).Tame (IO n) (IO (n.1, n.2.1 + 2, n.2.2 + 1)) :=
  show (L.bK l).Tame (L.hK l).Bad _ _
    from Block.Tame.on ((L.prK l).tame_core n) gxPL pxPL id (fun _ yo => yo) (Ja := IO n)
      (Jb := IO (n.1, n.2.1 + 2, n.2.2 + 1)) (fun _ h => h) fun _ _ _ h => h

omit [NeZero (2 : E)] in
theorem tame_coKey :
    ∀ (k l : ℕ) (n : ℕ × ℕ × ℕ), (L.coKey k l).Tame (IO n) (IO (n.1, n.2.1 + 2 * k, n.2.2 + k))
  | 0, _, n => Core.tame_id _ _
  | k + 1, l, n => (Core.Tame.seq (L.tame_coK n l) (tame_coKey k (l + 1) _)).conseq (fun _ h => h) fun x h => by
      have e : ((n.1, n.2.1 + 2 + 2 * k, n.2.2 + 1 + k) : ℕ × ℕ × ℕ) =
          (n.1, n.2.1 + 2 * (k + 1), n.2.2 + (k + 1)) :=
        Prod.ext rfl
          (Prod.ext (by show n.2.1 + 2 + 2 * k = n.2.1 + 2 * (k + 1); omega)
            (by show n.2.2 + 1 + k = n.2.2 + (k + 1); omega))
      exact e ▸ h

omit [Field E] [NeZero (2 : E)] [Fintype E] [DecidableEq E] [Fintype N] [DecidableEq N] in
theorem tame_coKe : L.coKe.Tame (IO n) (IO n) :=
  show L.bKe.Tame L.hKe.Bad _ _ from Block.Tame.pure _ fun _ h => ⟨_, rfl, h⟩

omit [NeZero (2 : E)] [Fintype N] [DecidableEq N] in
theorem tame_coT0 : L.coT0.Tame (IO n) (IO n) :=
  show L.bT0.Tame L.hT0.Bad _ _
    from Block.Tame.oneIf (r := Block.chalRound E (Fin (L.par.σ + L.par.lp) → E)) (fun ϱ => nzT ϱ)
      (fun x ϱ _ => L.setT0 x ϱ) _ fun _ _ _ h => h

omit [NeZero (2 : E)] in
theorem tame_coT (l : ℕ) : (L.coT l).Tame (IO n) (IO (n.1, n.2.1 + 2, n.2.2 + 1)) :=
  show (L.bT l).Tame (L.hT l).Bad _ _
    from Block.Tame.on ((L.prT l).tame_core n) gxPL pxPL id (fun _ yo => yo) (Ja := IO n)
      (Jb := IO (n.1, n.2.1 + 2, n.2.2 + 1)) (fun _ h => h) fun _ _ _ h => h

omit [NeZero (2 : E)] in
theorem tame_coTab :
    ∀ (k l : ℕ) (n : ℕ × ℕ × ℕ), (L.coTab k l).Tame (IO n) (IO (n.1, n.2.1 + 2 * k, n.2.2 + k))
  | 0, _, n => Core.tame_id _ _
  | k + 1, l, n => (Core.Tame.seq (L.tame_coT n l) (tame_coTab k (l + 1) _)).conseq (fun _ h => h) fun x h => by
      have e : ((n.1, n.2.1 + 2 + 2 * k, n.2.2 + 1 + k) : ℕ × ℕ × ℕ) =
          (n.1, n.2.1 + 2 * (k + 1), n.2.2 + (k + 1)) :=
        Prod.ext rfl
          (Prod.ext (by show n.2.1 + 2 + 2 * k = n.2.1 + 2 * (k + 1); omega)
            (by show n.2.2 + 1 + k = n.2.2 + (k + 1); omega))
      exact e ▸ h

omit [NeZero (2 : E)] in
theorem tame_coL : L.coL.Tame (IO n) (IO (n.1 + 1, n.2.1 + 2, n.2.2 + 1)) :=
  show L.bL.Tame L.hL.Bad _ _
    from Block.Tame.on (L.prL.tame_core n) L.gxL L.pxL id (fun _ yo => yo) (Ja := IO n)
      (Jb := IO (n.1 + 1, n.2.1 + 2, n.2.2 + 1)) (fun _ h => h) fun _ _ _ h => h.addLin _

omit [NeZero (2 : E)] [Fintype N] [DecidableEq N] in
theorem tame_coB0 : L.coB0.Tame (IO n) (IO n) :=
  show L.bB0.Tame L.hB0.Bad _ _
    from Block.Tame.oneIf (r := Block.chalRound E (Fin L.par.gT → E)) (fun ϱ => nzT ϱ)
      (fun (x : LkX N E) ϱ _ => { x with C := 0, pt := nat ϱ }) _ fun _ _ _ h => h

omit [NeZero (2 : E)] in
theorem tame_coB : L.coB.Tame (IO n) (IO (n.1 + 1, n.2.1 + 2, n.2.2 + 1)) :=
  show L.bB.Tame L.hB.Bad _ _
    from Block.Tame.on (L.prB.tame_core n) gxPL pxB id (fun _ yo => yo) (Ja := IO n)
      (Jb := IO (n.1 + 1, n.2.1 + 2, n.2.2 + 1)) (fun _ h => h) fun _ _ _ h => h.addLin _

omit [NeZero (2 : E)] [DecidableEq E] [Fintype N] [DecidableEq N] in
theorem tame_co5 : L.co5.Tame (IO n) (IO n) :=
  show L.bDeg.Tame L.hDeg.Bad _ _
    from Block.Tame.oneAll (r := Block.chalRound E (Fin L.par.σ → E))
      (fun (x : LkX N E) ϱ _ => { x with p6 := nat ϱ }) _ fun _ _ _ h => h

omit [NeZero (2 : E)] [Fintype N] in
theorem tame_coUV : L.coUV.Tame (IO n) (IO n) :=
  show L.bUV.Tame L.hUV.Bad _ _
    from Block.Tame.oneIf (r := L.rUV) (fun ϱ => nzT ϱ)
      (fun x ϱ s => L.setUV x ϱ s) _ fun _ _ _ h => h

omit [NeZero (2 : E)] [DecidableEq E] [Fintype N] [DecidableEq N] in
theorem tame_coXi : L.coXi.Tame (IO n) (IO n) :=
  show L.bXi.Tame L.hXi.Bad _ _
    from Block.Tame.oneAll (r := Block.chalRound E (Fin (2 * L.par.Pm) → E))
      (fun (x : LkX N E) c _ => { x with cx := nat c }) _ fun _ _ _ h => h

omit [NeZero (2 : E)] in
theorem tame_coRs : L.coRs.Tame (IO n) (IO n) :=
  show L.bRs.Tame L.hRs.Bad _ _
    from Block.Tame.on (L.prR.tame_sc (fun ξ : LkX N E => ξ.led.Ord n) (lkVars L.par.σ) [])
      (fun x => ((0 : Form N E), fun _ => 0, x)) (fun x xo => { x with C := xo.1, pt := xo.2.1 }) id
      (fun _ yo => yo) (Ja := IO n) (Jb := IO n) (fun _ h => h) fun _ _ h _ => h

omit [NeZero (2 : E)] [Fintype E] [DecidableEq E] [Fintype N] [DecidableEq N] in
theorem length_os (x : LkX N E) : (L.os x).length = 3 * L.par.Pm := by simp [os]

omit [NeZero (2 : E)] [Fintype E] [DecidableEq E] [Fintype N] [DecidableEq N] in
theorem tame_coRec : L.coRec.Tame (IO n) (IO (n.1 + 1, n.2.1 + 3 * L.par.Pm, n.2.2 + 1)) :=
  show L.bRec.Tame L.hRec.Bad _ _ from Block.Tame.pure _ fun x h => ⟨_, if_pos h.1, by
    have h1 := (h.addRel (L.fR x) (L.ts_lt x)).addLin (L.fS x)
    rw [L.length_os] at h1
    exact h1⟩

/-- What the argument adds to the list. -/
def addsL : ℕ × ℕ × ℕ := (3, 2 * L.par.D + 2 * L.par.r + 4 + 3 * L.par.Pm, L.par.D + L.par.r + 3)

omit [NeZero (2 : E)] in
theorem tame_co14b :
    L.co14b.Tame (IO n) (IO (n.1 + 2, n.2.1 + 2 * L.par.r + 4, n.2.2 + L.par.r + 2)) :=
  (Core.Tame.seq (L.tame_coKe n)
        (Core.Tame.seq (L.tame_coT0 n)
          (Core.Tame.seq (L.tame_coTab L.par.r 0 n)
            (Core.Tame.seq (L.tame_coL _) (Core.Tame.seq (L.tame_coB0 _) (L.tame_coB _)))))).conseq
      (fun _ h => h) fun x h => by
    have e : ((n.1 + 1 + 1, n.2.1 + 2 * L.par.r + 2 + 2, n.2.2 + L.par.r + 1 + 1) : ℕ × ℕ × ℕ) =
        (n.1 + 2, n.2.1 + 2 * L.par.r + 4, n.2.2 + L.par.r + 2) := rfl
    exact e ▸ h

omit [NeZero (2 : E)] in
theorem tame_co6 : L.co6.Tame (IO n) (IO (n.1 + 1, n.2.1 + 3 * L.par.Pm, n.2.2 + 1)) :=
  Core.Tame.seq (L.tame_coUV n)
    (Core.Tame.seq (L.tame_coXi n) (Core.Tame.seq (L.tame_coRs n) (L.tame_coRec n)))

omit [NeZero (2 : E)] in
/-- The lookup argument: a well-formed list stays well-formed and gains `addsL`; for a well-formed
list the verifier rejects exactly on the public set `Bad`. -/
theorem tame_coLookup :
    L.coLookup.Tame (fun led => led.Ord n)
      (IO (n.1 + L.addsL.1, n.2.1 + L.addsL.2.1, n.2.2 + L.addsL.2.2)) :=
  (Core.Tame.seq
        (Core.Tame.seq (L.tame_coAl n)
          (Core.Tame.seq (L.tame_coZY n)
            (Core.Tame.seq (L.tame_coKey L.par.D 0 n) (L.tame_co14b _))))
        (Core.Tame.seq (L.tame_co5 _) (L.tame_co6 _))).conseq
      (fun _ h => h) fun x h => by
    have e : ((n.1 + 2 + 1,
          n.2.1 + 2 * L.par.D + 2 * L.par.r + 4 + 3 * L.par.Pm,
          n.2.2 + L.par.D + L.par.r + 2 + 1) : ℕ × ℕ × ℕ) =
        (n.1 + L.addsL.1, n.2.1 + L.addsL.2.1, n.2.2 + L.addsL.2.2) :=
      by
        unfold addsL
        refine Prod.ext rfl (Prod.ext ?_ ?_)
        · simp only
          omega
        · simp only
          omega
    exact e ▸ h

omit [NeZero (2 : E)] in
/-- The same, for 0 < D, for the form of the argument in which the last layer of the key side is a
separate part. -/
theorem tame_coLookupR (hD : 0 < L.par.D) :
    L.coLookupR.Tame (fun led => led.Ord n)
      (IO (n.1 + L.addsL.1, n.2.1 + L.addsL.2.1, n.2.2 + L.addsL.2.2)) :=
  (Core.Tame.seq
        (Core.Tame.seq (L.tame_coAl n)
          (Core.Tame.seq (L.tame_coZY n) (L.tame_coKey (L.par.D - 1) 0 n)))
        (Core.Tame.seq (L.tame_coK _ (L.par.D - 1))
          (Core.Tame.seq (L.tame_co14b _) (Core.Tame.seq (L.tame_co5 _) (L.tame_co6 _))))).conseq
      (fun _ h => h) fun x h => by
    have e : ((n.1 + 2 + 1,
          n.2.1 + 2 * (L.par.D - 1) + 2 + 2 * L.par.r + 4 + 3 * L.par.Pm,
          n.2.2 + (L.par.D - 1) + 1 + L.par.r + 2 + 1) : ℕ × ℕ × ℕ) =
        (n.1 + L.addsL.1, n.2.1 + L.addsL.2.1, n.2.2 + L.addsL.2.2) :=
      by
        unfold addsL
        refine Prod.ext rfl (Prod.ext ?_ ?_)
        · simp only
          omega
        · simp only
          omega
    exact e ▸ h

end Blocks.Lk
