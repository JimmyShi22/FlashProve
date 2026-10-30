-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/StaysAt.lean: THE TWO PREMISES hy | hyF OF `hF_of_door` AND `hCar_ren`
(HFOfDoor.lean, HCarRen.lean: the strings behind the closing and in front of it agree on the
members' seats' trees and on the fresh mask's tree) AND THE CLAUSES «THE READING BY KEY IS Strs.col»
(`PlanAt`'s fourth, FrontFitsOf.lean; hforc), BY CALLS. Theorems. It changes no other file.

  `cols_stay_out`: **a piece's accepting transcript leads from a to a' ⊢ the column at every leaf of
    every tree below the piece's base is the same off a'.2 and off a.2**: by `out_strs`
    (OracleRides.lean) and `stays_behind` (Johnson/Top/H0/Walk/StaysBehind.lean).
  `hy_of_out`, `hyF_of_out`: so hy where each member's seat's tree is below the base; hyF where the
    fresh mask's tree is.
  `orcY_at`: where L is the first tree of the list with the key k, the reading at k
    (`K2.orcY`, Johnson/Top/H0/K2Hears/OrcStrs.lean) is Strs.col at L.no: by unfolding.
  `fresh_tree`: **the fresh mask's tree, named**: where the plan's list places the fresh mask in the
    tree tpF, tpF is below the base, L is the first tree of the frame's list with the key tpF, and
    keys below the base belong to trees below the base (another file's premise hKey,
    Walk/FrameCarryFenceEnds.lean): tree := L.no has hforc and is below the base.
Limits. «Below the base» at the members' seats is a premise (the table's fence test gives it at the
sampled tenants that are open: `fenceFit_at`, Johnson/Desc/First/FenceFit.lean: not called here).
Nothing on soundness.
-/
import Johnson.Desc.First.Link.Law.OracleRides
import Johnson.Top.H0.Walk.StaysBehind
import Johnson.Top.H0.K2Hears.OrcStrs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc (Strs)
open VerifiableInference.Desc.Sound
open _root_.Run.PQ (CK)
open _root_.Johnson.Desc.First.Walk.Tied (stays_behind)

/-- **THE TREES BELOW A PIECE's BASE STAY.** -/
theorem cols_stay_out {C : CK} {F : Frame} {T Cl W : Type} {p : Piece C F T Cl W}
    {a a' : T × F.E.Str} {τ : Iop.Tr (uLT C p.ds)} (h : p.ior.red.out a τ = some a') (j x : ℕ)
    (hj : j < p.base) : (strsOf F a'.2).col j x = (strsOf F a.2).col j x := by
  rw [out_strs h]
  exact (stays_behind C F p.base p.ds a.2 τ).2 j x hj

theorem hy_of_out {C : CK} {F : Frame} {T Cl W : Type} {p : Piece C F T Cl W}
    {a a' : T × F.E.Str} {τ : Iop.Tr (uLT C p.ds)} (h : p.ior.red.out a τ = some a') {n : ℕ}
    (seat : Fin n → ℕ × ℕ) (hs : ∀ i, (seat i).1 < p.base) (i : Fin n) (x : ℕ) :
    (strsOf F a'.2).col (seat i).1 x = (strsOf F a.2).col (seat i).1 x :=
  cols_stay_out h _ x (hs i)

theorem hyF_of_out {C : CK} {F : Frame} {T Cl W : Type} {p : Piece C F T Cl W}
    {a a' : T × F.E.Str} {τ : Iop.Tr (uLT C p.ds)} (h : p.ior.red.out a τ = some a') {tree : ℕ}
    (ht : tree < p.base) (x : ℕ) :
    (strsOf F a'.2).col tree x = (strsOf F a.2).col tree x := cols_stay_out h _ x ht

/-- The reading by key, where the list's first tree with that key is known. -/
theorem orcY_at {all : List LeftT} {key : ℕ → ℕ} {k : ℕ} {L : LeftT}
    (h : all.find? (fun L => key L.no == k) = some L) (Y : Strs) (x : ℕ) :
    First.K2.orcY all key Y k x = Y.col L.no x := by
  unfold First.K2.orcY
  rw [h]

/-- **THE FRESH MASK's TREE, NAMED.** -/
theorem fresh_tree {all : List LeftT} {key : ℕ → ℕ} {base tpF : ℕ} {L : LeftT}
    (hKey : ∀ k L, k < base → all.find? (fun L => key L.no == k) = some L → L.no < base)
    (ht : tpF < base) (h : all.find? (fun L => key L.no == tpF) = some L) (Y : Strs) :
    L.no < base ∧ ∀ x, First.K2.orcY all key Y tpF x = Y.col L.no x :=
  ⟨hKey tpF L ht h, fun x => orcY_at h Y x⟩

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.cols_stay_out
#print axioms VerifiableInference.Desc.LinkJoin.hy_of_out
#print axioms VerifiableInference.Desc.LinkJoin.hyF_of_out
#print axioms VerifiableInference.Desc.LinkJoin.orcY_at
#print axioms VerifiableInference.Desc.LinkJoin.fresh_tree
