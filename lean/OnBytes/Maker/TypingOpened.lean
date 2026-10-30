-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/TypingOpened.lean: tools for the form of the openings in the typing of a whole file,
chain by chain.

OnBytes/TypedOracleCompiler/Joined/K/YesRead.lean asks, for each chain's rounds, the record `Opened`: an opening
stands only at a position that is read and whose tree has a root, with a salt of sMT bits; each
position that is read has an opening; the path of an opening that is read is as long as its tree is
deep. From such records it has the strict format, the forests and the checks' form. This file gives
the record at a silent round and a stretch of written rounds, at the sMT of the premise `OpensFit`.

  `wire₁_qb`, `wire₂_qb`, `wire₃_qb`   each chain's share of a file's wire record.
  `treeOf_lo`, `treeOf_sh`            under `SentLo` | `SentSh` the tree of a position has a root,
                                    and its depth is its shape's.
  `opened_lo`, `opened_sh`            `Opened` at a silent round and a stretch, from `OpensFit`
                                    (OnBytes/Maker/OpensFit.lean).

OnBytes/Maker/TypingAlike.lean has the four records at a value of `typeFile`
(`opened_typeFileA`).

Not claimed. `OpensFit`, `SentLo`, `SentSh` at any value. That a path leads to a root. Nothing on
soundness.


-/
import OnBytes.Maker.OpensFit
import OnBytes.Maker.TypingHolds
import OnBytes.TypedOracleCompiler.Joined.K.YesRead

set_option autoImplicit false

namespace OnBytes.Maker

open TypedOracleCompiler.Iop TypedOracleCompiler.Joined TypedOracleCompiler.Compile.Batch _root_.Compile.Joined Rom
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile (Opening)
open _root_.Run _root_.Run.PQ

/-! ## Each chain's share of a file's wire record -/

section Wires
variable {lam K : ℕ} {G : Chains} {Y : Type} {E : ExtSpec} (V : Wires lam K G) (D : Desc G Y E)
  (ext : WireE E) (decO : DecidableEq (OPos G.sh)) (n m : ℕ)

theorem wire₁_qb : wire₁ (V.qb D ext decO n m) = (V.wF, V.W₁) := by
  show (V.wF, WireSB.fst (WireSB.app V.W₁ V.shJ)) = _
  rw [WireSB.fst_app]

theorem wire₂_qb : wire₂ (V.qb D ext decO n m) = (V.wJ, V.W₂) := by
  show WireSB.fst (s := G.c₂) (u := G.c₃) (A := G.A₂) (B := G.A₃)
    (WireSB.snd (s := G.s₁) (WireSB.app V.W₁ V.shJ)) = _
  rw [WireSB.snd_app]
  show (V.wJ, WireSB.fst (WireSB.app V.W₂ V.sh₃)) = _
  rw [WireSB.fst_app]

theorem wire₃_qb : wire₃ (V.qb D ext decO n m) = (V.w3, V.W₃) := by
  show WireSB.snd (s := G.c₂) (u := G.c₃) (A := G.A₂) (B := G.A₃)
    (WireSB.snd (s := G.s₁) (WireSB.app V.W₁ V.shJ)) = _
  rw [WireSB.snd_app]
  show WireSB.snd (s := G.s₂) (WireSB.app V.W₂ V.sh₃) = _
  rw [WireSB.snd_app]
  rfl

end Wires

/-! ## The tree of a position -/

section Stretch
variable (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)

theorem treeOf_lo :
    ∀ (ds : List RDT) (R : RootsOfChain 256 (uLT C ds)) (q : OPos (uLT C ds)), SentLo C ds R →
      ∃ sh c, treeShT ds (treeAt C ds q) = some sh ∧
        treeOf (uLT C ds) (RoundSplits.allLocal (uLT C ds)) (wiresLo C K chal ds) R q = some (sh.a, c)
  | d :: ds, (rt, R), .inl p, ⟨⟨l, hl, hn⟩, _⟩ => by
      have hk : treeIn d.trees p < d.trees.length := treeIn_lt d.trees p
      refine ⟨d.trees[treeIn d.trees p], l[treeIn d.trees p]'(hn ▸ hk), ?_, ?_⟩
      · show (if treeIn d.trees p < d.trees.length then d.trees[treeIn d.trees p]? else _) = _
        rw [if_pos hk, List.getElem?_eq_getElem hk]
      · show TypedOracleCompiler.Joined.treeAt (d.trees.map (·.a)) (rt.2.getD []) (treeT d.trees p) = _
        rw [hl, ← treeIn_eq]
        exact treeAt_of (by rw [List.getElem?_map, List.getElem?_eq_getElem hk]; rfl)
          (List.getElem?_eq_getElem _)
  | d :: ds, (rt, R), .inr q, ⟨_, h⟩ => by
      obtain ⟨sh, c, h1, h2⟩ := treeOf_lo ds R q h
      refine ⟨sh, c, ?_, h2⟩
      show (if d.trees.length + treeAt C ds q < d.trees.length then _ else
        treeShT ds (d.trees.length + treeAt C ds q - d.trees.length)) = _
      rw [if_neg (by omega), Nat.add_sub_cancel_left]
      exact h1

theorem treeOf_sh :
    ∀ (ds : List RDT) (R : RootsOfChain 256 (uLT C ds)) (q : OPos (uLT C ds)), SentSh C ds R →
      ∃ sh c, treeShT ds (treeAt C ds q) = some sh ∧
        treeOf (uLT C ds) (RoundSplits.const (RAnn.ofShared .sh) (uLT C ds)) (wiresSh C K chal ds) R q =
          some (sh.a, c)
  | d :: ds, (rt, R), .inl p, ⟨⟨l, hl, hn⟩, _⟩ => by
      have hk : treeIn d.trees p < d.trees.length := treeIn_lt d.trees p
      refine ⟨d.trees[treeIn d.trees p], l[treeIn d.trees p]'(hn ▸ hk), ?_, ?_⟩
      · show (if treeIn d.trees p < d.trees.length then d.trees[treeIn d.trees p]? else _) = _
        rw [if_pos hk, List.getElem?_eq_getElem hk]
      · show TypedOracleCompiler.Joined.treeAt (d.trees.map (·.a)) (rt.1.getD []) (treeT d.trees p) = _
        rw [hl, ← treeIn_eq]
        exact treeAt_of (by rw [List.getElem?_map, List.getElem?_eq_getElem hk]; rfl)
          (List.getElem?_eq_getElem _)
  | d :: ds, (rt, R), .inr q, ⟨_, h⟩ => by
      obtain ⟨sh, c, h1, h2⟩ := treeOf_sh ds R q h
      refine ⟨sh, c, ?_, h2⟩
      show (if d.trees.length + treeAt C ds q < d.trees.length then _ else
        treeShT ds (d.trees.length + treeAt C ds q - d.trees.length)) = _
      rw [if_neg (by omega), Nat.add_sub_cancel_left]
      exact h1

/-! ## A silent round and a stretch -/

variable {T : Type} (t : T) (a0 : RAnn (plainRound T t))
  (w0 : WireRB 256 (K + 1) (plainRound T t) a0) (ds : List RDT) (base : ℕ)
  (tabs : List (ℕ × List (ℕ × Row3))) (sMT : ℕ) (R : RootsOfChain 256 (plainRound T t :: uLT C ds))
  (rd : OPos (plainRound T t :: uLT C ds) → Bool)

theorem opened_lo (hS : SentLo C ds R.2)
    (hfit : OpensFit C ds base tabs sMT fun q => rd (.inr q) = true) :
    TypedOracleCompiler.Joined.Opened sMT (plainRound T t :: uLT C ds) (a0, RoundSplits.allLocal (uLT C ds))
      (w0, wiresLo C K chal ds) R rd (behind t (opensT C ds base tabs)) where
  only := fun p op h => by
    match p, op, h with
    | .inr q, op, h =>
      obtain ⟨h1, h2⟩ := hfit.only q op h
      obtain ⟨sh, c, -, h3⟩ := treeOf_lo C K chal ds R.2 q hS
      refine ⟨h1, h2, ?_⟩
      show (treeOf (uLT C ds) (RoundSplits.allLocal (uLT C ds)) (wiresLo C K chal ds) R.2 q).isSome = true
      rw [h3]
      rfl
  all := fun p h => by
    match p, h with
    | .inr q, h => exact hfit.all q h
  path := fun p op d c _ h ht => by
    match p, op, h, ht with
    | .inr q, op, h, ht =>
      obtain ⟨sh, c', h1, h3⟩ := treeOf_lo C K chal ds R.2 q hS
      have e : some (sh.a, c') = some (d, c) := h3.symm.trans ht
      obtain rfl : sh.a = d := congrArg Prod.fst (Option.some.inj e)
      exact hfit.path q op sh h h1

theorem opened_sh (hS : SentSh C ds R.2)
    (hfit : OpensFit C ds base tabs sMT fun q => rd (.inr q) = true) :
    TypedOracleCompiler.Joined.Opened sMT (plainRound T t :: uLT C ds)
      (a0, RoundSplits.const (RAnn.ofShared .sh) (uLT C ds)) (w0, wiresSh C K chal ds) R rd
      (behind t (opensT C ds base tabs)) where
  only := fun p op h => by
    match p, op, h with
    | .inr q, op, h =>
      obtain ⟨h1, h2⟩ := hfit.only q op h
      obtain ⟨sh, c, -, h3⟩ := treeOf_sh C K chal ds R.2 q hS
      refine ⟨h1, h2, ?_⟩
      show (treeOf (uLT C ds) (RoundSplits.const (RAnn.ofShared .sh) (uLT C ds)) (wiresSh C K chal ds)
        R.2 q).isSome = true
      rw [h3]
      rfl
  all := fun p h => by
    match p, h with
    | .inr q, h => exact hfit.all q h
  path := fun p op d c _ h ht => by
    match p, op, h, ht with
    | .inr q, op, h, ht =>
      obtain ⟨sh, c', h1, h3⟩ := treeOf_sh C K chal ds R.2 q hS
      have e : some (sh.a, c') = some (d, c) := h3.symm.trans ht
      obtain rfl : sh.a = d := congrArg Prod.fst (Option.some.inj e)
      exact hfit.path q op sh h h1

end Stretch

end OnBytes.Maker
