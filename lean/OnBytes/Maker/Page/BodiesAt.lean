-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/BodiesAt.lean: the body into which a symbol of a whole file's stretch is written
(OnBytes/Flat/LeafBodies.lean, `scWhole`) is the string of its own tree's leaf.

OnBytes/Flat/LeafBodies.lean says for one tree what a body is (`emb1`, `emb1_fit`), and lays the
codes of the trees together: for a round with several trees (`embTs`), a stretch of rounds (`scT`),
a whole file (`scWhole`). Here it is said for the list: which tree and which leaf a position's body
bears, in the letters of the typing (`treeAt`, `leafAt`, `symT'`, OnBytes/Maker/TypingT.lean).

  `BodyIs bd sb C ds emb`   at a position q of a tree of the shape sh, and a column that types to
        the symbol y: the body of y, read as a string of bits by bd, is `emb1` at sh, at q's leaf
        and at the column.
  `embTs_at`      one round.
  `bodyIs_scT`    **a stretch**: `BodyIs` at `SCode.emb` of `scT`, with bd the identity.
  `emb_app_left`, `emb_app_right`   `SCode.emb` at two lists of codes laid behind each other,
        against `embL` and `embR` (OnBytes/TypedOracleCompiler/Joined/CutAfter.lean).
  `codeWhole`, `scWhole_eq`   six codes laid as `scWhole` lays them; `scWhole` is that, at `scT` for
        the three stretches.
  `symb₁_whole`, `symb₂_whole`, `symb₃_whole`   **a whole file**: how the symbols of chain 1's, 2's,
        3's stretch are written (`symb₁`, `symb₂`, `symb₃`, OnBytes/TypedOracleCompiler/Joined/YesByCuts.lean) at
        `SCode.emb` of `codeWhole` is `SCode.emb` of that stretch's own code.

Not claimed. What the bits of `emb1` are (`emb1_fit`). Nothing on any hash; nothing on soundness.


-/
import OnBytes.Maker.TypingTLaws
import OnBytes.Flat.LeafBodies
import OnBytes.TypedOracleCompiler.Joined.YesByCuts

set_option autoImplicit false

namespace OnBytes.Maker.Page

open OnBytes.Maker OnBytes.Flat TypedOracleCompiler.Iop TypedOracleCompiler.Joined TypedOracleCompiler.Compile.Batch
open _root_.Compile.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ

/-- **The body of a symbol at a position is the string of its own tree's leaf.** -/
def BodyIs {Bd : Type} (bd : Bd → List Bool) (sb : ℕ) (C : CK) (ds : List RDT)
    (emb : (p : OPos (uLT C ds)) → OSym (uLT C ds) p → Bd) : Prop :=
  ∀ q sh col y, treeShT ds (treeAt C ds q) = some sh → symT' C ds q col = some y →
    ∃ (x : Fin (2 ^ sh.a)) (colF : Fin sh.W → UInt64), x.val = leafAt C ds q ∧
      List.ofFn colF = col ∧ bd (emb q y) = emb1 sb (some sh) x colF

/-- One round. -/
theorem embTs_at (sb : ℕ) : ∀ (ts : List Fmt.Shape) (p : PosT ts) (sh : Fmt.Shape)
    (col : List UInt64) (y : SymT ts p), ts[treeIn ts p]? = some sh → symIn ts p col = some y →
    ∃ (x : Fin (2 ^ sh.a)) (colF : Fin sh.W → UInt64), x.val = leafIn ts p ∧
      List.ofFn colF = col ∧ embTs sb ts p y = emb1 sb (some sh) x colF
  | s :: _, .inl x, sh, col, y, hs, hy => by
    obtain rfl : s = sh := Option.some.inj hs
    have hy' : (if h : col.length = s.W then
        some (fun i : Fin s.W => col[i.val]'(by rw [h]; exact i.isLt)) else none) = some y := hy
    by_cases hc : col.length = s.W
    · rw [dif_pos hc] at hy'
      obtain rfl := Option.some.inj hy'
      refine ⟨x, _, rfl, ?_, rfl⟩
      apply List.ext_getElem
      · rw [List.length_ofFn, hc]
      · intro i h1 h2
        rw [List.getElem_ofFn]
    · rw [dif_neg hc] at hy'
      cases hy'
  | _ :: ts, .inr p, sh, col, y, hs, hy =>
    embTs_at sb ts p sh col y (by simpa [treeIn] using hs) hy

/-- **A stretch.** -/
theorem bodyIs_scT (sb : ℕ) (C : CK) : ∀ ds : List RDT,
    BodyIs (fun b : List Bool => b) sb C ds (SCode.emb (uLT C ds) (scT sb C ds))
  | [], q, _, _, _, _, _ => nomatch q
  | d :: ds, .inl p, sh, col, y, hs, hy => by
    have hs' : (if treeIn d.trees p < d.trees.length then d.trees[treeIn d.trees p]? else
        treeShT ds (treeIn d.trees p - d.trees.length)) = some sh := hs
    rw [if_pos (treeIn_lt d.trees p)] at hs'
    exact embTs_at sb d.trees p sh col y hs' hy
  | d :: ds, .inr q, sh, col, y, hs, hy => by
    have hs' : (if d.trees.length + treeAt C ds q < d.trees.length then
        d.trees[d.trees.length + treeAt C ds q]? else
        treeShT ds (d.trees.length + treeAt C ds q - d.trees.length)) = some sh := hs
    rw [if_neg (by omega), Nat.add_sub_cancel_left] at hs'
    exact bodyIs_scT sb C ds q sh col y hs' hy

/-! ## Two lists of codes laid behind each other -/

section App
variable {I X : Type} {L : BatchProtocolWithLeafBody I X}

theorem emb_app_left : ∀ (s u : Shape) (cs : SCode (Body L) s) (cu : SCode (Body L) u),
    embL (L := L) (s := s) (u := u) (SCode.emb (s ++ u) (SCode.app s u cs cu)) = SCode.emb s cs
  | [], _, _, _ => funext fun p => nomatch p
  | _ :: s, u, (c, cs), cu => funext fun p => by
    match p with
    | .inl p => rfl
    | .inr q => exact congrFun (emb_app_left s u cs cu) q

theorem emb_app_right : ∀ (s u : Shape) (cs : SCode (Body L) s) (cu : SCode (Body L) u),
    embR (L := L) (s := s) (u := u) (SCode.emb (s ++ u) (SCode.app s u cs cu)) = SCode.emb u cu
  | [], _, _, _ => rfl
  | _ :: s, u, (_, cs), cu => emb_app_right s u cs cu

end App

/-! ## A whole file -/

/-- The codes of a whole file's rounds, laid as `scWhole` lays them. -/
def codeWhole {Bd : Type} (G : Chains) (cF : RCode Bd G.rF) (c1 : SCode Bd G.s₁)
    (cJ : RCode Bd G.rJ) (c2 : SCode Bd G.s₂) (c3r : RCode Bd G.r3) (c3 : SCode Bd G.s₃) :
    SCode Bd G.sh :=
  (cF, SCode.app _ _ c1 (cJ, SCode.app _ _ c2 (c3r, c3)))

/-- `scWhole` is that, at `scT` for the three stretches. -/
theorem scWhole_eq (sb : ℕ) (C : CK) (D : WholeD) {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3) :
    scWhole sb C D tF tJ t3 =
      codeWhole (chainsOf C D tF tJ t3) (RCode.none _ _ fun p => p) (scT sb C D.ds₁)
        (RCode.none _ _ fun p => p) (scT sb C D.ds₂) (RCode.none _ _ fun p => p)
        (scT sb C D.ds₃) := rfl

section Whole
variable {I X : Type} {L : BatchProtocolWithLeafBody I X} (G : Chains) (cF : RCode (Body L) G.rF)
  (c1 : SCode (Body L) G.s₁) (cJ : RCode (Body L) G.rJ) (c2 : SCode (Body L) G.s₂)
  (c3r : RCode (Body L) G.r3) (c3 : SCode (Body L) G.s₃)

/-- What stands behind chain 1's rounds. -/
theorem embR_whole :
    embR (L := L) (s := G.c₁) (u := G.c₂ ++ G.c₃)
        (SCode.emb G.sh (codeWhole G cF c1 cJ c2 c3r c3)) =
      SCode.emb G.shJ (cJ, SCode.app _ _ c2 (c3r, c3)) :=
  emb_app_right G.s₁ G.shJ c1 (cJ, SCode.app _ _ c2 (c3r, c3))

theorem symb₁_whole :
    (fun p => symb₁ (G := G) (SCode.emb G.sh (codeWhole G cF c1 cJ c2 c3r c3)) (.inr p)) =
      SCode.emb G.s₁ c1 :=
  emb_app_left G.s₁ G.shJ c1 (cJ, SCode.app _ _ c2 (c3r, c3))

theorem symb₂_whole :
    (fun p => symb₂ (G := G) (SCode.emb G.sh (codeWhole G cF c1 cJ c2 c3r c3)) (.inr p)) =
      SCode.emb G.s₂ c2 := by
  unfold symb₂
  rw [embR_whole]
  exact emb_app_left G.s₂ G.sh₃ c2 (c3r, c3)

theorem symb₃_whole :
    (fun p => symb₃ (G := G) (SCode.emb G.sh (codeWhole G cF c1 cJ c2 c3r c3)) (.inr p)) =
      SCode.emb G.s₃ c3 := by
  unfold symb₃
  rw [embR_whole]
  have e : embR (L := L) (s := G.c₂) (u := G.c₃)
      (SCode.emb G.shJ (cJ, SCode.app _ _ c2 (c3r, c3))) = SCode.emb G.sh₃ (c3r, c3) :=
    emb_app_right G.s₂ G.sh₃ c2 (c3r, c3)
  rw [e]
  rfl

end Whole

end OnBytes.Maker.Page
