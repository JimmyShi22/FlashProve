-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/ViewOp.lean: THE COLUMN THAT THE TYPED TRANSCRIPT HOLDS AT (TREE, PLACE) IS THE
COLUMN OF THE OPENING THAT THE TYPED STRING HAS AT THAT POSITION: AT ANY TABLE OF TYPED OPENINGS.
The step from a typing's table to Run/ViewERead.lean's hypothesis hcol. A piece of "the tie at H_b"
(LinkE | LinkF).
The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on
definitions of Compile/.
WHY (Run/ViewERead.lean's head: "hcol AT A TYPING's TABLES … wants: colAtS at trL … op is op's
symbol's column at the position that posAtS names, where a root was sent"). OnBytes/TypedOracleCompiler's colAtS_tr
(Run/PageIsViewProofs.lean) says it AT THE PARSER's TABLE (opL C tbl run ds: a look-up by the tree's
number in a table with ONE opening a tree). The lax verifier's typed string has whole paths and
another table; THE VIEW LOOKS AT THE SYMBOLS ALONE.
  colS C ds q s      the column of a symbol s at the position q of a list of written rounds (colT at
                     q's own round)
  colAtS_op      colAtS_tr's TEXT WITHOUT THE TABLE: if as many roots were read in each round as it
                 has trees (SentR), posAtS C ds n y = some q and op q = some z: colAtS C ds (trL C K
                 chal ds (rtSL C ds ros) pl ρ op) n y = some (colS C ds q z.sym). op IS ANY; salt
                 and path of z are not looked at
  hcol_of_op     so ViewERead's hcol follows from: every (tree, place, column) that the reader lists
                 has a position q by posAtS, an opening at q in the typed string, and that opening's
                 symbol spells the listed column
WHAT IS NOT SAID. That a typing's table has these openings (with ViewERead's lookup_agree |
lookup_or_clash: the typing's own matter). The stored tables' strings (hy).

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Run.ViewERead

set_option autoImplicit false

namespace TypedOracleCompiler.Run.PQ
open Rom TypedOracleCompiler.Iop _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Run.Twin
  TypedOracleCompiler.Run.Thin
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ TypedOracleCompiler.Run
open _root_.Run.Twin (allLo)
open _root_.Fmt (RoundOut)

/-- the column of a symbol at a position of a list of written rounds -/
def colS (C : CK) : (ds : List RD) → (q : OPos (uL C ds)) → OSym (uL C ds) q → List UInt64
  | [], q, _ => q.elim
  | d :: _, .inl p, s => colT d.trees p s
  | _ :: ds, .inr q, s => colS C ds q s

section
variable (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)

/-- At any table of typed openings: the transcript's column is the opening's. -/
theorem colAtS_op :
    ∀ (ds : List RD) (ros : List RoundOut) (pl : Plains (uL C ds)) (ρ : Rho (uL C ds))
        (op : (p : OPos (uL C ds)) → Option (Opening 256 (OSym (uL C ds) p))) (n y : ℕ)
            (q : OPos (uL C ds))
        (z : Opening 256 (OSym (uL C ds) q)),
      List.Forall₂ SentR ds ros → posAtS C ds n y = some q → op q = some z →
        colAtS C ds (trL C K chal ds (rtSL C ds ros) pl ρ op) n y = some (colS C ds q z.sym)
  | [], _, _, _, _, _, _, q, _, _, _, _ => q.elim
  | d :: ds, _, (p, pl), (c0, ρ), op, n, y, q, z, hs, hq, hop => by
      cases hs with
      | @cons _ ro _ ros h0 hs' =>
        have hq0 : (if n < d.trees.length then (posAtT d.trees n y).map Sum.inl
            else (posAtS C ds (n - d.trees.length) y).map Sum.inr) = some q := hq
        by_cases hn : n < d.trees.length
        · rw [if_pos hn] at hq0
          obtain ⟨q0, hq1, rfl⟩ := Option.map_eq_some_iff.1 hq0
          have hroot : rootP (roundS C d) (roundS C d).lo (wireS C K chal d).tree
                ((none, some ((_root_.Fmt.rootsOf ro.vals).map bytesToDig)) : RtC 256 × RtC 256)
                q0 = true := by
            show ((((_root_.Fmt.rootsOf ro.vals).map bytesToDig))[treeT d.trees q0]?).isSome = true
            rw [(place_posAtT d.trees n y q0 hq1).1, List.getElem?_map, Option.isSome_map,
              List.getElem?_eq_getElem (by rw [← h0.1]; exact hn)]
            rfl
          have key := trP_head (roundS C d) (SL C ds) (roundS C d).lo (allLo (SL C ds))
            (wireS C K chal d) (wiresSL C K chal ds)
            (none, some ((_root_.Fmt.rootsOf ro.vals).map bytesToDig)) (rtSL C ds ros)
            p pl c0 ρ op q0 z hroot hop
          show (if n < d.trees.length then
              (posAtT d.trees n y).map fun p' => colT d.trees p'
                ((trL C K chal (d :: ds) (rtSL C (d :: ds) (ro :: ros)) (p, pl) (c0, ρ) op).1.1 p')
            else _) = some (colT d.trees q0 z.sym)
          rw [if_pos hn, hq1]
          exact congrArg some (congrArg (colT d.trees q0) key)
        · rw [if_neg hn] at hq0
          obtain ⟨q1, hq1, rfl⟩ := Option.map_eq_some_iff.1 hq0
          have ih := colAtS_op ds ros pl ρ (fun q => op (.inr q)) (n - d.trees.length) y
              q1 z hs' hq1 hop
          show (if n < d.trees.length then _
              else
                colAtS C ds (trL C K chal ds (rtSL C ds ros) pl ρ fun q => op (.inr q))
                  (n - d.trees.length) y) = some (colS C ds q1 z.sym)
          rw [if_neg hn]
          exact ih

/-- ViewERead's hcol, from the typed string's openings. -/
theorem hcol_of_op (ds : List RD) (ros : List RoundOut) (pl : Plains (uL C ds)) (ρ : Rho (uL C ds))
    (op : (p : OPos (uL C ds)) → Option (Opening 256 (OSym (uL C ds) p))) (firstTree : ℕ)
    (hs : List.Forall₂ SentR ds ros)
    (h : ∀ ro ∈ ros, ∀ x ∈ ro.opens, ∀ zc ∈ x.2.1.zip x.2.2.cols,
      ∃ (q : OPos (uL C ds)) (z : Opening 256 (OSym (uL C ds) q)),
        posAtS C ds (x.1.tree - firstTree) zc.1 = some q ∧ op q = some z ∧
            colS C ds q z.sym = zc.2) :
    ∀ ro ∈ ros, ∀ x ∈ ro.opens, ∀ zc ∈ x.2.1.zip x.2.2.cols,
      colAtS C ds (trL C K chal ds (rtSL C ds ros) pl ρ op) (x.1.tree - firstTree)
          zc.1 = some zc.2 := by
  intro ro hro x hx zc hm
  obtain ⟨q, z, hq, hop, hc⟩ := h ro hro x hx zc hm
  rw [colAtS_op C K chal ds ros pl ρ op _ _ q z hs hq hop, hc]

end

end TypedOracleCompiler.Run.PQ
