-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/At/Symbols.lean: if the job fits its place and RidesZero holds, the symbols of the
honest sender's rows are the instance's symbols; and a tree's column at a position is determined by
the symbols of the tree's rows at that position.
Terms: Johnson/SendSim/At/Sim.lean; for the model's symbol, Johnson/SendSim/Defs.lean; sender,
readC, dataOf, entry, RidesZero: Johnson/SendSim/At/Bridge.lean. Limits of the folder:
Johnson/SendSim/Defs.lean.

What this file proves. Algebra and lists; no distribution is named.
  symOf_eq   If the job fits its place (sendFits) and RidesZero (a table that is sent along has
             entries 0 in its 2 ^ h rows if its coins are all 0) holds: the symbol symOf of a row ρ
             of rowsR data c at a position x is the instance's symAt at dataOf data and readC c, at
             ρ and the evaluation point of x.
  symOf_sym  For every family of rows V, symOf is the model's symbol (sym) of the row's entries
             entry V ρ and tailEntry V ρ. No premise.
  col_congr  The column of tree τ at a position x (col) is the same for two families of rows whose
             symOf agree at x for every row in τ. No premise. mainSyms_congr and maskSyms_congr say
             it of one oracle message's main and mask rows.

Limits. RidesZero is a premise of symOf_eq; it holds for every ride (ridesZero,
Johnson/SendSim/At/RideLay.lean).

How it fits. Johnson/SendSim/At/Shown.lean uses symOf_eq and col_congr for shownTie, which serves
rowsExact (Johnson/SendSim/At/RowsExact.lean) and rowsFresh (Johnson/SendSim/At/RowsFresh.lean). The
proofs rest on symG_crd, symF_eq and symG_mod (Johnson/SendSim/Tie/SymF.lean), sym_congr
(Johnson/SendSim/Tie/Sym.lean), and entry_split and tail_split (Johnson/SendSim/At/Split.lean). col,
symF and Rows are defined in Johnson/Prover/Send/Core.lean, sym in Johnson/LinkSim/Tail.lean.

The other names.
  symOf      a row's symbol at a position, read over the base field: a coordinate of the library's
             symG, or the library's symF.
  dg_three, dg_one   dg P k is 3 if the main rows are over the extension field, else 1.
-/
import Johnson.SendSim.At.Split

set_option autoImplicit false

namespace OnBytes.SendSim.At
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc OnBytes.LinkSim
open Johnson.Prover.Send (Rows shapeAt col mainSyms maskSyms symF)
open Johnson.Prover.Link (symG words3)

variable (P : K1.Par) (ride : Nat → Option Ride)

/-- The symbol of the row ρ at the position x, read over the base field, where V gives the rows of
each oracle message: a coordinate of the library's symG, or, for a main row over the base field, the
library's symF. -/
noncomputable def symOf (V : ℕ → Rows) (ρ : RowN P) (x : ℕ) : GF :=
  match ρ.2 with
  | .inl (r, t) =>
    if (shapeAt P ρ.1).mainDeg == 3 then
      crd (co t.val) (symG (codeAt P ρ) x ((V ρ.1).mainE r.val) ((V ρ.1).mainTlE r.val))
    else symF (codeAt P ρ) x ((V ρ.1).mainF r.val) ((V ρ.1).mainTlF r.val)
  | .inr (r, t) => crd t (symG (codeAt P ρ) x ((V ρ.1).mask r.val) ((V ρ.1).maskTl r.val))

/-- symOf is the model's symbol sym, at the evaluation point of x in the row's code, of the row's
message entry P V ρ and its tail tailEntry P V ρ. -/
theorem symOf_sym (V : ℕ → Rows) (ρ : RowN P) (x : ℕ) :
    symOf P V ρ x =
      sym (codeAt P ρ).r (codeAt P ρ).l (ptF (codeAt P ρ).a x) (entry P V ρ) (tailEntry P V ρ) := by
  obtain ⟨k, v⟩ := ρ
  rcases v with ⟨r, t⟩ | ⟨r, t⟩
  · unfold symOf entry tailEntry
    by_cases h3 : ((shapeAt P k).mainDeg == 3) = true
    · simp only [h3, if_true]
      exact symG_crd _ _ _ _ _
    · simp only [h3, Bool.false_eq_true, if_false]
      exact symF_eq _ _ _ _
  · exact symG_crd _ _ _ _ _

variable (data : Nat → Nat → Nat → Option (GF ⊕ GE)) (c : Cs (dueR P ride))

/-- If the job fits its place (sendFits) and RidesZero holds, the symbol of a row of rowsR data c at
x is the instance's symbol symAt at dataOf data and readC c, at the row and the evaluation point of
x. -/
theorem symOf_eq (hf : sendFits P ride = true) (hR : RidesZero ride) (ρ : RowN P) (x : ℕ) :
    symOf P (rowsR P ride data c) ρ x =
      (sender P ride).symAt (dataOf P ride data) (readC P ride c) (ρ, ptF (codeAt P ρ).a x) := by
  rw [symOf_sym]
  refine sym_congr _ _ _ (fun j _ => entry_split P ride c data hf hR ρ j) fun q hq => ?_
  rw [tail_split P ride c data ρ ⟨q, hq⟩]
  exact (tl_lt _ hq).symm

/-! ## A tree's column is a function of its rows' symbols -/

theorem dg_three {k : ℕ} (h3 : ((shapeAt P k).mainDeg == 3) = true) : dg P k = 3 := by
  simp [dg, h3]

theorem dg_one {k : ℕ} (h3 : ¬ ((shapeAt P k).mainDeg == 3) = true) : dg P k = 1 := by
  simp [dg, h3]

/-- The symbols of the main rows of oracle message k at a position x (mainSyms) are the same for two
families of rows whose symOf agree at x for every main row of k. -/
theorem mainSyms_congr (V V' : ℕ → Rows) (k : Fin P.sent.size) (x : ℕ)
    (h : ∀ v, symOf P V ⟨k, .inl v⟩ x = symOf P V' ⟨k, .inl v⟩ x) :
    mainSyms P V k x = mainSyms P V' k x := by
  unfold mainSyms
  refine congrArg List.flatten (List.map_congr_left fun r hr => ?_)
  have hr' : r < (shapeAt P k).mainRows := List.mem_range.1 hr
  by_cases h3 : ((shapeAt P k).mainDeg == 3) = true
  · simp only [h3, if_true]
    refine congrArg (fun y => words3 (ofE y)) (ext_crd fun t => ?_)
    have := h (⟨r, hr'⟩, ⟨t.val, by rw [dg_three P h3]; exact t.isLt⟩)
    unfold symOf at this
    simp only [h3, if_true, co_fin] at this
    exact this
  · simp only [h3, Bool.false_eq_true, if_false]
    have := h (⟨r, hr'⟩, ⟨0, by rw [dg_one P h3]; norm_num⟩)
    unfold symOf at this
    simp only [h3, Bool.false_eq_true, if_false] at this
    exact congrArg (fun y : GF => [OnBytes.Slice.ofF y]) this

/-- The same for the mask rows of oracle message k (maskSyms). -/
theorem maskSyms_congr (V V' : ℕ → Rows) (k : Fin P.sent.size) (x : ℕ)
    (h : ∀ v, symOf P V ⟨k, .inr v⟩ x = symOf P V' ⟨k, .inr v⟩ x) :
    maskSyms P V k x = maskSyms P V' k x := by
  unfold maskSyms
  refine congrArg List.flatten (List.map_congr_left fun r hr => ?_)
  have hr' : r < (shapeAt P k).maskRows := List.mem_range.1 hr
  refine congrArg (fun y => words3 (ofE y)) ?_
  rw [symG_mod, symG_mod]
  exact ext_crd fun t => h (⟨r, hr'⟩, t)

/-- The column of tree τ at the position x is the same for two families of rows V and V' whose
symbols symOf agree at x for every row whose oracle message is in τ. -/
theorem col_congr (V V' : ℕ → Rows) (τ x : ℕ)
    (h : ∀ ρ : RowN P, treeOf P ρ.1 = some τ → symOf P V ρ x = symOf P V' ρ x) :
    col P V τ x = col P V' τ x := by
  unfold col
  have key : ∀ k ∈ (List.range P.sent.size).filter fun k =>
      ((Own.treesMade P.codes P.sent).getD {}).tree[k]? == some τ,
      mainSyms P V k x = mainSyms P V' k x ∧ maskSyms P V k x = maskSyms P V' k x := by
    intro k hk
    rw [List.mem_filter, List.mem_range] at hk
    have ht : treeOf P k = some τ := by simpa [treeOf] using hk.2
    exact ⟨mainSyms_congr P V V' ⟨k, hk.1⟩ x fun v => h ⟨⟨k, hk.1⟩, .inl v⟩ ht,
      maskSyms_congr P V V' ⟨k, hk.1⟩ x fun v => h ⟨⟨k, hk.1⟩, .inr v⟩ ht⟩
  exact congrArg₂ (· ++ ·)
    (congrArg List.flatten (List.map_congr_left fun k hk => (key k hk).1))
    (congrArg List.flatten (List.map_congr_left fun k hk => (key k hk).2))

end OnBytes.SendSim.At

#print axioms OnBytes.SendSim.At.col_congr
#print axioms OnBytes.SendSim.At.symOf_sym
#print axioms OnBytes.SendSim.At.symOf_eq
