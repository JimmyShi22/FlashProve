-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/ListedWholeExt.lean: at the description of a whole file, the list of read positions of
the stored table that OnBytes/Maker/ListedWhole.lean makes from the wants (rdEWhole) is the wiring's
list of all positions cut down to the positions that the description reads.

No soundness: a test. This module serves the runs of lean/Ask/; it states nothing on soundness.

That equation is the premise hRE, on the stored table's read positions, of the equation between the
verifier along lists and the compiled verifier ("verifyBSL_eq",
OnBytes/TypedOracleCompiler/Compile/Batch/ListedVerifierLaws.lean). Beneath it the same equation is h1 of the
equation of the two forests ("forestExtL_eq", OnBytes/TypedOracleCompiler/Compile/Batch/ListedExtLaws.lean).

Over OnBytes/Maker/ListedWholeLaws.lean, for risingOf's two laws (risingOf_mem, risingOf_rising).

States.
  mem_placeWants: a number stands in placeWants ws exactly if ws wants it of the stored table, under
    whichever item.
  rising_fin_eq_filter: a strictly rising list of members of Fin n whose members are just those at
    which a test t says yes is (List.finRange n).filter t.
  rdEWhole_rising, mem_rdEWhole: rdEWhole rises strictly; its members are the positions that the
    file's reduction reads of the stored table ("mem_extReads", OnBytes/Maker/ReadsAt.lean).
  rdEWhole_eq: the equation, at any test t that says yes exactly at the positions that the
    description reads at x and ρ. The test is a letter so that no instance of decidability stands in
    the statement: a caller sets t to its own "decide (p ∈ ..)".
  mem_all_weOne: the stored table's wiring lists every position.
Limits: the verifier's side alone: nothing on where openings stand in an argument string. rdEWhole
and the description (extPosOf, OnBytes/Maker/Whole.lean) both drop a want at a number of 2 ^ D.a or
more, by the test "x < 2 ^ D.a"; whether such a want can arise is not shown here, and the equation
holds either way. Nothing on time or memory. Nothing on soundness. No example.
The program does not import this file.

-/
import OnBytes.Maker.ListedWholeLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Maker

open TypedOracleCompiler.Iop TypedOracleCompiler.Joined TypedOracleCompiler.Compile.Batch _root_.Compile.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ

/-! ## Lists -/

/-- **A strictly rising list with just the members that a test takes is the cut of all members.** -/
theorem rising_fin_eq_filter {n : ℕ} {l : List (Fin n)} {t : Fin n → Bool}
    (hl : l.Pairwise (· < ·)) (hm : ∀ p, p ∈ l ↔ t p = true) : l = (List.finRange n).filter t := by
  have hf : ((List.finRange n).filter t).Pairwise (· < ·) := (List.pairwise_lt_finRange n).filter _
  refine List.Perm.eq_of_pairwise (le := (· < ·))
    (fun a b _ _ hab hba => absurd hab (lt_asymm hba)) hl hf ?_
  refine (List.perm_ext_iff_of_nodup (hl.imp fun h => ne_of_lt h)
    (hf.imp fun h => ne_of_lt h)).2 fun p => ?_
  rw [hm p, List.mem_filter]
  exact ⟨fun h => ⟨List.mem_finRange p, h⟩, fun h => h.2⟩

/-- A number stands in placeWants ws exactly if ws wants it of the stored table under some item. -/
theorem mem_placeWants (x : ℕ) :
    ∀ ws : List Want, x ∈ placeWants ws ↔ ∃ item, Want.table item x ∈ ws
  | [] => ⟨fun h => absurd h List.not_mem_nil, fun ⟨_, h⟩ => absurd h List.not_mem_nil⟩
  | .table it y :: ws => by
    rw [placeWants, List.mem_cons, mem_placeWants x ws]
    constructor
    · rintro (e | ⟨item, h⟩)
      · exact ⟨it, by rw [e]; exact List.mem_cons_self⟩
      · exact ⟨item, List.mem_cons_of_mem _ h⟩
    · rintro ⟨item, h⟩
      rcases List.mem_cons.1 h with e | h
      · exact Or.inl (Want.table.inj e).2
      · exact Or.inr ⟨item, h⟩
  | .tree j y :: ws => by
    rw [placeWants, mem_placeWants x ws]
    constructor
    · rintro ⟨item, h⟩
      exact ⟨item, List.mem_cons_of_mem _ h⟩
    · rintro ⟨item, h⟩
      rcases List.mem_cons.1 h with e | h
      · cases e
      · exact ⟨item, h⟩

/-- What the reading of a number as a member of Fin N returns has that number. -/
theorem val_of_toFin {N x : ℕ} {p : Fin N}
    (h : (if h : x < N then some (⟨x, h⟩ : Fin N) else none) = some p) : p.val = x := by
  by_cases hx : x < N
  · rw [dif_pos hx] at h
    exact (congrArg Fin.val (Option.some.inj h)).symm
  · rw [dif_neg hx] at h
    cases h

/-- The stored table's wiring lists every position. -/
theorem mem_all_weOne (a : ℕ) (p : (oneExternalString (2 ^ a) SgX).Pos) : p ∈ (weOne a).all :=
  List.mem_finRange (n := 2 ^ a) p

/-! ## At a whole file -/

section
variable (C : CK) (D : WholeD) {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3)

/-- The list of read positions rises strictly. -/
theorem rdEWhole_rising (ρ : Rho (chainsOf C D tF tJ t3).sh) :
    List.Pairwise (fun p q : Fin (2 ^ D.a) => p < q) (rdEWhole C D tF tJ t3 ρ) := by
  unfold rdEWhole
  refine List.Pairwise.filterMap _ (fun a a' h b hb b' hb' => ?_) (risingOf_rising _)
  show b.val < b'.val
  rw [val_of_toFin hb, val_of_toFin hb']
  exact h

variable {Xi : Type} (silent : Xi → TF → TJ → T3 → Bool) (run : Xi → View → View → View → Bool)

/-- The list of read positions holds just the positions that the file's reduction reads. -/
theorem mem_rdEWhole (ρ : Rho (chainsOf C D tF tJ t3).sh) (p : (oneExternalString (2 ^ D.a) SgX).Pos) :
    p ∈ rdEWhole C D tF tJ t3 ρ ↔ p ∈ (reductionOfWholeFile C D tF tJ t3 silent run).extReads ρ := by
  rw [mem_extReads, ← mem_placeWants]
  unfold rdEWhole
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨x, hx, e⟩
    have ev : Fin.val (n := 2 ^ D.a) p = x := val_of_toFin e
    rw [show p.val = x from ev]
    exact (risingOf_mem _ _).1 hx
  · intro h
    exact ⟨p.val, (risingOf_mem _ _).2 h, dif_pos p.isLt⟩

/-- **The list of read positions is the wiring's list cut down to the positions read.** -/
theorem rdEWhole_eq (x : Xi) (ρ : Rho (chainsOf C D tF tJ t3).sh)
    (t : (oneExternalString (2 ^ D.a) SgX).Pos → Bool)
    (ht : ∀ p, t p = true ↔
      p ∈ (wholeDesc C D tF tJ t3 silent run).batch.loc.extReads x ρ) :
    rdEWhole C D tF tJ t3 ρ = (weOne D.a).all.filter t :=
  rising_fin_eq_filter (n := 2 ^ D.a) (rdEWhole_rising C D tF tJ t3 ρ) fun p =>
    (mem_rdEWhole C D tF tJ t3 silent run ρ p).trans (ht p).symm

end

end OnBytes.Maker

#print axioms OnBytes.Maker.rising_fin_eq_filter
#print axioms OnBytes.Maker.mem_placeWants
#print axioms OnBytes.Maker.val_of_toFin
#print axioms OnBytes.Maker.rdEWhole_rising
#print axioms OnBytes.Maker.mem_rdEWhole
#print axioms OnBytes.Maker.rdEWhole_eq
#print axioms OnBytes.Maker.mem_all_weOne
