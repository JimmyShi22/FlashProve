-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/StoredCols.lean: the columns that the format's step shows a block at a stretch
of one written round that opens no tree are the stored table's, off the oracle string.

  tabOf           the stored table's column at a position, off the oracles between two blocks.
  regroup_mem     every column in a group that the step makes is one of the columns shown.
  mem_of_lookup   what a look-up finds is in the list.
  wants_table     a stretch of one written round that opens no tree asks for the stored table alone.
  opened_table    so every column shown there is the stored table's at its position.
  shown_stored    **so is every column in the groups that the step makes.**
  loc_goodIn4'    "LOC" in the form of the rule of composition at the shared chain's own fourth
                  block, WITHOUT the premise on the columns.

What is not claimed. PREMISE: the written round opens no tree. That the symbol read carries its own
position is one of the tests in front of the run; it is not spent here: the column is taken at the
position asked for. The other premises of loc_goodIn4 stay, in its form: each under the promise in
front alone. No soundness of a verifier.

-/
import Johnson.Desc.K14.Law.GoodLoc

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat
open OnBytes.Means (Words)
open VerifiableInference.Desc (Block noDigest regroup OpenedColumn)
open VerifiableInference.Desc.Sound (Frame Piece)
open _root_.Run.PQ (CK)

/-- The stored table's column at a position; nothing beyond the table's end. -/
def tabOf {F : Frame} (y : F.E.Str) (x : Nat) : List UInt64 :=
  if h : x < 2 ^ F.a then (y.1 ⟨x, h⟩).2 else []

/-- Every column in a group that the step makes is one of the columns shown. -/
theorem regroup_mem : ∀ (ns : List Nat) (cols : List OpenedColumn) (g : List (Nat × List UInt64)),
    g ∈ regroup ns cols → ∀ e ∈ g, ∃ c ∈ cols, e = (c.2.1, c.2.2)
  | [], _, g, hg, _, _ => by cases hg
  | n :: ns, cols, g, hg, e, he => by
    rw [regroup] at hg
    rcases List.mem_cons.1 hg with rfl | hg
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 he
      exact ⟨c, List.mem_of_mem_take hc, rfl⟩
    · obtain ⟨c, hc, hce⟩ := regroup_mem ns (cols.drop n) g hg e he
      exact ⟨c, List.mem_of_mem_drop hc, hce⟩

/-- What a look-up finds is in the list. -/
theorem mem_of_lookup {β : Type} : ∀ (l : List (Nat × β)) (x : Nat) (b : β),
    l.lookup x = some b → (x, b) ∈ l
  | [], _, _, h => by cases h
  | (k, v) :: l, x, b, h => by
    rw [List.lookup_cons] at h
    split at h
    · rename_i hk
      obtain rfl := Option.some.inj h
      have : x = k := by simpa using hk
      subst this
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_of_lookup l x b h)

/-- A stretch of one written round that opens no tree asks for the stored table alone. -/
theorem wants_table (a : Nat) (dep : Nat → Option Nat) (d : RDT) (ho : d.opens = [])
    (Rs : List Fmt.Drawn) : ∀ w ∈ wantsOf a dep [d] Rs, ∃ item x, w = Want.table item x := by
  intro w hw
  cases Rs with
  | nil => cases hw
  | cons R Rs =>
    simp only [wantsOf, ho, List.flatMap_nil, List.append_nil, List.mem_flatMap, List.mem_map]
      at hw
    obtain ⟨s, _, x, _, rfl⟩ := hw
    exact ⟨_, _, rfl⟩

variable {S Cl W : Type} {C : CK} {F : Frame}

/-- Every column shown at such a stretch is the stored table's at its position. -/
theorem opened_table (p : Piece C F S Cl W) (d : RDT) (hds : p.ds = [d]) (ho : d.opens = [])
    (y : F.E.Str) (τ : Tr (uLT C p.ds)) :
    ∀ c ∈ (sView C p.stage y τ).opened, c.2.2 = tabOf y c.2.1 := by
  intro c hc
  simp only [sView, List.mem_filterMap, Option.map_eq_some_iff] at hc
  obtain ⟨w, hw, col, hcol, rfl⟩ := hc
  have hw' : w ∈ wantsOf F.a p.stage.depth p.ds (drawnT C p.ds (rhoT C p.ds τ)) := hw
  have hall : ∀ (ds : List RDT), ds = [d] → ∀ Rs, w ∈ wantsOf F.a p.stage.depth ds Rs →
      ∃ item x, w = Want.table item x := by
    intro ds e Rs h
    subst e
    exact wants_table _ _ d ho Rs w h
  obtain ⟨item, x, rfl⟩ := hall p.ds hds _ hw'
  simp only [sCol] at hcol
  split at hcol
  · rename_i hx
    obtain rfl := Option.some.inj hcol
    show (y.1 ⟨x, hx⟩).2 = tabOf y x
    unfold tabOf
    rw [dif_pos hx]
  · cases hcol

/-- **Every column in the groups that the step makes is the stored table's.** -/
theorem shown_stored (p : Piece C F S Cl W) (d : RDT) (hds : p.ds = [d]) (ho : d.opens = [])
    (y : F.E.Str) (τ : Tr (uLT C p.ds)) (rs : List Fmt.RoundView) (cols : List (Nat × List UInt64))
    (h : shownGroups F.ft p.b rs (sView C p.stage y τ).opened = [cols]) :
    ∀ x col, cols.lookup x = some col → col = tabOf y x := by
  intro x col hl
  have hm := mem_of_lookup cols x col hl
  obtain ⟨c, hc, hce⟩ := regroup_mem _ _ cols (by
    unfold shownGroups at h
    rw [h]
    exact List.mem_singleton.2 rfl) _ hm
  have h0 := opened_table p d hds ho y τ c (List.mem_of_mem_take hc)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hce
  exact h0

variable (Pin : St × F.E.Str → W → Prop)

/-- **"LOC" in the form of the rule of composition**, at the chain's own fourth block, the columns
being the stored table's by what the stretch is shown. -/
theorem loc_goodIn4' (rg : W → Words GE) (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (base : Nat) (d : RDT) {ns n : Nat}
    (hd : SendsDraws (toRD d) ns 0 n P.par.S.fold.index.code.logN) (ho : d.opens = [])
    (e' e : Nat) (he : (2 ^ P.par.S.fold.index.code.logN - e' - 1) ^ n ≤ e)
    (Prm Prm' : St × F.E.Str → Prop)
    (hback : ∀ x τ b w, On4 P.par x → Prm x → (posPiece (W := W) (F := F) b4 base d
      P.par.S.fold.index.code.logN n e).ior.red.out x τ = some b → Pin b w → Pin x w)
    (hkeep : ∀ x τ b, On4 P.par x → Prm x → (posPiece (W := W) (F := F) b4 base d
      P.par.S.fold.index.code.logN n e).ior.red.out x τ = some b → Prm' b)
    (hdet : ∀ (x : St × F.E.Str) w w', On4 P.par x → Prm x → Pin x w → Pin x w' →
      AgreeOn x.1.loc.oU.oracle (rg w) (rg w')) :
    (posPiece (W := W) (F := F) b4 base d P.par.S.fold.index.code.logN n e).GoodIn
      (fun x => On4 P.par x ∧ Prm x) (fun x => On4 P.par x ∧ Prm' x)
      (fun x w => Base OnBytes.Model.Reading.gl rg Pin x w ∧
        NearAt OnBytes.Model.Reading.gl P.par x.1 (rg w) (tabOf x.2) e')
      (Base OnBytes.Model.Reading.gl rg Pin) :=
  loc_goodIn4 Pin rg P b1 b2 b3 b4 b5 b6 b7 b8 hbl base d hd tabOf e' e he Prm Prm' hback hkeep hdet
    fun x τ _ cols _ hg => shown_stored
      (posPiece (W := W) (F := F) b4 base d P.par.S.fold.index.code.logN n e) d rfl ho x.2 τ _
      cols hg

end Desc.K14.Law
