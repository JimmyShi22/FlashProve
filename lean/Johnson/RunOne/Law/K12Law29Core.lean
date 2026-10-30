-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12Law29Core.lean: The key file's tables, row 2.9 (the
proximity test on the folded row's group G_u): THE «law» OF ITS WAY BACK, FROM THE TEST's OWN LAW:
the second theorem over `law_29` (K12Law29.lean): at Johnson/RunOne/KeyFillSeed.lean's filling
(baseK at the six; at_ := atSix; the reader kreadFam; the field's reading gl). One statement with
its proof: calls.
  `law_29_core`: the border's promise on₂ … 9 x · the game's relation `QW` between x and what
  the
    sub-protocol's piece puts out (it holds the test's own decision's «accept») · the place's first
    tree is 0 · `CoreFacts` at the verifier's state behind the door in · the bridge's premises at
    the group's two members (U: 3 · the shared split's masks: 5) ⊢ THERE IS A TUPLE OF TABLES tbl
    SUCH THAT FOR EVERY WITNESS w BEHIND: `relAt_back_to`'s premise «law» at the row, with message 3
    laid. «∃ tbl» stands in front of «∀ w»: the tuple comes from the statement in front, not from
    the witness.
How: `guard_29` (KeyBookAtSeats.lean: the promise hands «the mask has come · the book is in order»)
· `core_behind_QW` (Johnson/Desc/K12/Coin/CoreBehindQ.lean) · `member_of_core₂` | `words_of_core`
(K12TupleOfCore.lean) · `law_29`. ALSO `law_29_of_core`: from the seam's
core's CONCLUSION to the row's «law»:
`law_29_coreF`'s proof behind its first call, stated by itself: so that every form of the core
serves. What it is not. PREMISES, EACH NAMED, NONE PAID HERE: CoreFacts ·
hB3 (the laid table is the typed message's own: left to other
files) · hlog | told | hsm | hsh at the two members (the bridge's) · which
member sits at which message number (hmem0 | hmem3) · of the rows taken in: they read as 0 off the
statement's tables (hoff), name messages 0 and 3 alone (hnames), and every open row of the group is
among them (hsub) · the tables' sizes behind the test's beginning (hsz) · the counts on the group's
open rows · LayIdem · that the riding member's OOD sample and committed word stay across the test
(hsmp | hword). It
pays no field of the tables. No soundness is claimed. Nothing on hiding.

-/
import Johnson.RunOne.Law.K12Law29
import Johnson.RunOne.Law.K12TupleOfCore
import Johnson.RunOne.KeyBookAtSeats
import Johnson.Desc.K12.Coin.CoreBehindQ
import Johnson.RunOne.Law.GrowsOfAllSay
import Johnson.RunOne.Law.K12Hval

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.RunOne.Law.K12Law29Core
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Key.Fill
open VerifiableInference.Desc.K12 VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Sound (Frame strsOf)
open Cb Johnson.Pack OnBytes.Maker
open Johnson.Top.H (csKey)
open Johnson.RunOne Johnson.RunOne.KeyRows23
open LPFD.CandLaid
open H2K.Pin (tabP)
open _root_.Desc.K14.Law.Fence (CoreFacts)
open Johnson.RunOne.Law.K12TupleOfCore Johnson.RunOne.Law.K12Law29

/-- The six's members at the messages 3 (U) and 5 (the shared split's masks). -/
def i3 : Fin six.length := ⟨3, by decide⟩
def i5 : Fin six.length := ⟨5, by decide⟩

variable {XI Cells Rec : Type} (F : FileDescription XI) (Fr₂ : Frame)
  (decT : (ℕ → Option (ℕ × List UInt64)) → Rec → Option Cells)
  (recOf : VerifiableInference.Desc.Key.Xi → Option Rec) (orc₁ : ℕ → Option ℕ)
  (tab : Cells → ℕ → ℕ → OnBytes.F) (S : LinShape) (K₁ : KPlan)
  (enc : (Nat → E) → Nat → E) (rad a : Nat) (coll : Strs → Rec → Prop)
  (last₁ : VerifiableInference.Desc.Key.FirstState → Bool) (off₂ : Nat → Nat)

/-- **Row 2.9's «law», from the proximity test's own law.** -/
theorem law_29_core (π : P12) (lo : ℕ) (r : Fmt.M1.Stage → ℕ) (rdN : ℕ → ℕ)
    (smp : (P₂ × St₂) → (s : Sound.Sending) → (i : Fin s.l.length) →
      Option ((sigOf csKey s.l).om i).Smp)
    (mem : ℕ → Option Sound.Mem)
    (rd : (x : Sound.Mem) → ((sigOf csKey x.1.l).om x.2).Msg → OnBytes.Part → ℕ → GE)
    (hrd : ∀ x m part i, rd x m part i = tabP csKey (x.1.l.get x.2).1 m part i)
    (hB3 : ∀ (i : Fin six.length) (u : (OmAt csKey six i).Msg),
      ofU csKey (six.get i).1 (six.get i).2 u = tabP csKey (six.get i).1 u)
    (x y : (P₂ × St₂) × Fr₂.E.Str)
    (hQ : QW Fr₂ π (nlAt π lo) r rdN (Seat.enter (·.gU) (·.firstMask)) Seat.leave x y)
    (hft : π.nums.firstTree = 0)
    (hon : on₂ F Fr₂ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix S K₁
      (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad a coll last₁ off₂ 9 x)
    (facts : ∀ t, Seat.enter (·.gU) (·.firstMask) x.1.2 = .ok t →
      CoreFacts csKey F Fr₂ π (fun z => lo + z) (fun s => r s.st) smp mem
        (fun z => z = ⟨sixS, i3⟩ ∨ z = ⟨sixS, i5⟩) t x.2 x.1 (strsOf Fr₂ x.2))
    (hi : LayIdem (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂)
    (hlog : ∀ i : Fin six.length, i = i3 ∨ i = i5 → ∀ o,
      F.oracleAt (seatAt six numSix atSix i).1 = some o → o.logLength = aOf csKey (six.get i).1)
    (told : ∀ i : Fin six.length, i = i3 ∨ i = i5 →
      (F.oracleAt (seatAt six numSix atSix i).1).isSome = true)
    (hsm : ∀ i : Fin six.length, i = i3 ∨ i = i5 → ∀ σ : (OmAt csKey six i).Smp,
      smp x.1 sixS i = some σ → ∃ ρ : (OmAt csKey six i).Z.D,
        (OmAt csKey six i).Z.val σ.1 = (OmAt csKey six i).Z.val ρ ∧
        seedIsS csKey six numSix (rowIsK csKey six) (src₂ orc₁) i x.1 ρ σ.2)
    (hsh : ∀ i : Fin six.length, i = i3 ∨ i = i5 →
      Sound.ShownAt F csKey six (seatAt six numSix atSix) (strsOf Fr₂ x.2) i)
    (hmem0 : mem 0 = some ⟨sixS, i3⟩) (hmem3 : mem 3 = some ⟨sixS, i5⟩)
    (hoff : ∀ G0, x.1.2.st.groups[x.1.2.loc.gU]? = some G0 →
      ∀ q ∈ (runRows x.1.2.st G0).toList, OffTables OnBytes.Model.Reading.gl x.1.2.st q)
    (hsz : ∀ G0, x.1.2.st.groups[x.1.2.loc.gU]? = some G0 →
      ∀ q ∈ (runRows x.1.2.st G0).toList, ∀ o ∈ q.oracles, ∀ pt,
        Means.tableSize (begun x.1.2.st x.1.2.loc.gU G0) o pt = Means.tableSize x.1.2.st o pt)
    (hnames : ∀ G0, x.1.2.st.groups[x.1.2.loc.gU]? = some G0 →
      ∀ q ∈ (runRows x.1.2.st G0).toList, ∀ o ∈ q.oracles, o = 0 ∨ o = 3)
    (hsub : ∀ G0, x.1.2.st.groups[x.1.2.loc.gU]? = some G0 →
      (∀ q ∈ G0.rows.toList, q ∈ (runRows x.1.2.st G0).toList) ∧ 0 ∈ G0.members.toList ∧
        S.fold.index.answers + S.fold.columns + 1 ≤ G0.rows.size)
    (h1 : S.fold.index.answers ≠ 0) (h2 : S.fold.columns ≠ 0) (x0 : OnBytes.Oracle)
    (hx : x.1.2.st.oracles[0]? = some x0) (hsmd : x0.sampled = true)
    (hss : x0.sampleRows.size ≠ 0)
    (hsmp : (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂.smp y.1 (atSix 5).1
        (atSix 5).2 =
      (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂.smp x.1 (atSix 5).1
        (atSix 5).2)
    (hword : wordOf F (strsOf Fr₂ y.2) (atSix 5).1 (atSix 5).2 =
      wordOf F (strsOf Fr₂ x.2) (atSix 5).1 (atSix 5).2) :
    ∃ tbl : ℕ → Fill.Tab, ∀ (rw : KRow) (w : Wit Cells Unit Fill.Tab),
      rw.ins = [KItem.claim 2 "record", .claim 2 "columns", .claim 2 "FoldU", .srow 3, .pin 3] →
      KItem.pin 5 ∈ rw.outs ++ rw.ctx →
      (∀ i ∈ rw.outs ++ rw.ctx,
        i.holds F (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix
          (meaning₂ S K₁ (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad) y.1
          (strsOf Fr₂ y.2) w) →
      ∀ i ∈ rw.ins,
        i.holds F (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix
          (meaning₂ S K₁ (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad) x.1
          (strsOf Fr₂ x.2) (layAt atSix [3] tbl w) := by
  obtain ⟨hshape, hhas, hfree, _⟩ := id (hon.resolve_left (fun h => h trivial))
  obtain ⟨t, G0, ht, hG, μ, hall, hc⟩ := core_behind_QW csKey F Fr₂ π lo r rdN smp mem _ rd hrd _ _
    x y x.1 (strsOf Fr₂ x.2) hQ
    (fun t ht => by rw [hft]; exact guard_29 S a x.1.2 hshape t ht) facts
    (fun t ht => by cases ht; exact hfree.order)
  cases ht
  obtain ⟨hs1, hs2, hs3⟩ := hsub G0 hG
  have has : ∀ k ∈ pinned (open₂ 9),
      hasSmp (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ (atSix k).1
        (atSix k).2 x.1 = true := fun k hk => List.all_eq_true.1 hhas k hk
  refine ⟨tblOf μ, fun rw w hins hctx => ?_⟩
  exact law_29 OnBytes.Model.Reading.gl F Fr₂ _ atSix S K₁ _ enc rad a coll last₁ off₂ rw hins hctx
    x y.1 (strsOf Fr₂ y.2) w (tblOf μ) hon hi (by intro k hk k' hk' _; simp at hk hk'; omega)
    (by
      intro k hk k' hk' e
      simp at hk hk'
      subst hk hk'
      exact absurd e (by decide))
    (by
      rintro k (rfl | rfl)
      · exact member_of_core₂ F decT recOf orc₁ tab smp μ i3 (hlog i3 (Or.inl rfl))
          (told i3 (Or.inl rfl)) x.1 _ (has 3 (by decide)) (hsm i3 (Or.inl rfl))
          (hsh i3 (Or.inl rfl)) (hc _ (Or.inl rfl))
      · exact member_of_core₂ F decT recOf orc₁ tab smp μ i5 (hlog i5 (Or.inr rfl))
          (told i5 (Or.inr rfl)) x.1 _ (has 5 (by decide)) (hsm i5 (Or.inr rfl))
          (hsh i5 (Or.inr rfl)) (hc _ (Or.inr rfl)))
    hsmp hword rfl _ G0 x0 _ _ hall (hoff G0 hG) (hsz G0 hG)
    (by
      intro q hq o ho
      rcases hnames G0 hG q hq o ho with rfl | rfl
      · exact ⟨3, Or.inl rfl, rfl, words_of_core tab mem rd hrd hB3 μ 0 i3 hmem0⟩
      · exact ⟨5, Or.inr rfl, rfl, words_of_core tab mem rd hrd hB3 μ 3 i5 hmem3⟩)
    hG hs1 hs3 h1 h2 hx hsmd hss
    (fun q hq => H2K.Pin.sample_mem_runRows _ G0 0 x0 hs2 hx q hq)

/-- **The same over three general lemmas** (`holds_of_allSay`, GrowsOfAllSay.lean ·
`hval_of_links`, K12Hval.lean · `ofU_eq_tabP`, TabBridge.lean, inside the second): FIVE PREMISES OF
`law_29_core` FALL: hB3 · hoff · hsz · hnames · «every open row is among the rows taken in». In
their place: no open row is marked as a sample row (hK) · the group's members are the messages 0 and
3. -/
theorem law_29_coreF (π : P12) (lo : ℕ) (r : Fmt.M1.Stage → ℕ) (rdN : ℕ → ℕ)
    (smp : (P₂ × St₂) → (s : Sound.Sending) → (i : Fin s.l.length) →
      Option ((sigOf csKey s.l).om i).Smp)
    (mem : ℕ → Option Sound.Mem)
    (rd : (x : Sound.Mem) → ((sigOf csKey x.1.l).om x.2).Msg → OnBytes.Part → ℕ → GE)
    (hrd : ∀ x m part i, rd x m part i = tabP csKey (x.1.l.get x.2).1 m part i)
    (x y : (P₂ × St₂) × Fr₂.E.Str)
    (hQ : QW Fr₂ π (nlAt π lo) r rdN (Seat.enter (·.gU) (·.firstMask)) Seat.leave x y)
    (hft : π.nums.firstTree = 0)
    (hon : on₂ F Fr₂ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix S K₁
      (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad a coll last₁ off₂ 9 x)
    (facts : ∀ t, Seat.enter (·.gU) (·.firstMask) x.1.2 = .ok t →
      CoreFacts csKey F Fr₂ π (fun z => lo + z) (fun s => r s.st) smp mem
        (fun z => z = ⟨sixS, i3⟩ ∨ z = ⟨sixS, i5⟩) t x.2 x.1 (strsOf Fr₂ x.2))
    (hi : LayIdem (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂)
    (hlog : ∀ i : Fin six.length, i = i3 ∨ i = i5 → ∀ o,
      F.oracleAt (seatAt six numSix atSix i).1 = some o → o.logLength = aOf csKey (six.get i).1)
    (told : ∀ i : Fin six.length, i = i3 ∨ i = i5 →
      (F.oracleAt (seatAt six numSix atSix i).1).isSome = true)
    (hsm : ∀ i : Fin six.length, i = i3 ∨ i = i5 → ∀ σ : (OmAt csKey six i).Smp,
      smp x.1 sixS i = some σ → ∃ ρ : (OmAt csKey six i).Z.D,
        (OmAt csKey six i).Z.val σ.1 = (OmAt csKey six i).Z.val ρ ∧
        seedIsS csKey six numSix (rowIsK csKey six) (src₂ orc₁) i x.1 ρ σ.2)
    (hsh : ∀ i : Fin six.length, i = i3 ∨ i = i5 →
      Sound.ShownAt F csKey six (seatAt six numSix atSix) (strsOf Fr₂ x.2) i)
    (hmem0 : mem 0 = some ⟨sixS, i3⟩) (hmem3 : mem 3 = some ⟨sixS, i5⟩)
    (hK : Means.OpenKinds x.1.2.st)
    (hgrp : ∀ G0, x.1.2.st.groups[x.1.2.loc.gU]? = some G0 →
      (∀ o ∈ G0.members.toList, o = 0 ∨ o = 3) ∧ 0 ∈ G0.members.toList ∧
        S.fold.index.answers + S.fold.columns + 1 ≤ G0.rows.size)
    (h1 : S.fold.index.answers ≠ 0) (h2 : S.fold.columns ≠ 0) (x0 : OnBytes.Oracle)
    (hx : x.1.2.st.oracles[0]? = some x0) (hsmd : x0.sampled = true)
    (hss : x0.sampleRows.size ≠ 0)
    (hsmp : (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂.smp y.1 (atSix 5).1
        (atSix 5).2 =
      (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂.smp x.1 (atSix 5).1
        (atSix 5).2)
    (hword : wordOf F (strsOf Fr₂ y.2) (atSix 5).1 (atSix 5).2 =
      wordOf F (strsOf Fr₂ x.2) (atSix 5).1 (atSix 5).2) :
    ∃ tbl : ℕ → Fill.Tab, ∀ (rw : KRow) (w : Wit Cells Unit Fill.Tab),
      rw.ins = [KItem.claim 2 "record", .claim 2 "columns", .claim 2 "FoldU", .srow 3, .pin 3] →
      KItem.pin 5 ∈ rw.outs ++ rw.ctx →
      (∀ i ∈ rw.outs ++ rw.ctx,
        i.holds F (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix
          (meaning₂ S K₁ (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad) y.1
          (strsOf Fr₂ y.2) w) →
      ∀ i ∈ rw.ins,
        i.holds F (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix
          (meaning₂ S K₁ (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad) x.1
          (strsOf Fr₂ x.2) (layAt atSix [3] tbl w) := by
  obtain ⟨hshape, hhas, hfree, hno⟩ := id (hon.resolve_left (fun h => h trivial))
  obtain ⟨t, G0, ht, hG, μ, hall, hc⟩ := core_behind_QW csKey F Fr₂ π lo r rdN smp mem _ rd hrd _ _
    x y x.1 (strsOf Fr₂ x.2) hQ
    (fun t ht => by rw [hft]; exact guard_29 S a x.1.2 hshape t ht) facts
    (fun t ht => by cases ht; exact hfree.order)
  cases ht
  obtain ⟨hg1, hg2, hg3⟩ := hgrp G0 hG
  have has : ∀ k ∈ pinned (open₂ 9),
      hasSmp (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ (atSix k).1
        (atSix k).2 x.1 = true := fun k hk => List.all_eq_true.1 hhas k hk
  have hm3 := member_of_core₂ F decT recOf orc₁ tab smp μ i3 (hlog i3 (Or.inl rfl))
    (told i3 (Or.inl rfl)) x.1 _ (has 3 (by decide)) (hsm i3 (Or.inl rfl)) (hsh i3 (Or.inl rfl))
    (hc _ (Or.inl rfl))
  have hm5 := member_of_core₂ F decT recOf orc₁ tab smp μ i5 (hlog i5 (Or.inr rfl))
    (told i5 (Or.inr rfl)) x.1 _ (has 5 (by decide)) (hsm i5 (Or.inr rfl)) (hsh i5 (Or.inr rfl))
    (hc _ (Or.inr rfl))
  have hap : SeatsApart atSix [3] [3] := by intro k hk k' hk' _; simp at hk hk'; omega
  have hap' : SeatsApart atSix [3] [5] := by
    intro k hk k' hk' e
    simp at hk hk'
    subst hk hk'
    exact absurd e (by decide)
  have arr3 : ArrOk (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix [3] :=
    fun k hk => hfree.arr k (by simp at hk; subst hk; decide)
  have arr5 : ArrOk (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix [5] :=
    fun k hk => hfree.arr k (by simp at hk; subst hk; decide)
  refine ⟨tblOf μ, fun rw w hins hctx hbehind => ?_⟩
  rw [hins]
  have hp5 := rides_pin2_at F _ (atSix 5).1 (atSix 5).2 x.1 y.1 (strsOf Fr₂ x.2) (strsOf Fr₂ y.2) w
    hsmp hword (hbehind _ hctx)
  have hread := K12LawLay.reads_all F _ atSix (kreadFam (Cells := Cells) csKey six numSix atSix tab)
    [3] [5] (tblOf μ) w arr3 arr5
    (fun v k hk => hfree.reads v k (by simp at hk; subst hk; decide))
    (fun v k hk => hfree.reads v k (by simp at hk; subst hk; decide)) hi hap
    (fun k hk => by simp at hk; subst hk; decide) hap' x.1 (strsOf Fr₂ x.2)
    (fun k hk => by simp at hk; subst hk; exact hno 5 five_pinned)
    (fun k hk => by simp at hk; subst hk; exact hp5)
    (fun k hk => by simp at hk; subst hk; exact hm5)
  have hval : ∀ o ∈ G0.members.toList, ∀ pt, ∀ i < Means.tableSize x.1.2.st o pt,
      _root_.Desc.K14.Law.wordsT csKey mem rd μ o pt i =
        OnBytes.Slice.readE (valOf (plan₂ S) (kreadFam (Cells := Cells) csKey six numSix atSix tab)
          (layAt atSix [3] (tblOf μ) w) o pt i) := by
    intro o ho pt i _
    rcases hg1 o ho with rfl | rfl
    · exact K12Hval.hval_of_links csKey (plan₂ S) _ mem rd hrd μ _ 0 3 ⟨sixS, i3⟩ hmem0 rfl
        ((hread 3 (Or.inl (by simp))).trans (tblOf_at μ i3))
        (fun part j => read_val _ _ _ _ _ _ _ _) pt i
    · exact K12Hval.hval_of_links csKey (plan₂ S) _ mem rd hrd μ _ 3 5 ⟨sixS, i5⟩ hmem3 rfl
        ((hread 5 (Or.inr (by simp))).trans (tblOf_at μ i5))
        (fun part j => read_val _ _ _ _ _ _ _ _) pt i
  obtain ⟨hrows, hsr⟩ := GrowsOfAllSay.holds_of_allSay hfree.order hK hG _ hall _ hval
  exact items_29 F _ atSix S K₁ _ enc rad x.1 (strsOf Fr₂ x.2) _ G0 x0 hG hg3 h1 h2 hx hsmd hss
    hrows (hsr 0 hg2 x0 hx)
    (K12LawLay.pin_laid F _ atSix [3] (tblOf μ) w arr3 hi hap x.1 (strsOf Fr₂ x.2) 3 (by simp) hm3)

/-- **From the seam's core's CONCLUSION to the row's «law»**: `law_29_coreF`'s proof behind its
first call, as a statement of its own: whoever has «one tuple of typed messages of which all rows
taken in hold, a candidate at the group's two members», by whichever form of the core, has the
«law». No term of the game, none of the place. -/
theorem law_29_of_core
    (smp : (P₂ × St₂) → (s : Sound.Sending) → (i : Fin s.l.length) →
      Option ((sigOf csKey s.l).om i).Smp)
    (mem : ℕ → Option Sound.Mem)
    (rd : (x : Sound.Mem) → ((sigOf csKey x.1.l).om x.2).Msg → OnBytes.Part → ℕ → GE)
    (hrd : ∀ x m part i, rd x m part i = tabP csKey (x.1.l.get x.2).1 m part i)
    (x y : (P₂ × St₂) × Fr₂.E.Str)
    (hon : on₂ F Fr₂ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix S K₁
      (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad a coll last₁ off₂ 9 x)
    (hcore : ∃ t G0, Seat.enter (·.gU) (·.firstMask) x.1.2 = .ok t ∧
      t.st.groups[t.g]? = some G0 ∧
      ∃ m : (z : Sound.Mem) → ((sigOf csKey z.1.l).om z.2).Msg,
        Means.AllSay OnBytes.Model.Reading.gl (begun t.st t.g G0) (runRows t.st G0).toList
          (_root_.Desc.K14.Law.wordsT csKey mem rd m) ∧
        ∀ z, z = ⟨sixS, i3⟩ ∨ z = ⟨sixS, i5⟩ →
          Sound.CandAt csKey F smp z x.1 (strsOf Fr₂ x.2) (m z))
    (hi : LayIdem (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂)
    (hlog : ∀ i : Fin six.length, i = i3 ∨ i = i5 → ∀ o,
      F.oracleAt (seatAt six numSix atSix i).1 = some o → o.logLength = aOf csKey (six.get i).1)
    (told : ∀ i : Fin six.length, i = i3 ∨ i = i5 →
      (F.oracleAt (seatAt six numSix atSix i).1).isSome = true)
    (hsm : ∀ i : Fin six.length, i = i3 ∨ i = i5 → ∀ σ : (OmAt csKey six i).Smp,
      smp x.1 sixS i = some σ → ∃ ρ : (OmAt csKey six i).Z.D,
        (OmAt csKey six i).Z.val σ.1 = (OmAt csKey six i).Z.val ρ ∧
        seedIsS csKey six numSix (rowIsK csKey six) (src₂ orc₁) i x.1 ρ σ.2)
    (hsh : ∀ i : Fin six.length, i = i3 ∨ i = i5 →
      Sound.ShownAt F csKey six (seatAt six numSix atSix) (strsOf Fr₂ x.2) i)
    (hmem0 : mem 0 = some ⟨sixS, i3⟩) (hmem3 : mem 3 = some ⟨sixS, i5⟩)
    (hK : Means.OpenKinds x.1.2.st)
    (hgrp : ∀ G0, x.1.2.st.groups[x.1.2.loc.gU]? = some G0 →
      (∀ o ∈ G0.members.toList, o = 0 ∨ o = 3) ∧ 0 ∈ G0.members.toList ∧
        S.fold.index.answers + S.fold.columns + 1 ≤ G0.rows.size)
    (h1 : S.fold.index.answers ≠ 0) (h2 : S.fold.columns ≠ 0) (x0 : OnBytes.Oracle)
    (hx : x.1.2.st.oracles[0]? = some x0) (hsmd : x0.sampled = true)
    (hss : x0.sampleRows.size ≠ 0)
    (hsmp : (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂.smp y.1 (atSix 5).1
        (atSix 5).2 =
      (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂.smp x.1 (atSix 5).1
        (atSix 5).2)
    (hword : wordOf F (strsOf Fr₂ y.2) (atSix 5).1 (atSix 5).2 =
      wordOf F (strsOf Fr₂ x.2) (atSix 5).1 (atSix 5).2) :
    ∃ tbl : ℕ → Fill.Tab, ∀ (rw : KRow) (w : Wit Cells Unit Fill.Tab),
      rw.ins = [KItem.claim 2 "record", .claim 2 "columns", .claim 2 "FoldU", .srow 3, .pin 3] →
      KItem.pin 5 ∈ rw.outs ++ rw.ctx →
      (∀ i ∈ rw.outs ++ rw.ctx,
        i.holds F (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix
          (meaning₂ S K₁ (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad) y.1
          (strsOf Fr₂ y.2) w) →
      ∀ i ∈ rw.ins,
        i.holds F (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix
          (meaning₂ S K₁ (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad) x.1
          (strsOf Fr₂ x.2) (layAt atSix [3] tbl w) := by
  obtain ⟨_, hhas, hfree, hno⟩ := id (hon.resolve_left (fun h => h trivial))
  obtain ⟨t, G0, ht, hG, μ, hall, hc⟩ := hcore
  cases ht
  obtain ⟨hg1, hg2, hg3⟩ := hgrp G0 hG
  have has : ∀ k ∈ pinned (open₂ 9),
      hasSmp (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ (atSix k).1
        (atSix k).2 x.1 = true := fun k hk => List.all_eq_true.1 hhas k hk
  have hm3 := member_of_core₂ F decT recOf orc₁ tab smp μ i3 (hlog i3 (Or.inl rfl))
    (told i3 (Or.inl rfl)) x.1 _ (has 3 (by decide)) (hsm i3 (Or.inl rfl)) (hsh i3 (Or.inl rfl))
    (hc _ (Or.inl rfl))
  have hm5 := member_of_core₂ F decT recOf orc₁ tab smp μ i5 (hlog i5 (Or.inr rfl))
    (told i5 (Or.inr rfl)) x.1 _ (has 5 (by decide)) (hsm i5 (Or.inr rfl)) (hsh i5 (Or.inr rfl))
    (hc _ (Or.inr rfl))
  have hap : SeatsApart atSix [3] [3] := by intro k hk k' hk' _; simp at hk hk'; omega
  have hap' : SeatsApart atSix [3] [5] := by
    intro k hk k' hk' e
    simp at hk hk'
    subst hk hk'
    exact absurd e (by decide)
  have arr3 : ArrOk (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix [3] :=
    fun k hk => hfree.arr k (by simp at hk; subst hk; decide)
  have arr5 : ArrOk (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix [5] :=
    fun k hk => hfree.arr k (by simp at hk; subst hk; decide)
  refine ⟨tblOf μ, fun rw w hins hctx hbehind => ?_⟩
  rw [hins]
  have hp5 := rides_pin2_at F _ (atSix 5).1 (atSix 5).2 x.1 y.1 (strsOf Fr₂ x.2) (strsOf Fr₂ y.2) w
    hsmp hword (hbehind _ hctx)
  have hread := K12LawLay.reads_all F _ atSix (kreadFam (Cells := Cells) csKey six numSix atSix tab)
    [3] [5] (tblOf μ) w arr3 arr5
    (fun v k hk => hfree.reads v k (by simp at hk; subst hk; decide))
    (fun v k hk => hfree.reads v k (by simp at hk; subst hk; decide)) hi hap
    (fun k hk => by simp at hk; subst hk; decide) hap' x.1 (strsOf Fr₂ x.2)
    (fun k hk => by simp at hk; subst hk; exact hno 5 five_pinned)
    (fun k hk => by simp at hk; subst hk; exact hp5)
    (fun k hk => by simp at hk; subst hk; exact hm5)
  have hval : ∀ o ∈ G0.members.toList, ∀ pt, ∀ i < Means.tableSize x.1.2.st o pt,
      _root_.Desc.K14.Law.wordsT csKey mem rd μ o pt i =
        OnBytes.Slice.readE (valOf (plan₂ S) (kreadFam (Cells := Cells) csKey six numSix atSix tab)
          (layAt atSix [3] (tblOf μ) w) o pt i) := by
    intro o ho pt i _
    rcases hg1 o ho with rfl | rfl
    · exact K12Hval.hval_of_links csKey (plan₂ S) _ mem rd hrd μ _ 0 3 ⟨sixS, i3⟩ hmem0 rfl
        ((hread 3 (Or.inl (by simp))).trans (tblOf_at μ i3))
        (fun part j => read_val _ _ _ _ _ _ _ _) pt i
    · exact K12Hval.hval_of_links csKey (plan₂ S) _ mem rd hrd μ _ 3 5 ⟨sixS, i5⟩ hmem3 rfl
        ((hread 5 (Or.inr (by simp))).trans (tblOf_at μ i5))
        (fun part j => read_val _ _ _ _ _ _ _ _) pt i
  obtain ⟨hrows, hsr⟩ := GrowsOfAllSay.holds_of_allSay hfree.order hK hG _ hall _ hval
  exact items_29 F _ atSix S K₁ _ enc rad x.1 (strsOf Fr₂ x.2) _ G0 x0 hG hg3 h1 h2 hx hsmd hss
    hrows (hsr 0 hg2 x0 hx)
    (K12LawLay.pin_laid F _ atSix [3] (tblOf μ) w arr3 hi hap x.1 (strsOf Fr₂ x.2) 3 (by simp) hm3)

end Johnson.RunOne.Law.K12Law29Core

#print axioms Johnson.RunOne.Law.K12Law29Core.law_29_core
#print axioms Johnson.RunOne.Law.K12Law29Core.law_29_coreF
#print axioms Johnson.RunOne.Law.K12Law29Core.law_29_of_core
