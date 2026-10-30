-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12Back210.lean: The key file's
tables, row 2.10 (the proximity test on Omega's group G_omega; the test's second arm: the first fold
sends its own mask): THE «law» OF ITS WAY BACK, FROM THE TEST's OWN LAW, at the tables' files'
filling (baseK at the six; at_ := atSix; the reader kreadFam; the field's reading gl). Two
statements with their proofs: calls. Made of K12Law29Core.lean's `law_29_coreF`'s text at other
letters: a mend of the one is a mend of the other.
  `law_210_coreF`: the border's promise on₂ … 10 x · the game's relation `QWO` between x and
    what the sub-protocol's piece puts out (it holds the test's own decision's «accept») · the
    place's first tree is 0 · `CoreFacts` at the verifier's state behind the door in · the bridge's
    premises at the group's two members (Omega: 4 · the shared split's masks: 5) ⊢ THERE IS A TUPLE
    OF TABLES tbl SUCH THAT FOR EVERY ROW rw WITH THE TABLE's ROW's LISTS AND EVERY WITNESS w
    BEHIND: `relAt_back_to`'s premise «law», with message 5 laid.
  `back_210`: the same off the piece's own acceptance: from the three antecedents of the last
    clause of `Pays` (K12AtField.lean): the promise in front, «the piece accepts x ↦ y»,
    and the law's conclusion `QO` at the seat's doors. `QWO` by `qwo_of_yes`; the riding member's
    OOD sample and committed word by `riding_stays₂` (K12RidingStays.lean).
BESIDE THEM:
`law_210_of_core`: the same «law» from the seam's core's conclusion as a premise (one tuple of typed
messages of which all rows taken in hold, a candidate at the group's two members): no term of the
game, none of the place: its proof is `law_210_coreF`'s behind its first call. `qw_of_qwo`: the
second arm's relation holds the first's, at the numbering by labels from the chain's first own tree
on. `law_210_coreM` · `back_210M`: «left» member by member (`MemberLeft`,
`core_behind_QWm`, Johnson/Desc/K12/Coin/MemberAtYes.lean): hft is gone and `guard_210` is not
called: THE PRICE HAS MOVED, NOT GONE: clause (7) of `MemberLeft` stands at the number nuOf π nl t,
and its payer needs the book's order to know that label. In the form of K12Law29Core.lean
and K12Back29.lean.
What it is not, first.
  (1) THE OTHER HALF OF THAT CLAUSE OF `Pays` (the promise behind: on₂ … 11 y) IS NOT TOUCHED:
    without it `Pays` is not had. (`fwd_210`, K12Fwd210.lean, has it.)
  (2) PREMISES, EACH NAMED, NONE PAID HERE:

      hb · hal: the piece holds a sub-protocol alike to the test inside its doors:
        keyOmega_alike (KeyTileFacts.lean): typed; its tie to O_at (K12AtField.lean): nobody's.
      hp · hft: the test on the list of rounds; the place's first tree is 0: plan-side: typed
        (later_more).
      facts (law_210_coreF) | hj · left (back_210): CoreFacts behind the door in, whole | the
        Johnson test on the radii and what the test's own «accept» does not give of that bundle
        (`CoreLeft`; `coreFacts_of_yes`, Johnson/Desc/K12/Coin/CoreBehindQ.lean): the codes'
        equation, siteL's and sampleL's «accept» at each member, and the members' seven: at the key
        file nobody's.
      hi · hSm: LayIdem and SmOnly, on the tables' reading: the tables' files': plan-side.
      hlog · told · hsm · hsh: the bridge's four at the two members: the bridge's own premises.
      hmem2 · hmem3: which member sits at which message number: the filler's letters.
      hK: no open row is marked as a sample row: on the verifier's state: a payer is named
        (openKinds_at_reached₂).
      hgrp · hx · hsmd · hss: the group's members and count; message 3's OOD sample's rows: on the
        verifier's state.
      hlt · hbase: message 2 is there in front (on the verifier's state); its tree lies below the
        piece's base (plan-side).
  (3) It pays no field of the tables. No soundness is claimed. Nothing on hiding.

-/
import Johnson.RunOne.Law.K12Law210
import Johnson.RunOne.Law.K12TupleOfCore
import Johnson.RunOne.Law.K12RidingStays
import Johnson.RunOne.KeyBookAtSeats
import Johnson.Desc.K12.Coin.CoreBehindQ
import Johnson.Desc.K12.Coin.MemberAtYes
import Johnson.RunOne.Law.GrowsOfAllSay
import Johnson.RunOne.Law.K12Hval

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.RunOne.Law.K12Back210
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Key.Fill
open VerifiableInference.Desc.K12 VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Sound (Frame strsOf Piece held)
open Cb Johnson.Pack OnBytes.Maker
open _root_.Run (ckP)
open Johnson.Top.H (csKey)
open Johnson.RunOne Johnson.RunOne.KeyRows23
open LPFD.CandLaid
open H2K.Pin (tabP)
open H2K.Pub (johOk)
open _root_.Desc.K14.Law.Fence (CoreFacts)
open Johnson.RunOne.Law.K12TupleOfCore Johnson.RunOne.Law.K12Law210

/-- The six's members at the messages 4 (Omega) and 5 (the shared split's masks). -/
def i4 : Fin six.length := ⟨4, by decide⟩
def i5 : Fin six.length := ⟨5, by decide⟩

variable {XI Cells Rec : Type} (F : FileDescription XI) (Fr₂ : Frame)
  (decT : (ℕ → Option (ℕ × List UInt64)) → Rec → Option Cells)
  (recOf : VerifiableInference.Desc.Key.Xi → Option Rec) (orc₁ : ℕ → Option ℕ)
  (tab : Cells → ℕ → ℕ → OnBytes.F) (S : LinShape) (K₁ : KPlan)
  (enc : (Nat → E) → Nat → E) (rad a : Nat) (coll : Strs → Rec → Prop)
  (last₁ : VerifiableInference.Desc.Key.FirstState → Bool) (off₂ : Nat → Nat)

/-- **Row 2.10's «law», from the proximity test's own law.** -/
theorem law_210_coreF (π : P12) (t₁ t₂ : ℕ) (r : Fmt.M1.Stage → ℕ) (rdN : ℕ → ℕ)
    (smp : (P₂ × St₂) → (s : Sound.Sending) → (i : Fin s.l.length) →
      Option ((sigOf csKey s.l).om i).Smp)
    (mem : ℕ → Option Sound.Mem)
    (rd : (x : Sound.Mem) → ((sigOf csKey x.1.l).om x.2).Msg → OnBytes.Part → ℕ → GE)
    (hrd : ∀ x m part i, rd x m part i = tabP csKey (x.1.l.get x.2).1 m part i)
    (x y : (P₂ × St₂) × Fr₂.E.Str)
    (hQ : QWO Fr₂ π t₁ t₂ 1 r rdN (Seat.enter (·.gOmega) (fun _ => none)) Seat.leave x y)
    (hft : π.nums.firstTree = 0)
    (hon : on₂ F Fr₂ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix S K₁
      (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad a coll last₁ off₂ 10 x)
    (facts : ∀ t, Seat.enter (·.gOmega) (fun _ => none) x.1.2 = .ok t →
      CoreFacts csKey F Fr₂ π (noAt t₁ t₂ 1) (fun s => r s.st) smp mem
        (fun z => z = ⟨sixS, i5⟩ ∨ z = ⟨sixS, i4⟩) t x.2 x.1 (strsOf Fr₂ x.2))
    (hi : LayIdem (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂)
    (hlog : ∀ i : Fin six.length, i = i5 ∨ i = i4 → ∀ o,
      F.oracleAt (seatAt six numSix atSix i).1 = some o → o.logLength = aOf csKey (six.get i).1)
    (told : ∀ i : Fin six.length, i = i5 ∨ i = i4 →
      (F.oracleAt (seatAt six numSix atSix i).1).isSome = true)
    (hsm : ∀ i : Fin six.length, i = i5 ∨ i = i4 → ∀ σ : (OmAt csKey six i).Smp,
      smp x.1 sixS i = some σ → ∃ ρ : (OmAt csKey six i).Z.D,
        (OmAt csKey six i).Z.val σ.1 = (OmAt csKey six i).Z.val ρ ∧
        seedIsS csKey six numSix (rowIsK csKey six) (src₂ orc₁) i x.1 ρ σ.2)
    (hsh : ∀ i : Fin six.length, i = i5 ∨ i = i4 →
      Sound.ShownAt F csKey six (seatAt six numSix atSix) (strsOf Fr₂ x.2) i)
    (hmem3 : mem 3 = some ⟨sixS, i5⟩) (hmem2 : mem 2 = some ⟨sixS, i4⟩)
    (hK : Means.OpenKinds x.1.2.st)
    (hgrp : ∀ G0, x.1.2.st.groups[x.1.2.loc.gOmega]? = some G0 →
      (∀ o ∈ G0.members.toList, o = 3 ∨ o = 2) ∧ 3 ∈ G0.members.toList ∧ 0 + 1 ≤ G0.rows.size)
    (x0 : OnBytes.Oracle)
    (hx : x.1.2.st.oracles[3]? = some x0) (hsmd : x0.sampled = true)
    (hss : x0.sampleRows.size ≠ 0)
    (hsmp : (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂.smp y.1 (atSix 4).1
        (atSix 4).2 =
      (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂.smp x.1 (atSix 4).1
        (atSix 4).2)
    (hword : wordOf F (strsOf Fr₂ y.2) (atSix 4).1 (atSix 4).2 =
      wordOf F (strsOf Fr₂ x.2) (atSix 4).1 (atSix 4).2) :
    ∃ tbl : ℕ → Fill.Tab, ∀ (rw : KRow) (w : Wit Cells Unit Fill.Tab),
      rw.ins = [KItem.claim 2 "FoldO", .srow 5, .pin 5] →
      KItem.pin 4 ∈ rw.outs ++ rw.ctx →
      (∀ i ∈ rw.outs ++ rw.ctx,
        i.holds F (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix
          (meaning₂ S K₁ (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad) y.1
          (strsOf Fr₂ y.2) w) →
      ∀ i ∈ rw.ins,
        i.holds F (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix
          (meaning₂ S K₁ (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad) x.1
          (strsOf Fr₂ x.2) (layAt atSix [5] tbl w) := by
  obtain ⟨hshape, hhas, hfree, hno⟩ := id (hon.resolve_left (fun h => h trivial))
  obtain ⟨t, G0, ht, hG, μ, hall, hc⟩ := core_behind_QWO csKey F Fr₂ π t₁ t₂ 1 r rdN smp mem _ rd
    hrd _ _ x y x.1 (strsOf Fr₂ x.2) hQ
    (fun t ht => by rw [hft]; exact guard_210 S a x.1.2 hshape t ht) facts
    (fun t ht => by cases ht; exact hfree.order)
  cases ht
  obtain ⟨hg1, hg2, hg3⟩ := hgrp G0 hG
  have has : ∀ k ∈ pinned (open₂ 10),
      hasSmp (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ (atSix k).1
        (atSix k).2 x.1 = true := fun k hk => List.all_eq_true.1 hhas k hk
  have hm5 := member_of_core₂ F decT recOf orc₁ tab smp μ i5 (hlog i5 (Or.inl rfl))
    (told i5 (Or.inl rfl)) x.1 _ (has 5 (by decide)) (hsm i5 (Or.inl rfl)) (hsh i5 (Or.inl rfl))
    (hc _ (Or.inl rfl))
  have hm4 := member_of_core₂ F decT recOf orc₁ tab smp μ i4 (hlog i4 (Or.inr rfl))
    (told i4 (Or.inr rfl)) x.1 _ (has 4 (by decide)) (hsm i4 (Or.inr rfl)) (hsh i4 (Or.inr rfl))
    (hc _ (Or.inr rfl))
  have hap : SeatsApart atSix [5] [5] := by intro k hk k' hk' _; simp at hk hk'; omega
  have hap' : SeatsApart atSix [5] [4] := by
    intro k hk k' hk' e
    simp at hk hk'
    subst hk hk'
    exact absurd e (by decide)
  have arr5 : ArrOk (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix [5] :=
    fun k hk => hfree.arr k (by simp at hk; subst hk; decide)
  have arr4 : ArrOk (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix [4] :=
    fun k hk => hfree.arr k (by simp at hk; subst hk; decide)
  refine ⟨tblOf μ, fun rw w hins hctx hbehind => ?_⟩
  rw [hins]
  have hp4 := rides_pin2_at F _ (atSix 4).1 (atSix 4).2 x.1 y.1 (strsOf Fr₂ x.2) (strsOf Fr₂ y.2) w
    hsmp hword (hbehind _ hctx)
  have hread := K12LawLay.reads_all F _ atSix (kreadFam (Cells := Cells) csKey six numSix atSix tab)
    [5] [4] (tblOf μ) w arr5 arr4
    (fun v k hk => hfree.reads v k (by simp at hk; subst hk; decide))
    (fun v k hk => hfree.reads v k (by simp at hk; subst hk; decide)) hi hap
    (fun k hk => by simp at hk; subst hk; decide) hap' x.1 (strsOf Fr₂ x.2)
    (fun k hk => by simp at hk; subst hk; exact hno 4 four_pinned)
    (fun k hk => by simp at hk; subst hk; exact hp4)
    (fun k hk => by simp at hk; subst hk; exact hm4)
  have hval : ∀ o ∈ G0.members.toList, ∀ pt, ∀ i < Means.tableSize x.1.2.st o pt,
      _root_.Desc.K14.Law.wordsT csKey mem rd μ o pt i =
        OnBytes.Slice.readE (valOf (plan₂ S) (kreadFam (Cells := Cells) csKey six numSix atSix tab)
          (layAt atSix [5] (tblOf μ) w) o pt i) := by
    intro o ho pt i _
    rcases hg1 o ho with rfl | rfl
    · exact K12Hval.hval_of_links csKey (plan₂ S) _ mem rd hrd μ _ 3 5 ⟨sixS, i5⟩ hmem3 rfl
        ((hread 5 (Or.inl (by simp))).trans (tblOf_at μ i5))
        (fun part j => read_val _ _ _ _ _ _ _ _) pt i
    · exact K12Hval.hval_of_links csKey (plan₂ S) _ mem rd hrd μ _ 2 4 ⟨sixS, i4⟩ hmem2 rfl
        ((hread 4 (Or.inr (by simp))).trans (tblOf_at μ i4))
        (fun part j => read_val _ _ _ _ _ _ _ _) pt i
  obtain ⟨hrows, hsr⟩ := GrowsOfAllSay.holds_of_allSay hfree.order hK hG _ hall _ hval
  exact items_210 F _ atSix S K₁ _ enc rad x.1 (strsOf Fr₂ x.2) _ G0 x0 hG hg3 hx hsmd hss
    hrows (hsr 3 hg2 x0 hx)
    (K12LawLay.pin_laid F _ atSix [5] (tblOf μ) w arr5 hi hap x.1 (strsOf Fr₂ x.2) 5 (by simp) hm5)

/-- **Row 2.10's «law», from the seam's core's conclusion**: no term of the game, none of the
place. -/
theorem law_210_of_core
    (smp : (P₂ × St₂) → (s : Sound.Sending) → (i : Fin s.l.length) →
      Option ((sigOf csKey s.l).om i).Smp)
    (mem : ℕ → Option Sound.Mem)
    (rd : (x : Sound.Mem) → ((sigOf csKey x.1.l).om x.2).Msg → OnBytes.Part → ℕ → GE)
    (hrd : ∀ x m part i, rd x m part i = tabP csKey (x.1.l.get x.2).1 m part i)
    (x y : (P₂ × St₂) × Fr₂.E.Str)
    (hon : on₂ F Fr₂ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix S K₁
      (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad a coll last₁ off₂ 10 x)
    (hcore : ∃ t G0, Seat.enter (·.gOmega) (fun _ => none) x.1.2 = .ok t ∧
      t.st.groups[t.g]? = some G0 ∧
      ∃ m : (z : Sound.Mem) → ((sigOf csKey z.1.l).om z.2).Msg,
        Means.AllSay OnBytes.Model.Reading.gl (begun t.st t.g G0) (runRows t.st G0).toList
          (_root_.Desc.K14.Law.wordsT csKey mem rd m) ∧
        ∀ z, z = ⟨sixS, i5⟩ ∨ z = ⟨sixS, i4⟩ →
          Sound.CandAt csKey F smp z x.1 (strsOf Fr₂ x.2) (m z))
    (hi : LayIdem (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂)
    (hlog : ∀ i : Fin six.length, i = i5 ∨ i = i4 → ∀ o,
      F.oracleAt (seatAt six numSix atSix i).1 = some o → o.logLength = aOf csKey (six.get i).1)
    (told : ∀ i : Fin six.length, i = i5 ∨ i = i4 →
      (F.oracleAt (seatAt six numSix atSix i).1).isSome = true)
    (hsm : ∀ i : Fin six.length, i = i5 ∨ i = i4 → ∀ σ : (OmAt csKey six i).Smp,
      smp x.1 sixS i = some σ → ∃ ρ : (OmAt csKey six i).Z.D,
        (OmAt csKey six i).Z.val σ.1 = (OmAt csKey six i).Z.val ρ ∧
        seedIsS csKey six numSix (rowIsK csKey six) (src₂ orc₁) i x.1 ρ σ.2)
    (hsh : ∀ i : Fin six.length, i = i5 ∨ i = i4 →
      Sound.ShownAt F csKey six (seatAt six numSix atSix) (strsOf Fr₂ x.2) i)
    (hmem3 : mem 3 = some ⟨sixS, i5⟩) (hmem2 : mem 2 = some ⟨sixS, i4⟩)
    (hK : Means.OpenKinds x.1.2.st)
    (hgrp : ∀ G0, x.1.2.st.groups[x.1.2.loc.gOmega]? = some G0 →
      (∀ o ∈ G0.members.toList, o = 3 ∨ o = 2) ∧ 3 ∈ G0.members.toList ∧ 0 + 1 ≤ G0.rows.size)
    (x0 : OnBytes.Oracle)
    (hx : x.1.2.st.oracles[3]? = some x0) (hsmd : x0.sampled = true)
    (hss : x0.sampleRows.size ≠ 0)
    (hsmp : (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂.smp y.1 (atSix 4).1
        (atSix 4).2 =
      (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂.smp x.1 (atSix 4).1
        (atSix 4).2)
    (hword : wordOf F (strsOf Fr₂ y.2) (atSix 4).1 (atSix 4).2 =
      wordOf F (strsOf Fr₂ x.2) (atSix 4).1 (atSix 4).2) :
    ∃ tbl : ℕ → Fill.Tab, ∀ (rw : KRow) (w : Wit Cells Unit Fill.Tab),
      rw.ins = [KItem.claim 2 "FoldO", .srow 5, .pin 5] →
      KItem.pin 4 ∈ rw.outs ++ rw.ctx →
      (∀ i ∈ rw.outs ++ rw.ctx,
        i.holds F (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix
          (meaning₂ S K₁ (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad) y.1
          (strsOf Fr₂ y.2) w) →
      ∀ i ∈ rw.ins,
        i.holds F (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix
          (meaning₂ S K₁ (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad) x.1
          (strsOf Fr₂ x.2) (layAt atSix [5] tbl w) := by
  obtain ⟨_, hhas, hfree, hno⟩ := id (hon.resolve_left (fun h => h trivial))
  obtain ⟨t, G0, ht, hG, μ, hall, hc⟩ := hcore
  cases ht
  obtain ⟨hg1, hg2, hg3⟩ := hgrp G0 hG
  have has : ∀ k ∈ pinned (open₂ 10),
      hasSmp (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ (atSix k).1
        (atSix k).2 x.1 = true := fun k hk => List.all_eq_true.1 hhas k hk
  have hm5 := member_of_core₂ F decT recOf orc₁ tab smp μ i5 (hlog i5 (Or.inl rfl))
    (told i5 (Or.inl rfl)) x.1 _ (has 5 (by decide)) (hsm i5 (Or.inl rfl)) (hsh i5 (Or.inl rfl))
    (hc _ (Or.inl rfl))
  have hm4 := member_of_core₂ F decT recOf orc₁ tab smp μ i4 (hlog i4 (Or.inr rfl))
    (told i4 (Or.inr rfl)) x.1 _ (has 4 (by decide)) (hsm i4 (Or.inr rfl)) (hsh i4 (Or.inr rfl))
    (hc _ (Or.inr rfl))
  have hap : SeatsApart atSix [5] [5] := by intro k hk k' hk' _; simp at hk hk'; omega
  have hap' : SeatsApart atSix [5] [4] := by
    intro k hk k' hk' e
    simp at hk hk'
    subst hk hk'
    exact absurd e (by decide)
  have arr5 : ArrOk (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix [5] :=
    fun k hk => hfree.arr k (by simp at hk; subst hk; decide)
  have arr4 : ArrOk (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix [4] :=
    fun k hk => hfree.arr k (by simp at hk; subst hk; decide)
  refine ⟨tblOf μ, fun rw w hins hctx hbehind => ?_⟩
  rw [hins]
  have hp4 := rides_pin2_at F _ (atSix 4).1 (atSix 4).2 x.1 y.1 (strsOf Fr₂ x.2) (strsOf Fr₂ y.2) w
    hsmp hword (hbehind _ hctx)
  have hread := K12LawLay.reads_all F _ atSix (kreadFam (Cells := Cells) csKey six numSix atSix tab)
    [5] [4] (tblOf μ) w arr5 arr4
    (fun v k hk => hfree.reads v k (by simp at hk; subst hk; decide))
    (fun v k hk => hfree.reads v k (by simp at hk; subst hk; decide)) hi hap
    (fun k hk => by simp at hk; subst hk; decide) hap' x.1 (strsOf Fr₂ x.2)
    (fun k hk => by simp at hk; subst hk; exact hno 4 four_pinned)
    (fun k hk => by simp at hk; subst hk; exact hp4)
    (fun k hk => by simp at hk; subst hk; exact hm4)
  have hval : ∀ o ∈ G0.members.toList, ∀ pt, ∀ i < Means.tableSize x.1.2.st o pt,
      _root_.Desc.K14.Law.wordsT csKey mem rd μ o pt i =
        OnBytes.Slice.readE (valOf (plan₂ S) (kreadFam (Cells := Cells) csKey six numSix atSix tab)
          (layAt atSix [5] (tblOf μ) w) o pt i) := by
    intro o ho pt i _
    rcases hg1 o ho with rfl | rfl
    · exact K12Hval.hval_of_links csKey (plan₂ S) _ mem rd hrd μ _ 3 5 ⟨sixS, i5⟩ hmem3 rfl
        ((hread 5 (Or.inl (by simp))).trans (tblOf_at μ i5))
        (fun part j => read_val _ _ _ _ _ _ _ _) pt i
    · exact K12Hval.hval_of_links csKey (plan₂ S) _ mem rd hrd μ _ 2 4 ⟨sixS, i4⟩ hmem2 rfl
        ((hread 4 (Or.inr (by simp))).trans (tblOf_at μ i4))
        (fun part j => read_val _ _ _ _ _ _ _ _) pt i
  obtain ⟨hrows, hsr⟩ := GrowsOfAllSay.holds_of_allSay hfree.order hK hG _ hall _ hval
  exact items_210 F _ atSix S K₁ _ enc rad x.1 (strsOf Fr₂ x.2) _ G0 x0 hG hg3 hx hsmd hss
    hrows (hsr 3 hg2 x0 hx)
    (K12LawLay.pin_laid F _ atSix [5] (tblOf μ) w arr5 hi hap x.1 (strsOf Fr₂ x.2) 5 (by simp) hm5)


/-- The second arm's relation holds the first's, at the numbering by labels from the chain's first
own tree on: what it says besides of the first switch's openings is dropped. -/
theorem qw_of_qwo {P S : Type} {Fr : Frame} {π : P12} {t₁ t₂ ch : ℕ} {r : Fmt.M1.Stage → ℕ}
    {rdN : ℕ → ℕ} {enter : S → Except String T12} {leave : S → T12 → Except String S}
    {a b : (P × S) × Fr.E.Str} (h : QWO Fr π t₁ t₂ ch r rdN enter leave a b) :
    QW Fr π (nlAt π (numAt t₁ t₂ ch (.own 0))) r rdN enter leave a b := by
  obtain ⟨t, tE, h1, h2, hQ, h3⟩ := h
  exact ⟨t, tE, h1, h2, hQ.2, h3⟩

/-- **Row 2.10's «law» with «left» member by member**: at any numbering by labels nl. Nothing is
asked of the first tree or of the book: BUT clause (7) of `MemberLeft` stands at the number
nuOf π nl t: whoever pays it needs the book's order to know that label. -/
theorem law_210_coreM (π : P12) (nl : ℕ → ℕ) (r : Fmt.M1.Stage → ℕ) (rdN : ℕ → ℕ)
    (smp : (P₂ × St₂) → (s : Sound.Sending) → (i : Fin s.l.length) →
      Option ((sigOf csKey s.l).om i).Smp)
    (mem : ℕ → Option Sound.Mem)
    (rd : (x : Sound.Mem) → ((sigOf csKey x.1.l).om x.2).Msg → OnBytes.Part → ℕ → GE)
    (hrd : ∀ x m part i, rd x m part i = tabP csKey (x.1.l.get x.2).1 m part i)
    (x y : (P₂ × St₂) × Fr₂.E.Str)
    (hQ : QW Fr₂ π nl r rdN (Seat.enter (·.gOmega) (fun _ => none)) Seat.leave x y)
    (hon : on₂ F Fr₂ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix S K₁
      (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad a coll last₁ off₂ 10 x)
    (hj : johOk π r = true) (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (left : ∀ t, Seat.enter (·.gOmega) (fun _ => none) x.1.2 = .ok t → ∀ (s : Fmt.M1.Stage)
      (rest : List Fmt.M1.Stage) (G0 : OnBytes.Group) (Ly : OnBytes.GroupLayout)
      (D : H2K.First.Plain),
      Fixes π t s rest G0 Ly D →
      D.st.codes = csKey ∧
      ∃ (xs : Fin D.mems.length → Sound.Mem) (es : Fin D.mems.length → ℕ),
        Function.Injective xs ∧
        (∀ z, z = ⟨sixS, i5⟩ ∨ z = ⟨sixS, i4⟩ → ∃ j, xs j = z) ∧
        ∀ j : Fin D.mems.length,
          MemberLeft csKey F Fr₂ (nuOf π nl t) (fun q => r q.st) smp mem x.2 x.1
            (strsOf Fr₂ x.2) s D j (xs j) (es j))
    (hi : LayIdem (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂)
    (hlog : ∀ i : Fin six.length, i = i5 ∨ i = i4 → ∀ o,
      F.oracleAt (seatAt six numSix atSix i).1 = some o → o.logLength = aOf csKey (six.get i).1)
    (told : ∀ i : Fin six.length, i = i5 ∨ i = i4 →
      (F.oracleAt (seatAt six numSix atSix i).1).isSome = true)
    (hsm : ∀ i : Fin six.length, i = i5 ∨ i = i4 → ∀ σ : (OmAt csKey six i).Smp,
      smp x.1 sixS i = some σ → ∃ ρ : (OmAt csKey six i).Z.D,
        (OmAt csKey six i).Z.val σ.1 = (OmAt csKey six i).Z.val ρ ∧
        seedIsS csKey six numSix (rowIsK csKey six) (src₂ orc₁) i x.1 ρ σ.2)
    (hsh : ∀ i : Fin six.length, i = i5 ∨ i = i4 →
      Sound.ShownAt F csKey six (seatAt six numSix atSix) (strsOf Fr₂ x.2) i)
    (hmem3 : mem 3 = some ⟨sixS, i5⟩) (hmem2 : mem 2 = some ⟨sixS, i4⟩)
    (hK : Means.OpenKinds x.1.2.st)
    (hgrp : ∀ G0, x.1.2.st.groups[x.1.2.loc.gOmega]? = some G0 →
      (∀ o ∈ G0.members.toList, o = 3 ∨ o = 2) ∧ 3 ∈ G0.members.toList ∧ 0 + 1 ≤ G0.rows.size)
    (x0 : OnBytes.Oracle)
    (hx : x.1.2.st.oracles[3]? = some x0) (hsmd : x0.sampled = true)
    (hss : x0.sampleRows.size ≠ 0)
    (hsmp : (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂.smp y.1 (atSix 4).1
        (atSix 4).2 =
      (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂.smp x.1 (atSix 4).1
        (atSix 4).2)
    (hword : wordOf F (strsOf Fr₂ y.2) (atSix 4).1 (atSix 4).2 =
      wordOf F (strsOf Fr₂ x.2) (atSix 4).1 (atSix 4).2) :
    ∃ tbl : ℕ → Fill.Tab, ∀ (rw : KRow) (w : Wit Cells Unit Fill.Tab),
      rw.ins = [KItem.claim 2 "FoldO", .srow 5, .pin 5] →
      KItem.pin 4 ∈ rw.outs ++ rw.ctx →
      (∀ i ∈ rw.outs ++ rw.ctx,
        i.holds F (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix
          (meaning₂ S K₁ (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad) y.1
          (strsOf Fr₂ y.2) w) →
      ∀ i ∈ rw.ins,
        i.holds F (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix
          (meaning₂ S K₁ (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad) x.1
          (strsOf Fr₂ x.2) (layAt atSix [5] tbl w) := by
  obtain ⟨_, _, hfree, _⟩ := id (hon.resolve_left (fun h => h trivial))
  exact law_210_of_core F Fr₂ decT recOf orc₁ tab S K₁ enc rad a coll last₁ off₂ smp mem rd hrd x y
    hon
    (core_behind_QWm csKey F Fr₂ π nl r rdN smp mem _ rd hrd _ _ x y x.1 (strsOf Fr₂ x.2) hQ hj hp
      left (fun t ht => by cases ht; exact hfree.order))
    hi hlog told hsm hsh hmem3 hmem2 hK hgrp x0 hx hsmd hss hsmp hword

/-- **The same off the piece's own acceptance.** -/
theorem back_210 {Cl W : Type} (π : P12) (t₁ t₂ : ℕ) (r : Fmt.M1.Stage → ℕ) (rdN : ℕ → ℕ)
    (smp : (P₂ × St₂) → (s : Sound.Sending) → (i : Fin s.l.length) →
      Option ((sigOf csKey s.l).om i).Smp)
    (mem : ℕ → Option Sound.Mem)
    (rd : (x : Sound.Mem) → ((sigOf csKey x.1.l).om x.2).Msg → OnBytes.Part → ℕ → GE)
    (hrd : ∀ x m part i, rd x m part i = tabP csKey (x.1.l.get x.2).1 m part i)
    (p : Piece (ckP .two) Fr₂ (P₂ × St₂) Cl W) (B : Block St₂ Cl) (hb : p.b = held B)
    (hal : Alike ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside
      (Seat.enter (·.gOmega) (fun _ => none)) Seat.leave) B)
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (x y : (P₂ × St₂) × Fr₂.E.Str) (τ : Iop.Tr (uLT (ckP .two) p.ds))
    (hout : p.ior.red.out x τ = some y)
    (hq : ∃ t t', Seat.enter (·.gOmega) (fun _ => none) x.1.2 = .ok t ∧
      (Seat.leave x.1.2 t' = .ok y.1.2 ∧ y.1.1 = x.1.1) ∧
      QO Fr₂ π t₁ t₂ 1 (fun s => r s.st) rdN (t, x.2))
    (hft : π.nums.firstTree = 0)
    (hon : on₂ F Fr₂ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix S K₁
      (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad a coll last₁ off₂ 10 x)
    (hj : johOk π r = true)
    (left : ∀ t, Seat.enter (·.gOmega) (fun _ => none) x.1.2 = .ok t →
      CoreLeft csKey F Fr₂ π (noAt t₁ t₂ 1) (fun s => r s.st) smp mem
        (fun z => z = ⟨sixS, i5⟩ ∨ z = ⟨sixS, i4⟩) t x.2 x.1 (strsOf Fr₂ x.2))
    (hi : LayIdem (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂)
    (hlog : ∀ i : Fin six.length, i = i5 ∨ i = i4 → ∀ o,
      F.oracleAt (seatAt six numSix atSix i).1 = some o → o.logLength = aOf csKey (six.get i).1)
    (told : ∀ i : Fin six.length, i = i5 ∨ i = i4 →
      (F.oracleAt (seatAt six numSix atSix i).1).isSome = true)
    (hsm : ∀ i : Fin six.length, i = i5 ∨ i = i4 → ∀ σ : (OmAt csKey six i).Smp,
      smp x.1 sixS i = some σ → ∃ ρ : (OmAt csKey six i).Z.D,
        (OmAt csKey six i).Z.val σ.1 = (OmAt csKey six i).Z.val ρ ∧
        seedIsS csKey six numSix (rowIsK csKey six) (src₂ orc₁) i x.1 ρ σ.2)
    (hsh : ∀ i : Fin six.length, i = i5 ∨ i = i4 →
      Sound.ShownAt F csKey six (seatAt six numSix atSix) (strsOf Fr₂ x.2) i)
    (hmem3 : mem 3 = some ⟨sixS, i5⟩) (hmem2 : mem 2 = some ⟨sixS, i4⟩)
    (hK : Means.OpenKinds x.1.2.st)
    (hgrp : ∀ G0, x.1.2.st.groups[x.1.2.loc.gOmega]? = some G0 →
      (∀ o ∈ G0.members.toList, o = 3 ∨ o = 2) ∧ 3 ∈ G0.members.toList ∧ 0 + 1 ≤ G0.rows.size)
    (x0 : OnBytes.Oracle)
    (hx : x.1.2.st.oracles[3]? = some x0) (hsmd : x0.sampled = true)
    (hss : x0.sampleRows.size ≠ 0)
    (hSm : (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).SmOnly)
    (hlt : ∀ o, orc₂ ((baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).arr
      (atSix 4).1 (atSix 4).2) = some o → o < x.1.2.st.oracles.size)
    (hbase : (atSix 4).1 < p.base) :
    ∃ tbl : ℕ → Fill.Tab, ∀ (rw : KRow) (w : Wit Cells Unit Fill.Tab),
      rw.ins = [KItem.claim 2 "FoldO", .srow 5, .pin 5] →
      KItem.pin 4 ∈ rw.outs ++ rw.ctx →
      (∀ i ∈ rw.outs ++ rw.ctx,
        i.holds F (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix
          (meaning₂ S K₁ (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad) y.1
          (strsOf Fr₂ y.2) w) →
      ∀ i ∈ rw.ins,
        i.holds F (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix
          (meaning₂ S K₁ (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad) x.1
          (strsOf Fr₂ x.2) (layAt atSix [5] tbl w) := by
  obtain ⟨t, t', h1, ⟨h2, _⟩, h3⟩ := hq
  obtain ⟨hsmp, hword⟩ := K12RidingStays.riding_stays₂
    (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁) F Fr₂ hSm (·.gOmega)
    (fun _ => none) π (H2K.JointK.early_of_planOk π hp) (H2K.JointK.answers_of_planOk π hp) p B hb
    hal x y τ hout (atSix 4).1 (atSix 4).2 (fun o ho => ⟨hlt o ho, by simp⟩) hbase
  have hQ := qwo_of_yes π t₁ t₂ 1 r rdN _ _ p B hb hal x y τ hout ⟨t, t', h1, h2, h3⟩
  exact law_210_coreF F Fr₂ decT recOf orc₁ tab S K₁ enc rad a coll last₁ off₂ π t₁ t₂ r rdN smp mem
    rd hrd x y hQ hft hon
    (fun s hs => by
      obtain ⟨s₀, sE, k1, _, _, rs, gs, k3⟩ := id hQ
      obtain rfl : s₀ = s := Except.ok.inj (k1.symm.trans hs)
      exact coreFacts_of_yes csKey F Fr₂ π _ r smp mem _ s₀ sE x.2 x.1 (strsOf Fr₂ x.2) hj
        (H2K.JointK.early_of_planOk π hp) hp rs gs k3 (left _ hs))
    hi hlog told hsm hsh hmem3 hmem2 hK hgrp x0 hx hsmd hss hsmp hword

/-- **Row 2.10's «law» off the piece's own acceptance, with «left» member by member.** The
numbering is the second arm's own: by labels, from the chain's first own tree on. -/
theorem back_210M {Cl W : Type} (π : P12) (t₁ t₂ : ℕ) (r : Fmt.M1.Stage → ℕ) (rdN : ℕ → ℕ)
    (smp : (P₂ × St₂) → (s : Sound.Sending) → (i : Fin s.l.length) →
      Option ((sigOf csKey s.l).om i).Smp)
    (mem : ℕ → Option Sound.Mem)
    (rd : (x : Sound.Mem) → ((sigOf csKey x.1.l).om x.2).Msg → OnBytes.Part → ℕ → GE)
    (hrd : ∀ x m part i, rd x m part i = tabP csKey (x.1.l.get x.2).1 m part i)
    (p : Piece (ckP .two) Fr₂ (P₂ × St₂) Cl W) (B : Block St₂ Cl) (hb : p.b = held B)
    (hal : Alike ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside
      (Seat.enter (·.gOmega) (fun _ => none)) Seat.leave) B)
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (x y : (P₂ × St₂) × Fr₂.E.Str) (τ : Iop.Tr (uLT (ckP .two) p.ds))
    (hout : p.ior.red.out x τ = some y)
    (hq : ∃ t t', Seat.enter (·.gOmega) (fun _ => none) x.1.2 = .ok t ∧
      (Seat.leave x.1.2 t' = .ok y.1.2 ∧ y.1.1 = x.1.1) ∧
      QO Fr₂ π t₁ t₂ 1 (fun s => r s.st) rdN (t, x.2))
    (hon : on₂ F Fr₂ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix S K₁
      (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad a coll last₁ off₂ 10 x)
    (hj : johOk π r = true)
    (left : ∀ t, Seat.enter (·.gOmega) (fun _ => none) x.1.2 = .ok t → ∀ (s : Fmt.M1.Stage)
      (rest : List Fmt.M1.Stage) (G0 : OnBytes.Group) (Ly : OnBytes.GroupLayout)
      (D : H2K.First.Plain),
      Fixes π t s rest G0 Ly D →
      D.st.codes = csKey ∧
      ∃ (xs : Fin D.mems.length → Sound.Mem) (es : Fin D.mems.length → ℕ),
        Function.Injective xs ∧
        (∀ z, z = ⟨sixS, i5⟩ ∨ z = ⟨sixS, i4⟩ → ∃ j, xs j = z) ∧
        ∀ j : Fin D.mems.length,
          MemberLeft csKey F Fr₂ (nuOf π (nlAt π (numAt t₁ t₂ 1 (.own 0))) t) (fun q => r q.st)
            smp mem x.2 x.1 (strsOf Fr₂ x.2) s D j (xs j) (es j))
    (hi : LayIdem (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂)
    (hlog : ∀ i : Fin six.length, i = i5 ∨ i = i4 → ∀ o,
      F.oracleAt (seatAt six numSix atSix i).1 = some o → o.logLength = aOf csKey (six.get i).1)
    (told : ∀ i : Fin six.length, i = i5 ∨ i = i4 →
      (F.oracleAt (seatAt six numSix atSix i).1).isSome = true)
    (hsm : ∀ i : Fin six.length, i = i5 ∨ i = i4 → ∀ σ : (OmAt csKey six i).Smp,
      smp x.1 sixS i = some σ → ∃ ρ : (OmAt csKey six i).Z.D,
        (OmAt csKey six i).Z.val σ.1 = (OmAt csKey six i).Z.val ρ ∧
        seedIsS csKey six numSix (rowIsK csKey six) (src₂ orc₁) i x.1 ρ σ.2)
    (hsh : ∀ i : Fin six.length, i = i5 ∨ i = i4 →
      Sound.ShownAt F csKey six (seatAt six numSix atSix) (strsOf Fr₂ x.2) i)
    (hmem3 : mem 3 = some ⟨sixS, i5⟩) (hmem2 : mem 2 = some ⟨sixS, i4⟩)
    (hK : Means.OpenKinds x.1.2.st)
    (hgrp : ∀ G0, x.1.2.st.groups[x.1.2.loc.gOmega]? = some G0 →
      (∀ o ∈ G0.members.toList, o = 3 ∨ o = 2) ∧ 3 ∈ G0.members.toList ∧ 0 + 1 ≤ G0.rows.size)
    (x0 : OnBytes.Oracle)
    (hx : x.1.2.st.oracles[3]? = some x0) (hsmd : x0.sampled = true)
    (hss : x0.sampleRows.size ≠ 0)
    (hSm : (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).SmOnly)
    (hlt : ∀ o, orc₂ ((baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).arr
      (atSix 4).1 (atSix 4).2) = some o → o < x.1.2.st.oracles.size)
    (hbase : (atSix 4).1 < p.base) :
    ∃ tbl : ℕ → Fill.Tab, ∀ (rw : KRow) (w : Wit Cells Unit Fill.Tab),
      rw.ins = [KItem.claim 2 "FoldO", .srow 5, .pin 5] →
      KItem.pin 4 ∈ rw.outs ++ rw.ctx →
      (∀ i ∈ rw.outs ++ rw.ctx,
        i.holds F (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix
          (meaning₂ S K₁ (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad) y.1
          (strsOf Fr₂ y.2) w) →
      ∀ i ∈ rw.ins,
        i.holds F (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix
          (meaning₂ S K₁ (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad) x.1
          (strsOf Fr₂ x.2) (layAt atSix [5] tbl w) := by
  obtain ⟨t, t', h1, ⟨h2, _⟩, h3⟩ := hq
  obtain ⟨hsmp, hword⟩ := K12RidingStays.riding_stays₂
    (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁) F Fr₂ hSm (·.gOmega)
    (fun _ => none) π (H2K.JointK.early_of_planOk π hp) (H2K.JointK.answers_of_planOk π hp) p B hb
    hal x y τ hout (atSix 4).1 (atSix 4).2 (fun o ho => ⟨hlt o ho, by simp⟩) hbase
  exact law_210_coreM F Fr₂ decT recOf orc₁ tab S K₁ enc rad a coll last₁ off₂ π _ r rdN smp mem rd
    hrd x y (qw_of_qwo (qwo_of_yes π t₁ t₂ 1 r rdN _ _ p B hb hal x y τ hout ⟨t, t', h1, h2, h3⟩))
    hon hj hp left hi hlog told hsm hsh hmem3 hmem2 hK hgrp x0 hx hsmd hss hsmp hword

end Johnson.RunOne.Law.K12Back210

#print axioms Johnson.RunOne.Law.K12Back210.law_210_coreF
#print axioms Johnson.RunOne.Law.K12Back210.back_210
#print axioms Johnson.RunOne.Law.K12Back210.law_210_of_core
#print axioms Johnson.RunOne.Law.K12Back210.qw_of_qwo
#print axioms Johnson.RunOne.Law.K12Back210.law_210_coreM
#print axioms Johnson.RunOne.Law.K12Back210.back_210M
