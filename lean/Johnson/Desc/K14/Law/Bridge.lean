-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/Bridge.lean: from a plain law of a block (what a yes is made of; a count of
drawn values) to what the rule of composition asks of the block at its stretch (Piece.GoodIn).

  shownGroups     the groups of columns that the format's step makes, for a block, of what is shown.
  step_groups, single_groups, piece_groups   where a step, the fold at one block, a piece's
                  reduction says yes, the block's decision has said yes on the rounds shown, without
                  their sealed digests, AND ON THESE GROUPS: both are named.
  single_yes      the second of these with the groups under "there is".
  piece_yes       where a piece's reduction puts out a statement: its oracles are those that the
                  stretch leaves, and its record is what the block's decision returns at the record
                  in front, on the stretch's own rounds.
  piece_tests     there the tests that stand before the run have passed.
  goodIn_keep     a promise that every yes keeps may stand on both sides.
  goodIn_of_count **THE BRIDGE**: let the stretch's written rounds read as one typed draw of a value
                  of Z (the library's drawRound Z, Ior/Draw.lean; a carriage whose errors fit); let
                  the statement in front fix a set of lost values, no more than c; let a yes at a
                  value that is not lost keep the promise and carry a witness back. Then the piece
                  has GoodIn at its written errors.
No kind is named in this file. Where no draw counts, goodIn_of_sure
(Johnson/Desc/ChainEndGoodIn.lean) is the rule.

What is not claimed. The carriage, that its errors fit, and that it reads the value which the block
reads are premises. A block that refuses all has GoodIn too. Nothing on soundness of a protocol.

-/
import Johnson.Desc.ChainEndGoodIn
import Ior.Draw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open Iop Prob OnBytes.Maker OnBytes.Flat
open VerifiableInference.Desc (Block chainAt foldBlocks noDigest groupsOf regroup OpenedColumn)
open VerifiableInference.Desc.Sound (Frame Piece foldRun)
open _root_.Run.PQ (CK)
open Iop.IOR (drawRound)

/-- The groups of columns that the format's step makes, for a block, of what is shown. -/
def shownGroups {S Cl : Type} (ft : Nat) (b : Block S Cl) (rs : List Fmt.RoundView) (cols : List OpenedColumn) :
    List (List (Nat × List UInt64)) :=
  regroup ((groupsOf ft b.rounds (rs.map (·.drawn))).map (·.length))
    (cols.take ((groupsOf ft b.rounds (rs.map (·.drawn))).flatMap id).length)

/-- Where a block's step says yes, its decision has said yes on these groups. -/
theorem step_groups {S Cl : Type} (ft : Nat) (b : Block S Cl) (s s' : S) (rs : List Fmt.RoundView)
    (cols : List OpenedColumn) (k : Nat) (h : b.step ft s rs cols = .ok (s', k)) :
    b.decide s (rs.map noDigest) (shownGroups ft b rs cols) = .ok s' := by
  unfold Block.step at h
  dsimp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i v hv
        cases h
        exact hv

/-- The same where the fold at one block says yes. -/
theorem single_groups {T Cl : Type} {name : String} {ft : Nat} {b : Block T Cl} {s s' : T}
    {v : Fmt.View} (h : (chainAt name ft [b] s v).toOption = some s') :
    b.decide s (v.rounds.map noDigest) (shownGroups ft b v.rounds v.opened) = .ok s' := by
  unfold chainAt at h
  simp only [List.isEmpty_cons, Bool.false_eq_true, if_false] at h
  cases hfb : foldBlocks ft [b] s v.rounds v.opened with
  | error e =>
    rw [hfb] at h
    cases h
  | ok z =>
    obtain ⟨s1, rs1, c1⟩ := z
    rw [hfb] at h
    simp only [foldBlocks, List.splitAt_eq] at hfb
    split at hfb
    · cases hfb
    · split at hfb
      · cases hfb
      · next s2 k hst =>
        obtain ⟨rfl, rfl, rfl⟩ : s2 = s1 ∧ v.rounds.drop b.rounds.length = rs1 ∧
            v.opened.drop k = c1 := by
          have := Except.ok.inj hfb
          exact ⟨congrArg (·.1) this, congrArg (·.2.1) this, congrArg (·.2.2) this⟩
        cases hd : v.rounds.drop b.rounds.length with
        | cons _ _ =>
          rw [hd] at h
          cases h
        | nil =>
          cases hc : v.opened.drop k with
          | cons _ _ =>
            rw [hd, hc] at h
            cases h
          | nil =>
            rw [hd, hc] at h
            obtain rfl := Option.some.inj h
            rw [List.take_of_length_le (List.drop_eq_nil_iff.1 hd)] at hst
            exact step_groups ft b s s2 _ _ k hst

/-- **Where the fold at one block says yes**, the block's own decision has said yes on all the
rounds shown. It says more than single_decide (Johnson/Desc/ChainEndGoodIn.lean), which has the
rounds under "there is": here they are named. -/
theorem single_yes {T Cl : Type} {name : String} {ft : Nat} {b : Block T Cl} {s s' : T}
    {v : Fmt.View} (h : (chainAt name ft [b] s v).toOption = some s') :
    ∃ gs, b.decide s (v.rounds.map noDigest) gs = .ok s' :=
  ⟨_, single_groups h⟩

variable {S Cl W : Type} {C : CK} {F : Frame}

/-- **Where a piece's reduction puts out a statement.** It says more than Piece.out_of_decide
(Johnson/Desc/ChainEndGoodIn.lean): the rounds on which the decision has said yes are named. -/
theorem piece_yes (p : Piece C F S Cl W) (a : S × F.E.Str) (τ : Tr (uLT C p.ds))
    (b : S × F.E.Str) (h : p.ior.red.out a τ = some b) :
    b.2 = p.ior.imp a.2 τ ∧
      ∃ gs, p.b.decide a.1 ((rvT C p.ds τ ++ p.back).map noDigest) gs = .ok b.1 := by
  obtain ⟨s, y⟩ := a
  have h' : (if sTests C p.stage y τ = true then p.run s (sView C p.stage y τ) else none).map
      (fun xo => (xo, p.ior.imp y τ)) = some b := h
  split at h'
  · cases hr : p.run s (sView C p.stage y τ) with
    | none => rw [hr] at h'; cases h'
    | some xo =>
      rw [hr] at h'
      simp only [Option.map_some, Option.some.injEq] at h'
      subst h'
      exact ⟨rfl, single_yes hr⟩
  · cases h'

/-- The same where a piece's reduction puts out a statement. -/
theorem piece_groups (p : Piece C F S Cl W) (a : S × F.E.Str) (τ : Tr (uLT C p.ds))
    (b : S × F.E.Str) (h : p.ior.red.out a τ = some b) :
    p.b.decide a.1 ((rvT C p.ds τ ++ p.back).map noDigest)
      (shownGroups F.ft p.b (rvT C p.ds τ ++ p.back) (sView C p.stage a.2 τ).opened) = .ok b.1 := by
  obtain ⟨s, y⟩ := a
  have h' : (if sTests C p.stage y τ = true then p.run s (sView C p.stage y τ) else none).map
      (fun xo => (xo, p.ior.imp y τ)) = some b := h
  split at h'
  · cases hr : p.run s (sView C p.stage y τ) with
    | none => rw [hr] at h'; cases h'
    | some xo =>
      rw [hr] at h'
      simp only [Option.map_some, Option.some.injEq] at h'
      subst h'
      exact single_groups hr
  · cases h'

/-- Where a piece's reduction puts out a statement, the tests that stand before the run have
passed. -/
theorem piece_tests (p : Piece C F S Cl W) (a : S × F.E.Str) (τ : Tr (uLT C p.ds))
    (b : S × F.E.Str) (h : p.ior.red.out a τ = some b) : sTests C p.stage a.2 τ = true := by
  obtain ⟨s, y⟩ := a
  have h' : (if sTests C p.stage y τ = true then p.run s (sView C p.stage y τ) else none).map
      (fun xo => (xo, p.ior.imp y τ)) = some b := h
  split at h'
  · assumption
  · cases h'

/-- A promise that every yes keeps may stand on both sides. -/
theorem goodIn_keep (p : Piece C F S Cl W) (on on' : S × F.E.Str → Prop)
    (R R' : S × F.E.Str → W → Prop) (Prm : S × F.E.Str → Prop)
    (hk : ∀ a τ b, on a → p.ior.red.out a τ = some b → Prm a → Prm b) (h : p.GoodIn on on' R R') :
    p.GoodIn (fun a => on a ∧ Prm a) (fun b => on' b ∧ Prm b) R R' :=
  fun a ha => Doomed.mono _ _
    (fun τ hτ b hb => ⟨⟨(hτ b hb).1, hk a τ b ha.1 hb ha.2⟩, (hτ b hb).2⟩) (h a ha.1)

/-- **THE BRIDGE**: an inversion and a count give GoodIn. -/
theorem goodIn_of_count (p : Piece C F S Cl W) (on on' : S × F.E.Str → Prop)
    (R R' : S × F.E.Str → W → Prop) (Z : Type) [Fintype Z] [Nonempty Z] (c : Nat)
    (G : S × F.E.Str → CarryS (uLT C p.ds) [drawRound Z])
    (fits : ∀ a, (G a).Fits ((c, ()) : Nat × Unit) p.err)
    (Lost : S × F.E.Str → Z → Prop) (hcount : ∀ a, on a → cnt (Lost a) ≤ c)
    (hinv : ∀ a τ b, on a → p.ior.red.out a τ = some b →
      ∃ τ', (G a).tr τ = some τ' ∧
        (¬ Lost a τ'.2.1 → on' b ∧ ∀ w, R' b w → R a (p.ext a τ w))) :
    p.GoodIn on on' R R' := by
  intro a ha
  refine CarryS.doomed (G a) _ _ (fits a) _ (fun τ' => ¬ Lost a τ'.2.1) ?_ ?_ ?_
  · intro τ hτ b hb
    obtain ⟨τ', h1, _⟩ := hinv a τ b ha hb
    rw [hτ] at h1
    cases h1
  · intro τ τ' hτ hbad b hb
    obtain ⟨τ'', h1, h2⟩ := hinv a τ b ha hb
    rw [hτ] at h1
    cases h1
    exact h2 hbad
  · exact fun _ => le_trans (cnt_mono fun z hz => not_not.1 hz) (hcount a ha)

/-- A count of a property, as the number of elements of a filter. -/
theorem cnt_eq_card {α : Type} [Fintype α] (P : α → Prop) [DecidablePred P] :
    cnt P = (Finset.univ.filter P).card := by
  unfold cnt
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

end Desc.K14.Law
