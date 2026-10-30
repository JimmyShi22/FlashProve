-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/LocNear.lean: the count of (loc_x) against "near": if the code word of the
folded row is NOT within e' locations of the fold of the stored table's columns, few lists of drawn
locations can pass.

  NearAt          at no more than e' locations does (loc_x)'s equation fail: the code word of
                  (u, r_u), as the words hold it, is within e' locations of the fold of the table's
                  columns.
  card_locAt_lt   if not, the locations at which the equation holds are at most n - e' - 1, n the
                  number of locations.
  loc_near_run, loc_near_blocks   then the lists of c locations at which a run can go on to the two
                  tests so that all constraints hold of words that agree with the fixed ones on o_u
                  are no more than (n - e' - 1) ^ c: along a run; of the blocks' own decisions.
  near_iff        NearAt is the library's NearW (Cb/Ld/LdFoldEq.lean) at the typed data of the
                  encoded index that is made of the public shape.

What is not claimed. That the columns handed are the stored table's stands inside the counted event.
Nothing on what "near" gives of the folded row's message: that is the statement on codes' and the
record's. Nothing on how the locations are drawn. No soundness of a verifier.

-/
import Johnson.Desc.K14.Law.StepsSound
import Johnson.Desc.K14.Law.TypedIx

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open OnBytes.Means (Words)
open VerifiableInference.Desc (Block)

variable {K : Type} [Field K] (ρ : OnBytes.Model.Reading K)

open Classical in
/-- The code word of the folded row is within e' locations of the fold of the table's columns. -/
def NearAt (p : Par) (d : St) (m : Words K) (tab : Nat → List UInt64) (e' : Nat) : Prop :=
  (Finset.univ.filter fun x : Fin (2 ^ p.S.fold.index.code.logN) =>
    ¬ LocAt ρ p d m tab x.val).card ≤ e'

open Classical in
/-- If it is not, the equation holds at few locations. -/
theorem card_locAt_lt (p : Par) (d : St) (m : Words K) (tab : Nat → List UInt64) (e' : Nat)
    (h : ¬ NearAt ρ p d m tab e') :
    (Finset.univ.filter fun x : Fin (2 ^ p.S.fold.index.code.logN) =>
      LocAt ρ p d m tab x.val).card ≤ 2 ^ p.S.fold.index.code.logN - e' - 1 := by
  have hs := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin (2 ^ p.S.fold.index.code.logN))))
    (fun x => LocAt ρ p d m tab x.val)
  rw [Finset.card_univ, Fintype.card_fin] at hs
  unfold NearAt at h
  omega

open Classical in
/-- **The law of (loc_x) against "near", along a run.** -/
theorem loc_near_run (p : Par) (d0 d2 d3 : St) (m : Words K) (tab : Nat → List UInt64)
    (c e' : Nat) (h : ¬ NearAt ρ p d3 m tab e') :
    (Finset.univ.filter fun Q : Fin c → Fin (2 ^ p.S.fold.index.code.logN) =>
      ∃ (r4 : Fmt.RoundView) (cols : List (Nat × List UInt64)) (d7 d8 eU eO : St) (m' : Words K),
        r4.drawn.poss = List.ofFn (fun i => (Q i).val) ∧
        (∀ x col, cols.lookup x = some col → col = tab x) ∧
        SharedRun p d0 d2 d3 d7 d8 r4 cols ∧
        Reaches d8 eU d8.loc.gU ∧ Reaches d8 eO d8.loc.gOmega ∧ AgreeOn d3.loc.oU.oracle m m' ∧
        Means.AllSay ρ eU.st (rowsOn eU d8.loc.gU) m' ∧
        Means.AllSay ρ eO.st (rowsOn eO d8.loc.gOmega) m').card ≤
      (2 ^ p.S.fold.index.code.logN - e' - 1) ^ c :=
  le_trans (loc_sound_run ρ p d0 d2 d3 m tab c)
    (Nat.pow_le_pow_left (card_locAt_lt ρ p d3 m tab e' h) c)

open Classical in
/-- **The same, of the blocks' own decisions.** -/
theorem loc_near_blocks (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (hS : P.S.sharedSplitNeeded = true) (d0 d1 d2 d3 : St) (rs1 rs2 rs3 : List Fmt.RoundView)
    (gs1 gs2 gs3 : List (List (Nat × List UInt64)))
    (h1 : b1.decide d0 rs1 gs1 = .ok d1) (h2 : b2.decide d1 rs2 gs2 = .ok d2)
    (h3 : b3.decide d2 rs3 gs3 = .ok d3) (m : Words K) (tab : Nat → List UInt64) (c e' : Nat)
    (h : ¬ NearAt ρ P.par d3 m tab e') :
    (Finset.univ.filter fun Q : Fin c → Fin (2 ^ P.S.fold.index.code.logN) =>
      ∃ (r4 : Fmt.RoundView) (cols : List (Nat × List UInt64)) (rs5 rs6 rs7 rs8 : List Fmt.RoundView)
        (gs5 gs6 gs7 gs8 : List (List (Nat × List UInt64))) (d4 d5 d6 d7 d8 eU eO : St)
        (m' : Words K),
        r4.drawn.poss = List.ofFn (fun i => (Q i).val) ∧
        (∀ x col, cols.lookup x = some col → col = tab x) ∧
        b4.decide d3 [r4] [cols] = .ok d4 ∧ b5.decide d4 rs5 gs5 = .ok d5 ∧
        b6.decide d5 rs6 gs6 = .ok d6 ∧ b7.decide d6 rs7 gs7 = .ok d7 ∧
        b8.decide d7 rs8 gs8 = .ok d8 ∧
        Reaches d8 eU d8.loc.gU ∧ Reaches d8 eO d8.loc.gOmega ∧ AgreeOn d3.loc.oU.oracle m m' ∧
        Means.AllSay ρ eU.st (rowsOn eU d8.loc.gU) m' ∧
        Means.AllSay ρ eO.st (rowsOn eO d8.loc.gOmega) m').card ≤
      (2 ^ P.S.fold.index.code.logN - e' - 1) ^ c :=
  le_trans (loc_sound_blocks ρ P b1 b2 b3 b4 b5 b6 b7 b8 hb hS d0 d1 d2 d3 rs1 rs2 rs3
    gs1 gs2 gs3 h1 h2 h3 m tab c) (Nat.pow_le_pow_left (card_locAt_lt ρ P.par d3 m tab e' h) c)

/-- The fold of the stored table's column at a location. -/
def foldCol (p : Par) (d : St) (tab : Nat → List UInt64) (x : Nat) : K :=
  ∑ r ∈ Finset.range (weights p.S d.loc).size,
    ρ.val ((weights p.S d.loc).getD r zeroE) * ρ.val (ofF ((tab x).toArray.getD r 0))

open Classical in
/-- **NearAt is the library's NearW** at the typed data made of the public shape. -/
theorem near_iff [Fintype K] (p : Par) (d : St) (m : Words K) (tab : Nat → List UInt64)
    (e' err eM : Nat)
    (rank : ((Fin p.S.fold.index.v → Bool) →
      Fin p.S.fold.index.code.ell ⊕ Fin p.S.fold.index.code.r → K) → Nat) :
    NearAt ρ p d m tab e' ↔
      (ixOf ρ p.S.fold err eM rank).NearW e' (fun x => foldCol ρ p d tab x.val)
        (fullOf p.S.fold fun k => m d.loc.oU.oracle .main (d.loc.oU.lay.index k)) := by
  unfold NearAt Cb.LdIx.NearW Prob.cnt
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have e : (Finset.univ.filter fun x : Fin (2 ^ p.S.fold.index.code.logN) =>
        ¬ LocAt ρ p d m tab x.val) =
      Finset.univ.filter fun x : Fin (2 ^ p.S.fold.index.code.logN) =>
        foldCol ρ p d tab x.val ≠ (ixOf ρ p.S.fold err eM rank).G.mulVec
          (fullOf p.S.fold fun k => m d.loc.oU.oracle .main (d.loc.oU.lay.index k)) x := by
    refine Finset.filter_congr fun x _ => not_congr ?_
    unfold LocAt
    rw [mulVec_iff]
    exact eq_comm
  rw [e]

end Desc.K14.Law
