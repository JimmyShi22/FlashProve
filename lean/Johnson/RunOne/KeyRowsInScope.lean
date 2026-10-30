-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeyRowsInScope.lean: THE KEY FILE, ROWS 2.7 · 2.4 · 2.1 IN SCOPE: two of the common
premises of the rows in the form of the frame's call
(Johnson/RunOne/KeyRowsLaw.lean) ARE STRUCK:
  hS   "the description's shape is the key file's typed shape": in scope a theorem: the source holds
  the planner's chains (sourceOf_chains), and in scope
       the planner's sized key is keyFull (key_in_scope,
       Johnson/RunOne/Law/KeyInScope.lean)
  hW   "the written round at the row has the entry and kind of the key file's written list": CUT IN
  TWO, as the tables' files do at row 1.16:
       ONE HALF, PAID: a closed fact, by evaluation in Lean's kernel: the kind's own page of entries
       at keyFull, with the kinds that their names say,
       IS the written list's rounds number 0 | 3 | 6 (key_pairs)
       THE FRAME's HALF, A PREMISE (hpair): the maker's stretch at the row bears the block's own
       declared entry and its name's kind
  also "the shared split is needed" (row 2.1): split_key, by the kernel.

  sourceOf_chains · key_of_scope · hS_in_scope · p14Key · p14At_key · entries_key · key_pairs ·
  hW_of_pair
  r2_7_scope | r2_4_scope | r2_1_scope

OBJECT   pieceOf (held b) base [d] [] x, b := (Key.descriptionFromSource X N P).shared.blocksInOrder[7 | 4 | 1], X the source
that the program makes of the planner's answer
USER     the frame's keepsAt_of_law₂: not called here
What is not claimed. hpair. IT FIXES THE RELEASE's ONE CONFIGURATION: VerifierAndGoals.InScope. NO MEMBER
SHOWN of on₂ … k: the laws may be true and empty at the
real protocol. No soundness of a verifier.

-/
import Johnson.RunOne.KeyRowsLaw
import Johnson.RunOne.Law.KeyInScope
import Johnson.Desc.K14.Law.RoundsMake

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows23
open OnBytes OnBytes.Params OnBytes.Maker OnBytes.Flat
open OnBytes.Params (exc_bind)
open OnBytes.Model.Verify (Public)
open Johnson.G.OfPlan (Made)
open _root_.Run (ckP)
open _root_.Iop (Reduction Err)
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Plain
    VerifiableInference.Desc.Sound
open _root_.Desc.K14 (P14 blocks entries)
open _root_.Desc.K14.Law (atW entryAt rounds_of_blocks)
open VerifiableInference.Desc.K13.Law (ρg)
open Johnson.RunOne.KeyRows1 (plan₁)
open Johnson.RunOne.Law.AtFreeCfg (ReadOf)
open Johnson.RunOne.Law.KeyInScope (key_in_scope)
open Lk6.AtPlan (keyFull)
open scoped ENNReal

/-! ## 1 The shape -/

/-- The source holds the planner's chains. -/
theorem sourceOf_chains {m : Made} {X : Source} (h : sourceOf m = .ok X) : X.chains = m.p.chains :=
    by
  unfold sourceOf at h
  obtain ⟨D, _, h⟩ := exc_bind h
  obtain ⟨T, _, h⟩ := exc_bind h
  cases h
  rfl

section
variable {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true) {Z : Public} (hRd : ReadOf Zp.pol Z) {cfg
            : ByteArray} {m : Made}
  (hmd : madeAt Z Zp.lay cfg = .ok m) {X : Source} (hX : sourceOf m = .ok X)
include hZ hRd hmd hX

theorem key_of_scope : X.chains.made.sized.key = keyFull := by
  rw [sourceOf_chains hX]
  exact key_in_scope hZ hRd hmd

/-- **hS, in scope.** -/
theorem hS_in_scope (P : LaterPlaces) : (p14At X P).S = keyFull.once.shape := by
  show X.chains.made.sized.key.once.shape = _
  rw [key_of_scope hZ hRd hmd hX]

end

/-! ## 2 The written rounds -/

/-- The kind's parameters at the typed key. -/
def p14Key (bp : List (Nat × Nat)) : P14 :=
  { set := keyFull.set, scope := if keyFull.once.lines.oneTime then .once else .shared, codes :=
      keyFull.codes,
    S := keyFull.once.shape, item := 0, beforePoint := bp }

theorem p14At_key {X : Source} (hk : X.chains.made.sized.key = keyFull) (P : LaterPlaces) :
    p14At X P = p14Key (beforeSharedPoint P) := by
  show sharedPar X.chains (beforeSharedPoint P) = _
  unfold sharedPar p14Key
  simp only [hk]

/-- The page of entries does not read "before the point". -/
theorem entries_key (bp : List (Nat × Nat)) : entries (p14Key bp) = entries (p14Key []) := rfl

/-- An entry with the kind that its name says. -/
def pairAt (i : Nat) : Option (Fmt.Entry × Fmt.Kind) :=
  (Fmt.kindOf (entryAt (p14Key []) i).name).map fun k => (entryAt (p14Key []) i, k)

/-- **ONE HALF OF hW: A CLOSED FACT**: the kind's own entries at the typed key are the written
list's rounds number 0 | 3 | 6. -/
theorem key_pairs : atW Johnson.G.dryKeyFull.2.1 0 = pairAt 0 ∧ atW Johnson.G.dryKeyFull.2.1 3 =
    pairAt 1 ∧
    atW Johnson.G.dryKeyFull.2.1 6 = pairAt 2 := by
  decide +kernel

theorem split_key : keyFull.once.shape.sharedSplitNeeded = true := by decide +kernel

/-- hW out of the two halves. -/
theorem hW_of_pair (i idx : Nat) (hcl : atW Johnson.G.dryKeyFull.2.1 idx = pairAt i) (Q : P14) (hQ :
    entryAt Q i = entryAt (p14Key []) i)
    (l : List Fmt.DeclaredRound) (hl : l.map (·.entry) = [entryAt Q i]) (d : RDT)
    (hpair : ∃ r, l = [r] ∧ (d.entry, some d.kind) = (r.entry, Fmt.kindOf r.entry.name)) :
    atW Johnson.G.dryKeyFull.2.1 idx = some (d.entry, d.kind) := by
  obtain ⟨r, rfl, hp⟩ := hpair
  have hr : r.entry = entryAt Q i := (List.cons.inj hl).1
  obtain ⟨h1, h2⟩ := Prod.mk.inj hp
  rw [hcl]
  unfold pairAt
  rw [← hQ, ← hr, ← h2, ← h1]
  rfl

theorem entryAt_key {X : Source} (hk : X.chains.made.sized.key = keyFull) (P : LaterPlaces) (i :
    Nat) :
    entryAt (p14At X P) i = entryAt (p14Key []) i := by
  rw [p14At_key hk P]
  unfold entryAt
  rw [entries_key]

/-! ## 3 The three rows -/

section
variable {XI Cells M Smp Rec W : Type} (F : FileDescription XI) (Fr₂ : Frame) (T : BaseSt Cells M Smp Rec)
    (at_ : Where)
  (K₁ : KPlan) (R : KRead Cells M) (enc : (Nat → E) → Nat → E) (rad a : Nat)
  (coll : Strs → Rec → Prop) (last₁ : FirstState → Bool) (off₂ : Nat → Nat)
  (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces)
  (b1 b2 b3 b4 b5 b6 b7 b8 : Block St₂ Unit)
  (h : _root_.Desc.K14.blocks (p14At X P) = some [b1, b2, b3, b4, b5, b6, b7, b8])
include h

theorem r2_7_scope {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true) {Z : Public} (hRd : ReadOf
            Zp.pol Z) {cfg : ByteArray} {m : Made}
    (hmd : madeAt Z Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X)
    (b : Block St₂ Claim) (hbk : (descriptionFromSource X N P).shared.blocksInOrder[7]? = some b)
    (d : RDT) (hpair : ∃ r, b.rounds = [r] ∧ (d.entry, some d.kind) = (r.entry, Fmt.kindOf
        r.entry.name)) (base : Nat)
    (hbase : ∀ j ∈ pinned (open₂ 7), (at_ j).1 < base) (hcC : CellOnly coll)
    (hsame : ∀ x y, R.same x y ↔ OnBytes.Model.Reading.gl.val x = OnBytes.Model.Reading.gl.val y)
    (x' : Rest (ckP .two) Fr₂ (P₂ × St₂) W [d]) (hcap : x'.err = Err.cap 128 (uLT (ckP .two) [d])) :
    ∃ x : Rest (ckP .two) Fr₂ (P₂ × St₂) W [d],
      (pieceOf (held b) base [d] [] x).ior.red.Keeps
        (on₂ F Fr₂ T.h₂ at_ (p14At X P).S K₁ R enc rad a coll last₁ off₂ 7) (on₂ F Fr₂ T.h₂ at_
            (p14At X P).S K₁ R enc rad a coll last₁ off₂ (7 + 1))
        (L₂ F Fr₂ T.h₂ at_ (p14At X P).S K₁ R enc rad 7) (L₂ F Fr₂ T.h₂ at_ (p14At X P).S K₁ R enc
            rad (7 + 1)) x.err ∧
      Err.le x.err x'.err := by
  have hk := key_of_scope hZ hRd hmd hX
  obtain rfl : seat b7 = b := Option.some.inj ((shared_7 X N P b1 b2 b3 b4 b5 b6 b7 b8 h).symm.trans
      hbk)
  exact r2_7_law F Fr₂ T at_ K₁ R enc rad a coll last₁ off₂ X N P b1 b2 b3 b4 b5 b6 b7 b8 h
      (hS_in_scope hZ hRd hmd hX P) (seat b7) hbk d
    (hW_of_pair 2 6 key_pairs.2.2 (p14At X P) (entryAt_key hk P 2) b7.rounds (rounds_of_blocks _ b1
        b2 b3 b4 b5 b6 b7 b8 h).2.2 d hpair)
    base hbase hcC hsame x' hcap

theorem r2_4_scope {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true) {Z : Public} (hRd : ReadOf
            Zp.pol Z) {cfg : ByteArray} {m : Made}
    (hmd : madeAt Z Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X)
    {K : Type} [Field K] (ρ : Model.Reading K) (b : Block St₂ Claim)
    (hbk : (descriptionFromSource X N P).shared.blocksInOrder[4]? = some b)
    (d : RDT) (hpair : ∃ r, b.rounds = [r] ∧ (d.entry, some d.kind) = (r.entry, Fmt.kindOf
        r.entry.name)) (dep : Nat → Option Nat)
    (hm : Matches Fr₂.a dep b.rounds [d]) (base : Nat)
    (hbase : ∀ j ∈ pinned (open₂ 4), (at_ j).1 < base) (hcC : CellOnly coll)
    (hsame : ∀ x y, R.same x y ↔ ρ.val x = ρ.val y) (henc : EncIs ρ (p14At X P).par.S.fold enc)
    (x' : Rest (ckP .two) Fr₂ (P₂ × St₂) W [d]) (hcap : x'.err = Err.cap 128 (uLT (ckP .two) [d])) :
    ∃ x : Rest (ckP .two) Fr₂ (P₂ × St₂) W [d],
      (pieceOf (held b) base [d] [] x).ior.red.Keeps
        (on₂ F Fr₂ T.h₂ at_ (p14At X P).S K₁ R enc OnBytes.Params.recordRadius a coll last₁ off₂ 4)
            (on₂ F Fr₂ T.h₂ at_ (p14At X P).S K₁ R enc OnBytes.Params.recordRadius a coll last₁ off₂
            (4 + 1))
        (L₂ F Fr₂ T.h₂ at_ (p14At X P).S K₁ R enc OnBytes.Params.recordRadius 4) (L₂ F Fr₂ T.h₂ at_
            (p14At X P).S K₁ R enc OnBytes.Params.recordRadius (4 + 1)) x.err ∧
      Err.le x.err x'.err := by
  have hk := key_of_scope hZ hRd hmd hX
  obtain rfl : seat b4 = b := Option.some.inj ((shared_4 X N P b1 b2 b3 b4 b5 b6 b7 b8 h).symm.trans
      hbk)
  exact r2_4_law F Fr₂ T at_ K₁ R enc a coll last₁ off₂ X N P b1 b2 b3 b4 b5 b6 b7 b8 h ρ
      (hS_in_scope hZ hRd hmd hX P) (seat b4) hbk d
    (hW_of_pair 1 3 key_pairs.2.1 (p14At X P) (entryAt_key hk P 1) b4.rounds (rounds_of_blocks _ b1
        b2 b3 b4 b5 b6 b7 b8 h).2.1 d hpair)
    dep hm base hbase hcC hsame henc x' hcap

theorem r2_1_scope {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true) {Z : Public} (hRd : ReadOf
            Zp.pol Z) {cfg : ByteArray} {m : Made}
    (hmd : madeAt Z Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X)
    (one : OneTime) (hst : 1 ≤ one.ranges.stages.length) (hK : one.lin = (p14At X P).par.S)
    (err eM : Nat) (rank : ((Fin (p14At X P).par.S.fold.index.v → Bool) → Fin ((p14At X
        P).par.S.fold.index.code.r + (p14At X P).par.S.fold.index.code.ell) → Cb.Gl.E) → Nat)
    (b : Block St₂ Claim)
    (hbk : (descriptionFromSource X N P).shared.blocksInOrder[1]? = some b)
    (d : RDT) (hpair : ∃ r, b.rounds = [r] ∧ (d.entry, some d.kind) = (r.entry, Fmt.kindOf
        r.entry.name)) (base : Nat)
    (hbase : ∀ j ∈ pinned (open₂ 1), (at_ j).1 < base) (hcC : CellOnly coll)
    (hsame : ∀ x y, R.same x y ↔ ρg.val x = ρg.val y)
    (hof : ∀ (w : Wit Cells Unit M) c k, R.of { w with cells := c } k = R.of w k)
    (henc : EncIs ρg (p14At X P).par.S.fold enc)
    (hle : 2852142980 ≤ eM) (hM : eM < 3848273922)
    (hcoll : CollTie F Fr₂ T.h₂ at_ (p14At X P).par (plan₁ one) R enc 2852142980 a coll (last₁At
        one) off₂ err eM rank)
    (hdec : DecTie F Fr₂ T.h₂ at_ (p14At X P).par (plan₁ one) R enc 2852142980 a coll (last₁At one)
        off₂ err eM rank)
    (x' : Rest (ckP .two) Fr₂ (P₂ × St₂) W [d]) (hcap : x'.err = Err.cap 128 (uLT (ckP .two) [d])) :
    ∃ x : Rest (ckP .two) Fr₂ (P₂ × St₂) W [d],
      (pieceOf (held b) base [d] [] x).ior.red.Keeps
        (on₂ F Fr₂ T.h₂ at_ (p14At X P).S (plan₁ one) R enc 2852142980 a coll (last₁At one) off₂ 1)
            (on₂ F Fr₂ T.h₂ at_ (p14At X P).S (plan₁ one) R enc 2852142980 a coll (last₁At one) off₂
            (1 + 1))
        (L₂ F Fr₂ T.h₂ at_ (p14At X P).S (plan₁ one) R enc 2852142980 1) (L₂ F Fr₂ T.h₂ at_ (p14At X
            P).S (plan₁ one) R enc 2852142980 (1 + 1)) x.err ∧
      Err.le x.err x'.err := by
  have hk := key_of_scope hZ hRd hmd hX
  have hS := hS_in_scope hZ hRd hmd hX P
  obtain rfl : seat b1 = b := Option.some.inj ((shared_1 X N P b1 b2 b3 b4 b5 b6 b7 b8 h).symm.trans
      hbk)
  exact r2_1_law F Fr₂ T at_ R enc a coll off₂ X N P b1 b2 b3 b4 b5 b6 b7 b8 h one hst hK err eM
      rank hS (by rw [hS]; exact split_key) (seat b1) hbk d
    (hW_of_pair 0 0 key_pairs.1 (p14At X P) (entryAt_key hk P 0) b1.rounds (rounds_of_blocks _ b1 b2
        b3 b4 b5 b6 b7 b8 h).1 d hpair)
    base hbase hcC hsame hof henc hle hM hcoll hdec x' hcap

end

end Johnson.RunOne.KeyRows23
