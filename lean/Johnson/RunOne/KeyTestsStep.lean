-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeyTestsStep.lean: THE KEY FILE, THE SHARED CHAIN: Tests₂ (Johnson/RunOne/KeyOn2Parts.lean: sixteen facts ON THE VERIFIER's STATE ALONE; no string, no reading) GOES FORWARD ACROSS SIX SUB-PROTOCOLS: borders 1 → 2 («LIN point») · 3 → 4 («(rec_gamma)») · 4 → 5 («LOC») · 6 → 7 («joins») · 7 → 8 («LIN zeta») · 8 → 9 («SPLIT»). Six theorems; no definition.

HOW. BY PROGRAM out of free₂_k(k+1) (KeyForward · KeyRow23 · KeyRow26 · KeyRow28): the same terms field by field, with the fields that Tests₂ has not struck (the committed table's OOD sample [the tables' «record»] · samples · rowsIn · shown) and shape := shape₂_k(k+1). No PinsStay is asked: no field that is left reads the reading.
OBJECT. Tests₂ at_ S K₁ a last₁ off₂ k (z, d) at two states tied by the relations PointLaid · RecLaid · LocLaid · Joined · ZetaLaid · SplitLaid.
USER. The tables' files' fold along the shared chain's history; on₂_of_tests's premise T at the next border. With tests₂_23 | tests₂_56 (Johnson/RunOne/KeyRow22.lean): eight of the twelve steps.
LETTERS. at_, p | S, K₁, a, last₁, off₂: free. hl at 1 → 2 · 4 → 5 · 7 → 8: the number of elements drawn | of rows laid: from the rounds' test at the sub-protocol's accepting step (as in the rows' forward halves).
IS IT EMPTY? Tests₂ was evaluated true at every border 0 … 12 of the honest walk at two stored key files (synthetic weights; an evaluation, no theorem; the run is not in this library and cannot be repeated from it; at definitions in which shape₂ lacked its last clause); the six sub-protocols accept there, and that gives the six relations. An evaluation's print, no theorem.
Limits. Of the state alone. Nothing on soundness, on an honest prover or on hiding.
-/
import Johnson.RunOne.KeyForward
import Johnson.RunOne.KeyRow26
import Johnson.RunOne.KeyOn2Parts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows23
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.Key
open VerifiableInference.Desc.Key (FirstState)
open Desc.Plain (Par)

section
variable (at_ : Where) (p : Par) (S : LinShape) (K₁ : KPlan) (a : Nat)
  (last₁ : FirstState → Bool) (off₂ : Nat → Nat)

/-- **«LIN point»: Tests₂ at 1 gives Tests₂ at 2.** -/
theorem tests₂_12 (z : P₂) (d d' : St₂) {r : Fmt.RoundView} (P : PointLaid p d d' r)
    (hl : (_root_.Desc.K14.drawn r).length = p.S.kCol) (T : Tests₂ at_ p.S K₁ a last₁ off₂ 1 (z, d)) :
    Tests₂ at_ p.S K₁ a last₁ off₂ 2 (z, d') :=
  have hord : Means.InOrder d'.st := P.order T.order
  { T with
    shape := shape₂_12 p a d d' P hl T.shape
    key := by
      show d'.loc.key = _
      rw [P.loc]
      exact T.key
    codes := by
      show d'.st.codes = _
      rw [P.codes]
      exact T.codes
    lay := fun h3 => absurd h3 (by decide)
    placed := by
      show Placed (plan₂ p.S).orc (fun o => d'.book.place[o]?) off₂ at_ ((pinned (open₂ 2)).filter (3 ≤ ·))
      rw [P.book, pinned₂_2, ← pinned₂_1]
      exact T.placed
    order := hord
    linOk := fun _ => by
      show OnBytes.linOk d'.st.codes p.S = true
      rw [P.codes]
      exact P.lin
    seatU := fun h3 => absurd h3 (by decide)
    seatOmega := fun h6 => absurd h6 (by decide)
    maskU := fun h3 => absurd h3 (by decide) }

/-- **«(rec_gamma)»: Tests₂ at 3 gives Tests₂ at 4.** -/
theorem tests₂_34 (z : P₂) (d d' : St₂) {GU : OnBytes.Group} {rows : List OnBytes.Row}
    (P : RecLaid p d d' GU rows) (T : Tests₂ at_ p.S K₁ a last₁ off₂ 3 (z, d)) :
    Tests₂ at_ p.S K₁ a last₁ off₂ 4 (z, d') :=
  have hord : Means.InOrder d'.st := P.order T.order
  { T with
    shape := shape₂_34 p a d d' P T.shape
    key := by
      show d'.loc.key = _
      rw [P.loc]
      exact T.key
    codes := by
      show d'.st.codes = _
      rw [P.codes]
      exact T.codes
    lay := fun _ => by
      show d'.loc.oU.lay = vectorLay d'.st.codes p.S.fold.u p.S.fold.rowsHigh
      rw [P.loc, P.codes]
      exact T.lay (by decide)
    placed := by
      show Placed (plan₂ p.S).orc (fun o => d'.book.place[o]?) off₂ at_ ((pinned (open₂ 4)).filter (3 ≤ ·))
      rw [P.book, pinned₂_4, ← pinned₂_3]
      exact T.placed
    order := hord
    linOk := fun _ => by
      show OnBytes.linOk d'.st.codes p.S = true
      rw [P.codes]
      exact T.linOk (by decide)
    seatU := fun _ => by
      show (d'.st.oracles[0]?).any (·.shape == p.S.fold.u) = true
      rw [shapeAny_rec P]
      exact T.seatU (by decide)
    seatOmega := fun h6 => absurd h6 (by decide)
    maskU := fun _ => by
      show MaskWith (fun i => d'.book.place[i]?) 0 1
      rw [P.book]
      exact T.maskU (by decide) }

/-- **«LOC»: Tests₂ at 4 gives Tests₂ at 5.** -/
theorem tests₂_45 (z : P₂) (d d' : St₂) {r : Fmt.RoundView} {GU : OnBytes.Group} {rows : List OnBytes.Row}
    (P : LocLaid p d d' r GU rows) (hl : rows.length = p.S.fold.columns)
    (T : Tests₂ at_ p.S K₁ a last₁ off₂ 4 (z, d)) : Tests₂ at_ p.S K₁ a last₁ off₂ 5 (z, d') :=
  have hord : Means.InOrder d'.st := P.order T.order
  { T with
    shape := shape₂_45 p a d d' P hl T.shape
    key := by
      show d'.loc.key = _
      rw [P.loc]
      exact T.key
    codes := by
      show d'.st.codes = _
      rw [P.codes]
      exact T.codes
    lay := fun _ => by
      show d'.loc.oU.lay = vectorLay d'.st.codes p.S.fold.u p.S.fold.rowsHigh
      rw [P.loc, P.codes]
      exact T.lay (by decide)
    placed := by
      show Placed (plan₂ p.S).orc (fun o => d'.book.place[o]?) off₂ at_ ((pinned (open₂ 5)).filter (3 ≤ ·))
      rw [P.book, pinned₂_5, ← pinned₂_4]
      exact T.placed
    order := hord
    linOk := fun _ => by
      show OnBytes.linOk d'.st.codes p.S = true
      rw [P.codes]
      exact T.linOk (by decide)
    seatU := fun _ => by
      show (d'.st.oracles[0]?).any (·.shape == p.S.fold.u) = true
      rw [P.oracles]
      exact T.seatU (by decide)
    seatOmega := fun h6 => absurd h6 (by decide)
    maskU := fun _ => by
      show MaskWith (fun i => d'.book.place[i]?) 0 1
      rw [P.book]
      exact T.maskU (by decide) }

/-- **«joins»: Tests₂ at 6 gives Tests₂ at 7.** -/
theorem tests₂_67 (z : P₂) (d d' : St₂) {GU GO : OnBytes.Group} (J : Joined d d' GU GO)
    (T : Tests₂ at_ S K₁ a last₁ off₂ 6 (z, d)) : Tests₂ at_ S K₁ a last₁ off₂ 7 (z, d') :=
  have hord : Means.InOrder d'.st := J.order T.order
  { T with
    shape := shape₂_67 S a d d' J T.shape
    key := by
      show d'.loc.key = _
      rw [J.loc]
      exact T.key
    codes := by
      show d'.st.codes = _
      rw [J.codes]
      exact T.codes
    lay := fun _ => by
      show d'.loc.oU.lay = vectorLay d'.st.codes S.fold.u S.fold.rowsHigh
      rw [J.loc, J.codes]
      exact T.lay (by decide)
    placed := by
      show Placed (plan₂ S).orc (fun o => d'.book.place[o]?) off₂ at_ ((pinned (open₂ 7)).filter (3 ≤ ·))
      rw [J.book, open₂_76]
      exact T.placed
    order := hord
    linOk := fun _ => by
      show OnBytes.linOk d'.st.codes S = true
      rw [J.codes]
      exact T.linOk (by decide)
    seatU := fun _ => by
      show (d'.st.oracles[0]?).any (·.shape == S.fold.u) = true
      rw [shapeAny_joined J]
      exact T.seatU (by decide)
    seatOmega := fun _ => by
      show (d'.st.oracles[2]?).any (·.shape == S.omega) = true
      rw [shapeAny_joined J]
      exact T.seatOmega (by decide)
    maskU := fun _ => by
      show MaskWith (fun i => d'.book.place[i]?) 0 1
      rw [J.book]
      exact T.maskU (by decide) }

/-- **«LIN zeta»: Tests₂ at 7 gives Tests₂ at 8.** -/
theorem tests₂_78 (z : P₂) (d d' : St₂) {r : Fmt.RoundView} (P : ZetaLaid d d' r)
    (hl : (_root_.Desc.K14.drawn r).length = S.kRow) (T : Tests₂ at_ S K₁ a last₁ off₂ 7 (z, d)) :
    Tests₂ at_ S K₁ a last₁ off₂ 8 (z, d') :=
  have est : d'.st = d.st := by rw [P.is]
  have ebk : d'.book = d.book := by rw [P.is]
  have ekey : d'.loc.key = d.loc.key := by rw [P.is]
  have eou : d'.loc.oU = d.loc.oU := by rw [P.is]
  have hord : Means.InOrder d'.st := by rw [est]; exact T.order
  { T with
    shape := shape₂_78 S a d d' P hl T.shape
    key := by
      show d'.loc.key = _
      rw [ekey]
      exact T.key
    codes := by
      show d'.st.codes = _
      rw [est]
      exact T.codes
    lay := fun _ => by
      show d'.loc.oU.lay = vectorLay d'.st.codes S.fold.u S.fold.rowsHigh
      rw [eou, est]
      exact T.lay (by decide)
    placed := by
      show Placed (plan₂ S).orc (fun o => d'.book.place[o]?) off₂ at_ ((pinned (open₂ 8)).filter (3 ≤ ·))
      rw [ebk, pinned₂_8, ← pinned₂_7]
      exact T.placed
    order := hord
    linOk := fun _ => by
      show OnBytes.linOk d'.st.codes S = true
      rw [est]
      exact T.linOk (by decide)
    seatU := fun _ => by
      show (d'.st.oracles[0]?).any (·.shape == S.fold.u) = true
      rw [est]
      exact T.seatU (by decide)
    seatOmega := fun _ => by
      show (d'.st.oracles[2]?).any (·.shape == S.omega) = true
      rw [est]
      exact T.seatOmega (by decide)
    maskU := fun _ => by
      show MaskWith (fun i => d'.book.place[i]?) 0 1
      rw [ebk]
      exact T.maskU (by decide) }

/-- **«SPLIT»: Tests₂ at 8 gives Tests₂ at 9.** -/
theorem tests₂_89 (z : P₂) (d d' : St₂) {GU GO : OnBytes.Group} {x : OnBytes.Oracle}
    {l : OnBytes.Ledger} {n : Nat} {row : OnBytes.Row} {mu : E}
    (P : SplitLaid S d d' GU GO x l n row mu) (T : Tests₂ at_ S K₁ a last₁ off₂ 8 (z, d)) :
    Tests₂ at_ S K₁ a last₁ off₂ 9 (z, d') :=
  have hord : Means.InOrder d'.st := P.order T.order
  { T with
    shape := shape₂_89 S a d d' P T.shape
    key := by
      show d'.loc.key = _
      rw [P.loc]
      exact T.key
    codes := by
      show d'.st.codes = _
      rw [P.codes]
      exact T.codes
    lay := fun _ => by
      show d'.loc.oU.lay = vectorLay d'.st.codes S.fold.u S.fold.rowsHigh
      rw [P.loc, P.codes]
      exact T.lay (by decide)
    placed := by
      show Placed (plan₂ S).orc (fun o => d'.book.place[o]?) off₂ at_ ((pinned (open₂ 9)).filter (3 ≤ ·))
      rw [P.book, pinned₂_9, ← pinned₂_8]
      exact T.placed
    order := hord
    linOk := fun _ => by
      show OnBytes.linOk d'.st.codes S = true
      rw [P.codes]
      exact T.linOk (by decide)
    seatU := fun _ => by
      show (d'.st.oracles[0]?).any (·.shape == S.fold.u) = true
      rw [shapeAny_split P]
      exact T.seatU (by decide)
    seatOmega := fun _ => by
      show (d'.st.oracles[2]?).any (·.shape == S.omega) = true
      rw [shapeAny_split P]
      exact T.seatOmega (by decide)
    maskU := fun _ => by
      show MaskWith (fun i => d'.book.place[i]?) 0 1
      rw [P.book]
      exact T.maskU (by decide) }

end

end Johnson.RunOne.KeyRows23

#print axioms Johnson.RunOne.KeyRows23.tests₂_12
#print axioms Johnson.RunOne.KeyRows23.tests₂_34
#print axioms Johnson.RunOne.KeyRows23.tests₂_45
#print axioms Johnson.RunOne.KeyRows23.tests₂_67
#print axioms Johnson.RunOne.KeyRows23.tests₂_78
#print axioms Johnson.RunOne.KeyRows23.tests₂_89
