-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K4/Returns/AtChain.lean: THE LAYERS' OWN ROUNDS (K4): THE DECISION OF THE BLOCK
AT THE STATE THAT THE FIRST CHAIN CARRIES (blockAtC, Johnson/Desc/First/K4/AtC.lean), SEEN THROUGH
THAT STATE's SHAPE (Johnson/Desc/First/Shape/Chain.lean). General laws: nothing is evaluated.

  heardAt         WHAT THE HEARING RETURNS AT A STATE AND ITS ROUNDS: a function with code: hearFl
                  (OnBytes/Desc/First/K4/Plain.lean) at the state's own parts and the rounds under
                  K4's own entries, where nothing is left of the tape.
  stretchB        K4's three tests in front of the hearing: no count of rows waits; the stretch fits
                  K4's table; the strict reading.
  chainSh_k4Laid, hearAt_part, debt_isNone   what the decision lays, seen through the shape; the
                  hearing at K4's part of the state; the debt of rows as that part reads it.
  **k4_seat**     the decision, seen through the shape: where the three tests pass and heardAt
                  returns (o, G): the shape in front with the ledger's shape := G's, what the
                  hearing leaves := o's shape, the tables' shapes := those of o's list, and no count
                  of rows owed; elsewhere it refuses. One equation, at every state; no premise.

Limits. heardAt READS THE STATE AND THE ROUNDS' VALUES, NOT THE SHAPE: so this is not a step on the
shape. That heardAt returns is not said here. Under which name the decision refuses is not said.
Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.First.K4.Returns.Seat
import Johnson.Desc.First.K4.Returns.Ledger
import Johnson.Desc.First.K4.AtC
import Johnson.Desc.First.Shape.Chain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Rt
open OnBytes OnBytes.K.Kc D6.Ret
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open OnBytes.Model.Layer (Pub HPlan2 Own TableAt TableAsk)
open VerifiableInference.Desc.First (S LayOwn)
open VerifiableInference.Desc.First.Shape

/-- **What the hearing returns at a state and its rounds**: hearFl at the state's own parts (the
lookup's record, the ledger, the request's tokens) and the rounds under K4's own entries, where
nothing is left of the tape. Nothing outside a layers' link, and where the lookup's record is not
laid. -/
def heardAt (p : Par) (s : S) (rs : List Fmt.RoundView) : Option (Own × Fork) :=
  match s.here with
  | .lay a =>
    a.fo.bind fun fo =>
      match hearFl { p.P with tokv := s.tokv } p.hp p.g fo a.F
          (paired rs (entries p.P p.hp p.g)) with
      | some (o, G, []) => some (o, G)
      | _ => none
  | _ => none

/-- K4's three tests in front of the hearing: no count of rows waits; the stretch fits K4's table;
the strict reading. -/
def stretchB (p : Par) (s : S) (rs : List Fmt.RoundView) : Bool :=
  s.noneWaits && fitsAll (rounds p.P p.hp p.g) (entries p.P p.hp p.g) rs &&
    Kit.plainStretchWith rowsTabled (entries p.P p.hp p.g) rs

/-- The ledger and what was heard laid at a layers' link, and no count of rows owed, seen through
the shape. -/
theorem chainSh_k4Laid (s : S) (a : LayOwn) (hh : s.here = .lay a) (o : Own) (G : Fork) :
    chainSh { s with here := .lay { a with F := G, own := some o }, rowsOwed := none } =
      ((((chainSh s).setLed (ledSh G)).layOwn (some (ownSh o))).layTables
        (some (o.funs.toList.map funSh))).setRowsOwed none := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  obtain rfl : here = .lay a := hh
  rfl

/-- The hearing at K4's part of the state, with what it lays handed on through g. -/
theorem hearAt_part (p : Par) (a : LayOwn) (d : Option Nat) (tk : Array Nat) (rs : List Fmt.RoundView)
    {β : Type} (g : Part → β) :
    ((hearAt seatOwn p (a, d, tk) rs).map g).toOption =
      if (d.isNone && fitsAll (rounds p.P p.hp p.g) (entries p.P p.hp p.g) rs &&
          Kit.plainStretchWith rowsTabled (entries p.P p.hp p.g) rs) = true then
        a.fo.bind fun fo =>
          match hearFl { p.P with tokv := tk } p.hp p.g fo a.F
              (paired rs (entries p.P p.hp p.g)) with
          | some (o, G, []) => some (g ({ a with F := G, own := some o }, none, tk))
          | _ => none
      else none := by
  obtain ⟨L, F, fo, own, tl, lookHeard⟩ := a
  unfold hearAt
  dsimp only [seatOwn]
  cases d.isNone <;>
    cases fitsAll (rounds p.P p.hp p.g) (entries p.P p.hp p.g) rs <;>
    cases Kit.plainStretchWith rowsTabled (entries p.P p.hp p.g) rs <;> try rfl
  cases fo with
  | none => rfl
  | some fo =>
    show ((match hearFl { p.P with tokv := tk } p.hp p.g fo F
        (paired rs (entries p.P p.hp p.g)) with
      | some (o, G, []) =>
        (pure ((⟨L, G, some fo, some o, tl, lookHeard⟩ : LayOwn), (none : Option Nat), tk) :
          Except String Part)
      | some _ => throw "K4.the-stretch-is-not-used-up"
      | none => throw "K4.hear").map g).toOption =
      match hearFl { p.P with tokv := tk } p.hp p.g fo F (paired rs (entries p.P p.hp p.g)) with
      | some (o, G, []) => some (g ((⟨L, G, some fo, some o, tl, lookHeard⟩ : LayOwn), none, tk))
      | _ => none
    cases hearFl { p.P with tokv := tk } p.hp p.g fo F (paired rs (entries p.P p.hp p.g)) with
    | none => rfl
    | some x =>
      obtain ⟨o, G, u⟩ := x
      cases u <;> rfl

/-- The debt of rows, as K4's part reads it. -/
theorem debt_isNone (s : S) :
    ((if s.noneWaits = true then none else s.rowsOwed : Option Nat).isNone) = s.noneWaits := by
  cases hw : s.noneWaits with
  | true => rfl
  | false =>
    unfold S.noneWaits at hw
    cases hr : s.rowsOwed with
    | none =>
      rw [hr] at hw
      cases hw
    | some r => rfl

/-- **THE SEATED DECISION, SEEN THROUGH THE SHAPE**: one equation, at every state. -/
theorem k4_seat (p : Par) (s : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) :
    (((blockAtC p).decide s rs gs).toOption.map chainSh) =
      if stretchB p s rs = true then
        (heardAt p s rs).map fun x =>
          ((((chainSh s).setLed (ledSh x.2)).layOwn (some (ownSh x.1))).layTables
            (some (x.1.funs.toList.map funSh))).setRowsOwed none
      else none := by
  cases hh : s.here with
  | lay a =>
    have hd : (blockAtC p).decide s rs gs =
        (hearAt seatOwn p (a, (if s.noneWaits = true then none else s.rowsOwed), s.tokv) rs).map
          (setPart s) := by
      show ((VerifiableInference.Desc.named "the part is not there" (part? s)).bind fun x =>
        (hearAt seatOwn p x rs).map (setPart s)) = _
      unfold part?
      rw [hh]
      rfl
    have hv : heardAt p s rs = a.fo.bind fun fo =>
        match hearFl { p.P with tokv := s.tokv } p.hp p.g fo a.F
            (paired rs (entries p.P p.hp p.g)) with
        | some (o, G, []) => some (o, G)
        | _ => none := by
      unfold heardAt
      rw [hh]
    rw [hd, hearAt_part, debt_isNone, hv]
    unfold stretchB
    have key := chainSh_k4Laid s a hh
    obtain ⟨L, F, fo, own, tl, lookHeard⟩ := a
    split
    · cases fo with
      | none => rfl
      | some fo =>
        simp only [Option.bind_some]
        cases hearFl { p.P with tokv := s.tokv } p.hp p.g fo F
            (paired rs (entries p.P p.hp p.g)) with
        | none => rfl
        | some x =>
          obtain ⟨o, G, u⟩ := x
          cases u with
          | nil => exact congrArg some (key o G)
          | cons _ _ => rfl
    · rfl
  | _ =>
    have hd : ((blockAtC p).decide s rs gs).toOption = none := by
      show ((VerifiableInference.Desc.named "the part is not there" (part? s)).bind fun x =>
        (hearAt seatOwn p x rs).map (setPart s)).toOption = none
      unfold part?
      rw [hh]
      rfl
    have hv : heardAt p s rs = none := by
      unfold heardAt
      rw [hh]
    rw [hd, hv]
    split <;> rfl

end OnBytes.Desc.First.K4.Rt

#print axioms OnBytes.Desc.First.K4.Rt.chainSh_k4Laid
#print axioms OnBytes.Desc.First.K4.Rt.hearAt_part
#print axioms OnBytes.Desc.First.K4.Rt.debt_isNone
#print axioms OnBytes.Desc.First.K4.Rt.k4_seat
#print axioms OnBytes.Desc.First.K4.Rt.heardAt
#print axioms OnBytes.Desc.First.K4.Rt.stretchB
