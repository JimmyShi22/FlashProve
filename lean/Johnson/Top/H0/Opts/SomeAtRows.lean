-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Opts/SomeAtRows.lean: TWO OF THE SIX TESTS THAT MAKE UP At.k3SeatsB:
callsSomeB AND digSomeB (Johnson/P5J/Rad3Seat3Tests.lean), AT THE CLOSED LETTERS, FROM NAMED
PREMISES. General in the public part Zp and the layout's bytes: no scope, no pin. NO BLOCK IMPORTS
THIS FILE.
  RowsShaped rows ps   the first chain's rows' entry (sending k, place j) has the shape of the
                       plan's j-th seat with a sample of sending k
  radB_of              (B) of P1Opts.some_split at rad := radOf rows and R := «the radius of the
                       first entry of that shape» ⟸ radOneB over the first chain's rows ∧
                       RowsShaped
  radded_calls | radded_dig   each entry of the lookups' two lists is (shape, rad shape): by their
                              text
  callsSome_of | digSome_of   THE TWO TESTS ACCEPT AT LINK l ⟸ hrows : the second reading of the
                              three public files returns rows · h1 : radOneB … = true · hSh :
                              RowsShaped rows (At.pseats Zp) · A : each place of the list has a
                              seat of the plan with a sample, with the list's shape there and the
                              seat seat3At names
PREMISES, NOT PAYMENTS: hrows · h1 · hSh · A ARE SHOWN NOWHERE HERE. radOneB IS A TEST WITH CODE
OF Johnson/P5J/Rad3Seat3At.lean's OWN («a diagnosis»). NEITHER IT NOR «the rows are read» IS
ASKED BY verify(). Whether that trade counts is not settled here. No
soundness is claimed.
-/
import Johnson.Top.H0.Opts.SomeSplit
import Johnson.P5J.Rad3Seat3Tests

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1Opts
open OnBytes
open VerifiableInference.Desc.First.Look (Sent sigList sigListCalls lastMoment)
open P5T (PSeat mineAt radOf radOneB firstRows)

/-- The rows' shapes are the plan's seats'. -/
def RowsShaped (rows : List Johnson.G.SendRow) (ps : List PSeat) : Prop :=
  ∀ (k j : ℕ) (p : PSeat), (mineAt ps k)[j]? = some p →
    ∃ ρ : ℕ, ((firstRows rows)[k]?).bind (·.sampled[j]?) = some (p.shape, ρ)

theorem radB_of {rows : List Johnson.G.SendRow} {ps : List PSeat}
    (h1 : radOneB ((firstRows rows).flatMap (·.sampled)) = true) (hSh : RowsShaped rows ps) :
    ∀ (k j : ℕ) (p : PSeat), (mineAt ps k)[j]? = some p → radOf rows k j =
      ((((firstRows rows).flatMap (·.sampled)).find? (·.1 == p.shape)).map (·.2)).getD 0 := by
  intro k j p hp
  obtain ⟨ρ, he⟩ := hSh k j p hp
  exact rad_of_one rows h1 he

theorem radded_dig (D : Sent) (rad : OracleShape → ℕ) (i mom : ℕ) :
    ∀ e ∈ sigList D rad i mom, e.2 = rad e.1 := by
  intro e he
  unfold sigList at he
  obtain ⟨m, _, rfl⟩ := List.mem_map.1 he
  rfl

theorem radded_calls (D : Sent) (rad : OracleShape → ℕ) (i : ℕ) :
    ∀ e ∈ sigListCalls D rad i, e.2 = rad e.1 := by
  intro e he
  unfold sigListCalls at he
  rcases List.mem_append.1 he with h | h
  · obtain ⟨m, _, rfl⟩ := List.mem_map.1 h
    rfl
  · exact radded_dig D rad i 0 e h

variable (Zp : ProofFile.Pub) (lay : ByteArray)

theorem rad3_is {rows : List Johnson.G.SendRow}
    (hrows : P5T.rowsAt? Zp.pol lay Zp.KL = some rows) (sh : OracleShape) :
    P5J.At.rad3At Zp lay sh =
      ((((firstRows rows).flatMap (·.sampled)).find? (·.1 == sh)).map (·.2)).getD 0 := by
  unfold P5J.At.rad3At P5J.At.sampledAt
  rw [hrows]
  rfl

theorem some_at {rows : List Johnson.G.SendRow}
    (hrows : P5T.rowsAt? Zp.pol lay Zp.KL = some rows)
    (h1 : radOneB ((firstRows rows).flatMap (·.sampled)) = true)
    (hSh : RowsShaped rows (P5J.At.pseats Zp)) (L : List (OracleShape × ℕ)) (seat : ℕ → ℕ × ℕ)
    (hL : ∀ e ∈ L, e.2 = P5J.At.rad3At Zp lay e.1)
    (A : ∀ i : Fin L.length, ∃ p ∈ P5J.At.pseats Zp, p.smpd = true ∧ p.shape = (L.get i).1 ∧
      p.seat = seat i.1) : P5T.someB (P5J.At.ms Zp lay) L seat = true := by
  unfold P5J.At.ms P5T.msAtR
  refine some_split _ _ _ L seat (P5J.At.rad3At Zp lay) (fun i => hL _ (List.get_mem L i))
    (fun i => ?_) (fun k j p hp => ?_)
  · obtain ⟨p, hp, hs, e1, e2⟩ := A i
    exact ⟨p, hp, hs, P5T.planSeats_send_lt Zp Zp.D.1 p hp, e1, e2⟩
  · rw [rad3_is Zp lay hrows]
    unfold P5J.At.rad
    rw [hrows]
    exact radB_of h1 hSh k j p hp

theorem callsSome_of {rows : List Johnson.G.SendRow}
    (hrows : P5T.rowsAt? Zp.pol lay Zp.KL = some rows)
    (h1 : radOneB ((firstRows rows).flatMap (·.sampled)) = true)
    (hSh : RowsShaped rows (P5J.At.pseats Zp)) (l : ℕ)
    (A : ∀ i : Fin (P5J.At.callsListAt Zp lay l).length, ∃ p ∈ P5J.At.pseats Zp,
      p.smpd = true ∧ p.shape = ((P5J.At.callsListAt Zp lay l).get i).1 ∧
      p.seat = P5J.At.seat3At Zp l false i.1) : P5J.At.callsSomeB Zp lay l = true :=
  some_at Zp lay hrows h1 hSh _ _ (radded_calls _ _ _) A

theorem digSome_of {rows : List Johnson.G.SendRow}
    (hrows : P5T.rowsAt? Zp.pol lay Zp.KL = some rows)
    (h1 : radOneB ((firstRows rows).flatMap (·.sampled)) = true)
    (hSh : RowsShaped rows (P5J.At.pseats Zp)) (l : ℕ)
    (A : ∀ i : Fin (P5J.At.digListAt Zp lay l).length, ∃ p ∈ P5J.At.pseats Zp,
      p.smpd = true ∧ p.shape = ((P5J.At.digListAt Zp lay l).get i).1 ∧
      p.seat = P5J.At.seat3At Zp l true i.1) : P5J.At.digSomeB Zp lay l = true :=
  some_at Zp lay hrows h1 hSh _ _ (radded_dig _ _ _ _) A

end P1Opts

#print axioms P1Opts.radB_of
#print axioms P1Opts.some_at
#print axioms P1Opts.callsSome_of
#print axioms P1Opts.digSome_of
