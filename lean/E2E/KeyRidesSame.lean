-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyRidesSame.lean: AN ITEM THAT IS OPEN ACROSS A SUB-PROTOCOL OF NO KIND OF THE KEY FILE's
SHARED OR LAST CHAIN SAYS BEHIND IT WHAT IT SAID IN FRONT (`RidesPast`,
Johnson/Desc/ProofFile/Honest/Thread/Pays.lean): at the shared chain's front and end (numbers 0 and
11) and at the last chain's test on the taken trees' sources and its end (numbers 1 and 3): at the
threads with any halves and any tables (`laid₂`, `laid₃`, E2E/KeyRest.lean). No premise. On
sentences and states. NOTHING IS SHOWN OF ANY PROVER.

HOW. These four hand the state on as it was: that is the threads' own letter `keeps` there. So only
the oracles turn between the two sentences, and on the honest side hardly any sentence reads an
oracle: a pin says that the state holds the seat's sample and the message meets it; the pin on the
stored table reads the carried OOD sample.

  **`strs_free₃`**: ON THE LAST CHAIN NO SENTENCE READS AN ORACLE: by the library's texts
      (`meaning₃`, `claim₃`: Johnson/RunOne/KeyRows23At.lean, Johnson/Desc/Key/KeyMeaning23.lean)
  **`strs_free₂`**: ON THE SHARED CHAIN ONE ALONE DOES: the claim "NearU"
  `near_shut`: that claim is not open at the borders 0 and 11 of the shared chain's thread: BY
      EVALUATION
  **`ridesPast₂`**: `RidesPast (laid₂ …) b` at b = 0, 11
  **`ridesPast₃`**: `RidesPast (laid₃ …) b` at b = 1, 3

The library has the like for the way back, along oracles that stay at the open pins: `rides₂_seam`,
`rides₂_end`, `rides₃` (Johnson/RunOne/KeyKeeps23.lean): there a pin reads the committed word.

Limits.
- The sub-protocols of a kind of these two chains are not treated.
- `near_shut` is an evaluation of OUR table's rows: it shows no row right.
- THE EASE IS BOUGHT BY THE HONEST PIN (`holdsH`, E2E/KeyRest.lean), which leaves the committed word
  out of a pin's sentence; its price, that the committed word is an encoding of the message
  (`Encodes`), has no payer.
- It is true also where the thread holds at nothing.

-/
import E2E.KeyRest
import Johnson.Desc.ProofFile.Honest.Thread.Pays

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.KeyThread
open VerifiableInference.Desc (FileDescription Strs Wit Reading)
open VerifiableInference.Desc.Key
open VerifiableInference.Desc.Key (Xi)
open Johnson.RunOne.KeyRows23 (St₂ St₃ P₂ P₃ meaning₂ meaning₃ plan₂ readers₂)
open ProofFile.Honest

section
variable {XI Cells M Smp Rec : Type} (F : FileDescription XI) (at_ : Where)
  (meetsT : Rec → Cells → Prop) (S : OnBytes.Params.LinShape) (K₁ : KPlan) (R : KRead Cells M)

/-- **On the last chain no sentence reads an oracle.** -/
theorem strs_free₃ (G₃ : Reading (P₃ × St₃) Cells M Smp Rec) (i : KItem) (a : P₃ × St₃)
    (y y' : Strs) (v : Wit Cells Unit M)
    (hu : holdsH F G₃ at_ meetsT (meaning₃ S K₁ R) i a y v) :
    holdsH F G₃ at_ meetsT (meaning₃ S K₁ R) i a y' v := by
  cases i <;> exact hu

variable (enc : (Nat → OnBytes.E) → Nat → OnBytes.E) (rad : Nat)

/-- **On the shared chain one alone does.** -/
theorem strs_free₂ (G₂ : Reading (P₂ × St₂) Cells M Smp Rec) (i : KItem)
    (hi : i ≠ .claim 2 "NearU") (a : P₂ × St₂) (y y' : Strs) (v : Wit Cells Unit M)
    (hu : holdsH F G₂ at_ meetsT (meaning₂ S K₁ R enc rad) i a y v) :
    holdsH F G₂ at_ meetsT (meaning₂ S K₁ R enc rad) i a y' v := by
  cases i with
  | claim c n =>
    have hne : ¬(c = 2 ∧ n = "NearU") := fun h => hi (by rw [h.1, h.2])
    have hu' : claim₂ K₁ (plan₂ S) R (readers₂ S) enc rad c n a y v := hu
    show claim₂ K₁ (plan₂ S) R (readers₂ S) enc rad c n a y' v
    unfold claim₂ at hu' ⊢
    simp only [hne, if_false] at hu' ⊢
    exact hu'
  | _ => exact hu

end

/-- The one claim that reads an oracle is not open at the shared chain's first and last border but
one. -/
theorem near_shut : ∀ b ∈ [0, 11],
    ∀ i ∈ fwdOpen startShared (rowsAt (rows₂.map sharedRow)) b, i ≠ .claim 2 "NearU" := by decide

section
variable {Bk : ProverCoinCounts} {W₀ Rc Cells M Smp Rec X' : Type} (Xs : Source) (N : H2U.PlaceNums)
  (Pl : LaterPlaces) (L : KeyFill Bk W₀ Rc Cells M Smp Rec) (w₀ : W₀) (rc : Rc) (x : Xi)
  {hs₂ : List (Placed Empty (Common W₀ Rc OnBytes.TableKey) X')}
  {tb₂ : Fmt.TreeSource → Coins Bk → Common W₀ Rc OnBytes.TableKey → List Fmt.Drawn →
    VerifiableInference.Desc.Place × Table}
  {hs₃ : List (Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X')}
  {tb₃ : Fmt.TreeSource → Coins Bk → Local W₀ Rc Xi Unit → List Fmt.Drawn →
    VerifiableInference.Desc.Place × Table}

/-- **THE RIDERS, at the shared chain's front and end.** -/
theorem ridesPast₂ : ∀ b ∈ [0, 11], RidesPast (laid₂ Xs N Pl L w₀ rc x hs₂ tb₂) b := by
  intro b hb k s m E s' ps i v _ hk hi _ _ hu
  have hn := near_shut b hb i hi
  have e : s' = s := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl <;> exact hk
  subst e
  intro e₁
  exact strs_free₂ _ _ _ _ _ _ _ _ _ i hn _ _ _ v (hu e₁)

/-- **THE RIDERS, at the last chain's two of no kind.** -/
theorem ridesPast₃ : ∀ b ∈ [1, 3], RidesPast (laid₃ Xs N Pl L w₀ rc x hs₃ tb₃) b := by
  intro b hb k s m E s' ps i v _ hk _ _ _ hu
  have e : s' = s := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl <;> exact hk
  subst e
  exact strs_free₃ _ _ _ _ _ _ _ i _ _ _ v hu

end

end AtPublicFiles.KeyThread

#print axioms AtPublicFiles.KeyThread.strs_free₃
#print axioms AtPublicFiles.KeyThread.strs_free₂
#print axioms AtPublicFiles.KeyThread.near_shut
#print axioms AtPublicFiles.KeyThread.ridesPast₂
#print axioms AtPublicFiles.KeyThread.ridesPast₃
