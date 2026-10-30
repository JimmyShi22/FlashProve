-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/FillK6K7Says.lean: what the output head's and the reply's files' layer of
the table's filling (Johnson/Stored/FillK6K7.lean) gives to these files' laws: the layer's two tests
give these files' own Bools (Law/K6OnB.lean), and the premise PubSays of the tie at the head's
block (Johnson/Desc/Sound/K6Tied.lean) is paid at the filling.

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law).
  lookHeadB_is: at the public record's letters the layer's test on the lookup is cEndB, by rfl.
  tokenHeardB_says: the layer's test on the token gives a heard token below V; tokenB_of_heard: so
      tokenB.
  wellLaidB_of_ledgerB: the table's files' test on the ledger (Johnson/Desc/First/FillKeeper.lean:
      ledgerB) gives wellLaidB at the seat's ledger.
  pubSays_fill: PubSays Wp (fillK6K7 ... m Mg) m, AT EVERY Mg whose item "ledger m" gives wellLaidB.
  pubSays_layers: so at this layer laid over fillKeeper's: PubSays Wp (fillK6K7 ... m (fillKeeper
      nsOf Mg)) m, AT EVERY Mg: NO PREMISE IS LEFT.

Every letter under "there is": tokenHeardB_says: y: pinned by the seat's reader of the token.
What it does not say. That the blocks in front make and keep the three items (their second ties).
That a composed filling lays these two layers in this order, or lays no other layer over them that
names one of the three. Nothing on
soundness.
-/
import Johnson.Stored.FillK6K7
import Johnson.Desc.First.FillKeeper
import Johnson.Desc.Sound.K6Tied

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open VerifiableInference.Desc.First (S Pub Meaning ledgerB fillKeeper)

theorem lookHeadB_is (W : OnBytes.Model.Verify.Public) (s : S) :
    lookHeadB W.hS (readsOf W) s = cEndB W s := rfl

/-- The layer's test on the token: a token is heard, and it is below V. -/
theorem tokenHeardB_says (W : OnBytes.Model.Verify.Public) (s : S)
    (h : tokenHeardB W.hS (readsOf W) s = true) :
    ∃ y, Reply.token (seatAt W.hS (readsOf W)).toSeat s = some y ∧
      y < (parOf W.hS (workOf W)).sizes.V := by
  unfold tokenHeardB at h
  split at h
  · rename_i y hy
    exact ⟨y, hy, of_decide_eq_true h⟩
  · exact absurd h (by simp)

theorem tokenB_of_heard (W : OnBytes.Model.Verify.Public) (s : S)
    (h : tokenHeardB W.hS (readsOf W) s = true) : tokenB W s = true := by
  obtain ⟨y, hy, hlt⟩ := tokenHeardB_says W s h
  unfold tokenB
  rw [hy]
  exact decide_eq_true hlt

/-- FillKeeper.lean's test on the ledger (ledgerB) gives wellLaidB, at the seat's ledger. -/
theorem wellLaidB_of_ledgerB (W : OnBytes.Model.Verify.Public) (s : S) (h : ledgerB s = true) :
    wellLaidB ((seatAt W.hS (readsOf W)).ledger s) = true := by
  unfold ledgerB at h
  show wellLaidB (s.fork?.getD {}) = true
  cases hf : s.fork? with
  | none => rw [hf] at h; simp at h
  | some G =>
    rw [hf] at h
    simp only [Option.any_some, Bool.and_eq_true] at h
    show wellLaidB G = true
    unfold wellLaidB
    simp only [Bool.and_eq_true]
    exact ⟨⟨h.2, h.1.1⟩, h.1.2⟩

namespace AtTable

variable {P Wt : Type}

/-- **PubSays, at the layer**, over every Meaning whose item on the ledger gives wellLaidB.
-/
theorem pubSays_fill (Wp : OnBytes.Model.Verify.Public) (m : Nat) (Mg : Meaning P Wt)
    (hL : ∀ a, Mg.pub (.ledger m) a = true →
      wellLaidB ((seatAt Wp.hS (readsOf Wp)).ledger a.2) = true) :
    PubSays Wp (fillK6K7 Wp.hS (readsOf Wp) m Mg) m :=
  ⟨fun a h => hL a h,
    fun a h => tokenB_of_heard Wp a.2 h,
    fun a h => by
      rw [fillK6K7_look] at h
      exact h⟩

/-- **PubSays, at this layer laid over fillKeeper's**: no premise is left. -/
theorem pubSays_layers (Wp : OnBytes.Model.Verify.Public) (m : Nat) (nsOf : Nat → Option Nat)
    (Mg : Meaning P Wt) :
    PubSays Wp (fillK6K7 Wp.hS (readsOf Wp) m (fillKeeper nsOf Mg)) m :=
  pubSays_fill Wp m (fillKeeper nsOf Mg) fun a h => wellLaidB_of_ledgerB Wp a.2 h

end AtTable

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.tokenHeardB_says
#print axioms VerifiableInference.Desc.Kinds.Head.Law.tokenB_of_heard
#print axioms VerifiableInference.Desc.Kinds.Head.Law.wellLaidB_of_ledgerB
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.pubSays_fill
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.pubSays_layers
