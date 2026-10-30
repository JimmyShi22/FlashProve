-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
THE DEBT IS MOVED INTO NAMED PREMISES, NOT PAID.
E2E/KeyDoorDot.lean: `door_items` (E2E/KeyDoorPairs.lean) at the filling `dotFill`, with `hdot_key`
(E2E/KeyDotKey.lean) laid in: so that Lean holds the match of the two.

Main names.
  `omega_place`: in scope the description has a second test on Omega's group.
  `door_dot`: the items at the last thread's start, from the pairs, in scope, with `hdot`, `l₁`, `l₂`
    and `hO` paid. Left: `hw₂`, `hown`, and `hV`, at every pair and every continuation.

What stays open. NO THREAD IS SHOWN TO STAND. `hV` at the letters `g`, `wv`: at idle letters it holds
and says nothing; at the meant reader no term is laid, since nothing ties `L` to `K`. «In scope» is one
written value, the full size.

NOT IN FRONT OF A LAW OVER COINS: `door_dot` bears this label; the rule is at its home, the head of
Johnson/Bind/ForProver/FiveFieldsAt.lean. Its ground: it stands behind `ThrS` of the two threads at
`k`, of the first kind; `hw₂` and `hown` tie `w₂`, `R` to `rc`, of the first kind; `hV` is of both kinds, as at
`hdot_key`; `hs`, `scope` read public files, of neither kind. It calls `door_items` and `hdot_key`, which
bear the label, and keeps their letters. None of these is the term that the committer makes. None:
the bar is flat. `omega_place` names no coin.

Nothing on soundness, completeness, hiding or binding.

-/
import E2E.KeyDoorPairs
import E2E.KeyDotKey

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace AtPublicFiles.KeyDoorDot
open ProofFile.Honest ProofFile.Honest.K14
open OnBytes (TableKey)
open OnBytes.Means (Words)
open OnBytes.Slice (GE)
open VerifiableInference.Desc (Place Wit OpenedColumn)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Third (S₃)
open VerifiableInference.Desc.Last (MeaningL)
open VerifiableInference.Desc.Key (Xi FirstState Source LaterPlaces descriptionFromSource)
open _root_.Desc.K14 (St)
open _root_.Desc.K14.Law (VIs)
open AtPublicFiles.AtFiles (KeySourced)
open AtPublicFiles.AtFiles.Full (later_sourced omega_full)
open AtPublicFiles.KeyFile (KeyParts keyProver)
open AtPublicFiles.KeySharedThread (parKey threadKey randKey)
open AtPublicFiles.KeyThread (KeyFill laid₁)
open AtPublicFiles.KeyDoorItems (commonOf wit₃ lastT)
open AtPublicFiles.KeyDotItem (dotFill)
open AtPublicFiles.KeyDoorPairs (endsKey door_items)
open AtPublicFiles.KeyDotKey (hdot_key)

/-- In scope the description has a second test on Omega's group. -/
theorem omega_place {Z : VerifierAndGoals.PublicFiles} {Xs : Source} {Nr : H2U.PlaceNums} {Pl : LaterPlaces}
    (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true) : ∃ nO, Pl.O = some nO := by
  rw [later_sourced hs scope]
  exact ⟨_, omega_full⟩

section
variable {Bk : ProverCoinCounts} {W₀ Rc X₀ X Wk Cells M Smp Rec P₂ Wt₂ : Type}
  (Xs : Source) (Nr : H2U.PlaceNums) (Pl : LaterPlaces) (K : KeyParts W₀ Rc X₀ X Wk)
  (L : KeyFill Bk W₀ Rc Cells M Smp Rec)
  (ℓ₂ : WitLens Wt₂) (Nm : NumbersS)
  (Mg₂ : Common W₀ Rc TableKey → MeaningS St P₂ Wt₂)
  (tb₂ : Fmt.TreeSource → Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest₂ : Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Wt₂)
  (Kp₂ : Nat → St → St → Prop) (Vd₂ : Common W₀ Rc TableKey → Prop)
  (w₂ : Common W₀ Rc TableKey)
  (w₀ : W₀) (rc : Rc) (x : Xi)
  (hs₁ : List (Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X))
  (tb₁ : Fmt.TreeSource → Coins Bk → Local W₀ Rc Xi Unit → List Fmt.Drawn → Place × Table)
  (Said₁ : Nat → Coins Bk → Mid (Local W₀ Rc Xi Unit) X → Prop)
  (Said₂ : Nat → Coins Bk → Mid (Common W₀ Rc TableKey) X₀ → Prop)
  (d : (Xi × FirstState) × St)
  (g : Xi × FirstState → Nat → GE)
  (wv : Xi × FirstState → Wit Cells Unit M × Words GE → Nat → GE)
  (D : MeaningS St (Xi × FirstState) (Wit Cells Unit M × Words GE))
  (ML : MeaningL S₃ (Wit Cells Unit M × Words Cb.Gl.E))
  (table : Fmt.TreeSource → Coins Bk → Local W₀ Rc Xi Unit → List Fmt.Drawn → Place × Table)
  (n₁ n₂ : Nat) (Vd : Local W₀ Rc Xi Unit → Prop) (Rd : Nat → Local W₀ Rc Xi Unit → S₃ → Prop)
  (Kp : Place → S₃ → S₃ → Prop) (w : Local W₀ Rc Xi Unit)

/-- **`door_items` with `hdot_key` laid in.**
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem door_dot {Z : VerifierAndGoals.PublicFiles} (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true)
    (hw₂ : w₂ = commonOf (⟨w₀, rc, x, ()⟩ : Local W₀ Rc Xi Unit)) (k : Coins Bk)
    (R : Ready W₀ Rc Xi TableKey Unit X₀ X) (hown : R.own = ⟨w₀, rc, x, ()⟩)
    (hV : ∀ (e₁ : FirstState) (m₁ : Mid (Local W₀ Rc Xi Unit) X) (E₁ : Env) (e₂ : St)
        (m₂ : Mid (Common W₀ Rc TableKey) X₀) (E₂ : Env),
        ThrS (laid₁ Xs Nr Pl L w₀ rc x hs₁ tb₁) Said₁ 19 k e₁ m₁ E₁ →
        ThrS (threadKey Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂) Said₂ 12 k e₂ m₂ E₂ →
        ∀ ds, VIs (parKey Xs Pl).par.S (g (x, e₁))
          (holds2 (parKey Xs Pl) K.weights (randKey K) k w₂).Rw
          (wv (x, e₁) (wit₃ Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ k ⟨w₀, rc, x, ()⟩
            (m₁.st.heard ++ (m₂.st.heard ++ ds))))) :
    ∀ (e₁ : FirstState) (m₁ : Mid (Local W₀ Rc Xi Unit) X) (E₁ : Env) (e₂ : St)
      (m₂ : Mid (Common W₀ Rc TableKey) X₀) (E₂ : Env) (s₃ : S₃) (o : Option (List OpenedColumn)),
      ThrS (laid₁ Xs Nr Pl L w₀ rc x hs₁ tb₁) Said₁ (descriptionFromSource Xs Nr Pl).first.blocksInOrder.length k e₁ m₁ E₁ →
      ThrS (threadKey Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂) Said₂
        (descriptionFromSource Xs Nr Pl).shared.blocksInOrder.length k e₂ m₂ E₂ →
      (descriptionFromSource Xs Nr Pl).start₃ ((descriptionFromSource Xs Nr Pl).pub x) e₁ e₂ = .ok s₃ →
      (lastT Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂
        (fun _ => dotFill (parKey Xs Pl).par.S g wv D) ML
        (endsKey Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d) table n₁ n₂
        Vd Rd Kp w).Items
        ((lastT Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂
          (fun _ => dotFill (parKey Xs Pl).par.S g wv D) ML
          (endsKey Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d) table n₁
          n₂ Vd Rd Kp w).opened 0) k s₃ { R.start₃ (keyProver K) m₁ m₂ with opened := o } (envThird E₁ E₂) := by
  obtain ⟨l₁, l₂, -⟩ := AtPublicFiles.KeyThread.lengths scope hs.named
  obtain ⟨nO, hO⟩ := omega_place hs scope
  exact door_items Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d
    (fun _ => dotFill (parKey Xs Pl).par.S g wv D) ML table n₁ n₂ Vd Rd Kp w l₁ l₂ hw₂ k R hown
    (fun e₁ m₁ E₁ e₂ m₂ E₂ u₁ u₂ y ds =>
      hdot_key Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ g wv D hs scope nO hO l₁ hw₂ k
        u₁.1 u₂.1 y ds (hV e₁ m₁ E₁ e₂ m₂ E₂ u₁ u₂ ds))

end

end AtPublicFiles.KeyDoorDot

#print axioms AtPublicFiles.KeyDoorDot.omega_place
#print axioms AtPublicFiles.KeyDoorDot.door_dot
