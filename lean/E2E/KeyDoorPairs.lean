-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
THE DEBT IS MOVED INTO NAMED PREMISES, NOT PAID.
E2E/KeyDoorPairs.lean: the clause `hItems` of a door from the pairs `ThrS`
(Johnson/Desc/ProofFile/Honest/Thread/Said.lean) at the key file, with the library's term `endsBy`
(Johnson/Desc/ProofFile/Honest/Thread/OneState.lean) for the letter `ends`.

Why. Three premises of the door read `ends`: `hItems`, `hbeg`, `hForm`, and they read one value. `hbeg`
and `hForm` need that value to be the threads' own, which wants one state for each run. The library
has that at the pairs, under `OneState`. So the term is taken among the pairs, at letters `Said₁`,
`Said₂`, and the door is the library's `DoorBehindS` (E2E/KeyDoorS.lean). The last thread holds `ends`, so it is a
function of `Said₁`, `Said₂`.

Main names.
  `endsKey`: `endsBy` at the key's two threads, with the input's instance.
  `endsKey_stands`: it returns a pair at which the two threads stand, with the challenges given.
  `door_items`: `hItems`, from the pairs.
  `ends_are`: under `OneState` at both, `endsKey` returns the threads' own states.
  `begun_pairs`: so the last thread begins where the start says: `hbeg`, from the pairs.
  `door_pairs_key`: `DoorBehindS` at letters `Said₁`, `Said₂`, with `hItems` := `door_items` and
    `hbeg` := `begun_pairs`: Lean holds the match, and the statement shows what is left.
  `oneStand_fn`: `OneStand` holds of the clause «the run stands where a function of the coins, the
    input and the challenges says». IT HOLDS OF EVERY FUNCTION, BY THE CLAUSE's FORM, AND IT CANNOT FAIL:
    it shows the form that `Said` can take. That such a `Said` is met at the states where a thread
    stands, and that the frame's own play keeps it from member to member (`SaidNext`), is not shown.

What stays open. NO THREAD IS SHOWN TO STAND: every statement here holds for nothing where none
stands. The item (Dot) stands as the premise `hdot`. `R.own` is a premise (`hown`); `hw₂`, `l₁`, `l₂` too
(`lengths` pays the last two in scope). `door_pairs_key` asks `OneState` at both, so `OneStand`, one first
state, the test on the opened trees and their depths (`oneState_of`), and a `Said` that is entered at
both starts and kept from member to member: none of these is tried at the key here. `hForm` at the
library's form `fillAt`, `htrees`, `hr`, `hv`, `hst` stand as premises of `door_pairs_key`. At `Said := True`,
by reading, `OneStand` fails: two runs with one list of challenges may have shown unlike rounds: so
`hbeg` and `hForm` of the bare door have no road here. `door_items` does not feed `doorBehind_of` off
`True`: it is asked from the pairs, which is the weaker sentence.

NOT IN FRONT OF A LAW OVER COINS: `endsKey_stands`, `door_items`, `ends_are`, `begun_pairs` and
`door_pairs_key` bear this label; the rule is at its home, the head of Johnson/Bind/ForProver/FiveFieldsAt.lean. Their
ground. They stand behind `ThrS` of the two threads at a run's coins `k`, of the first kind: its clauses
tie those threads' letters and `Said₁`, `Said₂`. `hown` ties `R` to `rc`, `hw₂` ties `w₂` to it, of the
first kind. `hdot` stands at the witness, of the first kind. `door_pairs_key`'s clauses `htrees`, `hForm`,
`hr`, `hbeg` stand at `k`, and `hst`, `hv` at `R.own`, of the first kind. `o₁`, `o₂` range over every coin and
tie nothing: of neither kind. `door_items` calls `items_pair`, which bears the label, and keeps its
letters. None of these is the term that the committer makes. None: the bar
is flat. `oneStand_fn` is general in a function and names no coin of a run but as a letter of `OneStand`.

Nothing on soundness, completeness, hiding or binding.

-/
import E2E.KeyDoorItems
import E2E.KeyDoorS
import Johnson.Desc.ProofFile.Honest.Thread.OneState

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace AtPublicFiles.KeyDoorPairs
open ProofFile.Honest ProofFile.Honest.K14
open OnBytes (TableKey)
open OnBytes.Means (Words)
open VerifiableInference.Desc (Place Wit OpenedColumn)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Third (S₃)
open VerifiableInference.Desc.Last (MeaningL)
open VerifiableInference.Desc.Key (Xi FirstState Source LaterPlaces descriptionFromSource)
open _root_.Desc.K14 (St)
open AtPublicFiles.KeyFile (KeyParts keyProver)
open AtPublicFiles.KeySharedThread (threadKey)
open AtPublicFiles.KeyThread (KeyFill laid₁)
open AtPublicFiles.KeyDoorItems (commonOf wit₃ lastT items_pair)
open AtPublicFiles.KeyDoorS (doorPairs_of)

/-- **`OneStand` at a clause that a function fixes.** It holds of every function, by the clause's form:
it cannot fail, and it says nothing of a run. -/
theorem oneStand_fn {Bk : ProverCoinCounts} {W X : Type} (f : Coins Bk → W → List Fmt.Drawn → Mid W X) (n : Nat) :
    OneStand (fun _ k (m : Mid W X) => m = f k m.st.input m.st.heard) n := by
  intro k m m' h h' hi hh
  rw [h, h', hi, hh]

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

/-- The library's term at the key's two threads. -/
def endsPair (k : Coins Bk) (v : Local W₀ Rc Xi Unit) (h : List Fmt.Drawn) : FirstState × St :=
  @endsBy Bk _ _ _ _ _ _ _ _ _ _ _ _ _ (laid₁ Xs Nr Pl L w₀ rc x hs₁ tb₁) Said₁ 19
    (threadKey Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂) Said₂ 12 (fun v => v) commonOf
    ⟨d.1.2⟩ ⟨d.2⟩ k v h

/-- **The term for `ends`.** -/
def endsKey (k : Coins Bk) (v : Local W₀ Rc Xi Unit) (h : List Fmt.Drawn) :
    (Xi × FirstState) × St :=
  ((v.x, (endsPair Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d k v h).1),
    (endsPair Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d k v h).2)

/-- **It returns a pair at which the two threads stand**, wherever there is one.
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem endsKey_stands (k : Coins Bk) {e₁ : FirstState} {m₁ : Mid (Local W₀ Rc Xi Unit) X} {E₁ : Env}
    {e₂ : St} {m₂ : Mid (Common W₀ Rc TableKey) X₀} {E₂ : Env}
    (u₁ : ThrS (laid₁ Xs Nr Pl L w₀ rc x hs₁ tb₁) Said₁ 19 k e₁ m₁ E₁)
    (u₂ : ThrS (threadKey Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂) Said₂ 12 k e₂ m₂ E₂)
    (i₁ : m₁.st.input = ⟨w₀, rc, x, ()⟩)
    (i₂ : m₂.st.input = commonOf (⟨w₀, rc, x, ()⟩ : Local W₀ Rc Xi Unit)) :
    ∃ (f₁ : FirstState) (n₁ : Mid (Local W₀ Rc Xi Unit) X) (F₁ : Env) (f₂ : St)
      (n₂ : Mid (Common W₀ Rc TableKey) X₀) (F₂ : Env),
      ThrS (laid₁ Xs Nr Pl L w₀ rc x hs₁ tb₁) Said₁ 19 k f₁ n₁ F₁ ∧
      ThrS (threadKey Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂) Said₂ 12 k f₂ n₂ F₂ ∧
      n₁.st.heard ++ n₂.st.heard = m₁.st.heard ++ m₂.st.heard ∧
      endsKey Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d k
        ⟨w₀, rc, x, ()⟩ (m₁.st.heard ++ m₂.st.heard) = ((x, f₁), f₂) := by
  have hE : ∃ p : FirstState × St, ∃ (n₁ : Mid (Local W₀ Rc Xi Unit) X) (F₁ : Env)
      (n₂ : Mid (Common W₀ Rc TableKey) X₀) (F₂ : Env),
      ThrS (laid₁ Xs Nr Pl L w₀ rc x hs₁ tb₁) Said₁ 19 k p.1 n₁ F₁ ∧
      ThrS (threadKey Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂) Said₂ 12 k p.2 n₂ F₂ ∧
      n₁.st.input = ⟨w₀, rc, x, ()⟩ ∧
      n₂.st.input = commonOf (⟨w₀, rc, x, ()⟩ : Local W₀ Rc Xi Unit) ∧
      n₁.st.heard ++ n₂.st.heard = m₁.st.heard ++ m₂.st.heard :=
    ⟨(e₁, e₂), m₁, E₁, m₂, E₂, u₁, u₂, i₁, i₂, rfl⟩
  obtain ⟨a₁, F₁, a₂, F₂, v₁, v₂, -, -, hh⟩ := hE.choose_spec
  refine ⟨hE.choose.1, a₁, F₁, hE.choose.2, a₂, F₂, v₁, v₂, hh, ?_⟩
  have e : endsPair Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d k
      ⟨w₀, rc, x, ()⟩ (m₁.st.heard ++ m₂.st.heard) = hE.choose := by
    unfold endsPair endsBy
    exact dif_pos hE
  unfold endsKey
  rw [e]

variable (Dt : Local W₀ Rc Xi Unit →
    MeaningS St (Xi × FirstState) (Wit Cells Unit M × Words Cb.Gl.E))
  (ML : MeaningL S₃ (Wit Cells Unit M × Words Cb.Gl.E))
  (table : Fmt.TreeSource → Coins Bk → Local W₀ Rc Xi Unit → List Fmt.Drawn → Place × Table)
  (n₁ n₂ : Nat) (Vd : Local W₀ Rc Xi Unit → Prop) (Rd : Nat → Local W₀ Rc Xi Unit → S₃ → Prop)
  (Kp : Place → S₃ → S₃ → Prop) (w : Local W₀ Rc Xi Unit)

/-- **`hItems`, from the pairs, at the term for `ends`.**
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem door_items (l₁ : (descriptionFromSource Xs Nr Pl).first.blocksInOrder.length = 19)
    (l₂ : (descriptionFromSource Xs Nr Pl).shared.blocksInOrder.length = 12)
    (hw₂ : w₂ = commonOf (⟨w₀, rc, x, ()⟩ : Local W₀ Rc Xi Unit)) (k : Coins Bk)
    (R : Ready W₀ Rc Xi TableKey Unit X₀ X) (hown : R.own = ⟨w₀, rc, x, ()⟩)
    (hdot : ∀ (e₁ : FirstState) (m₁ : Mid (Local W₀ Rc Xi Unit) X) (E₁ : Env) (e₂ : St)
        (m₂ : Mid (Common W₀ Rc TableKey) X₀) (E₂ : Env),
        ThrS (laid₁ Xs Nr Pl L w₀ rc x hs₁ tb₁) Said₁ 19 k e₁ m₁ E₁ →
        ThrS (threadKey Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂) Said₂ 12 k e₂ m₂ E₂ →
        ∀ y ds, (Dt ⟨w₀, rc, x, ()⟩).dot (x, e₁) e₂ y
          (wit₃ Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ k ⟨w₀, rc, x, ()⟩
            (m₁.st.heard ++ (m₂.st.heard ++ ds)))) :
    ∀ (e₁ : FirstState) (m₁ : Mid (Local W₀ Rc Xi Unit) X) (E₁ : Env) (e₂ : St)
      (m₂ : Mid (Common W₀ Rc TableKey) X₀) (E₂ : Env) (s₃ : S₃) (o : Option (List OpenedColumn)),
      ThrS (laid₁ Xs Nr Pl L w₀ rc x hs₁ tb₁) Said₁ (descriptionFromSource Xs Nr Pl).first.blocksInOrder.length k e₁ m₁ E₁ →
      ThrS (threadKey Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂) Said₂
        (descriptionFromSource Xs Nr Pl).shared.blocksInOrder.length k e₂ m₂ E₂ →
      (descriptionFromSource Xs Nr Pl).start₃ ((descriptionFromSource Xs Nr Pl).pub x) e₁ e₂ = .ok s₃ →
      (lastT Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ Dt ML
        (endsKey Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d) table n₁ n₂
        Vd Rd Kp w).Items
        ((lastT Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ Dt ML
          (endsKey Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d) table n₁
          n₂ Vd Rd Kp w).opened 0) k s₃ { R.start₃ (keyProver K) m₁ m₂ with opened := o } (envThird E₁ E₂) := by
  intro e₁ m₁ E₁ e₂ m₂ E₂ s₃ o u₁ u₂ _
  rw [l₁] at u₁
  rw [l₂] at u₂
  have i₁ : m₁.st.input = ⟨w₀, rc, x, ()⟩ := u₁.1.2.2.2.2.2.2.1
  have i₂ : m₂.st.input = commonOf (⟨w₀, rc, x, ()⟩ : Local W₀ Rc Xi Unit) :=
    (u₂.1.2.2.2.2.2.2.1).trans hw₂
  obtain ⟨f₁, a₁, F₁, f₂, a₂, F₂, v₁, v₂, hh, he⟩ :=
    endsKey_stands Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d k u₁ u₂ i₁ i₂
  exact items_pair Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Dt ML
    (endsKey Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d) table n₁ n₂ Vd Rd
    Kp w l₁ l₂ hw₂ k v₁.1 v₂.1 (by rw [hh]; exact he) (hdot _ _ _ _ _ _ v₁ v₂) s₃ _ _ hown hh.symm

/-- **Under `OneState` at both, the term returns the threads' own states.**
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem ends_are (o₁ : OneState (laid₁ Xs Nr Pl L w₀ rc x hs₁ tb₁) Said₁ 19)
    (o₂ : OneState (threadKey Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂) Said₂ 12) (k : Coins Bk)
    {e₁ : FirstState} {m₁ : Mid (Local W₀ Rc Xi Unit) X} {E₁ : Env} {e₂ : St}
    {m₂ : Mid (Common W₀ Rc TableKey) X₀} {E₂ : Env}
    (u₁ : ThrS (laid₁ Xs Nr Pl L w₀ rc x hs₁ tb₁) Said₁ 19 k e₁ m₁ E₁)
    (u₂ : ThrS (threadKey Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂) Said₂ 12 k e₂ m₂ E₂)
    (i₁ : m₁.st.input = ⟨w₀, rc, x, ()⟩)
    (i₂ : m₂.st.input = commonOf (⟨w₀, rc, x, ()⟩ : Local W₀ Rc Xi Unit)) :
    endsKey Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d k
      ⟨w₀, rc, x, ()⟩ (m₁.st.heard ++ m₂.st.heard) = ((x, e₁), e₂) := by
  have e := @endsAre_endsBy Bk _ _ _ _ _ _ _ _ _ _ _ _ _ (laid₁ Xs Nr Pl L w₀ rc x hs₁ tb₁) Said₁ 19
    (threadKey Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂) Said₂ 12 (fun v => v) commonOf ⟨d.1.2⟩ ⟨d.2⟩
    o₁ o₂ k ⟨w₀, rc, x, ()⟩ e₁ m₁ E₁ e₂ m₂ E₂ u₁ u₂ i₁ i₂
  have e' : endsPair Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d k
      ⟨w₀, rc, x, ()⟩ (m₁.st.heard ++ m₂.st.heard) = (e₁, e₂) := e
  unfold endsKey
  rw [e']

/-- **`hbeg`, from the pairs**: under `OneState` at both, the last thread begins where the start says.
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem begun_pairs (o₁ : OneState (laid₁ Xs Nr Pl L w₀ rc x hs₁ tb₁) Said₁ 19)
    (o₂ : OneState (threadKey Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂) Said₂ 12) (k : Coins Bk)
    {e₁ : FirstState} {m₁ : Mid (Local W₀ Rc Xi Unit) X} {E₁ : Env} {e₂ : St}
    {m₂ : Mid (Common W₀ Rc TableKey) X₀} {E₂ : Env}
    (u₁ : ThrS (laid₁ Xs Nr Pl L w₀ rc x hs₁ tb₁) Said₁ 19 k e₁ m₁ E₁)
    (u₂ : ThrS (threadKey Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂) Said₂ 12 k e₂ m₂ E₂)
    (i₁ : m₁.st.input = ⟨w₀, rc, x, ()⟩)
    (i₂ : m₂.st.input = commonOf (⟨w₀, rc, x, ()⟩ : Local W₀ Rc Xi Unit)) {s₃ : S₃}
    (hst : (descriptionFromSource Xs Nr Pl).start₃ ((descriptionFromSource Xs Nr Pl).pub x) e₁ e₂ = .ok s₃) :
    (lastT Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ Dt ML
      (endsKey Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d) table n₁ n₂
      Vd Rd Kp w).begun k ⟨w₀, rc, x, ()⟩ (m₁.st.heard ++ m₂.st.heard) s₃ := by
  show (descriptionFromSource Xs Nr Pl).start₃
    (endsKey Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d k
      ⟨w₀, rc, x, ()⟩ (m₁.st.heard ++ m₂.st.heard)).1.1
    (endsKey Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d k
      ⟨w₀, rc, x, ()⟩ (m₁.st.heard ++ m₂.st.heard)).1.2
    (endsKey Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d k
      ⟨w₀, rc, x, ()⟩ (m₁.st.heard ++ m₂.st.heard)).2 = .ok s₃
  rw [ends_are Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d o₁ o₂ k u₁ u₂ i₁
    i₂]
  exact hst

/-- **The door from the pairs at the key**, at letters `Said₁`, `Said₂`: `hItems` is `door_items`, and
`hbeg` is `begun_pairs` under `OneState` at both. What is left stands in the statement.
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem door_pairs_key {T₁ : Thread Bk (descriptionFromSource Xs Nr Pl).S₁ (descriptionFromSource Xs Nr Pl).Cl (Local W₀ Rc Xi Unit)
      (Local W₀ Rc Xi Unit) X Xi}
    {T₂ : Thread Bk (descriptionFromSource Xs Nr Pl).S₂ (descriptionFromSource Xs Nr Pl).Cl Empty (Common W₀ Rc TableKey) X₀ TableKey}
    {T₃ : Thread Bk (descriptionFromSource Xs Nr Pl).S₃ (descriptionFromSource Xs Nr Pl).Cl (Local W₀ Rc Xi Unit)
      (Local W₀ Rc Xi Unit) X Xi}
    (S₃' : Nat → Coins Bk → Mid (Local W₀ Rc Xi Unit) X → Prop)
    (h₁ : T₁ = laid₁ Xs Nr Pl L w₀ rc x hs₁ tb₁)
    (h₂ : T₂ = threadKey Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂)
    (h₃ : T₃ = lastT Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ Dt ML
      (endsKey Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d) table n₁ n₂ Vd Rd Kp w)
    (o₁ : OneState (laid₁ Xs Nr Pl L w₀ rc x hs₁ tb₁) Said₁ 19)
    (o₂ : OneState (threadKey Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂) Said₂ 12)
    (l₁ : (descriptionFromSource Xs Nr Pl).first.blocksInOrder.length = 19)
    (l₂ : (descriptionFromSource Xs Nr Pl).shared.blocksInOrder.length = 12)
    (hw₂ : w₂ = commonOf (⟨w₀, rc, x, ()⟩ : Local W₀ Rc Xi Unit)) (k : Coins Bk)
    (R : Ready W₀ Rc Xi TableKey Unit X₀ X) (hown : R.own = ⟨w₀, rc, x, ()⟩)
    (hdot : ∀ (e₁ : FirstState) (m₁ : Mid (Local W₀ Rc Xi Unit) X) (E₁ : Env) (e₂ : St)
        (m₂ : Mid (Common W₀ Rc TableKey) X₀) (E₂ : Env),
        ThrS (laid₁ Xs Nr Pl L w₀ rc x hs₁ tb₁) Said₁ 19 k e₁ m₁ E₁ →
        ThrS (threadKey Xs Nr Pl K ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂) Said₂ 12 k e₂ m₂ E₂ →
        ∀ y ds, (Dt ⟨w₀, rc, x, ()⟩).dot (x, e₁) e₂ y
          (wit₃ Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ k ⟨w₀, rc, x, ()⟩
            (m₁.st.heard ++ (m₂.st.heard ++ ds))))
    (hah₁ : T₁.ahead = []) (hn₁ : T₁.near = 0) (hah₂ : T₂.ahead = [])
    (hah : T₃.ahead = declsTo T₁.bs (descriptionFromSource Xs Nr Pl).first.blocksInOrder.length ++
      declsTo T₂.bs (descriptionFromSource Xs Nr Pl).shared.blocksInOrder.length)
    (hnear : T₃.near = (declsTo T₁.bs (descriptionFromSource Xs Nr Pl).first.blocksInOrder.length).length)
    (hst : ∀ v, T₁.valid v → ∀ i p, T₁.stored v i p = T₃.stored R.own i p)
    (htrees : ∀ e₁ m₁ E₁ e₂ m₂ E₂ o₁ o₂, ThrS T₁ Said₁ (descriptionFromSource Xs Nr Pl).first.blocksInOrder.length k e₁ m₁ E₁ →
      ThrS T₂ Said₂ (descriptionFromSource Xs Nr Pl).shared.blocksInOrder.length k e₂ m₂ E₂ →
      T₃.Trees T₃.taken k { R.start₃ (keyProver K) m₁ m₂ with opened := some (o₁ ++ o₂) }
        (envThird E₁ E₂))
    (hForm : ∀ e₁ m₁ E₁ e₂ m₂ E₂ s₃ o₁ o₂,
      ThrS T₁ Said₁ (descriptionFromSource Xs Nr Pl).first.blocksInOrder.length k e₁ m₁ E₁ →
      ThrS T₂ Said₂ (descriptionFromSource Xs Nr Pl).shared.blocksInOrder.length k e₂ m₂ E₂ →
      (descriptionFromSource Xs Nr Pl).start₃ ((descriptionFromSource Xs Nr Pl).pub x) e₁ e₂ = .ok s₃ →
      T₃.Form 0 k s₃ { R.start₃ (keyProver K) m₁ m₂ with opened := some (o₁ ++ o₂) })
    (hr : ∀ e₁ m₁ E₁ e₂ m₂ E₂ s₃, ThrS T₁ Said₁ (descriptionFromSource Xs Nr Pl).first.blocksInOrder.length k e₁ m₁ E₁ →
      ThrS T₂ Said₂ (descriptionFromSource Xs Nr Pl).shared.blocksInOrder.length k e₂ m₂ E₂ →
      (descriptionFromSource Xs Nr Pl).start₃ ((descriptionFromSource Xs Nr Pl).pub x) e₁ e₂ = .ok s₃ →
      T₃.rides 0 R.own s₃)
    (hv : T₃.valid R.own)
    (hS₃ : ∀ m₁ m₂ o₁ o₂, Said₁ (descriptionFromSource Xs Nr Pl).first.blocksInOrder.length k m₁ →
      Said₂ (descriptionFromSource Xs Nr Pl).shared.blocksInOrder.length k m₂ → m₁.opened = some o₁ → m₂.opened = some o₂ →
      S₃' 0 k { R.start₃ (keyProver K) m₁ m₂ with opened := some (o₁ ++ o₂) }) :
    DoorBehindS (descriptionFromSource Xs Nr Pl) (keyProver K) T₁ T₂ T₃ Said₁ Said₂ S₃' x k R := by
  subst h₁ h₂ h₃
  refine doorPairs_of hah₁ hn₁ hah₂ hah hnear hst htrees ?_ hForm
    (fun e₁ m₁ E₁ e₂ m₂ E₂ s₃ o₁ o₂ =>
      door_items Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML table n₁ n₂
        Vd Rd Kp w l₁ l₂ hw₂ k R hown hdot e₁ m₁ E₁ e₂ m₂ E₂ s₃ (some (o₁ ++ o₂))) hr hv hS₃
  intro a₁ b₁ c₁ a₂ b₂ c₂ s₃ u₁ u₂ hs
  rw [l₁] at u₁
  rw [l₂] at u₂
  have i₁ : b₁.st.input = ⟨w₀, rc, x, ()⟩ := u₁.1.2.2.2.2.2.2.1
  have i₂ : b₂.st.input = commonOf (⟨w₀, rc, x, ()⟩ : Local W₀ Rc Xi Unit) :=
    (u₂.1.2.2.2.2.2.2.1).trans hw₂
  rw [hown]
  exact begun_pairs Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt ML table
    n₁ n₂ Vd Rd Kp w o₁ o₂ k u₁ u₂ i₁ i₂ hs

end

end AtPublicFiles.KeyDoorPairs

#print axioms AtPublicFiles.KeyDoorPairs.oneStand_fn
#print axioms AtPublicFiles.KeyDoorPairs.endsKey_stands
#print axioms AtPublicFiles.KeyDoorPairs.door_items
#print axioms AtPublicFiles.KeyDoorPairs.ends_are
#print axioms AtPublicFiles.KeyDoorPairs.begun_pairs
#print axioms AtPublicFiles.KeyDoorPairs.door_pairs_key
