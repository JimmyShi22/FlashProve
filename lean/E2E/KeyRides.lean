-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyRides.lean: AN ITEM THAT IS OPEN ACROSS A SUB-PROTOCOL OF NO KIND OF THE KEY FILE's FIRST
CHAIN SAYS BEHIND IT WHAT IT SAID IN FRONT (`RidesPast`,
Johnson/Desc/ProofFile/Honest/Thread/Pays.lean): at the twelve such sub-protocols, FROM THE EQUATION
ON THE STATE ALONE (`eq₁`, E2E/KeyKeepsEq.lean) and one premise on the reading. On sentences and
states. NOTHING IS SHOWN OF ANY PROVER.

THE LIBRARY HAS THE LIKE FOR THE WAY BACK (behind gives in front): `Rides`, `holds_rides`
(Johnson/Desc/Key/KeyQuiet.lean), `rides_same`, `rides_clr`, `rides_call`, `rides_14`. Here the same
structure is shown WITH THE TWO STATES SWAPPED, and the library's lemmas on the sorts of item
(Johnson/Desc/Key/KeyFrames.lean) are called at the swapped states.

  **`fwd_of_rides`**: GENERAL in the state, the readers and the reading: under the library's `Rides`
      at (behind, in front), a plain item's honest sentence (`holdsH`, E2E/KeyRest.lean) goes from
      in front to behind, at any oracles on either side
  `rides_clr'`, `oracle_call'`, `rides_call'`, `rides_rows'`: `Rides` swapped, behind "cleared", a
      caller, and "rng.0.rows" (there at a set without the item on the group's rows)
  **`fwd_layer`**: behind a layer: by the sorts of item: a list that is only appended to keeps its
      entries
  **`fwd_eq₁`**: so at the twelve numbers, from `eq₁`
  `fwd_claim`: an item of a later chain, at ONE state: its sentence at this meaning reads no oracle
  `okAcross`, `riders_ok`: which items are open across each of the twelve and are neither shut nor
      owed: all plain; the item on the group's rows is not among them at "rng.0.rows"; at the seal
      one item of a later chain: BY EVALUATION
  **`ridesPast₁`**: `RidesPast (laid₁ …) b`, for all halves and tables, at b = 2, 3, 5, 6, 7, 8, 9,
      11, 12, 13, 14, 18

Limits.
- THE PREMISE `ReadsL` (Johnson/RunOne/KeyCaller.lean): of the chain's state the reading reads the
  oracle messages without their ledgers, the book and the codes. It follows from a premise of the
  library's on one letter (`LettersOk.readsL`, E2E/KeyRest.lean), which the library shows at a
  filling of its own (Johnson/RunOne/KeyFillSeed.lean): not called here.
- An item that a row names as read and left is OWED AGAIN behind, in the forward reading of the
  table: it is no rider, and is not treated by `ridesPast₁`; `fwd_eq₁` serves for it too.
- The seven sub-protocols of a kind in this chain, and the two later chains, are not treated.
- It is true also where the thread holds at nothing.

-/
import E2E.KeyRest
import Johnson.Desc.ProofFile.Honest.Thread.Pays

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.KeyThread
open VerifiableInference.Desc (FileDescription Strs Wit Reading)
open VerifiableInference.Desc.Key
open VerifiableInference.Desc.Key (FirstState Xi)
open Johnson.RunOne.KeyRows1
open Johnson.RunOne.KeyRows23 (atSix)
open ProofFile.Honest

/-! ## 1 The rule -/

section
variable {XI P S Cells M Smp Rec : Type} (F : FileDescription XI) (G : Reading (P × S) Cells M Smp Rec)
  (at_ : Where) (meetsT : Rec → Cells → Prop) (K : KPlan) (R : KRead Cells M) (X : KReaders S)
  (near : Nat → P × S → Strs → Prop)
  (forms worth other : Nat → String → P × S → Strs → Wit Cells Unit M → Prop)

/-- **From in front to behind**, under the library's facts at the swapped states. -/
theorem fwd_of_rides (i : KItem) (hp : plain i = true) (p : P) (s s' : S) (y y' : Strs)
    (w : Wit Cells Unit M) (H : Rides G X [i] p s' s)
    (hu : holdsH F G at_ meetsT (meaning₁ K R X near forms worth other) i (p, s) y w) :
    holdsH F G at_ meetsT (meaning₁ K R X near forms worth other) i (p, s') y' w := by
  cases i with
  | unmarked => exact rides_unmarked K R X near forms worth other p s' s H.marked hu
  | pinT =>
    obtain ⟨r, h1, h2⟩ := hu
    exact ⟨r, H.pins.recOf.trans h1, h2⟩
  | inRange l => exact hu
  | pin k =>
    obtain ⟨o, z, h1, h2, h3⟩ := hu
    exact ⟨o, z, h1, (H.pins.smp _ _).trans h2, h3⟩
  | near k => simp [plain] at hp
  | srow k =>
    exact rides_srow K R X near forms worth other k p s' s y w
      (H.stmt ⟨_, List.mem_singleton.2 rfl, rfl⟩) hu
  | forms l r => simp [plain] at hp
  | worth l x => simp [plain] at hp
  | rows l =>
    exact rides_rows K R X near forms worth other l p s' s y w
      (H.stmt ⟨_, List.mem_singleton.2 rfl, rfl⟩) (H.rows l (List.mem_singleton.2 rfl)) hu
  | kclaims l =>
    exact rides_kclaims K R X near forms worth other l p s' s y w
      (H.keys l (List.mem_singleton.2 rfl)) hu
  | grows =>
    exact rides_grows K R X near forms worth other p s' s y w
      (H.stmt ⟨_, List.mem_singleton.2 rfl, rfl⟩) (H.grp (List.mem_singleton.2 rfl)).1
      (H.grp (List.mem_singleton.2 rfl)).2 hu
  | pile =>
    exact rides_pile K R X near forms worth other p s' s y w (H.pile (List.mem_singleton.2 rfl)) hu
  | claim c n => simp [plain] at hp

end

/-! ## 2 The library's facts, swapped, at the first chain -/

section
variable {Cells M Smp Rec : Type} (G : Reading (Xi × FirstState) Cells M Smp Rec)
  (one : OnBytes.Params.OneTime)

theorem rides_clr' (hG : ReadsD G) (O : List KItem) (p : Xi) (s : FirstState) :
    Rides G (readers₁ one) O p (clr s) s :=
  { marked := rfl, pins := hG p (clr s) s rfl
    stmt := fun _ => ⟨⟨rfl, fun _ _ => rfl⟩, fun _ x' h => ⟨x', h, rfl, rfl⟩⟩
    rows := fun _ _ => rfl, keys := fun _ _ => rfl, pile := fun _ => rfl
    grp := fun _ => ⟨rfl, fun _ G' h => ⟨G', h, rfl⟩⟩ }

variable {s : FirstState} {d' : VerifiableInference.Desc.Key.PlainState}

/-- A message in front of a caller is one behind it, with the same sample. -/
theorem oracle_call' (H : CallGround s d') (o : Nat) (x' : OnBytes.Oracle)
    (h : s.d.st.oracles[o]? = some x') :
    ∃ x, d'.st.oracles[o]? = some x ∧ x.sampled = x'.sampled ∧ x.sampleRows = x'.sampleRows := by
  have e := H.oracle o
  rw [h] at e
  cases hx : d'.st.oracles[o]? with
  | none =>
    rw [hx] at e
    cases e
  | some x =>
    rw [hx] at e
    have e' : unl x = unl x' := Option.some.inj e
    exact ⟨x, rfl, congrArg (·.sampled) e', congrArg (·.sampleRows) e'⟩

theorem rides_call' (hG : ReadsL G) (H : CallGround s d') (Fk : _) (hm : _) (O : List KItem)
    (p : Xi) :
    Rides G (readers₁ one) O p (withCall s d' Fk hm) s :=
  { marked := rfl
    pins := hG p (withCall s d' Fk hm) s (fun o => (H.oracle o).symm) H.book.symm H.codes.symm
    stmt := fun _ => ⟨⟨H.tables.1.symm, fun o part => (H.tables.2 o part).symm⟩,
      fun o x' h => oracle_call' H o x' h⟩
    rows := fun _ _ => rfl, keys := fun _ _ => rfl, pile := fun _ => rfl
    grp := fun _ => ⟨rfl, fun g G' h =>
      ⟨G', (show d'.st.groups[g]? = some G' from H.groups.symm ▸ h), rfl⟩⟩ }

theorem rides_rows' (hG : ReadsL G) (H : RowsGround s d') (O : List KItem)
    (hO : KItem.grows ∉ O) (p : Xi) : Rides G (readers₁ one) O p (withD s d') s :=
  { marked := rfl
    pins := hG p (withD s d') s (fun o => by
      show (s.d.st.oracles[o]?).map unl = (d'.st.oracles[o]?).map unl
      rw [H.oracles]) H.book.symm H.codes.symm
    stmt := fun _ => ⟨⟨H.tables.1.symm, fun o part => (H.tables.2 o part).symm⟩,
      fun o x' h => ⟨x', (show d'.st.oracles[o]? = some x' from H.oracles.symm ▸ h), rfl, rfl⟩⟩
    rows := fun _ _ => rfl, keys := fun _ _ => rfl, pile := fun _ => rfl
    grp := fun h => absurd h hO }

end

/-! ## 3 At the meaning of the first chain -/

section
variable {XI Cells M Smp Rec : Type} (F : FileDescription XI)
  (G : Reading (Xi × FirstState) Cells M Smp Rec) (at_ : Where) (meetsT : Rec → Cells → Prop)
  (one : OnBytes.Params.OneTime) (R : KRead Cells M)

/-- The rule at the first chain's meaning. -/
theorem fwd_at (i : KItem) (hp : plain i = true) (p : Xi) (s s' : FirstState) (y y' : Strs)
    (w : Wit Cells Unit M) (H : Rides G (readers₁ one) [i] p s' s)
    (hu : holdsH F G at_ meetsT (meaning₁At one R) i (p, s) y w) :
    holdsH F G at_ meetsT (meaning₁At one R) i (p, s') y' w :=
  fwd_of_rides F G at_ meetsT (plan₁ one) R (readers₁ one) _ _ _ _ i hp p s s' y y' w H hu

/-- **Behind a layer.** -/
theorem fwd_layer (hG : ReadsD G) (i : KItem) (hp : plain i = true) (p : Xi) (s s' : FirstState)
    (y y' : Strs) (w : Wit Cells Unit M) (h : LayerKeeps s s')
    (hu : holdsH F G at_ meetsT (meaning₁At one R) i (p, s) y w) :
    holdsH F G at_ meetsT (meaning₁At one R) i (p, s') y' w := by
  obtain ⟨F', rows, keys, rfl⟩ := h
  have hP : SamePins G
      (p, { s with base := { s.base with fork := some F', rows := s.base.rows ++ [rows],
                                         keys := s.base.keys ++ [keys] } }) (p, s) :=
    hG p _ s rfl
  cases i with
  | unmarked => exact hu
  | pinT =>
    obtain ⟨r, h1, h2⟩ := hu
    exact ⟨r, hP.recOf.trans h1, h2⟩
  | inRange l => exact hu
  | pin k =>
    obtain ⟨o, z, h1, h2, h3⟩ := hu
    exact ⟨o, z, h1, (hP.smp _ _).trans h2, h3⟩
  | near k => simp [plain] at hp
  | srow k => exact hu
  | forms l r => simp [plain] at hp
  | worth l x => simp [plain] at hp
  | rows l =>
    obtain ⟨rs, h1, h2, h3⟩ := hu
    have h1' : s.base.rows[l]? = some rs := h1
    obtain ⟨hl, -⟩ := List.getElem?_eq_some_iff.1 h1'
    refine ⟨rs, ?_, h2, h3⟩
    show (s.base.rows ++ [rows])[l]? = some rs
    rw [List.getElem?_append_left hl]
    exact h1'
  | kclaims l =>
    obtain ⟨L, ks, h1, h2, h3, h4⟩ := hu
    have h2' : (s.base.keys[l]?).bind (Johnson.RunOne.KeyReaders.pendingOf one l) = some ks := h2
    refine ⟨L, ks, h1, ?_, h3, h4⟩
    show ((s.base.keys ++ [keys])[l]?).bind (Johnson.RunOne.KeyReaders.pendingOf one l) = some ks
    cases hk : s.base.keys[l]? with
    | none =>
      rw [hk] at h2'
      cases h2'
    | some c =>
      obtain ⟨hl, -⟩ := List.getElem?_eq_some_iff.1 hk
      rw [List.getElem?_append_left hl]
      exact h2'
  | grows => exact hu
  | pile => exact hu
  | claim c n => simp [plain] at hp

/-- **AT THE TWELVE NUMBERS, FROM THE EQUATION.** -/
theorem fwd_eq₁ (hG : ReadsL G) (other : Nat → FirstState → FirstState → Prop) :
    ∀ b ∈ [2, 3, 5, 6, 7, 8, 9, 11, 12, 13, 14, 18], ∀ i, plain i = true →
      (b = 14 → i ≠ KItem.grows) → ∀ (p : Xi) (s s' : FirstState) (y y' : Strs)
      (w : Wit Cells Unit M), eq₁ one other b s s' →
      holdsH F G at_ meetsT (meaning₁At one R) i (p, s) y w →
      holdsH F G at_ meetsT (meaning₁At one R) i (p, s') y' w := by
  intro b hb i hp h14 p s s' y y' w he hu
  have same : ∀ t : FirstState, t = s → holdsH F G at_ meetsT (meaning₁At one R) i (p, t) y' w := by
    intro t ht
    subst ht
    exact fwd_at F G at_ meetsT one R i hp p t t y y' w (rides_same G one [i] p t) hu
  have clear : ∀ t : FirstState, t = clr s →
      holdsH F G at_ meetsT (meaning₁At one R) i (p, t) y' w := by
    intro t ht
    subst ht
    exact fwd_at F G at_ meetsT one R i hp p s _ y y' w
      (rides_clr' G one (ReadsL.readsD G hG) [i] p s) hu
  have call : ∀ (n : Nat) (t : FirstState), (∃ d' Fk hm, t = withCall s d' Fk hm ∧
      CallGround s d' ∧ ForkReady n Fk hm) →
      holdsH F G at_ meetsT (meaning₁At one R) i (p, t) y' w := by
    rintro n t ⟨d', Fk, hm, rfl, H, -⟩
    exact fwd_at F G at_ meetsT one R i hp p s _ y y' w (rides_call' G one hG H Fk hm [i] p) hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact same s' he
  · exact call _ s' he
  · exact fwd_layer F G at_ meetsT one R (ReadsL.readsD G hG) i hp p s s' y y' w he hu
  · exact same s' he
  · exact clear s' he
  · exact same s' he
  · exact call _ s' he
  · exact fwd_layer F G at_ meetsT one R (ReadsL.readsD G hG) i hp p s s' y y' w he hu
  · exact same s' he
  · exact clear s' he
  · obtain ⟨d', rfl, H, -⟩ := he
    exact fwd_at F G at_ meetsT one R i hp p s _ y y' w
      (rides_rows' G one hG H [i] (fun h => h14 rfl (List.mem_singleton.1 h).symm) p) hu
  · exact same s' he

/-- An item of a later chain, at one state: its sentence at this meaning reads no oracle. -/
theorem fwd_claim (c : Nat) (n : String) (a : Xi × FirstState) (y y' : Strs)
    (w : Wit Cells Unit M)
    (hu : holdsH F G at_ meetsT (meaning₁At one R) (.claim c n) a y w) :
    holdsH F G at_ meetsT (meaning₁At one R) (.claim c n) a y' w := hu

end

/-! ## 4 Which items are open across -/

/-- What may be open across the sub-protocol number b and neither shut nor owed. -/
def okAcross (b : Nat) (i : KItem) : Bool :=
  (plain i && !(b == 14 && i == .grows)) ||
    (b == 18 && match i with | .claim _ _ => true | _ => false)

theorem riders_ok : ∀ b ∈ [2, 3, 5, 6, 7, 8, 9, 11, 12, 13, 14, 18],
    ∀ i ∈ fwdOpen (start₁ 2) rowsFirst b, i ∉ (rowsFirst b).shuts → i ∉ (rowsFirst b).owes →
      okAcross b i = true := by decide

/-! ## 5 The debt -/

section
variable {Bk : ProverCoinCounts} {W₀ Rc Cells M Smp Rec X' : Type} (Xs : Source) (N : H2U.PlaceNums)
  (Pl : LaterPlaces) (L : KeyFill Bk W₀ Rc Cells M Smp Rec) (w₀ : W₀) (rc : Rc) (x : Xi)
  {hs₁ : List (Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X')}
  {tb₁ : Fmt.TreeSource → Coins Bk → Local W₀ Rc Xi Unit → List Fmt.Drawn →
    VerifiableInference.Desc.Place × Table}

/-- **THE RIDERS, AT THE TWELVE.** -/
theorem ridesPast₁ (hG : ReadsL L.base.h₁) :
    ∀ b ∈ [2, 3, 5, 6, 7, 8, 9, 11, 12, 13, 14, 18],
      RidesPast (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁) b := by
  intro b hb k s m E s' ps i v _ hk hi hs ho hu
  have ok := riders_ok b hb i hi hs ho
  unfold okAcross at ok
  rcases Bool.or_eq_true _ _ ▸ ok with h1 | h2
  · rw [Bool.and_eq_true] at h1
    refine fwd_eq₁ (D Xs N Pl) L.base.h₁ atSix L.meetsT (one₀ Xs) L.R hG L.kind₁ b hb i h1.1 ?_ _ s
      s' _ _ v hk hu
    rintro rfl rfl
    simp at h1
  · rw [Bool.and_eq_true] at h2
    have hb18 : b = 18 := by simpa using h2.1
    subst hb18
    have e : s' = s := hk
    subst e
    cases i with
    | claim c n =>
      exact fwd_claim (D Xs N Pl) L.base.h₁ atSix L.meetsT (one₀ Xs) L.R c n _
        ((laid₁ Xs N Pl L w₀ rc x hs₁ tb₁).strs E)
        ((laid₁ Xs N Pl L w₀ rc x hs₁ tb₁).strs (E.add ps)) v hu
    | _ => simp at h2

end

end AtPublicFiles.KeyThread

#print axioms AtPublicFiles.KeyThread.fwd_of_rides
#print axioms AtPublicFiles.KeyThread.rides_clr'
#print axioms AtPublicFiles.KeyThread.oracle_call'
#print axioms AtPublicFiles.KeyThread.rides_call'
#print axioms AtPublicFiles.KeyThread.rides_rows'
#print axioms AtPublicFiles.KeyThread.fwd_at
#print axioms AtPublicFiles.KeyThread.fwd_layer
#print axioms AtPublicFiles.KeyThread.fwd_eq₁
#print axioms AtPublicFiles.KeyThread.fwd_claim
#print axioms AtPublicFiles.KeyThread.riders_ok
#print axioms AtPublicFiles.KeyThread.ridesPast₁
