-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeySideCash.lean: WHAT THE SHARED CHAIN's CLAUSE ON THE STATE IS WORTH (`Side₂`,
E2E/KeySideDef.lean: the library's `Tests₂` at every good state of the first chain): under ONE
CLOSED PUBLIC PREMISE it gives the library's Bool on the shared chain's state and the half of that
heap that reads the key and the chain's own state; and in front of the last chain's start, where
both earlier threads' ends are in hand, the heap WHOLE. Short lemmas. On the verifier's states
alone. NOTHING IS SHOWN OF ANY PROVER.

  `GoodFirst X`: THE PREMISE: there is a state of the first chain at which its side holds at its
      last border. IT READS THE PUBLIC VALUES ALONE: no run, no instance, no prover
  **`side₂_cash`**: under it `Side₂ X k key s` gives the Bool `shape₂` at border k and `Own₂`
      (E2E/KeyRest.lean)
  **`door_join`**: a good state e₁ and `Side₂ X 12 key e₂` give `Tests₂` at border 12 whole, and so
      `Handed₂` of e₁ and e₂
  `good_of_thr`: the first chain's thread at its last border HOLDS a good state, as its own clause
      on the state: so `GoodFirst`
  **`door_of_threads`**: FROM THE TWO THREADS AT THEIR LAST BORDERS: the first thread's own clause
      and the shared chain's side off its fold, joined: `Tests₂` at 12 whole, and `Handed₂`. In
      scope, where the key fits, at any thread over the shared chain that begins at the description's
      start (`OverShared`, `Begun₂`)
  **`codes_of_threads`**: in scope, the like: the codes in the two last states are the public
      ones: the heap's
      tie between the two states, the library's `codes_of_last` (Johnson/RunOne/KeySeam1.lean) and a
      public equation

Limits.
- NO MEMBER OF `GoodFirst` IS SHOWN. In scope it follows from any history of accepting steps through
  the whole first chain, at any instance (`side18_sourced`, E2E/KeyStateSide18.lean); that there is
  one is not shown.
- `side₂_cash` AND `door_join` CARRY NO SCOPE: off the full size `GoodFirst` may well be false (the
  seats and numbers in it are the full size's numerals), and then they say nothing.
- `door_of_threads` speaks of the states at which the two threads stand. That these are the values
  of the letter `ends`, which the last chain's thread is handed, is not shown.
- It is true also where a thread holds at nothing.

-/
import E2E.KeyStateSide2

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.KeyThread
open VerifiableInference.Desc.Key (Xi FirstState Source LaterPlaces)
open Johnson.RunOne.KeyRows1 (plan₁)
open Johnson.RunOne.KeyRows23 (St₂ atSix shapeAt oneAt last₁At)
open LPFD (T₂ off₂N)
open ProofFile.Honest

/-- **The closed public premise.** -/
def GoodFirst (X : Source) : Prop := ∃ e₁ : FirstState, Side18 X 19 e₁

section
variable (X : Source)

/-- **What the shared chain's clause is worth under it.** -/
theorem side₂_cash (hg : GoodFirst X) {k : Nat} {key : OnBytes.TableKey} {s : St₂}
    (h : Side₂ X k key s) :
    LKFU.Shape23.ok (LKFU.Shape23.shape₂ (shapeAt X) (oneAt X).given.plan.samples k s) = true ∧
      Own₂ atSix (shapeAt X) off₂N k key s := by
  obtain ⟨e₁, he⟩ := hg
  have T := (tests₂_iff atSix (shapeAt X) (plan₁ (oneAt X)) (oneAt X).given.plan.samples
    (last₁At (oneAt X)) off₂N k ⟨key⟩ e₁ s).1 (h e₁ he)
  exact ⟨T.1, T.2.1⟩

/-- **In front of the last chain's start.** -/
theorem door_join {e₁ : FirstState} (he : Side18 X 19 e₁) {key : OnBytes.TableKey} {e₂ : St₂}
    (h : Side₂ X 12 key e₂) :
    T₂ X atSix off₂N 12 ((⟨key⟩, e₁), e₂) ∧
      Handed₂ atSix (shapeAt X) (plan₁ (oneAt X)) (last₁At (oneAt X)) e₁ e₂ :=
  ⟨h e₁ he, ((tests₂_iff atSix (shapeAt X) (plan₁ (oneAt X)) (oneAt X).given.plan.samples
    (last₁At (oneAt X)) off₂N 12 ⟨key⟩ e₁ e₂).1 (h e₁ he)).2.2⟩

end

section
variable {Bk : ProverCoinCounts} {W₀ Rc Cells M Smp Rec X' X₀' : Type} (Xs : Source) (N : H2U.PlaceNums)
  (Pl : LaterPlaces) (L : KeyFill Bk W₀ Rc Cells M Smp Rec) (w₀ : W₀) (rc : Rc) (x : Xi)
  {hs₁ : List (Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X')}
  {tb₁ : Fmt.TreeSource → Coins Bk → Local W₀ Rc Xi Unit → List Fmt.Drawn →
    VerifiableInference.Desc.Place × Table}
  {hs₂ : List (Placed Empty (Common W₀ Rc OnBytes.TableKey) X₀')}
  {tb₂ : Fmt.TreeSource → Coins Bk → Common W₀ Rc OnBytes.TableKey → List Fmt.Drawn →
    VerifiableInference.Desc.Place × Table}
  {Z : VerifierAndGoals.PublicFiles}

/-- The first chain's thread at its last border HOLDS a good state: its own clause on the state. -/
theorem good_of_thr {k : Coins Bk} {e₁ : FirstState} {m : Mid (Local W₀ Rc Xi Unit) X'} {E : Env}
    (hT : Thr (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁) 19 k e₁ m E) : GoodFirst Xs :=
  ⟨e₁, hT.2.2.1.2.1⟩

/-- **FROM THE TWO THREADS AT THEIR LAST BORDERS**: the first thread's clause on the state, and the
shared chain's side off its fold, joined. -/
theorem door_of_threads {V W Xh Pb : Type} {T : Thread Bk (D Xs N Pl).S₂ (D Xs N Pl).Cl V W Xh Pb}
    (hs : AtPublicFiles.AtFiles.KeySourced Z Xs N Pl) (scope : VerifierAndGoals.InScope Z = true)
    (hfit : KeyFits Xs x) {k₁ k₂ : Coins Bk} {e₁ : FirstState} {e₂ : St₂}
    {m₁ : Mid (Local W₀ Rc Xi Unit) X'} {m₂ : Mid W Xh}
    {E₁ E₂ : Env} (h₁ : Thr (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁) 19 k₁ e₁ m₁ E₁)
    (hO : OverShared Xs N Pl T) (hB : Begun₂ Xs N Pl x T) (h₂ : Thr T 12 k₂ e₂ m₂ E₂) :
    T₂ Xs atSix off₂N 12 ((x, e₁), e₂) ∧
      Handed₂ atSix (shapeAt Xs) (plan₁ (oneAt Xs)) (last₁At (oneAt Xs)) e₁ e₂ := by
  have hS : Side₂ Xs 12 x.key e₂ :=
    t₂_thr Xs N Pl x hs scope hfit hO hB (Nat.le_refl 12) h₂
  exact door_join Xs (key := x.key) h₁.2.2.1.2.1 hS

end

section
open VerifiableInference.Desc VerifiableInference.Desc.Key
open Johnson.RunOne.KeyRows23
open Johnson.RunOne.KeyRows1
open LPFD
variable {Bk : ProverCoinCounts} {W₀ Rc Cells M Smp Rec X' X₀' : Type} (Xs : Source) (N : H2U.PlaceNums)
  (Pl : LaterPlaces) (L : KeyFill Bk W₀ Rc Cells M Smp Rec) (w₀ : W₀) (rc : Rc) (x : Xi)
  {hs₁ : List (Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X')}
  {tb₁ : Fmt.TreeSource → Coins Bk → Local W₀ Rc Xi Unit → List Fmt.Drawn →
    VerifiableInference.Desc.Place × Table}
  {hs₂ : List (Placed Empty (Common W₀ Rc OnBytes.TableKey) X₀')}
  {tb₂ : Fmt.TreeSource → Coins Bk → Common W₀ Rc OnBytes.TableKey → List Fmt.Drawn →
    VerifiableInference.Desc.Place × Table}
  {Z : VerifierAndGoals.PublicFiles}

/-- **The codes at the two last states are the public ones**, in scope. -/
theorem codes_of_threads {V W Xh Pb : Type} {T : Thread Bk (D Xs N Pl).S₂ (D Xs N Pl).Cl V W Xh Pb}
    (hs : AtPublicFiles.AtFiles.KeySourced Z Xs N Pl) (scope : VerifierAndGoals.InScope Z = true)
    (hfit : KeyFits Xs x) {k₁ k₂ : Coins Bk} {e₁ : FirstState} {e₂ : St₂}
    {m₁ : Mid (Local W₀ Rc Xi Unit) X'} {m₂ : Mid W Xh} {E₁ E₂ : Env}
    (h₁ : Thr (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁) 19 k₁ e₁ m₁ E₁)
    (hO : OverShared Xs N Pl T) (hB : Begun₂ Xs N Pl x T) (h₂ : Thr T 12 k₂ e₂ m₂ E₂) :
    e₁.d.st.codes = codesAt Xs ∧ e₂.st.codes = codesAt Xs := by
  obtain ⟨X₀, m, h0, hm, hX, -, -⟩ := hs.source
  have hP := Johnson.RunOne.Law.ReadAtO.readOf_publicOfO h0
  have hp := hs.named.plan
  obtain ⟨x₀, x₁, hl⟩ := hl_in_scope scope hP hm hX hp
  have hfo := fileOk_of_planOk' _ hp
  obtain ⟨e1, e2⟩ := pubsOf_k m Xs hX
  have hc : (oneAt Xs).codes = codesAt Xs :=
    codes_of_front Xs N Pl (by rw [e2, e1]) (front_of_planOk Xs N Pl hp) hfo
  have hA : ASide (oneAt Xs) atSix 19 e₁ := h₁.2.2.1.2.1.1.1
  have c₁ : e₁.d.st.codes = codesAt Xs :=
    (codes_of_last (oneAt Xs) 19 e₁ (t1_of_aSide Xs atSix x₀ x₁ hl 19 e₁ hA)).trans hc
  exact ⟨c₁, (door_of_threads Xs N Pl L w₀ rc x hs scope hfit h₁ hO hB h₂).1.codes.trans c₁⟩

end

end AtPublicFiles.KeyThread

#print axioms AtPublicFiles.KeyThread.side₂_cash
#print axioms AtPublicFiles.KeyThread.door_join
#print axioms AtPublicFiles.KeyThread.good_of_thr
#print axioms AtPublicFiles.KeyThread.door_of_threads
#print axioms AtPublicFiles.KeyThread.codes_of_threads
