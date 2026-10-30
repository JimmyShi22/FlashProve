-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
THE DEBT IS MOVED INTO NAMED PREMISES, NOT PAID.
E2E/KeyLastOwn.lean: the last chain's thread at a key file (`lettersLastKey`,
E2E/KeyLastThread.lean) behind its own proximity test, the chain's member number 2.

Why. The thread reaches the chain's last border through this member alone. The library's `step_two`
(Johnson/Desc/Last/ShapeGives.lean) takes the form from border 2 to border 3 under four debts on what
the test's yes lays: the named values stay, the own group's test has begun, the codes stay, the
statement is tidy.

Main names.
  `own_key`: the member decides as the library's own test, seated.
  `own_step`: `step_two` at that test, with all four debts paid by what the yes lays and by the form
    at border 2, where the test's place sends its masks ahead and has one answer.
  `form_own`: `FormKeeps` at the member, at every value of the riders, in scope.
  `behind_own`, `behind_own_side`: `Behind` there.

OF `Behind`'s THREE CLAUSES ONLY THE FORM IS EARNED HERE. `keeps` is the premise `hK` itself, to the
letter. `rides` is a premise in `behind_own`; in `behind_own_side`, at the value meant, it is
`side₃_step`. `form_own` does not call it.

What stays open. `Kp` at the test's place is a letter and `hK` a premise on it, asked at every state:
no file here says which value is meant. That the riders hold at the chain's start at these letters
has no payer. The form is evaluated at no state of a key file: this is an implication from the thread
at border 2, true where nothing stands there. It reads no prover: that the test says yes at a run is
not said. `hs` and `scope` hold together at `VerifierAndGoals.storedPublicFiles` (`first_zFull`, E2E/KeyShapeFullAtZFull.lean).

NOT IN FRONT OF A LAW OVER COINS: `form_own`, `behind_own` and `behind_own_side` bear this label; the rule
is at its home, the head of Johnson/Bind/ForProver/FiveFieldsAt.lean. Their ground. They stand behind
`Thr` at border 2, in `FormKeeps` and `Behind`, whose clauses tie these letters, of the first kind: `w`
and `Vd` under the clause on the input; `wit`, `Mg₀`, `m₁`, `ML` under the clause on the items; `ends`
under the form; `table` under the clause on the trees; `Rd` under the clause on the riders. `p` is read
by nothing. `hs` and `scope` read the public files and `hK` names no coin: of neither kind. The two `behind`
statements call `behind_of_form`, which bears the label, and keep its tied letters. None of these is
the term that the committer makes. None: the bar is flat. `own_key` and `own_step` name no coin.

Nothing on soundness, completeness, hiding or binding.

-/
import E2E.KeyLastQuiet
import E2E.KeyShapeOwn
import E2E.KeySide3
import E2E.KeyBehind3
import Johnson.RunOne.Law.K12Grows
import Johnson.Desc.Sound.WordsMore

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace AtPublicFiles.KeyLastOwn
open ProofFile.Honest ProofFile.Honest.K14
open VerifiableInference.Desc (Block Place Strs)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Third (S₃ P₁₄ FirstEnd₃ SharedOut)
open VerifiableInference.Desc.Last (ItemL MeaningL fillAt shapeAt shapeAt_of_fill fill_of_shapeAt
  behindOk_of_two step_two lastPlaces)
open VerifiableInference.Desc.Key (Xi FirstState KItem Source LaterPlaces Claim descriptionFromSource thirdPar
  ownTest)
open VerifiableInference.Desc.K12 (T12 proximityTestKind guardedProximityTestParts)
open Johnson.Desc.First.Walk.Tied (StepYes)
open _root_.Desc.K14 (St)
open AtPublicFiles.KeyFile (KeyParts)
open AtPublicFiles.KeyThread (stepYes_of_step Side₃ side₃_step seat_behind)
open AtPublicFiles.KeyLastThread (lettersLastKey handKey endKey)
open AtPublicFiles.KeyLastQuiet (behind_of_form)

/-- The test at the member number 2, as the library seats it. -/
abbrev ownBlock (Pl : LaterPlaces) : Block S₃ Unit :=
  VerifiableInference.Desc.K12.Seat.onOwn
    (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ Pl.W) : Block T12 Unit)

/-- The member number 2 of the key's last chain decides as the library's own test. -/
theorem own_key (Xs : Source) (Nr : H2U.PlaceNums) (Pl : LaterPlaces) (blk : Block S₃ Claim)
    (hb : (descriptionFromSource Xs Nr Pl).second.blocksInOrder[2]? = some blk) : blk.decide = (ownBlock Pl).decide := by
  obtain rfl := Option.some.inj hb
  rfl

/-- **`step_two` at the own test**, and the statement behind it is tidy. The form at border 2 gives
the tidy statement and, through the start, that the codes' lengths are in order; the test's yes does
the rest. -/
theorem own_step {p : P₁₄} {R : List Fmt.DeclaredRound} {h : FirstEnd₃} {o : SharedOut} {Pl : LaterPlaces}
    {s s' : S₃} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (he : (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ Pl.W).early = true)
    (ha : (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ Pl.W).answers = 1)
    (hs : shapeAt p R 2 h o s = true) (hd : (ownBlock Pl).decide s rs gs = .ok s') :
    shapeAt p R 3 h o s' = true ∧ OnBytes.Means.Tidy s'.st := by
  obtain ⟨tE, hk, rfl⟩ := AtPublicFiles.AtFiles.own_inv _ s s' rs gs hd
  obtain ⟨⟨s₀, B⟩, -⟩ := behindOk_of_two hs
  obtain ⟨b, y, G, dot, L⟩ := B.laid
  have hl : s.st.codes.lengthsOk = true := by
    rw [L.codes]
    exact VerifiableInference.Desc.Sound.lengthsOk_of_start _ _ _ _ _ _ _ _ _ _ _ B.start
  obtain ⟨-, G', -, hG'⟩ := Johnson.RunOne.Law.K12Grows.k12_grows _ he ha _ tE rs gs hk
  have hT := VerifiableInference.Desc.K12.Coin.k12_tidy _ _ tE rs gs hk hl B.tidy
  exact ⟨step_two hs rfl ⟨_, hG', rfl⟩ (H2K.Out.k12_grows _ _ tE rs gs hk).1 hT, hT⟩

section
variable {Bk : ProverCoinCounts} {W₀ Rc X₀ X Wk Wt : Type}
  (Xs : Source) (Nr : H2U.PlaceNums) (Pl : LaterPlaces) (K : KeyParts W₀ Rc X₀ X Wk)
  (ℓ : WitLens Wt) (Nm : NumbersS)
  (Mg₀ : Local W₀ Rc Xi Unit → MeaningS St (Xi × FirstState) Wt)
  (m₁ : Local W₀ Rc Xi Unit → KItem → Xi × FirstState → Strs → Wt → Prop)
  (ML : MeaningL S₃ Wt)
  (ends : Coins Bk → Local W₀ Rc Xi Unit → List Fmt.Drawn → (Xi × FirstState) × St)
  (wit : Coins Bk → Local W₀ Rc Xi Unit → List Fmt.Drawn → Wt)
  (table : Fmt.TreeSource → Coins Bk → Local W₀ Rc Xi Unit → List Fmt.Drawn → Place × Table)
  (n₁ n₂ : Nat) (Vd : Local W₀ Rc Xi Unit → Prop) (Rd : Nat → Local W₀ Rc Xi Unit → S₃ → Prop)
  (Kp : Place → S₃ → S₃ → Prop) (w : Local W₀ Rc Xi Unit)

/-- **`FormKeeps` at the own test**, at every value of the riders. The clause on what is kept is the
premise `hK`.
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem form_own {Z : VerifierAndGoals.PublicFiles} (hs : AtPublicFiles.AtFiles.KeySourced Z Xs Nr Pl)
    (scope : VerifierAndGoals.InScope Z = true)
    (hK : ∀ blk, (descriptionFromSource Xs Nr Pl).second.blocksInOrder[2]? = some blk → ∀ ft s s', StepYes ft blk s s' →
      Kp ⟨3, none, 2, .K12⟩ s s') :
    FormKeeps (lettersLastKey Xs Nr Pl K ℓ Nm Mg₀ m₁ ML ends wit table n₁ n₂ Vd Rd Kp w).thread 2 := by
  intro blk hb k s m E ds y cols s' hA hds hS
  have hFit := hA.2.1
  have hF := hA.2.2.1.1
  obtain ⟨hM, hst⟩ := hS
  have hyes := stepYes_of_step hst
  obtain ⟨gs, hd⟩ := _root_.Desc.K14.Law.step_decides _ blk s s' _ cols _ hst
  rw [own_key Xs Nr Pl blk hb] at hd
  obtain ⟨⟨l, -, hy⟩, -⟩ := hM
  have es := seat_behind _ (k := k) hFit hy s'
  have hF' := (Bool.and_eq_true _ _).mp hF
  obtain ⟨f, o, hf, ho, hs0⟩ := shapeAt_of_fill _ _ _ _ hF'.1
  obtain ⟨he, ha⟩ := AtPublicFiles.AtFiles.own_place_in_scope hs scope
  obtain ⟨g1, hT⟩ := own_step he ha hs0 hd
  have h1 := fill_of_shapeAt _ _ _ _ hf ho g1
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [es]
    exact (Bool.and_eq_true _ _).mpr ⟨h1, rfl⟩
  · rw [es]
    exact hT.inOrder
  · intro q hq
    obtain rfl : (⟨3, none, 2, .K12⟩ : Place) = q := Option.some.inj hq
    show (if (⟨3, none, 2, .K12⟩ : Place) = ⟨3, none, 0, .K14⟩ then _ else _)
    rw [if_neg (by decide)]
    exact hK blk hb _ s s' hyes

/-- **`Behind` at the own test**: the form is earned; `hK` is the clause on what is kept; `hR` the
clause on the riders.
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem behind_own {Z : VerifierAndGoals.PublicFiles} (hs : AtPublicFiles.AtFiles.KeySourced Z Xs Nr Pl)
    (scope : VerifierAndGoals.InScope Z = true)
    (hK : ∀ blk, (descriptionFromSource Xs Nr Pl).second.blocksInOrder[2]? = some blk → ∀ ft s s', StepYes ft blk s s' →
      Kp ⟨3, none, 2, .K12⟩ s s')
    (hR : ∀ blk, (lettersLastKey Xs Nr Pl K ℓ Nm Mg₀ m₁ ML ends wit table n₁ n₂ Vd Rd Kp w).thread.bs[2]? =
        some blk → ∀ s s', StepYes
          (lettersLastKey Xs Nr Pl K ℓ Nm Mg₀ m₁ ML ends wit table n₁ n₂ Vd Rd Kp w).thread.ft blk s s' →
        ∀ v, Rd 2 v s → Rd 3 v s') :
    Behind (lettersLastKey Xs Nr Pl K ℓ Nm Mg₀ m₁ ML ends wit table n₁ n₂ Vd Rd Kp w).thread 2 :=
  behind_of_form (form_own Xs Nr Pl K ℓ Nm Mg₀ m₁ ML ends wit table n₁ n₂ Vd Rd Kp w hs scope hK) hR

/-- **The same at the riders that are meant.**
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem behind_own_side {Z : VerifierAndGoals.PublicFiles} (hs : AtPublicFiles.AtFiles.KeySourced Z Xs Nr Pl)
    (scope : VerifierAndGoals.InScope Z = true) (p : Johnson.RunOne.KeyRows23.P₃)
    (hK : ∀ blk, (descriptionFromSource Xs Nr Pl).second.blocksInOrder[2]? = some blk → ∀ ft s s', StepYes ft blk s s' →
      Kp ⟨3, none, 2, .K12⟩ s s') :
    Behind (lettersLastKey Xs Nr Pl K ℓ Nm Mg₀ m₁ ML ends wit table n₁ n₂ Vd
      (fun b _ s => Side₃ Xs Pl b (p, s)) Kp w).thread 2 :=
  behind_own Xs Nr Pl K ℓ Nm Mg₀ m₁ ML ends wit table n₁ n₂ Vd _ Kp w hs scope hK
    fun _ hb _ _ hy _ h => side₃_step Xs Nr Pl hs scope (by decide) hb hy h

end

end AtPublicFiles.KeyLastOwn

#print axioms AtPublicFiles.KeyLastOwn.own_key
#print axioms AtPublicFiles.KeyLastOwn.own_step
#print axioms AtPublicFiles.KeyLastOwn.form_own
#print axioms AtPublicFiles.KeyLastOwn.behind_own
#print axioms AtPublicFiles.KeyLastOwn.behind_own_side
