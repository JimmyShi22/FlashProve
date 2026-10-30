-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
THE DEBT IS MOVED INTO NAMED PREMISES, NOT PAID.
E2E/KeyLastQuiet.lean: the last chain's thread at a key file (`lettersLastKey`,
E2E/KeyLastThread.lean) brings what the statements on a thread over that chain ask at its two
sub-protocols that leave the state as it is: the test on the taken trees' sources (number 1) and
the chain's end (number 3); and it passes the tests with code.

Main names.
  `quiet_form`: GENERAL in the letters: the form goes to the next border, and `keeps` holds, behind
    a sub-protocol without a round that leaves the state as it is, from the step of the library's
    test that says so.
  `behind_of_form`: GENERAL in the thread: `FormKeeps` and a law on the riders give `Behind`.
  `sources_key`, `end_key`: the two members of the key's last chain are the library's.
  `form_sources`, `form_end`: `FormKeeps` at 1 and 3.
  `behind_sources`, `behind_end`, `behind_first`: `Behind` at 1, 3 and 0, from a law on the riders
    behind the step's yes.
  `behind_sources_side`, `behind_end_side`, `behind_first_side`: the same at the value meant,
    `Rd b v s := Side₃ Xs Pl b (p, s)`, in scope at what the description is made of, where
    `side₃_step` (E2E/KeySide3.lean) is that
    law.
  `owes_sources`, `owes_end`: the forward rows owe nothing.
  `ridesPast_quiet`: the riders past 1 and 3, where the letter `Kp` says that the state stays and
    the open items read no strings.
  `fits_last_key`: the tests with code, at a description that passes its test on the plan.

What stays open. `Rd` and `Kp` are letters, with premises here. Of the open items, those that can
read the strings are the first chain's pin and sample rows through `m₁`: at the honest pin
(`holdsH`, E2E/KeyRest.lean) they do not, and that ease has its price: that the committed word is
an encoding of the message has no payer. `Behind` at the own test (number 2) is not here, and the thread reaches border 3 through it alone.
NO STATE IS SHOWN AT WHICH THESE STATEMENTS SAY ANYTHING: they are implications from the thread at a
border; the form has been evaluated at no state of a key file, `second_key` holds vacuously where it
fails, and `Rd` at the chain's start has no payer at these letters.

NOT IN FRONT OF A LAW OVER COINS: `quiet_form`, `form_sources`, `form_end`, `behind_of_form`,
`behind_sources`, `behind_end`, `behind_first`, the three `…_side` and `ridesPast_quiet` bear this label; the rule is at its home, the
head of Johnson/Bind/ForProver/FiveFieldsAt.lean. This file's ground is that of E2E/KeyLastThread.lean:
they stand behind the thread at a border, whose clauses read the letters at the run's coins. None
of the letters is the term that the committer makes: none: the bar is flat.

Nothing on soundness, completeness or hiding.

-/
import E2E.KeyLastThread
import E2E.KeyRowsLater

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace AtPublicFiles.KeyLastQuiet
open ProofFile.Honest ProofFile.Honest.K14
open VerifiableInference.Desc (Block Place Strs)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Third (S₃ P₁₄ FirstEnd₃ SharedOut takenSources end₃ batchLinearConstraintsSecondPart ownAt)
open VerifiableInference.Desc.Last (ItemL MeaningL fillAt shapeAt shapeAt_of_fill fill_of_shapeAt
  step_one step_three startLast lastPlaces)
open VerifiableInference.Desc.Key (Xi FirstState KItem Source LaterPlaces Claim descriptionFromSource thirdPar
  ownTest)
open Johnson.Desc.First.Walk.Tied (StepYes)
open _root_.Desc.K14 (St)
open AtPublicFiles.KeyFile (KeyParts keyProver)
open AtPublicFiles.KeyThread (stepYes_of_step keeps_paid₃ fits_of lists_of_shaped decl₁ decl₂ decl₃)
open AtPublicFiles.KeyLastThread (lettersLastKey handKey endKey)

/-! ## 1 General -/

section general
variable {Bk : ProverCoinCounts} {Cl W₀ Rc Ix Tr X P₁ Wt : Type}
  (L : LastThread.Letters Bk St S₃ Cl W₀ Rc Ix Tr X P₁ Wt) (p : P₁₄)
  (R : List Fmt.DeclaredRound) (hand : P₁ → Option FirstEnd₃) (ended : St → Option SharedOut)

/-- **The form goes on behind a sub-protocol without a round that leaves the state as it is.**
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem quiet_form (hPL : L.PL = fillAt p R hand ended) (b : Nat)
    (hr : ∀ blk, L.bs[b]? = some blk → blk.rounds = [])
    (hgo : ∀ blk, L.bs[b]? = some blk → ∀ f o s s' rs gs, shapeAt p R b f o s = true →
      blk.decide s rs gs = .ok s' →
        shapeAt p R (b + 1) f o s' = true ∧
          (!decide (lastPlaces.length ≤ b + 1) || L.PL.nothingLeft s') = true)
    (hsame : ∀ blk, L.bs[b]? = some blk → ∀ s s', StepYes L.ft blk s s' → s' = s)
    (hK : ∀ s, L.keeps b s s) : FormKeeps L.thread b := by
  intro blk hb k s m E ds y cols s' hA hds hS
  obtain ⟨-, -, ⟨hF, hP⟩, -, -, -, -⟩ := hA
  obtain ⟨hM, hst⟩ := hS
  have e : s' = s := hsame blk hb s s' (stepYes_of_step hst)
  obtain ⟨gs, hd⟩ := _root_.Desc.K14.Law.step_decides _ blk s s' _ cols _ hst
  rw [hr blk hb] at hds
  obtain rfl : ds = [] := by
    cases ds with
    | nil => rfl
    | cons _ _ => cases hds
  obtain ⟨⟨l, -, hy⟩, -⟩ := hM
  have ei := (play_mid _ _ _ _ _ hy).1
  have eh := play_heard _ _ _ _ _ hy
  rw [List.append_nil] at eh
  have es : L.thread.seat k y.2 s' = ((L.thread.seat k m s).1, s') := by
    unfold Thread.seat
    rw [ei, eh]
  have hF' : (L.PL.shape b (L.thread.seat k m s).1.1 (L.thread.seat k m s).1.2 s &&
      (!decide (lastPlaces.length ≤ b) || L.PL.nothingLeft s)) = true := hF
  rw [Bool.and_eq_true] at hF'
  have h0 := hF'.1
  rw [hPL] at h0
  obtain ⟨f, o, hf, ho, hs0⟩ := shapeAt_of_fill p R _ _ h0
  obtain ⟨g1, g2⟩ := hgo blk hb f o s s' _ gs hs0 hd
  have h1 := fill_of_shapeAt p R _ _ hf ho g1
  have hP' : L.order s := hP
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [es]
    show (L.PL.shape (b + 1) (L.thread.seat k m s).1.1 (L.thread.seat k m s).1.2 s' &&
        (!decide (lastPlaces.length ≤ b + 1) || L.PL.nothingLeft s')) = true
    rw [Bool.and_eq_true]
    refine ⟨?_, g2⟩
    rw [hPL]
    exact h1
  · rw [es]
    show L.order s'
    rw [e]
    exact hP'
  · show L.keeps b s s'
    rw [e]
    exact hK s

end general

/-- **From the form and a law on the riders to the whole debt.**
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem behind_of_form {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} {T : Thread Bk S Cl V W X Pb} {b : Nat}
    (h : FormKeeps T b)
    (hr : ∀ blk, T.bs[b]? = some blk → ∀ s s', StepYes T.ft blk s s' → ∀ v, T.rides b v s →
      T.rides (b + 1) v s') : Behind T b := by
  intro blk hb k s m E ds y cols s' hT hd hS
  obtain ⟨f, kp⟩ := h blk hb k s m E ds y cols s' hT hd hS
  have hM := hS.1
  unfold Thread.Moved at hM
  obtain ⟨⟨l, -, hp⟩, -⟩ := hM
  have hi : y.2.st.input = m.st.input := (play_mid _ _ _ _ _ hp).1
  refine ⟨f, ?_, kp⟩
  rw [hi]
  exact hr blk hb s s' (stepYes_of_step hS.2) _ hT.2.2.2.2.2.1

/-! ## 2 The two members -/

section members
variable (Xs : Source) (Nr : H2U.PlaceNums) (Pl : LaterPlaces)

/-- The member 1 of the key's last chain is the library's test on the sources. -/
theorem sources_key (blk : Block S₃ Claim) (hb : (descriptionFromSource Xs Nr Pl).second.blocksInOrder[1]? = some blk) :
    blk.rounds = [] ∧ blk.decide = (takenSources (ownTest Pl) : Block S₃ Unit).decide := by
  obtain rfl := Option.some.inj hb
  exact ⟨rfl, rfl⟩

/-- The member 3 is the library's end. -/
theorem end_key (blk : Block S₃ Claim) (hb : (descriptionFromSource Xs Nr Pl).second.blocksInOrder[3]? = some blk) :
    blk.rounds = [] ∧ blk.decide = (end₃ [batchLinearConstraintsSecondPart (thirdPar Xs.chains),
      takenSources (ownTest Pl), ownAt (ownTest Pl)] : Block S₃ Unit).decide := by
  obtain rfl := Option.some.inj hb
  exact ⟨rfl, rfl⟩

end members

/-! ## 3 At the letters -/

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

/-- What the letter `keeps` asks at the member 1 and 3, at a state and itself. -/
theorem keeps_self
    (hK : ∀ q ∈ [(⟨3, none, 1, .frame⟩ : Place), ⟨3, none, 3, .frame⟩], ∀ s, Kp q s s) (b : Nat) (hb : b ∈ [1, 3]) (s : S₃) :
      (lettersLastKey Xs Nr Pl K ℓ Nm Mg₀ m₁ ML ends wit table n₁ n₂ Vd Rd Kp w).keeps b s s := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  intro q hq
  rcases hb with rfl | rfl
  · obtain rfl : (⟨3, none, 1, .frame⟩ : Place) = q := Option.some.inj hq
    show (if (⟨3, none, 1, .frame⟩ : Place) = ⟨3, none, 0, .K14⟩ then _ else _)
    rw [if_neg (by decide)]
    exact hK _ (by simp) s
  · obtain rfl : (⟨3, none, 3, .frame⟩ : Place) = q := Option.some.inj hq
    show (if (⟨3, none, 3, .frame⟩ : Place) = ⟨3, none, 0, .K14⟩ then _ else _)
    rw [if_neg (by decide)]
    exact hK _ (by simp) s

/-- `FormKeeps` at the test on the sources.
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem form_sources
    (hK : ∀ q ∈ [(⟨3, none, 1, .frame⟩ : Place), ⟨3, none, 3, .frame⟩], ∀ s, Kp q s s) :
    FormKeeps
      (lettersLastKey Xs Nr Pl K ℓ Nm Mg₀ m₁ ML ends wit table n₁ n₂ Vd Rd Kp w).thread 1 := by
  refine quiet_form _ (thirdPar Xs.chains) (ownTest Pl).rounds handKey endKey rfl 1
    (fun blk hb => (sources_key Xs Nr Pl blk hb).1) ?_ ?_
    (keeps_self Xs Nr Pl K ℓ Nm Mg₀ m₁ ML ends wit table n₁ n₂ Vd Rd Kp w hK 1 (by simp))
  · intro blk hb f o s s' rs gs hs hd
    rw [(sources_key Xs Nr Pl blk hb).2] at hd
    exact ⟨step_one (ownTest Pl) hs rs gs hd, rfl⟩
  · intro blk hb s s' hy
    exact (keeps_paid₃ Xs Nr Pl _).1 blk hb s s' hy

/-- `FormKeeps` at the chain's end.
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem form_end
    (hK : ∀ q ∈ [(⟨3, none, 1, .frame⟩ : Place), ⟨3, none, 3, .frame⟩], ∀ s, Kp q s s) :
    FormKeeps
      (lettersLastKey Xs Nr Pl K ℓ Nm Mg₀ m₁ ML ends wit table n₁ n₂ Vd Rd Kp w).thread 3 := by
  refine quiet_form _ (thirdPar Xs.chains) (ownTest Pl).rounds handKey endKey rfl 3
    (fun blk hb => (end_key Xs Nr Pl blk hb).1) ?_ ?_
    (keeps_self Xs Nr Pl K ℓ Nm Mg₀ m₁ ML ends wit table n₁ n₂ Vd Rd Kp w hK 3 (by simp))
  · intro blk hb f o s s' rs gs hs hd
    rw [(end_key Xs Nr Pl blk hb).2] at hd
    have h := step_three hs _ rs gs hd
    exact ⟨h.1, h.2⟩
  · intro blk hb s s' hy
    refine (keeps_paid₃ Xs Nr Pl _).2 blk ?_ s s' hy
    have e : (descriptionFromSource Xs Nr Pl).second.blocksInOrder.length - 1 = 3 := rfl
    show (descriptionFromSource Xs Nr Pl).second.blocksInOrder[(descriptionFromSource Xs Nr Pl).second.blocksInOrder.length - 1]? = some blk
    rw [e]
    exact hb

/-- The whole debt at the test on the sources, where a rider goes on at a quiet step.
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem behind_sources
    (hK : ∀ q ∈ [(⟨3, none, 1, .frame⟩ : Place), ⟨3, none, 3, .frame⟩], ∀ s, Kp q s s)
    (hR : ∀ blk, (lettersLastKey Xs Nr Pl K ℓ Nm Mg₀ m₁ ML ends wit table n₁ n₂ Vd Rd Kp w).thread.bs[1]? = some blk → ∀ s s',
      StepYes (lettersLastKey Xs Nr Pl K ℓ Nm Mg₀ m₁ ML ends wit table n₁ n₂ Vd Rd Kp w).thread.ft blk s s' → ∀ v, Rd 1 v s → Rd 2 v s') : Behind
      (lettersLastKey Xs Nr Pl K ℓ Nm Mg₀ m₁ ML ends wit table n₁ n₂ Vd Rd Kp w).thread 1 :=
  behind_of_form (form_sources Xs Nr Pl K ℓ Nm Mg₀ m₁ ML ends wit table n₁ n₂ Vd Rd Kp w hK) hR

/-- The whole debt at the chain's end.
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem behind_end
    (hK : ∀ q ∈ [(⟨3, none, 1, .frame⟩ : Place), ⟨3, none, 3, .frame⟩], ∀ s, Kp q s s)
    (hR : ∀ blk, (lettersLastKey Xs Nr Pl K ℓ Nm Mg₀ m₁ ML ends wit table n₁ n₂ Vd Rd Kp w).thread.bs[3]? = some blk → ∀ s s',
      StepYes (lettersLastKey Xs Nr Pl K ℓ Nm Mg₀ m₁ ML ends wit table n₁ n₂ Vd Rd Kp w).thread.ft blk s s' → ∀ v, Rd 3 v s → Rd 4 v s') : Behind
      (lettersLastKey Xs Nr Pl K ℓ Nm Mg₀ m₁ ML ends wit table n₁ n₂ Vd Rd Kp w).thread 3 :=
  behind_of_form (form_end Xs Nr Pl K ℓ Nm Mg₀ m₁ ML ends wit table n₁ n₂ Vd Rd Kp w hK) hR

/-- The whole debt at the chain's first member, from the form behind it.
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem behind_first
    (hR : ∀ blk, (lettersLastKey Xs Nr Pl K ℓ Nm Mg₀ m₁ ML ends wit table n₁ n₂ Vd Rd Kp w).thread.bs[0]? = some blk → ∀ s s',
      StepYes (lettersLastKey Xs Nr Pl K ℓ Nm Mg₀ m₁ ML ends wit table n₁ n₂ Vd Rd Kp w).thread.ft blk s s' → ∀ v, Rd 0 v s → Rd 1 v s') :
    Behind (lettersLastKey Xs Nr Pl K ℓ Nm Mg₀ m₁ ML ends wit table n₁ n₂ Vd Rd Kp w).thread 0 :=
  behind_of_form
    (AtPublicFiles.KeyLastThread.second_key Xs Nr Pl K ℓ Nm Mg₀ m₁ ML ends wit table n₁ n₂ Vd Rd Kp w) hR

/-- **The three at the value meant**, in scope at what the description is made of.
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem behind_sources_side {Z : VerifierAndGoals.PublicFiles} (hs : AtPublicFiles.AtFiles.KeySourced Z Xs Nr Pl)
    (scope : VerifierAndGoals.InScope Z = true) (p : Johnson.RunOne.KeyRows23.P₃)
    (hK : ∀ q ∈ [(⟨3, none, 1, .frame⟩ : Place), ⟨3, none, 3, .frame⟩], ∀ s, Kp q s s) :
    Behind
      (lettersLastKey Xs Nr Pl K ℓ Nm Mg₀ m₁ ML ends wit table n₁ n₂ Vd (fun b _ s => AtPublicFiles.KeyThread.Side₃ Xs Pl b (p, s)) Kp w).thread 1 :=
  behind_sources Xs Nr Pl K ℓ Nm Mg₀ m₁ ML ends wit table n₁ n₂ Vd _ Kp w hK
    fun _ hb _ _ hy _ h => AtPublicFiles.KeyThread.side₃_step Xs Nr Pl hs scope (by decide) hb hy h

/-- The like at the chain's end.
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem behind_end_side {Z : VerifierAndGoals.PublicFiles} (hs : AtPublicFiles.AtFiles.KeySourced Z Xs Nr Pl)
    (scope : VerifierAndGoals.InScope Z = true) (p : Johnson.RunOne.KeyRows23.P₃)
    (hK : ∀ q ∈ [(⟨3, none, 1, .frame⟩ : Place), ⟨3, none, 3, .frame⟩], ∀ s, Kp q s s) :
    Behind
      (lettersLastKey Xs Nr Pl K ℓ Nm Mg₀ m₁ ML ends wit table n₁ n₂ Vd (fun b _ s => AtPublicFiles.KeyThread.Side₃ Xs Pl b (p, s)) Kp w).thread 3 :=
  behind_end Xs Nr Pl K ℓ Nm Mg₀ m₁ ML ends wit table n₁ n₂ Vd _ Kp w hK
    fun _ hb _ _ hy _ h => AtPublicFiles.KeyThread.side₃_step Xs Nr Pl hs scope (by decide) hb hy h

/-- The like at the chain's first member.
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem behind_first_side {Z : VerifierAndGoals.PublicFiles} (hs : AtPublicFiles.AtFiles.KeySourced Z Xs Nr Pl)
    (scope : VerifierAndGoals.InScope Z = true) (p : Johnson.RunOne.KeyRows23.P₃) :
    Behind
      (lettersLastKey Xs Nr Pl K ℓ Nm Mg₀ m₁ ML ends wit table n₁ n₂ Vd (fun b _ s => AtPublicFiles.KeyThread.Side₃ Xs Pl b (p, s)) Kp w).thread 0 :=
  behind_first Xs Nr Pl K ℓ Nm Mg₀ m₁ ML ends wit table n₁ n₂ Vd _ Kp w
    fun _ hb _ _ hy _ h => AtPublicFiles.KeyThread.side₃_step Xs Nr Pl hs scope (by decide) hb hy h

/-- The forward row at the test on the sources owes nothing. -/
theorem owes_sources : (
  (lettersLastKey Xs Nr Pl K ℓ Nm Mg₀ m₁ ML ends wit table n₁ n₂ Vd Rd Kp w).thread.row 1).owes = [] := by
  show (LastRows.rows 1).owes = []
  decide

/-- The forward row at the chain's end owes nothing. -/
theorem owes_end : (
  (lettersLastKey Xs Nr Pl K ℓ Nm Mg₀ m₁ ML ends wit table n₁ n₂ Vd Rd Kp w).thread.row 3).owes = [] := by
  show (LastRows.rows 3).owes = []
  decide

/-- **The riders past a quiet member**, where the letter says that the state stays and the open
items read no strings.
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem ridesPast_quiet (b : Nat) (q : Place) (hq : lastPlaces[b]? = some q)
    (hq0 : q ≠ ⟨3, none, 0, .K14⟩) (hE : ∀ s s', Kp q s s' → s' = s)
    (hY : ∀ v i a y y' u, i ∈
      (lettersLastKey Xs Nr Pl K ℓ Nm Mg₀ m₁ ML ends wit table n₁ n₂ Vd Rd Kp w).thread.opened b →

        (lettersLastKey Xs Nr Pl K ℓ Nm Mg₀ m₁ ML ends wit table n₁ n₂ Vd Rd Kp w).thread.means v i a y u →

        (lettersLastKey Xs Nr Pl K ℓ Nm Mg₀ m₁ ML ends wit table n₁ n₂ Vd Rd Kp w).thread.means v i a y' u) :
    RidesPast
      (lettersLastKey Xs Nr Pl K ℓ Nm Mg₀ m₁ ML ends wit table n₁ n₂ Vd Rd Kp w).thread b := by
  intro k s m E s' ps i v _ hk hi _ _ hu
  have hk' := hk q hq
  have hk'' : Kp q s s' := by
    have e : kpSecond (thirdPar Xs.chains) Kp q s s' = Kp q s s' := if_neg hq0
    exact e ▸ hk'
  obtain rfl := hE s s' hk''
  exact hY _ _ _ _ _ _ hi hu

/-- **The tests with code.** -/
theorem fits_last_key (hp : (descriptionFromSource Xs Nr Pl).planOk = true) :
    (lettersLastKey Xs Nr Pl K ℓ Nm Mg₀ m₁ ML ends wit table n₁ n₂ Vd Rd Kp w).thread.fits 4 = true := by
  have ha :
    (lettersLastKey Xs Nr Pl K ℓ Nm Mg₀ m₁ ML ends wit table n₁ n₂ Vd Rd Kp w).thread.ahead =
      decl₁ (descriptionFromSource Xs Nr Pl) ++ decl₂ (descriptionFromSource Xs Nr Pl) := by
    show declsTo (descriptionFromSource Xs Nr Pl).first.blocksInOrder (descriptionFromSource Xs Nr Pl).first.blocksInOrder.length ++
      declsTo (descriptionFromSource Xs Nr Pl).shared.blocksInOrder (descriptionFromSource Xs Nr Pl).shared.blocksInOrder.length = _
    unfold declsTo
    rw [List.take_length, List.take_length]
  have hn :
    (lettersLastKey Xs Nr Pl K ℓ Nm Mg₀ m₁ ML ends wit table n₁ n₂ Vd Rd Kp w).thread.near = (decl₁ (descriptionFromSource Xs Nr Pl)).length := by
    show (declsTo (descriptionFromSource Xs Nr Pl).first.blocksInOrder (descriptionFromSource Xs Nr Pl).first.blocksInOrder.length).length = _
    unfold declsTo
    rw [List.take_length]
  have hf :
    (lettersLastKey Xs Nr Pl K ℓ Nm Mg₀ m₁ ML ends wit table n₁ n₂ Vd Rd Kp w).thread.front =
      (decl₁ (descriptionFromSource Xs Nr Pl) ++ decl₂ (descriptionFromSource Xs Nr Pl)).length := by
    show
      (lettersLastKey Xs Nr Pl K ℓ Nm Mg₀ m₁ ML ends wit table n₁ n₂ Vd Rd Kp w).thread.ahead.length = _
    rw [ha]
  refine fits_of _ 4 (by decide : fwdFit startLast LastRows.rows 4 = true)
    (fun x hx => lists_of_shaped ((planOk_all hp).2.2 x hx).2) (AtPublicFiles.KeyThread.takenIn_taken _) ?_ ?_ ?_
  · intro σ hσ
    obtain ⟨c, m, rfl⟩ := AtPublicFiles.KeyThread.takenIn_taken _ σ hσ
    rw [hf]
    show (if c == 0 then AtPublicFiles.KeyThread.sentIn (decl₁ (descriptionFromSource Xs Nr Pl)) m else
      (decl₁ (descriptionFromSource Xs Nr Pl)).length + AtPublicFiles.KeyThread.sentIn (decl₂ (descriptionFromSource Xs Nr Pl)) m) ≤ _
    rw [List.length_append]
    have a := AtPublicFiles.KeyThread.sentIn_le (decl₁ (descriptionFromSource Xs Nr Pl)) m
    have b := AtPublicFiles.KeyThread.sentIn_le (decl₂ (descriptionFromSource Xs Nr Pl)) m
    split <;> omega
  · intro j
    rw [hf]
    show ((decl₁ (descriptionFromSource Xs Nr Pl)).length + (decl₂ (descriptionFromSource Xs Nr Pl)).length) +
        AtPublicFiles.KeyThread.sentIn (decl₃ (descriptionFromSource Xs Nr Pl)) j = _ + AtPublicFiles.KeyThread.sentIn (decl₃ (descriptionFromSource Xs Nr Pl)) j
    rw [List.length_append]
  · rw [hn, hf, List.length_append]
    exact Nat.le_add_right _ _

end

end AtPublicFiles.KeyLastQuiet

#print axioms AtPublicFiles.KeyLastQuiet.quiet_form
#print axioms AtPublicFiles.KeyLastQuiet.behind_of_form
#print axioms AtPublicFiles.KeyLastQuiet.sources_key
#print axioms AtPublicFiles.KeyLastQuiet.end_key
#print axioms AtPublicFiles.KeyLastQuiet.keeps_self
#print axioms AtPublicFiles.KeyLastQuiet.form_sources
#print axioms AtPublicFiles.KeyLastQuiet.form_end
#print axioms AtPublicFiles.KeyLastQuiet.behind_sources
#print axioms AtPublicFiles.KeyLastQuiet.behind_end
#print axioms AtPublicFiles.KeyLastQuiet.behind_first
#print axioms AtPublicFiles.KeyLastQuiet.behind_sources_side
#print axioms AtPublicFiles.KeyLastQuiet.behind_end_side
#print axioms AtPublicFiles.KeyLastQuiet.behind_first_side
#print axioms AtPublicFiles.KeyLastQuiet.owes_sources
#print axioms AtPublicFiles.KeyLastQuiet.owes_end
#print axioms AtPublicFiles.KeyLastQuiet.ridesPast_quiet
#print axioms AtPublicFiles.KeyLastQuiet.fits_last_key
