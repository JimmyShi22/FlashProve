-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtProof/WordsTiedW.lean: WordsTied (K12/SaysOfMet.lean) at a test
whose group has three members, two messages of kind K1 and one of a shared chain's sending, as the
last chain's test has: from one equation on the witness's words.

  WordsAreSent    THE EQUATION: on the three members' tables the words are those of the senders'
                  rows: what the thread's witness has to be there
  begun_oracle, table_begun   the test's beginning keeps the shapes and the tables' sizes
  words_tied_three   WordsTied, from the equation

By what. wordsAt_memK1 (WordsOfK1.lean), wordsAt_member (K12/WordsOfMember.lean).

Limits.
- The equation is a premise: that the witness of a thread at the last chain meets it is the letter's
  who lays that witness: a term for the thread's wit is what it asks.
- R₀, R₁ are the rows at the member's stretch and front: wMember_rows and members_held make them the
  sender's at its own coins.
- hn₀, hn₁, hn₂, finds, shapes, codes are public facts of the job and the statement.
- Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtProof.WordsOfK1
import Johnson.Desc.ProofFile.Honest.K12.SaysOfMet
import Johnson.Desc.First.Close.Law.BatOwn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof
open OnBytes (Statement Group GroupLayout Oracle OracleShape)
open OnBytes.Slice (GE rdE begun)
open OnBytes.Means (Words tableSize)
open ProofFile.Honest (Addr Front State)
open ProofFile.Honest.K12 (TestCoins)
open ProofFile.Honest.K14 (Ask sendingsFit)
open ProofFile.Honest.K12.Light (ManyJob plainMany WordsTied memOfSending SameCut vecAt)
open Johnson.Prover.Send (shapeAt)

variable {W X : Type}

/-- **The test's beginning keeps the shapes.** -/
theorem begun_oracle (S : Statement) (g : Nat) (G : Group) (o : Nat) (s : OracleShape)
    (h : (S.oracles[o]?).map (·.shape) = some s) :
    ∃ y, (begun S g G).oracles[o]? = some y ∧ y.shape = s := by
  have e := (OnBytes.Slice.begun_shape S g G o).trans h
  obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 e
  exact ⟨y, hy, rfl⟩

/-- **The test's beginning keeps the tables' sizes.** -/
theorem table_begun (S : Statement) (g : Nat) (G : Group) (o : Nat) (pt : OnBytes.Part) :
    tableSize (begun S g G) o pt = tableSize S o pt := by
  unfold tableSize OnBytes.Statement.tableBits
  rw [OnBytes.LayLaw.begun_has, OnBytes.Slice.begun_rowBits, OnBytes.LayLaw.begun_placeBits]

/-- **THE EQUATION**: on the three members' tables the words are those of the senders' rows. -/
structure WordsAreSent (S : Statement) (m : Words GE) (o₀ o₁ o₂ : Nat) (R₀ R₁ : Johnson.Prover.Send.Rows)
    (s₀ s₁ : OracleShape) (J : ProofFile.Honest.K14.SendJob) (t : State Ask Unit)
    (cs : Array OnBytes.E) (k : Nat) : Prop where
  first : ∀ pt, ∀ i < tableSize S o₀ pt, m o₀ pt i = R₀.word s₀ pt i
  second : ∀ pt, ∀ i < tableSize S o₁ pt, m o₁ pt i = R₁.word s₁ pt i
  third : ∀ pt, ∀ i < tableSize S o₂ pt,
    m o₂ pt i = rdE.val (ProofFile.Honest.K14.wordsOf J.Q.sent (J.rows t cs) k pt i)

/-- **WordsTied at a group of three members, from the equation.** -/
theorem words_tied_three {Wd₀ Wd₁ : Type} (A : ManyJob W X) (w : W) (fr : Front X) (C : TestCoins)
    (J₀ : K1.SendJob Wd₀ X) (J₁ : K1.SendJob Wd₁ X) (l₀ : W → Wd₀) (l₁ : W → Wd₁) (a₀ a₁ a₂ : Addr)
    (k₀ k₁ : Nat) (f₀ f₁ f₂ : Option Nat × Option Nat)
    (hn₀ : A.mems[0]? = some (memK1 J₀ l₀ a₀ k₀ f₀))
    (hn₁ : A.mems[1]? = some (memK1 J₁ l₁ a₁ k₁ f₁))
    (Q : Desc.K14.P14) (hQ : sendingsFit Q = true) (J : ProofFile.Honest.K14.SendJob)
    (hJ : J.Q = (ProofFile.Honest.K14.jobU ⟨Q, 0⟩).Q ∧ J.sort = (ProofFile.Honest.K14.jobU ⟨Q, 0⟩).sort ∨
      J.Q = (ProofFile.Honest.K14.jobOmega ⟨Q, 0⟩).Q ∧ J.sort = (ProofFile.Honest.K14.jobOmega ⟨Q, 0⟩).sort)
    (k : Nat) (hk : k < J.Q.sent.size) (high : Bool) (hs : J.sort k = .plain high)
    (ask : W → Ask) (t : State Ask Unit) (hv : vecAt J k ask none w fr = J.data t k)
    (cs : Array OnBytes.E) (hn₂ : A.mems[2]? = some (memOfSending J a₂ k f₂ ask none))
    (same : SameCut J k cs (C.mem 2))
    (S : Statement) (g : Nat) (G : Group) (Ly : GroupLayout) (o₀ o₁ o₂ : Nat)
    (hm : G.members = #[o₀, o₁, o₂])
    (hf₀ : Ly.find o₀ = some 0) (hf₁ : Ly.find o₁ = some 1) (hf₂ : Ly.find o₂ = some 2)
    (hs₀ : (S.oracles[o₀]?).map (·.shape) = some (shapeAt J₀.P k₀))
    (hs₁ : (S.oracles[o₁]?).map (·.shape) = some (shapeAt J₁.P k₁))
    (hs₂ : (S.oracles[o₂]?).map (·.shape) = some (ProofFile.Honest.K12.Light.shapeAt J k))
    (hc₀ : S.codes = J₀.P.codes) (hc₁ : S.codes = J₁.P.codes) (hc₂ : S.codes = J.Q.codes)
    (hl₀ : 0 < (shapeAt J₀.P k₀).mainRows →
      (J₀.P.codes.base.getD (shapeAt J₀.P k₀).code default).ell =
        2 ^ (J₀.P.codes.base.getD (shapeAt J₀.P k₀).code default).logEll)
    (hz₀ : 0 < (shapeAt J₀.P k₀).maskRows →
      (J₀.P.codes.mask.getD (shapeAt J₀.P k₀).maskCode default).ell =
        2 ^ (J₀.P.codes.mask.getD (shapeAt J₀.P k₀).maskCode default).logEll)
    (hl₁ : 0 < (shapeAt J₁.P k₁).mainRows →
      (J₁.P.codes.base.getD (shapeAt J₁.P k₁).code default).ell =
        2 ^ (J₁.P.codes.base.getD (shapeAt J₁.P k₁).code default).logEll)
    (hz₁ : 0 < (shapeAt J₁.P k₁).maskRows →
      (J₁.P.codes.mask.getD (shapeAt J₁.P k₁).maskCode default).ell =
        2 ^ (J₁.P.codes.mask.getD (shapeAt J₁.P k₁).maskCode default).logEll)
    (hl₂ : 0 < (ProofFile.Honest.K12.Light.shapeAt J k).mainRows →
      (J.Q.codes.base.getD (ProofFile.Honest.K12.Light.shapeAt J k).code default).ell =
        2 ^ (J.Q.codes.base.getD (ProofFile.Honest.K12.Light.shapeAt J k).code default).logEll)
    (hz₂ : 0 < (ProofFile.Honest.K12.Light.shapeAt J k).maskRows →
      (J.Q.codes.mask.getD (ProofFile.Honest.K12.Light.shapeAt J k).maskCode default).ell =
        2 ^ (J.Q.codes.mask.getD (ProofFile.Honest.K12.Light.shapeAt J k).maskCode default).logEll)
    (m : Words GE)
    (E : WordsAreSent S m o₀ o₁ o₂
      (K1.rowsR J₀.P J₀.ride (J₀.data (l₀ w) fr) (csAt _ (K1.startR J₀.P J₀.ride k₀) (C.mem 0)) k₀)
      (K1.rowsR J₁.P J₁.ride (J₁.data (l₁ w) fr) (csAt _ (K1.startR J₁.P J₁.ride k₁) (C.mem 1)) k₁)
      (shapeAt J₀.P k₀) (shapeAt J₁.P k₁) J t cs k) :
    WordsTied S g G m Ly (plainMany A w fr C) := by
  intro o ho pt i hi
  have hoo : o = o₀ ∨ o = o₁ ∨ o = o₂ := by
    rw [hm] at ho
    simpa using ho
  have hi' : ∀ o', o' = o → i < tableSize (begun S g G) o' pt := fun o' e => by
    rw [table_begun, e]
    exact hi
  rcases hoo with rfl | rfl | rfl
  · obtain ⟨y, hy, hys⟩ := begun_oracle S g G _ _ hs₀
    rw [E.first pt i hi]
    exact (wordsAt_memK1 J₀ l₀ a₀ k₀ f₀ A 0 hn₀ w fr C _ Ly _ hf₀ y hy hys
      ((OnBytes.Slice.begun_codes S g G).trans hc₀) hl₀ hz₀ pt i (hi' _ rfl)).symm
  · obtain ⟨y, hy, hys⟩ := begun_oracle S g G _ _ hs₁
    rw [E.second pt i hi]
    exact (wordsAt_memK1 J₁ l₁ a₁ k₁ f₁ A 1 hn₁ w fr C _ Ly _ hf₁ y hy hys
      ((OnBytes.Slice.begun_codes S g G).trans hc₁) hl₁ hz₁ pt i (hi' _ rfl)).symm
  · obtain ⟨y, hy, hys⟩ := begun_oracle S g G _ _ hs₂
    rw [E.third pt i hi]
    exact (ProofFile.Honest.K12.Light.wordsAt_member Q hQ J hJ k hk high hs a₂ f₂ ask none w fr t hv cs A
      2 hn₂ C same _ Ly _ hf₂ y hy hys ((OnBytes.Slice.begun_codes S g G).trans hc₂) hl₂ hz₂ pt i
      (hi' _ rfl)).symm

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.begun_oracle
#print axioms ProofFile.Honest.K12.AtProof.table_begun
#print axioms ProofFile.Honest.K12.AtProof.words_tied_three
