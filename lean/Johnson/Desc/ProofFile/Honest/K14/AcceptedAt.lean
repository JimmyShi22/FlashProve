-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/AcceptedAt.lean: kind K14: ACCEPTED (Honest/Thread/Pays.lean) AT
THE EIGHT MEMBERS OF THE LINEAR CLAIM's SHARED ROUNDS, WITH THE THREAD T A VARIABLE, AT EVERY FALL.
The sentence names no item: so it is stated at every thread over the kind's type of states. The
facts that the proofs spend of a thread's fields are named premises.

  fits_like, want_like   the step's own tests on rounds and columns, and the list of the columns
                  that it reads, hang on a sub-protocol's declared rounds alone
  ChainAt T Q c key   **two facts**: T.bs begins with the shared chain's front sub-protocol and the
                  kind's eight (FlatAt, Johnson/Desc/K14/Honest/FlatSteps.lean) · where the chain
                  has begun, the verifier's state is the kind's first state at the input's key.
                  key: the reader of the committed table's key off the thread's input
  acceptedAt1, …, acceptedAt8   Accepted T fall b, from Plan2, ChainAt and FitsAt T b; at the member
                  3 also: a valid input's key has sizes that fit, and no seed of it has the factor 0
  rejects_at      where a seed of the key that the state holds has the factor 0, the step of
                  WHATEVER STANDS AT THE NUMBER 3 OF THE THREAD's LIST does not return
  key_at3, rejects_input   in front of that member the state holds the INPUT's key: so at a stand
                  whose input's key has such a seed the step does not return: the premise on a valid
                  input's seeds is not idle
  accepted_at     **Accepted T fall b at each b, 1 ≤ b ≤ 8, at every fall**, with FitsAt shown from
                  AtEight and the sendings' halves (eight_Fits, Honest/K14/PaidAll.lean); the two
                  premises on a valid input's key are asked at b = 3 alone

THE KIND HAS NO FALL. THE EIGHT SUB-PROTOCOLS TEST NO VALUE THAT THE PROVER SENDS IN THE RUN. Of the
verifier's own sampled values the step's tests on rounds ask that no sampled seed of a sending has
the factor 0 and that every location lies below the table's length: lists that a round cannot sample
are shut out by a premise of Accepted itself (drawsFit). Their one test on a value that is no
challenge reads the seeds in the key of the committed table, which is a part of the input and which
the state holds from the chain's start: a sentence on the input (Honest/K14/KeySeeds.lean), taken as
a premise on valid inputs. So Accepted is the light one of the sentences that a thread asks at these
members: its half on the decide functions follows from the run in front; its half on the step's own
tests on rounds and columns is FitsAt.

What is not claimed. That the premises hold at the shared chain's thread of the IOP as written in
Lean. That the thread's sentence in front holds at any stand. Nothing on soundness or on hiding.
-/
import Johnson.Desc.ProofFile.Honest.K14.Exchange2
import Johnson.Desc.ProofFile.Honest.K14.PaidAll
import Johnson.Desc.ProofFile.Honest.K14.KeySeeds
import Johnson.Desc.K14.Honest.StepsOn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes OnBytes.Params
open VerifiableInference.Desc (Block OpenedColumn)
open VerifiableInference.Desc.Own (keyFits allZero)
open Desc.K14 (P14 St first)
open Desc.K14.Honest

variable {Bk : ProverCoinCounts} {Cl V W X Pb : Type} {Q : P14} {sentU : Array OracleNotice} {layO : TreeLay}

/-! ## Small ones -/

/-- The step's own tests on rounds and columns read of a sub-protocol its declared rounds alone. -/
theorem fits_like {Cl : Type} {x : Block St Cl} {b : Block St Unit} (h : Like x b) {ft : Nat}
    {rs : List Fmt.RoundView} {cols : List OpenedColumn} (hx : x.Fits ft rs cols) : b.Fits ft rs cols := by
  unfold Block.Fits Block.want at hx ⊢
  rw [h.rounds] at hx
  exact hx

/-- So does the list of the columns that it reads. -/
theorem want_like {Cl : Type} {x : Block St Cl} {b : Block St Unit} (h : Like x b) (ft : Nat)
    (rs : List Fmt.RoundView) : x.want ft rs = b.want ft rs := by
  unfold Block.want
  rw [h.rounds]

/-- **The two facts on a thread's fields that Accepted at the eight members spends.** -/
structure ChainAt (T : Thread Bk St Cl V W X Pb) (Q : P14) (c : Model.Verify.Chains)
    (key : W → TableKey) : Prop where
  bs : ∀ B : Eight Q, FlatAt T.bs c B
  begun : ∀ k w h s₀, T.begun k w h s₀ → s₀ = first Q.codes (key w)

variable {T : Thread Bk St Cl V W X Pb} {c : Model.Verify.Chains} {key : W → TableKey}
  {fall : Nat → St → List Fmt.Drawn → Option String}

/-! ## Accepted, member by member -/

/-- **«Accepted» at "LIN point"**: from the thread in front, and: what was played and read passes
the step's own tests on rounds and columns (FitsAt). Nothing is asked of a sent value beyond its
form. -/
theorem acceptedAt1 (hQ : Plan2 Q sentU layO) (hT : ChainAt T Q c key)
    (hF : FitsAt T 1) :
    Accepted T fall 1 := by
  obtain ⟨B⟩ := hQ.eight
  intro blk hblk k s m E ds y cols hA hd _ _ hMv
  obtain ⟨-, -, -, -, hM, -, -⟩ := hA
  obtain ⟨-, -, -, -, s₀, c₀, hbeg, -, hfold⟩ := hM
  obtain rfl : s₀ = first Q.codes (key m.st.input) := hT.begun _ _ _ _ hbeg
  have F := hT.bs B
  have hl := F.at1 hblk
  have hfit := hF blk hblk k m E ds y cols hd hMv
  have hfit' : B.b1.Fits T.ft (roundsOf y.1) cols := fits_like hl hfit
  obtain ⟨rfl, -, -⟩ := FlatAt.start (B := B) F T.ft _ s _ [] c₀ [] hfold
  have S := hQ.pub (key m.st.input)
  obtain ⟨s', hs⟩ := S.on1 B T.ft _ cols hfit'
  have hMv' := hMv
  obtain ⟨⟨l, -, hy⟩, hc⟩ := hMv'
  have hw := want_length (blk := blk) (rs := roundsOf y.1)
    (yields_drawn _ _ _ _ (play_yields _ _ _ _ _ hy)) hc
  refine ⟨s', hMv, ?_⟩
  rw [hl.step, ← hw, want_like hl]
  exact hs

/-- **«Accepted» at the sending of o_u**: from the thread in front, and: what was played and read
passes the step's own tests on rounds and columns (FitsAt). Nothing is asked of a sent value beyond
its form. -/
theorem acceptedAt2 (hQ : Plan2 Q sentU layO) (hT : ChainAt T Q c key)
    (hF : FitsAt T 2) :
    Accepted T fall 2 := by
  obtain ⟨B⟩ := hQ.eight
  intro blk hblk k s m E ds y cols hA hd _ _ hMv
  obtain ⟨-, -, -, -, hM, -, -⟩ := hA
  obtain ⟨-, -, -, -, s₀, c₀, hbeg, -, hfold⟩ := hM
  obtain rfl : s₀ = first Q.codes (key m.st.input) := hT.begun _ _ _ _ hbeg
  have F := hT.bs B
  have hl := F.at2 hblk
  have hfit := hF blk hblk k m E ds y cols hd hMv
  have hfit' : B.b2.Fits T.ft (roundsOf y.1) cols := fits_like hl hfit
  obtain ⟨W, D, -, -, rfl, u⟩ := FlatAt.stepTo1 (B := B) F hQ.facts.goes T.ft _ s _ [] c₀ [] hfold
  have S := hQ.pub (key m.st.input)
  obtain ⟨s', hs⟩ := S.on2 u _ cols hfit'
  have hMv' := hMv
  obtain ⟨⟨l, -, hy⟩, hc⟩ := hMv'
  have hw := want_length (blk := blk) (rs := roundsOf y.1)
    (yields_drawn _ _ _ _ (play_yields _ _ _ _ _ hy)) hc
  refine ⟨s', hMv, ?_⟩
  rw [hl.step, ← hw, want_like hl]
  exact hs

/-- **«Accepted» at "(rec_gamma)"**, where a valid input's key has sizes that fit and no seed of it
has the factor 0: from the thread in front, and: what was played and read passes the step's own
tests on rounds and columns (FitsAt). Nothing is asked of a sent value beyond its form. -/
theorem acceptedAt3 (hQ : Plan2 Q sentU layO) (hT : ChainAt T Q c key)
    (hkey : ∀ w, T.valid w → keyFits (key w) Q.par.S.fold.index = true)
    (hseeds : ∀ w, T.valid w → noZeroFactor (key w) = true)
    (hF : FitsAt T 3) :
    Accepted T fall 3 := by
  obtain ⟨B⟩ := hQ.eight
  intro blk hblk k s m E ds y cols hA hd _ _ hMv
  obtain ⟨-, -, -, -, hM, -, hV⟩ := hA
  obtain ⟨-, -, -, -, s₀, c₀, hbeg, -, hfold⟩ := hM
  obtain rfl : s₀ = first Q.codes (key m.st.input) := hT.begun _ _ _ _ hbeg
  have F := hT.bs B
  have hl := F.at3 hblk
  have hfit := hF blk hblk k m E ds y cols hd hMv
  have hfit' : B.b3.Fits T.ft (roundsOf y.1) cols := fits_like hl hfit
  obtain ⟨W, D, -, -, rfl, u⟩ := FlatAt.stepTo2 (B := B) F hQ.facts.goes T.ft _ s _ [] c₀ [] hfold
  have S := hQ.pub (key m.st.input)
  have hb3 : ((key m.st.input).seeds.all (!allZero ·.beta)) = true := hseeds _ hV
  obtain ⟨s', hs⟩ := S.on3 u (hkey _ hV) hb3 _ cols hfit'
  have hMv' := hMv
  obtain ⟨⟨l, -, hy⟩, hc⟩ := hMv'
  have hw := want_length (blk := blk) (rs := roundsOf y.1)
    (yields_drawn _ _ _ _ (play_yields _ _ _ _ _ hy)) hc
  refine ⟨s', hMv, ?_⟩
  rw [hl.step, ← hw, want_like hl]
  exact hs

/-- **«Accepted» at "LOC"**: from the thread in front, and: what was played and read passes the
step's own tests on rounds and columns (FitsAt). Of a sent value nothing is asked beyond its
form. -/
theorem acceptedAt4 (hQ : Plan2 Q sentU layO) (hT : ChainAt T Q c key)
    (hF : FitsAt T 4) :
    Accepted T fall 4 := by
  obtain ⟨B⟩ := hQ.eight
  intro blk hblk k s m E ds y cols hA hd _ _ hMv
  obtain ⟨-, -, -, -, hM, -, -⟩ := hA
  obtain ⟨-, -, -, -, s₀, c₀, hbeg, -, hfold⟩ := hM
  obtain rfl : s₀ = first Q.codes (key m.st.input) := hT.begun _ _ _ _ hbeg
  have F := hT.bs B
  have hl := F.at4 hblk
  have hfit := hF blk hblk k m E ds y cols hd hMv
  have hfit' : B.b4.Fits T.ft (roundsOf y.1) cols := fits_like hl hfit
  obtain ⟨W, D, -, -, rfl, u⟩ := FlatAt.stepTo3 (B := B) F hQ.facts.goes T.ft _ s _ [] c₀ [] hfold
  have S := hQ.pub (key m.st.input)
  obtain ⟨s', hs⟩ := S.on4 u _ cols hfit'
  have hMv' := hMv
  obtain ⟨⟨l, -, hy⟩, hc⟩ := hMv'
  have hw := want_length (blk := blk) (rs := roundsOf y.1)
    (yields_drawn _ _ _ _ (play_yields _ _ _ _ _ hy)) hc
  refine ⟨s', hMv, ?_⟩
  rw [hl.step, ← hw, want_like hl]
  exact hs

/-- **«Accepted» at the sending of o_omega and o_sp**: from the thread in front, and: what was
played and read passes the step's own tests on rounds and columns (FitsAt). Nothing is asked of a
value sent. -/
theorem acceptedAt5 (hQ : Plan2 Q sentU layO) (hT : ChainAt T Q c key)
    (hF : FitsAt T 5) :
    Accepted T fall 5 := by
  obtain ⟨B⟩ := hQ.eight
  intro blk hblk k s m E ds y cols hA hd _ _ hMv
  obtain ⟨-, -, -, -, hM, -, -⟩ := hA
  obtain ⟨-, -, -, -, s₀, c₀, hbeg, -, hfold⟩ := hM
  obtain rfl : s₀ = first Q.codes (key m.st.input) := hT.begun _ _ _ _ hbeg
  have F := hT.bs B
  have hl := F.at5 hblk
  have hfit := hF blk hblk k m E ds y cols hd hMv
  have hfit' : B.b5.Fits T.ft (roundsOf y.1) cols := fits_like hl hfit
  obtain ⟨W, D, -, -, rfl, u⟩ := FlatAt.stepTo4 (B := B) F hQ.facts.goes T.ft _ s _ [] c₀ [] hfold
  have S := hQ.pub (key m.st.input)
  obtain ⟨s', hs⟩ := S.on5 u _ cols hfit'
  have hMv' := hMv
  obtain ⟨⟨l, -, hy⟩, hc⟩ := hMv'
  have hw := want_length (blk := blk) (rs := roundsOf y.1)
    (yields_drawn _ _ _ _ (play_yields _ _ _ _ _ hy)) hc
  refine ⟨s', hMv, ?_⟩
  rw [hl.step, ← hw, want_like hl]
  exact hs

/-- **«Accepted» at the joinings**: from the thread in front, and: what was played and read passes
the step's own tests on rounds and columns (FitsAt). Nothing is asked of a sent value beyond its
form. -/
theorem acceptedAt6 (hQ : Plan2 Q sentU layO) (hT : ChainAt T Q c key)
    (hF : FitsAt T 6) :
    Accepted T fall 6 := by
  obtain ⟨B⟩ := hQ.eight
  intro blk hblk k s m E ds y cols hA hd _ _ hMv
  obtain ⟨-, -, -, -, hM, -, -⟩ := hA
  obtain ⟨-, -, -, -, s₀, c₀, hbeg, -, hfold⟩ := hM
  obtain rfl : s₀ = first Q.codes (key m.st.input) := hT.begun _ _ _ _ hbeg
  have F := hT.bs B
  have hl := F.at6 hblk
  have hfit := hF blk hblk k m E ds y cols hd hMv
  have hfit' : B.b6.Fits T.ft (roundsOf y.1) cols := fits_like hl hfit
  obtain ⟨W, D, -, -, rfl, u⟩ := FlatAt.stepTo5 (B := B) F hQ.facts.goes T.ft _ s _ [] c₀ [] hfold
  have S := hQ.pub (key m.st.input)
  obtain ⟨s', hs⟩ := S.on6 u _ cols hfit'
  have hMv' := hMv
  obtain ⟨⟨l, -, hy⟩, hc⟩ := hMv'
  have hw := want_length (blk := blk) (rs := roundsOf y.1)
    (yields_drawn _ _ _ _ (play_yields _ _ _ _ _ hy)) hc
  refine ⟨s', hMv, ?_⟩
  rw [hl.step, ← hw, want_like hl]
  exact hs

/-- **«Accepted» at "LIN zeta"**: what was played and read passes the step's own tests on rounds and
columns (FitsAt). Of the thread in front nothing is spent: this step returns at any state. -/
theorem acceptedAt7 (hQ : Plan2 Q sentU layO) (hT : ChainAt T Q c key)
    (hF : FitsAt T 7) :
    Accepted T fall 7 := by
  obtain ⟨B⟩ := hQ.eight
  intro blk hblk k s m E ds y cols hA hd _ _ hMv
  obtain ⟨-, -, -, -, hM, -, -⟩ := hA
  obtain ⟨-, -, -, -, s₀, c₀, hbeg, -, hfold⟩ := hM
  obtain rfl : s₀ = first Q.codes (key m.st.input) := hT.begun _ _ _ _ hbeg
  have F := hT.bs B
  have hl := F.at7 hblk
  have hfit := hF blk hblk k m E ds y cols hd hMv
  have hfit' : B.b7.Fits T.ft (roundsOf y.1) cols := fits_like hl hfit
  obtain ⟨W, D, -, -, rfl, u⟩ := FlatAt.stepTo6 (B := B) F hQ.facts.goes T.ft _ s _ [] c₀ [] hfold
  have S := hQ.pub (key m.st.input)
  obtain ⟨s', hs⟩ := B.on7 hQ.facts.goes T.ft _ _ cols hfit'
  have hMv' := hMv
  obtain ⟨⟨l, -, hy⟩, hc⟩ := hMv'
  have hw := want_length (blk := blk) (rs := roundsOf y.1)
    (yields_drawn _ _ _ _ (play_yields _ _ _ _ _ hy)) hc
  refine ⟨s', hMv, ?_⟩
  rw [hl.step, ← hw, want_like hl]
  exact hs

/-- **«Accepted» at "SPLIT"**: from the thread in front, and: what was played and read passes the
step's own tests on rounds and columns (FitsAt). Of a sent value nothing is asked beyond its
form. -/
theorem acceptedAt8 (hQ : Plan2 Q sentU layO) (hT : ChainAt T Q c key)
    (hF : FitsAt T 8) :
    Accepted T fall 8 := by
  obtain ⟨B⟩ := hQ.eight
  intro blk hblk k s m E ds y cols hA hd _ _ hMv
  obtain ⟨-, -, -, -, hM, -, -⟩ := hA
  obtain ⟨-, -, -, -, s₀, c₀, hbeg, -, hfold⟩ := hM
  obtain rfl : s₀ = first Q.codes (key m.st.input) := hT.begun _ _ _ _ hbeg
  have F := hT.bs B
  have hl := F.at8 hblk
  have hfit := hF blk hblk k m E ds y cols hd hMv
  have hfit' : B.b8.Fits T.ft (roundsOf y.1) cols := fits_like hl hfit
  obtain ⟨W, D, -, -, rfl, u⟩ := FlatAt.stepTo7 (B := B) F hQ.facts.goes T.ft _ s _ [] c₀ [] hfold
  have S := hQ.pub (key m.st.input)
  obtain ⟨s', hs⟩ := S.on8 u _ cols hfit'
  have hMv' := hMv
  obtain ⟨⟨l, -, hy⟩, hc⟩ := hMv'
  have hw := want_length (blk := blk) (rs := roundsOf y.1)
    (yields_drawn _ _ _ _ (play_yields _ _ _ _ _ hy)) hc
  refine ⟨s', hMv, ?_⟩
  rw [hl.step, ← hw, want_like hl]
  exact hs

/-! ## The test on the seeds at the thread's own member; all eight -/

/-- **Where a seed of the key that the state holds has the factor 0, the step of whatever stands at
the number 3 of the thread's list does not return.** -/
theorem rejects_at (hQ : Plan2 Q sentU layO) (hT : ChainAt T Q c key) (blk : Block St Cl)
    (hblk : T.bs[3]? = some blk) (ft : Nat) (d d' : St) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
    (n : Nat) (h : noZeroFactor d.loc.key = false) : blk.step ft d rs cols ≠ .ok (d', n) := by
  obtain ⟨B⟩ := hQ.eight
  rw [((hT.bs B).at3 hblk).step]
  exact seeds_reject hQ.facts.goes B ft d d' rs cols n h

/-- **In front of the member number 3 the state holds the input's key.** -/
theorem key_at3 (hQ : Plan2 Q sentU layO) (hT : ChainAt T Q c key) {k : Coins Bk} {s : St}
    {m : Mid W X} {E : Env} (hA : Thr T 3 k s m E) : s.loc.key = key m.st.input := by
  obtain ⟨B⟩ := hQ.eight
  obtain ⟨-, -, -, -, hM, -, -⟩ := hA
  obtain ⟨-, -, -, -, s₀, c₀, hbeg, -, hfold⟩ := hM
  obtain rfl : s₀ = first Q.codes (key m.st.input) := hT.begun _ _ _ _ hbeg
  obtain ⟨W, D, -, -, rfl, u⟩ :=
    FlatAt.stepTo2 (B := B) (hT.bs B) hQ.facts.goes T.ft _ s _ [] c₀ [] hfold
  have S := hQ.pub (key m.st.input)
  obtain ⟨x, ids, t⟩ := S.to2 u
  exact (S.at2 t).carried.key

/-- **So the premise on a valid input's seeds is not idle**: at a stand of the thread in front of
the member number 3 whose INPUT's key has a seed with the factor 0, that member's step does not
return. -/
theorem rejects_input (hQ : Plan2 Q sentU layO) (hT : ChainAt T Q c key) (blk : Block St Cl)
    (hblk : T.bs[3]? = some blk) {k : Coins Bk} {s : St} {m : Mid W X} {E : Env}
    (hA : Thr T 3 k s m E) (h : noZeroFactor (key m.st.input) = false) (ft : Nat) (d' : St)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (n : Nat) : blk.step ft s rs cols ≠ .ok (d', n) :=
  rejects_at hQ hT blk hblk ft s d' rs cols n (by rw [key_at3 hQ hT hA]; exact h)

variable {W₀ Rc : Type} {T' : Thread Bk St Cl Empty (Common W₀ Rc TableKey) X Pb} {A : Data}
  {weights : W₀ → Weights} {rand : Rc → TableRand}

/-- **Accepted at each of the eight members, at every fall**, the thread a variable. -/
theorem accepted_at (hQ : Plan2 Q sentU layO) (hT : ChainAt T' Q c fun w => w.key)
    (hE : AtEight T' 1 Q A weights)
    (hh : ∀ g ∈ (proverSidesOfSharedSendings ⟨Q, A.atPoint⟩ weights rand :
      List (Placed Empty (Common W₀ Rc TableKey) X)), g ∈ T'.hs)
    (fall : Nat → St → List Fmt.Drawn → Option String) (b : Nat) (h1 : 1 ≤ b) (h8 : b ≤ 8)
    (hkey : b = 3 → ∀ w, T'.valid w → keyFits w.key Q.par.S.fold.index = true)
    (hseeds : b = 3 → ∀ w, T'.valid w → noZeroFactor w.key = true) : Accepted T' fall b := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8⟩ := eight_Fits (b0 := 1) hE hh
  match b, h1, h8, hkey, hseeds with
  | 1, _, _, _, _ => exact acceptedAt1 hQ hT f1
  | 2, _, _, _, _ => exact acceptedAt2 hQ hT f2
  | 3, _, _, hk, hs => exact acceptedAt3 hQ hT (hk rfl) (hs rfl) f3
  | 4, _, _, _, _ => exact acceptedAt4 hQ hT f4
  | 5, _, _, _, _ => exact acceptedAt5 hQ hT f5
  | 6, _, _, _, _ => exact acceptedAt6 hQ hT f6
  | 7, _, _, _, _ => exact acceptedAt7 hQ hT f7
  | 8, _, _, _, _ => exact acceptedAt8 hQ hT f8

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.fits_like
#print axioms ProofFile.Honest.K14.want_like
#print axioms ProofFile.Honest.K14.rejects_at
#print axioms ProofFile.Honest.K14.key_at3
#print axioms ProofFile.Honest.K14.rejects_input
#print axioms ProofFile.Honest.K14.accepted_at
#print axioms ProofFile.Honest.K14.acceptedAt1
#print axioms ProofFile.Honest.K14.acceptedAt2
#print axioms ProofFile.Honest.K14.acceptedAt3
#print axioms ProofFile.Honest.K14.acceptedAt4
#print axioms ProofFile.Honest.K14.acceptedAt5
#print axioms ProofFile.Honest.K14.acceptedAt6
#print axioms ProofFile.Honest.K14.acceptedAt7
#print axioms ProofFile.Honest.K14.acceptedAt8
