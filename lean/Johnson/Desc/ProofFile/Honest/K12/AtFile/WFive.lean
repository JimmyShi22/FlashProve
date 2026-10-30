-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/WFive.lean: three of the five statements at the last chain's
proximity test, number 2 of a last chain's thread: `BehindS`, `ExchangeS`, `RidesPastS`
(Thread/PaysS.lean). `PlaysS` and `AcceptedS`: WAccepted.lean. The thread is a term of `LastThread.Letters`
whose promise `PL` is `fillAt` (Johnson/Desc/Last/ShapeAt.lean).

  `seat_yes`       a yes of the seated block is the kind's yes at the way in's state, laid back
  `lengths_of_start`, `codes_of_start`   what the start's yes says of the codes
  `shape_three`    from the book-keeping at border 2 and the block's yes, the book-keeping at border
                   3: `step_two` (Johnson/Desc/Last/ShapeGives.lean) with its four debts paid:
                   the way out keeps the named values; `k12_run_codes`; `k12_tidy`
  `tidy_behind`    behind the block the statement is tidy
  `shape_of_form`, `form_of_shape`, `seat_next`   the thread's clause (P) and the book-keeping
  `behindS_at_W`   behind the test the form holds; the letters' order, rides and keeps stay premises
  `exchangeS_at_W`   the row owes nothing
  `ridesPastS_at_W`   the row shuts all that is open

Can they be empty. `ridesPastS_at_W` and `exchangeS_at_W` say nothing by the table's text: at this row
no item rides and none is owed: that is what they state, and a table that turned would fail the
closed line inside. `behindS_at_W` has `Stepped` among its premises: where the block says no it says
nothing.

Limits.
- hPL, hnext are premises: the thread's letters. `L.order`, `L.rides`, `L.keeps` are letters.
- NOT IN FRONT OF A LAW OVER COINS: each has the thread's pair as a premise and a sentence of the frame
  as its end.
- Nothing on completeness of the whole chain, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WAccepted
import Johnson.Desc.Last.ShapeGives
import Johnson.Desc.Last.ShapeAtTable
import Johnson.Desc.K12.Coin.TidyThrough
import Johnson.Desc.K12.Law.RunCodes
import Johnson.Desc.K15.FoldInv
import Johnson.Desc.ProofFile.Honest.Thread.Last

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtFile
open ProofFile.Honest
open ProofFile.Honest.K12
open OnBytes
open VerifiableInference.Desc (Block foldBlocks step_inv)
open VerifiableInference.Desc.K12 (T12 proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc.K12.Seat (enterOwn leaveOwn)
open VerifiableInference.Desc.Third (S₃ P₁₄ SharedOut start₃E start₃)
open VerifiableInference.Desc.Third.Law (start₃E_inv start₃_inv)
open VerifiableInference.Desc.Last (shapeAt fillAt behindOk_of_two step_two lastPlaces
  shapeAt_of_fill ItemL)

variable {W X Cl : Type}

/-- **A yes of the seated block is the kind's yes at the way in's state, laid back.** -/
theorem seat_yes {J : TestJob W X} {blk : Block S₃ Cl}
    (hseat : SeatOf blk J enterOwn leaveOwn) {s s' : S₃} {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))} (hy : blk.decide s rs gs = .ok s') :
    ∃ t', (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).decide
        { st := s.st, book := s.book, roots := s.roots, g := s.loc.own, pass := .nothing
          mask := s.loc.mask } rs gs = .ok t' ∧
      s' = { s with st := t'.st, book := t'.book, roots := t'.roots } := by
  rw [hseat.decide] at hy
  have hy' : ((proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).decide
      { st := s.st, book := s.book, roots := s.roots, g := s.loc.own, pass := .nothing
        mask := s.loc.mask } rs gs).bind (leaveOwn s) = .ok s' := hy
  cases hk : (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).decide
      { st := s.st, book := s.book, roots := s.roots, g := s.loc.own, pass := .nothing
        mask := s.loc.mask } rs gs with
  | error e =>
    rw [hk] at hy'
    cases hy'
  | ok t' =>
    rw [hk] at hy'
    exact ⟨t', rfl, (Except.ok.inj hy').symm⟩

/-- The start's yes says that the codes' lengths are in order. -/
theorem lengths_of_start {codes : Codes} {S : Params.LinShape} {st₁ : Statement} {book₁ : TreeBook}
    {roots₁ w₁ own₁ : ℕ} {mask₁ : Option ℕ} {pile₁ : List TensorRow} {o : SharedOut} {s₀ : S₃}
    (h : start₃E codes S st₁ book₁ roots₁ w₁ own₁ mask₁ pile₁ o = .ok s₀) :
    codes.lengthsOk = true := by
  cases e : codes.lengthsOk with
  | true => rfl
  | false =>
    unfold start₃E at h
    simp [e] at h

/-- The start's record holds the codes that it was handed. -/
theorem codes_of_start {codes : Codes} {S : Params.LinShape} {st₁ : Statement} {book₁ : TreeBook}
    {roots₁ w₁ own₁ : ℕ} {mask₁ : Option ℕ} {pile₁ : List TensorRow} {o : SharedOut} {s₀ : S₃}
    (h : start₃E codes S st₁ book₁ roots₁ w₁ own₁ mask₁ pile₁ o = .ok s₀) :
    s₀.st.codes = codes := by
  obtain ⟨f, -, hst⟩ := start₃E_inv _ _ _ _ _ _ _ _ _ _ _ h
  obtain ⟨c1, -, e0⟩ := start₃_inv _ _ _ _ hst
  subst e0
  exact c1

/-- **From the book-keeping at border 2 and the block's yes, the book-keeping at border 3.** -/
theorem shape_three {J : TestJob W X} {blk : Block S₃ Cl} (hseat : SeatOf blk J enterOwn leaveOwn)
    (hp : (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).planOk = true) {p : P₁₄}
    {R : List Fmt.DeclaredRound} {h : VerifiableInference.Desc.Last.Handed} {o : SharedOut} {s s' : S₃}
    (hs : shapeAt p R 2 h o s = true) {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))}
    (hy : blk.decide s rs gs = .ok s') : shapeAt p R 3 h o s' = true := by
  obtain ⟨t', ht', e⟩ := seat_yes hseat hy
  obtain ⟨⟨s₀, B⟩, -⟩ := behindOk_of_two hs
  obtain ⟨b, y, G, dot, L⟩ := B.laid
  have hl : s.st.codes.lengthsOk = true := by
    rw [L.codes, codes_of_start B.start]
    exact lengths_of_start B.start
  obtain ⟨⟨G', hG', hr⟩, hc⟩ := H2K.Out.k12_run_codes J.p hp _ t' rs gs ht'
  have ht := VerifiableInference.Desc.K12.Coin.k12_tidy J.p _ t' rs gs ht' hl B.tidy
  subst e
  exact step_two hs rfl ⟨G', hG', hr⟩ hc ht

/-- **Behind the block the statement is tidy.** -/
theorem tidy_behind {J : TestJob W X} {blk : Block S₃ Cl} (hseat : SeatOf blk J enterOwn leaveOwn)
    (hp : (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).planOk = true) {p : P₁₄}
    {R : List Fmt.DeclaredRound} {h : VerifiableInference.Desc.Last.Handed} {o : SharedOut} {s s' : S₃}
    (hs : shapeAt p R 2 h o s = true) {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))}
    (hy : blk.decide s rs gs = .ok s') : OnBytes.Means.Tidy s'.st := by
  obtain ⟨t', ht', e⟩ := seat_yes hseat hy
  obtain ⟨⟨s₀, B⟩, -⟩ := behindOk_of_two hs
  obtain ⟨b, y, G, dot, L⟩ := B.laid
  have hl : s.st.codes.lengthsOk = true := by
    rw [L.codes, codes_of_start B.start]
    exact lengths_of_start B.start
  have ht := VerifiableInference.Desc.K12.Coin.k12_tidy J.p _ t' rs gs ht' hl B.tidy
  subst e
  exact ht

section
variable {Bk : ProverCoinCounts} {S₂ Cl' W₀ Rc Xi Tr P₁ Wt : Type}
  (L : ProofFile.Honest.LastThread.Letters Bk S₂ S₃ Cl' W₀ Rc Xi Tr X P₁ Wt) {p : P₁₄} {R : List Fmt.DeclaredRound}
  {hand : P₁ → Option VerifiableInference.Desc.Last.Handed} {ended : S₂ → Option SharedOut}

/-- **The clause (P) at a border is the book-keeping.** -/
theorem shape_of_form (hPL : L.PL = fillAt p R hand ended) {b : ℕ} {k : Coins Bk} {s : S₃}
    {m : Mid (Local W₀ Rc Xi Tr) X} (h : L.thread.Form b k s m) :
    ∃ f o, hand (L.thread.seat k m s).1.1 = some f ∧ ended (L.thread.seat k m s).1.2 = some o ∧
      shapeAt p R b f o s = true := by
  obtain ⟨h1, -⟩ := h
  have h2 : (L.PL.shape b (L.thread.seat k m s).1.1 (L.thread.seat k m s).1.2 s &&
      (!decide (lastPlaces.length ≤ b) || L.PL.nothingLeft s)) = true := h1
  rw [Bool.and_eq_true, hPL] at h2
  exact shapeAt_of_fill p R hand ended h2.1

/-- **The book-keeping at border 3 and the letter's order give the clause (P) there.** -/
theorem form_of_shape (hPL : L.PL = fillAt p R hand ended) {k : Coins Bk} {s : S₃}
    {m : Mid (Local W₀ Rc Xi Tr) X} {f : VerifiableInference.Desc.Last.Handed} {o : SharedOut}
    (hh : hand (L.thread.seat k m s).1.1 = some f) (he : ended (L.thread.seat k m s).1.2 = some o)
    (h3 : shapeAt p R 3 f o s = true) (ho : L.order s) : L.thread.Form 3 k s m := by
  refine ⟨?_, ho⟩
  show (L.PL.shape 3 (L.thread.seat k m s).1.1 (L.thread.seat k m s).1.2 s &&
    (!decide (lastPlaces.length ≤ 3) || L.PL.nothingLeft s)) = true
  have e : (!decide (lastPlaces.length ≤ 3)) = true := by decide
  rw [e, Bool.true_or, Bool.and_true, hPL]
  show (match hand (L.thread.seat k m s).1.1, ended (L.thread.seat k m s).1.2 with
    | some h, some o => shapeAt p R 3 h o s
    | _, _ => false) = true
  rw [hh, he]
  exact h3

/-- What a chain was handed does not turn over a sub-protocol. -/
theorem seat_next {blk : Block S₃ Cl'} {b : ℕ} {k : Coins Bk} {m : Mid (Local W₀ Rc Xi Tr) X}
    {E : Env} {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc Xi Tr) X}
    {cols : List VerifiableInference.Desc.OpenedColumn} (hfit : L.thread.Fit b m)
    (hM : L.thread.Moved blk k m E ds y cols) (s' : S₃) :
    L.thread.seat k y.2 s' = L.thread.seat k m s' := by
  obtain ⟨⟨l, -, hy⟩, -⟩ := hM
  obtain ⟨ei, -, -⟩ := play_mid _ _ _ _ _ hy
  have eh := play_heard _ _ _ _ _ hy
  have hlen := L.thread.heard_length hfit
  have hfr : L.thread.front ≤ m.st.heard.length := by
    rw [hlen]
    exact Nat.le_add_right _ _
  unfold Thread.seat
  rw [ei, eh, List.take_append_of_le_length hfr]

variable (Said : ℕ → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop)

/-- **Behind the test the form holds**, and the letters' three. -/
theorem behindS_at_W (hPL : L.PL = fillAt p R hand ended) {blk : Block S₃ Cl'}
    (hblk : L.thread.bs[2]? = some blk) (J : TestJob (Local W₀ Rc Xi Tr) X)
    (hseat : SeatOf blk J enterOwn leaveOwn)
    (hp : (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).planOk = true)
    (hnext : ∀ k s m E ds y cols s', ThrS L.thread Said 2 k s m E →
      drawsFit blk.rounds ds = true → L.thread.Stepped blk k s m E ds y cols s' →
      L.order s' ∧ L.thread.rides 3 y.2.st.input s' ∧ L.thread.keeps 2 s s') :
    BehindS L.thread Said 2 := by
  intro blk' hb k s m E ds y cols s' u hd hS
  rw [hblk] at hb
  obtain rfl := Option.some.inj hb
  obtain ⟨ho, hr, hk⟩ := hnext k s m E ds y cols s' u hd hS
  obtain ⟨⟨-, hfit, hform, -⟩, -⟩ := u
  obtain ⟨f, o, hf, hoo, h2⟩ := shape_of_form L hPL hform
  obtain ⟨-, -, -, hdec⟩ := step_inv _ _ _ _ _ _ _ hS.2
  have h3 := shape_three hseat hp h2 hdec
  have es := seat_next L hfit hS.1 s'
  refine ⟨form_of_shape L hPL (f := f) (o := o) ?_ ?_ h3 ho, hr, hk⟩
  · rw [es]
    exact hf
  · rw [es]
    exact hoo

/-- **The row of the test owes nothing.** -/
theorem exchangeS_at_W : ExchangeS L.thread Said 2 := by
  intro blk _ k s m E ds y cols s' _ _ _ ds' i hi
  have e : (L.thread.row 2).owes = [] := rfl
  rw [e] at hi
  cases hi

/-- **The row of the test shuts all that is open in front of it.** -/
theorem ridesPastS_at_W : RidesPastS L.thread Said 2 := by
  intro k s m E s' ps i v _ _ hi hs _ _
  have e : ∀ j ∈ fwdOpen VerifiableInference.Desc.Last.startLast LastRows.rows 2,
      j ∈ (LastRows.rows 2).shuts := by decide
  exact absurd (e i hi) hs

end

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.seat_yes
#print axioms ProofFile.Honest.K12.AtFile.lengths_of_start
#print axioms ProofFile.Honest.K12.AtFile.codes_of_start
#print axioms ProofFile.Honest.K12.AtFile.shape_three
#print axioms ProofFile.Honest.K12.AtFile.tidy_behind
#print axioms ProofFile.Honest.K12.AtFile.shape_of_form
#print axioms ProofFile.Honest.K12.AtFile.form_of_shape
#print axioms ProofFile.Honest.K12.AtFile.seat_next
#print axioms ProofFile.Honest.K12.AtFile.behindS_at_W
#print axioms ProofFile.Honest.K12.AtFile.exchangeS_at_W
#print axioms ProofFile.Honest.K12.AtFile.ridesPastS_at_W
