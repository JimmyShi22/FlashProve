-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Law/OutAtThread.lean: THE OUTPUT HEAD'S OWN ROUNDS, AT A CHAIN'S
THREAD: BEHIND THE MEMBER'S STEP, AT FITTING LISTS OF CHALLENGES AND AT EVERY CONTINUATION, K6Out
(Johnson/Desc/Kinds/Law/RowPins.lean) HOLDS AT WHAT A LAW READS OFF THE THREAD'S WITNESS.
WHAT IT IS NOT. CONDITIONAL ON THREE STRUCTURES OF PREMISES, K6Seated, K6Fronted AND K6Script, WHICH
ARE NOT SHOWN HERE OF THE IOP AS WRITTEN IN LEAN, NOR OF ANY THREAD; no member of K6Script is known.
The thread T, the sentence Said and the reader cut are variables. That the verifier accepts is a
premise (it stands in Thread.Stepped): nothing here says that it accepts. The end is the field out
of the structure K6ShareDebts (Honest/K6/Law/Share.lean): it is none of the library's goals. Nothing
on soundness, on completeness or on what a proof hides. No example.
  K6Script T Said b W wit at_ cut   SEVEN NAMED PREMISES, each stated from the pair ThrS T Said in
     front of the member. cut: what a law reads off a witness of the thread's, of the input: cells
     and a mask row. c' below: the cells so read, at a continuation. Who is meant to pay each:
       cellsTie   the prover's cells and c' AGREE ON WHAT THE HEAD'S RELATION NAMES (Law/
                  CellsAlike.lean: SameCells; the prover's first: the order in which rider_same and
                  HidesTables.same take it). NOT an equation of the two: a law's reading is cut to 0
                  outside four ranges, the prover's is not. Whoever lays the witness's first sending
                  and the reader of the trace.
       maskTie    the frame's own form (Honest/Law/Rule/TiesOn.lean: MaskTieOn), at the state's
                  ledger and all coins that the row spends (Law/Rule/Spent.lean: spentOf): the mask
                  row read off the witness, from the ledger's next number on, reads as the coins
                  that the book lends the row. Its payer there: maskTieOn_all
                  (Law/Rule/TiesAll.lean); that wants "the ledger's next number in front of this
                  member is the one that the public parameters fix", which stands as an equation in
                  what the public item left 24 says beside its test (Law/K6LeftSays.lean:
                  LeftSays.next). Not called here.
       keyTie     the verifier's letters at the state are those that the prover's small input makes
                  of what was heard, word for word: the lookups' border.
       idn        AT c': it meets the row's seventeen identities at every position, and the mean's
                  and the count's forms are 0 there: the thread's own item on the segment's
                  relation, which this member's row takes in, says it of the witness's cells.
       guests     AT THE PROVER'S CELLS (so at no continuation: it names no witness): the two guests
                  are 0 at every position's corner. The item
                  that says it of the witness's cells is shut one member in front. It is carried to
                  c' inside the law (rider_same). Who could pay it: the trace's validity. The road
                  to K6Out spends it only to make two weighted sums vanish, which an item that is
                  open here has; but the library's lemma on that road takes it point by point.
       left       what is left of K6On (Law/SeatedSays.lean: K6Left): K6FrontItems.k6Left
                  (Johnson/Desc/K6/Honest/Law/FrontItems.lean) has it of the table's promise.
       keys       the keys' sentence holds in front at c' (Law/JoinFromFront.lean:
                  KeysTrueInFront): keys_back_left (Law/KeysRoadBack.lean) has it of the item
                  worth 24 3 "keys", which the thread hands at every continuation.
     K6Left's first clause and K6Front's laid say one thing; the proof spends K6On's, made of left.
  headSpent_eq         HidesOfEight.lean's list of the row's coins is the frame's spentOf at our
                       row.
  lookHeard_of_open, fork_of_open   an opened head's link holds what the lookup left, and a ledger.
  k6_out_at_thread     THE TOP.
CALLED: OutAtRow.lean (out_at_row), Plays.lean (k6_played, k6_fits, k6_bare), Accepted.lean
(K6Fronted), K6/Honest/Law/Returns.lean (K6Front, zt_of_points), Law/K6OutAtMember.lean
(K6MemberIs.on); of the library: given_ok, rider_same, planFacts.

-/
import Mathlib
import Johnson.Desc.ProofFile.Honest.K6.Law.OutAtRow
import Johnson.Desc.ProofFile.Honest.K6.Law.Accepted
import Johnson.Desc.ProofFile.Honest.Law.Rule.TiesOn

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K6
open OnBytes (E zeroE)
open OnBytes.Model (Fork)
open VerifiableInference.Desc (Block OpenedColumn Place Claim)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Kinds (Head.Par Head.Given Head.Law.readsOf)
open VerifiableInference.Desc.Kinds.Head (parOf given seatAt)
open VerifiableInference.Desc.Kinds.Head.Law (rd workOf dataOf HonestHead K6Out K6Left HeadOpen
  Pinned KeysTrueInFront K6Front zt_of_points SameCells CornerGuests meanAt countAt)
open SumLaw (firstRun endRun)
open scoped VerifiableInference.Desc.Kinds

variable {Bk : ProverCoinCounts} {W₀ Rc Tr X Pb : Type}

/-- **THE TIES AND THE STATE IN FRONT**, each from the pair "the thread and what is said" in front
of the member number b. A definition: a premise's form. Nothing is claimed of it, and nothing shows
that it can be met. -/
structure K6Script (T : Thread Bk S Claim (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Pb)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Inst Tr) X → Prop) (b : Nat)
    (W : OnBytes.Model.Verify.Public) (wit : Local W₀ Rc Inst Tr → HeadAsk) (at_ : Place)
    (cut : Local W₀ Rc Inst Tr → T.Wt → Pinned) : Prop where
  /-- the prover's cells and the cells read off the witness agree inside the ranges -/
  cellsTie : ∀ k s m E, ThrS T Said b k s m E → ∀ ds,
    letI : Head.Given := (wit m.st.input).given (parOf W.hS (workOf W)) m.st.heard
    SameCells (wit m.st.input).cells (cut m.st.input (T.wit k m.st.input (m.st.heard ++ ds))).1
  /-- the mask row read off the witness reads as the coins that the book lends the row -/
  maskTie : MaskTieOn T (ThrS T Said b) at_ (headRow (X := X) wit (parOf W.hS (workOf W)) at_)
    (fun s => s.fork?) (fun F _ w v j => rd ((cut w v).2 (F.next + j))) rd (spentOf _)
    (fun n j => j < n)
  /-- the verifier's letters at the state are the prover's -/
  keyTie : ∀ k s m E, ThrS T Said b k s m E →
    given (parOf W.hS (workOf W)) (seatAt W.hS (Head.Law.readsOf W)) s =
      .ok ((wit m.st.input).given (parOf W.hS (workOf W)) m.st.heard)
  /-- AT THE CELLS READ OFF THE WITNESS: the row's identities, the mean's and the count's forms -/
  idn : ∀ k s m E, ThrS T Said b k s m E → ∀ ds,
    letI : Head.Given := (wit m.st.input).given (parOf W.hS (workOf W)) m.st.heard
    (dataOf (cut m.st.input (T.wit k m.st.input (m.st.heard ++ ds))).1).Holds ∧
      meanAt (cut m.st.input (T.wit k m.st.input (m.st.heard ++ ds))).1.toCells = 0 ∧
      countAt (cut m.st.input (T.wit k m.st.input (m.st.heard ++ ds))).1.toCells = 0
  /-- AT THE PROVER'S CELLS, not at those read off the witness: the two guests are 0 at every
  position's corner -/
  guests : ∀ k s m E, ThrS T Said b k s m E →
    letI : Head.Given := (wit m.st.input).given (parOf W.hS (workOf W)) m.st.heard
    CornerGuests (wit m.st.input).cells.toCells
  /-- what is left of K6On -/
  left : ∀ k s m E, ThrS T Said b k s m E → K6Left W s
  /-- the keys' sentence in front, at the cells and the mask row read off the witness -/
  keys : ∀ k s m E, ThrS T Said b k s m E → ∀ ds, KeysTrueInFront W s
    (cut m.st.input (T.wit k m.st.input (m.st.heard ++ ds))).1
    (cut m.st.input (T.wit k m.st.input (m.st.heard ++ ds))).2

/-- **The list of the row's coins is the frame's, at our row.** -/
theorem headSpent_eq (wit : Local W₀ Rc Inst Tr → HeadAsk) (p : Head.Par) (at_ : Place)
    (c : RowCoins (headRow (X := X) wit p at_)) :
    headSpent (p := p) c.2.1.2.1.1 c.2.2.1 c.2.2.2.2.1.2.1.1 c.2.2.2.2.2.1 c.2.2.2.2.2.2.1
      c.2.2.2.2.2.2.2.1 = spentOf (headRow wit p at_) c := by
  have e : spentOf (headRow wit p at_) c =
      [] ++ ((coinsE c.2.1.2.1.1 ++ []) ++ ((firstRun c.2.2.1 ++ (endRun c.2.2.1 ++ [])) ++
        ([] ++ ((coinsE c.2.2.2.2.1.2.1.1 ++ []) ++
          ((firstRun c.2.2.2.2.2.1 ++ (endRun c.2.2.2.2.2.1 ++ [])) ++
            ((firstRun c.2.2.2.2.2.2.1 ++ (endRun c.2.2.2.2.2.2.1 ++ [])) ++
              ((firstRun c.2.2.2.2.2.2.2.1 ++ (endRun c.2.2.2.2.2.2.2.1 ++ [])) ++ []))))))) := rfl
  rw [e]
  unfold headSpent
  simp only [List.nil_append, List.append_nil, List.append_assoc]

/-- An opened head's link holds what the lookup left. -/
theorem lookHeard_of_open {s : S} (h : HeadOpen s) : ∃ gk, s.lookHeard? = some gk := by
  obtain ⟨o, h1, h2, h3⟩ := h
  obtain ⟨gk, hg⟩ := Option.isSome_iff_exists.1 h3
  refine ⟨gk, ?_⟩
  unfold VerifiableInference.Desc.First.S.lookHeard?
  rw [h1]
  simp [h2, hg]

/-- An opened head's link holds a ledger. -/
theorem fork_of_open {s : S} (h : HeadOpen s) : ∃ F, s.fork? = some F := by
  obtain ⟨o, h1, h2, _⟩ := h
  refine ⟨o.F, ?_⟩
  unfold VerifiableInference.Desc.First.S.fork?
  rw [h1]
  simp [h2]

/-- **BEHIND THE MEMBER'S STEP, AT FITTING LISTS AND AT EVERY CONTINUATION, K6Out HOLDS AT WHAT THE
LAW READS OFF THE THREAD'S WITNESS.** r: how many numbers of the ledger are left free behind the
member; it reaches no conclusion: it is there so that a caller can hand K6Front's field room as it
stands. at_ is free in form alone: K6Seated's field place ties it to the member's address. -/
theorem k6_out_at_thread
    {T : Thread Bk S Claim (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Pb}
    {Said : Nat → Coins Bk → Mid (Local W₀ Rc Inst Tr) X → Prop} {b : Nat}
    {W : OnBytes.Model.Verify.Public} {wit : Local W₀ Rc Inst Tr → HeadAsk} {at_ : Place}
    {blk : Block S Claim} {r : Nat} {cut : Local W₀ Rc Inst Tr → T.Wt → Pinned}
    (Hs : K6Seated T b wit (parOf W.hS (workOf W)) at_ blk) (Hf : K6Fronted T Said b W r blk)
    (Hc : K6Script T Said b W wit at_ cut) (hpl : blk.planOk = true) :
    ∀ k s m E ds y cols s', ThrS T Said b k s m E → drawsFit blk.rounds ds = true →
      T.Stepped blk k s m E ds y cols s' → ∀ ds',
      K6Out W s' (cut m.st.input (T.wit k m.st.input (y.2.st.heard ++ ds'))) := by
  intro k s m E ds y cols s' hT hd hS ds'
  obtain ⟨hM, hstep⟩ := hS
  have hF := k6_fits T Hs blk Hs.member k m E ds y cols hd hM
  obtain ⟨⟨l, hl, hp⟩, _⟩ := hM
  have hbare := k6_bare T Hs hd hp
  obtain ⟨c, hlend, _, hplay⟩ := k6_played T Hs hd hl m
  obtain rfl := Except.ok.inj (hp.symm.trans hplay)
  have R := Hf.front k s m E hT
  obtain ⟨gk, hgk⟩ := lookHeard_of_open R.open_
  obtain ⟨F, hFk⟩ := fork_of_open R.open_
  have hled : (seatAt W.hS (Head.Law.readsOf W)).ledger s = F := by
    show s.fork?.getD {} = F
    rw [hFk]
    rfl
  have hkey := Hc.keyTie k s m E hT
  have hsame := Hc.cellsTie k s m E hT (ds ++ ds')
  obtain ⟨i1, i2, i3⟩ := Hc.idn k s m E hT (ds ++ ds')
  have hgu := Hc.guests k s m E hT
  have hOn := Hf.member.on hpl R.start (Hc.left k s m E hT)
  have hPF : letI : Head.Given := (wit m.st.input).given (parOf W.hS (workOf W)) m.st.heard
      VerifiableInference.Desc.Kinds.Head.Law.PlanFacts := by
    letI : Head.Given := (wit m.st.input).given (parOf W.hS (workOf W)) m.st.heard
    exact VerifiableInference.Desc.Kinds.Head.Law.planFacts hOn.2.1
  have hHon : letI : Head.Given := (wit m.st.input).given (parOf W.hS (workOf W)) m.st.heard
      HonestHead (cut m.st.input (T.wit k m.st.input (m.st.heard ++ (ds ++ ds')))).1.toCells := by
    letI : Head.Given := (wit m.st.input).given (parOf W.hS (workOf W)) m.st.heard
    exact ⟨VerifiableInference.Desc.Kinds.Head.Law.Came.rider_same hsame hPF hgu, i2, i3⟩
  -- zt's size, at the prover's letters, which are the verifier's
  have hzt : letI : Head.Given := (wit m.st.input).given (parOf W.hS (workOf W)) m.st.heard
      (VerifiableInference.Desc.Kinds.FinalNorm.zt).size =
        VerifiableInference.Desc.Kinds.Norm.lt := by
    obtain ⟨z, y0, hz, _, hP⟩ := R.letters
    obtain ⟨z', _, hz', _, _, e⟩ :=
      VerifiableInference.Desc.Kinds.Head.Law.Came.given_ok _ _ s _ hkey
    obtain rfl : z = z' := Option.some.inj (hz.symm.trans hz')
    have e1 := congrArg (@Head.Given.normIn) e
    show (@VerifiableInference.Desc.Kinds.FinalNorm.zt
      ((wit m.st.input).given (parOf W.hS (workOf W)) m.st.heard).normIn).size = _
    rw [e1]
    exact @zt_of_points (parOf W.hS (workOf W)).sizes _ _ _ hP
  have hd' : drawsFit (parOf W.hS (workOf W)).rounds ds = true := by
    rw [← Hs.rounds]
    exact hd
  have hMk : headTiedFrom (cut m.st.input (T.wit k m.st.input (m.st.heard ++ (ds ++ ds')))).2
      ((seatAt W.hS (Head.Law.readsOf W)).ledger s).next
      (headSpent (p := (parOf W.hS (workOf W))) c.2.1.2.1.1 c.2.2.1 c.2.2.2.2.1.2.1.1 c.2.2.2.2.2.1
        c.2.2.2.2.2.2.1 c.2.2.2.2.2.2.2.1) := by
    rw [headSpent_eq, hled]
    exact fun j hj => Hc.maskTie k s m E hT F c hFk hlend (ds ++ ds') j hj
  obtain ⟨s'', H, G, hst, _, _, hO⟩ :=
    @out_at_row _ _ _ _ ((wit m.st.input).given (parOf W.hS (workOf W)) m.st.heard) W 24 _ _ blk
      Hf.member (by decide) (fun _ _ e => P4.same_of_eq e) hpl T.ft cols wit at_ c m.st m.shown ds
      blk.name s (cut m.st.input (T.wit k m.st.input (m.st.heard ++ (ds ++ ds')))).2 r
      (cut m.st.input (T.wit k m.st.input (m.st.heard ++ (ds ++ ds')))).1 (Hc.left k s m E hT)
      R.clean R.open_ R.start rfl hkey hsame i1 hHon R.room hzt
      hd' hF.1 hbare hMk gk hgk (Hc.keys k s m E hT (ds ++ ds') gk hgk)
  obtain rfl : s' = s'' := (Prod.mk.inj (Except.ok.inj (hstep.symm.trans hst))).1
  show K6Out W s' (cut m.st.input (T.wit k m.st.input (m.st.heard ++ ds ++ ds')))
  rw [List.append_assoc]
  exact hO

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.headSpent_eq
#print axioms ProofFile.Honest.K6.lookHeard_of_open
#print axioms ProofFile.Honest.K6.fork_of_open
#print axioms ProofFile.Honest.K6.k6_out_at_thread
