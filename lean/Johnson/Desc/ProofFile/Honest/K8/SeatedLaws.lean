-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K8/SeatedLaws.lean: THE SMALLNESS TEST AT ITS OWN MEMBER: THE PROOFS
OF THREE OF ITS DEBTS AS Johnson/Desc/ProofFile/Honest/K8/Seated.lean STATES THEM: it is accepted;
behind its yes; the exchange at the two items. Lemmas on the frame's own definitions, the library's
law of the seated block's step and the kind's own laws, general in the thread; none of the library's
goals.

  `quiet_play_inv`   where the play of a quiet part with a second stop returns, that stop was silent
                   at both askings
  `seated_moved`   AT THE SEAT, FROM THE PROVER's SIDE OF THE STEP ALONE (`Thread.Moved`): there is
                   one challenge d, which the kind's round can draw; what was played is the one
                   round in which nothing is sent; no column was read; the kind's second stop was
                   silent
  `fit_of_draw`   a challenge that the round can draw, shown with no item, passes the block's test
                   on its rounds
  `seat_next`   what was handed to the chain is unturned behind the member
  **`small_accepted`**, **`small_behind`**, **`small_exchange`**
The records' limits stand: what they name as premises is not shown at any thread. Through
Honest/K8/SeatedPlays.lean and QuietForm.lean these proofs lean on the general laws of
Johnson/Desc/ProofFile/Honest/K9/QuietMember.lean.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.SeatedPlays
import Johnson.Desc.ProofFile.Honest.K8.DrawBridgeProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Claim Place roundsFit)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K8 (Par MeansAtS Seats approximateRangeProofDrawKind atS round firstColumns
  step_seats_iff hear_mark)
open VerifiableInference.Desc.First.K8.Honest
open ProofFile.Honest.K9 (quietStop)

variable {W₀ Rc Xi Tr X Pb : Type} {Bk : ProverCoinCounts}

/-- Where the play returns, the second stop was silent at both askings. -/
theorem quiet_play_inv {V W X : Type} (hh : V → List Fmt.Drawn → List Fmt.Drawn → Option String)
    (sh : Odds) (d₀ : Fmt.DeclaredRound) (name : String) (a : Addr) (v : Option V)
    (c : (quietStop hh sh : Part V W X).Coins) (d : Fmt.Drawn) (m : Mid W X)
    (y : List Played × Mid W X)
    (h : play ((quietStop hh sh : Part V W X).steps name a [(d₀, [])] v c) [d] [] m = .ok y) :
    (v.bind fun u => hh u m.loc []) = none ∧ (v.bind fun u => hh u m.loc [d]) = none := by
  cases h0 : (v.bind fun u => hh u m.loc []) with
  | some e =>
    simp [Part.steps, quietStop, quietPart, play, Step.tell, Step.stop, Except.bind, h0] at h
  | none =>
    cases h1 : (v.bind fun u => hh u m.loc [d]) with
    | some e =>
      by_cases hf : (⟨[], []⟩ : Sending).fits d₀ [] = true <;>
        simp [Part.steps, quietStop, quietPart, play, Step.tell, Step.hear, Step.stop, Except.bind,
          h0, h1, hf] at h
    | none => exact ⟨rfl, rfl⟩

/-- **At the seat, from the prover's side of the step alone.** -/
theorem seated_moved {T : Thread Bk S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb}
    {b : Nat} {blk : Block S Claim} {cells : Tr → Cells} {P : Par × List (Nat × String × Nat)}
    (h : K8Seated T b blk cells P) {k : Coins Bk} {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc Xi Tr) X}
    {cols : List VerifiableInference.Desc.OpenedColumn} (hd : drawsFit blk.rounds ds = true)
    (hM : T.Moved blk k m E ds y cols) :
    ∃ d, ds = [d] ∧ drawFit (round P.1) d = true ∧ y = playedAt blk.name blk.place d m ∧
      cols = [] ∧ smallStop cells P m.st.input m.loc [d] = none := by
  rw [seated_rounds h] at hd
  obtain ⟨d, rfl, hdf⟩ := drawsFit_one hd
  obtain ⟨⟨l, hl, hy⟩, hc⟩ := hM
  rw [seated_rounds h, seated_cols] at hc
  obtain ⟨c, -, rfl⟩ := steps_one_half h.half hl
  have key : ∀ (ps : List (Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X)) (c : RowCoins ps),
      ps = [quietStop (smallStop cells P) (windowShare P.1)] →
      play (rowSteps blk.name blk.place (T.φ.sees m.st.input) ps 0 [(round P.1, [])] c) [d] [] m =
        .ok y →
      ((T.φ.sees m.st.input).bind fun u => smallStop cells P u m.loc []) = none ∧
        ((T.φ.sees m.st.input).bind fun u => smallStop cells P u m.loc [d]) = none := by
    intro ps c e hp
    subst e
    have e2 : rowSteps blk.name blk.place (T.φ.sees m.st.input)
        [(quietStop (smallStop cells P) (windowShare P.1) :
          Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X)] 0 [(round P.1, [])] c =
        (quietStop (smallStop cells P) (windowShare P.1) :
          Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X).steps blk.name ⟨blk.place, 0⟩
          [(round P.1, [])] (T.φ.sees m.st.input) c.1 := by
      simp [rowSteps, quietStop, quietPart]
    rw [e2] at hp
    exact quiet_play_inv _ _ _ _ _ _ _ d m y hp
  unfold Placed.steps at hy
  rw [seated_rounds h, h.oracles] at hy
  obtain ⟨h0, h1⟩ := key _ c (small_parts W₀ Rc Xi Tr X cells P h.named) hy
  have hy' := row_play (smallStop cells P) (windowShare P.1) (round P.1) (round_bare P.1).1 blk.name
    blk.place (T.φ.sees m.st.input) d m h0 h1 _ c (small_parts W₀ Rc Xi Tr X cells P h.named)
  have e1 : List.zip [round P.1] [([] : List VerifiableInference.Desc.Oracle)] =
      [(round P.1, [])] := rfl
  rw [e1] at hy
  rw [hy'] at hy
  rw [h.sees] at h1
  exact ⟨d, rfl, hdf, (Except.ok.inj hy).symm, (Except.ok.inj hc).symm, h1⟩

/-- A challenge that the round can draw, shown with no item, passes the block's test on rounds. -/
theorem fit_of_draw (p : Par) (d : Fmt.Drawn) (h : drawFit (round p) d = true) :
    roundsFit [round p] [⟨[], d⟩] = true := by
  unfold drawFit at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, -⟩, -⟩ := h
  simp only [roundsFit, Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨?_, a1⟩, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, trivial⟩
  rw [(round_bare p).1]
  rfl

/-- What was handed to the chain is unturned behind the member. -/
theorem seat_next (T : Thread Bk S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb) {b : Nat}
    (k : Coins Bk) (m : Mid (Local W₀ Rc Xi Tr) X) (hF : T.Fit b m) (name : String) (a : Place)
    (d : Fmt.Drawn) (s' : S) :
    T.seat k (playedAt name a d m).2 s' = ((T.seat k m s').1, s') := by
  have hl : T.front ≤ m.st.heard.length := by rw [T.heard_length hF]; exact Nat.le_add_right _ _
  show (T.handed k m.st.input ((m.st.heard ++ [d]).take T.front), s') = _
  rw [List.take_append_of_le_length hl]
  rfl

theorem small_accepted : Spec.small_accepted := by
  intro W₀ Rc Xi Tr X Pb Bk T b blk cells P fall h hR blk' hblk' k s m E ds y cols hT hd _ _ hM
  rw [h.here] at hblk'
  cases hblk'
  obtain ⟨d, rfl, hdf, rfl, rfl, -⟩ := seated_moved h hd hM
  obtain ⟨hfail, tl, c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ := hR _ s hT.2.2.1.1 hT.2.2.1.2
  refine ⟨s.putTl { tl with cfF := d.trits.toArray, cfFirst := firstColumns P.1 }, hM, ?_⟩
  exact (step_seats_iff P.1 blk h.seats T.ft s _ _ _ _).2
    ⟨⟨[], d⟩, rfl, fit_of_draw P.1 d hdf, ⟨tl, c1, c2, c3, c4, c5, c6, c7, c8, c9, rfl⟩, rfl, hfail⟩

theorem small_behind : Spec.small_behind := by
  intro W₀ Rc Xi Tr X Pb Bk T b blk cells P h hL blk' hblk' k s m E ds y cols s' hT hd hS
  rw [h.here] at hblk'
  cases hblk'
  obtain ⟨hM, hstep⟩ := hS
  obtain ⟨d, rfl, -, rfl, rfl, -⟩ := seated_moved h hd hM
  obtain ⟨r, -, -, hm, -, hfail⟩ := (step_seats_iff P.1 blk h.seats T.ft s s' _ _ _).1 hstep
  have hk : K8Keeps s s' := keeps_of_means hm
  have hf : s'.failed = none := (hear_mark P.1 s s' r hm).trans hfail
  refine ⟨?_, hL.rides _ s s' hT.2.2.2.2.2.1 hk hf, hL.keeps s s' hk hf⟩
  unfold Thread.Form
  rw [seat_next T k m hT.2.1]
  exact ⟨hL.form _ s s' hT.2.2.1.1 hk hf, hL.formP _ s r s' hT.2.2.1.2 hm⟩

theorem small_exchange : Spec.small_exchange := by
  intro W₀ Rc Xi Tr X Pb Bk T b blk cells P A iS iD h hI k s m E ds y cols s' hT hd hS
  obtain ⟨hM, hstep⟩ := hS
  obtain ⟨d, rfl, hdf, rfl, rfl, hq⟩ := seated_moved h hd hM
  obtain ⟨r, hr, -, hm, -, -⟩ := (step_seats_iff P.1 blk h.seats T.ft s s' _ _ _).1 hstep
  obtain rfl : (⟨[], d⟩ : Fmt.RoundView) = r := by
    have e : [(⟨[], d⟩ : Fmt.RoundView)] = [r] := hr
    exact List.head_eq_of_cons_eq e
  have hk : K8Keeps s s' := keeps_of_means hm
  obtain ⟨tl, cf, first, -, ht⟩ := hk.tl
  have hcf := (same_of_yes P.1 s s' _ _ hm ht).2
  obtain ⟨hX, hcols⟩ := hI.fine k s m E s' _ hT hk ht
  intro ds' i hi
  have hw : (playedAt blk.name blk.place d m).2.st.heard ++ ds' = m.st.heard ++ d :: ds' := by
    show (m.st.heard ++ [d]) ++ ds' = _
    rw [List.append_assoc]
    rfl
  have hboth := small_at_silence T.Wt A (T.wit k m.st.input (m.st.heard ++ d :: ds')) P.1 s s'
    ⟨[], d⟩ _ (askOfInput cells P.2 m.st.input) m.loc hm hdf hI.some ht hcols hX
    (hI.tie k s m E s' _ (d :: ds') hT hk ht) (hI.zz k s m E s' _ d ds' hT hk ht hcf) hq
  rw [hw]
  rcases List.mem_cons.1 hi with rfl | hi
  · exact hI.small _ _ _ _ hboth.1
  · obtain rfl := List.mem_singleton.1 hi
    exact hI.digits _ _ _ _ hboth.2

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.seated_moved
#print axioms ProofFile.Honest.K8.small_accepted
#print axioms ProofFile.Honest.K8.small_behind
#print axioms ProofFile.Honest.K8.small_exchange
