-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K8/SeatedItemsAt.lean: THE SMALLNESS TEST: PREMISES' FORMS, AND LAWS
FROM THEM. THE RECORD `K8ItemsAt` IS A FORM OF SIX PREMISES. TWO OF THEM (tie · zz) NAME THE HIDDEN
INPUT: each is an equation between the table of the thread's witness and a := THE INPUT's TRACE's
CELLS: where the thread's witness is a Script's it is an equation on the Script in all but name.
WHOEVER PAYS THEM AT A SCRIPT BRINGS THE STATEMENT BY NAME, AS TEXT, TO THE REVIEWER OF HIDING
FIRST, BEFORE IT IS TYPED. NOTHING IS PAID HERE. One structure; six theorems; none of the
library's goals.

WHY. `K8Items` (Johnson/Desc/ProofFile/Honest/K8/Seated.lean) has one fixed table of cells A : T.Wt
→ TableE, while its fields small and digits stand at every seat a. At the first chain's thread at
the head (1) the two items' meaning reads the library's `cellsAhead`
(Johnson/Desc/First/K8/CellsAhead.lean), which reads the seat's state a.2: so no one A meets all six
fields there; (2) the item on the forms asks, beside the forms' worth, public facts of the state
(`formsQA`, Johnson/Desc/Sound/FormsAhead.lean: an open segment's part; a test on the forms), which
SmallAt does not give at a state whatever: so small cannot be had at every seat. BOTH ARE ARGUED,
NOT PROVED. Here the letter A takes the seat, and small, digits, tie, zz and fine stand behind a
step of the member alone, from the pair of the stand and what is said (`ThrS`), WHERE THE THREAD's
FORM HOLDS BEHIND THE STEP (out of which that test comes:
Johnson/Desc/ProofFile/Honest/K8/FormsInAtHead.lean): just the hypotheses that the law has in hand:
weaker premises. For tie and zz that matters: the library's laws on the state behind a draw stand at
what is reached under the test on words and behind the draw's yes: the pair and the step give both
(`thrS_rchAt`, Johnson/Desc/ProofFile/Honest/Thread/ReachAtHead.lean); from the bare thread no law
that we know gives them. some does not turn.

  `K8ItemsAt`        the record, at a letter Said and a member blk: A : T.P × S → T.Wt → TableE ·
                   small · digits: behind a step of blk the two items mean no more than the
                   library's SmallAt, DigitsAt at the table of the seat behind the step · tie: in
                   the witness's table the symbol arrays are the packing of a, and the third vector
                   of reads holds a's sums weighted by each read's own coefficients (`TieBy`) · zz:
                   the array of digits is `digitAt` of a and the drawn matrix (`ZzBy`): both of
                   Johnson/Desc/ProofFile/Honest/K8/SmallLaw.lean, at a := cellsAtOf (cells ‹the
                   input's trace›) ‹the place's list›, at every first part z of a seat, behind a
                   step · fine: as in `K8Items`, behind a step · some: as there
  `keeps_of_stepped`   a step of the seated member gives `K8Keeps`
  `itemsAt_of_items`   where the member is seated, K8Items at A gives K8ItemsAt at fun _ => A
  **`small_exchange_at`**   K8Seated · K8ItemsAt ⊢ behind a step of the draw's member, where the
                   form holds behind it, the two items hold of the thread's witness
  `smallS_share_at`, `digitsS_share_at`   the two shares from the pair (`ExchangeAtS`), UNDER A
                   THIRD PREMISE hFb: the thread's form behind the member's step, from the pair
  `formBehind_of_behindS`   `BehindS` gives that hFb
"∀ z" in tie and zz asks more than the seat that is handed; `cellsAhead` reads a seat's first part
nowhere; it keeps the text of `Thread.seat` out of the record.
HOW. The lines of `small_exchange` (Johnson/Desc/ProofFile/Honest/K8/SeatedLaws.lean), WRITTEN A
FURTHER TIME, with `small_at_silence` (Honest/K8/DrawBridgeProofs.lean: general in the table) called
at the table of the seat behind the step.
NO OPTION IS RAISED, NO INSTANCE TAKEN AWAY. NO TACTIC THAT SEARCHES.
Limits. ALL SIX FIELDS STAY PREMISES HERE. THE LAW HAS A HYPOTHESIS MORE THAN THE ELDER (the form
behind the step): so the shares do not follow from the two records alone. ONE FACT, TWO FORMS:
`TieBy` here and the library's item's `TieOf` (Johnson/Desc/First/K8/LawItems.lean): one way is
typed, at small integers: `tieOf_of_tieBy` (Johnson/Desc/ProofFile/Honest/K8/SmallLawProofs.lean);
whoever spends both in one gather names the premise that the integers are small. KIN, NOT CALLED:
laws that end in `TieBy`, from premises on what a table holds: `tieBy_of_reads`
(Johnson/HonestTrace/PackedTieBy.lean), `tieBy_of_tieThird`
(Johnson/HonestTrace/PackedTieThird.lean). What the input's trace is, and that its cells are small,
are other debts: cells is a letter. Which of the files that this head names are rows of the library
is for the library's own list to say: it is not said here. THAT THE THREAD STANDS AT ANY OF THESE
BORDERS, AT ANY PROVER, IS NOT SAID HERE: where it stands at none, all is idle.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.SeatedShares
import Johnson.Desc.ProofFile.Honest.Thread.SharesS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Claim Place roundsFit)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K8 (Par MeansAtS Seats approximateRangeProofDrawKind atS tabs SmallAt DigitsAt Extra
  step_seats_iff)
open VerifiableInference.Desc.First.K8.Honest

variable {W₀ Rc Xi Tr X Pb : Type} {Bk : ProverCoinCounts}

/-- **The two items that are the kind's to fill, at a table that takes the seat.** A form of six
premises. tie and zz name the hidden input: a := the input's trace's cells. The ends of small,
digits and fine name no letter of the run (w is bound by "for all"); each STANDS BEHIND A STEP OF
THE MEMBER ALONE, from the pair of the thread's stand and what is said, where the thread's form
holds behind the step: behind a yes at which the second stop is silent.
NOT IN FRONT OF A LAW OVER COINS. -/
structure K8ItemsAt (T : Thread Bk S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop) (b : Nat)
    (blk : Block S Claim) (cells : Tr → Cells) (P : Par × List (Nat × String × Nat))
    (A : T.P × S → T.Wt → TableE) (iS iD : T.ι) : Prop where
  small : ∀ k s m E ds y cols s' w z yy v, ThrS T Said b k s m E → drawsFit blk.rounds ds = true →
    T.Stepped blk k s m E ds y cols s' → T.Form (b + 1) k s' y.2 →
    SmallAt (A (z, s')) s' v → T.means w iS (z, s') yy v
  digits : ∀ k s m E ds y cols s' w z yy v, ThrS T Said b k s m E → drawsFit blk.rounds ds = true →
    T.Stepped blk k s m E ds y cols s' → T.Form (b + 1) k s' y.2 →
    DigitsAt (A (z, s')) s' v → T.means w iD (z, s') yy v
  tie : ∀ k s m E ds y cols s' tl' e z, ThrS T Said b k s m E → drawsFit blk.rounds ds = true →
    T.Stepped blk k s m E ds y cols s' → T.Form (b + 1) k s' y.2 → s'.tl? = some tl' →
    TieBy tl' (A (z, s') (T.wit k m.st.input (m.st.heard ++ e)))
      (cellsAtOf (cells m.st.input.trace) P.2)
  zz : ∀ k s m E ds y cols s' tl' (d : Fmt.Drawn) e z, ThrS T Said b k s m E →
    drawsFit blk.rounds ds = true → T.Stepped blk k s m E ds y cols s' →
    T.Form (b + 1) k s' y.2 → s'.tl? = some tl' → tl'.cfF = d.trits.toArray →
    ZzBy tl' (A (z, s') (T.wit k m.st.input (m.st.heard ++ d :: e)))
      (cellsAtOf (cells m.st.input.trace) P.2)
  fine : ∀ k s m E ds y cols s' tl', ThrS T Said b k s m E → drawsFit blk.rounds ds = true →
    T.Stepped blk k s m E ds y cols s' → T.Form (b + 1) k s' y.2 →
    s'.tl? = some tl' → Extra s' ∧ DgP.colsTest tl' = true
  some : P.1.ks ≠ []

variable {T : Thread Bk S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb}
  {Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop} {b : Nat}
  {blk : Block S Claim} {cells : Tr → Cells} {P : Par × List (Nat × String × Nat)} {iS iD : T.ι}

/-- A step of the seated member keeps what the draw keeps. -/
theorem keeps_of_stepped (h : K8Seated T b blk cells P) {k : Coins Bk} {s s' : S}
    {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc Xi Tr) X} {cols : List VerifiableInference.Desc.OpenedColumn}
    (hS : T.Stepped blk k s m E ds y cols s') : K8Keeps s s' := by
  obtain ⟨-, hstep⟩ := hS
  obtain ⟨r, -, -, hm, -, -⟩ := (step_seats_iff P.1 blk h.seats T.ft s s' _ _ _).1 hstep
  exact keeps_of_means hm

/-- The record, at a table that does not read the seat, where the member is seated. -/
theorem itemsAt_of_items {A : T.Wt → TableE} (hK : K8Seated T b blk cells P)
    (h : K8Items T b cells P A iS iD) : K8ItemsAt T Said b blk cells P (fun _ => A) iS iD :=
  { small := fun _ _ _ _ _ _ _ s' w z yy v _ _ _ _ hs => h.small w (z, s') yy v hs
    digits := fun _ _ _ _ _ _ _ s' w z yy v _ _ _ _ hs => h.digits w (z, s') yy v hs
    tie := fun k s m E _ _ _ s' tl' e _ hA _ hS _ ht =>
      h.tie k s m E s' tl' e hA.1 (keeps_of_stepped hK hS) ht
    zz := fun k s m E _ _ _ s' tl' d e _ hA _ hS _ ht =>
      h.zz k s m E s' tl' d e hA.1 (keeps_of_stepped hK hS) ht
    fine := fun k s m E _ _ _ s' tl' hA _ hS _ ht =>
      h.fine k s m E s' tl' hA.1 (keeps_of_stepped hK hS) ht
    some := h.some }

variable {A : T.P × S → T.Wt → TableE}

/-- **THE EXCHANGE, AT THE TWO ITEMS**: behind a yes at which the second stop is silent.
NOT IN FRONT OF A LAW OVER COINS. -/
theorem small_exchange_at (h : K8Seated T b blk cells P)
    (hI : K8ItemsAt T Said b blk cells P A iS iD) :
    ∀ k s m E ds y cols s', ThrS T Said b k s m E → drawsFit blk.rounds ds = true →
      T.Stepped blk k s m E ds y cols s' → T.Form (b + 1) k s' y.2 →
      T.Items [iS, iD] k s' y.2 (E.add y.1) := by
  intro k s m E ds y cols s' hA hd hS hFb
  have hS0 := hS
  have hd0 := hd
  obtain ⟨hM, hstep⟩ := hS
  obtain ⟨d, rfl, hdf, rfl, rfl, hq⟩ := seated_moved h hd hM
  obtain ⟨r, hr, -, hm, -, -⟩ := (step_seats_iff P.1 blk h.seats T.ft s s' _ _ _).1 hstep
  obtain rfl : (⟨[], d⟩ : Fmt.RoundView) = r := by
    have e : [(⟨[], d⟩ : Fmt.RoundView)] = [r] := hr
    exact List.head_eq_of_cons_eq e
  have hk : K8Keeps s s' := keeps_of_means hm
  obtain ⟨tl, cf, first, -, ht⟩ := hk.tl
  have hcf := (same_of_yes P.1 s s' _ _ hm ht).2
  obtain ⟨hX, hcols⟩ := hI.fine k s m E _ _ _ s' _ hA hd0 hS0 hFb ht
  intro ds' i hi
  have hw : (playedAt blk.name blk.place d m).2.st.heard ++ ds' = m.st.heard ++ d :: ds' := by
    show (m.st.heard ++ [d]) ++ ds' = _
    rw [List.append_assoc]
    rfl
  have hboth : ∀ z, SmallAt (A (z, s')) s' (T.wit k m.st.input (m.st.heard ++ d :: ds')) ∧
      DigitsAt (A (z, s')) s' (T.wit k m.st.input (m.st.heard ++ d :: ds')) := fun z =>
    small_at_silence T.Wt (A (z, s')) (T.wit k m.st.input (m.st.heard ++ d :: ds')) P.1 s s'
      ⟨[], d⟩ _ (askOfInput cells P.2 m.st.input) m.loc hm hdf hI.some ht hcols hX
      (hI.tie k s m E _ _ _ s' _ (d :: ds') z hA hd0 hS0 hFb ht)
      (hI.zz k s m E _ _ _ s' _ d ds' z hA hd0 hS0 hFb ht hcf) hq
  rw [hw]
  rcases List.mem_cons.1 hi with rfl | hi
  · exact hI.small k s m E _ _ _ s' _ _ _ _ hA hd0 hS0 hFb (hboth _).1
  · obtain rfl := List.mem_singleton.1 hi
    exact hI.digits k s m E _ _ _ s' _ _ _ _ hA hd0 hS0 hFb (hboth _).2

/-- **The share at the forms of the run "small"**, from the pair: behind a yes at which the second
stop is silent. NOT IN FRONT OF A LAW OVER COINS. hFb: the form behind the step. -/
theorem smallS_share_at (h : K8Seated T b blk cells P)
    (hI : K8ItemsAt T Said b blk cells P A iS iD)
    (hFb : ∀ k s m E ds y cols s', ThrS T Said b k s m E → drawsFit blk.rounds ds = true →
      T.Stepped blk k s m E ds y cols s' → T.Form (b + 1) k s' y.2) :
    ExchangeAtS T Said b iS := by
  intro blk' hblk' k s m E ds y cols s' hA hd hS ds' j hj
  rw [h.here] at hblk'
  cases hblk'
  obtain rfl := List.mem_singleton.1 hj
  exact small_exchange_at h hI k s m E ds y cols s' hA hd hS (hFb _ _ _ _ _ _ _ _ hA hd hS) ds' j
    (List.mem_cons_self ..)

/-- **The share at the digits' lookup**, from the pair: behind a yes at which the second stop is
silent. NOT IN FRONT OF A LAW OVER COINS. hFb: the form behind the step. -/
theorem digitsS_share_at (h : K8Seated T b blk cells P)
    (hI : K8ItemsAt T Said b blk cells P A iS iD)
    (hFb : ∀ k s m E ds y cols s', ThrS T Said b k s m E → drawsFit blk.rounds ds = true →
      T.Stepped blk k s m E ds y cols s' → T.Form (b + 1) k s' y.2) :
    ExchangeAtS T Said b iD := by
  intro blk' hblk' k s m E ds y cols s' hA hd hS ds' j hj
  rw [h.here] at hblk'
  cases hblk'
  obtain rfl := List.mem_singleton.1 hj
  exact small_exchange_at h hI k s m E ds y cols s' hA hd hS (hFb _ _ _ _ _ _ _ _ hA hd hS) ds' j
    (List.mem_cons_of_mem _ (List.mem_singleton.2 rfl))

/-- `BehindS` gives the premise hFb of the two shares. -/
theorem formBehind_of_behindS (h : K8Seated T b blk cells P) (hB : BehindS T Said b) :
    ∀ k s m E ds y cols s', ThrS T Said b k s m E → drawsFit blk.rounds ds = true →
      T.Stepped blk k s m E ds y cols s' → T.Form (b + 1) k s' y.2 :=
  fun k s m E ds y cols s' hA hd hS => (hB blk h.here k s m E ds y cols s' hA hd hS).1

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.K8ItemsAt
#print axioms ProofFile.Honest.K8.keeps_of_stepped
#print axioms ProofFile.Honest.K8.itemsAt_of_items
#print axioms ProofFile.Honest.K8.small_exchange_at
#print axioms ProofFile.Honest.K8.smallS_share_at
#print axioms ProofFile.Honest.K8.digitsS_share_at
#print axioms ProofFile.Honest.K8.formBehind_of_behindS
