-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/QuietMember.lean: the two sentences `exact` and `fresh` of the frame's `Good`
(Honest/Side.lean) at one member that sends nothing at one round, of any side. At the frame's own constants `quietPart`
and `quietSim` (Honest/ForKinds.lean), with any second stop. No kind is named in the two sentences or in what they rest
on; `batPart_is` alone names K9's part. Statements and proofs on the frame's own definitions. No goal is stated. What
follows from these sentences is not said here: this file says, twice, that two laws are equal, in the frame's letters,
and no more.
  `quietStop h sh`   the part: { quietPart 1 with hid := h, hidShare := sh }: no coin, one move that says nothing, no
      first stop; its second stop h and that stop's stated number sh are free
  `quietAt j d₀ h sh a`   the member: number j, the one round d₀ with no oracle message, that part, `quietSim a 1`
  `silent_of_stopAt`   where the part's `stopAt` at one challenge d is not "the second stop": the second stop says
      nothing in front of the round (at own challenges []) and nothing behind it (at [d])
  `quiet_play_stop`    so the part's one step, at a round that cuts no item but roots, played alone by the frame's
      `play` from any stand m at d, returns: the value, written out; the stand's field `opened` is carried on unturned
  **`quiet_exact_at`**  `Good.exact`'s own sentence at that member, of any side σ. Five of its premises are not spent
      (On · bud · that the stand has seen what stands in front · that the stand's field `opened` is what the front holds
      for the reads of `Good`'s letter pre · that the front holds the columns). It keeps two (the challenges fit the
      round; the second stop does not stop the part) and adds one of its own: the round cuts no item but roots. Both
      sides are the law that gives the one list [⟨[], []⟩]
  **`quiet_fresh_at`**  `Good.fresh`'s own sentence at that member, under one premise on the book (no entry lets the
      part at q spend a coin of this part): the frame's own `fresh_of_nil` (Honest/Law/ToyLaw.lean). None of its three
      premises is spent, and none on the round is asked: the lemma spends nothing of the member
  `batPart_is`, `quietStop_none`   K9's part is `quietPart 1`; and `quietStop` at the stop that never speaks, stated 0
      of 1, is `quietPart 1`

A caller whose row has several parts lays `Good`'s two fields by cases on u ∈ σ.members and calls these at its quiet
member. General in S, Cl, V, W, X, Pb, the side (its block, row and fall), the face, the book (but for that premise),
ord, the member's number, the round, the simulator's address, h and sh. That the premises of either sentence can be met
together is shown by no line of this file. Both are called by `quiet_good`
(Honest/K9/QuietGood.lean; neither is in this library), which is on no
list, and by other kinds' files.

Limits of the one premise on the round ("it cuts no item but roots"). (1) It is wider than "nothing is sent": a round
whose entry counts a root, with an empty list of oracle messages, meets it: the two sentences stay true there, but of a
prover that lays no table for that root; what shuts such a round out is the plan's own test on a block's shape, not
`Good`. (2) It reads neither which stored trees the round opens, nor which other trees, nor its proof of work: a round
at which nothing is sent may draw positions and open trees: these columns are booked at the part that sent the tree. (3)
The premise (hi) lets through a round whose entry counts a root with no oracle message: whoever lays these sentences at
a description owes the plan's own test (`planOk`) beside them; a lemma "shaped and the premise give no root" is not in
this file. (4) The second stop h (it takes a value of the type V, which the face's `sees` yields of the input, and two
lists of challenges) and its stated number sh are free letters: no sentence of this file ties sh to h: a caller names
both, with the law that ties them. The lists at which the second stop speaks are left out of `quiet_exact_at` by its
premise hs, which is the field's own: nothing here bounds them. (5) The part hands its carried state on unturned; a
caller that lifts it owes the line on the lens. The two sentences are book-keeping for a part that sends nothing: they
are no result on any part that sends something.

What is not claimed. A part with more rounds than one, with a first stop, or with an oracle message. The premise on the
book at any book. No property of the protocol is claimed: nothing is said on its soundness, completeness, binding or
hiding.
-/
import Johnson.Desc.ProofFile.Honest.K9.Side
import Johnson.Desc.ProofFile.Honest.ForKinds
import Johnson.Desc.ProofFile.Honest.Law.ToyLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open VerifiableInference VerifiableInference.Desc

variable {S Cl V W X Pb : Type}

/-- The quiet part with a second stop. -/
def quietStop (h : V → List Fmt.Drawn → List Fmt.Drawn → Option String) (sh : Odds) : Part V W X :=
  { (quietPart 1 : Part V W X) with hid := h, hidShare := sh }

/-- The member: number j, the one round d₀ with no oracle message, `quietStop h sh`, `quietSim a 1`. Nothing ties a to
the side's place or to j. -/
def quietAt (j : Nat) (d₀ : Fmt.DeclaredRound) (h : V → List Fmt.Drawn → List Fmt.Drawn → Option String) (sh : Odds)
    (a : Addr) : Member V W X Pb := ⟨j, [(d₀, [])], quietStop h sh, ProofFile.Honest.quietSim a 1⟩

/-- Where `stopAt` is not "the second stop", the second stop is silent at both askings. -/
theorem silent_of_stopAt (h : V → List Fmt.Drawn → List Fmt.Drawn → Option String) (sh : Odds) (v : Option V)
    (loc : List Fmt.Drawn) (d : Fmt.Drawn)
    (hs : (quietStop h sh : Part V W X).stopAt v loc [d] ≠ some .hid) :
    (v.bind fun u => h u loc []) = none ∧ (v.bind fun u => h u loc [d]) = none := by
  have e : (quietStop h sh : Part V W X).stopAt v loc [d] =
      (if (v.bind fun u => h u loc []).isSome then some Why.hid
       else if (v.bind fun u => h u loc [d]).isSome then some Why.hid else none) := by
    simp only [Part.stopAt, quietStop, quietPart, List.range_succ, List.findSome?, List.length_replicate,
      List.range_zero, List.nil_append, List.cons_append, List.take_zero, Option.isSome_none, Bool.false_eq_true,
      if_false, Nat.reduceBEq, Nat.reduceAdd, List.take_succ_cons, List.take_nil]
    cases (v.bind fun u => h u loc []).isSome <;> cases (v.bind fun u => h u loc [d]).isSome <;> rfl
  rw [e] at hs
  cases h0 : (v.bind fun u => h u loc []) with
  | some _ => rw [h0] at hs; exact absurd rfl hs
  | none =>
    rw [h0] at hs
    cases h1 : (v.bind fun u => h u loc [d]) with
    | some _ => rw [h1] at hs; exact absurd rfl hs
    | none => exact ⟨rfl, rfl⟩

/-- The part's one step, played alone, where the second stop is silent. -/
theorem quiet_play_stop (h : V → List Fmt.Drawn → List Fmt.Drawn → Option String) (sh : Odds)
    (d₀ : Fmt.DeclaredRound) (hi : d₀.items.filter (· != .root) = []) (name : String) (a : Addr) (v : Option V)
    (c : (quietStop h sh : Part V W X).Coins) (d : Fmt.Drawn) (m : Mid W X)
    (h0 : (v.bind fun u => h u m.loc []) = none) (h1 : (v.bind fun u => h u m.loc [d]) = none) :
    play ((quietStop h sh : Part V W X).steps name a [(d₀, [])] v c) [d] [] m =
      .ok ([⟨name, a.place, a.part, true, [], [], d⟩],
        ⟨{ m.st.hears d with own := (m.st.hears d).own }, m.loc ++ [d], m.seen ++ [⟨[], d⟩], m.opened⟩) := by
  have hfit : (⟨[], []⟩ : Sending).fits d₀ [] = true := by
    unfold Sending.fits
    rw [hi]
    rfl
  simp [Part.steps, quietStop, quietPart, play, Step.tell, Step.hear, Step.stop, hfit, Except.bind, Except.map,
    h0, h1]

/-- **`Good.exact`'s sentence at the member, of any side.** -/
theorem quiet_exact_at (σ : Side S Cl V W X Pb) (φ : Face V W Pb) (j : Nat) (d₀ : Fmt.DeclaredRound)
    (hi : d₀.items.filter (· != .root) = []) (h : V → List Fmt.Drawn → List Fmt.Drawn → Option String)
    (sh : Odds) (a : Addr) (ca : CsAll (quietAt (W := W) (X := X) (Pb := Pb) j d₀ h sh a).part.carries)
    (m : Mid W X) (front : Before) (ds : List Fmt.Drawn) (asks : List (List (List Nat)))
    (hd : drawsFit ((quietAt (W := W) (X := X) (Pb := Pb) j d₀ h sh a).rounds.map (·.1)) ds = true)
    (hs : (quietAt (W := W) (X := X) (Pb := Pb) j d₀ h sh a).part.stopAt (φ.sees m.st.input) m.loc ds ≠ some .hid) :
    (Prob.unif (Cs (quietAt (W := W) (X := X) (Pb := Pb) j d₀ h sh a).part.takes ×
        CsAll (quietAt (W := W) (X := X) (Pb := Pb) j d₀ h sh a).part.spends)).map
        (fun c => σ.shows φ (quietAt j d₀ h sh a) (c.1, c.2, ca) m ds asks) =
      (Prob.unif (Cs (quietAt (V := V) (W := W) (X := X) (Pb := Pb) j d₀ h sh a).sim.takes)).map
        fun c => (quietAt j d₀ h sh a).tells φ c m.st.input front ds asks := by
  obtain ⟨d, rfl, _⟩ := drawsFit_one (d := d₀) hd
  obtain ⟨h0, h1⟩ := silent_of_stopAt h sh _ _ d hs
  have e1 : (fun c : Cs (quietAt (W := W) (X := X) (Pb := Pb) j d₀ h sh a).part.takes ×
        CsAll (quietAt (W := W) (X := X) (Pb := Pb) j d₀ h sh a).part.spends =>
      σ.shows φ (quietAt j d₀ h sh a) (c.1, c.2, ca) m [d] asks) = Function.const _ (some [⟨[], []⟩]) := by
    funext c
    unfold Side.shows
    show ((play ((quietStop h sh : Part V W X).steps _ _ [(d₀, [])] _ _) [d] [] m).toOption.map _) = _
    rw [quiet_play_stop h sh d₀ hi _ _ _ _ d m h0 h1]
    rfl
  have e2 : (fun c : Cs (quietAt (V := V) (W := W) (X := X) (Pb := Pb) j d₀ h sh a).sim.takes =>
      (quietAt j d₀ h sh a).tells φ c m.st.input front [d] asks) = Function.const _ (some [⟨[], []⟩]) := rfl
  show PMF.map _ _ = PMF.map _ _
  rw [e1, e2, PMF.map_const, PMF.map_const]

/-- **`Good.fresh`'s sentence at the member, of any side.** -/
theorem quiet_fresh_at (σ : Side S Cl V W X Pb) (φ : Face V W Pb) (Bk : ProverCoinCounts) (ord : List Place) (j : Nat)
    (d₀ : Fmt.DeclaredRound) (h : V → List Fmt.Drawn → List Fmt.Drawn → Option String) (sh : Odds) (a q : Addr)
    (hown : Bk.spentBy ⟨σ.block.place, j⟩ q = [])
    (sp : CsAll (quietAt (W := W) (X := X) (Pb := Pb) j d₀ h sh a).part.spends)
    (ca : CsAll (quietAt (W := W) (X := X) (Pb := Pb) j d₀ h sh a).part.carries) (m : Mid W X)
    (ds : List Fmt.Drawn) (asks : List (List (List Nat))) :
    (Prob.unif (Cs (quietAt (W := W) (X := X) (Pb := Pb) j d₀ h sh a).part.takes)).map (fun c =>
        (cutAll c (Bk.spentBy ⟨σ.block.place, j⟩ q), σ.shows φ (quietAt j d₀ h sh a) (c, sp, ca) m ds asks,
          cutAll c (Bk.knownBy ord ⟨σ.block.place, j⟩ q))) =
      (Prob.unif (CsAll ((Bk.spentBy ⟨σ.block.place, j⟩ q).map Ahead.named) ×
          Cs (quietAt (W := W) (X := X) (Pb := Pb) j d₀ h sh a).part.takes)).map fun x =>
        (some x.1, σ.shows φ (quietAt j d₀ h sh a) (x.2, sp, ca) m ds asks,
          cutAll x.2 (Bk.knownBy ord ⟨σ.block.place, j⟩ q)) :=
  fresh_of_nil _ hown _ _

/-- K9's part is the frame's quiet part of one round. -/
theorem batPart_is : (batPart : Part V W X) = quietPart 1 := rfl

/-- At the stop that never speaks, stated 0 of 1, it is the quiet part. -/
theorem quietStop_none : (quietStop (fun _ _ _ => none) ⟨0, 1⟩ : Part V W X) = quietPart 1 := rfl

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.quietStop
#print axioms ProofFile.Honest.K9.quietAt
#print axioms ProofFile.Honest.K9.silent_of_stopAt
#print axioms ProofFile.Honest.K9.quiet_play_stop
#print axioms ProofFile.Honest.K9.quiet_exact_at
#print axioms ProofFile.Honest.K9.quiet_fresh_at
#print axioms ProofFile.Honest.K9.batPart_is
#print axioms ProofFile.Honest.K9.quietStop_none
