-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/TapeAccepts.lean: CONDITIONAL.

What is here. Of a statement that the hearing of the feed-forward layers' own rounds (sub-protocol
K4) returns: the three hypotheses ON THE ROUNDS of `hearAt_returns`
(Johnson/Desc/First/K4/Returns/Seat.lean: "the hearing at a seat returns"), to the letter, at the
rounds that the honest row has played, without the sealed digest. Statements with their proofs.

A NAME: K4's test `fitsAll` (OnBytes/Desc/First/K4/Steps.lean) is written with its full name below:
in this namespace the bare name is the frame's `ProofFile.Honest.fitsAll` (Honest/Law/Kept.lean), another
function.

  `vals_of_items`   values whose items are all elements of the extension field are as many, and each
      is one
  `table_fits`   GENERAL IN THE TABLE: rounds that pass the general step's test on shapes
      (`roundsFit`, Johnson/Desc/Block.lean) under declared rounds that are made of a table's rows
      pass K4's two tests on the stretch (`fitsAll`; the strict reading
      `plainStretchWith rowsTabled`, OnBytes/Desc/First/FlStep.lean)
  `k4_fits_of_roundsFit`   so at the member's rounds: the hypotheses h1 and h2
  `k4_played_fits`   so at what the honest row has played (`fits_played`, Honest/Law/Cut.lean), at
      challenges that fit the member's rounds (hd)
  `rowsNorms_length`   the rows in front of the second token sumcheck are `rJ3 P g`
      (Law/SlotsUnder.lean) in number
  `coin_tape`, `k4_coin_tape`   where the honest side's own test on the sampled element
      (`k4CoinZero`, Honest/K4/Part.lean) says nothing: the hypothesis vE

Not shown here. THAT THE SUB-PROTOCOL's DECISION ACCEPTS ANYTHING: three of the hypotheses of a
statement to that end are shown here, the others not: these are tests on the plan and facts on the
verifier's state in front. That `K4SeatedA` (Law/SeatedA.lean: four of the seat's nine fields) can
be met: this file gives no example. Nothing on what the rounds hold beyond their shape and one
sampled element: THE TWO TESTS ON THE STRETCH READ NO SENT VALUE: rounds of the table's shape pass
them whatever they hold. Following import lines, and stopping unopened at every module under
Johnson/Goal/, Johnson/D/, Johnson/Bridge/ or ThirdParty/ and at every module whose name begins
Cb.Bridge, its imports reach 2 modules under Johnson/Bridge/, and none of the others; what lies
behind these is not counted; 7 of the modules that it reaches have RecCompile in their names, none
of them RecCompile's Honest*, Both or PassH*. The seven (Join, Wire, Pass, CmsGlue, CmsBcs, Cms,
Bcs) come with a module of the library (Johnson/E/KObj/ProofFile.lean) through Law/RowBatch.lean:
nothing here names one of them. Nothing on soundness, on completeness or on any other property.

Kin. `coin_tape` goes from the silence of the honest side's test on the sampled element to «not 0»
by the program's own test (`isZeroE`); `k4_coin_ne` (Law/Live/TapeOfMark.lean) goes from the same
silence, at words below the prime, to «not 0» in the field. `table_fits` reads `roundsFit` clause by
clause; the library has its seven clauses pair by pair (`roundsFit_iff`,
Johnson/Top/H0/StepLaws/RoundsFit.lean): not called. `vals_of_items` has the hypothesis of the
library's `scalars_of_items` (Honest/Small/Stated.lean) to the letter and goes its way arm by arm;
that law ends in: `scalars` returns, as many. `fits_of_roundsFit`, beside it, goes from `roundsFit`
to the masked sumcheck's hearing's test on shapes as `table_fits` goes to K4's two. Neither is
called.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.RowBatch
import Johnson.Desc.ProofFile.Honest.K4.Law.Starts
import Johnson.Desc.ProofFile.Honest.K4.Law.SeatedA
import Johnson.Desc.ProofFile.Honest.Law.Cut
import Johnson.Desc.First.K4.Returns.Seat
import Johnson.Desc.First.K4.Returns.Needs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes (isZeroE)
open OnBytes.Model (RoundName)
open OnBytes.K.Kc (paired)
open OnBytes.Desc.First (Kit.plainStretchWith Kit.plainRoundWith Kit.rowsOk)
open OnBytes.Desc.First.K4 (Par Rd rounds entries entryOf rowsTabled)
open OnBytes.Desc.First.K4.Rt (TapeOf rowsNorms tape_length)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Desc.First.P1 (drawnOf)
open VerifiableInference.Desc (Block Claim First.S roundsFit noDigest itemOf)

/-! ## 1 The two tests on the stretch -/

/-- Values whose items are all elements of the extension field are as many, and each is one. -/
theorem vals_of_items : ∀ (vals : List Fmt.ItemValue) (n : Nat),
    vals.map itemOf = List.replicate n .e →
    vals.length = n ∧ (vals.all fun x => match x with | .e _ => true | _ => false) = true
  | [], 0, _ => ⟨rfl, rfl⟩
  | .e _ :: l, n + 1, h => by
    rw [List.map_cons, List.replicate_succ, List.cons.injEq] at h
    obtain ⟨h1, h2⟩ := vals_of_items l n h.2
    exact ⟨congrArg (· + 1) h1, h2⟩
  | [], _ + 1, h => by cases h
  | _ :: _, 0, h => by cases h
  | .f _ :: _, _ + 1, h => by cases h
  | .word _ :: _, _ + 1, h => by cases h
  | .root _ :: _, _ + 1, h => by cases h
  | .answer _ :: _, _ + 1, h => by cases h

/-- **Rounds that pass the general step's test on shapes, under declared rounds that are made of a
table's rows, pass K4's two tests on the stretch.** General in the table. -/
theorem table_fits : ∀ (L : List Rd) (R : List Fmt.RoundView),
    roundsFit ((L.map entryOf).map fun e => ({ entry := e } : Fmt.DeclaredRound)) R = true →
    OnBytes.Desc.First.K4.fitsAll L (L.map entryOf) (R.map noDigest) = true ∧
      Kit.plainStretchWith rowsTabled (L.map entryOf) (R.map noDigest) = true
  | [], [], _ => ⟨rfl, rfl⟩
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | d :: L, r :: R, h => by
    have h' : (r.vals.map itemOf ==
          (Fmt.DeclaredRound.items { entry := entryOf d }).filter (· != .root) &&
        r.drawn.elems.length == (entryOf d).drawE && r.drawn.poss.length == (entryOf d).poss &&
        r.drawn.trits.length == (entryOf d).trits &&
        r.drawn.poss.all (· < 2 ^ (entryOf d).logN) &&
        r.drawn.trits.all (fun t => t == -1 || t == 0 || t == 1) &&
        VerifiableInference.Desc.drawsMarkedNonzeroHaveNonzeroWords { entry := entryOf d } r &&
        roundsFit ((L.map entryOf).map fun e => ({ entry := e } : Fmt.DeclaredRound)) R) = true := h
    simp only [Bool.and_eq_true, beq_iff_eq] at h'
    obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, -⟩, -⟩, -⟩, h8⟩ := h'
    obtain ⟨i1, i2⟩ := table_fits L R h8
    have hi : (Fmt.DeclaredRound.items { entry := entryOf d }).filter (· != .root) =
        List.replicate d.sent .e := by
      unfold Fmt.DeclaredRound.items Fmt.Entry.cut entryOf
      simp
    obtain ⟨v1, v2⟩ := vals_of_items r.vals d.sent (h1.trans hi)
    have hrow : Kit.rowsOk rowsTabled (L.map entryOf).isEmpty (entryOf d) = true := by
      unfold Kit.rowsOk rowsTabled
      cases hz : ((entryOf d).rows == 0) <;> simp
    refine ⟨?_, ?_⟩
    · show (d.fits (entryOf d) (noDigest r) &&
        OnBytes.Desc.First.K4.fitsAll L (L.map entryOf) (R.map noDigest)) = true
      rw [i1, Bool.and_true]
      unfold Rd.fits
      simp only [Bool.and_eq_true, beq_iff_eq]
      exact ⟨⟨⟨⟨⟨rfl, v1⟩, rfl⟩, h2⟩, rfl⟩, rfl⟩
    · show (Kit.plainRoundWith rowsTabled (L.map entryOf).isEmpty (entryOf d) (noDigest r) &&
        Kit.plainStretchWith rowsTabled (L.map entryOf) (R.map noDigest)) = true
      rw [i2, Bool.and_true]
      unfold Kit.plainRoundWith
      simp only [Bool.and_eq_true, beq_iff_eq]
      exact ⟨⟨⟨⟨⟨⟨rfl, rfl⟩, h2⟩, h3⟩, h4⟩, hrow⟩, v2⟩

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb : Type}
  {T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb} {b : Nat}
  {cells : Tr → Cells} {weights : W₀ → Weights} {tokens : Xi → Array Nat}
  {look : K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard} {Q : K4Pub} {p : Par}
  {blk : Block First.S Claim}

/-- **At the member's rounds: the hypotheses h1 and h2 of `hearAt_returns`**, at rs := the rounds
without the sealed digest. CONDITIONAL on the seat, of whose four fields it spends rounds alone, and
on h. -/
theorem k4_fits_of_roundsFit (Se : K4SeatedA T b cells weights tokens look Q p blk)
    (R : List Fmt.RoundView) (h : roundsFit blk.rounds R = true) :
    OnBytes.Desc.First.K4.fitsAll (rounds p.P p.hp p.g) (entries p.P p.hp p.g)
        (R.map noDigest) = true ∧
      Kit.plainStretchWith rowsTabled (entries p.P p.hp p.g) (R.map noDigest) = true := by
  rw [Se.rounds] at h
  exact table_fits (rounds p.P p.hp p.g) R h

/-- **At what the honest row has played.** CONDITIONAL on the seat, hM and hd. -/
theorem k4_played_fits (Se : K4SeatedA T b cells weights tokens look Q p blk) {k : Coins Bk}
    {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc Xi Tr) X} {cols : List VerifiableInference.Desc.OpenedColumn}
    (hM : T.Moved blk k m E ds y cols) (hd : drawsFit blk.rounds ds = true) :
    OnBytes.Desc.First.K4.fitsAll (rounds p.P p.hp p.g) (entries p.P p.hp p.g)
        ((roundsOf y.1).map noDigest) = true ∧
      Kit.plainStretchWith rowsTabled (entries p.P p.hp p.g) ((roundsOf y.1).map noDigest) =
        true := by
  obtain ⟨⟨l, hl, hy⟩, hc⟩ := hM
  obtain ⟨c, -, rfl, ho, hr⟩ := chainSteps_one hl Se.half
  exact k4_fits_of_roundsFit Se _ (fits_played hr ho hy hd hc).1.1

/-! ## 2 The sampled element -/

/-- The rows of the verifier's table in front of the second token sumcheck are `rJ3 P g`
(Law/SlotsUnder.lean) in number. -/
theorem rowsNorms_length (P : OnBytes.Model.Layer.Pub) (g : Nat) :
    (rowsNorms P g).length = rJ3 P g := by
  unfold rowsNorms rJ3 rJ2 rowsRound OnBytes.Desc.First.K4.k0 OnBytes.Desc.First.K4.layerRds
  cases hg : (g == 0) <;> simp [masked_len] <;> omega

/-- **Where the honest side's own test on the sampled element says nothing, the element that the
tape's round behind these rows has sampled is not 0.** R: rounds whose challenges are ds. -/
theorem coin_tape (Q : K4Pub) (ds : List Fmt.Drawn) (R : List Fmt.RoundView)
    (hR : ∀ n : Nat, (R[n]?).map Fmt.RoundView.drawn = ds[n]?) (hz : k4CoinZero Q ds = none)
    (es : List Fmt.Entry) :
    ∀ t₁ s0 eps t₂, TapeOf (rowsNorms Q.P Q.g) t₁ →
      paired (R.map noDigest) es =
        t₁ ++ ⟨some RoundName.pscEpsilon.name, 0, 0, s0, [eps]⟩ :: t₂ → isZeroE eps = false := by
  intro t₁ s0 eps t₂ h1 e
  have hl : t₁.length = rJ3 Q.P Q.g := (tape_length h1).trans (rowsNorms_length Q.P Q.g)
  have hdr := paired_drawn R es (rJ3 Q.P Q.g)
  rw [← paired_noDigest, e, ← hl, List.drop_left] at hdr
  have hdr' : [eps] = ((R[t₁.length]?).map fun r => r.drawn.elems.map OnBytes.E.ofTriple).getD [] :=
    hdr
  have q := hR t₁.length
  unfold k4CoinZero at hz
  rw [k4_starts] at hz
  have hz' : (match ds[rJ3 Q.P Q.g]? with
    | some d =>
      if isZeroE ((d.elems.head?.map OnBytes.E.ofTriple).getD OnBytes.oneE) then
        some _
      else none
    | none => none) = none := hz
  rw [← hl, ← q] at hz'
  cases hr : R[t₁.length]? with
  | none =>
    rw [hr] at hdr'
    cases hdr'
  | some r =>
    rw [hr] at hdr' hz'
    have hdr'' : [eps] = r.drawn.elems.map OnBytes.E.ofTriple := hdr'
    cases he : r.drawn.elems with
    | nil =>
      rw [he] at hdr''
      cases hdr''
    | cons x xs =>
      rw [he] at hdr''
      have hx : eps = OnBytes.E.ofTriple x := (List.cons.inj hdr'').1
      have hz'' : (if isZeroE ((r.drawn.elems.head?.map OnBytes.E.ofTriple).getD OnBytes.oneE) then
          some _
        else none) = none := hz'
      rw [he] at hz''
      have hz3 : (if isZeroE (OnBytes.E.ofTriple x) then
          some _
        else none) = none := hz''
      rw [hx]
      cases hb : isZeroE (OnBytes.E.ofTriple x) with
      | false => rfl
      | true =>
        rw [hb] at hz3
        cases hz3

/-- **At what the honest row has played: the hypothesis vE of `hearAt_returns`**, at rs := the
played rounds without the sealed digest. CONDITIONAL on the seat, of whose four fields it spends own
alone, hM and hz. -/
theorem k4_coin_tape (Se : K4SeatedA T b cells weights tokens look Q p blk) {k : Coins Bk}
    {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc Xi Tr) X} {cols : List VerifiableInference.Desc.OpenedColumn}
    (hM : T.Moved blk k m E ds y cols) (hz : k4CoinZero Q ds = none) :
    ∀ t₁ s0 eps t₂, TapeOf (rowsNorms p.P p.g) t₁ →
      paired ((roundsOf y.1).map noDigest) (entries p.P p.hp p.g) =
        t₁ ++ ⟨some RoundName.pscEpsilon.name, 0, 0, s0, [eps]⟩ :: t₂ → isZeroE eps = false := by
  obtain ⟨⟨l, _, hy⟩, _⟩ := hM
  obtain ⟨eP, _, eg, _, _⟩ := Se.own
  rw [eP, eg]
  exact coin_tape Q ds (roundsOf y.1) (played_drawn hy) hz _

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.vals_of_items
#print axioms ProofFile.Honest.K4.table_fits
#print axioms ProofFile.Honest.K4.k4_fits_of_roundsFit
#print axioms ProofFile.Honest.K4.k4_played_fits
#print axioms ProofFile.Honest.K4.rowsNorms_length
#print axioms ProofFile.Honest.K4.coin_tape
#print axioms ProofFile.Honest.K4.k4_coin_tape
