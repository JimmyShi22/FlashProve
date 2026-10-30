-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K4/Law/ValuesAtMember.lean: CONDITIONAL.

What is here. On the road on shapes (Johnson/AtFull/Shape/) a member of the first chain owes, beside its step on the state's shape,
one thing: its test on values says yes at what the prover's side has played: `Values` (Honest/Thread/Shape.lean), or the weaker
`ValuesJ` (Honest/Thread/ShapeJV.lean). At the member of the feed-forward layers' own rounds (sub-protocol K4) the table's test is
`k4ValsV p s rs` (Johnson/AtFull/Shape/K4Fit.lean), three Bools:
  (i)   `tokensFit`: in the first group alone: the tokens that the state holds are as many as the plan says, each below the
        vocabulary's size. It reads the request, no sent and no sampled value.
  (ii)  `mergedB` at what the state's reading `S.look?` returns: where both readings of points return, every call's point ends as the
        lookup's own. It says yes where a reading fails, and the clause says yes where `S.look?` returns nothing.
  (iii) `coinB` at the tape of the rounds: the tape has the first round of the second token sumcheck, and no element sampled in it
        is 0.
THE MEMBER's TEST ON VALUES READS NO VALUE THAT K4's SIDE SENDS: (i) reads the request, (ii) what the lookup heard, (iii) one challenge. A side
that sends false values of the right shape meets the statements here as well as the honest one.
Here: `Values` AT THAT MEMBER, general in the thread T and in the shape Zs, FROM: the seat (`K4SeatedA`, Law/SeatedA.lean) · hRd: wherever
the thread stands in front of the member, (i) and (ii) hold: JUST THE TWO Bools, nothing more · hf: where the table of falls is silent at
the member, so is the honest side's own test on that one sampled element (`k4CoinZero`, Honest/K4/Part.lean): (iii) HANGS ON A SAMPLED
ELEMENT, SO IT IS A FALL's · hcell: the shape's test at the member is `k4ValsV p`.

  `paired_drawn_at`   what round number n of a tape has sampled
  `fitsAll_round_at`  rounds that fit K4's table have a round at each row's number, and it fits the row. Kin: the library's
                      `fitsAll_at` and `fitsAll_length` (Johnson/Desc/First/K4/BlockLaws.lean) have the fit where row, entry and round are
                      all given, and the lengths; here the round is found
  `epsilon_row`       the row of K4's table behind the rows of the hearing's first part: one element is sampled
  **`coinB_of_silent`**   (iii), at rounds that fit the table and whose challenges are ds, where `k4CoinZero Q ds` says nothing
  **`k4_values_of_tests`**   `Values T Zs fall b`
  `k4_valuesJ_of_tests`   so `ValuesJ T Said J Zs fall b`, at every Said and J (`valuesJ_of`)

Limits. THAT THE PREMISES CAN BE MET TOGETHER: no example has been through Lean. At a fall that always speaks, a side that always stops, or a
thread that stands nowhere, the statements are idle. `k4CoinZero` says nothing where the challenge is lacking or holds no element, and
`coinB` is false there: the two are brought together by the fit of the rounds, which `Values` hands over as "the challenges fit the member's
declared rounds". The free-slot test is not among K4's member's tests on values: it stands at another member. Nothing on what any value is
worth.
No property is claimed.
A LAW, NOT A PART: by a reader's walk of import lines its imports reach modules under Johnson/Goal/: no file that defines a part of the proof
file's description may import this one.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.HearsSeated
import Johnson.Desc.ProofFile.Honest.Thread.ShapeJV
import Johnson.AtFull.Shape.K4Fit

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes (isZeroE)
open OnBytes.Model (RoundName)
open OnBytes.K.Kc (paired)
open OnBytes.Desc.First.K4 (Par Rd rounds entries)
open OnBytes.Desc.First.K4.RtPub (tokensFit)
open OnBytes.Desc.First.K4.Rt (rowsNorms rowsTerms rounds_eq coinB)
open OnBytes.Desc.First.K4.Honest
open Johnson.AtFull.Shape (k4ValsV mergedB)
open VerifiableInference.Desc (Block Claim First.S noDigest)

/-- What round number n of a tape has sampled. -/
theorem paired_drawn_at : ∀ (rs : List Fmt.RoundView) (es : List Fmt.Entry) (n : Nat),
    ((paired rs es)[n]?).map (·.drawn) = (rs[n]?).map fun r => r.drawn.elems.map OnBytes.E.ofTriple
  | [], _, _ => by simp [paired]
  | _ :: _, [], 0 => rfl
  | _ :: _, _ :: _, 0 => rfl
  | _ :: rs, [], n + 1 => by
    simp only [paired, List.getElem?_cons_succ]
    exact paired_drawn_at rs [] n
  | _ :: rs, _ :: es, n + 1 => by
    simp only [paired, List.getElem?_cons_succ]
    exact paired_drawn_at rs es n

/-- Rounds that fit a table fit it row by row. -/
theorem fitsAll_round_at (L : List Rd) : ∀ (es : List Fmt.Entry) (rs : List Fmt.RoundView) (n : Nat) (d : Rd),
    OnBytes.Desc.First.K4.fitsAll L es rs = true → L[n]? = some d → ∃ e r, rs[n]? = some r ∧ d.fits e r = true := by
  induction L with
  | nil =>
    intro es rs n d _ hd
    simp at hd
  | cons d0 L ih =>
    intro es rs n d h hd
    cases es with
    | nil => cases rs <;> simp [OnBytes.Desc.First.K4.fitsAll] at h
    | cons e es =>
      cases rs with
      | nil => simp [OnBytes.Desc.First.K4.fitsAll] at h
      | cons r rs =>
        have h' : (d0.fits e r && OnBytes.Desc.First.K4.fitsAll L es rs) = true := h
        rw [Bool.and_eq_true] at h'
        cases n with
        | zero =>
          obtain rfl : d0 = d := by simpa using hd
          exact ⟨e, r, rfl, h'.1⟩
        | succ n =>
          obtain ⟨e', r', h1, h2⟩ := ih es rs n d h'.2 (by simpa using hd)
          exact ⟨e', r', by simpa using h1, h2⟩

/-- The row of K4's table behind the rows of the hearing's first part. -/
theorem epsilon_row (P : OnBytes.Model.Layer.Pub) (hp : OnBytes.Model.Layer.HPlan2) (g : Nat) :
    (rounds P hp g)[(rowsNorms P g).length]? = some { name := .pscEpsilon, sent := 2 } := by
  rw [rounds_eq, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  simp [rowsTerms, OnBytes.Desc.First.K4.masked]

/-- **Where the honest side's own test on the sampled element says nothing, the table's test on the coin accepts**, at rounds R
that fit K4's table and whose challenges are ds. -/
theorem coinB_of_silent (Q : K4Pub) (hp : OnBytes.Model.Layer.HPlan2) (ds : List Fmt.Drawn) (R : List Fmt.RoundView)
    (hR : ∀ n : Nat, (R[n]?).map Fmt.RoundView.drawn = ds[n]?) (hz : k4CoinZero Q ds = none) (es : List Fmt.Entry)
    (hfit : OnBytes.Desc.First.K4.fitsAll (rounds Q.P hp Q.g) es (R.map noDigest) = true) :
    coinB Q.P Q.g (paired (R.map noDigest) es) = true := by
  obtain ⟨e, r', hr', hf⟩ := fitsAll_round_at _ _ _ _ _ hfit (epsilon_row Q.P hp Q.g)
  rw [List.getElem?_map] at hr'
  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.1 hr'
  unfold Rd.fits at hf
  simp only [Bool.and_eq_true, beq_iff_eq] at hf
  obtain ⟨⟨⟨⟨-, -⟩, -⟩, h4⟩, -⟩ := hf.1
  have hd1 : r.drawn.elems.length = 1 := h4
  have hpd := paired_drawn_at (R.map noDigest) es (rowsNorms Q.P Q.g).length
  rw [List.getElem?_map, hr] at hpd
  have q := hR (rowsNorms Q.P Q.g).length
  rw [hr] at q
  unfold k4CoinZero at hz
  rw [k4_starts] at hz
  have hz' : (match ds[rJ3 Q.P Q.g]? with
    | some d =>
      if isZeroE ((d.elems.head?.map OnBytes.E.ofTriple).getD OnBytes.oneE) then
        some _
      else none
    | none => none) = none := hz
  rw [← rowsNorms_length, ← q] at hz'
  have hz'' : (if isZeroE ((r.drawn.elems.head?.map OnBytes.E.ofTriple).getD OnBytes.oneE) then
      some _
    else none) = none := hz'
  unfold coinB
  cases ht : (paired (R.map noDigest) es)[(rowsNorms Q.P Q.g).length]? with
  | none =>
    rw [ht] at hpd
    simp at hpd
  | some fr =>
    rw [ht] at hpd
    have e1 : fr.drawn = r.drawn.elems.map OnBytes.E.ofTriple := Option.some.inj hpd
    show (fr.drawn.all fun e => !isZeroE e) = true
    rw [e1]
    cases he : r.drawn.elems with
    | nil =>
      rw [he] at hd1
      simp at hd1
    | cons x xs =>
      have hxs : xs = [] := by
        rw [he] at hd1
        simpa using hd1
      subst hxs
      rw [he] at hz''
      have hz3 : (if isZeroE (OnBytes.E.ofTriple x) then
          some _
        else none) = none := hz''
      cases hb : isZeroE (OnBytes.E.ofTriple x) with
      | false => simp [hb]
      | true =>
        rw [hb] at hz3
        cases hz3

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb : Type}
  {T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb} {b : Nat}
  {cells : Tr → Cells} {weights : W₀ → Weights} {tokens : Xi → Array Nat}
  {look : K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard} {Q : K4Pub} {p : Par}
  {blk₀ : Block First.S Claim} {fall : Nat → First.S → List Fmt.Drawn → Option String}

/-- **THE MEMBER's TEST ON VALUES SAYS YES AT WHAT THE SIDE HAS PLAYED.** CONDITIONAL on the seat Se, on hRd, hf and hcell. -/
theorem k4_values_of_tests (Zs : Shape First.S) (Se : K4SeatedA T b cells weights tokens look Q p blk₀)
    (hRd : ∀ k s m E, Thr T b k s m E → tokensFit { p.P with tokv := s.tokv } p.g = true ∧
      (s.look?.all fun fo => mergedB p.P fo) = true)
    (hf : ∀ s ds, fall b s ds = none → k4CoinZero Q ds = none)
    (hcell : ∀ s rs gs, Zs.vals b s rs gs = k4ValsV p s rs) : Values T Zs fall b := by
  intro blk hblk k s m E ds y cols hA hd _ hfl hM
  obtain rfl : blk₀ = blk := Option.some.inj (Se.member.symm.trans hblk)
  rw [hcell]
  obtain ⟨htk, hmg⟩ := hRd k s m E hA
  have hfit := (k4_played_fits Se hM hd).1
  obtain ⟨⟨l, _, hy⟩, _⟩ := hM
  obtain ⟨eP, _, eg, _, _⟩ := Se.own
  unfold k4ValsV
  simp only [Bool.and_eq_true]
  refine ⟨⟨htk, hmg⟩, ?_⟩
  rw [eP, eg] at hfit ⊢
  exact coinB_of_silent Q p.hp ds (roundsOf y.1) (played_drawn hy) (hf s ds hfl) _ hfit

/-- The weaker form, at every Said and J. CONDITIONAL as `k4_values_of_tests`. -/
theorem k4_valuesJ_of_tests (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop) (J : Nat → First.S → Prop)
    (Zs : Shape First.S) (Se : K4SeatedA T b cells weights tokens look Q p blk₀)
    (hRd : ∀ k s m E, Thr T b k s m E → tokensFit { p.P with tokv := s.tokv } p.g = true ∧
      (s.look?.all fun fo => mergedB p.P fo) = true)
    (hf : ∀ s ds, fall b s ds = none → k4CoinZero Q ds = none)
    (hcell : ∀ s rs gs, Zs.vals b s rs gs = k4ValsV p s rs) : ValuesJ T Said J Zs fall b :=
  valuesJ_of T Said (k4_values_of_tests Zs Se hRd hf hcell)

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.paired_drawn_at
#print axioms ProofFile.Honest.K4.fitsAll_round_at
#print axioms ProofFile.Honest.K4.epsilon_row
#print axioms ProofFile.Honest.K4.coinB_of_silent
#print axioms ProofFile.Honest.K4.k4_values_of_tests
#print axioms ProofFile.Honest.K4.k4_valuesJ_of_tests
