-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Hears/Shaped.lean: ROOM AND SHAPE: THE HEARING RETURNS. Rounds of
the make of the output head's own table of rounds are heard by the verifier's text, whatever they
hold, from a ledger with room. Statements and proofs ON THE VERIFIER's TEXT; no prover is in this
file, and no goal is stated.

Why. Whether the hearing returns holds no value: it reads how many scalars a round sends and how
many elements it draws, and whether the ledger has free numbers. So "the honest side's rounds are
heard" falls into two: this file, which needs no player; and "the rounds that the honest side plays
are of that make", which is not here.

  `varRounds_shaped`, `reads_shaped`   **of the shape alone the part's reader returns**: the
                    caller's scalars, the variables' rounds, the end values, each in its number
  `varRound_counts`   the variables' rounds and the round in the further variable send two scalars
                    and sample one element
  `sumcheck_shaped`   room and shape: a masked sumcheck that sends its claimed sum is heard
  `level_shaped`    the like for a sum that is not sent, where the form that it must equal has a
                    public part at the ledger in front
  `shaped_member`, `shaped_split`, `shaped_single`, `rounds_bracketed`   the shape has a member at
                    every table; the shape of a list that is laid together of two; of one round; the
                    table of rounds, bracketed part by part
  `hears_shaped`    **ROOM AND SHAPE: THE HEAD's HEARING RETURNS**: from a well laid ledger with
                    room for the sub-protocol's 41 + 8 lt + 4 lPd scalars and m more, where the
                    lookup's point on the positions has lt coordinates: all rounds are used up; the
                    ledger behind is well laid, its next free number has moved on by just that
                    count, it has as many numbers in
                    all and has room for m more; the point on the positions and the four sumchecks'
                    challenges have their lengths

Limits. CONDITIONAL ON ROOM, ON THE LEDGER's MAKE AND ON zt's LENGTH: that the ledger at a state of
a run is well laid and has room (`WellLaid`, `Fresh`: Johnson/Desc/Kinds/HeadLaw.lean,
Law/Returns.lean) is shown here of no state. THE ROOM THAT IS ASKED IS THE LIBRARY's OWN PREMISE, to
the number (`Fresh F (41 + 8 * lt + 4 * lPd)`: Law/K06Honest.lean, Law/K06HonestWhole.lean); the
count is `hear_takes_plan`'s (Law/Takes.lean). MEMBERS: the shape has one at every table
(`shaped_member`); of the two premises on the ledger none is laid here: the library has a ledger
with room at a small toy's state (`fresh_K`, Law/K06ToyRecord.lean), and both premises have code
(`wellLaidB`, Law/K6OnB.lean; `roomB_iff`, Law/K06Honest.lean). The shape is `ShapedNZ`
(Johnson/Desc/Kinds/Law/K06EveryList.lean):
each round is made of scalars and sampled elements alone, with no sealed digest: a step
strikes the digest before its decision sees the rounds, so whoever wants the hearing there asks the
shape of the rounds with the digests struck. Of that shape's clause on the element that is never 0
nothing is used here. THAT THE HONEST SIDE's ROUNDS HAVE THE SHAPE IS NOT SHOWN. Nothing on what was
heard but the five lengths; nothing on the decision's other tests or on the step. Called, not typed
anew: `heardBy_returns`, `sendThenBatch_returns`, `drawPoint_returns`, `round_returns`
(Law/Returns.lean), `publicPart_claimed` (Law/HonestParts.lean), `publicPart_returns` and the lemmas
on filled slots (Law/PublicPart.lean), `norm_glue` (Law/HeadSends.lean), `all_rests`
(Law/NormSends.lean), `roundOf_of` (Johnson/Desc/Part/MaskedSumHonest.lean), `own_callOf`
(Law/Takes.lean), `hide_unfold` (Law/LedgerAt.lean), `batch_spec` (Law/NormHear.lean),
`wl_sendThenBatch`, `wl_sumcheck`, `wl_level`, `bind_eq` (Law/Cut.lean), `consumes_sumcheck`,
`consumes_norm` (Law/Consumes.lean), `Fresh.less` (Law/Returns.lean). SOME SHORT RUNS OF LINES
FOLLOW THE LIBRARY's OWN PROOFS LINE BY LINE, because they stand there inside proofs on honest
rounds and are no lemmas: that the batched squares' start form has a public part behind the nine
scalars, with the four lines in front of it (`norm_front`, Law/NormSends.lean); that laying no
scalar leaves the ledger as it is, the bracketing of a level's table and the closing lines of
`level_shaped` (`level_honest`, Law/HonestParts.lean); the closing lines of `sumcheck_shaped`
(`sumcheck_honest`, same file).
Nothing on any property.

-/
import Johnson.Desc.Kinds.Law.K06EveryList
import Johnson.Desc.Kinds.Law.Returns
import Johnson.Desc.Kinds.Law.Takes
import Johnson.Desc.Kinds.Law.HonestParts
import Johnson.Desc.Kinds.Law.HeadSends
import Johnson.Desc.Kinds.Law.NormSends
import Johnson.Desc.Kinds.Law.PublicPart
import Johnson.Desc.Part.MaskedSumHonest

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace ProofFile.Honest.K6.Hears
open OnBytes (E zeroE oneE)
open OnBytes.Model (Fork)
open VerifiableInference.Desc.Kinds
open VerifiableInference.Desc.Kinds.Head (HeardAll)
open VerifiableInference.Desc.Kinds.Head.Law (ShapedNZ callOf WellLaid Fresh hidOf heardRec
  all_rests zS)
open VerifiableInference.Desc.Kinds.Head.Law.Came (bind_eq)
open VerifiableInference.Desc.Part.MaskedSum (Var Call Read rvOf roundOf roundOf_of varRounds
  readAll firstRound leadScalars challenges ownSlots)

/-! ## 1 Of the shape alone the part's reader returns -/

/-- The variables' rounds are read, of their shape alone. -/
theorem varRounds_shaped : ∀ (vs : List Var) (t : List Fmt.RoundView) (Rs : List Round), ShapedNZ t Rs →
    vs.length = Rs.length → (∀ v ∈ vs, v.d = 3) → (∀ R ∈ Rs, R.sent = 2 ∧ R.drawn = 1) →
    ∀ rest, ∃ l, varRounds vs (t ++ rest) = some (l, rest) ∧ l.length = vs.length
  | [], _, _, .nil, _, _, _, _ => ⟨[], rfl, rfl⟩
  | v :: vs, _, _, .cons (a := r) (b := R) (l₁ := t) (l₂ := Rs) h1 h2, hl, hv, hR, rest => by
    obtain ⟨s, d, rfl, hs, hd, _⟩ := h1
    obtain ⟨r2, r1⟩ := hR R List.mem_cons_self
    rw [r2] at hs
    rw [r1] at hd
    obtain ⟨g, rfl⟩ := List.length_eq_one_iff.1 hd
    obtain ⟨l, e, el⟩ := varRounds_shaped vs t Rs h2 (by simpa using hl)
      (fun v' h' => hv v' (List.mem_cons_of_mem _ h'))
      (fun R' h' => hR R' (List.mem_cons_of_mem _ h')) rest
    have hr : roundOf (v.d - 1) 1 (rvOf s [g]) = some (s, [g]) := by
      rw [hv v List.mem_cons_self]
      have := roundOf_of s [g]
      rw [hs] at this
      exact this
    refine ⟨(s, g) :: l, ?_, by simp [el]⟩
    show varRounds (v :: vs) (rvOf s [g] :: (t ++ rest)) = _
    simp only [varRounds, hr, e]
  | [], _, _, .cons _ _, hl, _, _, _ => by simp at hl
  | _ :: _, _, _, .nil, hl, _, _, _ => by simp at hl

/-- **OF THE SHAPE ALONE THE PART's READER RETURNS**: a first round with lead + 1 scalars and one
drawn element; a round with two scalars and one drawn element for each coordinate of z and one more;
a last round with the end values and no draw. -/
theorem reads_shaped (lead ends : Nat) (z : Point) (t : List Fmt.RoundView) (R0 Re : Round)
    (Rv : List Round) (h0 : R0.sent = lead + 1 ∧ R0.drawn = 1) (hn : Rv.length = z.size + 1)
    (hv : ∀ R ∈ Rv, R.sent = 2 ∧ R.drawn = 1) (he : Re.sent = ends ∧ Re.drawn = 0)
    (h : ShapedNZ t (R0 :: (Rv ++ [Re]))) :
    t.length = z.size + 3 ∧ ∃ (ld : List E) (R : Read),
      leadScalars (callOf lead z ends) t = some ld ∧ ld.length = lead ∧
      readAll (callOf lead z ends) t = some R ∧ R.values.length = ends ∧
      R.rounds.length = z.size + 1 := by
  cases h with
  | cons h1 h2 =>
    rename_i r0 t1
    obtain ⟨s0, d0, rfl, hs0, hd0, _⟩ := h1
    rw [h0.1] at hs0
    rw [h0.2] at hd0
    obtain ⟨eps, rfl⟩ := List.length_eq_one_iff.1 hd0
    have ha := List.forall₂_take_append t1 Rv [Re] h2
    have hb := List.forall₂_drop_append t1 Rv [Re] h2
    have ht1 : t1 = t1.take Rv.length ++ t1.drop Rv.length := (List.take_append_drop _ _).symm
    generalize t1.take Rv.length = ta at ha ht1
    generalize t1.drop Rv.length = tb at hb ht1
    cases hb with
    | cons hb1 hb2 =>
      cases hb2
      rename_i rv
      obtain ⟨sv, dv, rfl, hsv, hdv, _⟩ := hb1
      rw [he.1] at hsv
      rw [he.2] at hdv
      obtain rfl := List.length_eq_zero_iff.1 hdv
      subst ht1
      have hall : (callOf lead z ends).all = z.toList.map (Var.point · 3) ++ [Var.point zeroE 3] :=
        rfl
      obtain ⟨l, e, el⟩ := varRounds_shaped (callOf lead z ends).all ta Rv ha
        (by rw [hall, hn]; simp)
        (fun v hvm => by
          rw [hall] at hvm
          rcases List.mem_append.1 hvm with hm | hm
          · obtain ⟨x, _, rfl⟩ := List.mem_map.1 hm
            rfl
          · rw [List.mem_singleton.1 hm]
            rfl) hv [rvOf sv []]
      have hla : ta.length = Rv.length := ha.length_eq
      have hr0 : roundOf (lead + 1) 1 (rvOf s0 [eps]) = some (s0, [eps]) := by
        have := roundOf_of s0 [eps]
        rw [hs0] at this
        exact this
      have hre : roundOf ends 0 (rvOf sv []) = some (sv, []) := by
        have := roundOf_of sv []
        rw [hsv] at this
        exact this
      obtain ⟨mu, hmu⟩ : ∃ mu, s0.drop lead = [mu] :=
        List.length_eq_one_iff.1 (by rw [List.length_drop, hs0]; omega)
      refine ⟨by simp [hla, hn], s0.take lead, ⟨mu, eps, l, sv⟩, ?_, ?_, ?_, hsv, ?_⟩
      · show ((firstRound (callOf lead z ends) (rvOf s0 [eps])).map (·.1)) = _
        show (((roundOf (lead + 1) 1 (rvOf s0 [eps])).map fun x =>
          (x.1.take lead, x.1.drop lead, x.2)).map (·.1)) = _
        rw [hr0]
        rfl
      · rw [List.length_take, hs0]
        omega
      · show readAll ⟨lead, z.toList.map (Var.point · 3), some ⟨2, ends⟩⟩
          (rvOf s0 [eps] :: (ta ++ [rvOf sv []])) = _
        have e' : varRounds (Call.all ⟨lead, z.toList.map (Var.point · 3), some ⟨2, ends⟩⟩)
            (ta ++ [rvOf sv []]) = some (l, [rvOf sv []]) := e
        simp only [readAll, firstRound, hr0, Option.map_some, hmu, e', hre]
      · rw [el, hall]
        simp

/-! ## 2 Room and shape: one sumcheck -/

/-- The variables' rounds and the round in the further variable send two scalars and draw one
element. -/
theorem varRound_counts (n : Nat) :
    ∀ R ∈ List.replicate n (⟨"PSC round", 2, 1, false, 0⟩ : Round) ++ [⟨"PSC Y", 2, 1, true, 0⟩],
      R.sent = 2 ∧ R.drawn = 1 := by
  intro R hR
  rcases List.mem_append.1 hR with h | h
  · rw [(List.mem_replicate.1 h).2]
    exact ⟨rfl, rfl⟩
  · rw [List.mem_singleton.1 h]
    exact ⟨rfl, rfl⟩

/-- **ROOM AND SHAPE: A SUMCHECK THAT SENDS ITS CLAIMED SUM IS HEARD.** -/
theorem sumcheck_shaped (z : Point) {n : Nat} (hn : 1 ≤ n) {F : Fork} {m : Nat} (hW : WellLaid F)
    (hF : Fresh F (1 + (2 * z.size + 3 + n + m))) (t : List Fmt.RoundView)
    (h : ShapedNZ t (sumcheck.rounds z.size n)) :
    ∃ (S : Sum) (G : Fork), sumcheck z n F t = some (S, G, []) ∧ WellLaid G ∧ Fresh G m ∧
      G.next = F.next + (1 + (2 * z.size + 3 + n)) ∧ G.ns = F.ns ∧ S.r.size = z.size := by
  have eS : sumcheck.rounds z.size n = ⟨"PSC epsilon", 1 + 1, 1, false, 0⟩ ::
      ((List.replicate z.size ⟨"PSC round", 2, 1, false, 0⟩ ++ [⟨"PSC Y", 2, 1, true, 0⟩]) ++
        [⟨"PSC values", n, 0, false, 0⟩]) := by simp [sumcheck.rounds]
  rw [eS] at h
  obtain ⟨hlen, ld, R, hld, hll, hR, hv, hrl⟩ := reads_shaped 1 n z t _ _ _ ⟨rfl, rfl⟩ (by simp)
    (varRound_counts z.size) ⟨rfl, rfl⟩ h
  obtain ⟨c0, rfl⟩ := List.length_eq_one_iff.1 hll
  have hown := Head.Law.own_callOf 1 z n
  obtain ⟨T, es, Fa, F1, _, _, a2, a3, a4, a5⟩ := Head.Law.heardBy_returns 1
    (fun c => (c.getD 0 {}).var) z hn hlen hld hR hv (m := m) (F := F)
    (by rw [hown]; exact hF)
    (fun Fa hh => ⟨_, Head.Law.publicPart_claimed hW c0 (m := 2 * z.size + 3 + n + m) hF Fa hh⟩) []
  rw [List.append_nil] at a2
  have hs : ∃ S : Sum, sumcheck z n F t = some (S, F1, []) ∧ S.r.size = z.size := by
    unfold sumcheck
    rw [bind_eq a2]
    refine ⟨_, rfl, ?_⟩
    simp [challenges, Head.Law.heardRec, Head.Law.callOf, hrl]
  obtain ⟨S, hs, hsz⟩ := hs
  refine ⟨S, F1, hs, Head.Law.Came.wl_sumcheck _ _ _ _ _ _ _ hW hs, a5, ?_, a4, hsz⟩
  rw [a3, hown]
  show F.next + 1 + (2 * z.size + 3) + n = _
  omega

/-- **ROOM AND SHAPE: A SUMCHECK OF A SUM THAT IS NOT SENT IS HEARD**, where the form that the sum
must equal has a public part at the ledger in front. -/
theorem level_shaped (z : Point) (start : Form) {F : Fork} {m : Nat} (hW : WellLaid F)
    (hF : Fresh F (2 * z.size + 3 + 2 + m)) (hT : ∃ T, F.publicPart start = some T)
    (t : List Fmt.RoundView) (h : ShapedNZ t (level.rounds z.size)) :
    ∃ (S : Sum) (G : Fork), level z start F t = some (S, G, []) ∧ WellLaid G ∧ Fresh G m ∧
      G.next = F.next + (2 * z.size + 3 + 2) ∧ G.ns = F.ns ∧ S.r.size = z.size := by
  have eL : level.rounds z.size = (⟨"PSC epsilon", 0 + 1, 1, false, 0⟩ ::
      ((List.replicate z.size ⟨"PSC round", 2, 1, false, 0⟩ ++ [⟨"PSC Y", 2, 1, true, 0⟩]) ++
        [⟨"PSC values", 2, 0, false, 0⟩])) ++ [⟨"LINE", 0, 1, false, 0⟩] := by simp [level.rounds]
  rw [eL] at h
  generalize hL : ((⟨"PSC epsilon", 0 + 1, 1, false, 0⟩ : Round) ::
      ((List.replicate z.size ⟨"PSC round", 2, 1, false, 0⟩ ++ [⟨"PSC Y", 2, 1, true, 0⟩]) ++
        [⟨"PSC values", 2, 0, false, 0⟩])) = L1 at h
  have ha := List.forall₂_take_append t L1 _ h
  have hb := List.forall₂_drop_append t L1 _ h
  have ht : t = t.take L1.length ++ t.drop L1.length := (List.take_append_drop _ _).symm
  generalize t.take L1.length = ta at ha ht
  generalize t.drop L1.length = tb at hb ht
  rw [← hL] at ha
  cases hb with
  | cons hb1 hb2 =>
    cases hb2
    obtain ⟨sl, dl, rfl, hsl, hdl, _⟩ := hb1
    obtain rfl := List.length_eq_zero_iff.1 hsl
    obtain ⟨g, rfl⟩ := List.length_eq_one_iff.1 hdl
    subst ht
    obtain ⟨hlen, ld, R, hld, hll, hR, hv, hrl⟩ := reads_shaped 0 2 z ta _ _ _ ⟨rfl, rfl⟩ (by simp)
      (varRound_counts z.size) ⟨rfl, rfl⟩ ha
    obtain rfl := List.length_eq_zero_iff.1 hll
    have hown := Head.Law.own_callOf 0 z 2
    obtain ⟨T, es, Fa, F1, _, _, a2, a3, a4, a5⟩ := Head.Law.heardBy_returns 0 (fun _ => start) z
      (by omega : 1 ≤ 2) hlen hld hR hv (m := m) (F := F)
      (by
        rw [hown]
        show Fresh F (0 + (2 * z.size + 3 + 2 + m))
        rw [Nat.zero_add]
        exact hF)
      (fun Fa hh => by
        obtain ⟨run, _⟩ := Head.Law.hide_unfold hh
        have h0 : ({ F with next := F.next + ([] : List E).length } : Fork).hideRun F.next
            ([] : List E).toArray oneE =
            some ({ F with next := F.next + ([] : List E).length } : Fork) := by
          simp [Fork.hideRun]
        rw [h0] at run
        rw [← Option.some.inj run]
        exact hT) [rvOf [] [g]]
    have hs : ∃ S : Sum, level z start F (ta ++ [rvOf [] [g]]) = some (S, F1, []) ∧
        S.r.size = z.size := by
      unfold level
      rw [bind_eq a2]
      dsimp only
      rw [bind_eq (show Hear.round 0 1 F1 (rvOf [] [g] :: []) = some (([], [g]), F1, [])
        from Head.Law.round_returns [] [g] F1 [])]
      refine ⟨_, rfl, ?_⟩
      simp [challenges, Head.Law.heardRec, Head.Law.callOf, hrl]
    obtain ⟨S, hs, hsz⟩ := hs
    refine ⟨S, F1, hs, Head.Law.Came.wl_level _ _ _ _ _ _ _ hW hs, a5, ?_, a4, hsz⟩
    rw [a3, hown]
    show F.next + 0 + (2 * z.size + 3) + 2 = _
    omega

/-! ## 3 The whole hearing -/

/-- THE SHAPE HAS A MEMBER AT EVERY TABLE: each round sends zeros and draws ones. -/
theorem shaped_member : ∀ Rs : List Round, ShapedNZ
    (Rs.map fun R => rvOf (List.replicate R.sent zeroE) (List.replicate R.drawn oneE)) Rs
  | [] => .nil
  | R :: Rs => .cons ⟨_, _, rfl, List.length_replicate, List.length_replicate, fun x hx => by
      rw [List.eq_of_mem_replicate (List.mem_of_mem_drop hx)]
      rfl⟩ (shaped_member Rs)

/-- The shape of a list against two tables laid together: it falls into two. -/
theorem shaped_split {rs : List Fmt.RoundView} {A B : List Round} (h : ShapedNZ rs (A ++ B)) :
    ∃ a b, rs = a ++ b ∧ ShapedNZ a A ∧ ShapedNZ b B :=
  ⟨rs.take A.length, rs.drop A.length, (List.take_append_drop _ _).symm,
    List.forall₂_take_append rs A B h, List.forall₂_drop_append rs A B h⟩

/-- The shape against one round of the table. -/
theorem shaped_single {a : List Fmt.RoundView} {R : Round} (h : ShapedNZ a [R]) :
    ∃ s d, a = [rvOf s d] ∧ s.length = R.sent ∧ d.length = R.drawn := by
  cases h with
  | cons h1 h2 =>
    cases h2
    obtain ⟨s, d, rfl, hs, hd, _⟩ := h1
    exact ⟨s, d, rfl, hs, hd⟩

section Head
variable [Head.Sizes] [Head.Policy] [Head.Request] [Head.Token] [FinalNorm.In] [Head.In]

/-- The sub-protocol's table of rounds, bracketed part by part. -/
theorem rounds_bracketed : (Head.rounds : List Round) = drawPoint.rounds Norm.lt ++
    (sendThenBatch.rounds 9 9 ++ (level.rounds (Norm.lPd + Norm.lt) ++ (sendThenBatch.rounds 7 7 ++
      (sumcheck.rounds Norm.lt 4 ++ (sumcheck.rounds Norm.lt 2 ++
        sumcheck.rounds (Norm.lt + Norm.lPd) 2))))) := by
  show drawPoint.rounds Norm.lt ++ sendThenBatch.rounds 9 9 ++ [] ++
    level.rounds (0 + Norm.lPd + Norm.lt) ++
    sendThenBatch.rounds 7 7 ++ sumcheck.rounds Norm.lt 4 ++ sumcheck.rounds Norm.lt 2 ++
    sumcheck.rounds (Norm.lt + Norm.lPd) 2 = _
  rw [Nat.zero_add]
  simp only [List.append_assoc, List.append_nil]

/-- **ROOM AND SHAPE: THE HEAD's HEARING RETURNS.** m: how many free numbers are left behind it. The
letters of the policy, the request, the token and the head's own lookup stand among the variables
because lemmas of the library that are called here have them so; the statement names none of them.
-/
theorem hears_shaped {F : Fork} {m : Nat} (hW : WellLaid F)
    (hF : Fresh F (41 + 8 * Norm.lt + 4 * Norm.lPd + m)) (hzt : (FinalNorm.zt).size = Norm.lt)
    (rs : List Fmt.RoundView) (h : ShapedNZ rs Head.rounds) :
    ∃ (H : HeardAll) (G : Fork), Head.hear F rs = some (H, G, []) ∧ WellLaid G ∧ Fresh G m ∧
      G.next = F.next + (41 + 8 * Norm.lt + 4 * Norm.lPd) ∧ G.ns = F.ns ∧
      H.1.pV.size = Norm.lt ∧ H.1.squares.r.size = Norm.lPd + Norm.lt ∧
      H.1.products.r.size = Norm.lt ∧
      H.2.1.normed.r.size = Norm.lt ∧ H.2.2.logits.r.size = Norm.lt + Norm.lPd := by
  rw [rounds_bracketed] at h
  obtain ⟨t0, u0, rfl, s0, h⟩ := shaped_split h
  obtain ⟨t1, u1, rfl, s1, h⟩ := shaped_split h
  obtain ⟨tS, u2, rfl, sS, h⟩ := shaped_split h
  obtain ⟨t2, u3, rfl, s2, h⟩ := shaped_split h
  obtain ⟨tP, u4, rfl, sP, h⟩ := shaped_split h
  obtain ⟨tN, tL, rfl, sN, sL⟩ := shaped_split h
  obtain ⟨e0, pts, rfl, he0, hpts⟩ := shaped_single s0
  obtain rfl := List.length_eq_zero_iff.1 he0
  have hpts' : pts.length = Norm.lt := hpts
  obtain ⟨v9, d1, rfl, hv9, hd1⟩ := shaped_single s1
  have hv9' : v9.length = 9 := hv9
  obtain ⟨gam, rfl⟩ := List.length_eq_one_iff.1 hd1
  obtain ⟨v7, d2, rfl, hv7, hd2⟩ := shaped_single s2
  have hv7' : v7.length = 7 := hv7
  obtain ⟨om, rfl⟩ := List.length_eq_one_iff.1 hd2
  -- the point
  have h0 : drawPoint Norm.lt F [rvOf [] pts] = some (pts.toArray, F, []) := by
    have := Head.Law.drawPoint_returns pts F []
    rwa [hpts'] at this
  have hpV : (pts.toArray : Point).size = Norm.lt := by rw [List.size_toArray, hpts']
  have hzS : (zS pts.toArray).size = Norm.lPd + Norm.lt := by simp [zS, halves, hpV]
  -- the nine scalars
  obtain ⟨Fa, h1, a1, a2, a3, a4⟩ := Head.Law.sendThenBatch_returns v9 gam 9 (F := F)
    (m := 32 + 8 * Norm.lt + 4 * Norm.lPd + m) (by rw [hv9']; exact hF.less (by omega)) []
  rw [hv9'] at h1 a1 a4
  have wa : WellLaid Fa := Head.Law.Came.wl_sendThenBatch _ _ _ _ _ _ _ hW h1
  obtain ⟨b1, _, _⟩ := Head.Law.batch_spec hW h1
  have hT : ∃ T, Fa.publicPart (Norm.squaresStart (hidOf F.next v9) gam #[]) = some T := by
    apply Head.Law.publicPart_returns
    unfold Norm.squaresStart
    refine Head.Law.slotsFilled_smul _ (Head.Law.slotsFilled_sumTo _ _ fun i hi =>
      Head.Law.slotsFilled_sumTo _ _ fun s hs => Head.Law.slotsFilled_smul _ ?_)
    have hi0 : i = 0 := Nat.lt_one_iff.mp hi
    subst hi0
    rw [Nat.mul_zero, Nat.zero_add, b1 s hs]
    refine Head.Law.slotsFilled_slot ?_ ?_
    · rw [a2]
      have := hF.1
      omega
    · rw [a4, if_pos ⟨by omega, by omega⟩]
  -- the first sumcheck
  obtain ⟨S4, Fb, h3, wb, fb, nb, eb, z4⟩ := level_shaped (zS pts.toArray)
    (Norm.squaresStart (hidOf F.next v9) gam #[]) (m := 27 + 6 * Norm.lt + 2 * Norm.lPd + m) wa
    (by rw [hzS]; exact a3.less (by omega)) hT tS (by rw [hzS]; exact sS)
  -- the seven scalars
  obtain ⟨Fc, h4, c1, c2, c3, _⟩ := Head.Law.sendThenBatch_returns v7 om 7 (F := Fb)
    (m := 20 + 6 * Norm.lt + 2 * Norm.lPd + m) (by rw [hv7']; exact fb.less (by omega)) []
  rw [hv7'] at h4 c1
  have wc : WellLaid Fc := Head.Law.Came.wl_sendThenBatch _ _ _ _ _ _ _ wb h4
  -- the three later sumchecks
  obtain ⟨S6, G1, h5, w1, f1, n1, e1, z6⟩ := sumcheck_shaped pts.toArray (n := 4) (by omega)
    (m := 12 + 4 * Norm.lt + 2 * Norm.lPd + m) wc (by rw [hpV]; exact c3.less (by omega)) tP
    (by rw [hpV]; exact sP)
  obtain ⟨S7, G2, h6, w2, f2, n2, e2, z7⟩ := sumcheck_shaped FinalNorm.zt (n := 2) (by omega)
    (m := 6 + 2 * Norm.lt + 2 * Norm.lPd + m) w1 (by rw [hzt]; exact f1.less (by omega)) tN
    (by rw [hzt]; exact sN)
  have hzL : (FinalNorm.zt ++ halves Norm.lPd).size = Norm.lt + Norm.lPd := by simp [halves, hzt]
  obtain ⟨S8, G, h7, w3, f3, n3, e3, z8⟩ := sumcheck_shaped (FinalNorm.zt ++ halves Norm.lPd)
    (n := 2) (by omega) (m := m) w2 (by rw [hzL]; exact f2.less (by omega)) tL
    (by rw [hzL]; exact sL)
  have hn := Head.Law.norm_glue h0 h1 h3 h4 h5
  refine ⟨({ pV := pts.toArray, W := hidOf F.next v9, gam := gam, rhoI := #[], squares := S4,
             P := hidOf Fb.next v7, om := om, products := S6 }, { normed := S7 },
    { logits := S8 }), G, ?_, w3, f3, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have e : [rvOf [] pts] ++ ([rvOf v9 [gam]] ++ (tS ++ ([rvOf v7 [om]] ++ (tP ++ (tN ++ tL))))) =
        ([rvOf [] pts] ++ ([rvOf v9 [gam]] ++ (tS ++ ([rvOf v7 [om]] ++ (tP ++ []))))) ++
          (tN ++ (tL ++ [])) := by simp only [List.append_assoc, List.append_nil]
    rw [e]
    unfold Head.hear
    refine (bind_eq (all_rests Head.Law.Came.consumes_norm hn _)).trans ?_
    refine (bind_eq (show FinalNorm.hear G1 (tN ++ (tL ++ [])) =
      some ({ normed := S7 }, G2, tL ++ []) from by
        unfold FinalNorm.hear
        rw [bind_eq (all_rests (Head.Law.Came.consumes_sumcheck _ _) h6 _)]
        rfl)).trans ?_
    refine (bind_eq (all_rests (Head.Law.Came.consumes_sumcheck _ _) h7 _)).trans ?_
    rfl
  · rw [n3, n2, n1, c1, nb, a1, hzS, hpV, hzt, hzL]
    omega
  · rw [e3, e2, e1, c2, eb, a2]
  · exact hpV
  · exact z4.trans hzS
  · exact z6.trans hpV
  · exact z7.trans hzt
  · exact z8.trans hzL

end Head

#print axioms varRounds_shaped
#print axioms reads_shaped
#print axioms varRound_counts
#print axioms sumcheck_shaped
#print axioms level_shaped
#print axioms shaped_member
#print axioms shaped_split
#print axioms shaped_single
#print axioms rounds_bracketed
#print axioms hears_shaped

end ProofFile.Honest.K6.Hears
