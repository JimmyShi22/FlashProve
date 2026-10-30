-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Law/HidesAtRow.lean: THE OUTPUT HEAD'S OWN ROUNDS: WHERE THE
VERIFIER'S ONE HEARING RETURNS ON THE ROUNDS OF k6Out (Plays.lean: the row's rounds as one term),
THE STRUCTURE HidesTables (Johnson/Desc/K6/Honest/TruthOfTables.lean) HOLDS OF THE PROVER'S CELLS,
THE MASK ROW, WHAT WAS HEARD AND THE LEDGER THAT THE HEARING RETURNS. What its fourteen clauses say:
HidesOfEight.lean's head.
"Hides" in this name is the ledger's word: a slot is worth a value behind a mask entry (said = value
+ mask). It is no claim that anything is hidden from a verifier.
WHAT IT IS NOT. CONDITIONAL. THAT THE HEARING RETURNS, AND LEAVES NO ROUND, IS A PREMISE. THE
LETTERS g AT WHICH THE HEARING IS READ MUST BE (wit t.input).given p t.heard, THOSE THAT THE
PROVER'S SMALL INPUT MAKES: that the verifier's own letters at its state are these, word for word,
is owed by whoever calls this at a state. Premises too: there are as many challenges as declared
rounds; the ledger is well laid; the lookup's point on the positions has lt coordinates; the mask
row, from the ledger's next number on, reads as the row's coins in the order of spending
(HidesOfEight.lean: headSpent, tied there to no text of the frame's). That the frame's play returns
k6Out is Plays.lean's k6_played, not called here; it is conditional on K6Seated, which is not shown
there of the IOP as written in Lean.
Nothing on whether the verifier accepts, on soundness, on completeness or on what a proof hides.
Thirteen of the fourteen clauses are equations in the field. No example in this file.
AN EXAMPLE LIES APART, BY EVALUATION: Honest/K6/ToyHides.lean asks HidesTables' fourteen clauses,
written out a second time with code (nothing ties them to the structure's text but a reader's eye),
and the premise on the mask row at the coins that the frame's lendRow lends at the toy's book, at
the sessions of the second toy (Honest/K6/Toy2.lean). Neither file is in the library.
  vars_draw            the variables' rounds, as the part's reader read them, sampled one element
                       each.
  drawsOk_of_heardBy   WHERE heardBy RETURNS ON ITS OWN ROUNDS, THEIR CHALLENGES PASS drawsOk
                       (SumLaw/Terms.lean), at every call with as many variables and with end
                       values: the test reads no point. No premise on the challenges.
  heardBy_of_sumcheck, heardBy_of_level   the verifier's two texts return through heardBy.
  call_count           a job of the row's shape has n + 1 variables in the run, the further one
                       among them.
  front_eight          the eight parts have as many rounds as are declared.
  hides_at_row         THE MAIN STATEMENT. The four tests drawsOk of HidesOfEight.lean's main
                       statement are paid here, of the hearing's return.
CALLED: HidesOfEight.lean (hides_of_eight), Johnson/Desc/Kinds/Law/K06HearEight.lean (hear_eight),
Plays.lean (k6Out_eight, k6Coin_0 .. k6Coin_7, k6Piece_at, k6Piece_shape, k6Piece_alone,
k6_share_length, headCut_sum, foldl_add_sum), TablesLaw.lean (lg_vars); of SumLaw/: entries_draw,
all_some, withPoints_length; of the library: heardBy_spec, heardBy_cut, hear_spec, readAll_spec,
zS_size, and the small lemmas on a hearing's steps (bind_some, pure_some).
-/
import Mathlib
import Johnson.Desc.ProofFile.Honest.K6.Law.Plays
import Johnson.Desc.ProofFile.Honest.K6.HidesOfEight

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K6
open OnBytes (E zeroE)
open OnBytes.Model (Fork)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Part.MaskedSum (Call Var Ends VarsRead readAll)
open VerifiableInference.Desc.Kinds (Point Form Hid Sum sumcheck level heardBy Head.Par Head.Given
  Head.HeardAll FinalNorm.zt halves Norm.lPd)
open VerifiableInference.Desc.Kinds.Head.Law (WellLaid callOf zS zS_size hear_eight bind_some
  pure_some heardBy_spec)
open VerifiableInference.Desc.Kinds.Head.Honest (PairSum HidesTables lg_vars)
open SumLaw (frontOf drawsOk)

variable {W X : Type}

/-! ## 1 The test on the challenges' counts, of the hearing's return -/

/-- The variables' rounds, as the part's reader read them, sampled one element each. -/
theorem vars_draw : ∀ {vs : List Var} {used : List Fmt.RoundView} {l : List (List E × E)},
    VarsRead vs used l → used.map (fun r => r.drawn.elems.length) = List.replicate vs.length 1
  | [], [], [], _ => rfl
  | _ :: _, _ :: _, (_, _) :: _, h => by
    rw [List.map_cons, List.length_cons, List.replicate_succ, h.1.2.2.1, vars_draw h.2]
  | [], [], _ :: _, h => h.elim
  | [], _ :: _, _, h => h.elim
  | _ :: _, [], _, h => h.elim
  | _ :: _, _ :: _, [], h => h.elim

/-- **Where heardBy returns on its own rounds, their challenges pass drawsOk**, at every call k with
as many variables and with end values. -/
theorem drawsOk_of_heardBy {lead : Nat} {C : Array Hid → Form} {z : Point} {e : Nat}
    {F0 F1 : Fork} {rounds : List Fmt.RoundView} {x : Array Hid × Sum}
    (hv : heardBy lead C z e F0 rounds = some (x, F1, [])) (k : Call) (e' : Ends)
    (hk1 : k.all.length = z.size + 1) (hk2 : k.ends = some e') :
    drawsOk k (rounds.map (·.drawn)) = true := by
  obtain ⟨cA, S⟩ := x
  obtain ⟨_, _, _, _, _, _, _, _, a4, _, _, _⟩ := heardBy_spec hv
  obtain ⟨_, _, R, _, hR, _, _⟩ := VerifiableInference.Desc.Part.MaskedSum.hear_spec a4
  obtain ⟨r0, used, rv, front, rfl, s0, _, sv, se⟩ :=
    VerifiableInference.Desc.Part.MaskedSum.readAll_spec
      (show readAll ⟨lead, z.toList.map (.point · 3), some ⟨2, e⟩⟩ rounds = some R from hR)
  have e1 : ((r0 :: (used ++ [rv])).map (·.drawn)).map (·.elems.length) =
      1 :: (List.replicate (z.size + 1) 1 ++ [0]) := by
    rw [List.map_map, List.map_cons, List.map_append, List.map_cons, List.map_nil]
    show r0.drawn.elems.length ::
      (used.map (fun r => r.drawn.elems.length) ++ [rv.drawn.elems.length]) = _
    rw [s0.2.2.1, se.2.2.1, vars_draw sv, List.length_append, List.length_map,
      Array.length_toList]
    rfl
  unfold drawsOk
  rw [SumLaw.entries_draw, e1, hk1, hk2]
  exact beq_self_eq_true _

/-- The verifier's sumcheck returns through heardBy. -/
theorem heardBy_of_sumcheck {z : Point} {e : Nat} {F0 F1 : Fork} {rounds : List Fmt.RoundView} {S : Sum}
    (hv : sumcheck z e F0 rounds = some (S, F1, [])) :
    ∃ x, heardBy 1 (fun c => (c.getD 0 {}).var) z e F0 rounds = some (x, F1, []) := by
  unfold sumcheck at hv
  obtain ⟨cs, F, left, h1, h2⟩ := bind_some hv
  obtain ⟨cA, s'⟩ := cs
  dsimp only at h2
  obtain ⟨_, rfl, rfl⟩ := pure_some h2
  exact ⟨_, h1⟩

/-- The verifier's level returns through heardBy, on all its rounds but the last. -/
theorem heardBy_of_level {z : Point} {start : Form} {F0 F1 : Fork} {rounds : List Fmt.RoundView}
    {line : Fmt.RoundView} {S : Sum} (hv : level z start F0 (rounds ++ [line]) = some (S, F1, []))
    (hlen : rounds.length = z.size + 3) :
    ∃ x G1, heardBy 0 (fun _ => start) z 2 F0 rounds = some (x, G1, []) := by
  unfold level at hv
  obtain ⟨cs, G1, l1, h1, _⟩ := bind_some hv
  obtain ⟨e1, _, _⟩ := VerifiableInference.Desc.Kinds.Head.Law.Came.heardBy_cut h1
  rw [← hlen, List.take_left] at e1
  exact ⟨_, _, e1⟩

/-- A job of the row's shape has n + 1 variables in the run. -/
theorem call_count (lead n e : Nat) (sumAt : W → Front X → PairSum)
    (leadAt : W → Front X → List E) (w : W) (fr : Front X) :
    ((pairJob (pointShape lead n e) sumAt leadAt).callAt w fr).all.length = n + 1 := by
  rw [SumLaw.all_some _ _ _ ⟨2, e⟩ rfl, List.length_append, SumLaw.withPoints_length]
  show (List.replicate n _).length + 1 = _
  rw [List.length_replicate]

/-- The eight parts have as many rounds as are declared. -/
theorem front_eight (p : Head.Par) : headInFront p 8 = p.rounds.length := by
  rw [← headCut_sum]
  show (headCut p).foldl (· + ·) 0 = _
  rw [foldl_add_sum, Nat.zero_add]

/-! ## 2 The main statement -/

section Row
variable {W₀ Rc Tr X : Type}

/-- **WHERE THE ONE HEARING RETURNS ON THE ROUNDS OF k6Out, HidesTables HOLDS OF THE CELLS, THE MASK
ROW, WHAT WAS HEARD AND THE LEDGER THAT IT RETURNS.** g: the letters in front of the hearing, made
of the small input and of what the state has heard. c: the row's coins, part by part. t, seen: the
state, and what has been shown in front of the row (the rounds, and the opened columns where any are
handed); seen stands in the premise on the hearing alone. ds: the row's challenges. -/
theorem hides_at_row [g : Head.Given] (wit : Local W₀ Rc Inst Tr → HeadAsk) (p : Head.Par)
    (at_ : Place) (c : RowCoins (headRow (X := X) wit p at_)) (t : State (Local W₀ Rc Inst Tr) X)
    (seen : Seen) (ds : List Fmt.Drawn) (nm : String)
    (hg : g = (wit t.input).given p t.heard) (hl : ds.length = p.rounds.length) (F G : Fork)
    (H : Head.HeardAll) (mask : Nat → E) (hW : WellLaid F)
    (hh : VerifiableInference.Desc.Kinds.Head.hear F
      (roundsOf (k6Out nm wit p at_ c t seen ds)) = some (H, G, []))
    (hzt : (VerifiableInference.Desc.Kinds.FinalNorm.zt).size =
      VerifiableInference.Desc.Kinds.Norm.lt)
    (hM : headTiedFrom mask F.next (headSpent (p := p) c.2.1.2.1.1 c.2.2.1 c.2.2.2.2.1.2.1.1
      c.2.2.2.2.2.1 c.2.2.2.2.2.2.1 c.2.2.2.2.2.2.2.1)) :
    HidesTables (wit t.input).cells mask H G := by
  rw [k6Out_eight] at hh
  obtain ⟨l0, w0⟩ := k6Piece_shape wit p at_ c t seen ds 0 _ (k6Coin_0 wit p at_ c) hl
  obtain ⟨l1, _⟩ := k6Piece_shape wit p at_ c t seen ds 1 _ (k6Coin_1 wit p at_ c) hl
  obtain ⟨l2, w2⟩ := k6Piece_shape wit p at_ c t seen ds 2 _ (k6Coin_2 wit p at_ c) hl
  obtain ⟨l3, _⟩ := k6Piece_shape wit p at_ c t seen ds 3 _ (k6Coin_3 wit p at_ c) hl
  obtain ⟨l4, _⟩ := k6Piece_shape wit p at_ c t seen ds 4 _ (k6Coin_4 wit p at_ c) hl
  obtain ⟨l5, w5⟩ := k6Piece_shape wit p at_ c t seen ds 5 _ (k6Coin_5 wit p at_ c) hl
  obtain ⟨l6, w6⟩ := k6Piece_shape wit p at_ c t seen ds 6 _ (k6Coin_6 wit p at_ c) hl
  obtain ⟨_, w7⟩ := k6Piece_shape wit p at_ c t seen ds 7 _ (k6Coin_7 wit p at_ c) hl
  have a2 := k6Piece_alone wit p at_ c t seen ds 2 _ (k6Coin_2 wit p at_ c) hl
  have a5 := k6Piece_alone wit p at_ c t seen ds 5 _ (k6Coin_5 wit p at_ c) hl
  have a6 := k6Piece_alone wit p at_ c t seen ds 6 _ (k6Coin_6 wit p at_ c) hl
  have a7 := k6Piece_alone wit p at_ c t seen ds 7 _ (k6Coin_7 wit p at_ c) hl
  -- the two rounds of scalars, written out
  obtain ⟨d1, hd1⟩ := List.length_eq_one_iff.mp
    (k6_share_length wit p at_ c ds 1 _ (k6Coin_1 wit p at_ c) hl)
  obtain ⟨d4, hd4⟩ := List.length_eq_one_iff.mp
    (k6_share_length wit p at_ c ds 4 _ (k6Coin_4 wit p at_ c) hl)
  have q1 := k6Piece_at wit p at_ c t seen ds 1 _ (k6Coin_1 wit p at_ c)
  have q4 := k6Piece_at wit p at_ c t seen ds 4 _ (k6Coin_4 wit p at_ c)
  rw [hd1] at q1
  rw [hd4] at q4
  rw [q1, q4] at hh
  subst hg
  letI : Head.Given := (wit t.input).given p t.heard
  -- the seven returns, for the four tests on the challenges' counts
  obtain ⟨Fa, Fb, Fc, Fd, Fe, _, _, h2, _, h4, h5, h6, _, _, _, sPV⟩ :=
    hear_eight hW hh l0 rfl l2 l3 rfl l5 (by rw [l6, hzt]; rfl)
  obtain ⟨line, hline⟩ := List.length_eq_one_iff.mp l3
  rw [hline] at h2
  obtain ⟨_, _, b2⟩ := heardBy_of_level h2 (by rw [l2, zS_size H.1.pV sPV]; rfl)
  obtain ⟨_, b5⟩ := heardBy_of_sumcheck h4
  obtain ⟨_, b6⟩ := heardBy_of_sumcheck h5
  obtain ⟨_, b7⟩ := heardBy_of_sumcheck h6
  have hn7 : (FinalNorm.zt ++ halves Norm.lPd).size = headLt p + headLPd p := by
    rw [← Array.length_toList]
    exact (lg_vars (wit t.input).cells.toCells).trans (by rw [hzt]; rfl)
  have ok2 := drawsOk_of_heardBy b2 ((headSquaresJob p).callAt
    (headStateAt p (wit t.input) t.heard ds 2).input
    (frontOf (headStateAt p (wit t.input) t.heard ds 2)
      (seen.plus (((k6Pieces wit p at_ c t seen ds).take 2).flatten)))) ⟨2, 2⟩
    ((call_count 0 _ 2 _ _ _ _).trans (by rw [zS_size H.1.pV sPV]; rfl)) rfl
  have ok5 := drawsOk_of_heardBy b5 ((headProductsJob p).callAt
    (headStateAt p (wit t.input) t.heard ds 5).input
    (frontOf (headStateAt p (wit t.input) t.heard ds 5)
      (seen.plus (((k6Pieces wit p at_ c t seen ds).take 5).flatten)))) ⟨2, 4⟩
    ((call_count 1 _ 4 _ _ _ _).trans (by rw [sPV]; rfl)) rfl
  have ok6 := drawsOk_of_heardBy b6 ((headNormedJob p).callAt
    (headStateAt p (wit t.input) t.heard ds 6).input
    (frontOf (headStateAt p (wit t.input) t.heard ds 6)
      (seen.plus (((k6Pieces wit p at_ c t seen ds).take 6).flatten)))) ⟨2, 2⟩
    ((call_count 1 _ 2 _ _ _ _).trans (by rw [hzt]; rfl)) rfl
  have ok7 := drawsOk_of_heardBy b7 ((headLogitsJob p).callAt
    (headStateAt p (wit t.input) t.heard ds 7).input
    (frontOf (headStateAt p (wit t.input) t.heard ds 7)
      (seen.plus (((k6Pieces wit p at_ c t seen ds).take 7).flatten)))) ⟨2, 2⟩
    ((call_count 1 _ 2 _ _ _ _).trans (by rw [hn7])) rfl
  rw [w2] at ok2
  rw [w5] at ok5
  rw [w6] at ok6
  rw [w7] at ok7
  exact hides_of_eight p (wit t.input) t.heard ds rfl c.2.1.2.1.1 c.2.2.1 c.2.2.2.2.1.2.1.1
    c.2.2.2.2.2.1 c.2.2.2.2.2.2.1 c.2.2.2.2.2.2.2.1 _ _ _ _ _ _ _ _ _ _ d1 d4 F G H mask
    (by rw [front_eight, hl]) w0 hd1 l3 hd4 ok2 a2 ok5 a5 ok6 a6 ok7 a7 hW hh hzt hM

end Row

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.vars_draw
#print axioms ProofFile.Honest.K6.drawsOk_of_heardBy
#print axioms ProofFile.Honest.K6.heardBy_of_sumcheck
#print axioms ProofFile.Honest.K6.heardBy_of_level
#print axioms ProofFile.Honest.K6.call_count
#print axioms ProofFile.Honest.K6.front_eight
#print axioms ProofFile.Honest.K6.hides_at_row
