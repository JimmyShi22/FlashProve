-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/Law.lean: THE SMALLNESS TEST, ITS FIRST HALF (THE DRAW OF THE MATRIX): ITS
LAW.

The kind's text (Johnson/Desc/First/K8/Hear.lean) hears one round and hands a record on: it compares
no value of the prover's with another. So "the kind's yes gives the proved block's yes" is empty by
itself: the proved block (Cb/Pv/Tail/Block.lean; as a family of blocks:
Johnson/Top/H/TailRngOn.lean) draws and refuses nothing either. What the law must say is that the
two speak of ONE matrix. It is a short chain:
  (R) THE ROUNDS' DATA. The kind's declared round is a written round that draws columns x tau matrix
    entries and nothing else, at the typed block's own numbers: `onlyTrits`. With it the library's
    maps from the written round to the typed one apply (OnBytes/Tie/Pv/Tail/CarryRng.lean: carryRng,
    carryRng_fib, carryRng_tr).
  (L1) THE PROVED BLOCK. `block_good`: the library's theorem, at whatever caller has these numbers.
  (L2a) THE KIND'S OWN TEXT TO THE RECORD. `decide_ok`: a yes of decide means: one round; the eight
    tests hold; the record handed on is what the seat lays from the round's list of entries and the
    first columns. `lays_matrix`: where the round is the record that the kit with hash blocks makes
    of a written verifier message, that list is `listOf β` for β the typed challenge to which the
    library's maps carry that message: the matrix that the typed block puts into its out-statement
    (`out_matrix`). `firstColumns_get`: the first columns are the typed side's `firstCol`.
  (L2b) TO THE OUT-CLAIM. Not here: the test's equations are the kind's second half, another file's.
This closes a limit that CarryRng.lean names: "that the verifier's routine lays the record's list of
entries into its own record of the smallness test is read off the text ... and not proved here": for
the kind's own text it is (L2a).

Limits. Nothing on soundness beyond the library's theorem. `Fits` is a premise: that a place's
numbers are those of the caller's sizes is for whoever makes both from the plan. What a seat's `lay`
does with the list is the seat's. That the messages which the matrix multiplies are fixed before the
draw is not said here: the block names them in `before`, and the file's test on the plan asks the
order (FileDescription.beforeOk). On the typed side it is a condition on the caller, stated in no type: the
block's joints speak of the messages of the caller's signature, and Johnson/Top/H/TailRng.lean's
Limits say that these must be what is committed before the matrix is drawn. That the caller's
signature at a place holds just the messages that the block names in `before` is owed by whoever
lays the caller.


-/
import Johnson.Desc.First.K8.Hear
import OnBytes.Tie.Pv.Tail.CarryRng
import Johnson.Top.H.TailRngOn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8

open Cb.Pv.Tail OnBytes.Tie.Pv.Tail OnBytes.Slice Iop

/-- The place's numbers are the typed block's: how many matrices, each one's columns, how many
combinations. -/
structure Fits (p : Par) (s : Size) : Prop where
  nm  : s.NM = p.ks.length
  k   : ∀ i, i < p.ks.length → s.k i = p.ks.getD i 0
  tau : s.tau = p.tau

/-- Sizes with the place's numbers; the other numbers are the caller's. -/
def sizeAt (p : Par) (rest : Size) : Size :=
  { rest with NM := p.ks.length, k := fun i => p.ks.getD i 0, tau := p.tau }

theorem fits_sizeAt (p : Par) (rest : Size) : Fits p (sizeAt p rest) := ⟨rfl, fun _ _ => rfl, rfl⟩

/-! ## Sums -/

theorem foldl_add (l : List Nat) (a : Nat) : l.foldl (· + ·) a = a + l.sum := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => simp [List.foldl_cons, ih, Nat.add_assoc]

theorem sum_range_getD (l : List Nat) : ∑ i ∈ Finset.range l.length, l.getD i 0 = l.sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.length_cons, Finset.sum_range_succ', List.sum_cons]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [ih, Nat.add_comm]

theorem columns_eq {p : Par} {s : Size} (h : Fits p s) : s.columns = columns p := by
  unfold Size.columns columns
  rw [foldl_add, Nat.zero_add, ← sum_range_getD, Fin.sum_univ_eq_sum_range (fun i => s.k i) s.NM,
      h.nm]
  exact Finset.sum_congr rfl fun i hi => h.k i (Finset.mem_range.1 hi)

/-! ## (R) The rounds' data -/

/-- The kind's declared round, as the written round of the library's maps. -/
def rd (p : Par) : Run.PQ.RD :=
  { entry := (round p).entry, kind := .entries, items := (round p).items, tree := none, opens := []
      }

/-- The kind that the format gives the round's name. -/
theorem kind_rng (p : Par) : Fmt.kindOf (round p).entry.name = some (rd p).kind := by
  show Fmt.kindOf "RNG" = some Fmt.Kind.entries
  decide

/-- **(R)** The declared round draws columns x tau matrix entries, at the typed block's numbers, and
nothing else. -/
theorem onlyTrits {p : Par} {s : Size} (h : Fits p s) : OnlyTrits (rd p) (s.columns * s.tau) := by
  rw [columns_eq h, h.tau]
  exact onlyTrits_of (rd p) rfl rfl rfl rfl

/-! ## (L1) The proved block -/

/-- **(L1)** The library's theorem, at whatever caller. -/
theorem block_good (d : VerifiableInference.OnPublicFiles.TailCallerOn) (hOK : d.c.s.OK) :
    (KObj.KTailRngOn.blk d).Good := KObj.KTailRngOn_good d hOK

/-! ## (L2a) The kind's own text to the record -/

/-- What a yes of `decide` means. -/
theorem decide_ok {S Cl : Type} (seat : Seat S) (p : Par) (st st' : S) (rs : List Fmt.RoundView)
    (cols : List (List (Nat × List UInt64)))
    (h : (approximateRangeProofDrawKind (Cl := Cl) seat p).decide st rs cols = .ok st') :
    ∃ r, rs = [r] ∧ seat.closed st = true ∧ seat.nothingOwed st = true ∧ seat.drawn st = false ∧
      seat.matrices st = p.ks.length ∧ seat.ks st = p.ks ∧ seat.ms st = p.ms ∧
      seat.tau st = p.tau ∧ seat.tabs st = tabs p ∧
      seat.lay st r.drawn.trits.toArray (firstColumns p) = .ok st' := by
  match rs, h with
  | [r], h =>
    refine ⟨r, rfl, ?_⟩
    simp only [approximateRangeProofDrawKind] at h
    by_cases h1 : seat.closed st <;> by_cases h2 : seat.nothingOwed st <;> by_cases h3 : seat.drawn
        st <;>
      by_cases h4 : seat.matrices st = p.ks.length <;> by_cases h5 : seat.ks st = p.ks <;>
      by_cases h6 : seat.tau st = p.tau <;> by_cases h7 : seat.ms st = p.ms <;>
      by_cases h8 : seat.tabs st = tabs p <;> simp_all
  | [], h => simp [approximateRangeProofDrawKind] at h
  | _ :: _ :: _, h => simp [approximateRangeProofDrawKind] at h

section
variable {p : Par} {s : Size} (hf : Fits p s)

/-- The typed challenge to which the library's maps carry a written verifier message of the round.
-/
def matrixOf (c : (wRound (rd p)).Chal) : Dr s := matOf s (rd p) (onlyTrits hf) (valsOf (rd p) c)

/-- **(L2a)** Where the view's round is the record that the kit with hash blocks makes of a written
verifier message, a yes of `decide` hands on the record into which the seat has laid the list of
THAT typed challenge. -/
theorem lays_matrix {S Cl : Type} (seat : Seat S) (st st' : S) (r : Fmt.RoundView)
    (cols : List (List (Nat × List UInt64))) (c : (wRound (rd p)).Chal)
    (hr : r.drawn.trits =
      ((Run.ckP .two).dr (rd p).entry (rd p).kind (GChal.old (b := (rd p).entry.work) c)).trits)
    (h : (approximateRangeProofDrawKind (Cl := Cl) seat p).decide st [r] cols = .ok st') :
    seat.lay st (listOf (matrixOf hf c)) (firstColumns p) = .ok st' := by
  obtain ⟨r', e, _, _, _, _, _, _, _, _, hl⟩ := decide_ok seat p st st' [r] cols h
  obtain rfl : r = r' := by simpa using e
  rw [hr, drawn_view s (rd p) (onlyTrits hf) c] at hl
  exact hl

/-- A kind is shown its rounds without the sealed digest: the list of entries is the same. -/
theorem noDigest_trits (r : Fmt.RoundView) : (noDigest r).drawn.trits = r.drawn.trits := rfl

/-- The written transcript has an image, and on it the typed block puts out the statement with that
matrix. -/
theorem out_matrix {K : Type} [CommRing K] (Λ : Letters K s) (x : Λ.X) (y : Λ.E.Str)
    (m : (wRound (rd p)).Msg) (c : (wRound (rd p)).Chal)
    (hp : GChal.pass (b := (rd p).entry.work) c = true) :
    ∃ t, (carryRng s (rd p) (onlyTrits hf)).tr ((m, c, ()) : Tr [wRound (rd p)]) = some t ∧
      (R Λ).red.out (x, y) t = some ((x, matrixOf hf c), y) :=
  ⟨_, carryRng_tr s (rd p) (onlyTrits hf) m c hp, rng_out s (rd p) (onlyTrits hf) Λ x y c⟩

/-- The declared round asks for no work: its test of work passes at every written verifier message.
-/
theorem pass_rng (c : (wRound (rd p)).Chal) : GChal.pass (b := (rd p).entry.work) c = true := by
  unfold GChal.pass
  exact decide_eq_true fun i => absurd i.isLt (Nat.not_lt_zero _)

/-- So every written transcript of the round has an image. -/
theorem out_matrix_all {K : Type} [CommRing K] (Λ : Letters K s) (x : Λ.X) (y : Λ.E.Str)
    (m : (wRound (rd p)).Msg) (c : (wRound (rd p)).Chal) :
    ∃ t, (carryRng s (rd p) (onlyTrits hf)).tr ((m, c, ()) : Tr [wRound (rd p)]) = some t ∧
      (R Λ).red.out (x, y) t = some ((x, matrixOf hf c), y) :=
  out_matrix hf Λ x y m c (pass_rng c)

/-- At most w written verifier messages go to one matrix: the library's bound, at the declared
round. -/
theorem fib_rng :
    (carryRng s (rd p) (onlyTrits hf)).Fib
      (((Run.bsRound .two (rd p).entry (rd p).kind).w, ()) : ℕ × Unit) :=
  carryRng_fib s (rd p) (onlyTrits hf) (Nat.zero_le _)

end

/-! ## The block as the fold calls it -/

/-- The block reads no column: as a step it is `decide` on the round without the sealed digest, and
takes none. -/
theorem step_eq {S Cl : Type} (seat : Seat S) (p : Par) (ft : Nat) (st : S) (r : Fmt.RoundView) (cols :
           List OpenedColumn)
    (hfit : roundsFit [round p] [r] = true) :
    (approximateRangeProofDrawKind (Cl := Cl) seat p).step ft st [r] cols =
      ((approximateRangeProofDrawKind (Cl := Cl) seat p).decide st [noDigest r] []).map fun s' => (s', 0) := by
  have hR : (approximateRangeProofDrawKind (Cl := Cl) seat p).rounds = [round p] := rfl
  have hg : groupsOf ft [round p] ([r].map (·.drawn)) = [] := by
    simp [groupsOf, round]
  unfold Block.step
  rw [hR, hfit, hg]
  simp only [need, List.flatMap_nil, List.length_nil, List.take_zero, List.map_nil, List.map_cons,
      regroup]
  cases (approximateRangeProofDrawKind (Cl := Cl) seat p).decide st [noDigest r] [] <;> rfl

/-- **What a yes of the block means in the fold.** One round; it shows nothing of the prover's, no
drawn element, no position, and columns x tau entries; the eight tests hold; no column is taken; the
record handed on is what the seat lays. -/
theorem step_ok {S Cl : Type} (seat : Seat S) (p : Par) (ft : Nat) (st st' : S) (rs : List Fmt.RoundView)
    (cols : List OpenedColumn) (n : Nat) (h : (approximateRangeProofDrawKind (Cl := Cl) seat p).step ft st rs cols = .ok (st', n)) :
    n = 0 ∧ ∃ r, rs = [r] ∧ roundsFit [round p] [r] = true ∧ seat.closed st = true ∧
      seat.nothingOwed st = true ∧ seat.drawn st = false ∧ seat.matrices st = p.ks.length ∧
      seat.ks st = p.ks ∧ seat.ms st = p.ms ∧ seat.tau st = p.tau ∧ seat.tabs st = tabs p ∧
      seat.lay st r.drawn.trits.toArray (firstColumns p) = .ok st' := by
  have hfit : roundsFit [round p] rs = true := by
    cases hf : roundsFit [round p] rs with
    | true => rfl
    | false =>
      have hR : (approximateRangeProofDrawKind (Cl := Cl) seat p).rounds = [round p] := rfl
      unfold Block.step at h
      rw [hR, hf] at h
      simp [need, bind, Except.bind] at h
  obtain ⟨r, rfl⟩ : ∃ r, rs = [r] := by
    match rs, hfit with
    | [r], _ => exact ⟨r, rfl⟩
    | [], hfit => simp [roundsFit] at hfit
    | _ :: _ :: _, hfit => simp [roundsFit] at hfit
  rw [step_eq seat p ft st r cols hfit] at h
  cases hd : (approximateRangeProofDrawKind (Cl := Cl) seat p).decide st [noDigest r] [] with
  | error e => rw [hd] at h; simp [Except.map] at h
  | ok s1 =>
    rw [hd] at h
    simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨r', e, c1, c2, c3, c4, c5, c7, c6, c8, hl⟩ := decide_ok seat p st s1 [noDigest r] [] hd
    obtain rfl : noDigest r = r' := by simpa using e
    exact ⟨rfl, r, rfl, hfit, c1, c2, c3, c4, c5, c7, c6, c8, hl⟩

/-! ## The law as one equation, and two silly members that must not meet it -/

/-- What the block must do, as one plain function of the seat, the place's numbers, the record and
the rounds. -/
def spec {S : Type} (seat : Seat S) (p : Par) (st : S) (rs : List Fmt.RoundView) : Option (S × Nat) :=
  match rs with
  | [r] =>
    if roundsFit [round p] [r] && seat.closed st && seat.nothingOwed st && !seat.drawn st &&
        seat.matrices st == p.ks.length && seat.ks st == p.ks && seat.ms st == p.ms &&
        seat.tau st == p.tau && seat.tabs st == tabs p then
      (seat.lay st r.drawn.trits.toArray (firstColumns p)).toOption.map fun s' => (s', 0)
    else none
  | _ => none

/-- A block meets the law: as a step it says yes just where `spec` does, and hands on just that.
Both directions: a block that refuses everything does not meet it, nor one that accepts everything.
-/
def Meets {S Cl : Type} (seat : Seat S) (p : Par) (b : Block S Cl) : Prop :=
  ∀ (ft : Nat) (st : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn), (b.step ft st rs cols).toOption = spec
      seat p st rs

theorem step_rounds_no {S Cl : Type} (seat : Seat S) (p : Par) (ft : Nat) (st : S) (rs : List
    Fmt.RoundView)
    (cols : List OpenedColumn) (hf : roundsFit [round p] rs = false) :
    (approximateRangeProofDrawKind (Cl := Cl) seat p).step ft st rs cols = .error "the rounds" := by
  have hR : (approximateRangeProofDrawKind (Cl := Cl) seat p).rounds = [round p] := rfl
  unfold Block.step
  rw [hR, hf]
  rfl

/-- **The kind's text meets the law.** -/
theorem hear_meets {S Cl : Type} (seat : Seat S) (p : Par) : Meets seat p (approximateRangeProofDrawKind (Cl := Cl) seat p)
    := by
  intro ft st rs cols
  match rs with
  | [r] =>
    cases hfit : roundsFit [round p] [r] with
    | false => simp [step_rounds_no seat p ft st [r] cols hfit, spec, hfit, Except.toOption]
    | true =>
      rw [step_eq seat p ft st r cols hfit]
      simp only [spec, hfit, approximateRangeProofDrawKind, noDigest]
      cases h1 : seat.closed st <;> cases h2 : seat.nothingOwed st <;> cases h3 : seat.drawn st <;>
        by_cases h4 : seat.matrices st = p.ks.length <;> by_cases h5 : seat.ks st = p.ks <;>
        by_cases h6 : seat.tau st = p.tau <;> by_cases h7 : seat.ms st = p.ms <;>
        by_cases h8 : seat.tabs st = tabs p <;>
        simp [h4, h5, h6, h7, h8, Except.map, Except.toOption]
      cases seat.lay st r.drawn.trits.toArray (firstColumns p) <;> rfl
  | [] => simp [step_rounds_no seat p ft st [] cols rfl, spec, Except.toOption]
  | r :: r' :: l =>
    have hf : roundsFit [round p] (r :: r' :: l) = false := by simp [roundsFit]
    simp [step_rounds_no seat p ft st (r :: r' :: l) cols hf, spec, Except.toOption]

/-- A toy seat, place and round, for the two silly members. -/
def toySeat : Seat (Array Int) :=
  ⟨fun _ => true, fun _ => true, fun _ => false, fun _ => 1, fun _ => [1], fun _ => [1],
    fun _ => 1, fun _ => [], fun _ m _ => .ok m⟩
def toyPar : Par := ⟨0, 5, [1], [1], 1, [], [0], [1]⟩
def toyRound : Fmt.RoundView := ⟨[], ⟨[], [], [1], none⟩⟩

/-- The text with a decision that says yes to all and hands the record on as it came. -/
def sillyYes : Block (Array Int) Unit := { approximateRangeProofDrawKind toySeat toyPar with decide := fun s _ _ => .ok s }
/-- The text with a decision that says no to all. -/
def sillyNo : Block (Array Int) Unit :=
  { approximateRangeProofDrawKind toySeat toyPar with decide := fun _ _ _ => .error "no" }

theorem spec_toy : spec toySeat toyPar #[] [toyRound] = some (#[1], 0) := by decide

theorem sillyYes_fails : ¬ Meets toySeat toyPar sillyYes := fun h => by
  have e := h 0 #[] [toyRound] []
  rw [spec_toy] at e
  revert e
  decide

theorem sillyNo_fails : ¬ Meets toySeat toyPar sillyNo := fun h => by
  have e := h 0 #[] [toyRound] []
  rw [spec_toy] at e
  revert e
  decide


/-! ## THE LAW, with the typed matrix in it -/

section
variable {p : Par} {s : Size} (hf : Fits p s)

/-- The list of entries in the record that the kit with hash blocks makes of a written verifier
message. -/
def kitTrits (c : (wRound (rd p)).Chal) : List Int :=
  ((Run.ckP .two).dr (rd p).entry (rd p).kind (GChal.old (b := (rd p).entry.work) c)).trits

theorem kitTrits_eq (c : (wRound (rd p)).Chal) : (kitTrits c).toArray = listOf (matrixOf hf c) :=
  drawn_view s (rd p) (onlyTrits hf) c

include hf in
theorem kitTrits_length (c : (wRound (rd p)).Chal) : (kitTrits c).length = columns p * p.tau := by
  have e := congrArg Array.size (kitTrits_eq hf c)
  rw [List.size_toArray] at e
  rw [e, ← columns_eq hf, ← hf.tau]
  simp [listOf]

/-- A coefficient's value is -1, 0 or 1. -/
theorem coef_val (b : Prob.Coef) : b.val = -1 ∨ b.val = 0 ∨ b.val = 1 := by
  obtain ⟨x, y⟩ := b
  cases x <;> cases y <;> simp [Prob.Coef.val]

include hf in
/-- Every entry of the kit's list is -1, 0 or 1. -/
theorem kitTrits_all (c : (wRound (rd p)).Chal) :
    (kitTrits c).all (fun t => t == -1 || t == 0 || t == 1) = true := by
  have e : kitTrits c = (listOf (matrixOf hf c)).toList := by rw [← kitTrits_eq hf c]
  rw [e, List.all_eq_true]
  intro t ht
  simp only [listOf, Array.toList_ofFn, List.mem_ofFn] at ht
  obtain ⟨j, rfl⟩ := ht
  rcases coef_val (flatPort s (matrixOf hf c) j) with h | h | h <;> simp [h]

/-- **The law at one written verifier message c.** At a view's round that shows nothing of the
prover's, no drawn element and no position, and whose list of entries is the one that the kit makes
of c: the block says yes, and hands on st' and takes n columns, IF AND ONLY IF the eight tests hold
at the record, n = 0, and st' is what the seat lays from the list of THE TYPED CHALLENGE to which
the library's maps carry c: the matrix of the proved block's out-statement (`out_matrix_all`). -/
def LawAt {S Cl : Type} (seat : Seat S) (b : Block S Cl) (c : (wRound (rd p)).Chal) : Prop :=
  ∀ (ft : Nat) (st st' : S) (n : Nat) (cols : List OpenedColumn) (r : Fmt.RoundView),
    r.vals = [] → r.drawn.elems = [] → r.drawn.poss = [] → r.drawn.trits = kitTrits c →
    (b.step ft st [r] cols = .ok (st', n) ↔
      (seat.closed st = true ∧ seat.nothingOwed st = true ∧ seat.drawn st = false ∧
        seat.matrices st = p.ks.length ∧ seat.ks st = p.ks ∧ seat.ms st = p.ms ∧
        seat.tau st = p.tau ∧ seat.tabs st = tabs p ∧
        seat.lay st (listOf (matrixOf hf c)) (firstColumns p) = .ok st' ∧ n = 0))

include hf in
theorem fit_of (c : (wRound (rd p)).Chal) (r : Fmt.RoundView) (h1 : r.vals = []) (h2 : r.drawn.elems = [])
    (h3 : r.drawn.poss = []) (h4 : r.drawn.trits = kitTrits c) : roundsFit [round p] [r] = true :=
        by
  have hl : r.drawn.trits.length = columns p * p.tau := by rw [h4, kitTrits_length hf c]
  have ha := kitTrits_all hf c
  rw [← h4] at ha
  have hz : drawsMarkedNonzeroHaveNonzeroWords (round p) r = true := by
    unfold drawsMarkedNonzeroHaveNonzeroWords
    rw [kind_rng p]
    simp [h2]
  have hz' : drawsMarkedNonzeroHaveNonzeroWords { entry := { name := "RNG", trits := columns p * p.tau } } r = true := hz
  simp [roundsFit, round, Fmt.DeclaredRound.items, Fmt.Entry.cut, h1, h2, h3, hl, ha, hz']

/-- **THE KIND'S TEXT HAS THE LAW, at every written verifier message.** -/
theorem hear_law {S Cl : Type} (seat : Seat S) (c : (wRound (rd p)).Chal) :
    LawAt hf seat (approximateRangeProofDrawKind (Cl := Cl) seat p) c := by
  intro ft st st' n cols r h1 h2 h3 h4
  have hfit := fit_of hf c r h1 h2 h3 h4
  have ha : r.drawn.trits.toArray = listOf (matrixOf hf c) := by rw [h4, kitTrits_eq hf c]
  constructor
  · intro h
    obtain ⟨hn, r', e, _, c1, c2, c3, c4, c5, c7, c6, c8, hl⟩ :=
      step_ok seat p ft st st' [r] cols n h
    obtain rfl : r = r' := by simpa using e
    rw [ha] at hl
    exact ⟨c1, c2, c3, c4, c5, c7, c6, c8, hl, hn⟩
  · rintro ⟨c1, c2, c3, c4, c5, c7, c6, c8, hl, rfl⟩
    have e := hear_meets (Cl := Cl) seat p ft st [r] cols
    rw [← ha] at hl
    simp only [spec, hfit, c1, c2, c3, c4, c5, c6, c7, c8, hl, Except.toOption, Bool.and_self,
        Bool.not_false, beq_self_eq_true,
      if_true, Option.map_some] at e
    cases hs : (approximateRangeProofDrawKind (Cl := Cl) seat p).step ft st [r] cols with
    | error x => rw [hs] at e; simp at e
    | ok x =>
      rw [hs] at e
      simp only [Option.some.injEq] at e
      rw [e]

end

/-! The two silly members against THE LAW. -/

def toySize : Size := sizeAt toyPar ⟨0, fun _ => 0, fun _ => 0, fun _ => 0, 0, 0, 0, 0, 0⟩
theorem toyFits : Fits toyPar toySize := fits_sizeAt _ _

/-- The round that the toy place's law speaks of, at c. -/
def toyRoundAt (c : (wRound (rd toyPar)).Chal) : Fmt.RoundView := ⟨[], ⟨[], [], kitTrits c, none⟩⟩

/-- A decision that says no to all has the law at no written verifier message. -/
theorem sillyNo_law (c : (wRound (rd toyPar)).Chal) : ¬ LawAt toyFits toySeat sillyNo c := fun h =>
    by
  have e := (h 0 #[] (listOf (matrixOf toyFits c)) 0 [] (toyRoundAt c) rfl rfl rfl rfl).2
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hR : sillyNo.rounds = [round toyPar] := rfl
  unfold Block.step at e
  rw [hR, fit_of toyFits c (toyRoundAt c) rfl rfl rfl rfl] at e
  simp [need, sillyNo, bind, Except.bind, groupsOf, round] at e

/-- A decision that says yes to all, and hands the record on as it came, has the law at none either.
-/
theorem sillyYes_law (c : (wRound (rd toyPar)).Chal) : ¬ LawAt toyFits toySeat sillyYes c := fun h
    => by
  have hs : sillyYes.step 0 #[] [toyRoundAt c] [] = .ok (#[], 0) := by
    have hR : sillyYes.rounds = [round toyPar] := rfl
    unfold Block.step
    rw [hR, fit_of toyFits c (toyRoundAt c) rfl rfl rfl rfl]
    simp [need, sillyYes, bind, Except.bind, groupsOf, round, pure, Except.pure]
  have e := ((h 0 #[] #[] 0 [] (toyRoundAt c) rfl rfl rfl rfl).1 hs).2.2.2.2.2.2.2.2.1
  have e' : listOf (matrixOf toyFits c) = #[] := by simpa [toySeat] using e
  have hz := congrArg Array.size e'
  rw [← kitTrits_eq toyFits c, List.size_toArray, kitTrits_length toyFits c] at hz
  revert hz
  decide

/-! ## The first columns -/

/-- The running sums. -/
theorem firstColumns_aux (l : List Nat) : ∀ a : Array Nat, 0 < a.size →
    (l.foldl (fun a k => a.push (a.getD (a.size - 1) 0 + k)) a).size = a.size + l.length ∧
    (∀ i, i < a.size → (l.foldl (fun a k => a.push (a.getD (a.size - 1) 0 + k)) a).getD i 0 = a.getD
        i 0) ∧
    ∀ j, j ≤ l.length →
      (l.foldl (fun a k => a.push (a.getD (a.size - 1) 0 + k)) a).getD (a.size - 1 + j) 0 =
        a.getD (a.size - 1) 0 + (l.take j).sum := by
  induction l with
  | nil =>
    intro a _
    refine ⟨by simp, fun _ _ => rfl, fun j hj => ?_⟩
    have hj0 : j = 0 := by simpa using hj
    subst hj0
    simp
  | cons x l ih =>
    intro a ha
    have hs : (a.push (a.getD (a.size - 1) 0 + x)).size = a.size + 1 := by simp
    obtain ⟨h1, h2, h3⟩ := ih (a.push (a.getD (a.size - 1) 0 + x)) (by simp)
    have hlt : ∀ i, i < a.size → (a.push (a.getD (a.size - 1) 0 + x)).getD i 0 = a.getD i 0 := by
      intro i hi
      simp [Array.getD_eq_getD_getElem?, Array.getElem?_push, Nat.ne_of_lt hi]
    have hlast : (a.push (a.getD (a.size - 1) 0 + x)).getD a.size 0 = a.getD (a.size - 1) 0 + x :=
        by
      simp [Array.getD_eq_getD_getElem?]
    refine ⟨?_, ?_, ?_⟩
    · rw [List.foldl_cons, h1, hs, List.length_cons]
      omega
    · intro i hi
      rw [List.foldl_cons, h2 i (by rw [hs]; omega), hlt i hi]
    · intro j hj
      rw [List.foldl_cons]
      cases j with
      | zero =>
        rw [Nat.add_zero, h2 _ (by rw [hs]; omega), hlt _ (by omega)]
        simp
      | succ j =>
        have e : a.size - 1 + (j + 1) = (a.push (a.getD (a.size - 1) 0 + x)).size - 1 + j := by
          rw [hs]
          omega
        have hj' : j ≤ l.length := by simpa using hj
        rw [e, h3 j hj', hs, Nat.add_sub_cancel, hlast, List.take_succ_cons, List.sum_cons]
        omega

theorem sum_take (l : List Nat) (n : Nat) (hn : n ≤ l.length) :
    ∑ i ∈ Finset.range n, l.getD i 0 = (l.take n).sum := by
  rw [← sum_range_getD (l.take n), List.length_take, Nat.min_eq_left hn]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.1 hi
  simp [List.getD_eq_getElem?_getD, hi']

/-- The first columns that the kind lays are the typed side's. -/
theorem firstColumns_get {p : Par} {s : Size} (h : Fits p s) (μ : Fin s.NM) :
    (firstColumns p).getD μ.val 0 = firstCol s μ := by
  have hμ : μ.val < p.ks.length := h.nm ▸ μ.isLt
  have key := (firstColumns_aux p.ks #[0] (by simp)).2.2 μ.val hμ.le
  have e0 : (#[0] : Array Nat).size - 1 + μ.val = μ.val := by simp
  rw [e0] at key
  unfold firstColumns
  rw [key, ← sum_take p.ks μ.val hμ.le]
  unfold firstCol
  rw [← Fin.sum_univ_eq_sum_range (fun i => p.ks.getD i 0) μ.val]
  simp only [Array.getD_eq_getD_getElem?]
  simp only [List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.sub_self]
  simp only [List.getElem?_toArray, List.getElem?_cons_zero, Option.getD_some, Nat.zero_add]
  exact Finset.sum_congr rfl fun ν _ => (h.k ν.val (by omega)).symm

end VerifiableInference.Desc.First.K8

#print axioms VerifiableInference.Desc.First.K8.onlyTrits
#print axioms VerifiableInference.Desc.First.K8.decide_ok
#print axioms VerifiableInference.Desc.First.K8.lays_matrix
#print axioms VerifiableInference.Desc.First.K8.out_matrix
#print axioms VerifiableInference.Desc.First.K8.block_good
#print axioms VerifiableInference.Desc.First.K8.firstColumns_get
#print axioms VerifiableInference.Desc.First.K8.out_matrix_all
#print axioms VerifiableInference.Desc.First.K8.fib_rng
#print axioms VerifiableInference.Desc.First.K8.step_ok
#print axioms VerifiableInference.Desc.First.K8.hear_meets
#print axioms VerifiableInference.Desc.First.K8.sillyYes_fails
#print axioms VerifiableInference.Desc.First.K8.sillyNo_fails
#print axioms VerifiableInference.Desc.First.K8.hear_law
#print axioms VerifiableInference.Desc.First.K8.sillyNo_law
#print axioms VerifiableInference.Desc.First.K8.sillyYes_law
