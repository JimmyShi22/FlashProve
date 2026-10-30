-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/RowBatch.lean: CONDITIONAL. A kit: one definition of a
hypothesis's form, and statements with their proofs.

What is here. What the laws on the honest row of the feed-forward layers' own rounds (sub-protocol
K4) share, behind the member's own step on what the row has played: from that step to the return of
the verifier's hearing on the tape of the played rounds (`step_tape`); public numbers of the row
(how lifting and quiet parts leave the counts of rounds and of spent coins; what a sumcheck's part
counts); and small facts on the row products' job, on a tape and on the challenges as played. The
file's name is that of the claim for which the kit was first made; that claim's own road is here no
more.

  0  `K4SizedAt s`   at the state s in front of the member the layers' segment's ledger has arrays
     of its size. IT IS THE CLAUSE `sized` OF THE LIBRARY's `KeptAsks`
     (Johnson/Road/K4/Total/AtKept.lean), letter for letter; no statement here takes it: it is a
     field of `K4Stand` (Law/SlotsTrue.lean), which statements of that file take;
     Law/W/SlotsOfStand.lean fills that field from `KeptAsks`' own clause, which it has under a
     hypothesis of its own
  1  `segAt_parts`, `step_front`, `step_hears`, `step_data`, `seg_fork`, `moved_state`   where the
     kind's sub-protocol accepts: a layers' segment is open in front; the hearing's return on the
     tape of the rounds, from the ledger in front to the ledger behind; the witness's data are read
     as in front; the seat's ledger behind is the open segment's; the run's input is kept and its
     challenges are those in front with the member's
  2  `k0_cases`, `movesTo_lift`, `spentTo_lift`, `movesTo_quiet`, `spentTo_quiet`, `k4Sum_moves`,
     `k4Sum_coins`, `foldl_points`, `ownRun_token`, `ownRun_level`   public numbers of the row
     (`movesTo`, `spentTo`, `coinsIn`: Law/RowKit.lean)
  3  `rowProducts_congr`, `jobRows_maps`, `jobRows_lead`, `tapeCl_sent`, `played_drawn`
  4  `fits_covers`, `step_tape`   **from the member's own step to the hearing's return on the tape
     of the played rounds**, in the public data's letters: general: no slot is named

Not shown here. NO STATEMENT HERE SAYS WHAT ANY FORM, SLOT OR WORD IS WORTH. THE SIX OF 1 AND
`step_tape` EACH SPEAK AT ONE STAND: one state in front of the member, one run, one step. That the
member's step accepts is a hypothesis wherever it is named (h in `step_front`, `step_hears` and
`step_data`; hS in `step_tape`). `K4Seated` (Law/Seated.lean) and `K4Sits` (Law/Sits.lean), which
`step_tape` takes: see there; that they can be met together: this file gives no example.
Following import lines, and stopping unopened at every module under Johnson/Goal/, Johnson/D/,
Johnson/Bridge/ or ThirdParty/ and at every module whose name begins Cb.Bridge, its imports reach 2
modules under Johnson/Bridge/, and none of the others; what lies behind these is not counted; 7 of
the modules that it reaches have RecCompile in their names, none of them RecCompile's Honest*, Both
or PassH*. The seven (Join, Wire, Pass, CmsGlue, CmsBcs, Cms, Bcs) come with a module of the library
(Johnson/E/KObj/ProofFile.lean): nothing here names one of them. THE IMPORT LINES ARE MORE THAN THE
KIT SPENDS: they are kept so that no file above loses what it has
through them. Law/SlotsTrue.lean and Law/W/SlotsOfStand.lean are no part of the library. Nothing
on soundness, on completeness or on any other property.

Kin. `segAt_parts` is, but for how two types are spelt, a law of the library's of that name
(Johnson/Desc/First/Look/K3MaskOkTools.lean); that file is not imported here: by a walk of import
lines it would lay more than 700 further modules beneath this one. Two more laws of the library bear
the name: one has three of the four clauses, all but the ledger's
(Johnson/Desc/Sound/Clamp/FitsOfWide.lean); one goes the other way, from the state's readings to the
part (Johnson/Desc/Kinds/Law/K6RestAt.lean). The second clause of `segAt_parts` alone is the
library's `seg_fork` (Johnson/Desc/Kinds/Law/K6Silent.lean, Honest/Law/Rule/LedgerCallers.lean); the
`seg_fork` here has another end. `tapeCl_sent`: the library's law of that name
(Johnson/Road/K4/Claim4Heard.lean) has `getD 0` where this one has `headD`. `ownRun_level`: another
kind's law of that name has the same number at its own shape (Honest/K3/RowLaw.lean).

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.RowsLedger
import Johnson.Desc.ProofFile.Honest.K4.Law.RowKit
import Johnson.Desc.ProofFile.Honest.K4.Law.SumRowsStart
import Johnson.Desc.ProofFile.Honest.K4.Law.Sits
import Johnson.Desc.ProofFile.Honest.SumLaw.Counts
import Johnson.Desc.K4.Honest.Law.PtsSizes
import Johnson.Desc.ProofFile.Honest.Thread.Pays
import Johnson.Desc.ProofFile.Honest.Law.Run
import Johnson.Desc.First.K4.AtSHears
import Johnson.Desc.First.K4.ReadsAtS
import Johnson.Desc.First.Batch.SmallBehindDraw
import Johnson.Desc.ProofFile.Honest.K4.Law.OwnFits

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes (E zeroE oneE addE)
open OnBytes.Model (Reading Fork ledNS ledNP ledNO powers RoundName)
open OnBytes.Model.Layer (Own)
open OnBytes.K.Kc (paired leading)
open OnBytes.PscRun (Sized Later)
open OnBytes.Desc.First.K4 (Par blockAtS hearFl entries seatS k0 rowBatchForm heard_reads
  blockAtS_hears seatS_fork)
open OnBytes.Desc.First.K4.Honest
open VerifiableInference.Desc (Block Claim First.S)
open VerifiableInference.Desc.K9 (segAt? segAt_of)
open VerifiableInference.Desc.Sound (MsgQ dataQ)
open VerifiableInference.Desc.Part.MaskedSum (Call Var Ends ownSlots)
open ProofFile.Honest.SumLaw (sumPart_moves sumGs_count)

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb : Type}

/-! ## 0 A hypothesis's form -/

/-- **At the state s the layers' segment's ledger has arrays of its size.** It is the clause `sized`
of the library's `KeptAsks` (Johnson/Road/K4/Total/AtKept.lean). It is a definition: a
hypothesis's form. Nothing is claimed of it. -/
def K4SizedAt (s : First.S) : Prop := ∀ a, s.here = .lay a → Sized a.F

/-! ## 1 Behind the step -/

/-- What the open segment's part holds of the state. -/
theorem segAt_parts {s : First.S} {a : VerifiableInference.Desc.K9.Part} (h : segAt? s = some a) :
    s.link? = some a.L ∧ s.fork? = some a.F ∧ a.d.st = s.st ∧ a.d.book = s.book := by
  unfold segAt? at h
  cases hL : s.link? with
  | none =>
    rw [hL] at h
    exact nomatch h
  | some L =>
    cases hF : s.fork? with
    | none =>
      rw [hL, hF] at h
      exact nomatch h
    | some F =>
      cases ht : s.tl? with
      | none =>
        rw [hL, hF, ht] at h
        exact nomatch h
      | some tl =>
        rw [hL, hF, ht] at h
        obtain rfl := Option.some.inj h
        exact ⟨rfl, rfl, rfl, rfl⟩

/-- **Where the kind's sub-protocol accepts, a layers' segment is open in front**, and the open
segment's ledger is that segment's. -/
theorem step_front {p : Par} {s s' : First.S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : (blockAtS p).decide s rs gs = .ok s') :
    ∃ a a₀, segAt? s = some a ∧ s.here = .lay a₀ ∧ a.F = a₀.F := by
  obtain ⟨a₀, _, _, _, ha, _⟩ := heard_reads h
  obtain ⟨a, h1, _, h2, _⟩ := segAt_of s a₀.L a₀.F a₀.tl (by simp [First.S.link?, ha])
    (by simp [First.S.fork?, ha]) (by simp [First.S.tl?, ha])
  exact ⟨a, a₀, h1, ha, h2⟩

/-- **Where the kind's sub-protocol accepts**: the hearing's return on the tape of the rounds, from
the open segment's ledger in front to the one behind, at what the lookup in front has returned; what
was heard is laid. -/
theorem step_hears {p : Par} {s s' : First.S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : (blockAtS p).decide s rs gs = .ok s')
    {a a' : VerifiableInference.Desc.K9.Part} (ha : segAt? s = some a)
    (ha' : segAt? s' = some a') :
    ∃ fo o, hearFl { p.P with tokv := s.tokv } p.hp p.g fo a.F (paired rs (entries p.P p.hp p.g)) =
        some (o, a'.F, []) ∧ seatS.own s' = some o ∧ seatS.look s = some fo := by
  obtain ⟨a₀, fo, o, G, h0, _, hfo, _, _, hh, e⟩ := blockAtS_hears h
  have f0 : s.fork? = some a₀.F := by simp [First.S.fork?, h0]
  have f1 : s'.fork? = some G := by
    rw [e]
    rfl
  have e0 : a.F = a₀.F := Option.some.inj ((segAt_parts ha).2.1.symm.trans f0)
  have e1 : a'.F = G := Option.some.inj ((segAt_parts ha').2.1.symm.trans f1)
  refine ⟨fo, o, ?_, ?_, ?_⟩
  · rw [e0, e1]
    exact hh
  · rw [e]
    rfl
  · simp [seatS, h0, hfo]

/-- **The witness's data are read behind the step as in front of it.** -/
theorem step_data {p : Par} {s s' : First.S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : (blockAtS p).decide s rs gs = .ok s')
    {a a' : VerifiableInference.Desc.K9.Part} (ha : segAt? s = some a)
    (ha' : segAt? s' = some a') (own : List (Nat × Nat)) (rd : Nat × Nat → MsgQ) :
    dataQ own a' rd = dataQ own a rd := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hR⟩ := heard_reads h
  obtain ⟨l0, _, s0, b0⟩ := segAt_parts ha
  obtain ⟨l1, _, s1, b1⟩ := segAt_parts ha'
  have eL : a'.L = a.L := Option.some.inj (l1.symm.trans (hR.link.trans l0))
  have eS : a'.d.st = a.d.st := s1.trans (hR.st.trans s0.symm)
  have eB : a'.d.book = a.d.book := b1.trans (hR.book.trans b0.symm)
  unfold dataQ
  rw [eL, eS, eB]

/-- **The seat's ledger is the open segment's**, where the seat holds what K4 has heard. -/
theorem seg_fork {s' : First.S} {A : VerifiableInference.Desc.K9.Part} {o : Own}
    (hA : segAt? s' = some A) (ho : seatS.own s' = some o) : seatS.fork s' = A.F := by
  cases hh : s'.here with
  | lay a =>
    have f : s'.fork? = some a.F := by simp [First.S.fork?, hh]
    rw [seatS_fork hh]
    exact Option.some.inj (f.symm.trans (segAt_parts hA).2.1)
  | _ => simp [seatS, hh] at ho

/-- **The prover's run behind the member**: the input is kept; the challenges heard are those in
front with the member's own. -/
theorem moved_state {T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb}
    {blk : Block First.S Claim} {k : Coins Bk} {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc Xi Tr) X}
    {cols : List VerifiableInference.Desc.OpenedColumn} (h : T.Moved blk k m E ds y cols) :
    y.2.st.input = m.st.input ∧ y.2.st.heard = m.st.heard ++ ds := by
  obtain ⟨⟨l, _, hy⟩, _⟩ := h
  exact ⟨(play_mid l ds [] m y hy).1, play_heard l ds [] m y hy⟩

/-! ## 2 Public numbers of the row -/

section
variable (cells : Tr → Cells) (weights : W₀ → Weights) (tokens : Xi → Array Nat)
  (lk : List Fmt.Drawn → OnBytes.Model.Forest.Heard) (Q : K4Pub)

/-- The number of rounds in front of the norms' sums, in the first group and in a later one. -/
theorem k0_cases (g : Nat) : ((g == 0) = true ∧ k0 g = 3) ∨ ((g == 0) = false ∧ k0 g = 1) := by
  unfold k0
  cases h : (g == 0) with
  | true => exact Or.inl ⟨rfl, rfl⟩
  | false => exact Or.inr ⟨rfl, rfl⟩

/-- Seating a row's parts leaves the numbers of their rounds. -/
theorem movesTo_lift {V W Z V' W' Y : Type} (see : V → V') (wit : W → W') (get : Z → Y)
    (set : Z → Y → Z) : ∀ (ps : List (Part V' W' Y)) (i : Nat),
    movesTo (ps.map fun p => p.lift see wit get set) i = movesTo ps i
  | [], i => by simp [movesTo]
  | _ :: _, 0 => rfl
  | p :: ps, i + 1 => by
    have ih := movesTo_lift see wit get set ps i
    simp only [movesTo, List.map_cons, List.take_succ_cons, List.sum_cons] at ih ⊢
    rw [ih]
    simp [Part.lift]

/-- Seating a row's parts leaves the runs that they spend. -/
theorem spentTo_lift {V W Z V' W' Y : Type} (see : V → V') (wit : W → W') (get : Z → Y)
    (set : Z → Y → Z) : ∀ (ps : List (Part V' W' Y)) (i : Nat),
    spentTo (ps.map fun p => p.lift see wit get set) i = spentTo ps i
  | [], i => by simp [spentTo]
  | _ :: _, 0 => rfl
  | p :: ps, i + 1 => by
    have ih := spentTo_lift see wit get set ps i
    simp only [spentTo, List.map_cons, List.take_succ_cons, List.sum_cons] at ih ⊢
    rw [ih]
    rfl

/-- Quiet parts in front: one round each, no coin. -/
theorem movesTo_quiet (n : Nat) (l : List (Part Unit K4In Unit)) (i : Nat) :
    movesTo (List.replicate n k4Quiet ++ l) (n + i) = n + movesTo l i := by
  induction n with
  | zero => simp [movesTo]
  | succ n ih =>
    have e : n + 1 + i = (n + i) + 1 := by omega
    rw [e, List.replicate_succ, List.cons_append]
    simp only [movesTo, List.take_succ_cons, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    show 1 + (n + _) = n + 1 + _
    omega

/-- The like for the spent coins. -/
theorem spentTo_quiet (n : Nat) (l : List (Part Unit K4In Unit)) (i : Nat) :
    spentTo (List.replicate n k4Quiet ++ l) (n + i) = spentTo l i := by
  induction n with
  | zero => simp [spentTo]
  | succ n ih =>
    have e : n + 1 + i = (n + i) + 1 := by omega
    rw [e, List.replicate_succ, List.cons_append]
    simp only [spentTo, List.take_succ_cons, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    show 0 + _ = _
    omega

/-- A masked sumcheck with end values has three rounds more than variables. -/
theorem k4Sum_moves (sh : Call) (owner : String) (job : K4Pub → K4In → Pts → Option Job) (i : Nat)
    (e : Ends) (he : sh.ends = some e) :
    (k4Sum Q sh owner job i).moves.length = sh.vs.length + 3 := by
  unfold k4Sum
  rw [sumPart_moves]
  refine (List.length_map _).trans ?_
  rw [sumGs_count]
  show sh.vs.length + (match sh.ends with
    | none => 1
    | some _ => 3) = _
  rw [he]

/-- It spends its first run and its end values' run. -/
theorem k4Sum_coins (sh : Call) (owner : String) (job : K4Pub → K4In → Pts → Option Job) (i : Nat)
    (e : Ends) (he : sh.ends = some e) :
    coinsIn (k4Sum Q sh owner job i) = ownRun sh + e.n := by
  show (((runName maskRowRun (k4Addr Q i) "sum", (⟨0, ownRun sh⟩ : Due)) ::
    endRuns (runName owner (k4Addr Q i) "ends") sh.ends).map (·.2.e)).sum = _
  rw [he]
  simp [endRuns]

/-- Two for each of n variables of degree bound 3. -/
theorem foldl_points : ∀ (n k : Nat),
    (List.replicate n (Var.point zeroE 3)).foldl (fun n v => n + (v.d - 1)) k = k + 2 * n
  | 0, _ => rfl
  | n + 1, k => by
    rw [List.replicate_succ, List.foldl_cons, foldl_points n]
    show k + (3 - 1) + 2 * n = k + 2 * (n + 1)
    omega

/-- How many coins the first run of a sumcheck over the tokens holds. -/
theorem ownRun_token (lt dY n : Nat) : ownRun (k4TokenShape lt dY n) = 2 * lt + dY + 2 := by
  show 1 + ownSlots (List.replicate lt (Var.point zeroE 3) ++ [Var.point zeroE (dY + 1)]) = _
  unfold ownSlots
  rw [List.foldl_append, foldl_points]
  show 1 + (1 + 2 * lt + (dY + 1 - 1)) = _
  omega

/-- How many coins the first run of a product level's sumcheck holds. -/
theorem ownRun_level (mu : Nat) : ownRun (k4LevelShape mu) = 2 * mu + 3 := by
  show 0 + ownSlots (List.replicate mu (Var.point zeroE 3) ++ [Var.point zeroE (2 + 1)]) = _
  unfold ownSlots
  rw [List.foldl_append, foldl_points]
  show 0 + (1 + 2 * mu + (2 + 1 - 1)) = _
  omega

end

/-! ## 3 The row products and their job; the tape; the challenges as played -/

/-- The row products read of the sampled values what the lookup in front has sampled and the token
point, and nothing else. -/
theorem rowProducts_congr (Q : K4Pub) (w : K4In) (p p' : Pts) (hfo : p.fo = p'.fo)
    (hPV : p.PV = p'.PV) : rowProducts Q w p = rowProducts Q w p' := by
  unfold rowProducts rowMaps OnBytes.Desc.First.K4.Honest.envOf
  rw [hfo, hPV]

/-- The job of the sumcheck on the row products is made of the rows' tables. -/
theorem jobRows_maps {Q : K4Pub} {w : K4In} {p : Pts} {j : Job} (h : jobRows Q w p = some j) :
    ∃ ms, rowMaps Q w p = some ms ∧ j = rowsJobOf Q p ms := by
  rw [jobRows_eq] at h
  obtain ⟨ms, h1, h2⟩ := Option.bind_eq_some_iff.1 h
  split at h2
  · exact ⟨ms, h1, (Option.some.inj h2).symm⟩
  · cases h2

/-- Its lead is its cube's total. -/
theorem jobRows_lead {Q : K4Pub} {w : K4In} {p : Pts} {j : Job} (h : jobRows Q w p = some j) :
    j.lead = [j.cube.total] := by
  obtain ⟨ms, _, rfl⟩ := jobRows_maps h
  rfl

/-- The sum that a tape's first round claims is the first word that it sent. -/
theorem tapeCl_sent (t : OnBytes.K.Kc.Tape) :
    OnBytes.Desc.First.P1.tapeCl t = (OnBytes.Desc.First.P1.sentOf t).headD zeroE := by
  cases t <;> rfl

/-- The challenges of the rounds as played are those of the list. -/
theorem played_drawn {W Z : Type} {l : List (Step W Z)} {ds : List Fmt.Drawn} {m : Mid W Z}
    {y : List Played × Mid W Z} (hy : play l ds [] m = .ok y) (n : Nat) :
    ((roundsOf y.1)[n]?).map (·.drawn) = ds[n]? := by
  have h := yields_drawn l ds [] y.1 (play_yields l ds [] m y hy)
  rw [← List.getElem?_map, h]

/-! ## 4 At the seat -/

section
variable {T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb} {b : Nat}
  {cells : Tr → Cells} {weights : W₀ → Weights} {tokens : Xi → Array Nat}
  {look : K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard} {Q : K4Pub} {p : Par}
  {blk : Block First.S Claim}

/-- The public test holds that K4 covers the plan. -/
theorem fits_covers {Q : K4Pub} {fo : OnBytes.Model.Forest.Heard} {tokv : Array Nat}
    (h : k4Fits Q fo tokv = true) : OnBytes.Desc.First.K4.covers Q.P = true := by
  unfold k4Fits k4TableFits at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1.1.1.1.1.1.1

/-- **FROM THE MEMBER's OWN STEP TO THE HEARING's RETURN ON THE TAPE OF THE PLAYED ROUNDS**, in the
public data's letters. General in what is then read off the return: no slot and no claim is named.
a: the open segment's part in front. a₀: the layers' segment in front. fo: what the lookup in front
has returned. -/
theorem step_tape (Se : K4Seated T b cells weights tokens look Q p blk) (hSit : K4Sits T b p)
    {k : Coins Bk} {s s' : First.S} {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc Xi Tr) X}
    {cols : List VerifiableInference.Desc.OpenedColumn} (hS : T.Stepped blk k s m E ds y cols s')
    {A : VerifiableInference.Desc.K9.Part} {o : Own} (hA : segAt? s' = some A)
    (ho : seatS.own s' = some o) :
    ∃ a a₀ fo, segAt? s = some a ∧ s.here = .lay a₀ ∧ a.F = a₀.F ∧ a₀.fo = some fo ∧
      hearFl { Q.P with tokv := s.tokv } Q.hp Q.g fo a.F
        (paired (roundsOf y.1) (entries Q.P Q.hp Q.g)) = some (o, A.F, []) ∧
      ∀ own rd, dataQ own A rd = dataQ own a rd := by
  obtain ⟨gs, hdec⟩ := hSit blk Se.member s _ _ s' _ hS.2
  obtain ⟨a, a₀, ha, ha0, haF⟩ := step_front hdec
  obtain ⟨fo, o', hh, ho', hlk⟩ := step_hears hdec ha hA
  obtain rfl : o' = o := Option.some.inj (ho'.symm.trans ho)
  obtain ⟨eP, eh, eg, _, _⟩ := Se.own
  rw [paired_noDigest, eP, eh, eg] at hh
  have hfo : a₀.fo = some fo := by
    simpa [seatS, ha0] using hlk
  exact ⟨a, a₀, fo, ha, ha0, haF, hfo, hh, fun own rd => step_data hdec ha hA own rd⟩

end

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.K4SizedAt
#print axioms ProofFile.Honest.K4.segAt_parts
#print axioms ProofFile.Honest.K4.step_front
#print axioms ProofFile.Honest.K4.step_hears
#print axioms ProofFile.Honest.K4.step_data
#print axioms ProofFile.Honest.K4.seg_fork
#print axioms ProofFile.Honest.K4.moved_state
#print axioms ProofFile.Honest.K4.k0_cases
#print axioms ProofFile.Honest.K4.movesTo_lift
#print axioms ProofFile.Honest.K4.spentTo_lift
#print axioms ProofFile.Honest.K4.movesTo_quiet
#print axioms ProofFile.Honest.K4.spentTo_quiet
#print axioms ProofFile.Honest.K4.k4Sum_moves
#print axioms ProofFile.Honest.K4.k4Sum_coins
#print axioms ProofFile.Honest.K4.foldl_points
#print axioms ProofFile.Honest.K4.ownRun_token
#print axioms ProofFile.Honest.K4.ownRun_level
#print axioms ProofFile.Honest.K4.rowProducts_congr
#print axioms ProofFile.Honest.K4.jobRows_maps
#print axioms ProofFile.Honest.K4.jobRows_lead
#print axioms ProofFile.Honest.K4.tapeCl_sent
#print axioms ProofFile.Honest.K4.played_drawn
#print axioms ProofFile.Honest.K4.fits_covers
#print axioms ProofFile.Honest.K4.step_tape
