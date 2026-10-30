-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/SeatedAt.lean: CONDITIONAL: the premise `K5Seated`
(Honest/K5/Law/Seated.lean) ASSEMBLED at the first chain's `Thread` at the library's own letters
(`thrAt`, Honest/K5/Law/Ready.lean), for each group of layers; and with it the two debts `Plays` and
`Accepted` (Honest/Thread/Pays.lean) at the kind's member, without `K5Seated` as a premise.
Statements with their proofs.

  `seatAt_spec`   what the maker of a place's public data yields, where it yields (`seatAt`,
      Honest/K5/Row.lean): the plan's numbers, the count of rounds in front off the table of steps,
      and a yes of its two tests
  `declsTo_take`   the rounds in front of a border are a first stretch of all the list's rounds
  `k5Seated_at`   **the seven clauses**, from the member as `k5_member` hands it out
      (Honest/K5/Law/Member.lean), a return of `seatAt`, and four named premises
  `k5Seated_head`   the same with the member and the plan drawn from the hypothesis h
  `k5_plays_accepted`   **`Plays`, and `Accepted` at every fall**

WHAT IS PAID HERE. `member`, `place`, `rounds`, `oracles`: by `k5_member`. `own`: `seatAt` lays the
plan's own numbers. `fits`: `seatAt`'s first test, asked at challenges that are all 0, carried to
every list that the rounds in front can draw by `fits_of_blank` (Honest/K5/Law/Fits.lean); that the
rounds in front are the first `base` of the public part's declared rounds: by the library's
`LaidAt.decl₁` (Johnson/P5J/DeclIsPub.lean) and hbase.

THE FOUR NAMED PREMISES, each with who is meant to show it.
  hW : G.W = P5J.At.X Zp   the ground of which the public data are made holds what `verify-on-bytes`
      derives from the public files, as the public part has it. At the description's
      maker's own ground the library has it (`H2K5.Door.open_all`,
      Johnson/Desc/First/Att/Door/Law/K5AtConstant.lean). Whoever lays the ground calls that.
  hbase : Z5.base = roundsTo cF.blocksInOrder (borderOf g)   THE COUNT OFF THE TABLE OF STEPS IS THE NUMBER
      OF ROUNDS OF THE FLAT LIST IN FRONT OF THE MEMBER. Under h, at the segment's own name, it is
      shown: `hbase_at` (Honest/K5/Law/BaseAt.lean, which imports this file). `seatAt`'s second test
      does not give it: twelve segments have rounds of one shape.
  hK : KeySizes Z5   the key points' lengths hang on the challenges' numbers of elements alone.
      Whoever lays the reader of the key points.
  hh : the list of halves holds `k5Half cells Z5` for the place. Whoever lays the list of halves.
And hY, the return of `seatAt`: shown at no public files. And h, the one hypothesis that ties the
library's letters to the proof file's description: not shown here.

Limits. Every theorem is conditional. None of hY, hK, hh is shown anywhere; where they or h cannot
be met the theorems say nothing. Nothing is said of a value that is sent.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.Fits
import Johnson.Desc.ProofFile.Honest.K5.Law.Accepted
import Johnson.P5J.DeclIsPub

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open VerifiableInference.Desc (Block Chain Strs)
open ProofFile.Honest.FirstThread (Script WtF)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS CellsM)

/-! ## 1 What `seatAt` yields -/

/-- **What the maker of a place's public data yields, where it yields.** -/
theorem seatAt_spec {keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array OnBytes.E)}
    {Zp : Pub} {G : Ground} {l : Nat} {nm : String} {g : Nat} {Y : Seat5}
    (h : seatAt keyOf Zp G l nm g = some Y) :
    ∃ A base, G.W.A[g]? = some A ∧ Zp.roundsBefore? (nm ++ ".2.scores") = some base ∧
      Y = ⟨l, ⟨A.S, A.own⟩, base, keyOf Zp G l⟩ ∧
      Y.fits (blankDraws (Zp.D.1.take base)) = true ∧ Y.roundsFit Zp.D.1 = true := by
  unfold seatAt at h
  obtain ⟨A, hA, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨base, hb, h⟩ := Option.bind_eq_some_iff.1 h
  simp only at h
  split at h
  · rename_i hc
    obtain rfl := Option.some.inj h
    rw [Bool.and_eq_true] at hc
    exact ⟨A, base, hA, hb, rfl, hc.1, hc.2⟩
  · cases h

/-! ## 2 The rounds in front of a border -/

/-- The rounds in front of a border are a first stretch of all the list's rounds. -/
theorem declsTo_take {S Cl : Type} (bs : List (Block S Cl)) (b : Nat) :
    declsTo bs b = (bs.flatMap (·.rounds)).take (roundsTo bs b) := by
  have e : bs.flatMap (·.rounds) = declsTo bs b ++ (bs.drop b).flatMap (·.rounds) := by
    unfold declsTo
    rw [← List.flatMap_append, List.take_append_drop]
  rw [e]
  exact (List.take_left' rfl).symm

/-! ## 3 At the first chain's `Thread` at the library's own letters -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr X : Type}
  (hs : List (Placed (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X))
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok
    VerifiableInference.Desc.Sound.MsgT)
  (stored : Local W₀ Rc ProofFile.Inst Tr → Nat → Nat → Option (List UInt64))
  (ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (test : Nat → TS → Option String)
  (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ : Nat)
  (valid : Local W₀ Rc ProofFile.Inst Tr → Prop) (rides : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
  (keeps : Nat → TS → TS → Prop)

/-- **`K5Seated` AT THE FIRST CHAIN's `Thread` AT THE LIBRARY's OWN LETTERS**, for the group g of
layers. CONDITIONAL: blk is the member at the border and decides as the kind's own decision (hb, hD:
`k5_member` hands both out); a is the group's plan (ha); `seatAt` has yielded Z5 at the segment's
number (hY); and the four named premises of this file's head: hW, hbase, hK, hh. -/
theorem k5Seated_at {g : Nat} {a : OnBytes.Attention.Plan} {blk : Block TS ProofFile.Cl}
    (hb : cF.blocksInOrder[borderOf g]? = some blk) (hD : DecidesAs (parAt Zp g a) blk)
    (ha : (P5J.At.X Zp).A[g]? = some a)
    {keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array OnBytes.E)} {G : Ground}
    {nm : String} {Z5 : Seat5} (hY : seatAt keyOf Zp G (2 * g + 1) nm g = some Z5)
    (hW : G.W = P5J.At.X Zp) (hbase : Z5.base = roundsTo cF.blocksInOrder (borderOf g))
    (hK : KeySizes Z5) {cells : Tr → Cells}
    (hh : hs.find? (fun q => q.place == Z5.place) = some (k5Half cells Z5)) :
    K5Seated (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) (borderOf g) cells
      Z5 (parAt Zp g a) blk := by
  obtain ⟨A, base, hA, -, rfl, hf, -⟩ := seatAt_spec hY
  rw [hW, ha] at hA
  obtain rfl := Option.some.inj hA
  have hp : blk.place = (⟨2 * g + 1, ⟨a.S, a.own⟩, base, keyOf Zp G (2 * g + 1)⟩ : Seat5).place :=
    hD.place
  refine ⟨hb, hp, hD.rounds, hD.oracles, rfl, by rw [hp]; exact hh, ?_⟩
  have hbase' : base = roundsTo cF.blocksInOrder (borderOf g) := hbase
  have e : declsTo cF.blocksInOrder (borderOf g) = Zp.D.1.take base := by
    rw [declsTo_take, h.laid.decl₁, hbase']
  show ∀ front, drawsFit ([] ++ declsTo cF.blocksInOrder (borderOf g)) front = true → _
  rw [List.nil_append, e]
  exact fits_of_blank _ hK _ hf

/-- **The same with the member and the plan drawn from the hypothesis h** (`k5_member`,
Honest/K5/Law/Member.lean). CONDITIONAL: as `k5Seated_at`, without its first three premises; g is
below 12. -/
theorem k5Seated_head {g : Nat} (hg : g < 12)
    {keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array OnBytes.E)} {G : Ground}
    {nm : String} {Z5 : Seat5} (hY : seatAt keyOf Zp G (2 * g + 1) nm g = some Z5)
    (hW : G.W = P5J.At.X Zp) (hbase : Z5.base = roundsTo cF.blocksInOrder (borderOf g))
    (hK : KeySizes Z5) {cells : Tr → Cells}
    (hh : hs.find? (fun q => q.place == Z5.place) = some (k5Half cells Z5)) :
    ∃ blk a, (P5J.At.X Zp).A[g]? = some a ∧
      K5Seated (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) (borderOf g)
        cells Z5 (parAt Zp g a) blk := by
  obtain ⟨blk, a, hb, hP, hD⟩ := k5_member h hg
  exact ⟨blk, a, hP.plan, k5Seated_at h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hb
    hD hP.plan hY hW hbase hK hh⟩

/-- **THE TWO DEBTS AT THE KIND's MEMBER OF GROUP g, WITHOUT `K5Seated` AS A PREMISE**: `Plays`, and
`Accepted` at every fall (Honest/Thread/Pays.lean). CONDITIONAL: as `k5Seated_head`. -/
theorem k5_plays_accepted {g : Nat} (hg : g < 12)
    {keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array OnBytes.E)} {G : Ground}
    {nm : String} {Z5 : Seat5} (hY : seatAt keyOf Zp G (2 * g + 1) nm g = some Z5)
    (hW : G.W = P5J.At.X Zp) (hbase : Z5.base = roundsTo cF.blocksInOrder (borderOf g))
    (hK : KeySizes Z5) {cells : Tr → Cells}
    (hh : hs.find? (fun q => q.place == Z5.place) = some (k5Half cells Z5)) :
    Plays (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) (borderOf g) ∧
      ∀ fall, Accepted (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) fall
        (borderOf g) := by
  obtain ⟨blk, a, ha, Hs⟩ := k5Seated_head h hs Q stored ans test carryX item n₁ n₂ valid rides
    keeps hg hY hW hbase hK hh
  exact ⟨k5_plays _ Hs, k5_accepted h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hg ha
    Hs⟩

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.k5Seated_head
#print axioms ProofFile.Honest.K5.k5_plays_accepted
#print axioms ProofFile.Honest.K5.seatAt_spec
#print axioms ProofFile.Honest.K5.declsTo_take
#print axioms ProofFile.Honest.K5.k5Seated_at
