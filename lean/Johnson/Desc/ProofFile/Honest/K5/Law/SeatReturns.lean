-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/SeatReturns.lean: CONDITIONAL: under the hypothesis `P5J.AtMgA`
the maker of the public data of the kind "an attention segment's own rounds" (K5) YIELDS at each of
the twelve groups, wherever its third test says yes: of its three tests with code (`Seat5.fits`,
`Seat5.roundsFit`, Honest/K5/Row.lean; `Seat5.keysFit`, Honest/K5/KeysFit.lean), UNDER THAT
HYPOTHESIS, the third's yes gives the other two. And the member's debts with "the maker yields"
struck from the premises.

Clause by clause. The ground has the group's plan (the description's maker's own ground). The table
of steps has the place's first step, and counts the rounds in front of the member (`base_at_head`,
Honest/K5/Law/BaseAt.lean). `Seat5.fits`: the declared rounds in front are just so many; the
verifier's function for the named points returns at key points of the calls' lengths, and then the
lists have their lengths (`aloneOk_at_head`, Johnson/Desc/K5/Honest/Law/PointsReturn.lean).
`Seat5.roundsFit`: the declared rounds from there on are the member's own, which are the verifier's
rounds at the plan's numbers (`k5_member`, Honest/K5/Law/Member.lean): so under the hypothesis the
second test is a consequence, not a check; it checks where no such hypothesis is in hand.

  `ground_at_head`, `seat_pub_at_head`   the ground's public parameters; what the maker yields holds
                     the plan's shape and numbers and the segment's number
  `decls_drop`       GENERAL: the rounds behind a border are the rest of all the list's rounds
  `seatOf`           the public data that the maker yields at group g, written out; its number of
                     rounds in front is written off the flat list: that the table of steps counts
                     the same is `base_at_head`
  `roundsFit_at_head`, `fits_at_head`   CONDITIONAL: the second test; the first, from the third
  `seatAt_returns_at_head`   CONDITIONAL: **the third test's yes ⟹ `seatAt` and `seatAtK` yield
                     `seatOf`**
  `k5_owes_keys`     CONDITIONAL: the member's debts (`k5_owes_laidK`, Honest/K5/Law/LotLaid.lean)
                     without "the maker yields"

WHAT STAYS ON THE PUBLIC SIDE beside the hypothesis: two sentences on the letter keyOf, the reader
of the key points: at challenges that are all 0, of the shapes of the declared rounds in front, its
key points have the calls' lengths (the third test: hKey); their sizes are the same at all
challenges of the same shapes (`KeySizes`: hK). Whoever lays keyOf is meant to pay both.

Limits. Every theorem is conditional; the hypothesis is not shown here. `k5_owes_keys` keeps
`SayOwed` and `JoinOwed`, which hold the clauses on values of two of the six items owed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.LotLaid
import Johnson.Desc.K5.Honest.Law.PointsReturn

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc (Block Strs Chain)
open VerifiableInference.Desc.First.Att.P (entriesOf script)
open H2K5.Honest (K5Keeps aloneOk_at_head)
open ProofFile.Honest.FirstThread (Script WtF)
open P5J (AtMgA TS CellsM)

/-- The rounds behind a border are the rest of all the list's rounds. General in the list. No
premise. -/
theorem decls_drop {S Cl : Type} (bs : List (Block S Cl)) (b : Nat) :
    (bs.flatMap (·.rounds)).drop (roundsTo bs b) = (bs.drop b).flatMap (·.rounds) := by
  have e : bs.flatMap (·.rounds) = declsTo bs b ++ (bs.drop b).flatMap (·.rounds) := by
    unfold declsTo
    rw [← List.flatMap_append, List.take_append_drop]
  rw [e]
  exact List.drop_left' rfl

/-- **The public data that the maker yields at group g**, written out: the segment's number, the
plan's shape and numbers, the rounds in front of the member, the reader of the key points. -/
def seatOf (keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array OnBytes.E)) (Zp : ProofFile.Pub)
    (G : Ground) (cF : Chain TS ProofFile.Cl) (g : Nat) (a : Attention.Plan) : Seat5 :=
  ⟨2 * g + 1, ⟨a.S, a.own⟩, roundsTo cF.blocksInOrder (borderOf g), keyOf Zp G (2 * g + 1)⟩

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
  {keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array OnBytes.E)} {G : Ground}
include h

/-- The ground's public parameters are the description's. CONDITIONAL: under the hypothesis h; hG: G
is the ground that the description's maker makes. -/
theorem ground_at_head (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) :
    G.W = P5J.At.X Zp := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain rfl : Bs.G₀ = G := Option.some.inj (O.blank.symm.trans hG)
  exact O.W

/-- What the maker yields holds the plan's shape and numbers, and the segment's number.
CONDITIONAL: under the hypothesis h; hG; hY: the maker yields; ha: the group's plan. -/
theorem seat_pub_at_head (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {l : Nat} {nm : String}
    {g : Nat} {Z5 : Seat5} (hY : seatAt keyOf Zp G l nm g = some Z5) {a : Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a) : Z5.P = ⟨a.S, a.own⟩ ∧ Z5.link = l := by
  obtain ⟨A, base, hA, -, rfl, -, -⟩ := seatAt_spec hY
  rw [ground_at_head h hG, ha] at hA
  obtain rfl := Option.some.inj hA
  exact ⟨rfl, rfl⟩

/-- The declared rounds in front of the member are the first so many of all declared rounds.
CONDITIONAL: under the hypothesis h. -/
theorem front_at_head' (b : Nat) : Zp.D.1.take (roundsTo cF.blocksInOrder b) = declsTo cF.blocksInOrder b := by
  rw [declsTo_take, h.laid.decl₁]

/-- **The second test says yes.** CONDITIONAL: under the hypothesis h; g is below 12; ha. -/
theorem roundsFit_at_head {g : Nat} (hg : g < 12) {a : Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a) :
    (seatOf keyOf Zp G cF g a).roundsFit Zp.D.1 = true := by
  obtain ⟨blk, a', hb, hP, hD⟩ := k5_member h hg
  obtain rfl : a' = a := Option.some.inj (hP.plan.symm.trans ha)
  have hlt : borderOf g < cF.blocksInOrder.length := (List.getElem?_eq_some_iff.1 hb).1
  have hbk : cF.blocksInOrder[borderOf g] = blk := (List.getElem?_eq_some_iff.1 hb).2
  have er : blk.rounds = (entriesOf 0 (script a'.own)).map fun e =>
      { entry := if e.drawE == 0 then e else { e with work := (parAt Zp g a').work } } :=
    hD.rounds
  have el : blk.rounds.length = (entriesOf 0 (script a'.own)).length := by
    rw [er, List.length_map]
  show ((((Zp.D.1.drop (roundsTo cF.blocksInOrder (borderOf g))).take
      (entriesOf 0 (script a'.own)).length).map
        fun r => (r.entry.name, r.entry.msg, r.entry.drawE)) ==
    (entriesOf 0 (script a'.own)).map fun y => (y.name, y.msg, y.drawE)) = true
  rw [← h.laid.decl₁, decls_drop, List.drop_eq_getElem_cons hlt, hbk, List.flatMap_cons,
    List.take_left' el, er, List.map_map, beq_iff_eq]
  refine List.map_congr_left fun e _ => ?_
  show ((if e.drawE == 0 then e else { e with work := _ }).name,
    (if e.drawE == 0 then e else { e with work := _ }).msg,
    (if e.drawE == 0 then e else { e with work := _ }).drawE) = _
  split <;> rfl

/-- **The first test says yes wherever the third does.** CONDITIONAL: under the hypothesis h; g is
below 12; ha; hKey: the third test's yes at challenges that are all 0, of the shapes of the declared
rounds in front. -/
theorem fits_at_head {g : Nat} (hg : g < 12) {a : Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a)
    (hKey : (seatOf keyOf Zp G cF g a).keysFit
      (blankDraws (Zp.D.1.take (roundsTo cF.blocksInOrder (borderOf g)))) = true) :
    (seatOf keyOf Zp G cF g a).fits
      (blankDraws (Zp.D.1.take (roundsTo cF.blocksInOrder (borderOf g)))) = true := by
  have hl : (blankDraws (Zp.D.1.take (roundsTo cF.blocksInOrder (borderOf g)))).length =
      roundsTo cF.blocksInOrder (borderOf g) := by
    unfold blankDraws
    rw [List.length_map, front_at_head' h]
    rfl
  unfold Seat5.fits
  rw [Bool.and_eq_true, beq_iff_eq]
  exact ⟨hl, aloneOk_at_head h hg ha (beq_iff_eq.1 hKey)⟩

/-- **THE THIRD TEST's YES ⟹ THE MAKER YIELDS**, with two tests and with three. CONDITIONAL: under
the hypothesis h, which is not shown here; g is below 12; hG; ha; hKey. -/
theorem seatAt_returns_at_head {g : Nat} (hg : g < 12)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {a : Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a)
    (hKey : (seatOf keyOf Zp G cF g a).keysFit
      (blankDraws (Zp.D.1.take (roundsTo cF.blocksInOrder (borderOf g)))) = true) :
    seatAt keyOf Zp G (2 * g + 1) ("A" ++ toString g) g = some (seatOf keyOf Zp G cF g a) ∧
      seatAtK keyOf Zp G (2 * g + 1) ("A" ++ toString g) g =
        some (seatOf keyOf Zp G cF g a) := by
  have e1 : G.W.A[g]? = some a := by
    rw [ground_at_head h hG]
    exact ha
  have hs : seatAt keyOf Zp G (2 * g + 1) ("A" ++ toString g) g =
      some (seatOf keyOf Zp G cF g a) := by
    unfold seatAt
    rw [e1, Option.bind_some, base_at_head h hg, Option.bind_some]
    exact if_pos (by
      rw [Bool.and_eq_true]
      exact ⟨fits_at_head h hg ha hKey, roundsFit_at_head h hg ha⟩)
  refine ⟨hs, ?_⟩
  unfold seatAtK
  rw [hs, Option.bind_some]
  exact if_pos hKey

end

section
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

/-- **THE MEMBER's DEBTS WITHOUT "THE MAKER YIELDS"**: it plays; behind its yes; the exchange; it is
accepted, for every fall. CONDITIONAL: as `k5_owes_laidK`, with hKey, the third test's yes, in the
stead of hY. hKey and hK are sentences on the letter keyOf, asked at the plan of the group: there is
just one. `SayOwed`, `JoinOwed` HOLD THE CLAUSES ON VALUES of two of the six items owed. -/
theorem k5_owes_keys {n g : Nat} (hg : g < 12)
    {keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array OnBytes.E)} {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G)
    (hKey : ∀ a, (P5J.At.X Zp).A[g]? = some a → (seatOf keyOf Zp G cF g a).keysFit
      (blankDraws (Zp.D.1.take (roundsTo cF.blocksInOrder (borderOf g)))) = true)
    (hK : ∀ a, (P5J.At.X Zp).A[g]? = some a → KeySizes (seatOf keyOf Zp G cF g a))
    {cells : Tr → Cells} (hL : LotLaid hs (seatAtK keyOf Zp G) cells G)
    (hfit : (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).fits n = true)
    (hb : borderOf g < n)
    (Kp : ∀ s s', K5Keeps s s' → keeps (borderOf g) s s')
    (Rd : ∀ w s s', rides (borderOf g) w s → K5Keeps s s' → rides (borderOf g + 1) w s')
    (hans : AnsReadsRest ans ((P5J.At.N Zp cF).sent (2 * g + 1) 0))
    (hSay : ∀ a, (P5J.At.X Zp).A[g]? = some a →
      SayOwed h hs Q stored ans test carryX item n₁ n₂ valid rides keeps g a)
    (hJ : ∀ a, (P5J.At.X Zp).A[g]? = some a →
      JoinOwed h hs Q stored ans test carryX item n₁ n₂ valid rides keeps g a) :
    Plays (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) (borderOf g) ∧
      Behind (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) (borderOf g) ∧
      Exchange (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) (borderOf g) ∧
      ∀ fall, Accepted (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) fall
        (borderOf g) := by
  obtain ⟨-, a, -, hP, -⟩ := k5_member h hg
  exact k5_owes_laidK h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hg hG
    (seatAt_returns_at_head h hg hG hP.plan (hKey a hP.plan)).2 (hK a hP.plan) hL hfit hb Kp Rd hans
    hSay hJ

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.decls_drop
#print axioms ProofFile.Honest.K5.ground_at_head
#print axioms ProofFile.Honest.K5.seat_pub_at_head
#print axioms ProofFile.Honest.K5.front_at_head'
#print axioms ProofFile.Honest.K5.roundsFit_at_head
#print axioms ProofFile.Honest.K5.fits_at_head
#print axioms ProofFile.Honest.K5.seatAt_returns_at_head
#print axioms ProofFile.Honest.K5.k5_owes_keys
