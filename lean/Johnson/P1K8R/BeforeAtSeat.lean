-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/BeforeAtSeat.lean: THE SMALLNESS TEST: WHAT THE DRAWN MATRIX
MULTIPLIES IS SENT BEFORE THE MATRIX IS DRAWN: AT THE SEAT, AT ALL 25 PLACES OF THE PROOF FILE'S
DESCRIPTION. A JOINING. (A) (A') (B) (B') (E) ARE CLOSED IN SCOPE; (C) (D) STAND UNDER A TEST ON THE
RECORD IN FRONT OF THE DRAW, `Named.namedB`, WHICH NO LAW PAYS YET.

WHY. The count of the round of the draw (`Cb.Pv.Tail.cnt_bad_le`, Cb/Pv/Tail/Know.lean) holds for
each FIXED tuple of messages and each fixed explicit statement, over the drawn matrix. Its one
hypothesis is on sizes. It MEANS the round's error only where the protocol fixes these before the
draw: that is no hypothesis of the count: it is a fact to be shown of the description. Here it is
said over the plan, at the value of `onlineDescription` in the goals' scope.
  `places`: THE 25 PLACES, A WRITTEN LIST: (l, i) for l = 0 … 24: l: the link's number; i: the
    block's number, from 0, among the link's blocks in front of the batching: 4; at link 24, the
    head's, 5. The entry's number in the chain's flat list is 14 l + i + 2.
  `BeforeAt D flat p ix`: of a chain's declared rounds D, its flat list of blocks, a place's numbers
    p and a number ix in the list, with pre := the entries in front of ix:
    (A) the round behind pre's rounds is THE ROUND OF THE DRAW, `round p`;
    (A') the place names a tree for the matrices and a tree for the reads, and has a matrix;
    (B) every tree that the place names (`p.matsIn ++ p.readsIn`) is sent by a round STRICTLY IN
        FRONT of it, and its number is below the number of trees that pre's rounds send;
    (B') where such a tree has a sampled tenant, A ROUND WITH ANSWERS stands between the two: not
        tied here to this tree's own sample;
    (C) UNDER `Named.namedB p` at a statement, a book, a record tl and a link's record L: EVERY
        ARRAY THAT THE MATRIX MULTIPLIES (`Named.arrays tl`: each matrix's array of symbols,
        whichever link it was born at; the vectors of reads) lies, now, in a message that the
        statement and the book have, in a tree that is sent strictly in front of the round of the
        draw;
    (D) under the same: so does every member of the list of messages off which the law's caller
        reads (`Named.listOf`, `Named.seatFn`: the number that `namedCallerAt` gives a member), and
        its tree's number is below the number of trees that pre's rounds send: the stretch's base.
  `ListStays b`: (E) THE WEIGHTS: wherever the step of b goes on, the list of tables of the record
    in front is CLOSED, the record behind has that very list, closed, and the explicit statement of
    the law's letters (`recOf`, Johnson/Desc/First/K8/LawAtRecord.lean: the record without the two
    fields that the draw lays) is behind the step what it was in front.
  `beforeAt_false_of_late`, `beforeAt_false_of_unnamed`, `namedB_false_of_unnamed`: THE STATEMENT
    CAN FAIL: where a named tree is sent at or behind the round of the draw; where the place names
    no tree for the matrices; and the test of (C) says no where one array's tree is not named.
  `beforeAt_of_sits`: from `SitsAt` (Johnson/P1K8R/Sits.lean) and the file's test on the plan.
  `k08_before_at_seat`: **THE ROW**: in scope, from the value of `onlineDescription`, where the
    description's test on the plan says yes: at every (l, i) of `places`: the entry number
    14 l + i + 2 of the flat list is a block b with `ListStays b`, and `BeforeAt` holds there at the
    lot's own numbers.
Limits, said first. THAT `onlineDescription` RETURNS IN SCOPE IS A PREMISE. `F.planOk = true` IS A PREMISE: a
public test, which the description's run asks. (C) AND (D) ARE IMPLICATIONS FROM `Named.namedB`: a
test with code on the record in front of the draw; NO LAW SAYS YET THAT THE WALK'S RECORD MEETS IT.
That the record tl at which the test is asked is the record at which the law's letters are taken is
not said. A tree's number in the book is taken for its number in the first chain's order of sending.
MESSAGE-WISE: where inside a message an array's entries lie is not said. That the law's letters read
nothing but these members is the caller's (`CallerAt`). NOT IN IT: that the number of combinations
is 128 at the seat; that what is sent behind the draw (the digits) is not among the early entries;
that a tree sent in front binds one word. Nothing on soundness: no error term is stated here.

-/
import Johnson.P1K8R.Sits
import Johnson.Desc.First.K8.LawAtRecord

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1K8S

open Inst.Model
open OnBytes OnBytes.Model
open OnBytes.Model.Verify (publicOf)
open OnBytes.Model.Stages (LinkH)
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName OpenedColumn sendRound oraclesOf
  rootsIn)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K8
open ProofFile (Cl)

local notation "rIn" => VerifiableInference.Desc.roundsIn

/-- The 25 places: the link's number; the block's number among the link's blocks in front of the
batching. -/
def places : List (ℕ × ℕ) := (List.range 25).map fun l => (l, if l = 24 then 5 else 4)

/-- What the drawn matrix multiplies is sent before the matrix is drawn. -/
def BeforeAt (D : List Fmt.DeclaredRound) (flat : List (Block S Cl)) (p : Par) (ix : ℕ) : Prop :=
  D[rIn (flat.take ix)]? = some (round p) ∧
  (p.matsIn ≠ [] ∧ p.readsIn ≠ [] ∧ p.ks ≠ []) ∧
  (∀ n ∈ p.matsIn ++ p.readsIn, (∃ j, sendRound D n = some j ∧ j < rIn (flat.take ix)) ∧
    n < rootsIn (D.take (rIn (flat.take ix)))) ∧
  (∀ n ∈ p.matsIn ++ p.readsIn,
    ((oraclesOf flat)[n]?).any (fun o => o.tenants.any (·.sampled)) = true →
    ∃ j j' r, sendRound D n = some j ∧ D[j']? = some r ∧ r.entry.answers ≠ 0 ∧ j < j' ∧
      j' < rIn (flat.take ix)) ∧
  (∀ (S₀ : Statement) (book : TreeBook) (tl : HTailF2) (L : LinkCtx),
    Named.namedB p S₀ book tl L = true →
    (∀ t ∈ Named.arrays tl, ∃ o m j, Named.msgNow L t = some o ∧
      Named.memberAt S₀ book o = some m ∧ sendRound D m.2.1 = some j ∧
      j < rIn (flat.take ix)) ∧
    ∀ (rad : OracleShape → ℕ) (a : Fin (Named.listOf rad S₀ book tl L).length),
      (∃ j, sendRound D (Named.seatFn rad S₀ book tl L a).1 = some j ∧ j < rIn (flat.take ix)) ∧
        (Named.seatFn rad S₀ book tl L a).1 < rootsIn (D.take (rIn (flat.take ix))))

/-- The weights: the list of tables is closed in front of the draw, and the draw leaves it. -/
def ListStays (b : Block S Cl) : Prop :=
  ∀ (ft : Nat) (st st' : S) (k : Nat) (rs : List Fmt.RoundView) (cols : List OpenedColumn),
    b.step ft st rs cols = .ok (st', k) →
    ∃ tl tl', st.tl? = some tl ∧ tl.funClosed = true ∧ st'.tl? = some tl' ∧
      tl'.funClosed = true ∧ tl'.funs = tl.funs ∧ ∀ tl0, recOf tl0 st' = recOf tl0 st

/-! ## The statement can fail -/

/-- **A tooth of (B)**: where a tree that the place names is sent at or behind the round of the
draw, `BeforeAt` is false. -/
theorem beforeAt_false_of_late {D : List Fmt.DeclaredRound} {flat : List (Block S Cl)} {p : Par}
    {ix n j : ℕ} (hn : n ∈ p.matsIn ++ p.readsIn) (hj : sendRound D n = some j)
    (hl : rIn (flat.take ix) ≤ j) : ¬ BeforeAt D flat p ix := fun h => by
  obtain ⟨⟨j', e, hlt⟩, _⟩ := h.2.2.1 n hn
  obtain rfl : j = j' := Option.some.inj (hj.symm.trans e)
  omega

/-- **A tooth of (A')**: at a place that names no tree for the matrices `BeforeAt` is false: so (B)
is not met by an empty list. -/
theorem beforeAt_false_of_unnamed {D : List Fmt.DeclaredRound} {flat : List (Block S Cl)} {p : Par}
    {ix : ℕ} (h0 : p.matsIn = []) : ¬ BeforeAt D flat p ix := fun h => h.2.1.1 h0

/-- **A tooth of (C)'s test**: where one array that the matrix multiplies lies in a message whose
tree the place does not name, `Named.namedB` says no. -/
theorem namedB_false_of_unnamed {p : Par} {S₀ : Statement} {book : TreeBook} {tl : HTailF2}
    {L : LinkCtx} {t o : ℕ} {m : OracleShape × (ℕ × ℕ)} (ht : t ∈ Named.arrays tl)
    (h1 : Named.msgNow L t = some o) (h2 : Named.memberAt S₀ book o = some m)
    (h3 : m.2.1 ∉ p.matsIn ++ p.readsIn) : Named.namedB p S₀ book tl L = false := by
  cases hN : Named.namedB p S₀ book tl L with
  | false => rfl
  | true =>
    obtain ⟨o', m', e1, e2, e3, _⟩ := Named.namedB_at hN ht
    obtain rfl : o = o' := Option.some.inj (h1.symm.trans e1)
    obtain rfl : m = m' := Option.some.inj (h2.symm.trans e2)
    exact absurd e3 h3

section
variable {Z : ProofFile.Pub} {G₀ : ProofFile.Ground} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- From the seat and the file's test on the plan. -/
theorem beforeAt_of_sits {l i : ℕ} (hs : SitsAt Z G₀ c l i)
    (hP : (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z)
      c).planOk = true) :
    ∃ b Xl, c.blocksInOrder[14 * l + i + 2]? = some b ∧ G₀.built[l]? = some Xl ∧ ListStays b ∧
      BeforeAt (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z)
        c).roundsDeclaredByBlocks.1 c.blocksInOrder (ProofFile.k8ParW Z G₀ Xl l).toPar (14 * l + i + 2) := by
  obtain ⟨Lk, b, Xl, _, _, hb, e3, _, _, hL, hstep⟩ := hs
  have h0 := before_at_entry (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s)
    (ProofFile.startS Z) c) (seat := atS) hL (14 * l + i + 2) hb hP
  have hpl := (planOk_iff (Cl := Cl) atS (ProofFile.k8ParW Z G₀ Xl l).toPar).1
    (file_facts_likeP (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s)
      (ProofFile.startS Z) c) (seat := atS) hL _ _ (cut_at hb) hP).2.1
  have hbel := fun n hn => named_below_P (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B
    (fun s => s) (ProofFile.startS Z) c) (seat := atS) hL _ _ (cut_at hb) hP n hn
  refine ⟨b, Xl, hb, e3, ?_, h0.1, ⟨hpl.2.2.2.1, hpl.2.2.2.2.1, hpl.1⟩,
    fun n hn => ⟨h0.2.1 n hn, hbel n hn⟩, h0.2.2,
    fun S₀ book tl L hN => ⟨fun t ht => ?_, fun rad a => ?_⟩⟩
  · intro ft st st' k rs cols hy
    obtain ⟨r, _, _, ⟨tl, ht, hc, _, _, _, _, _, _, _, e⟩, _, _⟩ := (hstep ft st st' k rs cols).1 hy
    refine ⟨tl, { tl with cfF := r.drawn.trits.toArray
                          cfFirst := firstColumns (ProofFile.k8ParW Z G₀ Xl l).toPar },
      ht, hc, ?_, hc, rfl, fun tl0 => ?_⟩
    · rw [e]
      exact putTl_tl st tl _ ht
    · rw [e]
      exact recOf_put tl0 st tl _ _ ht
  · exact arrays_before_at_entry (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B
      (fun s => s) (ProofFile.startS Z) c) (seat := atS) hL (14 * l + i + 2) hb hP S₀ book tl L hN t ht
  · exact ⟨h0.2.1 _ (Named.named_of_test hN rad a), hbel _ (Named.named_of_test hN rad a)⟩

end

/-- `SitsAt` at every place of the written list. -/
theorem sits_at_places {Z : ProofFile.Pub} {G₀ : ProofFile.Ground} {c : Chain S Cl}
    (hL : ∀ g < 12, SitsAt Z G₀ c (2 * g) 4) (hA : ∀ g < 12, SitsAt Z G₀ c (2 * g + 1) 4)
    (hH : SitsAt Z G₀ c 24 5) : ∀ x ∈ places, SitsAt Z G₀ c x.1 x.2 := by
  intro x hx
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
  have hl' : l < 25 := List.mem_range.1 hl
  by_cases h24 : l = 24
  · subst h24
    exact hH
  · simp only [h24, if_false]
    by_cases he : l % 2 = 0
    · have := hL (l / 2) (by omega)
      rwa [show 2 * (l / 2) = l by omega] at this
    · have := hA (l / 2) (by omega)
      rwa [show 2 * (l / 2) + 1 = l by omega] at this

/-- **THE ROW: what the drawn matrix multiplies is sent before the matrix is drawn, at the seat**:
(A) (A') (B) (B') (E) closed in scope; (C) (D) under `Named.namedB`. -/
theorem k08_before_at_seat {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (hP : F.planOk = true) :
    ∃ (X : Verify.Public) (Z : ProofFile.Pub) (G₀ : ProofFile.Ground) (c : Chain S Cl) (A : ProofFile.SharedSeat)
        (B : ProofFile.SecondSeat),
      ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z ∧ publicOf P.pol P.KL (some lay) = .ok X ∧
      ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀ ∧ G₀.W = X ∧
      F = ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧
      ∀ x ∈ places, ∃ b Xl, c.blocksInOrder[14 * x.1 + x.2 + 2]? = some b ∧ G₀.built[x.1]? = some Xl ∧
        ListStays b ∧
        BeforeAt F.roundsDeclaredByBlocks.1 c.blocksInOrder (ProofFile.k8ParW Z G₀ Xl x.1).toPar (14 * x.1 + x.2 + 2) := by
  obtain ⟨X, Z, G₀, c, A, B, h1, h2, h3, h4, rfl, hL, hA, hH⟩ := k08_sits hS hR hF
  exact ⟨X, Z, G₀, c, A, B, h1, h2, h3, h4, rfl,
    fun x hx => beforeAt_of_sits (sits_at_places hL hA hH x hx) hP⟩

end P1K8S

#print axioms P1K8S.beforeAt_false_of_late
#print axioms P1K8S.namedB_false_of_unnamed
#print axioms P1K8S.beforeAt_of_sits
#print axioms P1K8S.sits_at_places
#print axioms P1K8S.k08_before_at_seat
