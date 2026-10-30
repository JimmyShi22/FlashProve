-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/OrderAtSeat.lean: THE SMALLNESS TEST: AT THE SEAT, WHEREVER THE
FOLD OVER THE PROOF FILE'S FIRST CHAIN REACHES THE BLOCK OF THE DRAW, THE GUARD OF ORDER HOLDS OF
THE RECORD THERE; AND SO, UNDER FOUR INVARIANTS OF THAT RECORD AND TWO FACTS ON THE PLAN, EVERY
ARRAY THAT THE MATRIX MULTIPLIES WAS SENT BEFORE THE MATRIX IS DRAWN. A JOINING.

P1K8R/BeforeAtSeat.lean leaves its clauses (C) and (D) under the test `Named.namedB` at the record
in front of the draw. Here that test is brought down, AT THE RECORD THAT THE FOLD CARRIES THERE:
  `quiet_orders`, `reads_orders`: the quiet step that the lot of K1 joins behind the sending of the
    reads (Johnson/IMR/K1Seat.lean: `k1Quiet`, `k1Reads`: `ProofFile.k1Pure`'s joining to the letter),
    whichever of the three texts it is, or the refuser: wherever its decision goes on,
    `Named.ordered` is yes behind it (Johnson/Desc/First/K8/LawOrdered.lean).
  `alone_retype_under`, `seated_reads_orders`: so at the block AS IT IS SEATED (`LaidAlone` of the
    lot's block carried over): along `Block.Under`.
  `ReadsAt Z G₀ c l i`: the entry in front of the draw's, number 14 l + i + 1 of the flat list, is
    such a block. `readsAt_open`: at all 25 places, from an opening's letters in scope
    (`k1_later`, Johnson/IMR/K1Seat.lean).
  `ordered_in_front`: **wherever the fold over the entries in front of the draw's goes on, `ordered`
    is yes at the record that it hands on.**
  `BookOk p s`: what is left, of that record and the plan: `Book.BookFits`, `BookHas`, `SentHere`,
    `earlyB`, and that the place names the trees of the link's two sendings
    (Johnson/Desc/First/K8/LawBookNames.lean).
  `bookOk_of_lists`: IT FOLLOWS, where the guard of order holds, from the book's two invariants,
    `Named.LinkLists` at the open link (the forms in which the laws on the link's opening and its
    two sendings end) and the two facts on the plan: the test `earlyB` is then no premise.
  `k08_arrays_at_seat`: **THE ROW's CLAUSE (C) AT THE RUN'S OWN RECORD**: in scope, from the value
    of `onlineDescription`, where the description's test on the plan says yes: at every place of the written
    list, for every run of the fold that reaches the block of the draw with a record s with `BookOk
    p s`: `Named.namedAt p s` = yes, a link is open in s with a record tl, and every array of
    `Named.arrays tl` lies, now, in a message that the statement and the book of s have, in a tree
    that is sent strictly in front of the round of the draw.
Limits, said first. THAT `onlineDescription` RETURNS IN SCOPE, AND `F.planOk = true`, ARE PREMISES. `BookOk`
IS A PREMISE ON THE RUN'S RECORD: NO LAW PAYS IT YET: its first two clauses are invariants that
a walk in other files carries; the third is owed by the link's two sendings; the fourth is a test on
public values; the last two are the plan's arithmetic. The fold is `foldBlocks` over the chain's
flat list, from any record s0: that a run of the description is such a fold is not said here.
Nothing on soundness.

-/
import Johnson.P1K8R.BeforeAtSeat
import Johnson.IMR.K1Seat
import Johnson.Desc.First.K8.LawOrdered

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1K8S

open Inst.Model
open OnBytes OnBytes.Model
open OnBytes.Model.Verify (publicOf)
open OnBytes.Model.Stages (LinkH)
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName OpenedColumn sendRound foldBlocks
  foldLays under_of_decide)
open VerifiableInference.Desc.First (S ModelPart kindsBeforeBatching)
open VerifiableInference.Desc.First.K8
open ProofFile (Cl)

local notation "rIn" => VerifiableInference.Desc.roundsIn

theorem of_ite_none {α : Type} {c : Prop} [Decidable c] {x : Option α} {q : α}
    (h : (if c then x else none) = some q) : x = some q := by
  split at h
  · exact h
  · exact nomatch h

/-- The quiet step behind the reads, whichever text it is: behind its yes the guard of order
holds. -/
theorem quiet_orders (G : ProofFile.Ground) (l : ℕ) (X : LinkH) :
    (IM.k1Quiet G l X).Lays Named.ordered (fun _ => some true) := by
  unfold IM.k1Quiet
  dsimp only
  generalize (if X.kind == 0 || X.kind == 1 then 4 else 5 : ℕ) = piece
  cases hq : ProofFile.readsQuietAt G l X piece with
  | none =>
    intro s rs gs s' h
    simp [ProofFile.orLoud, ProofFile.refuser, VerifiableInference.Desc.roundlessBlock] at h
  | some q =>
    show q.Lays _ _
    unfold ProofFile.readsQuietAt at hq
    split at hq
    · exact Named.attO_orders _ _ _ q (of_ite_none hq)
    · exact Named.blockAt_orders _ _ _ _ _ _ q (of_ite_none hq)

/-- The reads' place's block of the lot. -/
theorem reads_orders (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : ℕ) (X : LinkH) (pr : ℕ)
    (reads : Option (List ℕ)) :
    (IM.k1Reads Z G l X pr reads).Lays Named.ordered (fun _ => some true) :=
  Named.lays_behind (quiet_orders G l X) _ _

/-- A lot's block carried over and seated alone: the seated block is under the lot's. -/
theorem alone_retype_under {same : S → S → Bool} {b : Block S Cl} {x : Block S Unit}
    {name : String} {a : Place} (h : IM.LaidAlone same b x.retype name a) : b.Under x :=
  (IM.alone_underR h).2.trans (under_of_decide rfl)

theorem seated_reads_orders {Z : ProofFile.Pub} {G : ProofFile.Ground} {l pr : ℕ} {X : LinkH}
    {reads : Option (List ℕ)} {b : Block S Cl} {name : String} {a : Place}
    (h : IM.LaidAlone ProofFile.sameReply b (IM.k1Reads Z G l X pr reads).retype name a) :
    b.Lays Named.ordered (fun _ => some true) :=
  lays_of_under (alone_retype_under h) (reads_orders Z G l X pr reads)

/-- The entry in front of the draw's lays `ordered`. -/
def ReadsAt (c : Chain S Cl) (l i : ℕ) : Prop :=
  ∃ b : Block S Cl, c.blocksInOrder[14 * l + i + 1]? = some b ∧ b.Lays Named.ordered (fun _ => some true)

/-- **Wherever the fold over the entries in front of the draw's goes on, the guard of order holds at
the record that it hands on.** -/
theorem ordered_in_front {c : Chain S Cl} {l i : ℕ} (h : ReadsAt c l i) (ft : ℕ) (s0 : S)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (out : S × List Fmt.RoundView × List OpenedColumn)
    (H : foldBlocks ft (c.blocksInOrder.take (14 * l + i + 2)) s0 rs cols = .ok out) :
    Named.ordered out.1 = some true := by
  obtain ⟨b, hb, hl⟩ := h
  have e : c.blocksInOrder.take (14 * l + i + 2) = c.blocksInOrder.take (14 * l + i + 1) ++ b :: [] := by
    rw [show 14 * l + i + 2 = (14 * l + i + 1) + 1 from rfl, List.take_add_one, hb]
    rfl
  rw [e] at H
  exact foldLays S Cl _ Named.ordered _ ft _ b [] s0 rs cols out hl (fun _ h => nomatch h) H

/-- What is left, of the record in front of the draw and of the plan. -/
def BookOk (p : Par) (s : S) : Prop :=
  ∃ a b a' b' : ℕ, VerifiableInference.Desc.Book.BookFits s.book ∧ Named.BookHas s ∧
    (∀ L, s.link? = some L → Named.SentHere a b a' b' s.book L) ∧
    (∀ tl L, s.tl? = some tl → s.link? = some L → Named.earlyB tl L = true) ∧
    (∀ j, a ≤ j → j < b → j ∈ p.matsIn ++ p.readsIn) ∧
    ∀ j, a' ≤ j → j < b' → j ∈ p.matsIn ++ p.readsIn

/-- **`BookOk` from the forms in which the sending blocks' laws end** (`Named.LinkLists`,
Johnson/Desc/First/K8/LawOrdered.lean), where the guard of order holds. -/
theorem bookOk_of_lists {p : Par} {s : S} {a b a' b' : ℕ} (hO : Named.ordered s = some true)
    (h1 : VerifiableInference.Desc.Book.BookFits s.book) (h2 : Named.BookHas s)
    (hL : ∀ L, s.link? = some L → Named.LinkLists a b a' b' s.book L)
    (hM : ∀ j, a ≤ j → j < b → j ∈ p.matsIn ++ p.readsIn)
    (hR : ∀ j, a' ≤ j → j < b' → j ∈ p.matsIn ++ p.readsIn) : BookOk p s := by
  obtain ⟨tl, L, ht, hl, ho⟩ := Named.ordered_spec hO
  refine ⟨a, b, a', b', h1, h2, fun L' e => ?_, fun tl' L' e1 e2 => ?_, hM, hR⟩
  · obtain ⟨own0, ids, e0, x0, x1, x3⟩ := (hL L' e).own
    exact Named.sentHere_of_lists own0 ids e0 (hL L' e).kept x0 x1 x3
  · obtain rfl : tl = tl' := Option.some.inj (ht.symm.trans e1)
    obtain rfl : L = L' := Option.some.inj (hl.symm.trans e2)
    exact Named.earlyB_of_order ho (hL L hl).link (hL L hl).moments

section
variable {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- One place, from `k1_later`. -/
theorem readsAt_of_later (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl24 : l ≤ 24)
    (sub : ModelPart) (hl : (ProofFile.subsOf Z)[l]? = some sub) (i : ℕ)
    (hk : (kindsBeforeBatching sub (l == 0))[i]? = some KindName.K1) (hi : i = 3 ∨ i = 4) :
    ReadsAt c l (i + 1) := by
  obtain ⟨Lk, b, Xl, pr, pd, reads, digits, e1, e2, _, hn, harm⟩ :=
    IM.k1_later O l sub hl i hk (by omega)
  have hf : c.blocksInOrder[14 * l + (i + 1) + 1]? = some b := by
    have := IM.hear_at_flat e1 e2
    rw [IM.flatIx_scope hS hR O hl24 i] at this
    rw [show 14 * l + (i + 1) + 1 = 14 * l + i + 2 by omega]
    exact this
  rcases harm with ⟨_, h⟩ | ⟨e, _⟩
  · exact ⟨b, hf, seated_reads_orders h⟩
  · exfalso
    rcases IM.numbers_pieces hn with ⟨-, h'⟩ | ⟨-, h'⟩ <;> omega

/-- **At all 25 places.** -/
theorem readsAt_open (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∀ x ∈ places, ReadsAt c x.1 x.2 := by
  intro x hx
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
  have hl' : l < 25 := List.mem_range.1 hl
  by_cases h24 : l = 24
  · subst h24
    exact readsAt_of_later hS hR O (by omega) .head (IM.subs_head hS hR O.pub O.blank) 4
      (by unfold kindsBeforeBatching; rfl) (Or.inr rfl)
  · simp only [h24, if_false]
    by_cases he : l % 2 = 0
    · have h := IM.subs_at hS hR O.pub O.blank (g := l / 2) (by omega)
      rw [show 2 * (l / 2) = l by omega] at h
      exact readsAt_of_later hS hR O (by omega) .layers h 3
        (by unfold kindsBeforeBatching; cases (l == 0) <;> rfl) (Or.inl rfl)
    · have h := IM.subs_att hS hR O.pub O.blank (g := l / 2) (by omega)
      rw [show 2 * (l / 2) + 1 = l by omega] at h
      exact readsAt_of_later hS hR O (by omega) .attention h 3
        (by unfold kindsBeforeBatching; cases (l == 0) <;> rfl) (Or.inl rfl)

/-- `SitsAt` at all 25 places, from the same letters. -/
theorem sitsAt_open (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∀ x ∈ places, SitsAt Z Bs.G₀ c x.1 x.2 :=
  sits_at_places
    (fun g hg => by
      obtain ⟨Lk, b, Xl, _, e1, e2, e3, h, _⟩ := IM.k8_of_layers hS hR O g hg
      exact sitsAt_of_alone e1 e2 (IM.flatIx_scope hS hR O (by omega) 4) e3 h)
    (fun g hg => by
      obtain ⟨Lk, b, Xl, _, e1, e2, e3, h, _⟩ := IM.k8_of_attention hS hR O g hg
      exact sitsAt_of_alone e1 e2 (IM.flatIx_scope hS hR O (by omega) 4) e3 h)
    (by
      obtain ⟨Lk, b, Xl, e1, e2, e3, h, _⟩ := IM.k8_of_head hS hR O
      exact sitsAt_of_alone e1 e2 (IM.flatIx_scope hS hR O (by omega) 5) e3 h)

end

/-- **THE ROW's CLAUSE (C) AT THE RUN'S OWN RECORD**, under `BookOk`. -/
theorem k08_arrays_at_seat {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (hP : F.planOk = true) :
    ∃ (Z : ProofFile.Pub) (G₀ : ProofFile.Ground) (c : Chain S Cl) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat),
      ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z ∧
      ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀ ∧
      F = ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧
      ∀ x ∈ places, ∃ Xl, G₀.built[x.1]? = some Xl ∧
        ∀ (ft : ℕ) (s0 : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
          (out : S × List Fmt.RoundView × List OpenedColumn),
          foldBlocks ft (c.blocksInOrder.take (14 * x.1 + x.2 + 2)) s0 rs cols = .ok out →
          Named.ordered out.1 = some true ∧
          (BookOk (ProofFile.k8ParW Z G₀ Xl x.1).toPar out.1 →
            Named.namedAt (ProofFile.k8ParW Z G₀ Xl x.1).toPar out.1 = true ∧
            ∃ tl L, out.1.tl? = some tl ∧ out.1.link? = some L ∧
              ∀ t ∈ Named.arrays tl, ∃ o m j, Named.msgNow L t = some o ∧
                Named.memberAt out.1.st out.1.book o = some m ∧
                sendRound F.roundsDeclaredByBlocks.1 m.2.1 = some j ∧
                j < rIn (c.blocksInOrder.take (14 * x.1 + x.2 + 2))) := by
  obtain ⟨Z, Bs, base, c, A, B, O⟩ := IM.seat_open hF
  have hd := O.desc
  subst hd
  refine ⟨Z, Bs.G₀, c, A, B, O.pub, O.blank, rfl, fun x hx => ?_⟩
  obtain ⟨b, Xl, _, e3, _, hB⟩ := beforeAt_of_sits (sitsAt_open hS hR O x hx) hP
  refine ⟨Xl, e3, fun ft s0 rs cols out H => ?_⟩
  have ho := ordered_in_front (readsAt_open hS hR O x hx) ft s0 rs cols out H
  refine ⟨ho, fun hk => ?_⟩
  obtain ⟨a, b', a', b'', k1, k2, k3, k4, k5, k6⟩ := hk
  have hN := Named.namedAt_of_ordered ho k1 k2 k3 k4 k5 k6
  obtain ⟨tl, L, ht, hl, _⟩ := Named.ordered_spec ho
  refine ⟨hN, tl, L, ht, hl, ?_⟩
  have hNB : Named.namedB (ProofFile.k8ParW Z Bs.G₀ Xl x.1).toPar out.1.st out.1.book tl L = true := by
    unfold Named.namedAt at hN
    rw [ht, hl] at hN
    exact hN
  exact (hB.2.2.2.2 out.1.st out.1.book tl L hNB).1

end P1K8S

#print axioms P1K8S.quiet_orders
#print axioms P1K8S.seated_reads_orders
#print axioms P1K8S.ordered_in_front
#print axioms P1K8S.bookOk_of_lists
#print axioms P1K8S.readsAt_open
#print axioms P1K8S.k08_arrays_at_seat
