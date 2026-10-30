-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/FormSendGave.lean: THE FORM's HALF AT THE LINK's FRONT: THE SENDING's BLOCK
(sendK1, Johnson/Desc/Link/LinkDesc.lean) SAYS ok AS A STEP, TAKES NO COLUMN, AND LEAVES SendGave
(Johnson/Prover/Link/FormGave.lean); so front6_yes (FormFront6.lean) stands with the sending paid.

Main names.
  sent_size, shape0, shape1   the link's one message: how many oracle messages; the first two's
  shapes.
  numbers_at      the new messages' numbers.
  foldMsg_behind  a fold's message behind the sending.
  behind_some     what K15 notes behind the sending, at the new messages' numbers.
  sentIn, sentB, sentMid   the records inside the sending's block, written out.
  sendK1_gave     THE SENDING's BLOCK.
  front6_whole    front6_yes with the sending paid.

How. By the shared sending's laws (Johnson/Prover/Send/Form.lean): sendOwn_yes, behind_at,
wr_sampled, behind_rest, SendFront.of_lengths.

Limits. roundsFit at five rounds and "the columns" at "LINK" are premises: Block.step's own two
tests. The keys' sizes and "no seed's factor is 0" are premises. It ends in front of the proximity
test.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.FormFront6
import Johnson.Prover.Send.Form
import Johnson.Desc.K12.Law.TrOnto
import Johnson.Desc.Own.SendAgree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc
open _root_.Desc.Plain (DState)
open Desc.K15 (St Par15 P15)
open Johnson.Prover.Send

theorem sent_size (P : P15) : 2 ≤ (Desc.K15.parK1 P).sent.size ∧
    (P.S.masksAhead = true → 3 ≤ (Desc.K15.parK1 P).sent.size) := by
  rw [Desc.K15.parK1_sent]
  unfold linkMessage
  by_cases h : P.S.masksAhead = true <;> simp [h]

theorem shape0 (P : P15) :
    shapeAt (Desc.K15.parK1 P) 0 = (P.S.side false P.set.samples).u := by
  unfold shapeAt
  rw [Desc.K15.parK1_sent]
  unfold linkMessage
  by_cases h : P.S.masksAhead = true <;> simp [h]

theorem shape1 (P : P15) :
    shapeAt (Desc.K15.parK1 P) 1 = (P.S.side true P.set.samples).u := by
  unfold shapeAt
  rw [Desc.K15.parK1_sent]
  unfold linkMessage
  by_cases h : P.S.masksAhead = true <;> simp [h]

theorem numbers_at (Q : K1.Par) (first k : Nat) (h : k < Q.sent.size) :
    (Send.numbers Q first)[k]? = some (k + first) := by
  unfold Send.numbers
  simp [h]

/-- **A fold's message behind the sending.** k: its number among the messages sent. -/
theorem foldMsg_behind (P : P15) (d : DState (Array Nat)) (F : SendFront (Desc.K15.parK1 P) d)
    (seeds : List (List E × E)) (ys : List E) (k : Nat) (S : FoldeqShape) (lay : VectorLay)
    (hk : k < (Desc.K15.parK1 P).sent.size) (hs : shapeAt (Desc.K15.parK1 P) k = S.u)
    (ha : S.u.answers ≠ 0) :
    FoldMsg (K1.behind (Desc.K15.parK1 P) d seeds ys).st S ⟨k + d.st.oracles.size, lay⟩ := by
  have hat := behind_at (Desc.K15.parK1 P) d seeds ys k hk
  rw [hs] at hat
  obtain ⟨w1, w2, _, w4, _, _, _⟩ := wr_sampled (Desc.K15.parK1 P).codes seeds
    (d.st.oracles.size + k) S.u (ys.drop (K1.offset (Desc.K15.parK1 P) k)) ha
  have hmem : S.u ∈ (Desc.K15.parK1 P).tuple := by
    unfold K1.Par.tuple
    rw [List.mem_filter]
    refine ⟨List.mem_map.2 ⟨(Desc.K15.parK1 P).sent.getD k default, ?_, hs⟩, by simpa using ha⟩
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk]
    exact Array.mem_toList_iff.2 (Array.getElem_mem hk)
  obtain ⟨places, hp⟩ := Option.isSome_iff_exists.1 (F.pads S.u hmem)
  refine ⟨_, places, by rw [Nat.add_comm]; exact hat, w1, w2, by rw [w4, hp]; rfl, ?_⟩
  rw [(behind_rest (Desc.K15.parK1 P) d seeds ys).1, F.codes]
  exact hp

/-- What K15 notes behind the sending, at the new messages' numbers. -/
theorem behind_some (P : P15) (d : St) (first : Nat) :
    ∃ mask, Desc.K15.behind P.par d (Send.numbers (Desc.K15.parK1 P) first) = some { d with
      loc := { d.loc with
        o0 := ⟨0 + first, vectorLay d.st.codes (P.S.side false P.set.samples).u P.S.rowsHigh⟩
        o1 := ⟨1 + first, vectorLay d.st.codes (P.S.side false P.set.samples).u P.S.rowsHigh⟩
        firstMask := mask } } := by
  obtain ⟨h2, h3⟩ := sent_size P
  have i0 := numbers_at (Desc.K15.parK1 P) first 0 (by omega)
  have i1 := numbers_at (Desc.K15.parK1 P) first 1 (by omega)
  unfold Desc.K15.behind
  by_cases hm : P.S.masksAhead = true
  · have i2 := numbers_at (Desc.K15.parK1 P) first 2 (by have := h3 hm; omega)
    refine ⟨some (2 + first), ?_⟩
    have hm' : P.par.S.masksAhead = true := hm
    simp only [hm', if_true, i0, i1, i2, Option.map_some, Option.bind_eq_bind, Option.bind_some]
    rfl
  · refine ⟨none, ?_⟩
    have hm' : ¬ P.par.S.masksAhead = true := hm
    simp only [hm', if_false, i0, i1, Option.bind_eq_bind, Option.bind_some, Bool.false_eq_true]
    rfl

/-- The record that the sending's block enters with. -/
def sentIn (d1 : St) : DState (Array Nat) :=
  { st := d1.st, book := d1.book, roots := d1.roots, opened := d1.opened, loc := #[] }

/-- What `K1.behind` returns at the link's parameters for the sending (`parK1 P`), off `sentIn d1`,
the seeds of r1 and the answers of r2. -/
def sentB (P : P15) (d1 : St) (r1 r2 : Fmt.RoundView) : DState (Array Nat) :=
  K1.behind (Desc.K15.parK1 P) (sentIn d1) (K1.seedsOf (Desc.K15.parK1 P) (noDigest r1))
    (K1.answersIn (noDigest r2))

/-- d1 with the statement, the book, the roots and the opened columns of `sentB`. -/
def sentMid (P : P15) (d1 : St) (r1 r2 : Fmt.RoundView) : St :=
  { d1 with
    st := (sentB P d1 r1 r2).st, book := (sentB P d1 r1 r2).book
    roots := (sentB P d1 r1 r2).roots, opened := (sentB P d1 r1 r2).opened }

/-- **THE SENDING's BLOCK AT THE LINK, AS A STEP**: it says ok, takes no column, and leaves
SendGave. -/
theorem sendK1_gave (P : P15) (d1 : St) (r1 r2 : Fmt.RoundView) (cols : List OpenedColumn)
    (F : SendFront (Desc.K15.parK1 P)
      ({ st := d1.st, book := d1.book, roots := d1.roots, opened := d1.opened, loc := #[] } :
        DState (Array Nat)))
    (hfit : roundsFit (K1.rounds (Desc.K15.parK1 P)) [r1, r2] = true) (hn : 1 ≤ P.set.samples) :
    ∃ d2, (Desc.K15.sendK1 P).step 0 d1 [r1, r2] cols = .ok (d2, 0) ∧ SendGave P.par d1 d2 := by
  have F' : SendFront (Desc.K15.parK1 P) (sentIn d1) := F
  have hfit' : roundsFit (K1.rounds (Desc.K15.parK1 P)) [noDigest r1, noDigest r2] = true :=
    (H2K.Onto.roundsFit_noDigest _ [r1, r2]).trans hfit
  have hy := sendOwn_yes (Cl := Unit) (Desc.K15.parK1 P) (sentIn d1) (noDigest r1) (noDigest r2) []
    F' hfit'
  obtain ⟨h2, _⟩ := sent_size P
  obtain ⟨b1, b2, _, _, _, _, _, _⟩ := behind_rest (Desc.K15.parK1 P) (sentIn d1)
    (K1.seedsOf (Desc.K15.parK1 P) (noDigest r1)) (K1.answersIn (noDigest r2))
  obtain ⟨mask, hb⟩ := behind_some P (sentMid P d1 r1 r2) d1.st.oracles.size
  have ha : (P.S.side false P.set.samples).u.answers ≠ 0 := by
    show P.set.samples ≠ 0
    omega
  refine ⟨{ sentMid P d1 r1 r2 with
      loc := { d1.loc with
        o0 := ⟨0 + d1.st.oracles.size,
          vectorLay (sentB P d1 r1 r2).st.codes (P.S.side false P.set.samples).u P.S.rowsHigh⟩
        o1 := ⟨1 + d1.st.oracles.size,
          vectorLay (sentB P d1 r1 r2).st.codes (P.S.side false P.set.samples).u P.S.rowsHigh⟩
        firstMask := mask } }, ?_, ?_⟩
  · refine step_no_cols (Desc.K15.sendK1 P) 0 d1 _ [r1, r2] cols (fun r hr => ?_) hfit ?_
    · have hr' : r ∈ K1.rounds (Desc.K15.parK1 P) := hr
      unfold K1.rounds at hr'
      rcases List.mem_cons.1 hr' with rfl | hr'
      · exact ⟨rfl, rfl⟩
      · obtain rfl := List.mem_singleton.1 hr'
        exact ⟨rfl, rfl⟩
    · show ((K1.sendOwn (Desc.K15.parK1 P) : Block _ Unit).decide ⟨none, sentIn d1⟩
        [noDigest r1, noDigest r2] []).bind _ = _
      rw [hy]
      show named _ (Desc.K15.behind P.par (sentMid P d1 r1 r2)
        (Send.numbers (Desc.K15.parK1 P) d1.st.oracles.size)) = _
      rw [hb]
      rfl
  · exact ⟨b1, b2, rfl, rfl, rfl, rfl, by show 0 + _ ≠ 1 + _; omega,
      foldMsg_behind P (sentIn d1) F' _ _ 0 _ _ (by omega) (shape0 P) ha,
      foldMsg_behind P (sentIn d1) F' _ _ 1 _ _ (by omega) (shape1 P) ha, rfl, rfl⟩

/-- **front6_yes WITH THE SENDING PAID.** -/
theorem front6_whole (P : P15) (x : TableKey × TableKey) (r0 r1 r2 r3 r4 : Fmt.RoundView)
    (cols : List OpenedColumn) (he : Desc.K15.entries P = some (Desc.K15.fiveOf P))
    (hl : P.codes.lengthsOk = true) (hok : linkOk P.codes P.S P.set.samples = true)
    (hp : K1.planOkOwn (Desc.K15.parK1 P) = true) (k0 : Own.keyFits x.1 P.S.table = true)
    (k1 : Own.keyFits x.2 P.S.table = true) (z0 : x.1.seeds.all (!isZeroE ·.beta) = true)
    (z1 : x.2.seeds.all (!isZeroE ·.beta) = true)
    (f0 : roundsFit (Desc.K15.bPoint P (Desc.K15.fiveOf P)).rounds [r0] = true)
    (f12 : roundsFit (K1.rounds (Desc.K15.parK1 P)) [r1, r2] = true)
    (f3 : roundsFit (Desc.K15.bLink P (Desc.K15.fiveOf P)).rounds [r3] = true)
    (hc : (cols.take (linkWant P.S r3).length).map (fun c => (c.1, c.2.1, c.2.2.length)) =
      linkWant P.S r3)
    (f4 : roundsFit (Desc.K15.bPhi P (Desc.K15.fiveOf P)).rounds [r4] = true) :
    ∃ d' G', foldBlocks 0 (Desc.K15.frontBlock P :: Desc.K15.blocksOrV P)
        (Desc.K15.first P.codes x) [r0, r1, r2, r3, r4] cols =
        .ok (d', [], cols.drop (linkWant P.S r3).length) ∧ LinkSeats P.par d' G' := by
  have hn : 1 ≤ P.set.samples := by
    have h2 := (linkOk_gives P.codes P.S P.set.samples hok).2.1
    simp only [foldeqOk, FoldeqShape.ok, Bool.and_eq_true, decide_eq_true_eq] at h2
    exact h2.1.1.1.2
  obtain ⟨d2, hs, hg⟩ := sendK1_gave P (pointT P.par (Desc.K15.first P.codes x) (noDigest r0)) r1 r2
    cols (SendFront.of_lengths _ _ rfl hp rfl hl) f12 hn
  exact front6_yes P x r0 r1 r2 r3 r4 cols d2 he hok k0 k1 z0 z1 f0 hs hg f3 hc f4

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.sent_size
#print axioms Johnson.Prover.Link.shape0
#print axioms Johnson.Prover.Link.shape1
#print axioms Johnson.Prover.Link.numbers_at
#print axioms Johnson.Prover.Link.foldMsg_behind
#print axioms Johnson.Prover.Link.behind_some
#print axioms Johnson.Prover.Link.sendK1_gave
#print axioms Johnson.Prover.Link.front6_whole
