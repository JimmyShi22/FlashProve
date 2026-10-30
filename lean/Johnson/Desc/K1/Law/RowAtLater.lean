-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/RowAtLater.lean: THE ARM aRow OF
hgo_of_arms (Johnson/Desc/K1/Law/GoAtLater.lean), AS A CALL:
the table of joints' item "row m c" goes BACK over the own yes of a later
moment's sending of kind K1, from inside the promise in front. Definitions, and statements with
their proofs. THE LAW IS row_holds_back_of_step (Johnson/Desc/K1/Law/RowAtStep.lean);
here its seven premises are paid or brought down.
OBJECT. The blocks B with LaterRows P B. Two members are shown: laterAt
(Johnson/Desc/K1/Places.lean: a link's digits) and the reads' place's joined block k1Reads
(Johnson/IMR/K1Seat.lean).
USER. aRow_at (Johnson/Desc/K1/Law/CallsG.lean) calls aRow_of, and the proof of k01_fifty
(Johnson/Desc/K1/Law/K01Law.lean) calls aRow_at.
  LaterRows P B     what a yes of B on two rounds does to what the item reads: the older messages
                    stay (OldMsgs); every group stays with its open rows; the book grows at its end
                    (Booked); every older tree stays (TreesOlder).
  laterRows_commitAtS, laterRows_laterAt, laterRows_joined, laterRows_k1Reads.
  row_back_later    the item over a yes of B, the three facts on the state in front as premises.
  aRow_of           **THE ARM, in the top's own form** (YesOf, InAt: KeepAtLater.lean).
WHAT PAYS WHAT in aRow_of. The four relations: LaterRows. "The statement is in order": the promise's
clause inOrder, by FillsK1.inOrder and inOrder_of_k13. "The book has a place for every message and
no more": the promise's clause bookAt.
PREMISES THAT STAY. hrow: the meaning's letter row is the ruled sentence (at the composed meaning:
mgAll_row; FillsK1 has no such field yet). hholds: "every place of the book names a tree that the
book holds", of the state in front: NO CLAUSE OF THE PROMISE SAYS IT BY ITSELF: its meant payer
is holds_of_item | hholds_of (Johnson/Desc/K1/Law/BookHoldsAt.lean: off a
public item that says Book.BookFits); another road to it:
Johnson/Desc/K1/Law/BookFacts.lean [not in this library].
What is not claimed. These two. AT ONE WITNESS. Nothing on soundness, on an honest prover or on
hiding.

-/
import Johnson.Desc.K1.Law.KeepAtLater
import Johnson.Desc.K1.Law.FillsK1
import Johnson.Desc.K1.Law.PubAtLaterIndex
import Johnson.Desc.K1.Law.RowAtStep
import Johnson.Desc.K1.Law.JoinsRows
import Johnson.Desc.K1.Law.InOrderOfK13

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model _root_.Desc.Plain
open OnBytes.Means (InOrder)
open OnBytes.Maker Fo.Peel Cb Johnson.Pack
open VerifiableInference.Desc.Sound (MsgT Mem Sending)
open VerifiableInference.Desc.First (S ModelPart Pub Numbers RowClass Item Meaning PubData rowSays
  wordsAtFirst)
open VerifiableInference.Desc.K13.Law (openAt)
open OnBytes.Model.Stages (LinkH)

variable {Cl : Type}

/-! ## The blocks -/

/-- **A block of a later moment's sending of the place P**: what a yes of it on two rounds does to
what the item "row" reads. -/
def LaterRows (P : Par) (B : Block S Cl) : Prop :=
  ∀ s s' rs gs, rs.length = 2 → B.decide s rs gs = .ok s' →
    OldMsgs s.st s'.st ∧
      (∀ (j : Nat) (G : OnBytes.Group), s.st.groups[j]? = some G →
        ∃ G' : OnBytes.Group, s'.st.groups[j]? = some G' ∧ G'.rows = G.rows) ∧
      Booked P s.book s.st.oracles.size s'.book s'.st.oracles.size ∧ TreesOlder s.book s'.book

/-- The sending alone. -/
theorem laterRows_commitAtS (P : Par) (link moment : Nat) (arrays : Option (List Nat)) :
    LaterRows P (commitAtS P link moment arrays : Block S Cl) := by
  intro s s' rs gs h2 h
  obtain ⟨r₁, r₂, rfl⟩ := List.length_eq_two.1 h2
  obtain ⟨L, _, hJ⟩ := commitAtS_group P link moment arrays s s' r₁ r₂ gs h
  exact ⟨keepsOld_commitAtS P link moment arrays s s' _ gs h, hJ.rowsKept,
    commitAtS_booked P link moment arrays s s' r₁ r₂ gs h,
    commitAtS_treesOlder P link moment arrays s s' r₁ r₂ gs h⟩

/-- **The first member**: a segment's later moment at the plan's numbers (a link's digits). -/
theorem laterRows_laterAt (q : Params.First) (gp : GPar) (link piece moment : Nat)
    (arrays : Option (List Nat)) :
    LaterRows (parLater q gp link piece moment)
      (laterAt q gp link piece moment arrays : Block S Cl) :=
  laterRows_commitAtS _ _ _ _

/-- The sending with a quiet block joined behind it. -/
theorem laterRows_joined (P : Par) (link moment : Nat) (arrays : Option (List Nat)) (nm : String)
    (q : Block S Cl) (hq : QuietP q) :
    LaterRows P (Block.andThen nm (commitAtS P link moment arrays) q) := by
  intro s s' rs gs h2 h
  obtain ⟨r₁, r₂, rfl⟩ := List.length_eq_two.1 h2
  obtain ⟨s₁, gs₁, rs₂, gs₂, h1, h3⟩ := joined_yes P link moment arrays nm q s s' r₁ r₂ gs h
  obtain ⟨e1, e2, _⟩ := hq _ _ _ _ h3
  rw [e1, e2]
  exact laterRows_commitAtS P link moment arrays s s₁ _ gs₁ rfl h1

/-- **The second member**: the reads' place's joined block. -/
theorem laterRows_k1Reads (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : Nat) (X : LinkH) (pr : Nat)
    (reads : Option (List Nat)) :
    LaterRows (parLater G.first (gpOf Z) l pr 1) (IM.k1Reads Z G l X pr reads) :=
  laterRows_joined _ _ _ _ _ _ (quietP_orLoud _ _ _ G l X _)

/-! ## The item over a block's own yes -/

section
variable {Pp Cells Tok : Type}

/-- The item over a yes of B on two rounds. -/
theorem row_back_later {P : Par} {B : Block S Cl} (hB : LaterRows P B) (arr : ℕ → ℕ → ℕ)
    (N : Numbers) (Mg : Meaning Pp (Wit Cells Tok MsgT))
    (hrow : Mg.row = rowSays N (wordsAtFirst arr)) (x x' : Pp × S) (y y' : Strs)
    (w : Wit Cells Tok MsgT) (m : Nat) (c : RowClass) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h2 : rs.length = 2)
    (h : B.decide x.2 rs gs = .ok x'.2) (hI : InOrder x.2.st)
    (hn : x.2.book.place.size = x.2.st.oracles.size)
    (hold : ∀ (o : Nat) (q : Nat × Nat), x.2.book.place[o]? = some q →
      q.1 < x.2.book.trees.size)
    (h0 : Mg.row m c x' y' w) : Mg.row m c x y w := by
  obtain ⟨hO, hR, hBk, hT⟩ := hB _ _ _ _ h2 h
  exact row_holds_back_of_step arr N Mg hrow P x x' y y' w m c hO hR hBk hT hI hn hold h0

variable {Xi : Type} {D : PubData} {G : FileDescription Xi} {arr : ℕ → ℕ → ℕ}
  {smp : Pp × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf D.cs s.l).om i).Smp}
  {ms : List Mem} {decT : (ℕ → Option (ℕ × List UInt64)) → Pp × S → Option Cells}
  {shape : Params.ReqShape} {layout : Params.ReqLayout} {io0 : Pp × S → Bool}
  {base : Pub → Pp × S → Bool} {X3 : OnBytes.Model.Verify.Public} {D3 : First.Look.Sent}
  {MgP Mg : Meaning Pp (Wit Cells Tok MsgT)}

/-- **THE ARM aRow**, at any block of the sort, at any border k. -/
theorem aRow_of (hF : FillsK1 D G arr smp ms decT shape layout io0 base X3 D3 MgP Mg) (N : Numbers)
    (hrow : Mg.row = rowSays N (wordsAtFirst arr)) {P : Par} {B : Block S Unit}
    (hB : LaterRows P B) (hl : B.rounds.length = 2) (links : List ModelPart) (ps : List Place) (k : ℕ)
    (x x' : Pp × S) (y y' : Strs) (w : Wit Cells Tok MsgT) (m : Nat) (c : RowClass)
    (hy : YesOf B x x') (hIn : InAt N Mg links ps k x y)
    (hholds : ∀ (o : ℕ) (u : ℕ × ℕ), x.2.book.place[o]? = some u → u.1 < x.2.book.trees.size)
    (h0 : Mg.row m c x' y' w) :
    Mg.row m c x y w := by
  obtain ⟨_, rs, gs, hf, hd⟩ := hy
  have h2 : (rs.map noDigest).length = 2 := by
    rw [List.length_map, K13.Law.roundsFit_length _ _ hf, hl]
  obtain ⟨⟨_, hr⟩, hm⟩ := hIn
  rcases hr with hx | ⟨hb, _, _, _⟩
  · exact absurd hm hx
  simp only [Bool.and_eq_true] at hb
  obtain ⟨⟨⟨_, hord⟩, _⟩, hbk⟩ := hb
  have hI : InOrder x.2.st := by
    rw [hF.inOrder] at hord
    simp only [Bool.and_eq_true] at hord
    exact inOrder_of_k13 _ _ _ _ hord.2
  unfold First.bookAt at hbk
  simp only [Bool.and_eq_true, beq_iff_eq] at hbk
  exact row_back_later hB arr N Mg hrow x x' y y' w m c _ gs h2 hd hI hbk.1.2 hholds h0

end

end VerifiableInference.Desc.K1
