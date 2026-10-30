-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/FromThread.lean: kind K13, the members' batching: WHAT THE FIRST
CHAIN's THREAD (Honest/Thread/First.lean: `Letters.thread`) HANDS OVER AT THE BORDER IN FRONT OF THE
KIND's PLACE, AND WHAT THE ITEM THAT THE KIND OWES BEHIND IT ASKS. Statements with their proofs,
general in the thread's parameters. The words thread, border, item, forward row and witness are
explained in the head of Honest/Thread/Thr.lean.
Main names:
  `k13_form_front`: out of the public form: the state bears no mark of failure; the chain is out of
    the finish and not yet at its end; no count of rows waits.
  `k13_owes`: the forward row behind the border owes the items "pileOne", "pinW", "pinI".
  `k13_items_at`: an item that is open at a border holds of the thread's witness, at every
    continuation of the challenges heard.
  `k13_rows_front`: where the parameters' meaning of the item "pile" is "all rows on the table are
    true" at a reader: **all rows of the state's pile are true of what the reader makes of the
    thread's witness.**
  `k13_rows_behind`: **the same sentence at the state that the kind's sub-protocol leaves**, from:
    the row of the claim laid is true; the reader reads the same at the two states.
  `k13_rwBook_behind`: the library's reader through the book of commitment trees does.
  `ReplyIs`, `ReplyIs.kept`: the reply that the verifier's state holds is the one that the instance
    asks about; it goes over a step that leaves the reply.
  `ReplyRides`, `replyRides_of_rides`: at a border the thread gives `ReplyIs`; it does where the
    thread's parameter `rides` says so there.
That the state at a border is reached, in the library's sense, by the sub-protocols in front is the
frame's `thr_reach_of` (Honest/Thread/ReachBack.lean): through it the library's laws on reached
states are called at this border (TakenAtM3.lean of this folder).

ON THE REPLY. The reply is a value that the prover sends, in the clear, at the place of kind K7; the
verifier lays it into its state as heard, and compares it with what is asked in the file's last test
alone. The weights of the pile's last row read it. `ReplyRides` is the sentence that the reply heard
is the one asked, as a premise's form. It follows where it stands among the clauses of the thread's
parameter `rides` (`replyRides_of_rides`): the frame's laying of the thread at the library's
hypothesis has that clause from a border b₀ on (Honest/Thread/FirstHead.lean).

What is not claimed. `ReplyRides` at any thread. That a thread holds at any run. That the
parameters' meaning is as asked: at the library's own meaning it is, by unfolding (`mgAll_pile`,
Johnson/Desc/Sound/MgAll.lean), which this file does not import. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.Thread.First
import Johnson.Desc.K13.Honest.SubProtocols
import Johnson.Desc.K13.Law.ReaderByBook
import Johnson.Desc.K13.Law.Letters
import Johnson.Desc.K13.Law.PinDec

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open OnBytes
open OnBytes.Slice (GE)
open VerifiableInference.Desc (Place Strs)
open VerifiableInference.Desc.First (S Item onAt shapeAt standOf standAt Stand)
open VerifiableInference.Desc.Ground (takeMasksP)
open VerifiableInference.Desc.K13 (St)
open VerifiableInference.Desc.K13.Law (Wit ρg Holds RowsTrue rwBook rwBook_same rowOfClaim_member
  dOf takeMasks_same sampleOf)
open VerifiableInference.Desc.K13.Honest (withClaim)
open ProofFile.Honest.FirstThread (Letters)

variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr X Pp Cells Tok M : Type}
  (L : Letters Bk Cl W₀ Rc Xi Tr X Pp Cells Tok M)

/-- **Out of the public form in front of the kind's place.** hp: the written list of places has the
kind's place at number b. h: the thread's clause on the public form at the border number b. Then the
state bears no mark of failure, the chain is out of the finish and not yet at its end, and no count
of rows waits. -/
theorem k13_form_front {b : Nat} (hp : L.ps[b]? = some ⟨1, none, 3, .K13⟩) {k : Coins Bk} {s : S}
    {m : Mid (Local W₀ Rc Xi Tr) X} (h : L.thread.Form b k s m) :
    s.failed = none ∧ (∃ f, s.here = .fin f) ∧ s.noneWaits = true := by
  obtain ⟨h1, h2⟩ := h
  have hf : s.failed = none := Option.isNone_iff_eq_none.1 h1
  have h2' : onAt L.N L.mgP L.links L.ps[b]?
      (((VerifiableInference.Desc.First.openSets L.links L.ps
        (VerifiableInference.Desc.First.start L.links))[b]?).getD [])
      (((VerifiableInference.Desc.First.pubSets L.mgP.more L.links L.ps)[b]?).getD [])
      (L.pubOf m.st.input.x, s) FirstThread.noStrs := h2
  obtain ⟨-, hor⟩ := h2'
  rcases hor with hbad | ⟨hB, -⟩
  · exact absurd hf hbad
  · rw [hp] at hB
    simp only [Bool.and_eq_true] at hB
    obtain ⟨⟨⟨⟨⟨hsh, -⟩, -⟩, -⟩, -⟩, -⟩ := hB
    have hsh' : (standOf s == Stand.fin && (s.noneWaits || false) &&
        s.link?.all fun Lk => (none : Option Nat) == some Lk.link) = true := hsh
    simp only [Bool.and_eq_true, Bool.or_false] at hsh'
    obtain ⟨⟨hst, hw⟩, -⟩ := hsh'
    refine ⟨hf, ?_, hw⟩
    have e : standOf s = Stand.fin := eq_of_beq hst
    unfold standOf at e
    cases hs : s.here with
    | fin a => exact ⟨a, rfl⟩
    | head a =>
      rw [hs] at e
      simp only at e
      split at e <;> cases e
    | _ =>
      rw [hs] at e
      cases e

/-- Where the written list of places has the kind's place at number b, the forward row behind that
border owes these three items. -/
theorem k13_owes {b : Nat} (hp : L.ps[b]? = some ⟨1, none, 3, .K13⟩) :
    (L.thread.row b).owes = [Item.pileOne, .pinW, .pinI] := by
  show (FirstRows.rows L.links L.ps b).owes = _
  unfold FirstRows.rows
  rw [hp]
  rfl

/-- An item that is open at a border holds of the thread's witness, at every continuation ds of the
challenges heard. -/
theorem k13_items_at {b : Nat} {i : Item} (hi : i ∈ L.thread.opened b) {k : Coins Bk} {s : S}
    {m : Mid (Local W₀ Rc Xi Tr) X} {En : Env}
    (h : L.thread.Items (L.thread.opened b) k s m En) (ds : List Fmt.Drawn) :
    Item.holds L.N (L.mg m.st.input) i (L.pubOf m.st.input.x, s) (L.thread.strs En)
      (L.Q.wit k m.st.input (m.st.heard ++ ds)) :=
  h ds i hi

variable {nR kC : Nat}

/-- **All rows of the state's pile are true of what the reader makes of the thread's witness.** rd:
the reader. hMg: the parameters' meaning of the item "pile". hi: that item is open at the border.
hs: the chain is out of the finish and not yet at its end. -/
theorem k13_rows_front (rd : Pp × S → VerifiableInference.Desc.Wit Cells Tok M → Wit GE nR kC)
    (hMg : ∀ w x y v, (L.Mg w).pile x y v → RowsTrue (rd x) x.2 v) {b : Nat}
    (hi : Item.pile ∈ L.thread.opened b) {k : Coins Bk} {s : S}
    {f : VerifiableInference.Desc.First.FinOwn}
    (hs : s.here = .fin f) {m : Mid (Local W₀ Rc Xi Tr) X} {En : Env}
    (h : L.thread.Items (L.thread.opened b) k s m En) (ds : List Fmt.Drawn) :
    ∀ r ∈ s.out.pending, Holds ρg
      (rd (L.pubOf m.st.input.x, s) (L.Q.wit k m.st.input (m.st.heard ++ ds))) r := by
  have h1 := hMg _ _ _ _ (k13_items_at L hi h ds)
  intro r hr
  refine h1 r ?_
  show r ∈ S.rows s
  unfold S.rows
  rw [hs]
  exact hr

/-- **The sentence behind the kind's sub-protocol**: all rows on the table are true at the state
`withClaim`, from: the reader reads the same at the two states (hrd); the row of the claim is true
(hrow). -/
theorem k13_rows_behind (rd : Pp × S → VerifiableInference.Desc.Wit Cells Tok M → Wit GE nR kC)
    (p : Pp) (s : S) (st : Statement) (msg : Array OracleNotice) (row : TensorRow)
    (v : VerifiableInference.Desc.Wit Cells Tok M)
    (hrd : rd (p, withClaim s st msg row) v = rd (p, s) v) (hrow : Holds ρg (rd (p, s) v) row) :
    RowsTrue (rd (p, withClaim s st msg row)) (withClaim s st msg row) v := by
  intro r hr
  have e : (withClaim s st msg row).rows = [row] := by
    show [VerifiableInference.Desc.First.rowOfClaim (memberClaim row)] = [row]
    rw [rowOfClaim_member]
  rw [e] at hr
  rw [List.mem_singleton.1 hr, hrd]
  exact hrow

/-- **The library's reader through the book of commitment trees reads the same at the two states**:
the taking of mask entries changes ledgers alone. -/
theorem k13_rwBook_behind {Pq Cells' Tok' : Type} (arr : ℕ → ℕ → ℕ)
    (mat : Cells' → Fin nR → (Fin kC → Bool) → GE) (p : Pq) {s : S} {o n : ℕ} {t : List ℕ × St}
    (ht : takeMasksP (dOf s) o n = some t) (msg : Array OracleNotice) (row : TensorRow)
    (v : VerifiableInference.Desc.Wit Cells' Tok' VerifiableInference.Desc.Sound.MsgT) :
    rwBook arr mat (p, withClaim s t.2.st msg row) v = rwBook arr mat (p, s) v :=
  rwBook_same arr mat (p, s) (p, withClaim s t.2.st msg row) rfl (takeMasks_same ht).1
    (fun j => by
      have e := congrArg (Option.map fun q => q.1) ((takeMasks_same ht).2 j)
      simpa only [sampleOf, Option.map_map, Function.comp_def] using e) v

/-! ## The reply -/

/-- The reply that the verifier's state holds is the one that the instance asks about. asked: what
an instance asks about, as a field element. -/
def ReplyIs {Xi' : Type} (asked : Xi' → E) (x : Xi') (s : S) : Prop := s.out.reply = some (asked x)

/-- It goes over a step that leaves the reply. -/
theorem ReplyIs.kept {Xi' : Type} {asked : Xi' → E} {x : Xi'} {s s' : S}
    (e : s'.out.reply = s.out.reply) (h : ReplyIs asked x s) : ReplyIs asked x s' := e.trans h

/-- **At the border number b the thread gives `ReplyIs`**, at the input's instance. A premise's
form. -/
def ReplyRides (b : Nat) (asked : Xi → E) : Prop :=
  ∀ k s m En, Thr L.thread b k s m En → ReplyIs asked m.st.input.x s

/-- It does where the thread's parameter `rides` says so at that border. -/
theorem replyRides_of_rides {b : Nat} {asked : Xi → E}
    (h : ∀ w s, L.rides b w s → ReplyIs asked w.x s) : ReplyRides L b asked :=
  fun _ _ _ _ hT => h _ _ hT.2.2.2.2.2.1

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.ReplyIs.kept
#print axioms ProofFile.Honest.K13.replyRides_of_rides
#print axioms ProofFile.Honest.K13.k13_form_front
#print axioms ProofFile.Honest.K13.k13_owes
#print axioms ProofFile.Honest.K13.k13_items_at
#print axioms ProofFile.Honest.K13.k13_rows_front
#print axioms ProofFile.Honest.K13.k13_rows_behind
#print axioms ProofFile.Honest.K13.k13_rwBook_behind
