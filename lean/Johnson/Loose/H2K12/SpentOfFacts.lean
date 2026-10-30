-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Loose/H2K12/SpentOfFacts.lean:
THE LAW OF THE PROXIMITY TEST (the kind K12) ON THE PROOF FILE's
FIRST CHAIN: what the second half of the fourth tie spends of the verifier's state (Spent,
H2K12/Witness354.lean) FOLLOWS FROM what the first half spends (FactsK12,
H2K12/Promise354.lean), the table's promise and one more fact along "reached".
Statements and proofs.
Main names:
  enter_g         the group that the door enterFinish returns is the finish's own frame's.
  spent_of_facts  Spent, field by field: the group's number: from the door and FactsK12's
                  groupAtFinish · the codes · "in order": from the test tidy4B · "no two messages at
                  one place": from "the book fits" (BookFits, Johnson/Desc/Book/BookFits.lean)
                  alone: the tree's part at that place names the message · the trees' numbers: from
                  "the book is in order" where the chain's first tree has the number 0 · of each
                  member of the group under test: its tree is there ("the book fits"); a member of
                  the list sits at its place (the promise's "shown": member_listed,
                  H2K12/Promise354.lean); the message and its shape
                  (FactsK12's seedIs).
  witness_of_facts   THE FOURTH TIE's SECOND HALF (T4bAt, H2K12/Frame354.lean)
                  with FactsK12 and "the book fits" at every reached, unmarked state inside the
                  promise in the place of Spent.
  witness_memOf   the same at mem := memOf ms d.L.places (H2K12/Promise354.lean):
                  a term of the list of members and the list of places: the premise on
                  mem falls, by memOf_listed.
Limits. (1) A JOINING OVER LETTERS. FactsK12 is a premise; by its own file's head two of its fields
have no proof (groupAtFinish, seedIs): so this file pays nothing. (2) hft asks that
the first tree of the chain has the number 0: so it is meant at the first chain alone; elsewhere the
statements are idle. (3) WHETHER ALL PREMISES CAN BE MET TOGETHER AT ONE STATE IS SHOWN NOWHERE
HERE. No soundness statement. Nothing on hiding.

-/
import Johnson.Desc.Sound.BookTestsLaw
import Johnson.Desc.Means.TestsBack
import Johnson.Loose.H2K12.Promise354
import Johnson.Loose.H2K12.Witness354

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K12

open VerifiableInference.Desc (FileDescription Wit Place)
open VerifiableInference.Desc.Sound (Mem Sending MsgT seatOf strsOf)
open Johnson.Pack (sigOf)
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers)

/-- The group that the door returns is the finish's own frame's. -/
theorem enter_g (s : VerifiableInference.Desc.First.S) (t : VerifiableInference.Desc.K12.T12)
    (h : VerifiableInference.Desc.K12.enterFinish s = .ok t) :
    ∃ o, s.here = .fin o ∧ t.g = o.fr.group := by
  unfold VerifiableInference.Desc.K12.enterFinish at h
  split at h
  · rename_i o ho
    refine ⟨o, ho, ?_⟩
    cases h1 : s.noneWaits <;> cases h2 : s.failed.isNone <;>
      simp [h1, h2, VerifiableInference.Desc.need, bind, Except.bind, pure, Except.pure] at h
    rw [← h]
  · cases h

section
variable {P W Xi : Type} {Fr : VerifiableInference.Desc.Sound.Frame} (cs : OnBytes.Codes)
  (G : FileDescription Xi) (N : Numbers) (Mg : Meaning P W) (links : List ModelPart) (ps : List Place)
  (ms : List Mem) (d : VerifiableInference.Desc.First.FoldData) (mem : ℕ → Option Mem)

/-- **WHAT THE SECOND HALF SPENDS OF THE STATE, FROM WHAT THE FIRST HALF SPENDS.** -/
theorem spent_of_facts (k : ℕ) (a : (P × VerifiableInference.Desc.First.S) × Fr.E.Str)
    (hon : VerifiableInference.Desc.Sound.onQ N Mg links ps (fun a => a) k a)
    (hm : a.1.2.failed = none)
    (hsh : Mg.shown = VerifiableInference.Desc.Sound.shownJT cs G ms)
    (hn : links.length ∈ VerifiableInference.Desc.First.rowSegs
      ((VerifiableInference.Desc.First.openSets links ps
        (VerifiableInference.Desc.First.start links))[k]?.getD []))
    (F : FactsK12 d N links.length cs ms a.1.2)
    (hfits : VerifiableInference.Desc.K12.Door.atFirstFits a.1.2 = true) (hft : d.ft = 0)
    (hcs : d.sent.codes = cs) (hmem : ∀ o x, ListedAt ms d.L.places o x → mem o = some x)
    (t : VerifiableInference.Desc.K12.T12) (G0 : OnBytes.Group)
    (he : VerifiableInference.Desc.K12.enterFinish a.1.2 = .ok t)
    (hG : t.st.groups[t.g]? = some G0) :
    Wit354.Spent cs ms N links mem a.1.2 t.g G0 := by
  obtain ⟨o₀, ho₀, eg⟩ := enter_g a.1.2 t he
  have hg : t.g = N.groupAt links.length := eg.trans (F.groupAtFinish o₀ ho₀)
  have hG' : a.1.2.st.groups[N.groupAt links.length]? = some G0 := by
    rw [← hg, ← Wit354.enter_st a.1.2 t he]
    exact hG
  have hB := (VerifiableInference.Desc.Sound.bookFitsB_iff a.1.2.book).1 hfits
  refine ⟨hg, F.codes.trans hcs, (OnBytes.Means.tidy4B_iff.1 F.tidy).inOrder, ?_, ?_, ?_⟩
  · intro o o' x h1 h2
    obtain ⟨T, hT, p1⟩ := hB o x h1
    obtain ⟨T', hT', p2⟩ := hB o' x h2
    obtain rfl : T = T' := Option.some.inj (hT.symm.trans hT')
    exact Option.some.inj (p1.symm.trans p2)
  · intro z T hT
    have h0 := bookOrd_of d.ft a.1.2 F.bookInOrder z T hT
    rw [hft, Nat.zero_add] at h0
    exact h0
  · intro o ho q hq
    obtain ⟨T, hT, -⟩ := hB o q hq
    refine ⟨(Array.getElem?_eq_some_iff.1 hT).1, ?_⟩
    obtain ⟨x, hl, hp, -, -⟩ := member_listed cs G N Mg links ps ms d.L links.length k a hon hm hsh
      hn F.seatsCarried G0 hG' o ho
    obtain ⟨ρ, yv, -, X, -, -, -, hX, hs, -⟩ := F.seedIs G0 hG' o ho x hl
    exact ⟨x, X, hmem o x hl, hl.1, Option.some.inj (hp.symm.trans hq), hX, hs⟩

end

section
variable (cs : OnBytes.Codes) {Xi P Cells Tok Cl : Type} {C : _root_.Run.PQ.CK}
  (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
  (smp : P × VerifiableInference.Desc.First.S → (s : Sending) → (i : Fin s.l.length) →
    Option ((sigOf cs s.l).om i).Smp)
  (ms : List Mem)
  (decT : (ℕ → Option (ℕ × List UInt64)) → P × VerifiableInference.Desc.First.S → Option Cells)
  (c₀ : Cells) (tokOf : P × VerifiableInference.Desc.First.S → Tok) (N : Numbers)
  (Mg : Meaning P (Wit Cells Tok MsgT)) (links : List ModelPart) (ps : List Place)
  {Fr : VerifiableInference.Desc.Sound.Frame}

/-- **THE FOURTH TIE's SECOND HALF, FROM THE FIRST HALF's OWN FACTS.** -/
theorem witness_of_facts (k : ℕ) (hp : ps[k]? = some Wit354.pK)
    (hfit : Wit354.openFitB links ps k = true)
    (hpin : Mg.pin = VerifiableInference.Desc.Sound.pinJT cs G arr smp ms)
    (hnc : Mg.noColl = VerifiableInference.Desc.Sound.noCollJT cs G smp ms)
    (hsh : Mg.shown = VerifiableInference.Desc.Sound.shownJT cs G ms)
    (hrow : Mg.row = VerifiableInference.Desc.First.rowSays N
      (VerifiableInference.Desc.First.wordsAtFirst arr))
    (hGS : VerifiableInference.Desc.Sound.GroupsSeated ms N)
    (hL : VerifiableInference.Desc.First.laysNodup arr N links ps = true)
    (hSeats : (ms.map seatOf).Nodup) (mem : ℕ → Option Mem)
    (Rch : ℕ → (P × VerifiableInference.Desc.First.S) × Fr.E.Str → Prop)
    (q : VerifiableInference.Desc.Sound.Piece C Fr (P × VerifiableInference.Desc.First.S) Cl
      (Wit Cells Tok MsgT))
    (d : VerifiableInference.Desc.First.FoldData) (hft : d.ft = 0) (hcs : d.sent.codes = cs)
    (hmem : ∀ o x, ListedAt ms d.L.places o x → mem o = some x)
    (hFacts : ∀ a : (P × VerifiableInference.Desc.First.S) × Fr.E.Str,
      VerifiableInference.Desc.Sound.onQ N Mg links ps
        (fun x : P × VerifiableInference.Desc.First.S => x) k a → Rch k a →
      ¬ a.1.2.failed ≠ none → FactsK12 d N links.length cs ms a.1.2 ∧
        VerifiableInference.Desc.K12.Door.atFirstFits a.1.2 = true) :
    T4bAt N Mg links ps Rch k q
      (VerifiableInference.Desc.Sound.extQAt cs G arr smp ms decT c₀ tokOf N links ps
        (fun x : P × VerifiableInference.Desc.First.S => x) k)
      (fun a => Tuple354 cs G smp mem a.1 (strsOf Fr a.2)) :=
  Wit354.witness_at cs G arr smp ms decT c₀ tokOf N Mg links ps k hp hfit hpin hnc hrow hGS hL
    hSeats (fun _ => mem) Rch q fun a t G0 hon hr hm he hG =>
      spent_of_facts cs G N Mg links ps ms d mem k a hon (not_not.1 hm) hsh
        (VerifiableInference.Desc.First.mem_rowSegs
          ((Wit354.openFit_gives links ps k hfit).1 (.row links.length .carried)
            (by rw [Wit354.ins_at]; simp)))
        (hFacts a hon hr hm).1 (hFacts a hon hr hm).2 hft hcs hmem t G0 he hG

/-- **THE SAME, WITH THE LAYING OF MEMBERS AT MESSAGES A TERM.** -/
theorem witness_memOf (k : ℕ) (hp : ps[k]? = some Wit354.pK)
    (hfit : Wit354.openFitB links ps k = true)
    (hpin : Mg.pin = VerifiableInference.Desc.Sound.pinJT cs G arr smp ms)
    (hnc : Mg.noColl = VerifiableInference.Desc.Sound.noCollJT cs G smp ms)
    (hsh : Mg.shown = VerifiableInference.Desc.Sound.shownJT cs G ms)
    (hrow : Mg.row = VerifiableInference.Desc.First.rowSays N
      (VerifiableInference.Desc.First.wordsAtFirst arr))
    (hGS : VerifiableInference.Desc.Sound.GroupsSeated ms N)
    (hL : VerifiableInference.Desc.First.laysNodup arr N links ps = true)
    (hSeats : (ms.map seatOf).Nodup)
    (Rch : ℕ → (P × VerifiableInference.Desc.First.S) × Fr.E.Str → Prop)
    (q : VerifiableInference.Desc.Sound.Piece C Fr (P × VerifiableInference.Desc.First.S) Cl
      (Wit Cells Tok MsgT))
    (d : VerifiableInference.Desc.First.FoldData) (hft : d.ft = 0) (hcs : d.sent.codes = cs)
    (hFacts : ∀ a : (P × VerifiableInference.Desc.First.S) × Fr.E.Str,
      VerifiableInference.Desc.Sound.onQ N Mg links ps
        (fun x : P × VerifiableInference.Desc.First.S => x) k a → Rch k a →
      ¬ a.1.2.failed ≠ none → FactsK12 d N links.length cs ms a.1.2 ∧
        VerifiableInference.Desc.K12.Door.atFirstFits a.1.2 = true) :
    T4bAt N Mg links ps Rch k q
      (VerifiableInference.Desc.Sound.extQAt cs G arr smp ms decT c₀ tokOf N links ps
        (fun x : P × VerifiableInference.Desc.First.S => x) k)
      (fun a => Tuple354 cs G smp (memOf ms d.L.places) a.1 (strsOf Fr a.2)) :=
  witness_of_facts cs G arr smp ms decT c₀ tokOf N Mg links ps k hp hfit hpin hnc hsh hrow hGS hL
    hSeats (memOf ms d.L.places) Rch q d hft hcs (fun _ _ h => memOf_listed hSeats h) hFacts

end

end H2K12

#print axioms H2K12.enter_g
#print axioms H2K12.spent_of_facts
#print axioms H2K12.witness_of_facts
#print axioms H2K12.witness_memOf
