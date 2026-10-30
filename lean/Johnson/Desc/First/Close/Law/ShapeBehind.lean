-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/ShapeBehind.lean: WHAT K10 PAYS, OFF ITS OWN YES, OF THE TABLE's
PROMISE BEHIND ITS BLOCK: a mark stays; the book-keeping; where the book stands. Statements and
proofs; a second test on the table, with its yes at two rows of segments. A file BESIDE the table of
joints: it turns nothing of it.

  `putLive_link`, `putLive_standOf`, `putRec_standOf`, `putRec_link`: K10's writing (`putRec`,
    Johnson/Desc/First/Batch/Place.lean: the frame into the live copy of the calls' state; the
    statement; the rows owed) leaves where the record stands (`standOf`) and the open segment's
    number.
  `shapeAt_behind`: so the book-keeping (`shapeAt`) holds behind, where nothing is owed behind and
    the table lets the chain stand at the place behind as in front, in the same segment.
    `bookAt_behind`: `bookAt` holds behind, where the statement written has as many messages and the
    plan counts no tree and no message for the block.
  `closersNext links ps`: A TEST ON THE TABLE: behind every place of the kind K10 stands a place of
    the same segment at which the chain is to stand as in front. `closersNext_at`: its yes at the
    k-th place. `closersNext_real`: IT SAYS YES at 25 and at 5 segments (`sortsOf`,
    PromiseBehind.lean): by the kernel. `closersNext_tooth`: it can say no.
  `k10_promise_behind`: `onAt` behind K10's writing of what `closeFrame` returned, by the rule
    `onAt_step_close` (PromiseBehind.lean) with `closeFrame_st`, `behind_size` (StBehind.lean) and
    `putRec_keeps` (Leaves.lean): all beside this file.
Limits. `k10_promise_behind` HAS AS PREMISES STILL: the promise in front; the rule's two facts on
the table (hRows, hSub: paid at the two real rows by PromiseBehind.lean's test, hSub under "what is
kept lies in its group"); hst, hl (paid there by `closersNext_real`); ht, hm: the plan's numbers of
trees and of messages are the same at the two places: shown of no numbers; AND SIX SENTENCES ON THE
MEANING's LETTERS: "decodes" rides; "in order" rides; the public items behind; `pubP` behind; "held"
rides; "shown" and "no collision" ride: these can be paid only at a filling. z' (the first component
behind) is a letter. It speaks of K10's writing, not yet of the seated block or its piece. Nothing
on soundness.

-/
import Johnson.Desc.First.Close.Law.PromiseBehind
import Johnson.Desc.First.Close.Law.Leaves
import Johnson.Desc.First.Close.Law.StBehind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First

open VerifiableInference.Desc.K9 (recOf putRec)
open VerifiableInference.Desc.First.Close (Rec)

/-- Writing the live copy of the calls' state leaves the open link's number, and whether a link is
open. -/
theorem putLive_link (s : S) (c : OnBytes.Model.ChainCheck) :
    (s.putLive c).link?.map (·.link) = s.link?.map (·.link) := by
  unfold S.putLive
  cases h : s.link? with
  | none => simp only [S.link?] at h ⊢; exact congrArg _ h
  | some L =>
    unfold S.putLink S.link? at *
    cases hh : s.here with
    | lay a => rw [hh] at h; simp only at h ⊢; cases h; rfl
    | att a => rw [hh] at h; simp only at h ⊢; cases h; rfl
    | head a =>
      rw [hh] at h
      simp only at h ⊢
      by_cases ho : a.opened = true
      · rw [if_pos ho] at h ⊢
        cases h
        simp [ho]
      · rw [if_neg ho] at h
        cases h
    | between => rw [hh] at h; cases h
    | fin a => rw [hh] at h; cases h
    | mem a => rw [hh] at h; cases h

/-- Writing the live copy leaves where the record stands. -/
theorem putLive_standOf (s : S) (c : OnBytes.Model.ChainCheck) :
    standOf (s.putLive c) = standOf s := by
  unfold S.putLive
  cases h : s.link? with
  | none => rfl
  | some L =>
    unfold S.putLink
    cases hh : s.here with
    | lay a => simp only [standOf, hh]
    | att a => simp only [standOf, hh]
    | head a =>
      by_cases ho : a.opened = true
      · simp only [ho, if_true, standOf, hh, S.inLink, S.fork?]
      · simp only [ho, Bool.false_eq_true, if_false]
    | between => simp only [standOf, hh]
    | fin a => simp only [standOf, hh]
    | mem a => simp only [standOf, hh]

/-- K10's writing leaves where the record stands, and the open link's number. -/
theorem putRec_standOf (s : S) (r : Rec) : standOf (putRec s r) = standOf s :=
  putLive_standOf s _

theorem putRec_link (s : S) (r : Rec) :
    (putRec s r).link?.map (·.link) = s.link?.map (·.link) :=
  putLive_link s _

/-- **THE BOOK-KEEPING BEHIND K10's WRITING**: from the book-keeping in front, where nothing is owed
behind and the table lets the chain stand at the place behind as at the place in front, in the same
segment. -/
theorem shapeAt_behind (links : List ModelPart) (p p' : Place) (s : S) (r : Rec) (hr : r.owed = none)
    (hst : standAt links p' = standAt links p) (hl : p'.link = p.link)
    (h : shapeAt links (some p) s = true) : shapeAt links (some p') (putRec s r) = true := by
  unfold shapeAt at h ⊢
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at h ⊢
  obtain ⟨⟨h1, -⟩, h3⟩ := h
  refine ⟨⟨by rw [putRec_standOf, hst]; exact h1, Or.inl ?_⟩, ?_⟩
  · have e := (Close.putRec_keeps s r).2.2.2.2.2
    unfold S.noneWaits
    rw [e, hr]
  · have e := putRec_link s r
    cases hb : (putRec s r).link? with
    | none => rfl
    | some L' =>
      rw [hb] at e
      cases ha : s.link? with
      | none => rw [ha] at e; cases e
      | some L =>
        rw [ha] at e h3
        simp only [Option.map_some, Option.some.injEq] at e
        simp only [Option.all_some, beq_iff_eq] at h3 ⊢
        rw [hl, h3, e]

/-- **WHERE THE BOOK STANDS BEHIND K10's WRITING**: from where it stood in front, where the
statement that is written has as many messages and the plan counts no tree and no message for the
block. -/
theorem bookAt_behind (N : Numbers) (p p' : Option Place) (s : S) (r : Rec)
    (hs : r.st.oracles.size = s.st.oracles.size) (ht : N.treesAt p' = N.treesAt p)
    (hm : N.msgsAt p' = N.msgsAt p) (h : bookAt N p s = true) :
    bookAt N p' (putRec s r) = true := by
  unfold bookAt at h ⊢
  have eb := (Close.putRec_keeps s r).1
  have es : (putRec s r).st = r.st := rfl
  rw [eb, es, hs, ht, hm]
  exact h

/-- A TEST ON THE TABLE: behind every place of the kind K10 stands a place of the same segment, at
which the chain is to stand as in front. -/
def closersNext (links : List ModelPart) : List Place → Bool
  | p :: p' :: ps =>
    (p.kind != .K10 || (standAt links p' == standAt links p && p'.link == p.link)) &&
      closersNext links (p' :: ps)
  | [p] => p.kind != .K10
  | [] => true

/-- What its yes gives at the k-th place. -/
theorem closersNext_at (links : List ModelPart) : ∀ (ps : List Place) (k : Nat) (p : Place),
    closersNext links ps = true → ps[k]? = some p → p.kind = .K10 →
      ∃ p', ps[k + 1]? = some p' ∧ standAt links p' = standAt links p ∧ p'.link = p.link
  | [], _, _, _, h, _ => by simp at h
  | [q], 0, p, hf, h, hk => by
    obtain rfl : q = p := by simpa using h
    simp [closersNext, hk] at hf
  | [_], k + 1, _, _, h, _ => by simp at h
  | q :: p' :: ps, 0, p, hf, h, hk => by
    obtain rfl : q = p := by simpa using h
    unfold closersNext at hf
    simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hf
    obtain ⟨h1 | ⟨h1, h2⟩, -⟩ := hf
    · exact absurd hk h1
    · exact ⟨p', rfl, h1, h2⟩
  | _ :: p' :: ps, k + 1, p, hf, h, hk => by
    unfold closersNext at hf
    exact closersNext_at links (p' :: ps) k p (Bool.and_eq_true_iff.1 hf).2 (by simpa using h) hk

set_option maxRecDepth 1000000 in
/-- **It says yes at both real rows of segments.** -/
theorem closersNext_real : ∀ several : Bool,
    closersNext (sortsOf 25) (flatPlacesOf (sortsOf 25) several) = true ∧
      closersNext (sortsOf 5) (flatPlacesOf (sortsOf 5) several) = true := by
  decide +kernel

/-- A tooth: it can say no: a place of the kind K10 with a place of another segment behind it. -/
theorem closersNext_tooth :
    closersNext (sortsOf 5) [⟨1, some 0, 11, .K10⟩, ⟨1, some 1, 12, .K9⟩] = false := by
  decide

/-- **THE TABLE's PROMISE BEHIND A YES OF K10's WRITING.** a: in front; x: what the frame's closing
returned at what K10 reads of a's record; the record behind is K10's writing of it. p, p': the
places of K10's block and of the block behind it. OF THE NINE SENTENCES THAT THE RULE ASKS BESIDE
THE PROMISE IN FRONT AND ITS TWO FACTS ON THE TABLE, THREE ARE PAID HERE: a mark stays; the
book-keeping behind; where the book stands behind (under two equations on the plan's numbers). SIX
STAY, all on the meaning's letters. -/
theorem k10_promise_behind {P W : Type} (N : Numbers) (Mg : Meaning P W) (links : List ModelPart)
    (p p' : Place) (O : List Item) (Q Q' : List Pub) (a : P × S) (z' : P) (y y' : Strs)
    (es : List Fmt.Entry) (rs : List Fmt.RoundView) (x : OnBytes.ReqFrame × OnBytes.Statement)
    (hx : Close.closeFrame (recOf a.2).owed (recOf a.2).frame (recOf a.2).st es rs = .ok x)
    (hRows : rowSegs (stepOpen O (rowOf links p)) = [])
    (hSub : ∀ t ∈ sampledIn N (stepOpen O (rowOf links p)), t ∈ sampledIn N O)
    (hst : standAt links p' = standAt links p) (hl : p'.link = p.link)
    (ht : N.treesAt (some p') = N.treesAt (some p)) (hm : N.msgsAt (some p') = N.msgsAt (some p))
    (ha : onAt N Mg links (some p) O Q a y)
    (hDec : Mg.decodes a y → Mg.decodes (z', putRec a.2 ⟨none, x.1, x.2⟩) y')
    (hIn : a.2.failed = none → Mg.inOrder a = true →
      Mg.inOrder (z', putRec a.2 ⟨none, x.1, x.2⟩) = true)
    (hPub : a.2.failed = none → pubHeld Mg O Q a = true →
      pubHeld Mg (stepOpen O (rowOf links p)) Q' (z', putRec a.2 ⟨none, x.1, x.2⟩) = true)
    (hPP : a.2.failed = none → (∀ q ∈ Q, Mg.pubP q a) →
      ∀ q ∈ Q', Mg.pubP q (z', putRec a.2 ⟨none, x.1, x.2⟩))
    (hHeld : a.2.failed = none → ∀ t ∈ sampledIn N O, Mg.held t.1 t.2 a = true →
      Mg.held t.1 t.2 (z', putRec a.2 ⟨none, x.1, x.2⟩) = true)
    (hSN : a.2.failed = none → ∀ t ∈ sampledIn N O, Mg.shown t.1 t.2 y ∧ Mg.noColl t.1 t.2 a y →
      Mg.shown t.1 t.2 y' ∧ Mg.noColl t.1 t.2 (z', putRec a.2 ⟨none, x.1, x.2⟩) y') :
    onAt N Mg links (some p') (stepOpen O (rowOf links p)) Q'
      (z', putRec a.2 ⟨none, x.1, x.2⟩) y' := by
  obtain ⟨G, id, -, -, e3⟩ := Close.closeFrame_st hx
  have hsz : x.2.oracles.size = a.2.st.oracles.size := by
    rw [e3]
    exact Close.behind_size _ _ _ _
  have hf : (putRec a.2 ⟨none, x.1, x.2⟩).failed = a.2.failed :=
    (Close.putRec_keeps a.2 _).2.2.1
  refine onAt_step_close N Mg links (some p) (some p') O Q Q' (rowOf links p) a _ y y' hRows hSub
    ha (fun h => by show (putRec a.2 _).failed ≠ none; rw [hf]; exact h) hDec
    (fun hm0 _ => ?_) (fun hm0 _ => hIn hm0) (fun hm0 _ => hPub hm0)
    (fun _ _ hb => bookAt_behind N _ _ a.2 _ hsz ht hm hb) (fun hm0 _ => hPP hm0)
    (fun hm0 _ => hHeld hm0) (fun hm0 _ => hSN hm0)
  rcases ha.2 with hmk | ⟨hB, -⟩
  · exact absurd hm0 hmk
  · simp only [Bool.and_eq_true] at hB
    exact shapeAt_behind links p p' a.2 _ rfl hst hl hB.1.1.1.1.1

end VerifiableInference.Desc.First

#print axioms VerifiableInference.Desc.First.closersNext_at
#print axioms VerifiableInference.Desc.First.closersNext_real
#print axioms VerifiableInference.Desc.First.closersNext_tooth
#print axioms VerifiableInference.Desc.First.k10_promise_behind
#print axioms VerifiableInference.Desc.First.putLive_link
#print axioms VerifiableInference.Desc.First.putLive_standOf
#print axioms VerifiableInference.Desc.First.shapeAt_behind
#print axioms VerifiableInference.Desc.First.bookAt_behind
