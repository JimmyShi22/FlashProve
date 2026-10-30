-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/HeadPlanesFive.lean: the output head's row's clause on "planes", from a yes
of the head's own rounds' block and a yes of the block at the next place.

Law/RowPlanesHost.lean has the premise hlk: the two homes of what the lookup returned (S.look?,
S.lookHeard?) agree at the record. Law/RowPins.lean's look_behind shows it behind the head's own
rounds' block (piece 4 of the head's link). At piece 5 stands the sending of the reads with the step
that makes and closes the list of tables laid behind it (Block.andThen). Here the sending is shown
to leave both homes, so hlk is paid at the record behind piece 5.

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law).
  map_ok, andThen_ok: two plain inversions.
  look_laid: what the sending's block lays back leaves S.look? and S.lookHeard?.
  commit_keeps: so a yes of K1.commitAtS leaves both.
  look_at_five: the two homes agree behind piece 5's block, if they agree in front; and the record
      in front of the step that makes the tables is named.
  rowPlanes_five: THE ROW'S CLAUSE ON "planes" behind piece 5, from the two blocks' yes.
  seated_decide: a yes of the block that a lot seats at piece 4, typed at true claims (seatedClaims
      W l ms, Johnson/Stored/HeadAddsAtS.lean), is a yes of blockAt's decision. One way alone.
  rowPlanes_five_seated: rowPlanes_five from a yes of that seated block.
  rowPlanes_five_byStep: the same from Block.step of the two blocks (pieces 4 and 5), one behind the
      other. Not the fold's own call: what a driver lays around a block's step is not crossed.

Every letter under "there is", and the clause that pins it. look_at_five, rowPlanes_five: s2 by the
sending's decision at s1; o, cov, x, t by TabsLie's fields.
The text that the law speaks of: blockAt W.hS (readsOf W) (workOf W) l
(Johnson/Stored/HeadSeatAt.lean) and (K1.laterAt q gp l 5 moment arrays).andThen name
(K8.ReadsQuiet.head ...). q, gp, moment, arrays
and name are letters that no premise but the block's yes reads: whatever a description lays there.
Who calls it: nobody yet.

Premises that nobody pays here: as Law/RowPlanesHost.lean's rowPlanes_behind, without hlk.
Limits. The run "planes" is run at a later record than the one behind piece 5. Piece 5's block is
typed at the unit type of claims, as K8.ReadsQuiet.head is. No draw, no error
term, nothing on soundness.
-/
import Johnson.Desc.Kinds.Law.RowPlanesHost
import Johnson.Desc.Kinds.Law.SeatedBridge
import Johnson.Desc.K1.Places

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes OnBytes.Model OnBytes.K.Kc
open Cb Cb.Fo Cb.Fo.NumsEq TwV Fo Meaning.Planes
open Cb.Fo.Pin
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.K8
open Planes

/-- A mapped value that is there comes from a value that is there. -/
theorem map_ok {ε α β : Type} {f : α → β} {x : Except ε α} {b : β} (h : x.map f = .ok b) :
    ∃ a, x = .ok a ∧ f a = b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, Except.ok.inj h⟩

/-- A yes of two blocks laid as one: both said yes, the second at the record that the first left. -/
theorem andThen_ok {Cl : Type} {name : String} {p q : Block S Cl} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : (p.andThen name q).decide s rs gs = .ok s') :
    ∃ s2, p.decide s (rs.take p.rounds.length) (gs.take p.openings) = .ok s2 ∧
      q.decide s2 (rs.drop p.rounds.length) (gs.drop p.openings) = .ok s' := by
  have h' : (p.decide s (rs.take p.rounds.length) (gs.take p.openings)).bind (fun s2 =>
      q.decide s2 (rs.drop p.rounds.length) (gs.drop p.openings)) = .ok s' := h
  cases h1 : p.decide s (rs.take p.rounds.length) (gs.take p.openings) with
  | error e =>
    rw [h1] at h'
    cases h'
  | ok s2 =>
    rw [h1] at h'
    exact ⟨s2, rfl, h'⟩

/-- What the sending's block lays back leaves both homes of what the lookup returned. -/
theorem look_laid {Lt : Type} (s : S) (d) (L : LinkCtx) (F : Fork) :
    (((K1.laid (L := Lt) s d).putLink L).putFork F).look? = s.look? ∧
      (((K1.laid (L := Lt) s d).putLink L).putFork F).lookHeard? = s.lookHeard? := by
  cases hh : s.here with
  | head a =>
    by_cases ho : a.opened = true <;>
      simp [K1.laid, S.putLink, S.putFork, S.look?, S.lookHeard?, hh, ho]
  | _ => simp [K1.laid, S.putLink, S.putFork, S.look?, S.lookHeard?, hh]

/-- **A yes of the sending's block leaves both homes.** -/
theorem commit_keeps {Cl : Type} {P : K1.Par} {link moment : Nat} {arrays : Option (List Nat)}
    {s s' : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (hd : (K1.commitAtS P link moment arrays : Block S Cl).decide s rs gs = .ok s') :
    s'.look? = s.look? ∧ s'.lookHeard? = s.lookHeard? := by
  simp only [K1.commitAtS] at hd
  split at hd
  · obtain ⟨y, _, rfl⟩ := map_ok hd
    exact look_laid s _ _ _
  · cases hd

/-- **The two homes agree behind piece 5's block, if they agree in front.** s2: the record in front
of the step that makes the tables. -/
theorem look_at_five {q : Params.First} {gp : _root_.Desc.Plain.GPar} {l moment : Nat}
    {arrays : Option (List Nat)} {name : String} {P : ReadsQuiet.PH} {s1 s3 : S}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h5 : ((K1.laterAt q gp l 5 moment arrays).andThen name (ReadsQuiet.head P)).decide s1 rs gs =
      .ok s3) (hlk : s1.look? = s1.lookHeard?) :
    ∃ s2, (K1.laterAt q gp l 5 moment arrays : Block S Unit).decide s1
        (rs.take (K1.laterAt q gp l 5 moment arrays : Block S Unit).rounds.length)
        (gs.take (K1.laterAt q gp l 5 moment arrays : Block S Unit).openings) = .ok s2 ∧
      (ReadsQuiet.head P).decide s2
        (rs.drop (K1.laterAt q gp l 5 moment arrays : Block S Unit).rounds.length)
        (gs.drop (K1.laterAt q gp l 5 moment arrays : Block S Unit).openings) = .ok s3 ∧
      s2.look? = s2.lookHeard? ∧ s3.look? = s3.lookHeard? := by
  obtain ⟨s2, a1, a2⟩ := andThen_ok h5
  obtain ⟨c1, c2⟩ := commit_keeps a1
  obtain ⟨k1, k2, _⟩ := readsQuiet_keeps a2
  have e2 : s2.look? = s2.lookHeard? := by rw [c1, c2]; exact hlk
  exact ⟨s2, a1, a2, e2, by rw [k1, k2]; exact e2⟩

/-- **The row's clause on "planes" behind piece 5 of the head's link**, from a yes of the head's own
rounds' block at piece 4 and a yes of piece 5's block at the record that it left. -/
theorem rowPlanes_five (W : OnBytes.Model.Verify.Public) (l : Nat) {q : Params.First}
    {gp : _root_.Desc.Plain.GPar} {moment : Nat} {arrays : Option (List Nat)} {name : String}
    {s0 s1 s3 : S}
    {rs0 rs : List Fmt.RoundView} {gs0 gs : List (List (Nat × List UInt64))}
    (h4 : (blockAt W.hS (readsOf W) (workOf W) l).decide s0 rs0 gs0 = .ok s1)
    (h5 : ((K1.laterAt q gp l 5 moment arrays).andThen name
      (ReadsQuiet.head ⟨⟨1, some l, 5, .K1⟩, W.hS, W.HLy, W.H⟩)).decide s1 rs gs = .ok s3) :
    s3.look? = s3.lookHeard? ∧
    ∃ o cov x t, TabsLie W.hS W.HLy W.H s3 o cov x t ∧
      ∀ (tr : HTree), o.F.trees[readsOf W]? = some tr → tr.K ≠ 0 →
      ∀ (cellM : Nat → Nat → Nat → K),
        (W.H.tl.mats.getD (W.hS.NHf + 1 + 1) {}).m / 2 ^ W.hS.lmbH = 1 →
        planeCols x.g1.shape W.hS.lmbH ≤ (W.H.tl.mats.getD (W.hS.NHf + 1 + 1) {}).k →
        ∀ ν : _root_.Fo.Pl → K,
          (∀ r < 2 ^ W.hS.lmbH, ∀ c < planeCols x.g1.shape W.hS.lmbH,
            cellM (W.hS.NHf + 1 + 1) r c = ν (.cell r c)) →
          ∀ Wd : World K,
            ReadsAll Reading.gl o.tl.mats o.tl.funs Wd.entry (readsOf W) tr.K cellM →
            (K6OutP W W.hS.lmbH s3 Wd ↔ K6InP W.hS.lmbH s3 Wd ν) := by
  obtain ⟨s2, _, a2, e2, e3⟩ := look_at_five h5 (Came.look_behind W.hS (readsOf W) (workOf W) l h4)
  exact ⟨e3, rowPlanes_behind W l a2 e2⟩

/-- **A yes of the block that a lot seats at piece 4, typed at true claims, is a yes of blockAt's
decision**, with the same record behind. -/
theorem seated_decide {W : OnBytes.Model.Verify.Public} {l : Nat} {ms : List (Nat × Nat)}
    {b : Block S Claim} (hb : seatedClaims W l ms = some b) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (hd : b.decide s rs gs = .ok s') :
    (blockAt W.hS (readsOf W) (workOf W) l).decide s rs gs = .ok s' := by
  obtain ⟨b0, h0, rfl⟩ := seatedClaims_some hb
  have hd0 : b0.decide s rs gs = .ok s' := ((tested_decide _ _ _ b0 s s' rs gs).mp hd).1
  unfold blockClaims at h0
  cases hU : W.H.tl.ix.U.getD 2 none with
  | none =>
    rw [hU] at h0
    simp at h0
  | some i =>
    rw [hU] at h0
    simp only [Option.map_some, Option.some.injEq] at h0
    subst h0
    have e : readsOf W = i := by
      unfold readsOf
      rw [hU]
      rfl
    rw [e]
    exact hd0

/-- **The same from a yes of the seated block at piece 4** (seatedClaims W l ms). -/
theorem rowPlanes_five_seated (W : OnBytes.Model.Verify.Public) (l : Nat) {ms : List (Nat × Nat)}
    {b4 : Block S Claim} (hb : seatedClaims W l ms = some b4) {q : Params.First}
    {gp : _root_.Desc.Plain.GPar} {moment : Nat} {arrays : Option (List Nat)} {name : String}
    {s0 s1 s3 : S} {rs0 rs : List Fmt.RoundView} {gs0 gs : List (List (Nat × List UInt64))}
    (h4 : b4.decide s0 rs0 gs0 = .ok s1)
    (h5 : ((K1.laterAt q gp l 5 moment arrays).andThen name
      (ReadsQuiet.head ⟨⟨1, some l, 5, .K1⟩, W.hS, W.HLy, W.H⟩)).decide s1 rs gs = .ok s3) :
    s3.look? = s3.lookHeard? ∧
    ∃ o cov x t, TabsLie W.hS W.HLy W.H s3 o cov x t ∧
      ∀ (tr : HTree), o.F.trees[readsOf W]? = some tr → tr.K ≠ 0 →
      ∀ (cellM : Nat → Nat → Nat → K),
        (W.H.tl.mats.getD (W.hS.NHf + 1 + 1) {}).m / 2 ^ W.hS.lmbH = 1 →
        planeCols x.g1.shape W.hS.lmbH ≤ (W.H.tl.mats.getD (W.hS.NHf + 1 + 1) {}).k →
        ∀ ν : _root_.Fo.Pl → K,
          (∀ r < 2 ^ W.hS.lmbH, ∀ c < planeCols x.g1.shape W.hS.lmbH,
            cellM (W.hS.NHf + 1 + 1) r c = ν (.cell r c)) →
          ∀ Wd : World K,
            ReadsAll Reading.gl o.tl.mats o.tl.funs Wd.entry (readsOf W) tr.K cellM →
            (K6OutP W W.hS.lmbH s3 Wd ↔ K6InP W.hS.lmbH s3 Wd ν) :=
  rowPlanes_five W l (seated_decide hb h4) h5

/-- **The same from Block.step of the two blocks**, one behind the other. -/
theorem rowPlanes_five_byStep (W : OnBytes.Model.Verify.Public) (l : Nat) {ms : List (Nat × Nat)}
    {b4 : Block S Claim} (hb : seatedClaims W l ms = some b4) {q : Params.First}
    {gp : _root_.Desc.Plain.GPar} {moment : Nat} {arrays : Option (List Nat)} {name : String}
    {s0 s1 s3 : S} {ft : Nat} {rs0 rs : List Fmt.RoundView} {cols0 cols : List OpenedColumn} {n4 n5 : Nat}
    (h4 : b4.step ft s0 rs0 cols0 = .ok (s1, n4))
    (h5 : ((K1.laterAt q gp l 5 moment arrays).andThen name
      (ReadsQuiet.head ⟨⟨1, some l, 5, .K1⟩, W.hS, W.HLy, W.H⟩)).step ft s1 rs cols =
        .ok (s3, n5)) :
    s3.look? = s3.lookHeard? ∧
    ∃ o cov x t, TabsLie W.hS W.HLy W.H s3 o cov x t ∧
      ∀ (tr : HTree), o.F.trees[readsOf W]? = some tr → tr.K ≠ 0 →
      ∀ (cellM : Nat → Nat → Nat → K),
        (W.H.tl.mats.getD (W.hS.NHf + 1 + 1) {}).m / 2 ^ W.hS.lmbH = 1 →
        planeCols x.g1.shape W.hS.lmbH ≤ (W.H.tl.mats.getD (W.hS.NHf + 1 + 1) {}).k →
        ∀ ν : _root_.Fo.Pl → K,
          (∀ r < 2 ^ W.hS.lmbH, ∀ c < planeCols x.g1.shape W.hS.lmbH,
            cellM (W.hS.NHf + 1 + 1) r c = ν (.cell r c)) →
          ∀ Wd : World K,
            ReadsAll Reading.gl o.tl.mats o.tl.funs Wd.entry (readsOf W) tr.K cellM →
            (K6OutP W W.hS.lmbH s3 Wd ↔ K6InP W.hS.lmbH s3 Wd ν) := by
  obtain ⟨gs0, d4⟩ := Came.step_decide ft b4 s0 rs0 cols0 s1 n4 h4
  obtain ⟨gs, d5⟩ := Came.step_decide ft _ s1 rs cols s3 n5 h5
  exact rowPlanes_five_seated W l hb d4 d5

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.rowPlanes_five_byStep
#print axioms VerifiableInference.Desc.Kinds.Head.Law.seated_decide
#print axioms VerifiableInference.Desc.Kinds.Head.Law.rowPlanes_five_seated
#print axioms VerifiableInference.Desc.Kinds.Head.Law.commit_keeps
#print axioms VerifiableInference.Desc.Kinds.Head.Law.look_at_five
#print axioms VerifiableInference.Desc.Kinds.Head.Law.rowPlanes_five
