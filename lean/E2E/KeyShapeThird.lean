--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyShapeThird.lean: THE KEY FILE's THIRD CHAIN, CUT IN TWO: STRUCTURE | VALUES. The cut
is Johnson/Desc/ProofFile/Honest/Thread/Shape.lean's: a verifier's state is read onto its SHAPE
(numbers, flags, lists of these; no field element); each sub-protocol's tests on the structure are
written as a function g of the shape alone; what is left are its named tests on values. Owed at each
sub-protocol: (B1) where its step accepts and g returns, g returns the shape behind; (B2) where g
returns and the named tests on values pass, its decision returns. Definitions, statements and
proofs. NOTHING IS SHOWN OF ANY PROVER: no completeness.

THE SHAPE. `Sh₃ := CoreSh × LocSh`. `CoreSh` (Johnson/Desc/Ground/Shape/Core.lean): statement, book
of trees and count of roots without a field element and without a row's summands. `LocSh`: ONE MARK
on the statement (`stTidyB`, Marks.lean: every open row and sample row passes the tests of its
adding), the third chain's five named numbers and, until the first sub-protocol has taken it, the
shape of what it reads of the two earlier chains' ends (`BorderSh`): ONE MARK on the row weights
(`weightsB`, E2E/KeyDotFits.lean), the mark on the shared chain's last statement, that statement's
and its book's shapes, the shared point's LENGTH, Omega's number there. The reader takes the shape
of the test on the table, which is public: the mark on the weights is said at it.

What is shown here (part 1: the two sub-protocols that are one test each, and turn nothing).
  `borderSh`, `locSh`, `sh₃`: the readers.
  `takenSh`, **`takenSh_eq`**: the list of the taken trees' numbers is a function of the shape.
  `gSources`: "the taken trees' sources" on the shape. **`sources_carries`**, **`sources_returns`**:
    (B1), (B2), with no test on values.
  `untestedSh`, **`untestedSh_eq`**: the chain's end's two clauses are a function of the shape.
  `gEnd`: the chain's end on the shape. **`end_carries`**, **`end_returns`**: (B1), (B2), with no
    test on values.

Limits. The first sub-protocol and the own proximity test are not here.


-/
import E2E.KeySources
import E2E.KeyDotFits
import Johnson.Desc.Ground.Shape.Marks
import Johnson.Desc.ProofFile.Honest.Thread.ShapeJoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.AtFiles
open OnBytes
open OnBytes.Params (LinShape)
open ProofFile.Honest (CarriesR ReturnsR)
open VerifiableInference.Desc.Ground.Sh
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Third (S₃ Loc₃ Border SharedOut takenOf takenSources end₃)

/-! ## The shape -/

/-- What the first sub-protocol reads of the two earlier chains' ends. weights: the mark on the row
weights (E2E/KeyDotFits.lean). tidy: the mark on the shared chain's last statement. -/
structure BorderSh where
  weights : Bool
  tidy : Bool
  st : StSh
  book : BookSh
  psi : Nat
  omega : Nat
  deriving DecidableEq, Repr

def borderSh (S : LinShape) (codes : Codes) (x : Border) : BorderSh :=
  ⟨weightsB S (linLayOmega codes S) x.g, stTidyB x.shared.st, stSh x.shared.st,
    bookSh x.shared.book, x.shared.psi.length, x.shared.omega⟩

/-- The third chain's named values, and the mark on its statement (`stTidyB`,
Johnson/Desc/Ground/Shape/Marks.lean). -/
structure LocSh where
  tidy : Bool
  w : Nat
  own : Nat
  mask : Option Nat
  border : Option BorderSh
  omega : Nat
  firstTree : Nat
  deriving DecidableEq, Repr

def locSh (S : LinShape) (st : Statement) (l : Loc₃) : LocSh :=
  ⟨stTidyB st, l.w, l.own, l.mask, l.border.map (borderSh S st.codes), l.omega, l.firstTree⟩

/-- **The third chain's shape.** -/
abbrev Sh₃ : Type := CoreSh × LocSh

/-- **The reader.** S: the shape of the test on the table: public. -/
def sh₃ (S : LinShape) (s : S₃) : Sh₃ :=
  (coreSh ⟨s.st, s.book, s.roots⟩, locSh S s.st s.loc)

/-! ## "The taken trees' sources" -/

/-- The taken trees' numbers, of the shape. -/
def takenSh (a : Sh₃) : Option (List (Nat × Nat)) :=
  (a.1.st.groups[a.2.own]?).bind fun G =>
    (G.members ++ a.2.mask.toList).mapM fun i =>
      ((a.1.book.place[i]?).bind fun q => a.1.book.trees[q.1]?).map fun t =>
        (if i == a.2.omega then 1 else 0, t.number)

/-- **It is the library's list.** -/
theorem takenSh_eq (S : LinShape) (s : S₃) : takenSh (sh₃ S s) = takenOf s := by
  unfold takenSh takenOf
  show ((stSh s.st).groups[s.loc.own]?).bind _ = _
  rw [grp_get]
  cases s.st.groups[s.loc.own]? with
  | none => rfl
  | some G =>
    show ((G.members.toList ++ s.loc.mask.toList).mapM fun i =>
      (((bookSh s.book).place[i]?).bind fun q => (bookSh s.book).trees[q.1]?).map fun t =>
        ((if i == s.loc.omega then 1 else 0 : Nat), t.number)) = _
    congr 1
    funext i
    rw [place_get]
    cases s.book.place[i]? with
    | none => rfl
    | some q =>
      show (((bookSh s.book).trees[q.1]?).map _) = (s.book.trees[q.1]?).map _
      rw [tree_get]
      cases s.book.trees[q.1]? <;> rfl

/-- The sub-protocol on the shape. rounds: the own test's declared rounds: public. -/
def gSources (rounds : List Fmt.DeclaredRound) (a : Sh₃) : Except String Sh₃ :=
  match takenSh a with
  | some ts => if tiedB rounds ts then .ok a else .error "the taken trees' sources are not tied"
  | none => .error "a member of the own group, or the mask, has no tree in the book"

theorem sources_carries {Cl : Type} (S : LinShape) (own : Block S₃ Cl) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) :
    CarriesR (sh₃ S) (fun s => (takenSources own).decide s rs gs) (gSources own.rounds) := by
  intro s s' t hf hg
  obtain rfl := VerifiableInference.Desc.Third.Law.takenSources_same own s s' rs gs hf
  unfold gSources at hg
  split at hg
  · split at hg
    · exact (Except.ok.inj hg).symm
    · cases hg
  · cases hg

theorem sources_returns {Cl : Type} (S : LinShape) (own : Block S₃ Cl) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) :
    ReturnsR (sh₃ S) (fun s => (takenSources own).decide s rs gs) (gSources own.rounds)
      (fun _ => true) := by
  intro s t hg _
  unfold gSources at hg
  rw [takenSh_eq] at hg
  split at hg
  · rename_i ts hts
    split at hg
    · rename_i hb
      exact ⟨s, takenSources_passes own s rs gs (tied_of_B own s ts hts hb)⟩
    · cases hg
  · cases hg

/-! ## The chain's end -/

/-- The end's two clauses, of the shape. -/
def untestedSh (a : StSh) : Bool :=
  a.groups.all (·.inRun) && a.oracles.all fun x =>
    !x.sampled || x.groups.any fun g => (a.groups[g]?).any (·.inRun)

/-- **They are the library's.** -/
theorem untestedSh_eq (S : Statement) :
    untestedSh (stSh S) = (VerifiableInference.Desc.ChainEnd.untestedL S).all (·.2) := by
  unfold untestedSh VerifiableInference.Desc.ChainEnd.untestedL
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  congr 1
  · show (S.groups.toList.map grpSh).all (·.inRun) = _
    rw [List.all_map, ← Array.all_toList]
    rfl
  · show (S.oracles.toList.map orcSh).all _ = _
    rw [List.all_map, ← Array.all_toList]
    congr 1
    funext x
    show (!x.sampled || x.groups.any fun g => ((stSh S).groups[g]?).any (·.inRun)) = _
    congr 2
    funext g
    rw [grp_get]
    cases S.groups[g]? <;> rfl

/-- The chain's end on the shape. -/
def gEnd (a : Sh₃) : Except String Sh₃ :=
  if untestedSh a.1.st then .ok a else .error "something is left untested"

theorem refuse_iff (l : VerifiableInference.Desc.ChainEnd.Clauses) :
    VerifiableInference.Desc.ChainEnd.refuse l = .ok () ↔ l.all (·.2) = true := by
  unfold VerifiableInference.Desc.ChainEnd.refuse
  constructor
  · intro h
    split at h
    · cases h
    · rename_i hn
      rw [List.all_eq_true]
      intro c hc
      have := List.find?_eq_none.1 hn c hc
      simpa using this
  · intro h
    have hn : l.find? (!·.2) = none := List.find?_eq_none.2 fun c hc => by
      simp [List.all_eq_true.1 h c hc]
    rw [hn]

theorem end_carries {Cl : Type} (S : LinShape) (front : List (Block S₃ Cl)) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) :
    CarriesR (sh₃ S) (fun s => (end₃ front).decide s rs gs) gEnd := by
  intro s s' t hf hg
  have hf' : (VerifiableInference.Desc.ChainEnd.refuse
      (VerifiableInference.Desc.ChainEnd.untestedL s.st)).map (fun _ => s) = .ok s' := hf
  have e : s = s' := by
    cases hr : VerifiableInference.Desc.ChainEnd.refuse
        (VerifiableInference.Desc.ChainEnd.untestedL s.st) with
    | error w => rw [hr] at hf'; cases hf'
    | ok u => rw [hr] at hf'; exact Except.ok.inj hf'
  subst e
  unfold gEnd at hg
  split at hg
  · exact (Except.ok.inj hg).symm
  · cases hg

theorem end_returns {Cl : Type} (S : LinShape) (front : List (Block S₃ Cl)) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) :
    ReturnsR (sh₃ S) (fun s => (end₃ front).decide s rs gs) gEnd (fun _ => true) := by
  intro s t hg _
  unfold gEnd at hg
  split at hg
  · rename_i hb
    have hb' : untestedSh (stSh s.st) = true := hb
    rw [untestedSh_eq] at hb'
    refine ⟨s, ?_⟩
    show (VerifiableInference.Desc.ChainEnd.refuse
      (VerifiableInference.Desc.ChainEnd.untestedL s.st)).map (fun _ => s) = .ok s
    rw [(refuse_iff _).2 hb']
    rfl
  · cases hg

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.takenSh_eq
#print axioms AtPublicFiles.AtFiles.sources_carries
#print axioms AtPublicFiles.AtFiles.sources_returns
#print axioms AtPublicFiles.AtFiles.untestedSh_eq
#print axioms AtPublicFiles.AtFiles.refuse_iff
#print axioms AtPublicFiles.AtFiles.end_carries
#print axioms AtPublicFiles.AtFiles.end_returns
