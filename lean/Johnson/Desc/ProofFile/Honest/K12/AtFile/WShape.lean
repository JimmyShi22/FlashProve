-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/WShape.lean: the shape of the state on entry to the last
chain's proximity test, as a term of what the two earlier chains hand over. The shape in front of a
test on the shared chain is a term of the plan (`doorU`, `doorO`, Johnson/Desc/K14/Shape/Door.lean).
Here it is a function of the shape of the first chain's last record: the last chain begins at that
record whole (`start₃E_st`), and one block changes it.

  `secondSh`       the shape behind the block "K14, second part", on shapes: the ground's own
                   functions on shapes, in the block's order
  `second_carries` where the block says yes, `secondSh` returns the shape behind it
  `doorOwnSh`      the shape on entry: the core behind that block, the own group's number, nothing
                   passes yet, the mask's number
  `start_numbers`  what the start lays: the numbers of the own group and of the mask, and the border
  `door_own_shape` the start's yes, the block's yes and the way in: `doorOwnSh` at the shapes of
                   what was handed is the shape of the state on entry
  `frontFive_of_own`   so the public test on the shape (`frontFiveB`) at the state on entry, from the
                   same test at `doorOwnSh`

What each name reads. `secondSh` reads of the shared chain's end the shape of its statement, the
shape of its book and Omega's number; of the plan the leaf class of Omega; of the first chain's
last record the shape of its statement and book.

The premise that stays. `frontFiveB` at this shape reads the first chain's last record's shape c.
A closed value of c is the run on shapes over all the first chain's members
(Johnson/AtFull/Shape/JoinTable.lean) or a written border: neither stands. So a caller has
`doorOwnSh ... c` as a term, and the line on it as a named premise.

Limits.
- Nothing on a value: a shape holds no field element. Nothing on the rows: tidy, dense and the
  claims stand beside the shape.
- The block's guard that Omega has the plan's shape is not used: the term reads Omega's shape off
  the shared statement.
- Nothing on a run. Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.Third.Law.AtDoor
import Johnson.Desc.Third.Law.StartBook
import Johnson.Desc.Third.Law.Sharp
import Johnson.Desc.K12.Seat.Own
import Johnson.Desc.Ground.Shape.Ground
import Johnson.Desc.ProofFile.Honest.K12.FrontAtShape

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtFile
open OnBytes
open VerifiableInference.Desc.Ground.Sh (CoreSh StSh BookSh coreSh stSh bookSh orcSh treeSh shD
  adoptS elsewhereS joinS addRowS adopt_carries elsewhere_carries join_carries addRow_carries
  orc_get place_get tree_get)
open VerifiableInference.Desc.Third (S₃ P₁₄ SharedOut Border batchLinearConstraintsSecondPart start₃E)
open VerifiableInference.Desc.Third.Law (takeOver_inv k14Second_inv start₃E_inv start₃_inv
  firstOutFrom_inv start₃E_st start₃E_book linDotRow_plain)
open VerifiableInference.Desc.K12 (T12 P12)
open VerifiableInference.Desc.K12.Seat (enterOwn)
open ProofFile.Honest.Sh (TestSh testSh PassSh)
open ProofFile.Honest.K12 (frontFiveB)

/-- **The shape behind "K14, second part".** S: the plan's shape. own: the own group's number. b, k,
omega: the shape of the shared chain's statement and book, and Omega's number there. c: the shape
in front. -/
def secondSh (S : Params.LinShape) (own : ℕ) (b : StSh) (k : BookSh) (omega : ℕ) (c : CoreSh) :
    Option CoreSh :=
  (k.place[omega]?).bind fun q => (k.trees[q.1]?).bind fun t => (b.oracles[omega]?).bind fun y =>
    (adoptS c #[{ shape := y.shape, leafClass := S.omegaLeafClass }] [(t.number, t.src)]).bind
      fun a => (a.1[0]?).bind fun mine => (elsewhereS a.2 mine b omega).bind fun d₁ =>
        (joinS d₁ own mine false).bind fun d₂ => addRowS d₂ own .plain

/-- **Where the block says yes, the term returns the shape behind it.** -/
theorem second_carries {Cl : Type} (p : P₁₄) (s s' : S₃) (x : Border) (rs : List Fmt.RoundView)
    (gs : List (List (ℕ × List UInt64))) (hx : s.loc.border = some x)
    (h : (batchLinearConstraintsSecondPart (Cl := Cl) p).decide s rs gs = .ok s') :
    secondSh p.S s.loc.own (stSh x.shared.st) (bookSh x.shared.book) x.shared.omega
        (coreSh ⟨s.st, s.book, s.roots⟩) = some (coreSh ⟨s'.st, s'.book, s'.roots⟩) := by
  obtain ⟨x', a, dot, b, hb, ht, hd, hr, e⟩ := k14Second_inv p s s' rs gs h
  rw [hx] at hb
  obtain rfl := Option.some.inj hb
  obtain ⟨q, t, y, ⟨ids, dA⟩, d₁, h1, h2, h3, h4, h5, h6, h7⟩ :=
    takeOver_inv p.S s.loc.own x.shared (s.withCols []) a ht
  have e1 : (bookSh x.shared.book).place[x.shared.omega]? = some q := (place_get _ _).trans h1
  have e2 : (bookSh x.shared.book).trees[q.1]? = some (treeSh t) := by
    rw [tree_get, h2]
    rfl
  have e3 : (stSh x.shared.st).oracles[x.shared.omega]? = some (orcSh y) := by
    rw [orc_get, h3]
    rfl
  have e4 : adoptS (coreSh ⟨s.st, s.book, s.roots⟩)
      #[{ shape := (orcSh y).shape, leafClass := p.S.omegaLeafClass }]
      [((treeSh t).number, (treeSh t).src)] = some (ids, shD dA) :=
    adopt_carries (s.withCols []) dA _ _ ids h4
  have e5 : ids[0]? = some a.1 := h5
  have e6 : elsewhereS (shD dA) a.1 (stSh x.shared.st) x.shared.omega = some (shD d₁) :=
    elsewhere_carries dA d₁ a.1 x.shared.st x.shared.omega h6
  have e7 : joinS (shD d₁) s.loc.own a.1 false = some (shD a.2) :=
    join_carries d₁ a.2 s.loc.own a.1 false h7
  have e8 : addRowS (shD a.2) s.loc.own .plain = some (shD b) := by
    have k := addRow_carries a.2 b s.loc.own dot hr
    rw [linDotRow_plain _ _ _ _ _ _ _ _ hd] at k
    exact k
  have key : secondSh p.S s.loc.own (stSh x.shared.st) (bookSh x.shared.book) x.shared.omega
      (coreSh ⟨s.st, s.book, s.roots⟩) = some (shD b) := by
    unfold secondSh
    rw [e1, Option.bind_some, e2, Option.bind_some, e3, Option.bind_some, e4, Option.bind_some]
    show (ids[0]?).bind _ = _
    rw [e5, Option.bind_some]
    show (elsewhereS (shD dA) a.1 _ _).bind _ = _
    rw [e6, Option.bind_some, e7, Option.bind_some]
    exact e8
  subst e
  exact key

/-- **The shape on entry to the own test.** mask: the number of the message that holds the first
fold's table. c: the shape of the first chain's last record; the last chain has received no root. -/
def doorOwnSh (S : Params.LinShape) (own : ℕ) (mask : Option ℕ) (b : StSh) (k : BookSh)
    (omega : ℕ) (c : CoreSh) : Option TestSh :=
  (secondSh S own b k omega { c with roots := 0 }).map fun c' => ⟨c', own, .nothing, mask⟩

/-- What the start lays of the numbers and of the border. -/
theorem start_numbers {codes : Codes} {S : Params.LinShape} {st₁ : Statement} {book₁ : TreeBook}
    {roots₁ w₁ own₁ : ℕ} {mask₁ : Option ℕ} {pile₁ : List TensorRow} {o : SharedOut} {s₀ : S₃}
    (h : start₃E codes S st₁ book₁ roots₁ w₁ own₁ mask₁ pile₁ o = .ok s₀) :
    s₀.loc.own = own₁ ∧ s₀.loc.mask = mask₁ ∧ ∃ g, s₀.loc.border = some ⟨g, o⟩ := by
  obtain ⟨f, hf, hst⟩ := start₃E_inv _ _ _ _ _ _ _ _ _ _ _ h
  obtain ⟨_, _, _, ho, hm, _⟩ := firstOutFrom_inv _ _ _ _ _ _ _ _ _ hf
  obtain ⟨_, _, e0⟩ := start₃_inv _ _ _ _ hst
  subst e0
  exact ⟨ho, hm, f.g, rfl⟩

/-- **At the last chain: the start's yes, the block's yes and the way in give the shape on entry.**
-/
theorem door_own_shape {Cl : Type} (p : P₁₄) {st₁ : Statement} {book₁ : TreeBook}
    {roots₁ w₁ own₁ : ℕ} {mask₁ : Option ℕ} {pile₁ : List TensorRow} {o : SharedOut} {s₀ s : S₃}
    {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))} {t : T12}
    (h₀ : start₃E p.codes p.S st₁ book₁ roots₁ w₁ own₁ mask₁ pile₁ o = .ok s₀)
    (h₁ : (batchLinearConstraintsSecondPart (Cl := Cl) p).decide s₀ rs gs = .ok s) (h₂ : enterOwn s = .ok t) :
    doorOwnSh p.S own₁ mask₁ (stSh o.st) (bookSh o.book) o.omega
      (coreSh ⟨st₁, book₁, roots₁⟩) = some (testSh t) := by
  obtain ⟨ho, hm, g, hb⟩ := start_numbers h₀
  have hst := start₃E_st _ _ _ _ _ _ _ _ _ _ _ h₀
  obtain ⟨eb, er, -⟩ := start₃E_book _ _ _ _ _ _ _ _ _ _ _ h₀
  have k : secondSh p.S own₁ (stSh o.st) (bookSh o.book) o.omega
      (coreSh ⟨s₀.st, s₀.book, s₀.roots⟩) = some (coreSh ⟨s.st, s.book, s.roots⟩) := by
    rw [← ho]
    exact second_carries p s₀ s ⟨g, o⟩ rs gs hb h₁
  have ec : ({ coreSh ⟨st₁, book₁, roots₁⟩ with roots := 0 } : CoreSh) =
      coreSh ⟨s₀.st, s₀.book, s₀.roots⟩ := by
    rw [hst, eb, er]
    rfl
  obtain ⟨_, _, _, _, _, _, _, _, e⟩ := k14Second_inv p s₀ s rs gs h₁
  have hl : s.loc.own = own₁ ∧ s.loc.mask = mask₁ := by
    rw [e]
    exact ⟨ho, hm⟩
  have et : t = { st := s.st, book := s.book, roots := s.roots, g := s.loc.own, pass := .nothing
                  mask := s.loc.mask } := (Except.ok.inj h₂).symm
  unfold doorOwnSh
  rw [ec, k, Option.map_some, et, hl.1, hl.2]
  rfl

/-- **The public test on the state on entry, from the same test at the term.** -/
theorem frontFive_of_own {Cl : Type} (p : P₁₄) {st₁ : Statement} {book₁ : TreeBook}
    {roots₁ w₁ own₁ : ℕ} {mask₁ : Option ℕ} {pile₁ : List TensorRow} {o : SharedOut} {s₀ s : S₃}
    {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))} {t : T12} (q : P12) (K : Codes)
    (h₀ : start₃E p.codes p.S st₁ book₁ roots₁ w₁ own₁ mask₁ pile₁ o = .ok s₀)
    (h₁ : (batchLinearConstraintsSecondPart (Cl := Cl) p).decide s₀ rs gs = .ok s) (h₂ : enterOwn s = .ok t)
    (hl : (doorOwnSh p.S own₁ mask₁ (stSh o.st) (bookSh o.book) o.omega
      (coreSh ⟨st₁, book₁, roots₁⟩)).any (frontFiveB q K) = true) :
    frontFiveB q K (testSh t) = true := by
  rw [door_own_shape p h₀ h₁ h₂] at hl
  exact hl

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.second_carries
#print axioms ProofFile.Honest.K12.AtFile.start_numbers
#print axioms ProofFile.Honest.K12.AtFile.door_own_shape
#print axioms ProofFile.Honest.K12.AtFile.frontFive_of_own
