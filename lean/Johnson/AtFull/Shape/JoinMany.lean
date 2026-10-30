-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/JoinMany.lean: THE JOIN OF ANY NUMBER OF PIECES OF THE RUN ON SHAPES, EACH TO A
WRITTEN BORDER LESS WHAT IS SET ASIDE THERE: ONE LAW, `many_all`, OF WHICH JoinAll.lean's one_all,
three_all AND four_all ARE INSTANCES. One structure, one inductive type, thirteen definitions, ten
theorems. General; the closed facts are premises; nothing is evaluated.

Purpose. A link of the first chain is shown by Lean's kernel in pieces. How it is cut differs from
link to link: an attention link in four (JoinHalves.lean), a layers' link in more, with more set
aside at its inner borders (SixAside.lean), a cheap stretch in one. So that a new cut wants no new
join, the cut is a LIST here.

Main names.
* `SetAside`: what is set aside at a written border: a type of parts; `less`, `put`, `part`; `no`,
  the parts where a run refuses; and `eta`: less x = c → x = put c (part x). Three members:
  `SetAside.whole` (nothing: the border is written whole), `SetAside.pair` (PairAside.lean),
  `SetAside.six` (SixAside.lean). `SetAside.partE`, `SetAside.lessB`, `SetAside.lessB_ok`: pairE,
  lessB and lessB_ok of the elder files, at any member.
* `RunPiece`: `.run k A c`: a stretch of k members to the border c, written less A's parts. `.halves
  l j cl st c`: ONE member, the batching of the attention link l, in two halves cut behind its j-th
  run (JoinHalves.lean), to the border c, written less the pair. THE HALVES ARE NO STRETCH OF
  MEMBERS: they sit in the list as one piece of one member with two facts. `RunPiece.k`,
  `RunPiece.A`, `RunPiece.c`.
* `RunPiece.next hint p m S`: the start behind a piece, as a function of the record: the written
  border with the parts that the piece's own run left, as a term; BEHIND .halves THAT RUN IS THE
  UNDIVIDED MEMBER's, not the second half's. `RunPiece.Shown hint p m S`: the piece's closed facts
  under atXLC: one for a stretch; for the halves two, and that m = 14 l + 9 with l < 24 odd.
* `piecesLen`, `PiecesShown hint m S ps` (all pieces' facts, each at the start that the pieces in
  front leave: a conjunction that ends in True), `behindPieces hint m S ps` (what stands behind the
  last).
* `atXLC_all`, `piece_runs`, `pieces_run`. **`many_all`**: hsz, PiecesShown hint m (fun _ => c₀) ps,
  piecesLen ps = n, and, at every record X that publicOfO returns, behindPieces hint m (fun _ => c₀)
  ps X = c ⊢ RunsAll m n c₀ c. Where the last border is written whole the last premise is by rfl.
  The number n is the caller's own spelling: so the list of pieces does not stand in the conclusion.
* `one_of_many`, `three_of_many`, `four_of_many`: one_all's, three_all's and four_all's premises and
  conclusions, sign for sign, by many_all at the lists [.run k .whole c₁], [.run k .pair c₁, .run k'
  .pair c₂, .run k'' .whole c₃] and [.run k .pair c₁, .halves l j cl st c₂, .run k'' .whole c₃]:
  those facts are taken as they stand: Lean unfolds the one form into the other. `of_many_same`:
  Lean's own word that the three have their sisters' statements up to unfolding (an equation
  of two proofs is well typed only where their statements are definitionally one). A caller may cite
  either. `toy_six`: two stretches at letters, the inner border less the six, the second fact
  spelled by SixAside.lean's own names.

Limits. THE FACTS ARE PREMISES: that any can be met is shown nowhere here. A FACT ON A LATER PIECE
ALONE CAN BE TRUE ALTHOUGH A PIECE IN FRONT REFUSED: partE then answers the empty parts: only all
together say what the conclusion says. THE PARTS THAT ARE CARRIED COST: partE is a match on a run's
outcome: where a piece reads a part that is set aside, whoever evaluates its fact must run the
pieces in front inside it, as far as their return; BEHIND .halves THAT IS THE WHOLE BATCHING IN ONE
LINE, the very evaluation that the halves were made to spare: no law here turns the carried pair
into the second half's. SetAside's eta is all that is asked of a member: that `less` takes anything
away, or that the written border is short, is not; NOR THAT `less` LEAVES ANYTHING: a member whose
parts are the whole shape and whose `less` is constant is lawful: there the written border says
nothing and a fact says only that the run returns: that a piece ends at its written border but for
the parts means what these words say at the three members alone. THAT LEAN UNFOLDS THOSE FACTS INTO
 THE LIST's FORMS IS SHOWN IN THIS FILE AT LETTERS ALONE; at numerals and written borders it was
seen once, outside the library (an attention link's four facts taken by many_all as they
stood: seconds, and no more memory than the imports'). piecesLen ps is a sum that ends in + 0 (k +
(k' + (k'' + 0))): the premise piecesLen ps = n carries it to the caller's numeral; the later starts
are sums (m + k). IN PRACTICE A LIST ENDS AT A BORDER WRITTEN WHOLE: elsewhere the last premise says
that a term which holds a run has one value at every record that publicOfO returns: a closed fact
under atXLC could pay that, and no maker for it is here. The field `no` is free: nothing ties it to
less or put. RunsAll holds emptily if publicOfO returns nothing (JoinAll.lean). Nothing holds the
run below the table's 358 members. No piece for a layers' link's own dear members is here: only the
border's device; SetAside.six is spent by the toy alone. At VerifierAndGoals.storedPublicFiles alone; at the format's
second hash function; synthetic weights. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.JoinAll
import Johnson.AtFull.Shape.SixAside

set_option autoImplicit false
set_option relaxedAutoImplicit false

-- No default table of scales is in sight: a statement that reads a table says which.
attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open PairAside SixAside
open VerifiableInference.PlanWritten (publicOfO)
open VerifiableInference.Desc.First.Shape

/-- **What is set aside at a written border**: a type of parts; the shape less them; the parts laid
back; a shape's own parts; the parts where a run refuses; and that a shape is what it is less the
parts, with its own parts laid back. -/
structure SetAside where
  P : Type
  less : ShA → ShA
  put : ShA → P → ShA
  part : ShA → P
  no : P
  eta : ∀ x c : ShA, less x = c → x = put c (part x)

namespace SetAside

/-- Nothing is set aside: the border is written whole. -/
def whole : SetAside where
  P := Unit
  less := fun x => x
  put := fun c _ => c
  part := fun _ => ()
  no := ()
  eta := fun _ _ h => h

/-- The pair look, lookHeard (PairAside.lean). -/
def pair : SetAside where
  P := Pair
  less := PairAside.less
  put := withLk
  part := pairOf
  no := (none, none)
  eta := fun _ _ h => eta_lk h

/-- The six parts inside a layers' link (SixAside.lean). -/
def six : SetAside where
  P := Six
  less := less6
  put := withSix
  part := sixOf
  no := ((none, none), none)
  eta := fun _ _ h => eta_six h

/-- The parts that a run leaves; the field `no` where it refuses. (Nothing ties `no` to less or put,
and no proof spends it; at the three members it is the empty parts.) -/
def partE (A : SetAside) (r : Except String ShA) : A.P :=
  match r with
  | .ok x => A.part x
  | .error _ => A.no

/-- "It returns x, and x less the parts is c." -/
noncomputable def lessB (A : SetAside) (r : Except String ShA) (c : ShA) : Bool :=
  match r with
  | .ok x => @decide (A.less x = c) (ByLists.decShAL _ _)
  | .error _ => false

/-- Where lessB accepts, the run returned c with its own parts. -/
theorem lessB_ok {A : SetAside} {r : Except String ShA} {c : ShA} (h : A.lessB r c = true) :
    r = .ok (A.put c (A.partE r)) := by
  cases r with
  | error e => cases h
  | ok x => exact congrArg Except.ok (A.eta x c (@of_decide_eq_true _ (ByLists.decShAL _ _) h))

end SetAside

/-- **A piece of the run**: a stretch of k members, to a border c written less the parts of A; or
ONE member, an attention link's batching, shown in two halves (JoinHalves.lean), to a border c
written less the pair. -/
inductive RunPiece where
  | run (k : Nat) (A : SetAside) (c : ShA)
  | halves (l j : Nat) (cl : List ClaimSh) (st : ChainSh) (c : ShA)

/-- How many members a piece has. -/
def RunPiece.k : RunPiece → Nat
  | .run k _ _ => k
  | .halves .. => 1

/-- What is set aside at the border behind it. -/
def RunPiece.A : RunPiece → SetAside
  | .run _ A _ => A
  | .halves .. => .pair

/-- The written border behind it. -/
def RunPiece.c : RunPiece → ShA
  | .run _ _ c => c
  | .halves _ _ _ _ c => c

section
variable (hint : Nat → List (Nat × Nat))

/-- The start behind a piece, as a function of the record: the written border with the parts that
the piece's own run left, as a term. m: the piece's first member; S: its start. BEHIND .halves THAT
RUN IS THE UNDIVIDED MEMBER's (runH hint X m 1 (S X)), NOT THE SECOND HALF's: in value the same pair
(by half_join's proof; its statement does not say so), as a term not: a later piece that opens the
pair pays the whole batching in one line. -/
noncomputable def RunPiece.next (p : RunPiece) (m : Nat) (S : Verify.Public → ShA)
    (X : Verify.Public) : ShA :=
  p.A.put p.c (p.A.partE (runH hint X m p.k (S X)))

/-- **The closed facts that show a piece**: one under atXLC for a stretch; for the halves: that m is
an attention link's batching's number, and two under atXLC. -/
def RunPiece.Shown (p : RunPiece) (m : Nat) (S : Verify.Public → ShA) : Prop :=
  match p with
  | .run k A c => atXLC (fun X => A.lessB (runH hint X m k (S X)) c) = true
  | .halves l j cl st c => l < 24 ∧ l % 2 = 1 ∧ m = 14 * l + 9 ∧
      atXLC (fun X => frontB (frontH X l j (S X)) cl st) = true ∧
      atXLC (fun X => backB (backH X l j (cl, withLkC st (pairH (frontH X l j (S X))))) (S X).2 c) =
        true

/-- The number of members of a list of pieces. -/
def piecesLen : List RunPiece → Nat
  | [] => 0
  | p :: ps => p.k + piecesLen ps

/-- All pieces' facts, each at the start that the pieces in front leave. -/
def PiecesShown : Nat → (Verify.Public → ShA) → List RunPiece → Prop
  | _, _, [] => True
  | m, S, p :: ps => p.Shown hint m S ∧ PiecesShown (m + p.k) (p.next hint m S) ps

/-- What stands behind the last piece. -/
noncomputable def behindPieces : Nat → (Verify.Public → ShA) → List RunPiece → Verify.Public → ShA
  | _, S, [] => S
  | m, S, p :: ps => behindPieces (m + p.k) (p.next hint m S) ps

/-- A closed fact under atXLC holds at every record that publicOfO returns. -/
theorem atXLC_all (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975) {t : Verify.Public → Bool}
    (h : atXLC t = true) {X₀ : Verify.Public}
    (hX : publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) =
      .ok X₀) : t X₀ = true := by
  obtain ⟨X₁, h1, e⟩ := atXLC_zFull hsz h
  obtain rfl : X₁ = X₀ := Except.ok.inj (h1.symm.trans hX)
  exact e

/-- One piece, at a record. -/
theorem piece_runs (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975) {X₀ : Verify.Public}
    (hX : publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) =
      .ok X₀) (p : RunPiece) (m : Nat) (S : Verify.Public → ShA) (h : p.Shown hint m S) :
    (shapeL (LWn X₀)).runFrom m p.k (S X₀) = .ok (p.next hint m S X₀) := by
  rw [runH_eq hint hX]
  cases p with
  | run k A c => exact SetAside.lessB_ok (atXLC_all hsz h hX)
  | halves l j cl st c =>
    obtain ⟨hl, ho, rfl, Ha, Hb⟩ := h
    exact lessB_ok (half_join hint X₀ hl ho j (S X₀) cl st c (atXLC_all hsz Ha hX)
      (atXLC_all hsz Hb hX))

/-- All pieces, at a record. -/
theorem pieces_run (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975) {X₀ : Verify.Public}
    (hX : publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) =
      .ok X₀) : ∀ (ps : List RunPiece) (m : Nat) (S : Verify.Public → ShA),
      PiecesShown hint m S ps →
      (shapeL (LWn X₀)).runFrom m (piecesLen ps) (S X₀) = .ok (behindPieces hint m S ps X₀)
  | [], _, _, _ => rfl
  | p :: ps, m, S, F =>
    runFrom_chain _ (piece_runs hint hsz hX p m S F.1) (pieces_run hsz hX ps _ _ F.2)

/-- **THE JOIN OF ANY NUMBER OF PIECES**: from the whole written shape c₀, the pieces' facts, the
number of their members in the caller's own spelling (hn), and that what stands behind the last
piece is c at every record that publicOfO returns (he: by rfl where the last border is written
whole) ⊢ RunsAll. -/
theorem many_all (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975) (m : Nat) (c₀ c : ShA) (ps : List RunPiece)
    (F : PiecesShown hint m (fun _ => c₀) ps) {n : Nat} (hn : piecesLen ps = n)
    (he : ∀ X, publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) =
      .ok X → behindPieces hint m (fun _ => c₀) ps X = c) :
    RunsAll m n c₀ c := fun X₀ hX => by
  rw [← he X₀ hX, ← hn]
  exact pieces_run hint hsz hX ps m (fun _ => c₀) F

/-! ## The three elder joins are its instances -/

/-- one_all's premise and conclusion, by many_all. -/
theorem one_of_many (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975) (m k : Nat) (c₀ c₁ : ShA)
    (P : atXLC (fun X => wholeB (runH hint X m k c₀) c₁) = true) : RunsAll m k c₀ c₁ :=
  many_all hint hsz m c₀ c₁ [.run k .whole c₁] ⟨P, trivial⟩ (Nat.add_zero k) fun _ _ => rfl

/-- three_all's premises and conclusion, by many_all. -/
theorem three_of_many (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975) (m k k' k'' : Nat)
    (c₀ c₁ c₂ c₃ : ShA)
    (P1 : atXLC (fun X => lessB (runH hint X m k c₀) c₁) = true)
    (P2 : atXLC (fun X => lessB (runH hint X (m + k) k' (withLk c₁ (lkA hint m k c₀ X))) c₂) = true)
    (P3 : atXLC (fun X => wholeB (runH hint X (m + k + k') k''
      (withLk c₂ (lkB hint m k k' c₀ c₁ X))) c₃) = true) :
    RunsAll m (k + k' + k'') c₀ c₃ :=
  many_all hint hsz m c₀ c₃ [.run k .pair c₁, .run k' .pair c₂, .run k'' .whole c₃]
    ⟨P1, P2, P3, trivial⟩ (show k + (k' + (k'' + 0)) = k + k' + k'' by omega) fun _ _ => rfl

/-- four_all's premises and conclusion, by many_all. -/
theorem four_of_many (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975) (m k k'' : Nat) {l : Nat} (hl : l < 24)
    (ho : l % 2 = 1) (hm : m + k = 14 * l + 9) (j : Nat) (c₀ c₁ c₂ c₃ : ShA)
    (cl : List ClaimSh) (st : ChainSh)
    (P1 : atXLC (fun X => lessB (runH hint X m k c₀) c₁) = true)
    (P2a : atXLC (fun X => frontB (frontH X l j (withLk c₁ (lkA hint m k c₀ X))) cl st) = true)
    (P2b : atXLC (fun X => backB (backH X l j
      (cl, withLkC st (pairH (frontH X l j (withLk c₁ (lkA hint m k c₀ X)))))) c₁.2 c₂) = true)
    (P3 : atXLC (fun X => wholeB (runH hint X (m + k + 1) k''
      (withLk c₂ (lkB hint m k 1 c₀ c₁ X))) c₃) = true) :
    RunsAll m (k + 1 + k'') c₀ c₃ :=
  many_all hint hsz m c₀ c₃ [.run k .pair c₁, .halves l j cl st c₂, .run k'' .whole c₃]
    ⟨P1, ⟨hl, ho, hm, P2a, P2b⟩, P3, trivial⟩ (show k + (1 + (k'' + 0)) = k + 1 + k'' by omega)
    fun _ _ => rfl

/-- Lean's own word that the three have their sisters' statements UP TO UNFOLDING: an equation
of two proofs is well typed only where their statements are definitionally one. (It does not see how
a premise is spelled, nor a binder's name or brackets: that the texts are the same sign for sign is
a reader's to hold.) -/
theorem of_many_same : @one_of_many = @one_all ∧ @three_of_many = @three_all ∧
    @four_of_many = @four_all := ⟨rfl, rfl, rfl⟩

/-- A TOY WITH THE SIX SET ASIDE, at letters: two stretches, the inner border written less the six:
the second fact as a caller would spell it by SixAside.lean's own names. -/
theorem toy_six (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975) (m k k' : Nat) (c₀ c₁ c₂ : ShA)
    (P1 : atXLC (fun X => SetAside.six.lessB (runH hint X m k c₀) c₁) = true)
    (P2 : atXLC (fun X => wholeB (runH hint X (m + k) k'
      (withSix c₁ (sixE (runH hint X m k c₀)))) c₂) = true) : RunsAll m (k + k') c₀ c₂ :=
  many_all hint hsz m c₀ c₂ [.run k .six c₁, .run k' .whole c₂] ⟨P1, P2, trivial⟩
    (show k + (k' + 0) = k + k' by omega) fun _ _ => rfl

end

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.SetAside
#print axioms Johnson.AtFull.Shape.SetAside.whole
#print axioms Johnson.AtFull.Shape.SetAside.pair
#print axioms Johnson.AtFull.Shape.SetAside.six
#print axioms Johnson.AtFull.Shape.SetAside.partE
#print axioms Johnson.AtFull.Shape.SetAside.lessB
#print axioms Johnson.AtFull.Shape.SetAside.lessB_ok
#print axioms Johnson.AtFull.Shape.RunPiece
#print axioms Johnson.AtFull.Shape.RunPiece.k
#print axioms Johnson.AtFull.Shape.RunPiece.A
#print axioms Johnson.AtFull.Shape.RunPiece.c
#print axioms Johnson.AtFull.Shape.RunPiece.next
#print axioms Johnson.AtFull.Shape.RunPiece.Shown
#print axioms Johnson.AtFull.Shape.piecesLen
#print axioms Johnson.AtFull.Shape.PiecesShown
#print axioms Johnson.AtFull.Shape.behindPieces
#print axioms Johnson.AtFull.Shape.atXLC_all
#print axioms Johnson.AtFull.Shape.piece_runs
#print axioms Johnson.AtFull.Shape.pieces_run
#print axioms Johnson.AtFull.Shape.many_all
#print axioms Johnson.AtFull.Shape.one_of_many
#print axioms Johnson.AtFull.Shape.three_of_many
#print axioms Johnson.AtFull.Shape.four_of_many
#print axioms Johnson.AtFull.Shape.of_many_same
#print axioms Johnson.AtFull.Shape.toy_six
