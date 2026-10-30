-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/JoinHalves.lean: THE ONE MEMBER OF AN ATTENTION LINK THAT IS TOO DEAR IN ONE
PIECE, ITS BATCHING (number 14 l + 9, l odd), SHOWN IN TWO HALVES, AND THE JOIN OF FOUR PIECES:
`half_join`, `four_as_one`. THE PLACE j OF THE CUT (behind how many of the link's runs of claims) IS
A LETTER. Seven definitions, five theorems. General laws and implications: THE CLOSED FACTS ARE
PREMISES; nothing is evaluated here.

Purpose. JoinPieces.lean joins three closed facts on pieces of a link. At link 1 the middle piece,
the batching alone, stood above the bounds that we hold a line for Lean's kernel to (timed trials;
not shown here); cut between two of its ten runs, each half stood within them. BatchSplit.lean parts
the step on shapes (`batchGS_cut`). What stands between the halves is the gathering's own state: the
claims' shapes gathered so far, and the chain's shape. The claims hold nothing of look and
lookHeard; the chain's shape does: so the pair is set aside there as at the borders
(PairAside.lean).

Main names.
* `decClaims`: the decider for lists of claims' shapes: lawful by its type, whatever the search
  took. Seen on scratch sheets, not shown here: at Lean's default bound on the size of an instance's
  term (128) the search fails, first at lists of runs' shapes (a list of a product of six numbers:
  "size: 158 ≥ 128", by Lean's own trace); under the one option in front of it it succeeds; a walk
  over the values of the definitions that the found term reaches met Lean's own deciders for lists,
  products, options and numbers alone, and no name with "Array" in it. A definition, no instance: it
  is named wherever it is spent, in the proofs too.
* `attNums L l`: the four records that the table's cell at the batching looks up (TabLetters.lean's
  TabL.batch; TabLight.lean's cellsH). attNums, frontH and backH hold no test on l: half_join's hl
  and ho keep an even l and an l from 24 on out.
* `frontH X l j a`, `backH X l j y`: the two halves at LWn X: batchFrontG over the order's first j
  runs; batchBackGL.1 over the rest: both over gAtt, the light rows' steps. These two, frontB and
  backB are marked noncomputable: they are meant for Lean's kernel alone, and no code is to be
  compiled for them.
* `frontB r cl st`: "r returned y; y's claims are cl; y's chain's shape less the two is st." `pairH
  r`: the pair that r's state bears. `backB r F c`: "r returned u; (u, F) less the two is c."
* `frontB_ok`; `cellsH_batch`: the light cell at 14 l + 9, where the four numbers are there.
* **`half_join`**: frontB (frontH X l j a) cl st = true → backB (backH X l j (cl, withLkC st (pairH
  (frontH X l j a)))) a.2 c = true → lessB (runH hint X (14 * l + 9) 1 a) c = true:
  JoinPieces.lean's test on the middle piece, at one record X.
* `three_at`: three_as_one's argument at one record that publicOfO returns. **`four_as_one`**: hsz
  and four closed facts under atXLC (P1 · P2a · P2b · P3) ⊢ three_as_one's conclusion with k' = 1.
  HOW A CALLER PAYS THE SMALL PREMISES: l is handed in by name, hl, ho and hm by decide: for link 1:
  four_as_one hint hsz 15 8 5 (l := 1) (by decide) (by decide) (by decide) 6 …. THE LATER STARTS ARE
  SPELLED AS SUMS: P3 wants m + k + 1 (15 + 8 + 1), not 14 * l + 10 and not a numeral.

Limits. THE FOUR FACTS ARE PREMISES: that they can be met is shown nowhere here. P2b ALONE CAN BE
TRUE ALTHOUGH THE FIRST HALF REFUSED: pairH then answers (none, none); likewise P2a, P2b and P3
alone although the piece in front refused (pairE's default): only together do they say what the
conclusion says. THE CARRIED PAIRS COST: pairH and pairE are matches on a run's outcome: to read ANY
part of a carried pair the evaluator must first bring the run in front to its return, through all
its guards: so where a run of the second half reads look or lookHeard ("planes" does), P2b pays the
first half's guards once more, and beneath them, through lkA, the piece in front (in a timed run
at link 1, cut behind the sixth run: some 31 s and 4.8 GB over the same half at a pair that holds no
such run; not shown here). P3's start is JoinPieces.lean's lkB: it holds the whole member's run, not
the halves'; no law here turns it into the second half's pair; a P3 that runs to the link's end lays
both to none and, in the same runs, never opened it. The conclusion speaks of shapeL (LWn X₀): LWn
X₀ is no test on X₀; that run is the table's own only with the head at the full-size files, hsz and
lettersTest_atXL besides (YesAtZFullN.lean's yes_of_publicN), which are not called here. Nothing
holds m + k + 1 + k'' below the table's 358 members. three_at repeats nine lines of three_pieces'
proof. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.JoinPieces
import Johnson.AtFull.Shape.BatchSplit

set_option autoImplicit false
set_option relaxedAutoImplicit false

-- No default table of scales is in sight: a statement that reads a table says which.
attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open PairAside
open VerifiableInference.PlanWritten (publicOfO)
open VerifiableInference.Desc.First.Shape
open VerifiableInference.Desc.K9 (testsWhere Where SegSort TWhere)
open VerifiableInference.Desc.K9.Shape
open IM (subAt)

set_option synthInstance.maxSize 100000 in
/-- The decider for lists of claims' shapes, by Lean's own search under a wider bound on the size of
an instance's term. A definition, no instance: it is named wherever it is spent. -/
def decClaims : DecidableEq (List ClaimSh) := inferInstance

/-- The four records that the table's cell at an attention link's batching looks up. No test on l:
at an even l, or from 24 on, it may answer with records that are no member's. -/
def attNums (L : TabLetters) (l : Nat) :
    Option (Where × (SegSort × Nat × TWhere) × Attention.Plan ×
      VerifiableInference.Desc.First.Look.P) :=
  match L.k9 l, testsWhere L.XZ l 0, L.XG.A[l / 2]?,
      VerifiableInference.Desc.First.Look.placeAt L.XG l false with
  | some p, some w, some A, some q => some (p, w, A, q)
  | _, _, _, _ => none

/-- The first half of link l's batching at LWn X: the draw, the guard, the first j runs. -/
noncomputable def frontH (X : Verify.Public) (l j : Nat) (a : ShA) :
    Except String (List ClaimSh × ChainSh) :=
  match attNums (LWn X) l with
  | some (p, w, A, q) =>
    batchFrontG w.1 (gAtt A q.lm) p.rows
      ((VerifiableInference.Desc.First.orderOf (subAt l)).take j) a.1
  | none => .error "the batching: no numbers"

/-- The second half: the other runs, the adding, the test on the mark. -/
noncomputable def backH (X : Verify.Public) (l j : Nat) (y : List ClaimSh × ChainSh) :
    Except String ChainSh :=
  match attNums (LWn X) l with
  | some (_, w, A, q) =>
    batchBackGL.1 w.1 (gAtt A q.lm) ((VerifiableInference.Desc.First.orderOf (subAt l)).drop j) y
  | none => .error "the batching: no numbers"

/-- "It returns y; the claims gathered are cl; the chain's shape less the two is st." -/
noncomputable def frontB (r : Except String (List ClaimSh × ChainSh)) (cl : List ClaimSh)
    (st : ChainSh) : Bool :=
  match r with
  | .ok y => @decide (y.1 = cl) (decClaims _ _) &&
      @decide (withLkC y.2 (none, none) = st) (ByLists.decChainShL _ _)
  | .error _ => false

/-- The pair that the first half leaves; (none, none) where it refuses. (pairE's like, one level
down: on the gathering's state.) -/
def pairH (r : Except String (List ClaimSh × ChainSh)) : Pair :=
  match r with
  | .ok y => (y.2.look, y.2.lookHeard)
  | .error _ => (none, none)

/-- "It returns u; u with the rows' makes F, less the two, is c." -/
noncomputable def backB (r : Except String ChainSh) (F : FormsSh) (c : ShA) : Bool :=
  match r with
  | .ok u => @decide (less (u, F) = c) (ByLists.decShAL _ _)
  | .error _ => false

/-- Where frontB accepts, the first half returned cl and st with its own pair. -/
theorem frontB_ok {r : Except String (List ClaimSh × ChainSh)} {cl : List ClaimSh} {st : ChainSh}
    (h : frontB r cl st = true) : r = .ok (cl, withLkC st (pairH r)) := by
  cases r with
  | error e => cases h
  | ok y =>
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.1 h
    have e1 : y.1 = cl := @of_decide_eq_true _ (decClaims _ _) h1
    have e2 : withLkC y.2 (none, none) = st := @of_decide_eq_true _ (ByLists.decChainShL _ _) h2
    have e4 : y.2 = withLkC st (y.2.look, y.2.lookHeard) := by
      subst e2
      obtain ⟨c, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17,
        a18⟩ := y
      rfl
    obtain ⟨y1, y2⟩ := y
    subst e1
    exact congrArg (fun z => Except.ok (y1, z)) e4

/-- The light cell at an attention link's batching, where the four numbers are there. -/
theorem cellsH_batch (hint : Nat → List (Nat × Nat)) (L : TabLetters) {l : Nat} (hl : l < 24)
    (ho : l % 2 = 1) {p : Where} {w : SegSort × Nat × TWhere} {A : Attention.Plan}
    {q : VerifiableInference.Desc.First.Look.P} (hN : attNums L l = some (p, w, A, q)) :
    (cellsH hint L (14 * l + 9)).1 = liftQ (batchGSL.1 p.rows w.1 (gAtt A q.lm)
      (VerifiableInference.Desc.First.orderOf (subAt l))) := by
  unfold attNums at hN
  unfold cellsH
  rw [if_neg (by omega)]
  have el : (14 * l + 9 - 1) / 14 = l := by omega
  have ej : (14 * l + 9 - 1) % 14 = 8 := by omega
  simp only [el, ej, ho]
  cases h1 : L.k9 l with
  | none => rw [h1] at hN; cases hN
  | some p' =>
    cases h2 : testsWhere L.XZ l 0 with
    | none => rw [h1, h2] at hN; cases hN
    | some w' =>
      cases h3 : L.XG.A[l / 2]? with
      | none => rw [h1, h2, h3] at hN; cases hN
      | some A' =>
        cases h4 : VerifiableInference.Desc.First.Look.placeAt L.XG l false with
        | none => rw [h1, h2, h3, h4] at hN; cases hN
        | some q' =>
          rw [h1, h2, h3, h4] at hN
          cases hN
          rfl

/-- **THE TWO HALVES GIVE THE MEMBER**: at an attention link l: where the first half from a returns
cl and st (less the two), and the second half from cl and st with the first half's own pair returns
c (less the two): the one member 14 l + 9 from a returns c (less the two). The place j of the cut is
a letter. -/
theorem half_join (hint : Nat → List (Nat × Nat)) (X : Verify.Public) {l : Nat} (hl : l < 24)
    (ho : l % 2 = 1) (j : Nat) (a : ShA) (cl : List ClaimSh) (st : ChainSh) (c : ShA)
    (Ha : frontB (frontH X l j a) cl st = true)
    (Hb : backB (backH X l j (cl, withLkC st (pairH (frontH X l j a)))) a.2 c = true) :
    lessB (runH hint X (14 * l + 9) 1 a) c = true := by
  have ea := frontB_ok Ha
  cases hN : attNums (LWn X) l with
  | none =>
    unfold frontH at Ha
    rw [hN] at Ha
    cases Ha
  | some N =>
    obtain ⟨p, w, A, q⟩ := N
    have er : runH hint X (14 * l + 9) 1 a = (cellsH hint (LWn X) (14 * l + 9)).1 a := rfl
    rw [er, cellsH_batch hint (LWn X) hl ho hN]
    unfold liftQ
    rw [← batchGSL.2, batchGS_cut w.1 (gAtt A q.lm) p.rows j]
    have ef : batchFrontG w.1 (gAtt A q.lm) p.rows
        ((VerifiableInference.Desc.First.orderOf (subAt l)).take j) a.1 = frontH X l j a := by
      unfold frontH
      rw [hN]
    rw [ef, ea]
    show lessB ((batchBackG w.1 (gAtt A q.lm)
      ((VerifiableInference.Desc.First.orderOf (subAt l)).drop j)
      (cl, withLkC st (pairH (frontH X l j a)))).map fun u => (u, a.2)) c = true
    rw [batchBackGL.2]
    have eb : batchBackGL.1 w.1 (gAtt A q.lm)
        ((VerifiableInference.Desc.First.orderOf (subAt l)).drop j)
        (cl, withLkC st (pairH (frontH X l j a))) =
        backH X l j (cl, withLkC st (pairH (frontH X l j a))) := by
      unfold backH
      rw [hN]
    rw [eb]
    cases hb : backH X l j (cl, withLkC st (pairH (frontH X l j a))) with
    | error e => rw [hb] at Hb; cases Hb
    | ok u => rw [hb] at Hb; exact Hb

section
variable (hint : Nat → List (Nat × Nat))

/-- three_as_one's argument at one record: where publicOfO returns X₀ and the three tests accept AT
X₀, the k + k' + k'' members from m on return c₃ over the table's second text. -/
theorem three_at {pol KL : ByteArray} {lay : Option ByteArray} {X₀ : Verify.Public}
    (hX : publicOfO OnBytes.secondHashFunction pol KL lay = .ok X₀) (m k k' k'' : Nat) (c₀ c₁ c₂ c₃ : ShA)
    (t1 : lessB (runH hint X₀ m k c₀) c₁ = true)
    (t2 : lessB (runH hint X₀ (m + k) k' (withLk c₁ (lkA hint m k c₀ X₀))) c₂ = true)
    (t3 : wholeB (runH hint X₀ (m + k + k') k'' (withLk c₂ (lkB hint m k k' c₀ c₁ X₀))) c₃ = true) :
    (shapeL (LWn X₀)).runFrom m (k + k' + k'') c₀ = .ok c₃ := by
  have hp : ∀ (g : Nat) (A : Attention.Plan), (LWn X₀).XG.A[g]? = some A →
      VerifiableInference.Desc.First.Att.P.padKeyOk
        (VerifiableInference.Desc.First.Att.P.parCOf A).geo = true :=
    fun g A hA => hpad_of_public hX g A hA
  have e : ∀ m k a, (shapeL (LWn X₀)).runFrom m k a = runH hint X₀ m k a := fun m k a =>
    (runFrom_congr (funext fun n => congrArg Prod.fst (cellsH_eq hint _ hp n))
      (funext fun n => congrArg Prod.snd (cellsH_eq hint _ hp n)) m k a).symm
  have e1 : (shapeL (LWn X₀)).runFrom m k c₀ = .ok (withLk c₁ (lkA hint m k c₀ X₀)) :=
    (e _ _ _).trans (lessB_ok t1)
  have e2 : (shapeL (LWn X₀)).runFrom (m + k) k' (withLk c₁ (lkA hint m k c₀ X₀)) =
      .ok (withLk c₂ (lkB hint m k k' c₀ c₁ X₀)) := (e _ _ _).trans (lessB_ok t2)
  rw [runFrom_add, runFrom_add, e1]
  show ((shapeL (LWn X₀)).runFrom (m + k) k' (withLk c₁ (lkA hint m k c₀ X₀))).bind _ = _
  rw [e2]
  show (shapeL (LWn X₀)).runFrom (m + (k + k')) k'' (withLk c₂ (lkB hint m k k' c₀ c₁ X₀)) = _
  rw [← Nat.add_assoc]
  exact (e _ _ _).trans (wholeB_ok t3)

/-- **THE JOIN OF FOUR PIECES**: as three_as_one, with the one member in the middle, an attention
link's batching, shown in two halves. -/
theorem four_as_one (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975) (m k k'' : Nat) {l : Nat} (hl : l < 24)
    (ho : l % 2 = 1) (hm : m + k = 14 * l + 9) (j : Nat) (c₀ c₁ c₂ c₃ : ShA)
    (cl : List ClaimSh) (st : ChainSh)
    (P1 : atXLC (fun X => lessB (runH hint X m k c₀) c₁) = true)
    (P2a : atXLC (fun X => frontB (frontH X l j (withLk c₁ (lkA hint m k c₀ X))) cl st) = true)
    (P2b : atXLC (fun X => backB (backH X l j
      (cl, withLkC st (pairH (frontH X l j (withLk c₁ (lkA hint m k c₀ X)))))) c₁.2 c₂) = true)
    (P3 : atXLC (fun X => wholeB (runH hint X (m + k + 1) k''
      (withLk c₂ (lkB hint m k 1 c₀ c₁ X))) c₃) = true) :
    ∃ X₀ : Verify.Public,
      publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀ ∧
      (shapeL (LWn X₀)).runFrom m (k + 1 + k'') c₀ = .ok c₃ := by
  obtain ⟨X₀, hX, t1⟩ := atXLC_zFull hsz P1
  obtain ⟨X₁, hX1, ta⟩ := atXLC_zFull hsz P2a
  obtain ⟨X₂, hX2, tb⟩ := atXLC_zFull hsz P2b
  obtain ⟨X₃, hX3, t3⟩ := atXLC_zFull hsz P3
  obtain rfl : X₁ = X₀ := Except.ok.inj (hX1.symm.trans hX)
  obtain rfl : X₂ = X₁ := Except.ok.inj (hX2.symm.trans hX)
  obtain rfl : X₃ = X₂ := Except.ok.inj (hX3.symm.trans hX)
  have t2 : lessB (runH hint X₃ (m + k) 1 (withLk c₁ (lkA hint m k c₀ X₃))) c₂ = true := by
    rw [hm]
    exact half_join hint X₃ hl ho j (withLk c₁ (lkA hint m k c₀ X₃)) cl st c₂ ta tb
  exact ⟨X₃, hX, three_at hint hX m k 1 k'' c₀ c₁ c₂ c₃ t1 t2 t3⟩

end

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.decClaims
#print axioms Johnson.AtFull.Shape.attNums
#print axioms Johnson.AtFull.Shape.frontH
#print axioms Johnson.AtFull.Shape.backH
#print axioms Johnson.AtFull.Shape.frontB
#print axioms Johnson.AtFull.Shape.pairH
#print axioms Johnson.AtFull.Shape.backB
#print axioms Johnson.AtFull.Shape.frontB_ok
#print axioms Johnson.AtFull.Shape.cellsH_batch
#print axioms Johnson.AtFull.Shape.half_join
#print axioms Johnson.AtFull.Shape.three_at
#print axioms Johnson.AtFull.Shape.four_as_one
