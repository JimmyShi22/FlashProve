-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/Game.lean: **THE GAME OF THE PROXIMITY TEST, AS A STATEMENT OF ITS OWN: FROM A
COUNT AT THE BATCHING's ROUND AND THE CHAIN's OWN LEMMA TO "THE PROVER HAS LOST" OVER THE PIECE's
WRITTEN ROUNDS, AT THE PIECE's OWN ERRORS.** Statements and proofs. For the row words_are_committed
of the list of the laws owed: the part of it that joins no letters: the game.

What is said. Take the piece as the tiling makes it (`pieceOf`, Johnson/Desc/Sound/Tiles.lean): the
block of the proximity test, its stretch dB :: dt ("BAT"'s round, then the chain's), WHATEVER
EXTRACTOR, and errors (e, εt). If e is at least the count of the batching's round (the list's bound
at the first radius times the number of rows less one, times the sampler's number of that round) and
εt bears the chain's own errors, then at every statement inside the promise the prover has lost at
the start (`Iop.Doomed`, round by round, at (e, εt)) towards: wherever the piece says yes, there is
ONE witness within the first radius of the group's word, of whose own words all the batched rows
hold, and whose parts are candidates at each sampled member (`NTuple`).

  `GameAt`, `GameAtO`: the form, at any piece: the two arms (the first fold's mask came earlier; the
    first fold sends its own).
  `gameAt_iff`: the form is "has lost" over p.ds at p.err: by definition.
  `leads_iff_refuses`: for every reduction: the form is "where there is no such tuple, the prover
    has lost towards a refusal".
  `K12Game`, `k12_game`; `K12GameO`, `k12_gameO`: the two arms at the block's own record.
  `K12GameF2`, `k12_gameF2`: the first arm at the first chain's finish of a description, at the seat
    on the chain's own state.
  `cand_of_leads`: a tool, for every piece: a law of this form, a promise that gives its promise, a
    promise behind that a yes hands on, and the seams of letters give `TestGivesCand`
    (Johnson/Desc/Sound/WordsLaw.lean) to the letter.
  `K12Seams`; `k12_testGivesCand`: that tool at the proximity test's piece: WHAT IS LEFT OF
    `TestGivesCand` THERE ONCE THE GAME IS PAID: three premises, none of which speaks of a
    challenge, a count or an error.
Where the game is played: LawY.lean (`k12_lawY` | `k12_lawYO`: the count at "BAT"'s round; behind
each other challenge the library's `chain_many_list`), the payer of the count
(Johnson/Desc/K12/Law/Tuple/BatValsPayAt.lean, the kind's own law's side), PaidRec.lean,
FreeOff.lean, AtF2.lean. Here: larger errors (`Doomed.mono_err`) and any extractor (the reduction
reads neither).
Limits. NO SOUNDNESS IS CLAIMED. The facts on codes (`CodesAt`) and "εt bears the chain's errors"
are premises inside `AtPlace` | `AtPlaceOwn`; `johOk`, `batOneOk`, `PayPub`: tests on the plan whose
yes is a run's word. The promise (the record's count of roots; `FirstOpens` | `FirstOpensOwn`;
`PayRec`) is handed on by no block here. That e is small against the number of "BAT"'s challenges
is not said here. `NTuple` is not "every row holds at the witness". The seams are not paid here. A
VERIFIER THAT SAYS NO TO ALL HAS THE FORM (GameChecks.lean): that the piece says yes at a statement
inside the promise is no theorem anywhere: it is the block's listed runs' word.

-/
import Johnson.Desc.K12.Coin.AtF2
import Johnson.Desc.Sound.WordsLaw
import Johnson.Desc.Sound.Tiles

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open Iop Prob _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain
open H2K.JointK (recAt)
open H2K.Pin (NTuple PayRec)
open H2K.Pub (sgOf writtenOf WR chainFrom CodesAt spendOk PayPub johOk batV0)
open H2K.First (batOneOk)
open Johnson.G.OfPlan (rootsOf)
open Johnson.Pack (sigOf)

/-! ## 1 The form -/

/-- **The game's form, first arm, at any piece**: at every statement whose record counts n roots,
whose first openings are the book's and at which the batched rows lie within the group, the prover
has lost towards: a yes gives one tuple for all rows. -/
def GameAt {W : Type} (F : Frame) (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ) (rad : Sg → ℕ)
    (rd : ℕ → ℕ) (base n : ℕ) (p : Piece (ckP .two) F T12 Unit W) : Prop :=
  p.ior.red.Leads
    (fun x => x.1.roots = n ∧ (FirstOpens π num no base x.1 ∧ PayRec π x.1))
    (fun x _ => QN π (NTuple F π no rad rd) x) p.err

/-- The second arm's form. -/
def GameAtO {W : Type} (F : Frame) (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ) (rad : Sg → ℕ)
    (rd : ℕ → ℕ) (base n : ℕ) (p : Piece (ckP .two) F T12 Unit W) : Prop :=
  p.ior.red.Leads
    (fun x => x.1.roots = n ∧ (FirstOpensOwn π num no base x.1 ∧ PayRec π x.1))
    (fun x _ => QN π (NTuple F π no rad rd) x) p.err

/-- The form is "has lost" over the piece's rounds at the piece's errors. -/
theorem gameAt_iff {W : Type} (F : Frame) (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ)
    (rad : Sg → ℕ) (rd : ℕ → ℕ) (base n : ℕ) (p : Piece (ckP .two) F T12 Unit W) :
    GameAt F π num no rad rd base n p ↔
      ∀ a : T12 × F.E.Str, a.1.roots = n ∧ (FirstOpens π num no base a.1 ∧ PayRec π a.1) →
        Doomed (uLT (ckP .two) p.ds) p.err fun τ =>
          ∀ b, p.ior.red.out a τ = some b → QN π (NTuple F π no rad rd) a :=
  Iff.rfl

/-- For every reduction: "has lost towards: a yes gives R of the statement in front" is "where R
fails of the statement in front, has lost towards a refusal". -/
theorem leads_iff_refuses {A B : Type} {K : Reduction A B} {on R : A → Prop} {ε : Err K.shape} :
    K.Leads on (fun a _ => R a) ε ↔
      ∀ a, on a → ¬ R a → Doomed K.shape ε fun τ => K.out a τ = none := by
  constructor
  · intro h a ha hn
    refine Doomed.mono _ _ (fun τ hτ => ?_) (h a ha)
    cases hb : K.out a τ with
    | none => rfl
    | some b => exact absurd (hτ b hb) hn
  · intro h a ha
    by_cases hR : R a
    · exact Doomed.of_forall _ _ fun _ _ _ => hR
    · exact Doomed.mono _ _ (fun τ hτ b hb => by rw [hτ] at hb; cases hb) (h a ha hR)

/-! ## 2 The game at the block's own record -/

/-- **THE GAME, FIRST ARM.** -/
def K12Game : Prop :=
  ∀ (F : Frame) (W : Type) (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ)
    (L mC mS mW : Sg → ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) (base : ℕ) (dB : RDT) (dt : List RDT)
    (ext : T12 × F.E.Str → Iop.Tr (uLT (ckP .two) (dB :: dt)) → W → W) (e : ℕ)
    (εt : Err (uLT (ckP .two) dt)) (n : ℕ) (r : Fmt.M1.Stage → ℕ),
    π.early = true → (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true →
    (π.nums.free = n → AtPlace F π num L mC mS mW rad base dB dt εt) →
    (∀ s, rad s = r s.st) → johOk π r = true → batOneOk π = true →
    batV0 π r * (bsRound .two dB.entry dB.kind).w ≤ e →
    GameAt F π num no rad rd base n
      (pieceOf (proximityTestKind guardedProximityTestParts π) base (dB :: dt) [] ⟨ext, (e, εt)⟩)

theorem k12_game : K12Game := by
  intro F W π num no L mC mS mW rad rd base dB dt ext e εt n r he hp hA hr hj hb1 hle a ha
  exact Doomed.mono_err _ ⟨hle, Err.le_refl _⟩
    (k12_lawRecFree F W π num no L mC mS mW rad rd base dB dt εt n he hp hA r hr hj hb1 a ha)

/-- **THE GAME, SECOND ARM.** -/
def K12GameO : Prop :=
  ∀ (F : Frame) (W : Type) (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ)
    (L mC mS mW : Sg → ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) (base : ℕ) (dB : RDT) (dt : List RDT)
    (ext : T12 × F.E.Str → Iop.Tr (uLT (ckP .two) (dB :: dt)) → W → W) (e v₀ : ℕ)
    (εt : Err (uLT (ckP .two) dt)) (n : ℕ),
    π.early = true → (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true →
    (π.nums.free = n → AtPlaceOwn F π num L mC mS mW rad base dB dt εt) →
    PayPub π rad dB.entry.rows v₀ → Fmt.dsOf dB.entry dB.kind = [.elem, .trits 0] →
    dB.entry.logN ≤ 64 → v₀ * (bsRound .two dB.entry dB.kind).w ≤ e →
    GameAtO F π num no rad rd base n
      (pieceOf (proximityTestKind guardedProximityTestParts π) base (dB :: dt) [] ⟨ext, (e, εt)⟩)

theorem k12_gameO : K12GameO := by
  intro F W π num no L mC mS mW rad rd base dB dt ext e v₀ εt n he hp hA hP h1 hlog hle a ha
  exact Doomed.mono_err _ ⟨hle, Err.le_refl _⟩
    (k12_lawRecFreeO F W π num no L mC mS mW rad rd base dB dt v₀ εt n he hp hA hP h1 hlog a ha)

/-! ## 3 The game at the first chain's finish of a description -/

/-- **THE GAME AT A DESCRIPTION**: `k12_F2_at`'s law (AtF2.lean) at the piece as the tiling makes
it: the seat on the chain's own state, any extractor, errors (e, εt). -/
def K12GameF2 : Prop :=
  ∀ {Xi : Type} (F : FileDescription Xi) (file : String) (D : WholeD), F.data file = .ok D →
    ∀ (key : ℕ → ℕ) (ft : ℕ) (W : Type) (π : P12) (no : ℕ → ℕ)
    (L mC mS mW : Sg → ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) (pre post : List Fmt.DeclaredRound)
    (r₀ : Fmt.DeclaredRound),
    F.roundsDeclaredByBlocks.1 = pre ++ ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds ++ (post ++ [r₀])) →
    ∀ (dB : RDT) (dt : List RDT) (εt : Err (uLT (ckP .two) dt)),
    dB :: dt = (D.ds₁.drop pre.length).take (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds.length →
    π.early = true → π.answers = 1 → (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true →
    spendOk π = true → CodesAt L mC mS mW rad π.nums.stages → π.nums.ownMask = false →
    ∀ (w0 : WR) (l : List WR), writtenOf π.nums = some (w0 :: l) →
    (∀ a rest w0 l (c : OnBytes.Slice.Chain (sgOf a)), π.nums.stages = a :: rest →
      writtenOf π.nums = some (w0 :: l) → chainFrom (.at L mC mS mW rad) rest a l = some c →
      Bears c.errL εt) →
    ∀ (r : Fmt.M1.Stage → ℕ), (∀ s, rad s = r s.st) → johOk π r = true → batOneOk π = true →
    ∀ (ext : First.S × (frameAt D (allOf D) key ft).E.Str →
        Iop.Tr (uLT (ckP .two) (dB :: dt)) → W → W) (e : ℕ),
    batV0 π r * (bsRound .two dB.entry dB.kind).w ≤ e →
    (pieceOf (C := ckP .two) (F := frameAt D (allOf D) key ft) (atFinish π)
        (0 + nTrees (D.ds₁.take pre.length)) (dB :: dt) [] ⟨ext, (e, εt)⟩).ior.red.Leads
      (fun x => ∀ fo, x.1.here = .fin fo → (recAt x.1 fo).roots = rootsOf pre ∧
        (FirstOpens π (numAt F.t₁ F.t₂ 0) no (0 + nTrees (D.ds₁.take pre.length)) (recAt x.1 fo) ∧
          PayRec π (recAt x.1 fo)))
      (fun x y => ∃ fo, x.1.here = .fin fo ∧ x.1.noneWaits = true ∧ x.1.failed.isNone = true ∧
        QN π (NTuple (frameAt D (allOf D) key ft) π no rad rd) (recAt x.1 fo, x.2) ∧
        ∃ st book roots, y.1 = { x.1 with st := st, book := book, roots := roots })
      (e, εt)

theorem k12_gameF2 : K12GameF2 := by
  intro Xi F file D h key ft W π no L mC mS mW rad rd pre post r₀ e' dB dt εt hcons early answers
    planOk spend codes ho w0 l hw bears r hr hj hb1 ext e hle a ha
  exact Doomed.mono_err _ ⟨hle, Err.le_refl _⟩
    (k12_F2_at F file D h key ft W π no L mC mS mW rad rd pre post r₀ e' dB dt εt hcons early
      answers planOk spend codes ho w0 l hw bears r hr hj hb1 a ha)

/-! ## 4 What the game is spent on: the one row that is owed of words_are_committed -/

section
variable (cs : OnBytes.Codes) {Xi : Type} (G : FileDescription Xi) {A Cells Tok : Type} (arr : ℕ → ℕ → ℕ)
  (smp : A → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  {C : PQ.CK} {Fr : Frame} {Cl : Type}

/-- A tool, for every piece: from a law "has lost towards: a yes gives R of the statement in front"
to `TestGivesCand`. hon: the row's promises give the law's. hkeep: a yes hands on the promise
behind. hseam: R gives one tuple of candidates of which the row's ins hold. -/
theorem cand_of_leads (p : Piece C Fr A Cl (Wit Cells Tok MsgT)) (mine : List Mem)
    (on on' : A × Fr.E.Str → Prop) (ins outs : A × Fr.E.Str → Wit Cells Tok MsgT → Prop)
    (onK R : A × Fr.E.Str → Prop)
    (hg : p.ior.red.Leads onK (fun a _ => R a) p.err)
    (hon : ∀ a, on a → Promised cs G smp mine a.1 (strsOf Fr a.2) → onK a)
    (hkeep : ∀ a τ b, on a → Promised cs G smp mine a.1 (strsOf Fr a.2) →
      p.ior.red.out a τ = some b → on' b)
    (hseam : SeatsFit cs G mine → Fenced p.base mine →
      ∀ a, on a → Promised cs G smp mine a.1 (strsOf Fr a.2) → R a → ∀ b w, outs b w →
        ∃ c : (x : Mem) → ((sigOf cs x.1.l).om x.2).Msg,
          (∀ x ∈ mine, CandAt cs G smp x a.1 (strsOf Fr a.2) (c x)) ∧
            ∀ w', LaidBy cs arr mine c w w' → ins a w') :
    TestGivesCand cs G arr smp p mine on on' ins outs := by
  intro hS hF a ha hp
  exact Doomed.mono _ _
    (fun τ hτ b hb => ⟨hkeep a τ b ha hp hb, fun w hw => hseam hS hF a ha hp (hτ b hb) b w hw⟩)
    (hg a (hon a ha hp))

end

section
variable (cs : OnBytes.Codes) {Xi : Type} (G : FileDescription Xi) {Cells Tok : Type} (arr : ℕ → ℕ → ℕ)
  (smp : T12 → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)

/-- **The seams of letters, in one statement**: where the seats fit, the members are fenced and the
row's promises hold: the kind's own "one tuple for all rows" gives one tuple of candidates IN THE
ROW's LETTERS, of which the row's ins hold. No challenge, no count, no error stands in it. -/
def K12Seams (F : Frame) (π : P12) (no : ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) (base : ℕ)
    (mine : List Mem) (on : T12 × F.E.Str → Prop)
    (ins outs : T12 × F.E.Str → Wit Cells Tok MsgT → Prop) : Prop :=
  SeatsFit cs G mine → Fenced base mine →
    ∀ a, on a → Promised cs G smp mine a.1 (strsOf F a.2) → QN π (NTuple F π no rad rd) a →
      ∀ b w, outs b w →
        ∃ c : (x : Mem) → ((sigOf cs x.1.l).om x.2).Msg,
          (∀ x ∈ mine, CandAt cs G smp x a.1 (strsOf F a.2) (c x)) ∧
            ∀ w', LaidBy cs arr mine c w w' → ins a w'

/-- **THE ONE ROW THAT IS OWED, AT THE PROXIMITY TEST's PIECE, WITH THE GAME PAID** (first arm). -/
theorem k12_testGivesCand (F : Frame) (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ)
    (rad : Sg → ℕ) (rd : ℕ → ℕ) (base n : ℕ) (p : Piece (ckP .two) F T12 Unit (Wit Cells Tok MsgT))
    (hb : p.base = base) (hg : GameAt F π num no rad rd base n p) (mine : List Mem)
    (on on' : T12 × F.E.Str → Prop) (ins outs : T12 × F.E.Str → Wit Cells Tok MsgT → Prop)
    (hon : ∀ a, on a → Promised cs G smp mine a.1 (strsOf F a.2) →
      a.1.roots = n ∧ (FirstOpens π num no base a.1 ∧ PayRec π a.1))
    (hkeep : ∀ a τ b, on a → Promised cs G smp mine a.1 (strsOf F a.2) →
      p.ior.red.out a τ = some b → on' b)
    (hseam : K12Seams cs G arr smp F π no rad rd base mine on ins outs) :
    TestGivesCand cs G arr smp p mine on on' ins outs :=
  cand_of_leads cs G arr smp p mine on on' ins outs _ _ hg hon hkeep (by rw [hb]; exact hseam)

end

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.gameAt_iff
#print axioms VerifiableInference.Desc.K12.Coin.leads_iff_refuses
#print axioms VerifiableInference.Desc.K12.Coin.k12_game
#print axioms VerifiableInference.Desc.K12.Coin.k12_gameO
#print axioms VerifiableInference.Desc.K12.Coin.k12_gameF2
#print axioms VerifiableInference.Desc.K12.Coin.cand_of_leads
#print axioms VerifiableInference.Desc.K12.Coin.k12_testGivesCand
