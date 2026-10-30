-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LPFPol/DescAtPolicy.lean: the proof file's description (`ProofFile.onlineDescription`) at a parameter file
with another acceptance policy: it returns where it returned, and its plan part is the same.
Statements and proofs.
Premises: hX, hX': `publicOfO` returns X at the first parameter file and `X.withPol C theta cap` at
the second; hH: `HeadSame X C theta cap` (Johnson/LPFPol/Lots.lean): the two tests on the plan of
the output head's own block do not move.
  `SameDesc F' F`: one verdict of the tests on the plan; the same declared rounds; the same depth of
      the stored table; the same rows of the cut, chain by chain.
  `blankBy_wp`, `baseOf_wp`: the segments' records for a request of zeros, and the maker's base.
  `fileDescBy_same`: two records `fileDescBy` over first chains with one list of skeletons.
  `descPure_wp`: THE STATEMENT OF THIS FILE.
Limits. The three premises are not paid here. F' and F are not shown to be one description: the
output head's own block holds the policy in its decision and in its claims. Nothing is said on what
either decides. Nothing on soundness.

-/
import Johnson.LPFPol.Lots
import Johnson.LPFPol.BackSame
import Johnson.LPFPol.PubPlain
import Johnson.LPFPol.SkelReads
import Johnson.Desc.ProofFile.Law.PureMade

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace LPFPol
open LPFPol.SkR ProofFile
open OnBytes OnBytes.Model
open OnBytes.Params (exc_bind)
open ProofFile.Law (exBind_ok orSay_ok descPure_parts)
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.PlanWritten (publicOfO cutOf)

/-- The plan part of two descriptions is one. -/
structure SameDesc (F' F : FileDescription ProofFile.Inst) : Prop where
  planOk : F'.planOk = F.planOk
  decl : F'.roundsDeclaredByBlocks = F.roundsDeclaredByBlocks
  depth : F'.tableDepth = F.tableDepth
  cut₁ : cutOf F'.first.blocksInOrder = cutOf F.first.blocksInOrder
  cut₂ : cutOf F'.shared.blocksInOrder = cutOf F.shared.blocksInOrder
  cut₃ : cutOf F'.second.blocksInOrder = cutOf F.second.blocksInOrder

theorem lettersBy_wp (Z : Pub) (pol' : ByteArray) (C theta cap : Nat) (s : S) {G : Ground}
    (h : lettersBy pureRoad.links Z s = .ok G) :
    lettersBy pureRoad.links (wpZ Z pol' C theta cap) s = .ok (wpG G C theta cap) ∧ G.W =
        Z.p.X := by
  unfold lettersBy at h ⊢
  dsimp only at h ⊢
  by_cases hc : s.out.reply.isNone = true
  · rw [if_pos hc] at h ⊢
    obtain ⟨cov, hcov, h⟩ := exc_bind h
    obtain ⟨links, hl, h⟩ := exc_bind h
    cases h
    refine ⟨?_, rfl⟩
    refine (bind_ok (a := cov) hcov).trans ?_
    refine (bind_ok (a := links) hl).trans ?_
    rfl
  · rw [if_neg hc] at h ⊢
    obtain ⟨cov, hcov, h⟩ := exc_bind h
    obtain ⟨links, hl, h⟩ := exc_bind h
    cases h
    refine ⟨?_, rfl⟩
    refine (bind_ok (a := cov) hcov).trans ?_
    refine (bind_ok (a := links) hl).trans ?_
    rfl

theorem blankBy_wp (Z : Pub) (pol' : ByteArray) (C theta cap : Nat) {G : Ground}
    (h : blankBy pureRoad.links Z = some G) :
    blankBy pureRoad.links (wpZ Z pol' C theta cap) = some (wpG G C theta cap) ∧ G.W = Z.p.X := by
  unfold blankBy at h ⊢
  dsimp only at h ⊢
  cases e : lettersBy pureRoad.links Z (Z.s₀.withReq (Array.replicate Z.p.X.T 0 ++ #[0, 1])) with
  | error w =>
    rw [e] at h
    cases h
  | ok G0 =>
    rw [e] at h
    obtain rfl : G0 = G := Option.some.inj h
    obtain ⟨g1, g2⟩ := lettersBy_wp Z pol' C theta cap _ e
    refine ⟨?_, g2⟩
    show (lettersBy pureRoad.links (wpZ Z pol' C theta cap)
      (Z.s₀.withReq (Array.replicate Z.p.X.T 0 ++ #[0, 1]))).toOption = _
    rw [g1]
    rfl

theorem baseOf_wp (o : SecondHashFunctionArgument) (Z : Pub) (pol' : ByteArray) (C theta cap : Nat) {B : PureBase}
    (h : baseOf Z (pureSeat o Z) = .ok B) :
    ∃ B', baseOf (wpZ Z pol' C theta cap) (pureSeat o (wpZ Z pol' C theta cap)) = .ok B' ∧
      B'.spots = B.spots ∧ B'.shape = B.shape ∧ B'.batchAt = B.batchAt ∧
      B'.G₀ = wpG B.G₀ C theta cap ∧
      (B'.all = (pureSeat o (wpZ Z pol' C theta cap)).lots.map fun L => (L, L.blocks B'.G₀)) ∧
      (B.all = (pureSeat o Z).lots.map fun L => (L, L.blocks B.G₀)) ∧ B.G₀.W = Z.p.X := by
  unfold baseOf at h
  obtain ⟨ps, h1, h⟩ := exBind_ok h
  obtain ⟨sh, h2, h⟩ := exBind_ok h
  obtain ⟨G, h3, h⟩ := exBind_ok h
  obtain rfl := Except.ok.inj h
  obtain ⟨g1, g2⟩ := blankBy_wp Z pol' C theta cap (orSay_ok h3)
  refine ⟨PureBase.mk ps sh (wpG G C theta cap)
      ((pureSeat o (wpZ Z pol' C theta cap)).lots.map fun L => (L, L.blocks (wpG G C theta cap)))
      ((subsOf Z).zipIdx.map fun x =>
        (x.2, ⟨1, some x.2, (VerifiableInference.Desc.First.kindsBeforeBatching x.1 (x.2 == 0)).length + 1,
          VerifiableInference.Desc.KindName.K9⟩)), ?_, rfl, rfl, rfl, rfl, ?_, ?_, g2⟩
  rotate_left
  · rfl
  · rfl
  unfold baseOf
  show (orSay _ (spotsOf Z.cuts)).bind _ = _
  rw [h1]
  show (shapeOf Z).bind _ = _
  rw [h2]
  show (orSay _ (blankBy pureRoad.links (wpZ Z pol' C theta cap))).bind _ = _
  rw [g1]
  rfl

/-- Two records over first chains with one list of skeletons. -/
theorem fileDescBy_same (o : SecondHashFunctionArgument) (mk : LinksBy) (Z Z' : Pub) (A : SharedSeat)
    (B : SecondSeat)
    (st st' : InstPub → S) (c c' : Chain S Cl) (hD : Z'.D = Z.D) (hd : Z'.depth = Z.depth)
    (hm : Z'.p.chains.made = Z.p.chains.made) (h : SameSk c'.blocksInOrder c.blocksInOrder) :
    SameDesc (fileDescBy o mk Z' A B (fun s => s) st' c')
        (fileDescBy o mk Z A B (fun s => s) st c) := by
  have eDecl : (fileDescBy o mk Z' A B (fun s => s) st' c').roundsDeclaredByBlocks =
      (fileDescBy o mk Z A B (fun s => s) st c).roundsDeclaredByBlocks := by
    show (c'.blocksInOrder.flatMap (·.rounds), _, _) = (c.blocksInOrder.flatMap (·.rounds), _, _)
    rw [h.rounds]
    rfl
  have eRoots : (fileDescBy o mk Z' A B (fun s => s) st' c').roots =
      (fileDescBy o mk Z A B (fun s => s) st c).roots := by
    show [VerifiableInference.Desc.oraclesOf c'.blocksInOrder, _, _] =
        [VerifiableInference.Desc.oraclesOf c.blocksInOrder, _, _]
    rw [h.oracles]
    rfl
  have ePlaces : (fileDescBy o mk Z' A B (fun s => s) st' c').places =
      (fileDescBy o mk Z A B (fun s => s) st c).places := by
    show VerifiableInference.Desc.placesOf c'.blocksInOrder ++ _ ++ _ =
        VerifiableInference.Desc.placesOf c.blocksInOrder ++ _ ++ _
    rw [h.places]
    rfl
  have eFile : (fileDescBy o mk Z' A B (fun s => s) st' c').fileOk =
      (fileDescBy o mk Z A B (fun s => s) st c).fileOk := by
    show (A.fileOk && B.fileOk && VerifiableInference.Desc.proofOk Z'.p.chains.made &&
      Johnson.Desc.Ok.everyOk Z'.p.chains.made) = _
    rw [hm]
    rfl
  have eLabels : (fileDescBy o mk Z' A B (fun s => s) st' c').labelsOk =
      (fileDescBy o mk Z A B (fun s => s) st c).labelsOk := by
    unfold FileDescription.labelsOk FileDescription.lastChainFirstTreeNumber
    rw [eDecl]
  have ePl : (fileDescBy o mk Z' A B (fun s => s) st' c').placesOk =
      (fileDescBy o mk Z A B (fun s => s) st c).placesOk := by
    unfold FileDescription.placesOk
    rw [ePlaces]
    show (_ && _ && _ && _) = (_ && _ && _ && _)
    rw [show VerifiableInference.Desc.placesOf
        (fileDescBy o mk Z' A B (fun s => s) st' c').first.blocksInOrder =
      VerifiableInference.Desc.placesOf (fileDescBy o mk Z A B (fun s => s) st c).first.blocksInOrder from
          h.places]
    rfl
  have eBefore : (fileDescBy o mk Z' A B (fun s => s) st' c').beforeOk =
      (fileDescBy o mk Z A B (fun s => s) st c).beforeOk := by
    unfold FileDescription.beforeOk
    rw [eDecl]
    show (VerifiableInference.Desc.beforeAt _ (VerifiableInference.Desc.oraclesOf c'.blocksInOrder, _, _) 0 0
        c'.blocksInOrder &&
      VerifiableInference.Desc.beforeAt _ (VerifiableInference.Desc.oraclesOf c'.blocksInOrder, _, _) 1 0
          _ &&
      VerifiableInference.Desc.beforeAt _ (VerifiableInference.Desc.oraclesOf c'.blocksInOrder, _, _) 2 0
          _) = _
    rw [h.oracles, SameSk.before _ _ 0 h 0]
    rfl
  have eBook : (fileDescBy o mk Z' A B (fun s => s) st' c').treeSharingOk =
      (fileDescBy o mk Z A B (fun s => s) st c).treeSharingOk := by
    unfold FileDescription.treeSharingOk
    rw [eDecl, eRoots]
  have eReads : (fileDescBy o mk Z' A B (fun s => s) st' c').readsOk =
      (fileDescBy o mk Z A B (fun s => s) st c).readsOk := by
    unfold FileDescription.readsOk
    rw [eDecl]
  have eSent : (fileDescBy o mk Z' A B (fun s => s) st' c').sentFit =
      (fileDescBy o mk Z A B (fun s => s) st c).sentFit := by
    unfold FileDescription.sentFit
    rw [eDecl]
    show ([VerifiableInference.Desc.sentOf c'.blocksInOrder, _, _].zipIdx.all _) = _
    rw [h.sent]
    rfl
  have eSeal : (fileDescBy o mk Z' A B (fun s => s) st' c').sealLast =
      (fileDescBy o mk Z A B (fun s => s) st c).sealLast := by
    show (!c'.last.rounds.isEmpty) = (!c.last.rounds.isEmpty)
    rw [last_same h]
  refine ⟨?_, eDecl, hd, h.cut, rfl, rfl⟩
  have eBlocks : VerifiableInference.Desc.blocksOk
      (fileDescBy o mk Z' A B (fun s => s) st' c').first.blocksInOrder =
      VerifiableInference.Desc.blocksOk (fileDescBy o mk Z A B (fun s => s) st c).first.blocksInOrder :=
          h.blocksOk
  have ePlans : (fileDescBy o mk Z' A B (fun s => s) st' c').plans =
      (fileDescBy o mk Z A B (fun s => s) st c).plans := hD
  have eDepth : (fileDescBy o mk Z' A B (fun s => s) st' c').tableDepth =
      (fileDescBy o mk Z A B (fun s => s) st c).tableDepth := hd
  unfold FileDescription.planOk FileDescription.planOkCore
  rw [eFile, eBlocks, eDecl, ePlans, eDepth, eLabels, ePl, eBefore, eBook, eReads, eSent, eSeal]
  rfl

/-- **The description at the other policy.** -/
theorem descPure_wp {o : SecondHashFunctionArgument} {pol pol' lay KL : ByteArray} {X : Verify.Public}
    {C theta cap : Nat}
    (hX : publicOfO o pol KL (some lay) = .ok X)
    (hX' : publicOfO o pol' KL (some lay) = .ok (X.withPol C theta cap))
    (hH : HeadSame X C theta cap) {F : FileDescription ProofFile.Inst} (hF : onlineDescription o pol lay KL = .ok F) :
    ∃ F', onlineDescription o pol' lay KL = .ok F' ∧ SameDesc F' F := by
  obtain ⟨Z, B, base, c, A, B2, hZ, hB, hf, hl, hb, hc, hA, hB2, rfl⟩ := descPure_parts hF
  have hZ' : pureRoad.pub o pol' lay KL = .ok (wpZ Z pol' C theta cap) := pubPlain_wp hX hX' hZ
  have eX : Z.p.X = X := pubPlain_X hX hZ
  obtain ⟨B', hB', e1, e2, e3, eG, hall', hall, eW⟩ := baseOf_wp o Z pol' C theta cap hB
  have hH' : HeadSame B.G₀.W C theta cap := by rw [eW, eX]; exact hH
  have ek : (pureSeat o (wpZ Z pol' C theta cap)).lots.map (lotSk B'.G₀) =
      (pureSeat o Z).lots.map (lotSk B.G₀) := by
    rw [eG]
    exact lots_same Z B.G₀ pol' C theta cap hH'
  obtain ⟨f', l', base', hb', -, c', hc', hsk⟩ :=
    back_same Z (wpZ Z pol' C theta cap) (pureSeat o Z) (pureSeat o (wpZ Z pol' C theta cap)) B B'
        hall hall'
      (steady_pure Z B.G₀) (steady_pure _ B'.G₀) e1 e2 e3 rfl ek rfl rfl hf hl hb hc
  refine ⟨fileDescBy o pureRoad.links (wpZ Z pol' C theta cap) A B2 (fun s => s)
    (startS (wpZ Z pol' C theta cap)) c', ?_, fileDescBy_same _ _ _ _ _ _ _ _ _ _ rfl rfl rfl hsk⟩
  show (pureRoad.pub o pol' lay KL).bind (fun Z => onlineDescriptionFromPublicPart Z (pureSeat o Z)) = _
  rw [hZ']
  show onlineDescriptionFromPublicPart (wpZ Z pol' C theta cap) (pureSeat o (wpZ Z pol' C theta cap)) = _
  unfold onlineDescriptionFromPublicPart
  rw [hB']
  show (if _ then _ else if _ then _ else onlineDescriptionAfterTests _ _ _) = _
  rw [f', l']
  show onlineDescriptionAfterTests _ _ _ = _
  unfold onlineDescriptionAfterTests
  rw [hb']
  show (chainBy _ base' _ _).bind _ = _
  rw [hc']
  show (match onlineSharedChain Z, onlineLastChain Z with
    | some A, some B => _
    | _, _ => _) = _
  rw [hA, hB2]
  rfl

end LPFPol

#print axioms LPFPol.fileDescBy_same
#print axioms LPFPol.descPure_wp
