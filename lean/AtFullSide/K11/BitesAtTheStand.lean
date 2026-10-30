-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K11/BitesAtTheStand.lean: the five debts of the kind K11 speak at every stand. From the
thread's sentence at number 346 and a list of challenges that fits the member's rounds, where the
fall says nothing, the prover plays the member, the member's step accepts, and the items that the
row owes hold behind it.

  k11_no_stop_at_stand   the chain's stops say nothing at the member
  k11_steps_at_stand     the book's steps return at the member
  k11_bites              the end, at any thread over the base prover's sides and the first chain
  k11_bites_at_matrix    the same at the first thread with the written script at the matrices

Limits. That the thread's sentence holds at number 346 at any run is a premise here. The maker's
return, the head and the letter on what is said stay premises.
-/
import AtFullSide.K11.LendsAtTheTerm
import AtFullSide.K11.AtFirstScript

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtFullSide.K11
open VerifiableInference.Desc (Block Chain Place KindName)
open OnBytes.Maker (WholeD)
open OnBytes.HonestTrace (Sz)
open P5J (AtMgA TS)
open ProofFile.Honest
open ProofFile.Honest.K1 (firstScriptAt)
open ProofFile.Honest.K11
open ProofFile.Honest.FirstThread
open ProofFile.Honest.Term (matrixInput)
open AtPublicFiles.AtFiles
open AtPublicFiles.AtFiles.HonestTerm.K11Term
open Johnson.Desc.First.ForkMerge.Exchange (headMergeAtFull)

variable {W₀ : Type} {I : WiderIn W₀} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
  {Bs : ProofFile.PureBase}

/-- The member at number 346 stands at the kind's place. -/
theorem k11_member_place (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {blk : Block TS ProofFile.Cl}
    (hblk : cF.blocksInOrder[346]? = some blk) : blk.place = IM.k11Place := by
  obtain ⟨Bs', _, name, _, _, _, _, _, hf, _⟩ := headMergeAtFull Z D r Zp Np cF x h
  obtain rfl : blk = _ := Option.some.inj (hblk.symm.trans hf)
  rfl

/-- **At the member the chain's stops say nothing.** -/
theorem k11_no_stop_at_stand (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hM : baseMaker I Z = .ok A)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) {blk : Block TS ProofFile.Cl}
    (hblk : cF.blocksInOrder[346]? = some blk) (v : Option (Input W₀)) (loc ds : List Fmt.Drawn) :
    chainStopAt v [blk] A.H.first loc ds = none := by
  have hf : (A.H.first.find? fun q => q.place == blk.place) = some (k11Side (I.weights Zp) Zp Bs.G₀) := by
    rw [k11_member_place h hblk]
    exact k11_found h hM hB
  have hs := k11_no_stop (Rc := IndexCommitterCoins) (Tr := Cells) (X := Unit) (I.weights Zp) Zp Bs.G₀ v loc
    (ds.take blk.rounds.length)
  show ((A.H.first.find? fun q => q.place == blk.place).bind fun q =>
    rowStopAt v q.parts loc (ds.take blk.rounds.length)).or none = none
  rw [hf]
  show (rowStopAt v (k11Row (Rc := IndexCommitterCoins) (Tr := Cells) (X := Unit) (I.weights Zp) Zp Bs.G₀).half.parts
    loc (ds.take blk.rounds.length)).or none = none
  rw [hs]
  rfl

/-- **At the member the book's steps return**, at every view and every run's coins. -/
theorem k11_steps_at_stand (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hM : baseMaker I Z = .ok A)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) {blk : Block TS ProofFile.Cl}
    (hblk : cF.blocksInOrder[346]? = some blk) (v : Option (Input W₀)) (k : Coins A.B) :
    ∃ l, chainSteps A.B (A.B.rowsOf 0) (k.look 0) v [blk] A.H.first = .ok l := by
  have hpl := k11_member_place h hblk
  have hf : (A.H.first.find? fun q => q.place == blk.place) = some (k11Side (I.weights Zp) Zp Bs.G₀) := by
    rw [hpl]
    exact k11_found h hM hB
  exact k11_pays h hM (k11_alone_base h hM) _ (List.mem_of_find?_eq_some hf) rfl blk
    (List.mem_of_getElem? hblk) (hpl.trans (k11_place_is h hB).symm) A.H.first hf v k

/-- **The five speak at every stand**: at any thread over the base prover's sides and the first
chain, where the thread's sentence holds at 346, the challenges fit and the fall says nothing: the
member is played, its step accepts, and the items that the row owes hold behind it. -/
theorem k11_bites (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (hM : baseMaker I Z = .ok A)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)
    {T : Thread A.B TS ProofFile.Cl (Input W₀) (Input W₀) Unit ProofFile.Inst}
    {Said : Nat → Coins A.B → Mid (Input W₀) Unit → Prop}
    {fall : Nat → TS → List Fmt.Drawn → Option String} (hc : T.chain = 0) (hh : T.hs = A.H.first)
    (hbs : T.bs = cF.blocksInOrder) (F : FiveAtBorder T Said fall 346) {blk : Block TS ProofFile.Cl}
    (hblk : T.bs[346]? = some blk) {k : Coins A.B} {s : TS} {m : Mid (Input W₀) Unit} {E : Env}
    {ds : List Fmt.Drawn} (hT : ThrS T Said 346 k s m E) (hd : drawsFit blk.rounds ds = true)
    (hf : fall 346 s ds = none) :
    ∃ y cols s', T.Stepped blk k s m E ds y cols s' ∧
      T.Items (T.row 346).owes k s' y.2 (E.add y.1) := by
  have hblk' : cF.blocksInOrder[346]? = some blk := by
    rw [← hbs]
    exact hblk
  have hstop : chainStopAt (T.φ.sees m.st.input) [blk] T.hs m.loc ds = none := by
    rw [hh]
    exact k11_no_stop_at_stand h hM hB hblk' _ _ _
  obtain ⟨l, hl⟩ := k11_steps_at_stand h hM hB hblk' (T.φ.sees m.st.input) k
  have hl' : chainSteps A.B (A.B.rowsOf T.chain) (k.look T.chain) (T.φ.sees m.st.input) [blk] T.hs =
      .ok l := by
    rw [hc, hh]
    exact hl
  obtain ⟨y, cols, hMv, -⟩ := F.plays blk hblk k s m E ds l hT hd hstop hl'
  obtain ⟨s', hSt⟩ := F.accepted blk hblk k s m E ds y cols hT hd hstop hf hMv
  exact ⟨y, cols, s', hSt, F.exchange blk hblk k s m E ds y cols s' hT hd hSt⟩

/-- **The same at the first thread with the written script, at the online prover's index.** -/
theorem k11_bites_at_matrix {Z : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
    (hM : baseMaker matrixInput Z = .ok A) (hd : HeadAtReturn Z A) (numbers : FallNumbers)
    (w : Input FullSizeMatrix) (Said : Nat → Coins A.B → Mid (Input FullSizeMatrix) Unit → Prop)
    (hS : ∀ b k m, Said b k m → SaidOk b k m) (fall : Nat → TS → List Fmt.Drawn → Option String)
    {blk : Block TS ProofFile.Cl}
    (hblk : (firstThread hd ⟨firstScriptAt matrixInput Sz.ref openHonest A hd.firstChain, numbers⟩
      w).bs[346]? = some blk) {k : Coins A.B} {s : TS} {m : Mid (Input FullSizeMatrix) Unit} {E : Env}
    {ds : List Fmt.Drawn}
    (hT : ThrS (firstThread hd ⟨firstScriptAt matrixInput Sz.ref openHonest A hd.firstChain, numbers⟩
      w) Said 346 k s m E)
    (hds : drawsFit blk.rounds ds = true) (hf : fall 346 s ds = none) :
    ∃ y cols s',
      (firstThread hd ⟨firstScriptAt matrixInput Sz.ref openHonest A hd.firstChain, numbers⟩
        w).Stepped blk k s m E ds y cols s' ∧
      (firstThread hd ⟨firstScriptAt matrixInput Sz.ref openHonest A hd.firstChain, numbers⟩
        w).Items ((firstThread hd ⟨firstScriptAt matrixInput Sz.ref openHonest A hd.firstChain,
          numbers⟩ w).row 346).owes k s' y.2 (E.add y.1) := by
  obtain ⟨Bs, base, O⟩ := hd.head.laid.opened
  exact k11_bites hd.head hM O.made rfl rfl rfl (k11_five_at_matrix hM hd numbers w Said hS fall)
    hblk hT hds hf

end AtFullSide.K11

#print axioms AtFullSide.K11.k11_member_place
#print axioms AtFullSide.K11.k11_no_stop_at_stand
#print axioms AtFullSide.K11.k11_steps_at_stand
#print axioms AtFullSide.K11.k11_bites
#print axioms AtFullSide.K11.k11_bites_at_matrix
