-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K8/TieAtHead.lean: the honest side of the smallness test (K8): THE
FIELD tie OF `K8TwoAt` (Johnson/Desc/ProofFile/Honest/K8/ExchangeByKind.lean), IN ITS OWN FORM, AT
THE FIRST CHAIN's LETTERS AT THE LIBRARY's HEAD, AT EVERY SCRIPT: EXCHANGED FOR THREE PREMISES:
hopen (public: the item "tie l" is open at the draw's number), hsym (ON THE SCRIPT AND THE HIDDEN
INPUT: behind the draw's step the matrices' symbol arrays in the thread's witness's table are the
packing of the cells of the input's trace) AND hsmall (ON THE HIDDEN INPUT: these cells are small,
AT EVERY INDEX: no range is set, which is more than the law beneath takes). One theorem; no
definition.

`K8TwoAt.tie` is exchanged, not paid: hsym and hsmall are proved nowhere; hopen is shown by nobody
yet. Behind a yes at which the second stop is silent. hsym is an equation on the Script.
NOT IN FRONT OF A LAW OVER COINS. hsym and hsmall are premises ON THE HIDDEN INPUT:
in front of a sentence on hiding neither stands as a bare premise: there it is had from Vd, by name,
or the sentence says that its range is cut by a condition on the trace.

  **`tie_at_head`**
How. THE CLAUSE ON THE READS IS NOT ASKED OF THE SCRIPT A SECOND TIME. The thread's stand holds its
open items of the thread's witness (the fourth clause of `Thr`,
Johnson/Desc/ProofFile/Honest/Thread/Thr.lean); at these letters the item "tie l" says the library's
`TieAt` at the table `cellsAt`, by unfolding. `tieAt_ahead_iff`
(Johnson/Desc/First/K8/LawSmallAhead.lean) carries it to `cellsAhead`; its premises on the state:
`namedB_of_reach` (Johnson/P1K8R/NamedOfReach.lean) with `namesDoorB_at_head`, `fork_of_link`,
`cond_of_front` at `front_at_place`. The draw's yes turns two fields of the record that the tie does
not read, and no cell of the table (`cellsAhead_putTl`). Then `tieBy_of_tieOf`
(Johnson/Desc/ProofFile/Honest/K8/TieBack.lean): the item's small integers are the named ones in
range.
One option is raised (maxHeartbeats) and one instance is taken away, as in the files beneath. No
tactic that searches.
Limits. An implication. No letters are given at which the premises hold together. Counted nowhere.
`K8Seated` is a premise. That the thread stands at any of these numbers, at any prover, is not said:
where it stands at none, or the member takes no step there, all is idle. The full size alone.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.ExchangeByKind
import Johnson.Desc.ProofFile.Honest.K8.TieBack
import Johnson.Desc.First.K8.LawSmallAhead
import Johnson.P1K8R.NamedOfReach
import Johnson.HB.LLHARD.K8NamesDoorAtHead
import Johnson.HB.LLHARD.Q38A.ForkOfLink

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc
open VerifiableInference.Desc.Sound (MsgT cellsAt)
open VerifiableInference.Desc.First (S Item)
open VerifiableInference.Desc.First.K8 (TieAt cellsAhead cellsAhead_putTl tieAt_ahead_iff putTl_tl)
open VerifiableInference.Desc.First.K8.Ready (cond_of_front planFitsAllB)
open VerifiableInference.Desc.First.K8.Honest
open _root_.Desc.K14.Law (seatZ secondAt)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersHead WtF Script thrS_rchAt)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **The field tie at the head's letters, exchanged, not paid**: for hopen (public), hsym (on the
Script and the hidden input: the symbols' clause alone) and hsmall (on the hidden input, at every
index), each proved nowhere here; the head, the opening, the built segment, hOk and `K8Seated` stay
too. Behind a yes at which the second stop is silent.
NOT IN FRONT OF A LAW OVER COINS. -/
theorem tie_at_head {Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop}
    (hOk : ∀ b k m, Said b k m → SaidOk b k m) {l : ℕ} (hl : l < 25) {Bs : ProofFile.PureBase}
    {base₀ : List (Block S ProofFile.Cl)}
    (O₁ : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np))
    {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) {blk : Block S ProofFile.Cl} {cells : Tr → Cells}
    {mats : List (Nat × String × Nat)}
    (hK : K8Seated (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (14 * l + (if l = 24 then 5 else 4) + 2) blk cells (ProofFile.k8Par Zp Bs.G₀ Xl l, mats))
    (hopen : Item.tie l ∈ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.opened
      (14 * l + (if l = 24 then 5 else 4) + 2))
    (hsym : ∀ k s m E ds y cols s' tl' e (z : ProofFile.InstPub),
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
        (14 * l + (if l = 24 then 5 else 4) + 2) k s m E →
      drawsFit blk.rounds ds = true →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y
        cols s' →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Form
        (14 * l + (if l = 24 then 5 else 4) + 2 + 1) k s' y.2 →
      s'.tl? = some tl' →
      ∀ μ, μ < tl'.NM → ∀ c, c < (tl'.mats.getD μ {}).k →
        ∀ i', i' < Alg.symRows (tl'.mats.getD μ {}).m →
          cellsAhead h.𝔇.cs h.𝔇.arr h.𝔇.ms h.𝔇.N l (z, s')
              ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.wit k m.st.input
                (m.st.heard ++ e)) (tl'.gtTree.getD μ 0) i' c =
            ((Alg.pack ((radb : ℕ) : ℤ) (fun i : Fin (tl'.mats.getD μ {}).m =>
              cellsAtOf (cells m.st.input.trace) mats μ i c) i' : ℤ) : Cb.Gl.E))
    (hsmall : ∀ v, v = w ∧ Vd v → ∀ μ i c,
      |cellsAtOf (cells v.trace) mats μ i c| < 2 * ((2 ^ lbz : ℕ) : ℤ)) :
    ∀ k s m E ds y cols s' tl' e (z : ProofFile.InstPub),
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
        (14 * l + (if l = 24 then 5 else 4) + 2) k s m E →
      drawsFit blk.rounds ds = true →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y
        cols s' →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Form
        (14 * l + (if l = 24 then 5 else 4) + 2 + 1) k s' y.2 →
      s'.tl? = some tl' →
      TieBy tl'
        (cellsAhead h.𝔇.cs h.𝔇.arr h.𝔇.ms h.𝔇.N l (z, s')
          ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.wit k m.st.input
            (m.st.heard ++ e)))
        (cellsAtOf (cells m.st.input.trace) mats) := by
  intro k s m E ds y cols s' tl' e z hA hd hS hF ht
  have hx : ((l, if l = 24 then 5 else 4) : ℕ × ℕ) ∈ P1K8S.places :=
    List.mem_map.2 ⟨l, List.mem_range.2 hl, rfl⟩
  have hr0 := thrS_rchAt h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w ()
    (Nat.le_of_lt (List.getElem?_eq_some_iff.1 hK.here).1) ⟨hA.1, hOk _ _ _ hA.2⟩
  -- the open item at the stand
  have hTA : TieAt (cellsAt h.𝔇.cs h.𝔇.arr h.𝔇.ms h.𝔇.N l (m.st.input.x.pub, s)) s
      ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.wit k m.st.input
        (m.st.heard ++ e)) := hA.1.2.2.2.1 e (Item.tie l) hopen
  -- the state in front of the draw
  obtain ⟨tlN, Lk, htN, hLk, hN⟩ := P1K8S.namedB_of_reach h.scope h.reads O₁ h.laid.planOk
    (P5J.namesDoorB_at_head h) hx e3 ((m.st.input.x.pub, s), ()) hr0
  obtain ⟨Fk, hFk⟩ := Q38.fork_of_link s Lk hLk
  obtain ⟨-, -, -, -, s₀, cols₀, hbeg, -, hfold⟩ := hA.1.2.2.2.2.1
  have e0 : s₀ = ProofFile.startS Zp m.st.input.x.pub := hbeg
  rw [e0] at hfold
  have hW : planFitsAllB Bs.G₀.W = true := by
    rw [O₁.W]
    exact h.k8_planFits
  obtain ⟨tlF, htF, -, -, hgt, hu⟩ := cond_of_front
    (P1K8S.front_at_place h.scope h.reads O₁ (P1K8S.planFitsAll_of_test hW) hx _ _ _ _ hfold)
  obtain rfl : tlN = tlF := Option.some.inj (htN.symm.trans htF)
  obtain ⟨tl₂, ht₂, hTO⟩ := (tieAt_ahead_iff h.𝔇.cs h.𝔇.arr h.𝔇.ms h.𝔇.N l m.st.input.x.pub s hLk
    hFk htN hN hgt hu _).2 hTA
  obtain rfl : tlN = tl₂ := Option.some.inj (htN.symm.trans ht₂)
  -- behind the draw's yes
  obtain ⟨tl, cf, first, h1, -, -, -, -, es⟩ := keeps_of_stepped hK hS
  obtain rfl : tlN = tl := Option.some.inj (htN.symm.trans h1)
  have et : tl' = { tlN with cfF := cf, cfFirst := first } := by
    rw [es, putTl_tl s tlN _ htN] at ht
    exact (Option.some.inj ht).symm
  have eA : (cellsAhead h.𝔇.cs h.𝔇.arr h.𝔇.ms h.𝔇.N l (z, s') : WtF → ℕ → ℕ → ℕ → Cb.Gl.E) =
      cellsAhead h.𝔇.cs h.𝔇.arr h.𝔇.ms h.𝔇.N l (m.st.input.x.pub, s) := by
    funext W
    rw [es, cellsAhead_putTl h.𝔇.cs h.𝔇.arr h.𝔇.ms h.𝔇.N l z s tlN _ htN W]
    rfl
  refine tieBy_of_tieOf tl' _ _ ?_ (hsym k s m E ds y cols s' tl' e z hA hd hS hF ht)
    (fun μ _ c _ i _ => hsmall m.st.input hA.1.2.2.2.2.2.2 μ i c)
  rw [eA, et]
  exact hTO

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.tie_at_head
