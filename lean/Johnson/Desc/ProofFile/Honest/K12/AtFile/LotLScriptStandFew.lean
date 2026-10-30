-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LotLScriptStandFew.lean

It states no goal. No property of the protocol is claimed.

THE TIE OF THE WORDS AT A STAND IN
FRONT OF THE CLOSING PROXIMITY TEST (`wordsTied_at_closing_stand`, LotLScriptStand.lean), WITH FEWER
PREMISES, AT THE SIZE Sz.ref. One statement with its proof: calls.

  `wordsTied_at_closing_stand_few`   hok and hpub are paid by `closing_premises_at_finish`
      (LotLPublicClosing.lean)

Hypotheses left. h: the head. hA: the maker returns A at the base prover's filling AT Sz.ref. hf: pl
is the finish (there is one: `finish_at_base`, AtFullSide/K1/FirstScript.lean). hc: the closing's
public test says yes at every place of the plan: the statement of closing_at_head
(K2/Law/ClosingAtHead.lean; not imported). hstart: a valid input's instance passes
the description's test okStart. hReach: as in LotLScriptStand.lean. hbook: the public test on the book
`wordsBookB` (ClosingWordsBook.lean) says yes at the maker's book, at the finish's
part and the test's second part: it pays hcarry by `carryRows_at_row_coins` (LotLOwedLent.lean).

Limits. Those of LotLScriptStand.lean. At Sz.ref alone. Nothing on completeness, soundness or hiding.

NOT IN FRONT OF A LAW OVER COINS: `wordsTied_at_closing_stand_few` bears this label; the rule is at
its home, the head of Johnson/Bind/ForProver/FiveFieldsAt.lean.
This file's own ground, in the rule's terms.
- h and hA speak of the public files, of the letters I and Op (how an index, an instance and the
  challenges are read, and one named member of the index's type) and of what the maker returns at
  the filling made of them. By their text they name no coin, no run's input (its index, its trace)
  and no Script: of neither kind.
- hf, hc and hbook speak of the finish, of the closing's public test and of the book's entries: they
  name no coin. hstart is bound over every input that meets Vd and reads its instance: it names no
  coin.
- hReach is itself bound over all coins and every stand: by itself it picks among no coins.
- w, the run's input, is a letter under no premise in front. It holds the committer's coins (its
  field rc) and the hidden input (its fields w₀ and trace).
- A run's coins k are bound inside the end. Beside k it binds the letters st, m and E (the
  verifier's state, the state of the prover's side, the available tables) under `ThrS … 354 k st m
  E`: a premise of the first kind: it names k; by its text, at fixed st, m and E it can hold at some
  values of the coins and fail at others.
- The end binds besides c under `lendRow … (k.look …) … = .ok c` and Rr under `carryRows …
  (restCoins J' c.2.1).mem = .ok Rr`: of the first kind. J' under its equation, the record R under
  `enterFinish st = .ok R` and G under `R.st.groups[R.g]? = some G` name no coin.
- One clause of the invariant says that the input of m is w and meets Vd, a letter for a predicate
  on the input: what it reads of the input is not fixed here.
- The thread's other letters (test, carryX, item, n₁, n₂, b₀, Vd, Rd, Kp, Said) stand under no
  premise in front that names a coin; the invariant reads them. The Script is no letter: it is the
  term `firstScriptAt`.
- What lifts the bar. For c and Rr the made terms are what `lendRow` and `carryRows` return:
  `carryRows_returns_at_input` (LReturnsClosing.lean) shows, from the head, the ground and the
  finish, at the rows of `Sz.ref` and at every input whose instance passes the description's test,
  that the second returns whatever is lent. For st, m and E the made terms would be those of the
  honest run at the border, as terms of w, k and the challenges, and the lemma would show the
  premises at them at every value of the coins. None is known to this file: so the bar is flat.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLScriptStand
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLPublicClosing
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLOwedLent

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace ProofFile.Honest.K12.LotL
open VerifiableInference.Desc (Chain Place Strs)
open VerifiableInference.Desc.K12 (T12 enterFinish)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (below wordsFirst)
open Johnson.Desc.First.Walk.Tied (Reach)
open OnBytes.Means (layoutOf)
open OnBytes.HonestTrace (Sz)
open ProofFile.Honest.FirstThread (lettersHead WtF)
open ProofFile.Honest.K1 (LocB firstScriptAt readersB)
open ProofFile.Honest.K2 (SwitchPlace)
open ProofFile.Honest.K2.Law (SwitchCoins)
open ProofFile.Honest.K12.Light (WordsTied)
open ProofFile.Honest.K12.AtProof (plainL finishAt jobL doorAtL heardL ClosingAtEveryPlace
  closing_premises_at_finish carryRows_at_row_coins finish_two_messages)
open P5J (AtMgA TS)

variable {W₀ : Type} {Z : VerifierAndGoals.PublicFiles} {I : WiderIn W₀} {Op : OnlineProverArguments}
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- hc, hstart, hReach AND hbook ARE PREMISES. **THE TIE OF THE WORDS AT A STAND IN FRONT OF THE
CLOSING PROXIMITY TEST, AT Sz.ref.** -/
theorem wordsTied_at_closing_stand_few (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction Sz.ref Op) =
      .ok A)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : LocB W₀ → Prop) (Rd : Nat → LocB W₀ → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : LocB W₀)
    (Said : ℕ → Coins A.B → Mid (LocB W₀) Unit → Prop)
    {pl : SwitchPlace} (hf : finishAt A.Z A.G = some pl)
    (hc : ClosingAtEveryPlace Z A.Z Np cF)
    (hstart : ∀ v, Vd v → (P5J.F0T OnBytes.secondHashFunction A.Z Np cF).okStart v.x = true)
    (hReach : ∀ k st m E, ThrS (lettersHead h A.H (firstScriptAt I Sz.ref Op A cF) test carryX item
        n₁ n₂ b₀ Vd Rd Kp w).thread Said 354 k st m E →
      Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS A.Z) 354 (m.st.input.x.pub, st))
    (hbook : AtProof.wordsBookB A.B ⟨pl.place, 0⟩ ⟨(H2U.p12OfMade A.Z.made).place, 1⟩
      pl.front.length = true) :
    ∀ k st m E R (J' : TestJob (LocB W₀) Unit),
      J' = atStand (jobL (H2U.p12OfMade A.Z.made) (doorAtL A.Z) (widerRows Sz.ref A.Z A.G)
        (readersB I A.Z) (K2.lotClosingAt A.G.first.layout (K2.segmentsOf A.Z A.G)) pl) m.st.input
        (frontOf m) R →
      ∀ c : RowCoins [(firstPart J' : Part (LocB W₀) (LocB W₀) Unit), restPart J'],
      ThrS (lettersHead h A.H (firstScriptAt I Sz.ref Op A cF) test carryX item n₁ n₂ b₀ Vd Rd Kp
        w).thread Said 354 k st m E →
      enterFinish st = .ok R →
      lendRow A.B (A.B.rowsOf (lettersHead h A.H (firstScriptAt I Sz.ref Op A cF) test carryX item
          n₁ n₂ b₀ Vd Rd Kp w).thread.chain)
        (k.look (lettersHead h A.H (firstScriptAt I Sz.ref Op A cF) test carryX item n₁ n₂ b₀ Vd Rd
          Kp w).thread.chain) J'.p.place
        [(firstPart J' : Part (LocB W₀) (LocB W₀) Unit), restPart J'] 0 = .ok c →
      ∀ Rr : Johnson.Prover.Send.Rows,
      AtProof.carryRows (widerRows Sz.ref A.Z A.G) (readersB I A.Z)
        (K2.lotClosingAt A.G.first.layout (K2.segmentsOf A.Z A.G)) pl m.st.input
        (heardL (frontOf m)) (restCoins J' c.2.1).mem = .ok Rr →
      ∀ G, R.st.groups[R.g]? = some G →
      WordsTied R.st R.g G
        (wordsFirst (P5J.At.arr A.Z) st.st st.book
          ((lettersHead h A.H (firstScriptAt I Sz.ref Op A cF) test carryX item n₁ n₂ b₀ Vd Rd Kp
            w).thread.wit k m.st.input (m.st.heard ++ [])))
        (layoutOf R.st G) (plainL Rr (J'.first m.st.input (frontOf m) (restCoins J' c.2.1))) := by
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  obtain ⟨-, eG, -⟩ := atPure_at_laid_ground h.laid O.blank hA
  have hGd : ProofFile.blankBy ProofFile.pureRoad.links A.Z = some A.G := by
    rw [eG]
    exact O.blank
  obtain ⟨hok, -, hpub⟩ := closing_premises_at_finish h hGd hf hc
  have h1 : 1 < (K2.switchSent pl.sizes pl.others).size := by
    have t := finish_two_messages
    rw [← finish_is_written h hA, hf, Option.map_some] at t
    rw [Option.some.inj t]
    decide
  exact wordsTied_at_closing_stand h hA test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hf hok
    (fun v hv => hpub v.x (hstart v hv)) hReach
    (fun k st m E R J' hJ' c _ _ hl cs V hH hV =>
      carryRows_at_row_coins hH hV h1 J' (by rw [hJ']; rfl) hl (by rw [hJ']; exact hbook))

end ProofFile.Honest.K12.LotL

end

#print axioms ProofFile.Honest.K12.LotL.wordsTied_at_closing_stand_few
