-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the kind's share at the last chain, in the text of the row that spends it.
/-
AtFullSide/K12/SecondShareK12.lean: CONDITIONAL: A CONDITIONAL WITH NO KNOWN MEMBER.

Can the hypotheses be met together at a real run? NOT KNOWN. `OwnTestDebts`.rowsSay: at the letters'
names it is `rowsSay_at_the_letters` (AtFullSide/K12/RowsSayAtTheLetters.lean), UNDER PREMISES THAT
STAY THERE: the head at the return, the maker's return and the last chain's open letters P
(`openLast`, Honest/K12/AtFile/WAtTheLetters.lean, is a value of P); by reading, not by a theorem,
it cannot be paid at a companion Said that does not hold the tie to the two earlier chains' ends. No
value of the thread and its companion is laid here: Th, Said are letters. No value of G is laid:
hrows is a premise on a letter. Nothing shows that ready or runC returns or that a part of the test
is called: where none is called on₃'s ends hold for nothing. The thread's own input w, one of the
seventeen letters of `OwnTestDebts`.thread, is tied to the run by hI₃ alone: at a family whose third
member stands at another input on₃'s ends hold for nothing too; at the letters' names
(AtFullSide/K12/SecondShareAtTheLetters.lean) w is the own input of the run's return of ready.

What is here. THE KIND K12's SHARE AT THE LAST CHAIN, IN THE TEXT OF THE ROW THAT SPENDS IT: at
every list of G's last chain whose place is of the kind K12. The fellow at the last chain of
AtFullSide/K12/SharedShareK12.lean (the shared chain's two tests). A SORTING OF HYPOTHESES: IT PAYS
NOTHING BEYOND WHAT THE LAWS CALLED PAY. Two definitions, meant as hypotheses; three statements. The
description is a letter F under an equation (eF), so that the statements can be read at the
description that the maker's return holds.

  `K12RowAtW`   a list takes place, parts, On and bud from a row of the lot's value `lotW`.
  `OwnTestDebts`   what is left at the request's own test, by name: three fields: thread · said ·
      rowsSay.
  `k12_on₃_at_base`   `OnAtRun₃` at every such list: `onAtRun_W_six_paid` (Sim2/ListWSixPaid.lean)
      at the lot's row (`row_of_lotW`, Sim2/ListWAtLot.lean). That the filling's list is not empty
      is no premise: it follows from the row (`lotW_halves`).
  `k12_bud₃_at_base`   the kind's share of bud₃: `rowW_owes` (Johnson/M1/SlotsSeat.lean): from the
      head and hrows alone.
  `k12_on₃_at_named`   the first in the form of the socket `threads_of_named`
      (Johnson/T3/ThreadsAtRing.lean): `OnAtRunAt₃` at a family under a letter.

THE PREMISES OF THE FIRST AND THE LAST, SORTED. PUBLIC: h · eF. THE MAKER: hAr (the filling at hand;
at the matrices and T1's values it is the base filling); the book is the return's own: no premise on
a book. WHICH OBJECTS: hP | ring · hM (the job that the filling lays at the return's ground) ·
hrows. THE RUN: T · hρ · hR · hrun: the rule's own letters. THE INVARIANT: hI₃: the rule's family at
border 2 of the last chain is the thread's with its companion: at a value of `ThreadsP` made of
named threads it holds by rfl [others' word; not held here]. THE DEBTS: `OwnTestDebts`. THE BINDERS
w₀, rc, x ARE FREE, AND EVERY PREMISE ON THE RUN (T · hR · hrun · hI₃ · the debts) STANDS AT THEM:
each has to be had there. The step from a relation to these letters is owed where T and the debts
are paid: the premise hRel of AtFullSide/K12/ShareK12AtTheThreads.lean.

Every letter under "there are": in `K12RowAtW` the row is tied by its membership in the lot's rows
and by the four equations; in `OwnTestDebts`.thread the seventeen letters are tied by the one
equation on Th: both stand in hypotheses. No end of a statement here holds a "there are".

Limits. All limits of Sim2/ListWSixPaid.lean's, Sim2/ListWAtLot.lean's and the heads of the
lot's two files. Files beneath bear "NOT IN FRONT OF A LAW OVER COINS" for rowsSay's like:
 whoever pays that field pays it at every coin at which a stand is there. The rule
moves the debt and pays none of it. At the maker's return at that filling. Not `Good`. Nothing
on completeness, soundness or hiding.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim2.ListWSixPaid
import Johnson.Desc.ProofFile.Honest.K12.Sim2.ListWAtLot
import Johnson.M1.SlotsSeat
import Johnson.M1.BudShareCore
import Johnson.T3.ThreadsAtRing

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace AtFullSide.K12
open VerifiableInference.Desc (Block Chain FileDescription KindName Place)
open VerifiableInference.Desc.K12.Seat (enterOwn)
open VerifiableInference.Desc.Third (S₃)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.AtProof ProofFile.Honest.K12.Light ProofFile.Honest.K12.Sim2
open ProofFile.Honest.LastThread (lettersLast)
open ProofFile.Honest.K12.AtFile (takenLast)

attribute [local irreducible] P2Law.ProofPlan.WP

variable {W₀ : Type} {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}

/-- **One list of the kind K12 at the last chain takes its four fields from a row of the lot at the
request's own test** (`lotW` at the face of a chain of its own, Johnson/M1/SlotsUW.lean). A
definition, meant as a hypothesis on a G that is a letter. -/
def K12RowAtW {Bk : ProverCoinCounts} {S' Cl' : Type} (I : WiderIn W₀) (Sz : OnBytes.HonestTrace.Sz)
    (O : OnlineProverArguments) (Zp : ProofFile.Pub) (Gd : ProofFile.Ground)
    (L : Lettered Bk S' Cl' (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit
        ProofFile.Inst) : Prop :=
  ∃ row : Unlettered (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit ProofFile.Inst,
    row ∈ (lotW Face.own I OnBytes.secondHashFunction Sz O).rows Zp Gd ∧
    L.place = row.place ∧ L.row = row.row ∧ L.On = row.On ∧ L.bud = row.bud

/-- **What `onAtRun_W_six_paid` (Sim2/ListWSixPaid.lean) leaves at the request's own test, by
name**, at a description F (a letter: the laws ask it under an equation), a prover Hp, one run's
coins k, the job M, a thread Th of the last chain and its companion Said. thread: Th is the
library's last thread at some letters, with the written list of the trees taken over (under HEq,
because F is a letter). said: at border 2 the companion gives the field's letter at the columns of
the two earlier chains. rowsSay: `SaysAt` at every stand of the thread at border 2 and whatever the
frame lends the unguarded pair. A definition, meant as a hypothesis. -/
structure OwnTestDebts (F : FileDescription ProofFile.Inst) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : Chain P5J.TS ProofFile.Cl)
    (Hp : Prover W₀ IndexCommitterCoins ProofFile.Inst OnBytes.TableKey Cells Unit Unit) {Bk : ProverCoinCounts}
    (k : Coins Bk) (M : ManyJob (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit)
    (Th : Thread Bk F.S₃ F.Cl (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit
        ProofFile.Inst)
    (Said : ℕ → Coins Bk → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop) : Prop where
  thread : ∃ (Wt : Type) (N : VerifiableInference.Desc.Shared.NumbersS)
    (Mg : (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) →
      VerifiableInference.Desc.Shared.MeaningS Desc.K14.St (ProofFile.InstPub × P5J.TS) Wt)
    (ML : VerifiableInference.Desc.Last.MeaningL S₃ Wt)
    (PL : VerifiableInference.Desc.Last.PromMeaningL Desc.K14.St S₃ (ProofFile.InstPub × P5J.TS))
    (order : S₃ → Prop)
    (ends : Coins Bk → (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) → List Fmt.Drawn → (ProofFile.InstPub × P5J.TS) ×
        Desc.K14.St)
    (wit : Coins Bk → (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) → List Fmt.Drawn → Wt)
    (table : Fmt.TreeSource → Coins Bk → (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) → List Fmt.Drawn → Place ×
        Table)
    (fixed : Fmt.TreeSource → ℕ) (item n₁ n₂ : ℕ) (Vd : (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) → Prop)
    (Rd : ℕ → (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) → S₃ → Prop) (Kp : Place → S₃ → S₃ → Prop)
    (w : (Local W₀ IndexCommitterCoins ProofFile.Inst Cells)),
    HEq Th (lettersLast Zp Np cF Hp N Mg ML PL order takenLast ends wit table fixed item n₁ n₂ Vd
        Rd Kp
        w).thread
  said : ∀ k m, Said 2 k m → SaidField Th (BaseTied F Th) 2 k m
  rowsSay : ∀ (st : F.S₃) (m₀ : Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit) (E₀ : Env)
    (c : RowCoins [(firstPart M.toRun.toTest : Part (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (Local W₀ IndexCommitterCoins
              ProofFile.Inst Cells) Unit),
      restPart M.toRun.toTest]),
    ThrS Th Said 2 k st m₀ E₀ →
    lendRow Bk (Bk.rowsOf 2) (k.look 2) placeW
      [(firstPart M.toRun.toTest : Part (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (Local W₀ IndexCommitterCoins ProofFile.Inst
                Cells) Unit),
        restPart M.toRun.toTest] 0 = .ok c →
    SaysAt M m₀.st.input (frontOf m₀) (restCoins M.toRun.toTest c.2.1)

/-- CONDITIONAL: see the head. **K12's SHARE OF on₃.** -/
theorem k12_on₃_at_base {x₀ : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF x₀) (I : WiderIn W₀)
    (S' : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) {Ar : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hAr : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S' O) =
      .ok Ar) (F : FileDescription ProofFile.Inst) (eF : F = (P5J.F0T OnBytes.secondHashFunction Zp Np cF))
    {H : Prover W₀ IndexCommitterCoins ProofFile.Inst OnBytes.TableKey Cells Unit Unit}
    {G : Sides F Ar.B W₀ IndexCommitterCoins OnBytes.TableKey Cells Unit Unit}
    (hP : G.prover H = Ar.H) {w₀ : W₀} {rc : IndexCommitterCoins}
    {x : ProofFile.Inst} {k : Coins Ar.B} {ρ : Draws}
    {R : Ready W₀ IndexCommitterCoins ProofFile.Inst OnBytes.TableKey Cells Unit Unit} {r : RunC F}
    (T : ThreadsP F Ar.B (G.prover H) w₀ rc x k R) (hρ : ρ.due F = true)
    (hR : ready F Ar.B (G.prover H) w₀ rc x k = .ok R)
    (hrun : runC F Ar.B (G.prover H) w₀ rc x k ρ = .ok r)
    (M : ManyJob (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit)
    (hM : jobRealW S' (P5J.F0T OnBytes.secondHashFunction Zp Np cF) enterOwn O.pile (K1.lotNo OnBytes.secondHashFunction Zp)
      (fun w => ⟨w.trace, I.weights Zp w.w₀, w.rc⟩) (fun w => I.weights Zp w.w₀)
      (fun P w => randAt P w.rc) Zp Ar.G = some M)
    (Th : Thread Ar.B F.S₃ F.Cl (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (Local W₀ IndexCommitterCoins ProofFile.Inst Cells)
        Unit ProofFile.Inst)
    (Said : ℕ → Coins Ar.B → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop)
    (hI₃ : T.I₃ 2 = ThrS Th Said 2) (debts : OwnTestDebts F Zp Np cF Ar.H k M Th Said)
    (hrows : ∀ L ∈ G.second, L.place.kind = KindName.K12 → K12RowAtW I S' O Zp Ar.G L) :
    ∀ L ∈ G.second, L.place.kind = KindName.K12 → OnAtRun₃ (G := G) (H := H) T ρ r L := by
  subst eF
  intro L hL hk
  obtain ⟨row, hrow, hpl, hr, hOn, hbud⟩ := hrows L hL hk
  obtain ⟨M', hM', hq⟩ := row_of_lotW (Np := Np) (cF := cF) h.toAtMg Face.own I S' O Ar.G row hrow
  obtain rfl : M' = M := Option.some.inj (hM'.symm.trans hM)
  have hbare : L.bare = rowAtW Face.own OnBytes.secondHashFunction Zp Np cF M'.toRun.toTest := by
    rw [← hq]
    show (⟨L.place, L.row, L.On, L.bud⟩ : Unlettered _ _ _ _) = row
    rw [hpl, hr, hOn, hbud]
  have eZ : Ar.Z = Zp := (atPure_at_laid h.laid hAr).1
  have hne : secondW (X := Unit) I OnBytes.secondHashFunction S' O Ar.Z Ar.G ≠ [] := by
    rw [eZ, ← lotW_halves Face.own I OnBytes.secondHashFunction S' O Zp Ar.G]
    intro e
    have e' : ((lotW (X := Unit) Face.own I OnBytes.secondHashFunction S' O).rows Zp Ar.G).map (·.half) = [] :=
      e
    rw [List.map_eq_nil_iff.1 e'] at hrow
    cases hrow
  obtain ⟨Wt, N, Mg, ML, PL, order, ends, wit, table, fixed, item, n₁, n₂, Vd, Rd, Kp, w, hTh⟩ :=
    debts.thread
  obtain rfl := eq_of_heq hTh
  exact onAtRun_W_six_paid h I S' O hAr hne hP T hρ hR hrun M' hM L hbare N Mg ML PL order ends wit
    table fixed item n₁ n₂ Vd Rd Kp w Said debts.said hI₃ debts.rowsSay

/-- CONDITIONAL: on the head and hrows. **K12's SHARE OF bud₃**: no other premise. -/
theorem k12_bud₃_at_base (h : P5J.AtMg OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF) (I : WiderIn W₀)
    (S' : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) {Bk : ProverCoinCounts} (F : FileDescription ProofFile.Inst)
    (eF : F = (P5J.F0T OnBytes.secondHashFunction Zp Np cF))
    {G : Sides F Bk W₀ IndexCommitterCoins OnBytes.TableKey Cells Unit Unit} (Gd : ProofFile.Ground)
    (hrows : ∀ L ∈ G.second, L.place.kind = KindName.K12 → K12RowAtW I S' O Zp Gd L) :
    ∀ L ∈ G.second, L.place.kind = KindName.K12 → Johnson.M1.BudOwed₃ F L := by
  subst eF
  intro L hL hk
  obtain ⟨row, hrow, hpl, hr, -, hbud⟩ := hrows L hL hk
  exact rowW_owes h Face.own I OnBytes.secondHashFunction S' O Gd row hrow L hpl hr hbud

/-- CONDITIONAL: see the head. **K12's SHARE OF on₃ IN THE FORM OF THE SOCKET** (`threads_of_named`,
Johnson/T3/ThreadsAtRing.lean): ready and runC at the return's own prover, the ring as a premise, a
value T at that prover, its third family under a letter I₃ (eI), and the end `OnAtRunAt₃` at that
letter. -/
theorem k12_on₃_at_named {x₀ : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF x₀) (I : WiderIn W₀)
    (S' : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) {Ar : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hAr : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S' O) =
      .ok Ar) (F : FileDescription ProofFile.Inst) (eF : F = (P5J.F0T OnBytes.secondHashFunction Zp Np cF))
    {G : Sides F Ar.B W₀ IndexCommitterCoins OnBytes.TableKey Cells Unit Unit}
    (ring : G.prover Ar.H = Ar.H) {w₀ : W₀} {rc : IndexCommitterCoins}
    {x : ProofFile.Inst} {k : Coins Ar.B}
    {R : Ready W₀ IndexCommitterCoins ProofFile.Inst OnBytes.TableKey Cells Unit Unit}
    (hR : ready F Ar.B Ar.H w₀ rc x k = .ok R)
    (T : ThreadsP F Ar.B Ar.H w₀ rc x k R)
    (I₃ : ℕ → Coins Ar.B → F.S₃ → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Env → Prop)
    (eI : T.I₃ = I₃)
    (M : ManyJob (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit)
    (hM : jobRealW S' (P5J.F0T OnBytes.secondHashFunction Zp Np cF) enterOwn O.pile (K1.lotNo OnBytes.secondHashFunction Zp)
      (fun w => ⟨w.trace, I.weights Zp w.w₀, w.rc⟩) (fun w => I.weights Zp w.w₀)
      (fun P w => randAt P w.rc) Zp Ar.G = some M)
    (Th : Thread Ar.B F.S₃ F.Cl (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (Local W₀ IndexCommitterCoins ProofFile.Inst Cells)
        Unit ProofFile.Inst)
    (Said : ℕ → Coins Ar.B → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop)
    (hI₃ : I₃ 2 = ThrS Th Said 2) (debts : OwnTestDebts F Zp Np cF Ar.H k M Th Said)
    (hrows : ∀ L ∈ G.second, L.place.kind = KindName.K12 → K12RowAtW I S' O Zp Ar.G L)
    (ρ : Draws) (r : RunC F) (hρ : ρ.due F = true)
    (hrun : runC F Ar.B Ar.H w₀ rc x k ρ = .ok r) :
    ∀ L ∈ G.second, L.place.kind = KindName.K12 →
      OnAtRunAt₃ G Ar.H w₀ rc x k I₃ ρ r L := by
  intro L hL hk
  have a : OnAtRunAt₃ G Ar.H w₀ rc x k (ThreadsP.ofEq ring.symm T).I₃ ρ r L :=
    k12_on₃_at_base h I S' O hAr F eF ring (ThreadsP.ofEq ring.symm T) hρ (by rw [ring]; exact hR)
      (by rw [ring]; exact hrun) M hM Th Said (by rw [ThreadsP.ofEq_I₃, eI]; exact hI₃) debts hrows
      L hL hk
  rw [ThreadsP.ofEq_I₃, eI] at a
  exact a

end AtFullSide.K12

#print axioms AtFullSide.K12.K12RowAtW
#print axioms AtFullSide.K12.OwnTestDebts
#print axioms AtFullSide.K12.k12_on₃_at_base
#print axioms AtFullSide.K12.k12_bud₃_at_base
#print axioms AtFullSide.K12.k12_on₃_at_named
