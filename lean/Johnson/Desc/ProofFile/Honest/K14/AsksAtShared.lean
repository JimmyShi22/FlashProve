-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K14/AsksAtShared.lean: the linear claim's shared rounds (kind K14):
ALL THAT THE KIND's STATEMENTS ASK OF THE SHARED CHAIN's THREAD (K14Asks: sixteen fields,
Honest/K14/Asks.lean) AT THE LETTERS OF THE PROOF FILE's OWN DESCRIPTION (lettersShared,
Honest/Thread/SharedHead.lean), at any prover H, at every type of witnesses and every way ℓ to read
this kind's words off one. It says which of the sixteen fields are shown there, which change their
form, and which stay premises.

THE SIXTEEN, in asks_among, the statement with the fewest premises:
  plan, shapes        SHOWN under the library's hypothesis at the full size (h : P5J.AtMgA,
                      Johnson/P5J/MgAtAll.lean): plan2_at_head, sendings_at_head
  point, zeta         SHOWN: the public data is planData, whose two numbers are 0 and 6
  halves, sends       SHOWN for a prover whose list of the shared chain's sides begins with this
                      kind's six sides (hs), where the rest of the list stands at other places, each
                      once (apart, off): halves_among (Honest/K14/HalvesAmong.lean)
  letters             A PREMISE: nine equations on the letters (Asked). It holds where this kind's
                      makers are laid at the five open letters (asked_laid,
                      Honest/K14/AskedAtShared.lean): asks_laid shows the form
  tenant              A PREMISE, on the table's numbers N
  treesU, treesO      PREMISES, on the letters table and fixed
  cols, tab, key, seeds, ans   ONE PREMISE: FiveFields (Honest/K14/FiveFields.lean) at «the input is
                      this run's own input w, and Vd holds of it», with the prover's own stored
                      columns: facts on the committer's table and key. EACH IS TO BE SHOWN OF THE
                      COMMITTER's TABLE AND KEY; it is not met by laying the fact into Vd, and at a
                      Vd that holds of nothing K14Asks says nothing of a run (the rule of use at the
                      letter valid, Honest/Thread/Thr.lean's head)
  book                A PREMISE, on the book of coins

Main names:
  sentWithU           what goes out with the folded row's message at the plan: a value
  plan2_sentWithU     under h: the plan's public premises hold at that value
  asks_atShared       K14Asks at lettersShared, field by field; the five implications from «valid»
                      are taken at the run's own input alone
  asks_laid           the same where this kind's makers are laid: without the field letters
  asks_among          **K14Asks at lettersShared under h**, from the three premises on the prover's
                      list and the six fields that stay premises

What is not claimed. That any premise holds. That the thread's invariant holds at any state. Nothing
on completeness, soundness or hiding.
Terms. letter, border: lean/GLOSSARY.md. A thread is the invariant along a chain with its parameters
(Honest/Thread/Thr.lean). A member is a sub-protocol of a chain's flat list, numbered from 0. A side
is the prover's list of parts at one place (Placed, Honest/Frame.lean).
-/
import Johnson.Desc.ProofFile.Honest.K14.AskedAtShared
import Johnson.Desc.ProofFile.Honest.K14.FiveFieldsAsks
import Johnson.Desc.ProofFile.Honest.K14.HalvesAmong
import Johnson.Desc.ProofFile.Honest.K14.SendingsAtHead
import Johnson.Desc.ProofFile.Honest.K14.SendingsShapesLaw
import Johnson.Desc.ProofFile.Honest.K14.Thread2Full

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes OnBytes.Params
open OnBytes.Slice (rdE)
open VerifiableInference.Desc (Chain Place)
open VerifiableInference.Desc.Own (keyFits)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.K12.Seat (tests last)
open ProofFile.Honest.SharedThread (lettersShared)
open P5J (TS)
open Desc.K14 (St)
open Desc.K14.Honest
open Desc.K14.Law (genK)

variable {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {Bk : ProverCoinCounts}
  {W₀ Rc Tr X₀ X P₁ Wt : Type} {ℓ : WitLens Wt} {H : Prover W₀ Rc ProofFile.Inst TableKey Tr X₀ X}
  {N : NumbersS} {Mg : Common W₀ Rc TableKey → MeaningS St P₁ Wt}
  {shape : Nat → St → Bool} {nothingLeft : St → Bool} {order : St → Prop}
  {wit : Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Wt}
  {table : Fmt.TreeSource → Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table}
  {fixed : Fmt.TreeSource → Nat} {n₁ n₂ : Nat} {Vd : Common W₀ Rc TableKey → Prop}
  {Rd : Nat → Common W₀ Rc TableKey → St → Prop} {Kp : Place → St → St → Prop}
  {w : Common W₀ Rc TableKey} {sentU : Array OracleNotice} {layO : TreeLay} {A : Data}
  {weights : W₀ → Weights} {rand : Rc → TableRand}

/-- **K14Asks AT lettersShared.** letters: Asked (AskedAtShared.lean). The ten fields plan, shapes,
point, zeta, halves, sends, tenant, treesU, treesO, book are taken as they lie. THE FIVE
IMPLICATIONS FROM valid ARE TAKEN AT THE RUN's OWN INPUT w ALONE, under Vd w; the committed table is
the prover's own (H.storedWords). -/
theorem asks_atShared
    (letters : Asked ℓ (lettersShared Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁ n₂
      Vd Rd Kp w) (qAt Zp Np) sentU Zp.p.chains (tests Np) last (holds2 (qAt Zp Np) weights rand))
    (plan : Plan2 (qAt Zp Np) sentU layO) (shapes : SendShapes (qAt Zp Np))
    (point : A.atPoint = 0) (zeta : A.atZeta = 6)
    (halves : HalvesIn (qAt Zp Np) (othersOf ℓ (lettersShared Zp Np cF H N Mg shape nothingLeft
      order wit table fixed n₁ n₂ Vd Rd Kp w) Zp.p.chains (tests Np) last
      (holds2 (qAt Zp Np) weights rand)) A weights)
    (sends : SendsIn (qAt Zp Np) (othersOf ℓ (lettersShared Zp Np cF H N Mg shape nothingLeft
      order wit table fixed n₁ n₂ Vd Rd Kp w) Zp.p.chains (tests Np) last
      (holds2 (qAt Zp Np) weights rand)) A weights rand)
    (tenant : Function.Injective N.tenant)
    (treesU : TreesLaid (lettersShared Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁ n₂
      Vd Rd Kp w).thread 2 (jobU ⟨qAt Zp Np, 0⟩) (witOf (qAt Zp Np) weights rand))
    (treesO : TreesLaid (lettersShared Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁ n₂
      Vd Rd Kp w).thread 5 (jobOmega ⟨qAt Zp Np, 0⟩) (witOf (qAt Zp Np) weights rand))
    (cols : Vd w → ∀ p < 2 ^ (Desc.K14.readsAtLoc (qAt Zp Np).S.fold (qAt Zp Np).item).sh.a,
      ∃ u, H.storedWords w.w₀ w.rc (Desc.K14.readsAtLoc (qAt Zp Np).S.fold (qAt Zp Np).item).item
        p = some u ∧ u.length = (Desc.K14.readsAtLoc (qAt Zp Np).S.fold (qAt Zp Np).item).sh.W)
    (tab : Vd w → ∀ (k : Coins Bk), ∀ x < 2 ^ (qAt Zp Np).par.S.fold.index.code.logN,
      ∀ r < (qAt Zp Np).par.S.fold.index.rows,
        rdE.val (ofF (((H.storedWords w.w₀ w.rc (qAt Zp Np).item x).getD []).toArray.getD r 0)) =
          genK rdE (qAt Zp Np).par.S.fold x ((holds2 (qAt Zp Np) weights rand k w).Rw r))
    (key : Vd w → keyFits w.key (qAt Zp Np).par.S.fold.index = true)
    (seeds : Vd w → noZeroFactor w.key = true)
    (ans : Vd w → ∀ k : Coins Bk,
      OwnAnswers (qAt Zp Np) w.key (holds2 (qAt Zp Np) weights rand k w))
    (book : ∀ e ∈ Bk.ahead, e.spender = ⟨place 8, 0⟩ → e.once = true →
      e.owner = ⟨sendPlace 5, 0⟩ ∧ e.start = ⟨0, offsetOf (jobOmega ⟨qAt Zp Np, 0⟩).Q.codes
        (jobOmega ⟨qAt Zp Np, 0⟩).Q.sent (jobOmega ⟨qAt Zp Np, 0⟩).sort 1⟩) :
    K14Asks ℓ
      (lettersShared Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd Rd Kp w)
      (qAt Zp Np) sentU layO Zp.p.chains (tests Np) last A weights rand where
  letters := letters
  plan := plan
  shapes := shapes
  point := point
  zeta := zeta
  halves := halves
  sends := sends
  tenant := tenant
  treesU := treesU
  treesO := treesO
  cols := fun v hv => by
    obtain ⟨rfl, hV⟩ := hv
    exact cols hV
  tab := fun k v hv => by
    obtain ⟨rfl, hV⟩ := hv
    exact tab hV k
  key := fun v hv => by
    obtain ⟨rfl, hV⟩ := hv
    exact key hV
  seeds := fun v hv => by
    obtain ⟨rfl, hV⟩ := hv
    exact seeds hV
  ans := fun k v hv => by
    obtain ⟨rfl, hV⟩ := hv
    exact ans hV k
  book := book

/-- **K14Asks AT THE LAID LETTERS, UNDER THE FIFTEEN OTHER FIELDS**: where this kind's makers are
laid at lettersShared's five open letters, the field letters holds (AskedAtShared.lean:
asked_laid). L stands for that term, by the equation hL. -/
theorem asks_laid {Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt} {shape₀ : Nat → St → Bool}
    {rest : Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Wt} {Kp₀ : Place → St → St → Prop}
    {L : SharedThread.Letters Bk St ProofFile.Cl W₀ Rc TableKey X₀ P₁ Wt}
    (hL : L = lettersShared Zp Np cF H N (fun v => mgWords ℓ (qAt Zp Np) N (Mg₀ v))
      (form2 (qAt Zp Np) shape₀) nothingLeft (fun s => OnBytes.Means.InOrder s.st)
      (witL ℓ (qAt Zp Np) sentU (holds2 (qAt Zp Np) weights rand) rest) table fixed n₁ n₂ Vd Rd
      (kp2 (qAt Zp Np) sentU Kp₀) w)
    (plan : Plan2 (qAt Zp Np) sentU layO) (shapes : SendShapes (qAt Zp Np))
    (point : A.atPoint = 0) (zeta : A.atZeta = 6)
    (halves : HalvesIn (qAt Zp Np) (othersOf ℓ L Zp.p.chains (tests Np) last
      (holds2 (qAt Zp Np) weights rand)) A weights)
    (sends : SendsIn (qAt Zp Np) (othersOf ℓ L Zp.p.chains (tests Np) last
      (holds2 (qAt Zp Np) weights rand)) A weights rand)
    (tenant : Function.Injective N.tenant)
    (treesU : TreesLaid L.thread 2 (jobU ⟨qAt Zp Np, 0⟩) (witOf (qAt Zp Np) weights rand))
    (treesO : TreesLaid L.thread 5 (jobOmega ⟨qAt Zp Np, 0⟩) (witOf (qAt Zp Np) weights rand))
    (cols : Vd w → ∀ p < 2 ^ (Desc.K14.readsAtLoc (qAt Zp Np).S.fold (qAt Zp Np).item).sh.a,
      ∃ u, H.storedWords w.w₀ w.rc (Desc.K14.readsAtLoc (qAt Zp Np).S.fold (qAt Zp Np).item).item
        p = some u ∧ u.length = (Desc.K14.readsAtLoc (qAt Zp Np).S.fold (qAt Zp Np).item).sh.W)
    (tab : Vd w → ∀ (k : Coins Bk), ∀ x < 2 ^ (qAt Zp Np).par.S.fold.index.code.logN,
      ∀ r < (qAt Zp Np).par.S.fold.index.rows,
        rdE.val (ofF (((H.storedWords w.w₀ w.rc (qAt Zp Np).item x).getD []).toArray.getD r 0)) =
          genK rdE (qAt Zp Np).par.S.fold x ((holds2 (qAt Zp Np) weights rand k w).Rw r))
    (key : Vd w → keyFits w.key (qAt Zp Np).par.S.fold.index = true)
    (seeds : Vd w → noZeroFactor w.key = true)
    (ans : Vd w → ∀ k : Coins Bk,
      OwnAnswers (qAt Zp Np) w.key (holds2 (qAt Zp Np) weights rand k w))
    (book : ∀ e ∈ Bk.ahead, e.spender = ⟨place 8, 0⟩ → e.once = true →
      e.owner = ⟨sendPlace 5, 0⟩ ∧ e.start = ⟨0, offsetOf (jobOmega ⟨qAt Zp Np, 0⟩).Q.codes
        (jobOmega ⟨qAt Zp Np, 0⟩).Q.sent (jobOmega ⟨qAt Zp Np, 0⟩).sort 1⟩) :
    K14Asks ℓ L (qAt Zp Np) sentU layO Zp.p.chains (tests Np) last A weights rand := by
  subst hL
  exact asks_atShared
    (asked_laid Zp Np cF H N nothingLeft table fixed n₁ n₂ Vd Rd w ℓ Mg₀ shape₀ rest Kp₀) plan
    shapes point zeta halves sends tenant treesU treesO cols tab key seeds ans book

/-- **What goes out with the folded row's message, at the plan**: the library's own list; the empty
array where the library makes none (under the hypothesis at the full size it makes one:
plan2_sentWithU). -/
abbrev sentWithU (Zp : ProofFile.Pub) (Np : H2U.Places4) : Array OracleNotice :=
  (Desc.K14.withU (qAt Zp Np).S).getD #[]

/-- **Under the library's hypothesis at the full size the plan's public premises hold at
sentWithU.** -/
theorem plan2_sentWithU {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    {x₀ : VerifiableInference.Desc.First.Look.Place} {o : ProofFile.SecondHashFunctionArgument}
    (h : P5J.AtMgA o Z D r Zp Np cF x₀) : ∃ layO, Plan2 (qAt Zp Np) (sentWithU Zp Np) layO := by
  obtain ⟨u, l, p⟩ := plan2_at_head h
  have hu : Desc.K14.withU (qAt Zp Np).S = some u := p.facts.goes
  have e : sentWithU Zp Np = u := by
    show (Desc.K14.withU (qAt Zp Np).S).getD #[] = u
    rw [hu]
    rfl
  exact ⟨l, e ▸ p⟩

/-- **K14Asks AT lettersShared, UNDER THE HYPOTHESIS AT THE FULL SIZE, FOR A PROVER WHOSE LIST
BEGINS WITH THIS KIND's SIX SIDES.** hs, apart, off: the prover's list of the shared chain's sides
is the six, then `more`, whose sides stand at other places, each once. letters, tenant, treesU,
treesO, five, book: the fields that stay premises (the file's head). -/
theorem asks_among {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    {x₀ : VerifiableInference.Desc.First.Look.Place} {o : ProofFile.SecondHashFunctionArgument}
    (h : P5J.AtMgA o Z D r Zp Np cF x₀)
    {more : List (Placed Empty (Common W₀ Rc TableKey) X₀)}
    (hs : H.shared = proverSidesOfSharedRounds (planData (qAt Zp Np)) weights ++
      proverSidesOfSharedSendings ⟨qAt Zp Np, 0⟩ weights rand ++ more)
    (apart : (more.map (·.place)).Nodup) (off : ∀ g ∈ more, g.place ∉ sixPlaces)
    (letters : Asked ℓ (lettersShared Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁ n₂
      Vd Rd Kp w) (qAt Zp Np) (sentWithU Zp Np) Zp.p.chains (tests Np) last
      (holds2 (qAt Zp Np) weights rand))
    (tenant : Function.Injective N.tenant)
    (treesU : TreesLaid (lettersShared Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁ n₂
      Vd Rd Kp w).thread 2 (jobU ⟨qAt Zp Np, 0⟩) (witOf (qAt Zp Np) weights rand))
    (treesO : TreesLaid (lettersShared Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁ n₂
      Vd Rd Kp w).thread 5 (jobOmega ⟨qAt Zp Np, 0⟩) (witOf (qAt Zp Np) weights rand))
    (five : FiveFields (qAt Zp Np) (fun v => v = w ∧ Vd v) (fun v => H.storedWords v.w₀ v.rc)
      weights rand)
    (book : ∀ e ∈ Bk.ahead, e.spender = ⟨place 8, 0⟩ → e.once = true →
      e.owner = ⟨sendPlace 5, 0⟩ ∧ e.start = ⟨0, offsetOf (jobOmega ⟨qAt Zp Np, 0⟩).Q.codes
        (jobOmega ⟨qAt Zp Np, 0⟩).Q.sent (jobOmega ⟨qAt Zp Np, 0⟩).sort 1⟩) :
    ∃ layO, K14Asks ℓ
      (lettersShared Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd Rd Kp w)
      (qAt Zp Np) (sentWithU Zp Np) layO Zp.p.chains (tests Np) last (planData (qAt Zp Np)) weights
      rand := by
  obtain ⟨layO, plan⟩ := plan2_sentWithU h
  obtain ⟨hh, hsn⟩ := halves_among (Q := qAt Zp Np)
    (O := othersOf ℓ (lettersShared Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁ n₂
      Vd Rd Kp w) Zp.p.chains (tests Np) last (holds2 (qAt Zp Np) weights rand))
    (A := planData (qAt Zp Np)) (weights := weights) (rand := rand) rfl hs apart off
  exact ⟨layO, asks_of_five five letters plan (sendShapes_of_fit (sendings_at_head h).1) rfl rfl hh
    hsn tenant treesU treesO book⟩

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.asks_atShared
#print axioms ProofFile.Honest.K14.asks_laid
#print axioms ProofFile.Honest.K14.plan2_sentWithU
#print axioms ProofFile.Honest.K14.asks_among
