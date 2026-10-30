-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/YesAtFifty.lean: THE SHARED "SENDING" (the kind K1): FROM A
STEP OF THE HONEST SIDE AT ONE OF THE FIFTY LATER MEMBERS TO THE FORM IN WHICH THE LIBRARY's LAWS OF
THE KIND TAKE A YES: K1.YesOf (Johnson/Desc/K1/Law/KeepAtLater.lean) OF THE LOT's OWN BLOCK blkL.
PUBLIC; NO WITNESS, NO MEANING, NO COIN IN IT. Four theorems; no definition.

  - yes_of_stepped   AT ANY THREAD OVER THE FIRST CHAIN's STATES AND ProofFile's CLAIMS (IM.Yes is typed
                  at these): Thread.Stepped's own second half (Honest/Thread/Pays.lean: the
                  acceptance of the sub-protocol's own step) IS the library's IM.Yes
                  (Johnson/IMR/HandsDef.lean) at the thread's first tree.
  - yesOf_fifty_head UNDER h (the library's head: A HYPOTHESIS), O: at l < 25, d: a yes of whatever
                  stands at number K1.noL l d of the flat list is a yes of blkL Zp Bs.G₀ l d X arrs,
                  at some X, arrs, at every public part z: the sealed k01_flat and yesOf_of_yes, as
                  our sealed pub_later_head (Honest/K1/Law/PubBehindAtFifty.lean) calls them.
  - yesOf_reads_head THE SAME AT THE READS (d = false), WITH Bs.G₀.built[l]? = some X AT THE SAME X:
                  the sealed k01_flat_reads (Johnson/Desc/K1/Law/K01LawTied.lean).
  - yesOf_reads_two  and with it a yes of that block's own decision on two rounds (the sealed
                  YesOf.two and two_blkL), at the same X and arrs.

Limits. IT PAYS NOTHING: that any step is taken is a hypothesis. THE FULL SIZE, THE FORMAT's EARLIER
HASH. Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.Thread.Pays
import Johnson.Desc.K1.Law.LettersAtFifty
import Johnson.Desc.K1.Law.HandsMoreAtLater
import Johnson.Desc.K1.Law.CallsG
import Johnson.Desc.K1.Law.MgK1
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Block Chain OpenedColumn)
open OnBytes.Maker (WholeD)
open OnBytes.Model.Stages (LinkH)
open P5J (AtMgA TS F0T)

/-- A step of the honest side is the library's yes of the sub-protocol's step. At any thread over
the first chain's type of states and ProofFile's type of claims (IM.Yes is typed at these two). -/
theorem yes_of_stepped {V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk TS ProofFile.Cl V W X Pb)
    {blk : Block TS ProofFile.Cl} {k : Coins Bk} {s : TS} {m : Mid W X} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid W X} {cols : List OpenedColumn} {s' : TS}
    (hS : T.Stepped blk k s m E ds y cols s') : IM.Yes T.ft blk s s' :=
  ⟨_, _, _, hS.2⟩

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)}

/-- **A YES AT ONE OF THE FIFTY IS THE LOT's OWN BLOCK's YES.** -/
theorem yesOf_fifty_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (_root_.Desc.K14.Law.seatZ Zp Np) (_root_.Desc.K14.Law.secondAt Zp Np)) {l : ℕ} (hl : l < 25)
    (d : Bool) {blk : Block TS ProofFile.Cl} (hb : cF.blocksInOrder[K1.noL l d]? = some blk) {ft : ℕ} {s s' : TS}
    (hy : IM.Yes ft blk s s') (z : ProofFile.InstPub) :
    ∃ (X : LinkH) (arrs : Option (List ℕ)),
      K1.YesOf (K1.blkL Zp Bs.G₀ l d X arrs) (z, s) (z, s') := by
  obtain ⟨e, X, arrs, he, hu⟩ := K1.k01_flat h.scope h.reads O l hl d
  obtain rfl : e = blk := Option.some.inj (he.symm.trans hb)
  exact ⟨X, arrs, K1.yesOf_of_yes hu hy z⟩

/-- **AT THE READS, WITH THE BUILT SEGMENT AT THE SAME X.** -/
theorem yesOf_reads_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (_root_.Desc.K14.Law.seatZ Zp Np) (_root_.Desc.K14.Law.secondAt Zp Np)) {l : ℕ} (hl : l < 25)
    {blk : Block TS ProofFile.Cl} (hb : cF.blocksInOrder[K1.noL l false]? = some blk) {ft : ℕ} {s s' : TS}
    (hy : IM.Yes ft blk s s') (z : ProofFile.InstPub) :
    ∃ (X : LinkH) (arrs : Option (List ℕ)), Bs.G₀.built[l]? = some X ∧
      K1.YesOf (K1.blkL Zp Bs.G₀ l false X arrs) (z, s) (z, s') := by
  obtain ⟨e, X, arrs, he, hX, hu⟩ := K1.k01_flat_reads h.scope h.reads O l hl
  obtain rfl : e = blk := Option.some.inj (he.symm.trans hb)
  exact ⟨X, arrs, hX, K1.yesOf_of_yes (IM.alone_underR hu) hy z⟩

/-- And with it a yes of that block's own decision on two rounds, at the same X and arrs. -/
theorem yesOf_reads_two (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (_root_.Desc.K14.Law.seatZ Zp Np) (_root_.Desc.K14.Law.secondAt Zp Np)) {l : ℕ} (hl : l < 25)
    {blk : Block TS ProofFile.Cl} (hb : cF.blocksInOrder[K1.noL l false]? = some blk) {ft : ℕ} {s s' : TS}
    (hy : IM.Yes ft blk s s') (z : ProofFile.InstPub) :
    ∃ (X : LinkH) (arrs : Option (List ℕ)) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64))),
      Bs.G₀.built[l]? = some X ∧ K1.YesOf (K1.blkL Zp Bs.G₀ l false X arrs) (z, s) (z, s') ∧
      (K1.blkL Zp Bs.G₀ l false X arrs).decide s [r₁, r₂] gs = .ok s' := by
  obtain ⟨X, arrs, hX, hY⟩ := yesOf_reads_head h O hl hb hy z
  obtain ⟨r₁, r₂, gs, hd⟩ := hY.two (K1.two_blkL Zp Bs.G₀ l false X arrs)
  exact ⟨X, arrs, r₁, r₂, gs, hX, hY, hd⟩

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.yes_of_stepped
#print axioms ProofFile.Honest.K1.yesOf_fifty_head
#print axioms ProofFile.Honest.K1.yesOf_reads_head
#print axioms ProofFile.Honest.K1.yesOf_reads_two
