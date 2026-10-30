-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LotTreesSentBeforeOwnTestProved.lean: LOT P3 (LotOldAtOwnTest, fifth text) AT V := THE LAST CHAIN's OWN (In1 FullSizeMatrix EncodingRandomness): CLOSED: from part 4's takenAtTheOwnTest (LOT-K12-d,
K12/Part4/OwnTaken.lean), whose eight premises (OwnTestGround) are all paid here at the value K := offlineSenders description.

  tblOwn, restOwn, threadOwnP3   a thread of the last chain whose table at the three sources is the three senders' own texts and whose fixed is fixedLast: P3's statement
                                 names no thread: any such thread serves
  ground_p3      **OwnTestGround at that thread and at the value**: book, place: the lot's own premises · senders, idxPlace, wPlace: own_senders_fields, ParAlike
                 (E2E/KeyK1/SendersAlike.lean) · tables: by definition · omegaReads, wReads: K12/AtKeyOwn/ReadsAtPins.lean: under ChainPins, paid in scope at the
                 description's return (chainPins_at_description, E2E/KeyK1/KeyK1AtTerm.lean)
  tableAt_idx, tableAt_w, tableAt_omega   the thread's table at a state is TablesAreLaid's text
  **lot_p3**     THE LOT

Limits. V := In1 FullSizeMatrix EncodingRandomness alone: a Thread over that input exists at no other V (Face has two constructors); the lot is narrowed so (lane). IT RESTS ON ANOTHER
HOUSE's LAW: by its own word (lane) a trial, read by its hostile reader by difference, with 60 kernel lines replayed by no independent checker. THE LOT's FILE IS IMPORTED WITH ALL ITS OWN IMPORTS and one mend («noncomputable section»): it loads beside IOP's K12/AtFile/ClosingStand.lean
since the lot's cone renamed its own K12FrontD. That the lot's premises are met
together anywhere (lendRow's return; TablesAreLaid at a stand) is not shown here. Nothing on completeness, soundness or hiding.
-/
import E2E.LotTreesSentBeforeOwnTest
import Johnson.Desc.ProofFile.Honest.K12.Part4.OwnTaken
import Johnson.Desc.ProofFile.Honest.K12.AtKeyOwn.ReadsAtPins
import E2E.KeyK1.KeyK1AtTerm
import E2E.KeyK1.SendersAlike
import Johnson.Desc.ProofFile.Honest.K12.AtKeyOwn.Frame

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace AtPublicFiles.KeyLastChain.Lots
open ProofFile.Honest ProofFile.Honest.K12
open ProofFile.Honest.K12.Part4
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open AtPublicFiles.AtFiles.HonestTerm (OfflineDescription offlineDescription)
open VerifiableInference.Desc.Key (descriptionFromSource)

variable (files : VerifierAndGoals.PublicFiles) (D : OfflineDescription) (K₀ : KeyPub)

/-- The three senders' own texts of a tree's table. -/
def tblOwn : Fmt.TreeSource → Coins (keyBook K₀) → AtPublicFiles.KeyFile.In1 AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles files).EncodingRandomness →
    List Fmt.Drawn → VerifiableInference.Desc.Place × Table
  | .taken 0 0 => K1.treeTbl 0 id (lotK files D).idx (lotK files D).own₀ 0
  | .taken 0 5 => K1.treeTbl 0 id (lotK files D).w (lotK files D).own₀ 0
  | _ => fun k w h =>
    K14.sendTable (K14.jobOmega (lotK files D).send)
      (K14.witOf (lotK files D).send.P (lotK files D).weights fun c => AtPublicFiles.KeyFile.randK14 ((lotK files D).rand c))
      (K14.sendPlace 5) 1 0 k (AtPublicFiles.KeyDoorItems.commonOf w)
      (h.drop ((descriptionFromSource D.source D.numbers D.later).first.blocksInOrder.flatMap (·.rounds)).length)

/-- Letters that no statement here reads. -/
def restOwn : AtPublicFiles.KeyThread.Rest (keyBook K₀) (descriptionFromSource D.source D.numbers D.later).S₃
    (AtPublicFiles.KeyFile.In1 AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles files).EncodingRandomness) :=
  { table := tblOwn files D K₀, stored := fun _ _ _ => none, valid := fun _ => True, P := Unit
    handed := fun _ _ _ => (), Wt := Unit, form := fun _ _ => true, formP := fun _ _ => True
    means := fun _ _ _ _ _ => True, wit := fun _ _ _ => (), strs := Env.strs 0 fun _ => none
    begun := fun _ _ _ _ => True, rides := fun _ _ _ => True, keeps := fun _ _ _ => True }

/-- A thread of the last chain with these tables. -/
def threadOwnP3 := AtPublicFiles.KeyThread.keyBase₃ (X := Unit) (descriptionFromSource D.source D.numbers D.later) (restOwn files D K₀)

variable {files D K₀}

/-- **part 4's ground at that thread, at the value: all eight fields.** -/
theorem ground_p3 (hZ : VerifierAndGoals.InScope files = true) (h : offlineDescription files = .ok D)
    (hK : fullPub = some K₀) (hp : AtPublicFiles.KeyLay.pWK D.later = H2K.Member.piKWFull) :
    OwnTestGround (threadOwnP3 files D K₀) (lotK files D) D.source D.numbers D.later
      AtPublicFiles.KeyDoorItems.commonOf := by
  have hc := AtPublicFiles.KeyK1.chainPins_at_description hZ h
  obtain ⟨s1, s2, s3, s4, s5, s6, s7⟩ := AtPublicFiles.KeyK1.own_senders_fields (Rc := (AtPublicFiles.AtFiles.protocolAtFiles files).EncodingRandomness) (X := Unit) hc
    AtPublicFiles.AtFiles.HonestTerm.matrixReader
  exact
    { book := hK, place := hp
      senders := ⟨s1, s2, s3, s4, s5, s6, s7⟩
      idxPlace := (AtPublicFiles.KeyK1.idx_alike (W₀ := AtPublicFiles.AtFiles.FullSizeMatrix) (Rc := (AtPublicFiles.AtFiles.protocolAtFiles files).EncodingRandomness) (X := Unit) hc).1.place
      wPlace := (AtPublicFiles.KeyK1.w_alike (Rc := (AtPublicFiles.AtFiles.protocolAtFiles files).EncodingRandomness) (X := Unit) hc
        AtPublicFiles.AtFiles.HonestTerm.matrixReader).1.place
      tables := { chain := rfl, indexMasks := rfl, vectorW := rfl, omega := rfl, fixed := fun _ _ => rfl
                  index := fun _ => rfl, committed := fun _ => rfl }
      omegaReads := ProofFile.Honest.K12.AtKeyOwn.omegaReads_pinned hc
      wReads := ProofFile.Honest.K12.AtKeyOwn.wReads_pinned hc AtPublicFiles.AtFiles.HonestTerm.matrixReader }

/-- The thread's table at the three sources, at a state: the texts of TablesAreLaid. -/
theorem tableAt_idx (k : Coins (keyBook K₀))
    (m : Mid (Local AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles files).EncodingRandomness VerifiableInference.Desc.Key.Xi Unit) Unit) :
    (threadOwnP3 files D K₀).tableAt (.taken 0 0) k m =
      K1.treeTbl 0 id (lotK files D).idx (lotK files D).own₀ 0 k m.st.input
        (m.st.heard.take (AtPublicFiles.KeyThread.sentIn (AtPublicFiles.KeyThread.decl₁ (descriptionFromSource D.source D.numbers D.later)) 0)) := rfl

theorem tableAt_w (k : Coins (keyBook K₀))
    (m : Mid (Local AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles files).EncodingRandomness VerifiableInference.Desc.Key.Xi Unit) Unit) :
    (threadOwnP3 files D K₀).tableAt (.taken 0 5) k m =
      K1.treeTbl 0 id (lotK files D).w (lotK files D).own₀ 0 k m.st.input
        (m.st.heard.take (AtPublicFiles.KeyThread.sentIn (AtPublicFiles.KeyThread.decl₁ (descriptionFromSource D.source D.numbers D.later)) 5)) := rfl

theorem tableAt_omega (k : Coins (keyBook K₀))
    (m : Mid (Local AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles files).EncodingRandomness VerifiableInference.Desc.Key.Xi Unit) Unit) :
    (threadOwnP3 files D K₀).tableAt (.taken 1 1) k m =
      K14.sendTable (K14.jobOmega ⟨(lotK files D).send.P, 0⟩)
        (K14.witOf (lotK files D).send.P (lotK files D).weights fun r => AtPublicFiles.KeyFile.randK14 ((lotK files D).rand r))
        (K14.sendPlace 5) 1 0 k (AtPublicFiles.KeyDoorItems.commonOf m.st.input)
        ((m.st.heard.take ((AtPublicFiles.KeyThread.decl₁ (descriptionFromSource D.source D.numbers D.later)).length +
            AtPublicFiles.KeyThread.sentIn (AtPublicFiles.KeyThread.decl₂ (descriptionFromSource D.source D.numbers D.later)) 1)).drop
          (AtPublicFiles.KeyThread.decl₁ (descriptionFromSource D.source D.numbers D.later)).length) := rfl

/-- One tree: from TakenIs and a table at hand that shows the thread's. -/
theorem one_tree {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb) (k : Coins Bk) (m : Mid W X)
    (T₀ : List Tree) (i : ℕ) (σ : Fmt.TreeSource) (I : ProofFile.Honest.K12.AtFile.TakenIs T k m T₀ i σ) (E : Env)
    (tb : VerifiableInference.Desc.Place × Table) (e : T.tableAt σ k m = tb)
    (h : ∃ u, E.tree σ = some u ∧ u.2.same tb.2 = true) :
    ∃ (u : VerifiableInference.Desc.Place × Table) (Tb : Table), E.tree σ = some u ∧ u.2.same Tb = true ∧
      Tb.logLength = (T₀.getD i (0, fun _ => [])).1 ∧
      ∀ x, x < 2 ^ Tb.logLength → Tb.col x = (T₀.getD i (0, fun _ => [])).2 x := by
  subst e
  obtain ⟨u, hu, hs⟩ := h
  exact ⟨u, _, hu, hs, I.depth.symm, fun x hx => I.col x (by rw [I.depth]; exact hx)⟩

set_option maxHeartbeats 1000000 in
/-- **LOT P3, at the last chain's own V.** -/
theorem lot_p3
    (k : Coins (keyBook K₀))
    (m : Mid (Local AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles files).EncodingRandomness VerifiableInference.Desc.Key.Xi Unit) Unit)
    (E : Env)
    (c : RowCoins [(firstPart (lotJob files D).toRun.toTest :
        Part (AtPublicFiles.KeyFile.In1 AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles files).EncodingRandomness)
          (Local AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles files).EncodingRandomness VerifiableInference.Desc.Key.Xi Unit) Unit),
      restPart (lotJob files D).toRun.toTest]) :
    LotOldAtOwnTest files D K₀ k m E c := by
  intro hZ _ h hK hp hl hTab
  have G := ground_p3 (files := files) (D := D) hZ h hK hp
  have I := takenAtTheOwnTest _ _ _ _ _ _ _ _ _ K₀ (threadOwnP3 files D K₀) (lotK files D) D.source D.numbers D.later
    AtPublicFiles.KeyDoorItems.commonOf G k m c hl
  have I0 : ProofFile.Honest.K12.AtFile.TakenIs (threadOwnP3 files D K₀) k m _ 0 (.taken 0 0) := I 0 (by decide)
  have I1 : ProofFile.Honest.K12.AtFile.TakenIs (threadOwnP3 files D K₀) k m _ 1 (.taken 0 5) := I 1 (by decide)
  have I2 : ProofFile.Honest.K12.AtFile.TakenIs (threadOwnP3 files D K₀) k m _ 2 (.taken 1 1) := I 2 (by decide)
  have J0 := one_tree _ k m _ 0 _ I0 E _ (tableAt_idx k m) hTab.idx
  have J1 := one_tree _ k m _ 1 _ I1 E _ (tableAt_w k m) hTab.wTree
  have J2 := one_tree _ k m _ 2 _ I2 E _ (tableAt_omega k m) hTab.omega
  clear I I0 I1 I2 G hTab hl
  refine ProofFile.Honest.K12.AtKeyOwn.oldAt_of_tables E _ [.taken 0 0, .taken 0 5, .taken 1 1] ?_ ?_ ?_
  · exact Nat.le_refl 3
  · intro σ hσ n
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hσ
    rcases hσ with rfl | rfl | rfl <;> exact fun h => nomatch h
  · intro i hi
    have hi3 : i < 3 := hi
    obtain rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    · exact J0
    · exact J1
    · exact J2

end AtPublicFiles.KeyLastChain.Lots

#print axioms AtPublicFiles.KeyLastChain.Lots.ground_p3
#print axioms AtPublicFiles.KeyLastChain.Lots.lot_p3
