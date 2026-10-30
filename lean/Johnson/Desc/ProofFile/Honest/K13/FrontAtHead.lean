-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/FrontAtHead.lean: THE PREMISE `LayersFront`
(Johnson/Desc/K13/Honest/ClaimsIsAt.lean: three sentences on the state of the verifier's fold in
front of the layers' own sub-protocol) AT THE FIRST CHAIN OF THE PROOF FILE's IOP AS WRITTEN IN
LEAN, UNDER THE LIBRARY's ONE HYPOTHESIS AT THE FULL SIZE: TWO OF THE THREE ARE SHOWN: THE LEDGER's
SIZES; THE TOKENS. Statements with their proofs: calls.

THE LIBRARY HAS BOTH. `OnPublicFiles.sized_upTo` (Johnson/Desc/First/Look/K03RowsBare.lean): behind each
hearing sub-protocol of the 24 segments in front of the head's, from any state, the fold's state has
an open ledger with its three arrays at their length (`OnBytes.PscRun.Sized`); it is called at
segment 2 g and hearing sub-protocol 1: number 28 g + 4 stands behind that; so it is called in
Johnson/Road/K4/InT/WinsReached.lean (`kept_reached`: kin: of reached states). `Meaning.K2.flat_req`
(Johnson/LTPileR/ReqSeat.lean): every sub-protocol of the chain's list that passes its own test on
the plan leaves the request's words; kin there: `reach_req` (of reached states, with what the words
are). `S.tokv` (Johnson/Desc/First/State.lean) reads these words alone. That the chain and the
public data of `flat_req` are h's: as in the proof of the library's `K1.hlk_atAll`
(Johnson/Desc/K1/Law/LinksQuietAtAll.lean), by `Desc.K14.Law.Sh.first_inj`. `Keeps.foldBlocks_keeps`
(Johnson/Desc/FoldKeeps.lean), `P5J.flat_ok` (Johnson/P5J/FoldJ1.lean). All called.
Main names. Under h : `P5J.AtMgA`:
  `flat_req_head`, `fold_req_head`: every sub-protocol of cF.blocksInOrder, and so the fold over any front of
    that list from any state, leaves the request's words.
  `layersFront_of_tie`: **for g < 12 and any start: `LayersFront` at number 28 g + 4, at Szd :=
    `OnBytes.PscRun.Sized`, any Tie, tokOf x := the tokens of the start's own state `(start
    x).tokv`: FROM ITS SECOND SENTENCE ALONE** (tie: what the lookup returned, as the state holds
    it, stands in Tie to the instance and the challenges in front).

What is not claimed. The second sentence, at any Tie. That h holds at any public files. Nothing on
soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K13.SitesAtFlat
import Johnson.Desc.First.Look.K03RowsBare
import Johnson.LTPileR.ReqSeat
import Johnson.Desc.K1.Law.LinksQuietAtAll
import Johnson.P5J.FoldJ1

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K13
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain foldBlocks)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Keeps (Decides)
open VerifiableInference.Desc.K13.Honest (LayersFront roundsAhead)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- Every sub-protocol of the chain's list leaves the request's words. -/
theorem flat_req_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∀ b ∈ cF.blocksInOrder, Decides (fun s t : S => t.req = s.req) b := by
  obtain ⟨Z', A', B', c', h1, h2, k⟩ := Meaning.K2.flat_req h.laid.value
  obtain rfl : Z' = Zp := Except.ok.inj (h1.symm.trans h.laid.pub)
  obtain rfl : cF = c' := _root_.Desc.K14.Law.Sh.first_inj h2
  exact fun b hb => k b hb (P5J.flat_ok h.toAtMg b hb)

/-- So does the fold over any front of the list, from any state. -/
theorem fold_req_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (j : Nat) (s₀ : S)
    (rs : List Fmt.RoundView) (cols : List VerifiableInference.Desc.OpenedColumn)
    (q : S × List Fmt.RoundView × List VerifiableInference.Desc.OpenedColumn)
    (hf : foldBlocks 0 (cF.blocksInOrder.take j) s₀ rs cols = .ok q) : q.1.req = s₀.req :=
  VerifiableInference.Desc.Keeps.foldBlocks_keeps (fun s t : S => t.req = s.req) (fun _ => rfl)
    (fun _ _ _ a b => b.trans a) 0 (cF.blocksInOrder.take j)
    (fun b hb => flat_req_head h b (List.mem_of_mem_take hb)) s₀ rs cols q hf

/-- **TWO OF THE THREE SENTENCES ON THE FOLD's STATE IN FRONT OF THE LAYERS' OWN SUB-PROTOCOL ARE
SHOWN; THE THIRD IS LEFT.** -/
theorem layersFront_of_tie (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Xi : Type} (start : Xi → S)
    (g : Nat) (hg : g < 12) (Tie : Xi → List Fmt.Drawn → Forest.Heard → Prop)
    (htie : ∀ x rs cols sj c y fo,
      foldBlocks 0 (cF.blocksInOrder.take (28 * g + 4)) (start x) rs cols =
        .ok (sj, rs.drop (roundsAhead cF.blocksInOrder (28 * g + 4)), c) →
      sj.failed = none → sj.here = .lay y → y.fo = some fo →
      Tie x ((rs.take (roundsAhead cF.blocksInOrder (28 * g + 4))).map (·.drawn)) fo) :
    LayersFront cF.blocksInOrder start (28 * g + 4) OnBytes.PscRun.Sized Tie fun x => (start x).tokv where
  sized := fun x rs cols sj c y hf _ hy => by
    obtain ⟨Bs, base, O⟩ := h.laid.opened
    rw [show 28 * g + 4 = 14 * (2 * g) + 1 + 2 + 1 by omega] at hf
    obtain ⟨G, hG, sG⟩ := VerifiableInference.OnPublicFiles.sized_upTo h.scope h.reads O h.laid.planOk
      (2 * g) (by omega) 1 (by omega) hf
    have e : sj.fork? = some y.F := by simp [S.fork?, hy]
    obtain rfl : G = y.F := Option.some.inj (hG.symm.trans e)
    exact sG
  tie := htie
  tokens := fun x rs cols sj c hf _ => by
    have e : sj.req = (start x).req := fold_req_head h _ _ rs cols _ hf
    unfold S.tokv S.reqT
    rw [e]

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.flat_req_head
#print axioms ProofFile.Honest.K13.fold_req_head
#print axioms ProofFile.Honest.K13.layersFront_of_tie
