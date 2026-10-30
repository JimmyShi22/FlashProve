-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Law.TabsView
import Johnson.Desc.K12.Law.AccKPlace
/-
Johnson/Desc/K12/Law/AccKHas.lean: accK HAS A YES WHEREVER Block.step OF proximityTestKind guardedProximityTestParts p SAYS YES AND SIX BOOLEANS HOLD: NO PREMISE IS LEFT THAT IS NOT A BOOLEAN WITH CODE, A NUMBER OF THE PLACE, OR THE STEP's OWN YES. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING. OF proximityTestKind guardedProximityTestParts p.
  tablesOfView   TablesOfView (Johnson/Desc/K12/Law/AccKPlace.lean) IS PAID: by tables_of_view (Johnson/Desc/K12/Law/TabsView.lean)
  accK_yes_real   early · answers = 1 · planOk · nzOk · dealOk · tieOk · logOk · canonOk of the rounds behind "BAT" · a yes of Block.step at a view (r0 :: rs', cols) ⇒ the place's chain c (k12_step_accH's five conjuncts) ∧ ∃ e row Ly S' D, gpL's yes ∧ FrontK p t0 a r0 e row Ly S' D ∧ ∃ W0 fM, DeepK D W0 fM ∧ ∃ τ that shows just the rounds rs' (the sealed digests apart), accK p F t0 r0 c D.ts (wAt c W0 D.fresh.t fM) τ = true ∧ THE VIEW's COLUMNS, AS MANY AS THE STEP WANTS, ARE τ's OWN WRITTEN COLUMNS (cols.take … = colsOf … (srcK p c (blOf c τ) D.ts …))
WHAT IT IS WORTH: «accK, the verifier in the lemma, says yes at some typed transcript wherever» THE STEP SAYS YES ON A VIEW AND THESE BOOLEANS HOLD. Each of them, and the step's yes, has said yes in runs at the four proximity tests of the smaller stored example proof: A RUN's WORD, AND NOT IN ONE RUN OVER ONE SET OF BYTES: nzOk · dealOk · tieOk · logOk · canonOk ran in a program of this project that is not in this repository, whose block has another text of the parts than this library's (none of the five reads the parts); planOk's and the step's yes ran in another such program, at the four tests of both stored proofs, over another build of the library than the one that ships: THAT ITS PARTS ARE THIS LIBRARY's IS NOT SHOWN; at the tiny place they ran of the other text of the parts alone; canonOk | logOk have run true at the full size too, their controls false.
AGAINST IT, FIRST: (1) THE LETTER fM THAT tables_of_view GIVES IS A CONSTANT (fun _ => W0 D.fresh.t): the first mask's table stands among W0's, whatever the first message. WHERE THE MASK IS THE TEST's OWN (sent in the chain's first message) THE LAW IS SPENT AT fM := the first message's oracle: THAT ARM IS NOT SHOWN BY THIS THEOREM: «at some letters with DeepK», not «at the letters of the own mask's arm» (for that arm: Johnson/Desc/K12/Law/AccKOwn.lean, under six premises more) · (2) ONE ACCEPTING TRANSCRIPT IS NOT A PROVER THAT IS NOT DOOMED: k12_lemma_fwd's premise «¬ Doomed …» wants a whole tree of accepting transcripts (completeness's): NOT SHOWN TO HAVE A MEMBER · (3) the tests of work pass at τ because its bits of work are laid as zeros: nothing on a search · (4) the blocks of τ are any blocks, its oracles tables made off the opened columns: THE ORACLE MODEL: that a view from bytes comes from ONE committed table a tree is the Merkle trees' binding: NOT HERE · (5) no completeness; no level of security; NO SENTENCE ON BITS TO A PERSON.
EVERY THEOREM OF THIS FILE IS PROVED OUTRIGHT: nothing is left open and nothing is laid down by decree; what each rests on is printed at the file's end.
-/
set_option autoImplicit false
namespace H2K.JointK
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open Iop Prob Cb Cb.Ood _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Pub (Letters sgOf WR writtenOf)
open H2K.First (gpOf gpL Plain nzOk dealOk tieOk canonOk logOk)

theorem tablesOfView : TablesOfView :=
  fun p F a rest _ c w0 ws t row L D h1 h2 h3 h4 h5 h6 h7 h8 h9 r0 rs' cols hf =>
    H2K.First.tables_of_view p F a rest c w0 ws t row L D h1 h2 h3 h4 h5 h6 h7 h8 h9 r0 rs' cols hf


theorem accK_yes_real (X : Letters) (p : P12) (he : p.early = true)
    (ha : p.answers = 1) (t0 : T12) (hp : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true)
    (hnz : nzOk p = true) (hdeal : dealOk p = true) (htie : tieOk p = true)
    (hlog : logOk p = true) (F : ℕ) (r0 : Fmt.RoundView) (rs' : List Fmt.RoundView) (cols : List OpenedColumn)
    (hcan : canonOk rs' = true) (tE : T12) (n : ℕ)
    (hstep : (proximityTestKind guardedProximityTestParts p : Blk').step F t0 (r0 :: rs') cols = .ok (tE, n)) :
    ∃ (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (w0 : WR) (l : List WR) (c : Chain (sgOf a)),
      p.nums.stages = a :: rest ∧ writtenOf p.nums = some (w0 :: l) ∧
      H2K.Pub.chainFrom X rest a l = some c ∧ c.rds = l.map WR.rd ∧
      stagesOf c = p.nums.stages ∧
      ∃ (e : Fmt.Entry) (row : GroupRow) (Ly : GroupLayout) (S' : Statement) (D : Plain),
        H2K.First.ok (gpL p a row D) = true ∧ FrontK p t0 a r0 e row Ly S' D ∧
        ∃ (W0 : ℕ → WO) (fM : H2K.Pub.Msg1 c → WO), DeepK D W0 fM ∧
          ∃ τ, (PQ.rvSL (ckP .two) c.rds τ).map noDigest = rs'.map noDigest ∧
            accK p F t0 r0 c D.ts (wAt c W0 D.fresh.t fM) τ = true ∧
            cols.take ((proximityTestKind guardedProximityTestParts p : Blk').want F (r0 :: rs')).length =
              colsOf (groupsOf F (proximityTestKind guardedProximityTestParts p : Blk').rounds ((r0 :: rs').map (·.drawn)))
                (srcK p c (blOf c τ) D.ts fun z x =>
                  colW (wAt c W0 D.fresh.t fM (blOf c τ) z).1
                    (wAt c W0 D.fresh.t fM (blOf c τ) z).2 x) :=
  accK_yes_place tablesOfView X p he ha t0 hp hnz hdeal htie hlog F r0 rs' cols hcan tE n hstep

end H2K.JointK

#print axioms H2K.JointK.tablesOfView
#print axioms H2K.JointK.accK_yes_real
