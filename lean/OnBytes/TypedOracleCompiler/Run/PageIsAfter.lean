-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/PageIsAfter.lean.
TWO: CUT BY PROGRAM out of the library's Run/PageIsAfter.lean (only what the entry's clause holds
and stands on a declaration that the sibling says again), then turned by hand where it had to be.
THE HEAD BELOW IS THE LIBRARY's AND SPEAKS OF THE LIBRARY's FILE: much of what it announces IS NOT
HERE, and what it says of "one root | one tree a round" is not true of this file. HERE STAND ONLY:
rows_top, cntP_rt, forestsP_front.

Run/PageIsAfter.lean: THE PROOF OF A PART OF THE PLAN OF Run/PageIs.lean: Spec.pi_after: ON THE
PARSER'S ARGUMENT STRING, GIVEN WHAT THE CHAIN YIELDS, THE STRICT FORMAT HOLDS, AND WHAT FOLLOWS THE
CHAIN IS "every opening walks to the root sent, the test bits pass, and dec says yes on the view of
what the lenient reader handed out". The statement stands in Run/PageIs.lean; here its proof.
   opens_ne             no opening of a trace has an empty list
   rows_top             Run/PageIsForest.lean's hypothesis round by round holds of what the lenient
                        reader hands out, "read" being the protocol's own set of positions read
                        (Run/PageIsRows.lean: rows_ind; Run/PageIsTabProofs.lean: pi_row, pi_sent)
   cntP_rt, run_size    the roots that the chain yields are as many as were read; the run's value
                        has 32 bytes
   strict_top       the first half: the first salt has 256 bits; no root is left over; an opening
                    stands only under a root, only where the verifier reads, with a salt of the
                    right length (strict_ind); no external opening, slot 0, no path
   forestsP_front       the trivial round in front makes no forest
   after_top        the second half: the forests (forests_ind); at most nOpen checks (cnt_le), of
                    depths at most maxDepth; the walks = treeAll = rootsAll (tree_roots); no request
                    tree before the chain has joined; the decision (Run/PageIsViewProofs.lean:
                    pi_view)
   pi_after
WHAT IS NOT SAID.  What the head of Run/PageIs.lean leaves out.

Terms: lean/GLOSSARY.md.

-/
import Run.PageIsAfter
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.PageIsForest
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.PageIsOp
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.PageIsTab
import OnBytes.TypedOracleCompiler.Run.PageIs   -- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.PlanQS   -- TWO: reached in the library through files that are not said again
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.PlanQSMore
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.PlanQTypes
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.CodingFn
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.ParseChain
import OnBytes.TypedOracleCompiler.Run.ParseBS  -- TWO: reached in the library through files that are not said again
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.CodingFnThin
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.CodingFnTag
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.TwinDefs
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.ThinDefs
import OnBytes.TypedOracleCompiler.Run.ThinTie  -- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.TwinDet  -- TWO: reached in the library through files that are not said again
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.VerifyDet
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.ThinTieProofs
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.TwinDetProofs
import OnBytes.TypedOracleCompiler.Run.TwinTie  -- TWO: reached in the library through files that are not said again
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.TwinTiePureProofs
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.TwinTiePure
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.VerifyDetProofs
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.ParseThin
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.ParseLaws
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.Toy1TieChecks
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.Toy1TieTree
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.CodingPage160
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.CodingPage164
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.PageIsTabProofs
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.PageIsReaders
import OnBytes.TypedOracleCompiler.Run.PageIsRows
import OnBytes.TypedOracleCompiler.Run.PageIsViewProofs
import OnBytes.TypedOracleCompiler.Run.PageIsTopProofs

set_option autoImplicit false

namespace TypedOracleCompiler.Run.PQ
open Rom TypedOracleCompiler.Iop _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Run.Twin
    TypedOracleCompiler.Run.Thin
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ TypedOracleCompiler.Run
open _root_.Run.Twin (allLo)
export _root_.Run.PQ (opens_ne run_size)
open _root_.Fmt (Chain RoundOut ChainOut OpenOut Plan Src)

section
variable (h : HId) (S : _root_.Fmt.Spec) (C : CK) (dec : View → Bool)

/-- the hypothesis round by round holds of what the lenient reader hands out, "read" being the
protocol's own set of positions read -/
theorem rows_top (o : ChainOut) (ρ : Rho (uL C (rds S))) (pls : Plains (up (SOf C (rds S))))
    (hok : ok S = true) (hf : LaxFacts h S o)
    (hd : drawnSL C (rds S) ρ = o.rounds.toList.map (·.drawn)) :
    RowsL C (opensB o) S.plan.salt (rds S) o.rounds.toList (fun q =>
      @decide (Sum.inr q ∈ (PSof C (rds S) dec).reads () (default, ρ) pls)
          (@Finset.decidableMem _ (decOS C (rds S)) _ _)) := by
  refine rows_ind C (opensB o) S.plan.salt
    (fun n y => (n, y) ∈ wanted (rds S) (o.rounds.toList.map (·.drawn))) (rds S) o.rounds.toList 0 _
    (pi_sent h S o hok hf) (fun n sh hs => ?_) fun q => ?_
  · rcases pi_row h S o hok hf n sh hs with ⟨x, row⟩ | bare
    · obtain ⟨ro, hro, hx⟩ := row.mem
      have hsh := row.shape
      subst hsh
      exact Or.inl
        ⟨obOf x, row.look, rfl,
          opens_ok h S.plan S.rounds o.rounds.toList _ _ hf.trace ro hro x hx,
          opens_ne h S.plan S.rounds o.rounds.toList _ _ hf.trace ro hro x hx,
          fun y => by rw [Nat.zero_add]; exact row.want y⟩
    · exact Or.inr ⟨bare.look, fun y => by rw [Nat.zero_add]; exact bare.want y⟩
  · rw [decide_eq_true_iff]
    show Sum.inr q ∈
        (((wanted (rds S) (drawnSL C (rds S) ρ)).filterMap fun nx =>
          (posAtS C (rds S) nx.1 nx.2).map fun p =>
            (Sum.inr p : OPos (Twin.up (SOf C (rds S)))))).toFinset ↔
      _
    rw [List.mem_toFinset, List.mem_filterMap, hd]
    constructor
    · rintro ⟨⟨n, y⟩, hw, hp⟩
      obtain ⟨q', hq', hq⟩ := Option.map_eq_some_iff.1 hp
      exact ⟨n, y, by rw [Nat.zero_add]; exact hw, by rw [hq', Sum.inr.inj hq]⟩
    · rintro ⟨n, y, hw, hp⟩
      exact ⟨(n, y),
        by rw [Nat.zero_add] at hw; exact hw,
        by show (posAtS C (rds S) n y).map _ = _; rw [hp]; rfl⟩

end

/-- the chain's roots, counted -/
theorem cntP_rt (C : CK) :
    ∀ (ds : List RD) (ros : List RoundOut), List.Forall₂ SentRel ds ros →
      cntP (SL C ds) (rtSL C ds ros) = (ros.flatMap fun ro => _root_.Fmt.rootsOf ro.vals).length
  | [], _, .nil => rfl
  | d :: ds, _, .cons (b := ro) (l₂ := ros) hs ht => by
    have ih := cntP_rt C ds ros ht
    show (0 + ((_root_.Fmt.rootsOf ro.vals).map bytesToDig).length +
        cntP (SL C ds) (rtSL C ds ros)) = _
    rw [ih, List.flatMap_cons, List.length_append, List.length_map, Nat.zero_add]

section
variable (O : ByteArray → ByteArray) (S : _root_.Fmt.Spec) (C : CK) (K : ℕ)
  (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (dec : View → Bool)

/-- the trivial round in front makes no forest -/
theorem forestsP_front {I X : Type} {L : BatchProtocolWithLeafBody I X} (ds : List RD)
    (emb : (p : OPos (up (SOf C ds))) → OSym (up (SOf C ds)) p → Body L) (rts : RootsOfChain 256 (uL C ds))
    (isRead : OPos (up (SOf C ds)) → Bool)
    (f : (p : OPos (up (SOf C ds))) → Option (Opening 256 (OSym (up (SOf C ds)) p)))
    (c : List (Forest 256 L))
    (hc : forestsP (fun _ => L) (SL C ds) (allLo (SL C ds)) (wiresSL C K chal ds)
        (fun p => emb (.inr p)) rts (fun p => isRead (.inr p)) (fun p => f (.inr p)) = some c) :
    forestsP (fun _ => L) (SOf C ds) (allLo (SOf C ds)) (wire0S C K chal, wiresSL C K chal ds) emb
        ((none, some []), rts) isRead f = some c := by
  simp only [forestsP]
  split
  · rename_i a b c' e1 e2 e3
    have ea : a = [] := Option.some.inj (e1.symm.trans rfl)
    have eb : b = [] := Option.some.inj (e2.symm.trans rfl)
    have ec : c' = c := Option.some.inj (e3.symm.trans hc)
    subst ea eb ec
    rfl
  · rename_i hne
    exact (hne [] [] c rfl rfl hc).elim

end

end TypedOracleCompiler.Run.PQ
