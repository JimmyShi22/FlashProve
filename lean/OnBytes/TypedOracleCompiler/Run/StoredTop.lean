-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/StoredTop.lean: the sibling's compiled verifier says yes, at the family `famXPd`, on
the typed string made from a chain that opens stored tables.
The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on
definitions of Compile/.

After OnBytes/Tie/StoredTop.lean (9 declarations, 449 lines). The evaluable form of the
compiled verifier (`verifyP`) goes in three steps: it recomputes the hash chain; it tests the strict
format of the typed string; it walks all openings to their roots and asks the protocol's own
verdict. This file takes the steps one by one, for the typed string that the sibling's typing makes
from what the strict reader has read, and puts them together. THE SIBLING'S PLAIN TIE IS NOT SAID
AGAIN: `pi_chain`, `strict_ind`, `rows_top`, `forests_ind`, `tree_roots`, `cnt_le`, `pi_sent`,
`pi_typed'` are used as they lie, through OnBytes/TypedOracleCompiler/Run/StoredChain.lean and OwnForests.lean. The
second half (from `typingX` on) is CUT AND TURNED BY PROGRAM.

AS TEXT, but for `_root_.` before `Fmt.` and some line breaks (3). `typedX`, `typingX`,
`exists_zip`.
TURNED (4).
 `strictX`          `some []` for `some none`; the trivial round's strict format is that of no tree,
                    as in the sibling's `strict_top`.
 `afterX`           the own trees' forests are had AT the interface with stored tables
                    (`forestsX_ind`), where the original maps them over from the plain case's; asked
                    beside the original's hypotheses: `hi` (the body of every own symbol is spelled
                    as the format spells its leaf) and `hns` (it is no stored symbol). The bound on
                    a check's depth goes through two folds, as in the sibling's `after_top`.
 `acceptX`          `some []` for `some none`; nothing else.
 `verifyX_true`     at every pd: asked is that the reader's digest is the pd of the family; the
                    verifier's embeddings of bodies are `embS` and `B.embE`; `hi` and `hns`.
NEW (1).
 `lxi_plains`       the library's text (Run/ParseLaxXIsProofs.lean), over the sibling's rounds'
                    data.
ELSEWHERE (2). `toLink` has no counterpart and `leaf_agree` is `famXPd_leaf_onl`:
OnBytes/TypedOracleCompiler/Run/OwnForests.lean.

WHAT IT IMPORTS FROM OUTSIDE THE SIBLING, through the files under it: seven files of
OnBytes/Tie/ (StoredRead, StoredLists, StoredWalk, TwoTrees, StoredExt, StoredGlue, StoredView),
none of OnBytes/Hash/ by the lists of imports; the library's Run/ParseLaxXIsProofs.lean
(`lxi_opensB`, `lxi_rootsB`).

WHAT IS NOT SAID. ONE DIRECTION: what was read and checked is accepted. No equation between the
verifier behind a parser and a formula on what a reader hands out. That what the strict reader has
read meets the hypotheses (`StoOK`, `StoredFact`, `LaxFacts`, the cut rc) is another file's:
OnBytes/TypedOracleCompiler/Run/StoredMain.lean (`stoOK_of`, `stored_core`). That any bodies meet `hi` and `hns`.
Nothing on soundness; no probability; nothing on any hash: O is any function on byte strings with
answers of 32 bytes, pd any bytes.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Run.StoredChain
import OnBytes.TypedOracleCompiler.Run.OwnForests
import OnBytes.TypedOracleCompiler.Run.StoredExt
import OnBytes.TypedOracleCompiler.Run.PageIsAfterTop
import OnBytes.TypedOracleCompiler.Run.StoredGlue
import OnBytes.TypedOracleCompiler.Run.StoredView
import OnBytes.TypedOracleCompiler.Run.PageIsTopProofs
import Run.ParseLaxXIsProofs

set_option autoImplicit false

namespace TypedOracleCompiler.Run.PQ
open Rom TypedOracleCompiler.Iop _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Run.Twin
  TypedOracleCompiler.Run.Thin
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ TypedOracleCompiler.Run
open _root_.Run.Twin (allLo)
open OnBytes.Tie (tabsOf readOf askedOf StoOK roundWithStoredOpenings StoredFact offStored_rounds storedB_eq)

/-- The typing of plain parts does not look at the vertices met. The library's text
(Run/ParseLaxXIsProofs.lean), over the sibling's rounds' data. -/
theorem lxi_plains (C : CK) :
    ∀ (ds : List RD) (l : List _root_.Fmt.RoundOut),
      plainsSL C ds (l.map stripR) = plainsSL C ds l
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | d :: ds, o :: os => by
      show (match PlainOf.ofGots d.items o.vals, plainsSL C ds (os.map stripR) with
        | some p, some r => some (GPlain.mk d.entry.work p o.nonce, r)
        | _, _ => none) = _
      rw [lxi_plains C ds os]
      rfl

section
variable (D : XD) (dec : View → Bool) (O : ByteArray → ByteArray) (hO : ∀ s, (O s).size = 32)

/-- The typed string: that of the plain case, with the stored tables' openings. -/
def typedX (run : ByteArray) (oo : _root_.Fmt.ChainOut) (pl : Plains (uL D.C D.ds))
    (sto : List (Bool × ℕ × OpenB)) : OneProtocolProof 256 (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).up :=
  { mkBPrfP (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec) run (rootsB oo) ((), pl)
      (opensAt (TYX D.base.plan.salt D.C D.ds D.a D.xs dec).up run oo) with
    ext := extOf D.a D.base.cfg (tabsOf sto) }

include hO in
/-- The strict format holds on the typed string `typedX`, if: O's answers and the configuration's
digest have 32 bytes; the chain's own part oo has the library's `LaxFacts` within the sibling's
limits, and the run value run; ρ holds the draws of oo's rounds; the stored tables' openings sto
have `StoOK`; and they list what the draws ask of the tables (hx). -/
theorem strictX (r0 r1 : ByteArray) (hok : PQ.ok D.base = true) (hc : D.base.cfg.size = 32)
    (oo : _root_.Fmt.ChainOut) (run : ByteArray) (pl : Plains (uL D.C D.ds))
    (ρ : Rho (uL D.C D.ds))
    (v : Bits) (sto : List (Bool × ℕ × OpenB))
    (hf : LaxFacts (_root_.Fmt.HO O) D.base oo) (hr : oo.run = some run)
    (hd : drawnSL D.C D.ds ρ = oo.rounds.toList.map (·.drawn))
    (hs : StoOK O D.base.cfg D.a D.base.plan.salt r0 r1 sto)
    (hx : xWanted D.a D.ds D.xs (drawnSL D.C D.ds ρ) = askedOf sto) :
    strictP (256 + 8 * D.base.plan.salt) 256 (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec)
      (wqX D.C D.K (chalP D.base.plan.field D.K) D.ds D.a D.xs dec) 0 ()
      (typedX D dec run oo pl sto) (default, ρ)
      ((none, some []), rtSL D.C D.ds oo.rounds.toList) (.loc v) = true := by
  have hrun := run_size O D.base hO oo run hf hr
  unfold strictP
  dsimp only
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · show decide ((bytesToBits run).length = 256) = true
    rw [length_bytesToBits, hrun]
    rfl
  · show decide (((rootsB oo).map bytesToDig).length
      ≤ 0 + 0 + cntP (SL D.C D.ds) (rtSL D.C D.ds oo.rounds.toList)) = true
    rw [cntP_rt D.C D.ds oo.rounds.toList (pi_sent _ D.base oo hok hf), List.length_map]
    exact decide_eq_true (Nat.le_of_eq (by simp only [Nat.zero_add]; rfl))
  · have := strict_ind D.C D.K (chalP D.base.plan.field D.K) (opensB oo) run D.base.plan.salt hrun
      D.ds oo.rounds.toList _ (rows_top (_root_.Fmt.HO O) D.base D.C dec oo ρ
        (effsP (PSof D.C D.ds dec).S (PSof D.C D.ds dec).ann
          ((none, some []), rtSL D.C D.ds oo.rounds.toList) ((), pl)) hok hf hd)
    show (sTreesP _ (s0 D.C) (fun _ _ => none) [] _ _ _ &&
        sTreesP _ (s0 D.C) (fun _ _ => none) [] _ _ _ &&
      sSP (256 + 8 * D.base.plan.salt) (SL D.C D.ds) (allLo (SL D.C D.ds))
        (wiresSL D.C D.K (chalP D.base.plan.field D.K) D.ds)
        (rtSL D.C D.ds oo.rounds.toList) _ _) = true
    rw [Bool.and_eq_true, Bool.and_eq_true]
    exact ⟨⟨rfl, rfl⟩, this⟩
  · have := ext_strict D O r0 r1 hc sto hs
    show sExtP (256 + 8 * D.base.plan.salt) (weX D.a)
      (fun p => decide (p ∈ ((xWanted D.a D.ds D.xs (drawnSL D.C D.ds ρ)).filterMap
        (xPos (2 ^ D.a))).toFinset)) (extOf D.a D.base.cfg (tabsOf sto)) = true
    rw [hx]
    exact this
  · rfl
  · rfl
  · rfl

/-- The sibling's typing of a chain output o gives `typedX`, if: o's rounds are rc with each round's
stored openings joined in, and oo's are rc's own parts without the vertices met; each round has as
many stored openings as the description says; o has a run value; oo's plain parts are typed as pl;
oo's own openings pass the typing's test; and the stored openings have `StoOK`. -/
theorem typingX (r0 r1 : ByteArray) (o oo : _root_.Fmt.ChainOut) (run : ByteArray)
    (pl : Plains (uL D.C D.ds))
    (rc : List (_root_.Fmt.RoundOut × List (_root_.Fmt.Shape × List ℕ × _root_.Fmt.OpenOut)))
    (ho : o.rounds.toList = rc.map roundWithStoredOpenings) (hoo : oo.rounds.toList = rc.map fun p => stripR p.1)
    (hl : List.Forall₂ (fun (ts : List _root_.Fmt.Stored)
      (p : _root_.Fmt.RoundOut × List (_root_.Fmt.Shape × List ℕ × _root_.Fmt.OpenOut)) =>
        ts.length = p.2.length)
      D.stored rc)
    (hr : o.run = some run) (hpl : plainsSL D.C D.ds oo.rounds.toList = some pl)
    (hob : (opensB oo).all (fun y => y.2.2.ok D.base.plan.salt y.2.1) = true)
    (hs : StoOK O D.base.cfg D.a D.base.plan.salt r0 r1 (storedB D.xs o)) :
    toBPrfX D.base.plan.salt D.base.cfg D.C D.ds D.a D.xs dec o
      = some (typedX D dec run oo pl (storedB D.xs o)) := by
  have e1 : oo.rounds.toList = (offStored D.xs o).rounds.toList.map stripR := by
    rw [hoo, xs_eq, offStored_rounds D.stored o rc ho hl, List.map_map]
    rfl
  have hB : opensB oo = opensB (offStored D.xs o) := lxi_opensB _ _ e1
  have hR : rootsB oo = rootsB (offStored D.xs o) := lxi_rootsB _ _ e1
  have hP : plainsSL D.C D.ds (offStored D.xs o).rounds.toList = some pl := by
    rw [← lxi_plains, ← e1]
    exact hpl
  have hall : (storedB D.xs o).all (fun x => x.2.2.ok D.base.plan.salt x.2.1 && x.2.2.a == D.a)
      = true := by
    rw [List.all_eq_true]
    intro e he
    rw [Bool.and_eq_true, hs.ok e he, hs.depth e he]
    exact ⟨rfl, beq_self_eq_true _⟩
  have hT : toBPrfP (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec) (TYX D.base.plan.salt D.C D.ds D.a D.xs dec)
      (offStored D.xs o) = some ([bytesToDig o.pd],
        mkBPrfP (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec) run (rootsB oo) ((), pl)
          (opensAt (TYX D.base.plan.salt D.C D.ds D.a D.xs dec).up run oo)) := by
    rw [parseThin_to]
    refine (parseLaws_some (TYX D.base.plan.salt D.C D.ds D.a D.xs dec).up _ _).2
      ⟨run, ((), pl), hr, ?_, ?_, ?_⟩
    · show (plainsSL D.C D.ds (offStored D.xs o).rounds.toList).map (fun r => ((), r))
        = some ((), pl)
      rw [hP]
      rfl
    · rw [← hB]
      exact hob
    · rw [hR]
      have : opensAt (TYX D.base.plan.salt D.C D.ds D.a D.xs dec).up run oo
          = opensAt (TYX D.base.plan.salt D.C D.ds D.a D.xs dec).up run (offStored D.xs o) := by
        funext p
        unfold opensAt
        rw [hB]
      rw [this]
      rfl
  unfold toBPrfX
  rw [if_pos hall, hT]
  rfl

/-- A member of the first list has a partner in a second list no shorter. -/
theorem exists_zip {α β : Type} : ∀ (l1 : List α) (l2 : List β) (x : α), x ∈ l1 →
    l1.length ≤ l2.length → ∃ c, (x, c) ∈ l1.zip l2
  | [], _, _, h, _ => by cases h
  | _ :: _, [], _, _, h => by simp at h
  | a :: l1, b :: l2, x, h, hl => by
    rcases List.mem_cons.1 h with rfl | h'
    · exact ⟨b, by simp⟩
    · obtain ⟨c, hc⟩ := exists_zip l1 l2 x h' (by simpa using hl)
      exact ⟨c, by rw [List.zip_cons_cons]; exact List.mem_cons_of_mem _ hc⟩

/-- The protocol's own verdict on the typed transcript is yes, if the decision says yes on the view
of o (hdec), all work passes (hpass), every part of the draws is full (hfull), all tables have the
depth `D.a` and are items 0 or 1 (hD), and o, oo, rc, ρ and the stored openings are as in `typingX`
and `strictX`, each stored opening with `StoredFact`. -/
theorem acceptX (r0 r1 : ByteArray) (hok : PQ.ok D.base = true) (o oo : _root_.Fmt.ChainOut)
    (run : ByteArray) (pl : Plains (uL D.C D.ds)) (ρ : Rho (uL D.C D.ds))
    (hL : LaxFacts (_root_.Fmt.HO O) D.base oo) (hpl : plainsSL D.C D.ds oo.rounds.toList = some pl)
    (hd : drawnSL D.C D.ds ρ = oo.rounds.toList.map (·.drawn))
    (rc : List (_root_.Fmt.RoundOut × List (_root_.Fmt.Shape × List ℕ × _root_.Fmt.OpenOut)))
    (hoo : oo.rounds.toList = rc.map fun p => stripR p.1) (ho : o.rounds.toList = rc.map roundWithStoredOpenings)
    (hS : List.Forall₂ (fun (ts : List _root_.Fmt.Stored)
        (p : _root_.Fmt.RoundOut × List (_root_.Fmt.Shape × List ℕ × _root_.Fmt.OpenOut)) =>
      List.Forall₂ (StoredFact (_root_.Fmt.HO O) D.base.cfg D.base.statement p.1.drawn.poss) ts p.2)
      D.stored rc)
    (hD : ∀ s ∈ D.stored.flatten, s.sh.a = D.a ∧ s.item ≤ 1)
    (hs : StoOK O D.base.cfg D.a D.base.plan.salt r0 r1 (storedB D.xs o))
    (hpass : passSL D.C D.ds ρ = true) (hfull : everyOpeningHasItsDraws D.xs (drawnSL D.C D.ds ρ) = true)
    (hx : xWanted D.a D.ds D.xs (drawnSL D.C D.ds ρ) = askedOf (storedB D.xs o))
    (hdec : dec (_root_.Fmt.viewX ⟨D.base, D.stored⟩ o) = true) :
    (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).accept ()
        ((weX D.a).build fun p =>
          (extOf D.a D.base.cfg (tabsOf (storedB D.xs o)) p).map Opening.sym)
        (trP (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).S (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).ann
          (wqX D.C D.K (chalP D.base.plan.field D.K) D.ds D.a D.xs dec).sh
          ((none, some []), rtSL D.C D.ds oo.rounds.toList) ((), pl) (default, ρ)
          (opensAt (TYX D.base.plan.salt D.C D.ds D.a D.xs dec).up run oo)) = true := by
  have hl : List.Forall₂ (fun (ts : List _root_.Fmt.Stored)
      (p : _root_.Fmt.RoundOut × List (_root_.Fmt.Shape × List ℕ × _root_.Fmt.OpenOut)) =>
        ts.length = p.2.length)
      D.stored rc := hS.imp fun _ _ hh => hh.length_eq
  have hcar : symbolsCarryTheirPositions D.a D.ds D.xs (drawnSL D.C D.ds ρ)
      ((weX D.a).build fun p =>
        (extOf D.a D.base.cfg (tabsOf (storedB D.xs o)) p).map Opening.sym) = true := by
    unfold symbolsCarryTheirPositions
    rw [hx, List.all_eq_true]
    intro wx hwx
    obtain ⟨e, he, hw⟩ := List.mem_flatMap.1 hwx
    obtain ⟨x, hxe, rfl⟩ := List.mem_map.1 hw
    obtain ⟨col, hcol⟩ := exists_zip e.2.2.idx e.2.2.cols x hxe
      (le_of_eq (TieTree.ok_spec _ _ _ (hs.ok e he)).1.symm)
    obtain ⟨p, hp, hrd⟩ := ext_symbol D O r0 r1 _ hs e he x col hcol
    rw [hp]
    show (((twoExternalStrings (2 ^ D.a) SgX).rd _ p).1 == x) = true
    rw [hrd]
    exact beq_self_eq_true x
  have hview := viewX_eq (_root_.Fmt.HO O) D D.K (chalP D.base.plan.field D.K) hok oo o run pl ρ hL
    hpl hd
    rc hoo ho hS hD
    ((weX D.a).build fun p => (extOf D.a D.base.cfg (tabsOf (storedB D.xs o)) p).map Opening.sym)
    (fun tp htp tz htz xc hxc => ext_symbol D O r0 r1 _ hs
      (tz.1.item == 1, tz.2.1.W, obOf tz.2) (by
        rw [xs_eq, storedB_eq D.stored o rc ho hl]
        exact List.mem_flatMap.2 ⟨tp, htp, List.mem_map.2 ⟨tz, htz, rfl⟩⟩) xc.1 xc.2 hxc)
  show (passSL D.C D.ds (rhoSL D.C D.ds (trL D.C D.K (chalP D.base.plan.field D.K) D.ds
        (rtSL D.C D.ds oo.rounds.toList) pl ρ (opL D.C (opensB oo) run D.ds))) &&
      everyOpeningHasItsDraws D.xs (drawnSL D.C D.ds (rhoSL D.C D.ds (trL D.C D.K (chalP D.base.plan.field D.K) D.ds
                          (rtSL D.C D.ds oo.rounds.toList) pl ρ (opL D.C (opensB oo) run D.ds)))) &&
      symbolsCarryTheirPositions D.a D.ds D.xs (drawnSL D.C D.ds (rhoSL D.C D.ds (trL D.C D.K
                          (chalP D.base.plan.field D.K) D.ds (rtSL D.C D.ds oo.rounds.toList) pl ρ
                          (opL D.C (opensB oo) run D.ds)))) _ &&
      dec (PQ.viewX D.C D.ds D.a D.xs _ (trL D.C D.K (chalP D.base.plan.field D.K) D.ds
        (rtSL D.C D.ds oo.rounds.toList) pl ρ (opL D.C (opensB oo) run D.ds)))) = true
  rw [rhoSL_tr, hpass, hfull, hcar, hview, hdec]
  rfl

variable {Bd : Type} (B : BodyD Bd) (pd : ByteArray)
  (embS : (p : OPos (Twin.up (SOf D.C D.ds))) → OSym (Twin.up (SOf D.C D.ds)) p → Bd)

include hO in
/-- What follows the chain, at `famXPd`. Under the hypotheses of `strictX`, if also r0 and r1
have 32 bytes, all own openings walk to their roots (hroots), sto lists no more places than the
parts of the draws have (hcnt), the body of every own symbol is spelled as the format spells its
leaf (hi) and is no stored symbol (hns), then all walks end in their roots, so the verdict is the
protocol's own. -/
theorem afterX (r0 r1 : ByteArray) (h0 : r0.size = 32) (h1 : r1.size = 32)
    (hok : PQ.ok D.base = true) (hc : D.base.cfg.size = 32)
    (hi : ∀ p a, B.own (embS (.inr p) a) = some (leafSL D.C D.base.plan.salt D.ds ⟨p, a⟩))
    (hns : ∀ p a, B.getE (embS (.inr p) a) = none)
    (oo : _root_.Fmt.ChainOut) (run : ByteArray) (pl : Plains (uL D.C D.ds))
    (ρ : Rho (uL D.C D.ds))
    (v : Bits) (sto : List (Bool × ℕ × OpenB))
    (hf : LaxFacts (_root_.Fmt.HO O) D.base oo) (hr : oo.run = some run)
    (hd : drawnSL D.C D.ds ρ = oo.rounds.toList.map (·.drawn))
    (hroots : rootsAll (_root_.Fmt.HO O) D.base.cfg run oo.rounds.toList = true)
    (hs : StoOK O D.base.cfg D.a D.base.plan.salt r0 r1 sto)
    (hx : xWanted D.a D.ds D.xs (drawnSL D.C D.ds ρ) = askedOf sto)
    (hcnt : (sto.map (·.2.2.idx.length)).sum ≤ (D.xs.map (·.count)).sum) :
    afterP (fun _ => D.L Bd dec) (famXPd B D dec pd O (D.K + 1)) (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec)
      (wqX D.C D.K (chalP D.base.plan.field D.K) D.ds D.a D.xs dec)
      embS B.embE 0
      [bytesToDig r0, bytesToDig r1] () (typedX D dec run oo pl sto) (default, ρ)
      ((none, some []), rtSL D.C D.ds oo.rounds.toList) (.loc v)
    = (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).accept ()
        ((weX D.a).build fun p => (extOf D.a D.base.cfg (tabsOf sto) p).map Opening.sym)
        (trP (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).S (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).ann
          (wqX D.C D.K (chalP D.base.plan.field D.K) D.ds D.a D.xs dec).sh
          ((none, some []), rtSL D.C D.ds oo.rounds.toList) ((), pl) (default, ρ)
          (opensAt (TYX D.base.plan.salt D.C D.ds D.a D.xs dec).up run oo)) := by
  have hrun := run_size O D.base hO oo run hf hr
  have hsS := strict_ind D.C D.K (chalP D.base.plan.field D.K) (opensB oo) run D.base.plan.salt hrun
      D.ds oo.rounds.toList _ (rows_top (_root_.Fmt.HO O) D.base D.C dec oo ρ
        (effsP (PSof D.C D.ds dec).S (PSof D.C D.ds dec).ann
          ((none, some []), rtSL D.C D.ds oo.rounds.toList) ((), pl)) hok hf hd)
  obtain ⟨Fs, g1, g2, g3, g4⟩ := forestsX_ind B D dec pd O D.C D.K (chalP D.base.plan.field D.K)
    (opensB oo) run
    D.base.plan.salt hO hrun D.ds oo.rounds.toList _ (fun p a => embS (.inr p) a)
    (rows_top (_root_.Fmt.HO O) D.base D.C dec oo ρ
        (effsP (PSof D.C D.ds dec).S (PSof D.C D.ds dec).ann
          ((none, some []), rtSL D.C D.ds oo.rounds.toList) ((), pl)) hok hf hd) hi hns
    (256 + 8 * D.base.plan.salt) hsS
  obtain ⟨Fx, x1, x2, x3, x4⟩ := ext_forest B D dec pd O hO r0 r1 h0 h1 hc sto hs
  have hFo : forestsOfP (fun _ => D.L Bd dec) (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec)
      (wqX D.C D.K (chalP D.base.plan.field D.K) D.ds D.a D.xs dec)
      embS B.embE
      [bytesToDig r0, bytesToDig r1] () (typedX D dec run oo pl sto) (default, ρ)
      ((none, some []), rtSL D.C D.ds oo.rounds.toList)
      = some (Fs ++ [Fx]) := by
    have x1' : forestExtP (fun _ => D.L Bd dec) (weX D.a) B.embE
        [bytesToDig r0, bytesToDig r1]
        (fun p => decide (p ∈ ((xWanted D.a D.ds D.xs (drawnSL D.C D.ds ρ)).filterMap
          (xPos (2 ^ D.a))).toFinset)) (extOf D.a D.base.cfg (tabsOf sto)) = some [Fx] := by
      rw [hx]
      exact x1
    unfold forestsOfP
    dsimp only
    split
    · rename_i a b e1 e2
      have ea : a = Fs :=
        Option.some.inj (e1.symm.trans
          (forestsP_front D.C D.K (chalP D.base.plan.field D.K) D.ds _ _ _ _ Fs g1))
      have eb : b = [Fx] := Option.some.inj (e2.symm.trans x1')
      rw [ea, eb]
    · rename_i hne
      exact (hne _ _ (forestsP_front D.C D.K (chalP D.base.plan.field D.K) D.ds _ _ _ _ Fs g1)
        x1').elim
  have hlen : (flatP (fun _ => D.L Bd dec) (Fs ++ [Fx])).length
      ≤ nOpen D.ds + (D.xs.map (·.count)).sum := by
    rw [flatP_append, List.length_append, g2, x2]
    exact Nat.add_le_add (cnt_le _ D.base oo hok hf) hcnt
  have hall : (flatP (fun _ => D.L Bd dec) (Fs ++ [Fx])).all
      (fun c => wellP (fun _ => D.L Bd dec) c && decide (c.depth ≤ max (maxDepth D.ds) D.a))
      = true := by
    rw [flatP_append, List.all_append, Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
    refine ⟨fun c hc => ?_, fun c hc => ?_⟩
    · obtain ⟨w, d, hdm, sh, hsh, hdd⟩ := g3 c hc
      rw [Bool.and_eq_true]
      refine ⟨w, decide_eq_true ?_⟩
      rw [hdd]
      exact le_trans (le_trans (le_depthOf d.trees sh.a (List.mem_map_of_mem hsh))
        ((foldl_max_le (fun d : RD => depthOf d.trees) D.ds 0).2 d hdm)) (le_max_left _ _)
    · obtain ⟨w, hdd⟩ := x3 c hc
      rw [Bool.and_eq_true]
      exact ⟨w, decide_eq_true (by rw [hdd]; exact le_max_right _ _)⟩
  have hrd : readsP (fun _ => D.L Bd dec) (Fs ++ [Fx])
      = readsP (fun _ => D.L Bd dec) Fs ++ (readsOneP (fun _ => D.L Bd dec) Fx ++ []) := by
    unfold readsP
    rw [List.flatMap_append]
    rfl
  unfold afterP
  rw [hFo]
  dsimp only
  rw [if_pos ⟨hlen, hall⟩, hrd, g4, treeAll_onl,
    tree_roots Bd B.own O D.base D.C dec oo run hok hf, hroots,
    runForestsP_cons (fun _ => D.L Bd dec) (famXPd B D dec pd O (D.K + 1)) Fx [] [], x4]
  rfl

include hO in
/-- All parts together, at `famXPd`. If the decision says yes on the view of o (hdec), then the
sibling's typing of o gives a string, and the evaluable form of the sibling's compiled verifier says
yes on it. The other hypotheses are bounds, limits on the description, what is asked of bodies, and
what the strict reader has checked of o: O's answers, r0, r1 and the configuration's digest have 32
bytes; the own part is within the sibling's limits; the statement is `D.stm r0 r1`; the body of
every own symbol is spelled as the format spells its leaf (hi) and is no stored symbol (hns); o is
rc with the stored openings joined in, oo its own part, both with the run value run; oo has
`LaxFacts`, its `pd` is the pd of the family, all its work has passed and all its own openings have
walked to their roots; each stored opening has `StoredFact`, all have `StoOK`, one depth and items 0
or 1; and every part of the draws is full. -/
theorem verifyX_true (r0 r1 : ByteArray) (h0 : r0.size = 32) (h1 : r1.size = 32)
    (hok : PQ.ok D.base = true) (hst : D.base.statement = D.stm r0 r1)
    (hc : D.base.cfg.size = 32)
    (hi : ∀ p a, B.own (embS (.inr p) a) = some (leafSL D.C D.base.plan.salt D.ds ⟨p, a⟩))
    (hns : ∀ p a, B.getE (embS (.inr p) a) = none) (o oo : _root_.Fmt.ChainOut)
    (run : ByteArray)
    (rc : List (_root_.Fmt.RoundOut × List (_root_.Fmt.Shape × List ℕ × _root_.Fmt.OpenOut)))
    (hoo : oo.rounds.toList = rc.map fun p => stripR p.1) (ho : o.rounds.toList = rc.map roundWithStoredOpenings)
    (hr : o.run = some run) (hrr : oo.run = some run)
    (hL : LaxFacts (_root_.Fmt.HO O) D.base oo) (hpd : oo.pd = pd)
    (hpass : passL (_root_.Fmt.HO O) D.base.rounds oo.rounds.toList ⟨D.base.label, oo.rho0, 0⟩ =
      true)
    (hroots : rootsAll (_root_.Fmt.HO O) D.base.cfg run oo.rounds.toList = true)
    (hS : List.Forall₂ (fun (ts : List _root_.Fmt.Stored)
        (p : _root_.Fmt.RoundOut × List (_root_.Fmt.Shape × List ℕ × _root_.Fmt.OpenOut)) =>
      List.Forall₂ (StoredFact (_root_.Fmt.HO O) D.base.cfg D.base.statement p.1.drawn.poss) ts p.2)
      D.stored rc)
    (hD : ∀ s ∈ D.stored.flatten, s.sh.a = D.a ∧ s.item ≤ 1)
    (hs : StoOK O D.base.cfg D.a D.base.plan.salt r0 r1 (storedB D.xs o))
    (hfull : everyOpeningHasItsDraws D.xs (oo.rounds.toList.map (·.drawn)) = true)
    (hdec : dec (_root_.Fmt.viewX ⟨D.base, D.stored⟩ o) = true) :
    ∃ π, toBPrfX D.base.plan.salt D.base.cfg D.C D.ds D.a D.xs dec o = some π ∧
      verifyP (fun _ => D.L Bd dec) (famXPd B D dec pd O (D.K + 1)) id none
        (256 + 8 * D.base.plan.salt) 256
        .link (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec)
        (wqX D.C D.K (chalP D.base.plan.field D.K) D.ds D.a D.xs dec)
        embS
        (embPX Bd D.C D.ds D.a D.xs dec (fun _ _ p => (p.val, [])) (fun _ => some ()))
        (fun _ => none) B.embE 0 [bytesToDig r0, bytesToDig r1] () π = true := by
  obtain ⟨run', pl, hr', hpl, -⟩ := pi_typed' (_root_.Fmt.HO O) D.base D.C dec oo hL
  obtain ⟨ρ, v, hch, hd, hp⟩ := chainX B D dec pd O hO r0 r1 hok hst h0 h1 oo run pl hL hpd hrr hpl
  have hl : List.Forall₂ (fun (ts : List _root_.Fmt.Stored)
      (p : _root_.Fmt.RoundOut × List (_root_.Fmt.Shape × List ℕ × _root_.Fmt.OpenOut)) =>
        ts.length = p.2.length)
      D.stored rc := hS.imp fun _ _ hh => hh.length_eq
  have hob : (opensB oo).all (fun y => y.2.2.ok D.base.plan.salt y.2.1) = true := by
    rw [List.all_eq_true]
    intro y hy
    obtain ⟨ro, hro, hy'⟩ := List.mem_flatMap.1 hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy'
    exact opens_ok (_root_.Fmt.HO O) D.base.plan D.base.rounds oo.rounds.toList _ _ hL.trace ro hro
      x hx
  have hx : xWanted D.a D.ds D.xs (drawnSL D.C D.ds ρ) = askedOf (storedB D.xs o) := by
    rw [hd]
    exact xWanted_asked (_root_.Fmt.HO O) D o rc ho hS hok oo hL hoo fun s hs' => (hD s hs').1
  refine ⟨typedX D dec run oo pl (storedB D.xs o),
    typingX D dec O r0 r1 o oo run pl rc ho hoo hl hr hpl hob hs, ?_⟩
  unfold verifyP
  have hch' : chainP (fun _ => D.L Bd dec) (famXPd B D dec pd O (D.K + 1)) id none .link
      [bytesToDig r0, bytesToDig r1] ((fun _ => none : Unit → Option Unit) ())
      (typedX D dec run oo pl (storedB D.xs o)).salt (typedX D dec run oo pl (storedB D.xs o)).rtreq
      (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).S (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).ann
      (wqX D.C D.K (chalP D.base.plan.field D.K) D.ds D.a D.xs dec).sh
      (embPX Bd D.C D.ds D.a D.xs dec (fun _ _ p => (p.val, [])) (fun _ => some ())) 0 .first
      (typedX D dec run oo pl (storedB D.xs o)).roots
      (typedX D dec run oo pl (storedB D.xs o)).plains
      = some ((default, ρ), ((none, some []), rtSL D.C D.ds oo.rounds.toList), .loc v) := hch
  rw [hch']
  dsimp only
  rw [strictX D dec O hO r0 r1 hok hc oo run pl ρ v _ hL hrr hd hs hx, if_pos rfl,
    afterX D dec O hO B pd embS r0 r1 h0 h1 hok hc hi hns oo run pl ρ v _ hL hrr hd hroots hs hx
      (sto_count (_root_.Fmt.HO O) D o rc ho hS)]
  exact acceptX D dec O r0 r1 hok o oo run pl ρ hL hpl hd rc hoo ho hS hD hs (hp.trans hpass)
    (by rw [hd]; exact hfull) hx hdec

end

end TypedOracleCompiler.Run.PQ
