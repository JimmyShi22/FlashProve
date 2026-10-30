-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/StoredTop.lean: the compiled verifier says yes on the typed string made from a chain
that opens stored tables.

The evaluable form of the compiled verifier (`Run.Thin.verifyP`) goes in three steps: it recomputes
the hash chain; it tests the strict format of the typed string; it walks all openings to their roots
and asks the protocol's own verdict. This file takes the steps one by one, for the typed string that
the library's typing makes from what the strict reader has read, and puts them together. What is
assumed of what was read is proved of the strict reader's output in OnBytes/Tie/StoredRead.lean and
gathered in OnBytes/Tie/StoredMain.lean.

The chain's own trees are those of the plain case, without stored tables. The library's laws on them
are stated at another interface and tag and are carried over (by `toLink` below and the maps of
OnBytes/Tie/ForestMap.lean).
The two stored tables are the matter of OnBytes/Tie/StoredExt.lean, the view of
OnBytes/Tie/StoredView.lean.

Main definitions: `typedX`, `toLink`.
Main theorems: `strictX`, `afterX`, `typingX`, `acceptX`, `verifyX_true`.
It claims nothing on soundness.
-/
import Run.PageIsProofs
import Run.PlanQXRun
import OnBytes.Tie.StoredChain
import OnBytes.Tie.StoredLists
import OnBytes.Tie.StoredExt
import OnBytes.Tie.ForestMap
import OnBytes.Tie.StoredView
import OnBytes.Tie.StoredGlue
import OnBytes.Tie.StoredDom
import OnBytes.Tie.Limits

set_option autoImplicit false

namespace OnBytes.Tie
open Rom Iop Compile Compile.Batch Run Run.PQ Run.Twin Run.Thin

section
variable (D : XD) (dec : View → Bool) (O : ByteArray → ByteArray) (hO : ∀ s, (O s).size = 32)

/-- The typed string: that of the plain case, with the stored tables' openings. -/
def typedX (run : ByteArray) (oo : Fmt.ChainOut) (pl : Plains (uL D.C D.ds))
    (sto : List (Bool × ℕ × OpenB)) : OneProtocolProof 256 (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).up :=
  { mkBPrfP (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec) run (rootsB oo) ((), pl)
      (opensAt (TYX D.base.plan.salt D.C D.ds D.a D.xs dec).up run oo) with
    ext := extOf D.a D.base.cfg (tabsOf sto) }

include hO in
/-- The strict format holds on the typed string `typedX`, if: O's answers and the configuration's
digest have 32 bytes; the chain's own part oo has the library's `LaxFacts` within the library's
limits, and the run value run; ρ holds the draws of oo's rounds; the stored tables' openings sto
have `StoOK`; and they list what the draws ask of the tables (hx). -/
theorem strictX (r0 r1 : ByteArray) (hok : PQ.ok D.base = true) (hc : D.base.cfg.size = 32)
    (oo : Fmt.ChainOut) (run : ByteArray) (pl : Plains (uL D.C D.ds)) (ρ : Rho (uL D.C D.ds))
    (v : Bits) (sto : List (Bool × ℕ × OpenB))
    (hf : LaxFacts (Fmt.HO O) D.base oo) (hr : oo.run = some run)
    (hd : drawnSL D.C D.ds ρ = oo.rounds.toList.map (·.drawn))
    (hs : StoOK O D.base.cfg D.a D.base.plan.salt r0 r1 sto)
    (hx : xWanted D.a D.ds D.xs (drawnSL D.C D.ds ρ) = askedOf sto) :
    strictP (256 + 8 * D.base.plan.salt) 256 (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec)
      (wqX D.C D.K (chalP D.base.plan.field D.K) D.ds D.a D.xs dec) 0 ()
      (typedX D dec run oo pl sto) (default, ρ)
      ((none, some none), rtSL D.C D.ds oo.rounds.toList) (.loc v) = true := by
  have hrun := run_size O D.base hO oo run hf hr
  unfold strictP
  dsimp only
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · show decide ((bytesToBits run).length = 256) = true
    rw [length_bytesToBits, hrun]
    rfl
  · show decide (((rootsB oo).map bytesToDig).length
      ≤ 0 + 0 + cntP (SL D.C D.ds) (rtSL D.C D.ds oo.rounds.toList)) = true
    rw [cntP_rt D.C D.ds oo.rounds.toList (pi_sent _ D.base oo hok hf), List.length_map]
    exact decide_eq_true (Nat.le_of_eq (by simp only [Nat.zero_add]; rfl))
  · have := strict_ind D.C D.K (chalP D.base.plan.field D.K) (opensB oo) run D.base.plan.salt hrun
      D.ds oo.rounds.toList _ (rows_top (Fmt.HO O) D.base D.C dec oo ρ
        (effsP (PSof D.C D.ds dec).S (PSof D.C D.ds dec).ann
          ((none, some none), rtSL D.C D.ds oo.rounds.toList) ((), pl)) hok hf hd)
    show (sCompP _ (s0 D.C) (fun _ => none) 0 _ _ _ && sCompP _ (s0 D.C) (fun _ => none) 0 _ _ _ &&
      sSP (256 + 8 * D.base.plan.salt) (SL D.C D.ds) (allLo (SL D.C D.ds))
        (wiresSL D.C D.K (chalP D.base.plan.field D.K) D.ds)
        (rtSL D.C D.ds oo.rounds.toList) _ _) = true
    rw [Bool.and_eq_true, Bool.and_eq_true]
    exact ⟨⟨List.all_eq_true.2 fun _ _ => rfl, List.all_eq_true.2 fun _ _ => rfl⟩, this⟩
  · have := ext_strict D O r0 r1 hc sto hs
    show sExtP (256 + 8 * D.base.plan.salt) (weX D.a)
      (fun p => decide (p ∈ ((xWanted D.a D.ds D.xs (drawnSL D.C D.ds ρ)).filterMap
        (xPos (2 ^ D.a))).toFinset)) (extOf D.a D.base.cfg (tabsOf sto)) = true
    rw [hx]
    exact this
  · rfl
  · rfl

/-- A leaf's content at the plain case's interface, carried to the interface with stored tables. -/
def toLink : Body (LbS D.C D.ds dec) → Body (D.L dec)
  | some (.inr ⟨.onl, s⟩) => some (.inr ⟨.link, s⟩)
  | _ => none

/-- The two cases' typed leaf functions agree along `toLink`. -/
theorem leaf_agree (b : Body (LbS D.C D.ds dec)) (salt : Bits) :
    (famX D dec O (D.K + 1) OracleName.leaf (⟨toLink D dec b, salt⟩ : LeafIn (D.L dec)) : Dig 256)
      = Run.famOf O (PDS D.base D.C dec) (D.K + 1) OracleName.leaf
          (⟨b, salt⟩ : LeafIn (LbS D.C D.ds dec)) := by
  rcases b with _ | s | ⟨t, s⟩
  · rfl
  · rfl
  · cases t with
    | test => rfl
    | link => rfl
    | onl =>
      obtain ⟨p, col⟩ := s
      rcases p with p | q
      · exact p.elim
      · rfl

include hO in
/-- What follows the chain. Under the hypotheses of `strictX`, if also r0 and r1 have 32 bytes, all
own openings walk to their roots (hroots) and sto lists no more places than the parts of the draws
have (hcnt), then all walks end in their roots, so the verdict is the protocol's own. -/
theorem afterX (r0 r1 : ByteArray) (h0 : r0.size = 32) (h1 : r1.size = 32)
    (hok : PQ.ok D.base = true) (hc : D.base.cfg.size = 32)
    (oo : Fmt.ChainOut) (run : ByteArray) (pl : Plains (uL D.C D.ds)) (ρ : Rho (uL D.C D.ds))
    (v : Bits) (sto : List (Bool × ℕ × OpenB))
    (hf : LaxFacts (Fmt.HO O) D.base oo) (hr : oo.run = some run)
    (hd : drawnSL D.C D.ds ρ = oo.rounds.toList.map (·.drawn))
    (hroots : rootsAll (Fmt.HO O) D.base.cfg run oo.rounds.toList = true)
    (hs : StoOK O D.base.cfg D.a D.base.plan.salt r0 r1 sto)
    (hx : xWanted D.a D.ds D.xs (drawnSL D.C D.ds ρ) = askedOf sto)
    (hcnt : (sto.map (·.2.2.idx.length)).sum ≤ (D.xs.map (·.count)).sum) :
    afterP (fun _ => D.L dec) (famX D dec O (D.K + 1)) (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec)
      (wqX D.C D.K (chalP D.base.plan.field D.K) D.ds D.a D.xs dec)
      (fun p s => some (.inr ⟨Tag.link, ⟨p, s⟩⟩)) (fun s => some (.inl s)) 0
      [bytesToDig r0, bytesToDig r1] () (typedX D dec run oo pl sto) (default, ρ)
      ((none, some none), rtSL D.C D.ds oo.rounds.toList) (.loc v)
    = (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).accept ()
        ((weX D.a).build fun p => (extOf D.a D.base.cfg (tabsOf sto) p).map Opening.sym)
        (trP (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).S (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).ann
          (wqX D.C D.K (chalP D.base.plan.field D.K) D.ds D.a D.xs dec).sh
          ((none, some none), rtSL D.C D.ds oo.rounds.toList) ((), pl) (default, ρ)
          (opensAt (TYX D.base.plan.salt D.C D.ds D.a D.xs dec).up run oo)) := by
  have hrun := run_size O D.base hO oo run hf hr
  obtain ⟨Fs, g1, g2, g3, g4⟩ := forests_ind (L := LbS D.C D.ds dec) O (PDS D.base D.C dec) D.C D.K
    (chalP D.base.plan.field D.K) (opensB oo) run D.base.plan.salt hO hrun D.ds oo.rounds.toList _
    (fun s => ⟨.inr s.1, s.2⟩)
    (rows_top (Fmt.HO O) D.base D.C dec oo ρ (effsP (PSof D.C D.ds dec).S (PSof D.C D.ds dec).ann
      ((none, some none), rtSL D.C D.ds oo.rounds.toList) ((), pl)) hok hf hd) (fun s => rfl)
  obtain ⟨Fx, x1, x2, x3, x4⟩ := ext_forest D dec O hO r0 r1 h0 h1 hc sto hs
  have key : forestsP (fun _ => D.L dec) (SOf D.C D.ds) (allLo (SOf D.C D.ds))
      (wire0S D.C D.K (chalP D.base.plan.field D.K),
        wiresSL D.C D.K (chalP D.base.plan.field D.K) D.ds)
      (fun p s => some (.inr ⟨Tag.link, ⟨p, s⟩⟩))
      ((none, some none), rtSL D.C D.ds oo.rounds.toList)
      (fun p => @decide (p ∈ (PSof D.C D.ds dec).reads () (default, ρ)
        (effsP (PSof D.C D.ds dec).S (PSof D.C D.ds dec).ann
          ((none, some none), rtSL D.C D.ds oo.rounds.toList) ((), pl)))
        (@Finset.decidableMem _ (decOS D.C D.ds) _ _))
      (opensAt (TYS D.base D.C dec).up run oo) = some (Fs.map (mapF (toLink D dec))) := by
    have k1 := forestsP_front D.C D.K (chalP D.base.plan.field D.K) D.ds (L := LbS D.C D.ds dec)
      (fun p a => some (.inr ⟨Tag.onl, ⟨p, a⟩⟩)) (rtSL D.C D.ds oo.rounds.toList)
      (fun p => @decide (p ∈ (PSof D.C D.ds dec).reads () (default, ρ)
        (effsP (PSof D.C D.ds dec).S (PSof D.C D.ds dec).ann
          ((none, some none), rtSL D.C D.ds oo.rounds.toList) ((), pl)))
        (@Finset.decidableMem _ (decOS D.C D.ds) _ _))
      (opensAt (TYS D.base D.C dec).up run oo) Fs g1
    have k2 := forestsP_map (K := D.K + 1) (toLink D dec) (SOf D.C D.ds) (allLo (SOf D.C D.ds))
      (wire0S D.C D.K (chalP D.base.plan.field D.K),
        wiresSL D.C D.K (chalP D.base.plan.field D.K) D.ds)
      (fun p a => some (.inr ⟨Tag.onl, ⟨p, a⟩⟩))
      ((none, some none), rtSL D.C D.ds oo.rounds.toList)
      (fun p => @decide (p ∈ (PSof D.C D.ds dec).reads () (default, ρ)
        (effsP (PSof D.C D.ds dec).S (PSof D.C D.ds dec).ann
          ((none, some none), rtSL D.C D.ds oo.rounds.toList) ((), pl)))
        (@Finset.decidableMem _ (decOS D.C D.ds) _ _))
      (opensAt (TYS D.base D.C dec).up run oo)
    rw [k1] at k2
    exact k2
  have hFo : forestsOfP (fun _ => D.L dec) (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec)
      (wqX D.C D.K (chalP D.base.plan.field D.K) D.ds D.a D.xs dec)
      (fun p s => some (.inr ⟨Tag.link, ⟨p, s⟩⟩)) (fun s => some (.inl s))
      [bytesToDig r0, bytesToDig r1] () (typedX D dec run oo pl sto) (default, ρ)
      ((none, some none), rtSL D.C D.ds oo.rounds.toList)
      = some (Fs.map (mapF (toLink D dec)) ++ [Fx]) := by
    have x1' : forestExtP (fun _ => D.L dec) (weX D.a) (fun s => some (.inl s))
        [bytesToDig r0, bytesToDig r1]
        (fun p => decide (p ∈ ((xWanted D.a D.ds D.xs (drawnSL D.C D.ds ρ)).filterMap
          (xPos (2 ^ D.a))).toFinset)) (extOf D.a D.base.cfg (tabsOf sto)) = some [Fx] := by
      rw [hx]
      exact x1
    unfold forestsOfP
    dsimp only
    split
    · rename_i a b e1 e2
      have ea : a = Fs.map (mapF (toLink D dec)) := Option.some.inj (e1.symm.trans key)
      have eb : b = [Fx] := Option.some.inj (e2.symm.trans x1')
      rw [ea, eb]
    · rename_i hne
      exact (hne _ _ key x1').elim
  have hfl : flatP (fun _ => D.L dec) (Fs.map (mapF (toLink D dec)) ++ [Fx])
      = (flatP (fun _ => LbS D.C D.ds dec) Fs).map (mapC (toLink D dec))
        ++ flatP (fun _ => D.L dec) [Fx] := by
    rw [← flatP_map]
    exact List.flatMap_append
  have hrd : readsP (fun _ => D.L dec) (Fs.map (mapF (toLink D dec)) ++ [Fx])
      = readsP (fun _ => D.L dec) (Fs.map (mapF (toLink D dec)))
        ++ (readsOneP (fun _ => D.L dec) Fx ++ []) := by
    unfold readsP
    rw [List.flatMap_append]
    rfl
  have hlen : (flatP (fun _ => D.L dec) (Fs.map (mapF (toLink D dec)) ++ [Fx])).length
      ≤ nOpen D.ds + (D.xs.map (·.count)).sum := by
    rw [hfl, List.length_append, List.length_map, g2, x2]
    exact Nat.add_le_add (cnt_le _ D.base oo hok hf) hcnt
  have hall : (flatP (fun _ => D.L dec) (Fs.map (mapF (toLink D dec)) ++ [Fx])).all
      (fun c => wellP (fun _ => D.L dec) c && decide (c.depth ≤ max (maxDepth D.ds) D.a))
      = true := by
    rw [hfl, List.all_append, Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
    refine ⟨fun c hc => ?_, fun c hc => ?_⟩
    · obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 hc
      obtain ⟨w, d, hdm, hdd⟩ := g3 c0 hc0
      rw [Bool.and_eq_true, wellP_map]
      refine ⟨w, decide_eq_true ?_⟩
      show c0.depth ≤ _
      rw [hdd]
      exact le_trans ((PQ.foldl_max_le (fun d => depthOf d.tree) D.ds 0).2 d hdm) (le_max_left _ _)
    · obtain ⟨w, hdd⟩ := x3 c hc
      rw [Bool.and_eq_true]
      exact ⟨w, decide_eq_true (by rw [hdd]; exact le_max_right _ _)⟩
  have hrun1 : runForestsP (fun _ => D.L dec) (famX D dec O (D.K + 1))
      (Fs.map (mapF (toLink D dec))) (readsP (fun _ => D.L dec) (Fs.map (mapF (toLink D dec))))
      = true := by
    rw [readsP_map, runForestsP_map (toLink D dec)
      (Run.famOf O (PDS D.base D.C dec) (D.K + 1)) (famX D dec O (D.K + 1)) (fun q => rfl) Fs _
      (fun c _ => leaf_agree D dec O c.inp.body c.inp.salt)]
    have h4 := g4 [] []
    rw [List.append_nil, List.append_nil] at h4
    rw [h4, tree_roots O D.base D.C dec oo run hok hf, hroots]
    rfl
  unfold afterP
  rw [hFo]
  dsimp only
  rw [if_pos ⟨hlen, hall⟩, hrd, runForestsP_append, hrun1,
    runForests_cons (K := D.K) (famX D dec O (D.K + 1)) Fx [] [], x4]
  rfl

/-- The library's typing of a chain output o gives `typedX`, if: o's rounds are rc with each round's
stored openings joined in, and oo's are rc's own parts without the vertices met; each round has as
many stored openings as the description says; o has a run value; oo's plain parts are typed as pl;
oo's own openings pass the typing's test; and the stored openings have `StoOK`. -/
theorem typingX (r0 r1 : ByteArray) (o oo : Fmt.ChainOut) (run : ByteArray)
    (pl : Plains (uL D.C D.ds))
    (rc : List (Fmt.RoundOut × List (Fmt.Shape × List ℕ × Fmt.OpenOut)))
    (ho : o.rounds.toList = rc.map roundWithStoredOpenings) (hoo : oo.rounds.toList = rc.map fun p => stripR p.1)
    (hl : List.Forall₂ (fun (ts : List Fmt.Stored)
      (p : Fmt.RoundOut × List (Fmt.Shape × List ℕ × Fmt.OpenOut)) => ts.length = p.2.length)
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
theorem acceptX (r0 r1 : ByteArray) (hok : PQ.ok D.base = true) (o oo : Fmt.ChainOut)
    (run : ByteArray) (pl : Plains (uL D.C D.ds)) (ρ : Rho (uL D.C D.ds))
    (hL : LaxFacts (Fmt.HO O) D.base oo) (hpl : plainsSL D.C D.ds oo.rounds.toList = some pl)
    (hd : drawnSL D.C D.ds ρ = oo.rounds.toList.map (·.drawn))
    (rc : List (Fmt.RoundOut × List (Fmt.Shape × List ℕ × Fmt.OpenOut)))
    (hoo : oo.rounds.toList = rc.map fun p => stripR p.1) (ho : o.rounds.toList = rc.map roundWithStoredOpenings)
    (hS : List.Forall₂ (fun (ts : List Fmt.Stored)
        (p : Fmt.RoundOut × List (Fmt.Shape × List ℕ × Fmt.OpenOut)) =>
      List.Forall₂ (StoredFact (Fmt.HO O) D.base.cfg D.base.statement p.1.drawn.poss) ts p.2)
      D.stored rc)
    (hD : ∀ s ∈ D.stored.flatten, s.sh.a = D.a ∧ s.item ≤ 1)
    (hs : StoOK O D.base.cfg D.a D.base.plan.salt r0 r1 (storedB D.xs o))
    (hpass : passSL D.C D.ds ρ = true) (hfull : everyOpeningHasItsDraws D.xs (drawnSL D.C D.ds ρ) = true)
    (hx : xWanted D.a D.ds D.xs (drawnSL D.C D.ds ρ) = askedOf (storedB D.xs o))
    (hdec : dec (Fmt.viewX ⟨D.base, D.stored⟩ o) = true) :
    (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).accept ()
        ((weX D.a).build fun p =>
          (extOf D.a D.base.cfg (tabsOf (storedB D.xs o)) p).map Opening.sym)
        (trP (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).S (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).ann
          (wqX D.C D.K (chalP D.base.plan.field D.K) D.ds D.a D.xs dec).sh
          ((none, some none), rtSL D.C D.ds oo.rounds.toList) ((), pl) (default, ρ)
          (opensAt (TYX D.base.plan.salt D.C D.ds D.a D.xs dec).up run oo)) = true := by
  have hl : List.Forall₂ (fun (ts : List Fmt.Stored)
      (p : Fmt.RoundOut × List (Fmt.Shape × List ℕ × Fmt.OpenOut)) => ts.length = p.2.length)
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
  have hview := viewX_eq (Fmt.HO O) D D.K (chalP D.base.plan.field D.K) hok oo o run pl ρ hL hpl hd
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

include hO in
/-- All parts together. If the decision says yes on the view of o (hdec), then the library's typing
of o gives a string, and the evaluable form of the compiled verifier says yes on it. The other
hypotheses are bounds, limits on the description, and what the strict reader has checked of o: O's
answers, r0, r1 and the configuration's digest have 32 bytes; the own part is within the library's
limits; the statement is `D.stm r0 r1`; o is rc with the stored openings joined in, oo its own part,
both with the run value run; oo has `LaxFacts`, its `pd` is `Fmt.paramsDigest` of the parameters,
all its work has passed and all its own openings have walked to their roots; each stored opening has
`StoredFact`, all have `StoOK`, one depth and items 0 or 1; and every part of the draws is full. -/
theorem verifyX_true (r0 r1 : ByteArray) (h0 : r0.size = 32) (h1 : r1.size = 32)
    (hok : PQ.ok D.base = true) (hst : D.base.statement = D.stm r0 r1)
    (hc : D.base.cfg.size = 32) (o oo : Fmt.ChainOut)
    (run : ByteArray)
    (rc : List (Fmt.RoundOut × List (Fmt.Shape × List ℕ × Fmt.OpenOut)))
    (hoo : oo.rounds.toList = rc.map fun p => stripR p.1) (ho : o.rounds.toList = rc.map roundWithStoredOpenings)
    (hr : o.run = some run) (hrr : oo.run = some run)
    (hL : LaxFacts (Fmt.HO O) D.base oo) (hpd : oo.pd = Fmt.paramsDigest D.base.params)
    (hpass : passL (Fmt.HO O) D.base.rounds oo.rounds.toList ⟨D.base.label, oo.rho0, 0⟩ = true)
    (hroots : rootsAll (Fmt.HO O) D.base.cfg run oo.rounds.toList = true)
    (hS : List.Forall₂ (fun (ts : List Fmt.Stored)
        (p : Fmt.RoundOut × List (Fmt.Shape × List ℕ × Fmt.OpenOut)) =>
      List.Forall₂ (StoredFact (Fmt.HO O) D.base.cfg D.base.statement p.1.drawn.poss) ts p.2)
      D.stored rc)
    (hD : ∀ s ∈ D.stored.flatten, s.sh.a = D.a ∧ s.item ≤ 1)
    (hs : StoOK O D.base.cfg D.a D.base.plan.salt r0 r1 (storedB D.xs o))
    (hfull : everyOpeningHasItsDraws D.xs (oo.rounds.toList.map (·.drawn)) = true)
    (hdec : dec (Fmt.viewX ⟨D.base, D.stored⟩ o) = true) :
    ∃ π, toBPrfX D.base.plan.salt D.base.cfg D.C D.ds D.a D.xs dec o = some π ∧
      verifyP (fun _ => D.L dec) (famX D dec O (D.K + 1)) id none (256 + 8 * D.base.plan.salt) 256
        .link (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec)
        (wqX D.C D.K (chalP D.base.plan.field D.K) D.ds D.a D.xs dec)
        (fun p s => some (.inr ⟨Tag.link, ⟨p, s⟩⟩))
        (embPX D.C D.ds D.a D.xs dec (fun _ _ p => (p.val, [])) (fun _ => some ()))
        (fun _ => none) (fun s => some (.inl s)) 0 [bytesToDig r0, bytesToDig r1] () π = true := by
  obtain ⟨run', pl, hr', hpl, -⟩ := pi_typed' (Fmt.HO O) D.base D.C dec oo hL
  obtain ⟨ρ, v, hch, hd, hp⟩ := chainX D dec O hO r0 r1 hok hst h0 h1 oo run pl hL hpd hrr hpl
  have hl : List.Forall₂ (fun (ts : List Fmt.Stored)
      (p : Fmt.RoundOut × List (Fmt.Shape × List ℕ × Fmt.OpenOut)) => ts.length = p.2.length)
      D.stored rc := hS.imp fun _ _ hh => hh.length_eq
  have hob : (opensB oo).all (fun y => y.2.2.ok D.base.plan.salt y.2.1) = true := by
    rw [List.all_eq_true]
    intro y hy
    obtain ⟨ro, hro, hy'⟩ := List.mem_flatMap.1 hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy'
    exact opens_ok (Fmt.HO O) D.base.plan D.base.rounds oo.rounds.toList _ _ hL.trace ro hro x hx
  have hx : xWanted D.a D.ds D.xs (drawnSL D.C D.ds ρ) = askedOf (storedB D.xs o) := by
    rw [hd]
    exact xWanted_asked (Fmt.HO O) D o rc ho hS hok oo hL hoo fun s hs' => (hD s hs').1
  refine ⟨typedX D dec run oo pl (storedB D.xs o),
    typingX D dec O r0 r1 o oo run pl rc ho hoo hl hr hpl hob hs, ?_⟩
  unfold verifyP
  have hch' : chainP (fun _ => D.L dec) (famX D dec O (D.K + 1)) id none .link
      [bytesToDig r0, bytesToDig r1] ((fun _ => none : Unit → Option Unit) ())
      (typedX D dec run oo pl (storedB D.xs o)).salt (typedX D dec run oo pl (storedB D.xs o)).rtreq
      (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).S (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).ann
      (wqX D.C D.K (chalP D.base.plan.field D.K) D.ds D.a D.xs dec).sh
      (embPX D.C D.ds D.a D.xs dec (fun _ _ p => (p.val, [])) (fun _ => some ())) 0 .first
      (typedX D dec run oo pl (storedB D.xs o)).roots
      (typedX D dec run oo pl (storedB D.xs o)).plains
      = some ((default, ρ), ((none, some none), rtSL D.C D.ds oo.rounds.toList), .loc v) := hch
  rw [hch']
  dsimp only
  rw [strictX D dec O hO r0 r1 hok hc oo run pl ρ v _ hL hrr hd hs hx, if_pos rfl,
    afterX D dec O hO r0 r1 h0 h1 hok hc oo run pl ρ v _ hL hrr hd hroots hs hx
      (sto_count (Fmt.HO O) D o rc ho hS)]
  exact acceptX D dec O r0 r1 hok o oo run pl ρ hL hpl hd rc hoo ho hS hD hs (hp.trans hpass)
    (by rw [hd]; exact hfull) hx hdec

end

end OnBytes.Tie

#print axioms OnBytes.Tie.verifyX_true
