-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/PageIsChain.lean.
TWO: CUT BY PROGRAM out of the library's Run/PageIsChain.lean (only what the entry's clause holds
and stands on a declaration that the sibling says again), then turned by hand where it had to be.
THE HEAD BELOW IS THE LIBRARY's AND SPEAKS OF THE LIBRARY's FILE: much of what it announces IS NOT
HERE, and what it says of "one root | one tree a round" is not true of this file. HERE STAND ONLY:
bytes_ofGots, msg_bytes, map_dig_bytes, FitL, fit_from, fit_rds, famOf_row, takeRt_fit, chainP_lo,
chain_ind, famOf_first, chainP_first, pi_chain.

Run/PageIsChain.lean: the statement on the hash chain in the comparison of the two verifiers of
Run/PageIs.lean.

Run/PageIs.lean compares two verifiers of a proof file: our rendering in Lean (Fmt/Rules8.lean) of
the verifier of the format page (FORMAT.md, which comes with the programs, that is, with the C++
implementation that accompanies this Lean code), and the compiled verifier behind a lenient reader
that only cuts the file into its parts. This file proves that comparison's statement on the hash
chain from which the verifier's challenges are drawn, Spec.pi_chain. It is generic in the oracle, in
the description of the protocol's rounds, and in the choice of challenge types (the parameter C :
CK, called a kit in the code: for each round the type of the verifier's message, and the map from
such a message to the format's record of what was drawn), together with the function chal that makes
such a message from hash blocks.

What the statement says. Let O be any function on byte strings with answers of 32 bytes. Let S be a
description within the limits of the generic construction (Run.PQ.ok). Let C and chal be such that
what C reads off the message that chal makes from a round's K blocks is the format's draw on the
first of these blocks, as many as the round's draws can need (KitFits), with room for every round's
blocks. Let o be what the lenient reader hands out, of which only LaxFacts of Run/PageIs.lean is
used, with its rounds typed (plainsSL). Then the chain of the evaluable form of the compiled
verifier (Run/ThinDefs.lean, chainP; that this form computes the compiled verifier's verdict is
thin_verify, stated in Run/ThinTie.lean and proved in Run/ThinTieProofs.lean), at the typed oracle
functions that O induces and on the reader's argument string, does not refuse, ends in a local
phase, and yields each round's root as o has it. Moreover, what it draws is what o says was drawn,
and its test bits pass exactly if every round's proof-of-work test of the format page passes
(passL).

1. What the file contains. Theorems with their proofs, and two definitions with which they are
stated. The parts are lettered as in the text below the head.
   A. gotBytes, only_item, extract_self, items_only, bytes_ofGots, roots_ofGots, msg_bytes,
   roots_size. The message that was read is the spelling of the typed plain part (a reader accepts
   only the spelling of what it returns: Fmt/Rules1Only.lean). As many roots are read as the items
   have; each has 32 bytes.
   C. msgA_eq, drawn_eq, pass_bits. On a round's blocks: the blocks of the verifier's message, as
   the format cuts them off the row, are the bytes of the typed message blocks. So the view of the
   verifier's message is the format's draw. The test bits against the proof-of-work test in bits.
   B. FitL, roundsOk_count, shape_some, fit_from, fit_rds. What the limits of the generic
   construction say: the rounds' data are the description's; a round has a tree exactly if it sends
   a root; at most one; as many as its items say.
   D. famOf_row (on Run/ChainRow.lean), old_grind, pass_grind (two cases: without proof of work no
   block is kept back; with it the typed block 0 gives the test bits), old_mk, nonce_mk, takeRt_fit,
   chainP_lo, and chain_ind: the rounds by induction, for a suffix of the rounds, any chain value,
   and any embedding of plain parts that the spellings read rightly.
   E.  first_bytes, size_HO32, famOf_first, firstValue_HO, chainP_first, and pi_chain.

2. What is checked when the file compiles. No tests (#guard) in this file.

3. Theorems. All of the above; the one that other files use is pi_chain.

4. What is not claimed.
   That LaxFacts holds of the lenient reader's output (Run/PageIsReaders.lean), what follows the
   chain (Run/PageIsAfter.lean), and the comparison of the two verifiers as a whole
   (Run/PageIsProofs.lean, Run/PageIsCoreProofs.lean) are other files of the same comparison.
   NO STATEMENT ON SOUNDNESS.

Terms: lean/GLOSSARY.md.

-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library: a test by Lean's evaluator, which
   leaves no declaration. So nothing that is checked of declarations is checked of such a run. No
   clause of a soundness theorem of this library speaks of a run. -/
import Run.PageIsChain
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
import OnBytes.TypedOracleCompiler.Run.Toy1TieTree
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.CodingPage160
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.CodingPage164
import OnBytes.TypedOracleCompiler.Run.PageIs
import Fmt.Rules8Ok
import OnBytes.TypedOracleCompiler.Run.ChainRow

set_option autoImplicit false

namespace TypedOracleCompiler.Run.PQ
open Rom TypedOracleCompiler.Iop _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Run.Twin
    TypedOracleCompiler.Run.Thin
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ TypedOracleCompiler.Run
open _root_.Run.Twin (allLo)
export _root_.Run.PQ (gotBytes only_item items_only roots_ofGots msgA_eq drawn_eq pass_bits
    roundsOk_count shape_some old_grind pass_grind old_mk nonce_mk roots_size first_bytes size_HO32
    firstValue_HO)
open _root_.Fmt (Chain RoundOut ChainOut Item ItemValue)

/-! ## A. A message's bytes -/

/-- The typed plain part spells the items that were read. TWO: with THE LIST of the roots read, each
at its own place: the library's side condition ("if every root among them is rt") is gone. -/
theorem bytes_ofGots :
    ∀ (ts : List Item) (l : List ItemValue) (p : PlainOf ts), PlainOf.ofGots ts l = some p →
      bytesL (_root_.Fmt.rootsOf l) ts p = _root_.Fmt.cat (l.map gotBytes)
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by cases h
  | .root :: ts, .root d :: l, p, h => by
      have ih := bytes_ofGots ts l p h
      show d ++ bytesL (_root_.Fmt.rootsOf l) ts p = _
      rw [List.map_cons, _root_.Fmt.cat_cons, ih]
      rfl
  | .f :: ts, .f x :: l, p, h => by
      rcases h1 : PlainOf.ofGots ts l with _ | y
      · simp [PlainOf.ofGots, h1] at h
      · simp only [PlainOf.ofGots, h1, Option.map_some, Option.some.injEq] at h
        subst h
        rw [List.map_cons, _root_.Fmt.cat_cons, ← bytes_ofGots ts l y h1]
        show bytesL (_root_.Fmt.rootsOf l) (.f :: ts) ((x, y) : UInt64 × PlainOf ts) = _
        cases _root_.Fmt.rootsOf l <;> rfl
  | .word :: ts, .word x :: l, p, h => by
      rcases h1 : PlainOf.ofGots ts l with _ | y
      · simp [PlainOf.ofGots, h1] at h
      · simp only [PlainOf.ofGots, h1, Option.map_some, Option.some.injEq] at h
        subst h
        rw [List.map_cons, _root_.Fmt.cat_cons, ← bytes_ofGots ts l y h1]
        show bytesL (_root_.Fmt.rootsOf l) (.word :: ts) ((x, y) : UInt64 × PlainOf ts) = _
        cases _root_.Fmt.rootsOf l <;> rfl
  | .e :: ts, .e x :: l, p, h => by
      rcases h1 : PlainOf.ofGots ts l with _ | y
      · simp [PlainOf.ofGots, h1] at h
      · simp only [PlainOf.ofGots, h1, Option.map_some, Option.some.injEq] at h
        subst h
        rw [List.map_cons, _root_.Fmt.cat_cons, ← bytes_ofGots ts l y h1]
        show bytesL (_root_.Fmt.rootsOf l) (.e :: ts) ((x, y) : _root_.Fmt.Ext × PlainOf ts) = _
        cases _root_.Fmt.rootsOf l <;> rfl
  | .answer :: ts, .answer x :: l, p, h => by
      rcases h1 : PlainOf.ofGots ts l with _ | y
      · simp [PlainOf.ofGots, h1] at h
      · simp only [PlainOf.ofGots, h1, Option.map_some, Option.some.injEq] at h
        subst h
        rw [List.map_cons, _root_.Fmt.cat_cons, ← bytes_ofGots ts l y h1]
        show bytesL (_root_.Fmt.rootsOf l) (.answer :: ts)
            ((x, y) : _root_.Fmt.Ext × PlainOf ts) = _
        cases _root_.Fmt.rootsOf l <;> rfl
  | _ :: _, [], _, h => by simp [PlainOf.ofGots] at h
  | .root :: _, .f _ :: _, _, h => by simp [PlainOf.ofGots] at h
  | .root :: _, .e _ :: _, _, h => by simp [PlainOf.ofGots] at h
  | .root :: _, .word _ :: _, _, h => by simp [PlainOf.ofGots] at h
  | .root :: _, .answer _ :: _, _, h => by simp [PlainOf.ofGots] at h
  | .f :: _, .e _ :: _, _, h => by simp [PlainOf.ofGots] at h
  | .f :: _, .word _ :: _, _, h => by simp [PlainOf.ofGots] at h
  | .f :: _, .root _ :: _, _, h => by simp [PlainOf.ofGots] at h
  | .f :: _, .answer _ :: _, _, h => by simp [PlainOf.ofGots] at h
  | .word :: _, .f _ :: _, _, h => by simp [PlainOf.ofGots] at h
  | .word :: _, .e _ :: _, _, h => by simp [PlainOf.ofGots] at h
  | .word :: _, .root _ :: _, _, h => by simp [PlainOf.ofGots] at h
  | .word :: _, .answer _ :: _, _, h => by simp [PlainOf.ofGots] at h
  | .e :: _, .f _ :: _, _, h => by simp [PlainOf.ofGots] at h
  | .e :: _, .word _ :: _, _, h => by simp [PlainOf.ofGots] at h
  | .e :: _, .root _ :: _, _, h => by simp [PlainOf.ofGots] at h
  | .e :: _, .answer _ :: _, _, h => by simp [PlainOf.ofGots] at h
  | .answer :: _, .f _ :: _, _, h => by simp [PlainOf.ofGots] at h
  | .answer :: _, .e _ :: _, _, h => by simp [PlainOf.ofGots] at h
  | .answer :: _, .word _ :: _, _, h => by simp [PlainOf.ofGots] at h
  | .answer :: _, .root _ :: _, _, h => by simp [PlainOf.ofGots] at h

/-- THE MESSAGE THAT WAS READ IS THE SPELLING OF THE TYPED PLAIN PART. -/
theorem msg_bytes (f : _root_.Fmt.Fld) (ts : List Item) (msg : ByteArray) (l : List ItemValue)
    (p : PlainOf ts)
    (h : _root_.Fmt.whole (_root_.Fmt.readItems f ts) msg = some l)
    (hp : PlainOf.ofGots ts l = some p) :
    bytesL (_root_.Fmt.rootsOf l) ts p = msg ∧ ∀ d ∈ _root_.Fmt.rootsOf l, d.size = 32 := by
  unfold _root_.Fmt.whole at h
  rcases h1 : _root_.Fmt.readItems f ts msg 0 with _ | ⟨y, j⟩
  · simp [h1] at h
  · simp only [h1] at h
    by_cases hj : j = msg.size
    · rw [if_pos hj] at h
      obtain rfl := Option.some.inj h
      obtain ⟨a1, -, -, a4⟩ := items_only f ts msg 0 y j (Nat.zero_le _) h1
      refine ⟨?_, a1⟩
      rw [bytes_ofGots ts y p hp, ← a4, hj]
      apply ByteArray.ext
      rw [ByteArray.data_extract, ← ByteArray.size_data]
      simp
    · rw [if_neg hj] at h
      cases h

/-- TWO: roots of 32 bytes come back from their digests -/
theorem map_dig_bytes : ∀ R : List ByteArray, (∀ d ∈ R, d.size = 32) →
    (R.map bytesToDig).map digToBytes = R
  | [], _ => rfl
  | x :: R, h => by
      show digToBytes (bytesToDig x) :: (R.map bytesToDig).map digToBytes = x :: R
      rw [TieTree.dig_bytes x (h x List.mem_cons_self),
        map_dig_bytes R fun d hd => h d (List.mem_cons_of_mem _ hd)]

/-! ## C. One round, on its blocks -/



/-! ## B. What the road's limits say of the rounds -/

/-- the rounds' data against the description's rounds -/
def FitL : List RD → List _root_.Fmt.Round → Prop
  | [], [] => True
  | d :: ds, r :: rs =>
    d.entry = r.entry ∧ d.kind = r.kind ∧ d.items = r.items ∧
    d.trees.length = r.entry.roots ∧
    _root_.Fmt.countItem .root r.items = r.entry.roots ∧
    r.entry.roots ≤ TypedOracleCompiler.Iop.maxRt ∧ FitL ds rs
  | _, _ => False

theorem fit_from (S : _root_.Fmt.Spec) :
    ∀ (rs : List _root_.Fmt.Round) (sent : ℕ), sent + (rs.map (·.entry.roots)).sum = nRoots S →
      (∀ r ∈ rs, _root_.Fmt.countItem .root r.items = r.entry.roots) →
      (∀ r ∈ rs, r.entry.roots ≤ TypedOracleCompiler.Iop.maxRt) → FitL (rdsFrom S sent rs) rs
  | [], _, _, _, _ => trivial
  | r :: rs, sent, hsum, hc, h1 => by
      rw [List.map_cons, List.sum_cons] at hsum
      refine ⟨rfl, rfl, rfl, ?_,
        hc r List.mem_cons_self,
        h1 r List.mem_cons_self,
        fit_from S rs (sent + r.entry.roots) (by omega)
          (fun r' hr' => hc r' (List.mem_cons_of_mem _ hr'))
          fun r' hr' => h1 r' (List.mem_cons_of_mem _ hr')⟩
      show ((List.range r.entry.roots).map fun k =>
          (shapeOfOwn S (sent + k)).getD (bareShape S.firstTree (sent + k))).length = _
      rw [List.length_map, List.length_range]

/-- Within the road's limits. -/
theorem fit_rds (S : _root_.Fmt.Spec) (h : ok S = true) : FitL (rds S) S.rounds := by
  simp only [ok, Bool.and_eq_true, and_assoc] at h
  obtain ⟨hS, h1, -, -, -⟩ := h
  refine fit_from S S.rounds 0 (by rw [Nat.zero_add]; rfl) ?_ ?_
  · exact roundsOk_count _ _ _ S.rounds _ _ (_root_.Fmt.ok_rounds hS)
  · intro r hr
    exact of_decide_eq_true (List.all_eq_true.1 h1 r hr)

/-! ## D. The typed answer to a round's chain query; the wire's message -/

/-- the typed answer, block by block, is the digest of the page's block -/
theorem famOf_row {I X : Type} {L : BatchProtocolWithLeafBody I X} (O : ByteArray → ByteArray)
    (hO : ∀ x, (O x).size = 32) (D : PageD L .onl) (K : ℕ) (i : ℕ) (ρ : List Bool)
    (rt : List (Dig 256)) (pl : PlainPart (Compile.Batch.shapeOf L .onl) (annOf L .onl))
    (kind : _root_.Fmt.Kind) (hk : kind.num = D.kind (i + 1)) :
    (∀ k : Fin K,
      (famOf O D K (.fb .onl)
          (⟨i + 1, .f2 none ρ, rt, pl⟩ : FbIn 256 L .onl) : (Fin K → Dig 256) × Dig 256).1 k =
        bytesToDig
          (_root_.Fmt.blockW (_root_.Fmt.HO O) D.label (bitsToBytes ρ) (i + 1)
            (D.msg (i + 1) (rt.map digToBytes) pl) kind (D.work (i + 1)) (D.nonce (i + 1) pl)
            (blockNo (D.work (i + 1)) K k.castSucc))) ∧
    (famOf O D K (.fb .onl)
        (⟨i + 1, .f2 none ρ, rt, pl⟩ : FbIn 256 L .onl) : (Fin K → Dig 256) × Dig 256).2 =
      bytesToDig
        (_root_.Fmt.blockW (_root_.Fmt.HO O) D.label (bitsToBytes ρ) (i + 1)
          (D.msg (i + 1) (rt.map digToBytes) pl) kind (D.work (i + 1)) (D.nonce (i + 1) pl)
          (_root_.Fmt.firstBlock (D.work (i + 1)) - 1)) := by
  rw [← famP_eq]
  refine ⟨fun k => ?_, ?_⟩
  · show digS ((famB (fun _ => L) O D K (.fb .onl)
            (⟨i + 1, .f2 none ρ, rt, pl⟩ : FbIn 256 L .onl)).getD
          k.castSucc.val ByteArray.empty) = _
    rw [famB_row (fun _ => L) O hO D K i ρ rt pl kind hk k.castSucc, digS_eq]
  · show digS ((famB (fun _ => L) O D K (.fb .onl)
            (⟨i + 1, .f2 none ρ, rt, pl⟩ : FbIn 256 L .onl)).getD
          (Fin.last K).val ByteArray.empty) = _
    rw [famB_row (fun _ => L) O hO D K i ρ rt pl kind hk (Fin.last K), blockNo_last, digS_eq]

/-- the roots of a round's component, off the list of roots -/
theorem takeRt_fit (n : ℕ) (R rest : List ByteArray) (h : n = R.length)
    (h1 : R.length ≤ TypedOracleCompiler.Iop.maxRt) :
    takeRt n ((R ++ rest).map bytesToDig) = some (R.map bytesToDig, rest.map bytesToDig) := by
  subst h
  unfold takeRt
  rw [if_pos ⟨h1, by rw [List.length_map, List.length_append]; omega⟩, List.map_append,
    List.take_left' (List.length_map _), List.drop_left' (List.length_map _)]

/-- a local round behind the first: the chain's step -/
theorem chainP_lo {I X : Type} {lam K : ℕ} {y : X} (Lf : Unit → BatchProtocolWithLeafBody I X)
    (g : Fam (typedOracleFamily lam K (Lf ()))) (t : Tag) (cms : List (Dig lam)) (salt : Bits) (rtreq : Dig lam)
    (r : RS) (Ss : List RS) (A : RoundSplits (up Ss)) (w : WireRB lam K r.up r.lo)
    (W : RoundsQueryLayout lam K (up Ss) A)
    (embP : PlainPart (up (r :: Ss)) (r.lo, A) → PlainPart (Compile.Batch.shapeOf (Lf ()) t) (annOf (Lf ()) t))
    (i : ℕ) (v : Bits) (rts rts' : List (Dig lam)) (rt : List (Dig lam)) (pl : r.Plain)
    (pls : Plains (up Ss)) (ht : takeRt w.depthJ.length rts = some (rt, rts')) :
    chainP Lf g id none t cms (some y : Option X) salt rtreq (r :: Ss) (r.lo, A) (w, W) embP i
        (.loc v) rts (pl, pls) =
      (chainP Lf g id none t cms (some y : Option X) salt rtreq Ss A W
        (fun z => embP (.inr z)) (i + 1)
        (.loc (List.ofFn
            (g (OracleName.fb t)
              (⟨i, .f2 none v, rt,
                embP (.inl (.inr pl))⟩ : FbIn lam (Lf ()) t) : (Fin K → Dig lam) × Dig lam).2))
        rts' pls).map fun z =>
          ((w.chal (g (OracleName.fb t)
                  (⟨i, .f2 none v, rt,
                    embP (.inl (.inr pl))⟩ : FbIn lam (Lf ()) t) : (Fin K → Dig lam) × Dig lam).1,
              z.1),
            ((none, some rt), z.2.1),
            z.2.2) := by
  show (match takeRt w.depthJ.length rts with
    | some (rt, rts') => _
    | none => none) = _
  rw [ht]
  rfl

/-! ## The rounds, by induction -/

section Rounds
variable (Bd : Type) (leaf : Bd → Option (Nat × Nat × ByteArray))
  (O : ByteArray → ByteArray) (hO : ∀ s, (O s).size = 32) (S : _root_.Fmt.Spec) (C : CK)
  (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (dec : View → Bool)
  (hkit : KitFits S.plan.field C K chal) (cms : List (Dig 256)) (salt : Bits) (rtreq : Dig 256)

include hO hkit in
theorem chain_ind :
    ∀ (ds : List RD) (rs : List _root_.Fmt.Round) (ros : List RoundOut) (i : ℕ) (c : Chain)
        (roots : Array ByteArray) (v : Bits)
        (embP : PlainPart (uL C ds) (allLo (SL C ds)) →
          PlainPart (Compile.Batch.shapeOf (LbS Bd C (rds S) dec) .onl)
              (annOf (LbS Bd C (rds S) dec) .onl))
        (pl : Plains (uL C ds)),
      FitL ds rs → (∀ k, S.rounds[i + k]? = rs[k]?) →
      (∀ r ∈ rs, _root_.Fmt.blocksFor (_root_.Fmt.wordsAtMost r.entry r.kind) ≤ K) →
      (∀ n rt z,
        (PDS Bd S C dec leaf).msg n rt (embP z) = msgSL C rt ds (embPL C ds z)) →
      (∀ n z, (PDS Bd S C dec leaf).nonce n (embP z) = nonceSL C ds (embPL C ds z)) →
      c.label = S.label → c.round = i → bitsToBytes v = c.rho →
      TraceL (_root_.Fmt.HO O) S.plan rs ros c roots → plainsSL C ds ros = some pl →
      ∃ (ρ : Rho (uL C ds)) (v' : Bits),
        chainP (fun _ => LbS Bd C (rds S) dec) (famOf O (PDS Bd S C dec leaf) (K + 1))
            id none .onl cms
            (some () : Option Unit) salt rtreq (SL C ds) (allLo (SL C ds)) (wiresSL C K chal ds)
            embP (i + 1) (.loc v)
            ((ros.flatMap fun r => _root_.Fmt.rootsOf r.vals).map bytesToDig) pl =
          some (ρ, rtSL C ds ros, .loc v') ∧
        drawnSL C ds ρ = ros.map (·.drawn) ∧
        passSL C ds ρ = passL (_root_.Fmt.HO O) rs ros c
  | [], [], [], i, c, roots, v, embP, pl, _, _, _, _, _, _, _, _, _, _ => ⟨(), v, rfl, rfl, rfl⟩
  | [], [], _ :: _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ht, _ => ht.elim
  | [], _ :: _, _, _, _, _, _, _, _, hf, _, _, _, _, _, _, _, _, _ => hf.elim
  | _ :: _, [], _, _, _, _, _, _, _, hf, _, _, _, _, _, _, _, _, _ => hf.elim
  | _ :: _, _ :: _, [], _, _, _, _, _, _, _, _, _, _, _, _, _, _, ht, _ => ht.elim
  | d :: ds, r :: rs, ro :: ros, i, c, roots, v, embP, pl, hf, hsuf, hroom, hmsg, hnon, hlab,
      hrnd, hv, ht, hp =>
      by
      obtain ⟨he, hk, hit, htree, hcount, h1, hf'⟩ := hf
      obtain ⟨hask, hwhole, hdrawn, -, -, ht'⟩ := ht
      -- the typed plain parts
      rcases hp0 : PlainOf.ofGots d.items ro.vals with _ | p0
      · simp [plainsSL, hp0] at hp
      rcases hp1 : plainsSL C ds ros with _ | pls
      · simp [plainsSL, hp0, hp1] at hp
      simp only [plainsSL, hp0, hp1, Option.some.injEq] at hp
      subst hp
      -- the round's data in the spellings
      have hr0 : S.rounds[i]? = some r := by simpa using hsuf 0
      have hkind : r.kind.num = (PDS Bd S C dec leaf).kind (i + 1) := by
        show _ = if i + 1 = 0 then 7 else ((S.rounds[i + 1 - 1]?).map (·.kind.num)).getD 7
        rw [if_neg (Nat.succ_ne_zero i), Nat.add_sub_cancel, hr0]
        rfl
      have hwork : (PDS Bd S C dec leaf).work (i + 1) = r.entry.work := by
        show (if i + 1 = 0 then 0 else ((S.rounds[i + 1 - 1]?).map (·.entry.work)).getD 0) = _
        rw [if_neg (Nat.succ_ne_zero i), Nat.add_sub_cancel, hr0]
        rfl
      simp only [_root_.Fmt.askOK, Bool.and_eq_true, and_assoc, decide_eq_true_iff, Bool.or_eq_true,
        bne_iff_ne, beq_iff_eq] at hask
      obtain ⟨-, hrho, -, -, hw64, -, hw0, -⟩ := hask
      -- the root
      have hlen : (_root_.Fmt.rootsOf ro.vals).length = r.entry.roots := by
        rw [roots_ofGots d.items ro.vals p0 hp0, hit, hcount]
      have htake := takeRt_fit (wireS C K chal d).depthJ.length (_root_.Fmt.rootsOf ro.vals)
        (ros.flatMap fun r => _root_.Fmt.rootsOf r.vals)
        (by rw [hlen]; exact (List.length_map _).trans htree) (by rw [hlen]; exact h1)
      have hsz := roots_size S.plan.field r.items ro.msg ro.vals hwhole
      have hrt := map_dig_bytes (_root_.Fmt.rootsOf ro.vals) hsz
      -- message and nonce as the spellings give them
      have hM : (PDS Bd S C dec leaf).msg (i + 1)
            (((_root_.Fmt.rootsOf ro.vals).map bytesToDig).map digToBytes)
            (embP (.inl (.inr (GPlain.mk d.entry.work p0 ro.nonce)))) = ro.msg := by
        rw [hmsg, hrt]
        show bytesL _ d.items
            (GPlain.old (b := d.entry.work) (GPlain.mk d.entry.work p0 ro.nonce)) = _
        rw [old_mk]
        exact (msg_bytes S.plan.field d.items ro.msg ro.vals p0
          (by rw [hit]; exact hwhole) hp0).1
      have hN : (PDS Bd S C dec leaf).nonce (i + 1)
            (embP (.inl (.inr (GPlain.mk d.entry.work p0 ro.nonce)))) = ro.nonce := by
        rw [hnon]
        show GPlain.nonce (b := d.entry.work) (GPlain.mk d.entry.work p0 ro.nonce) = _
        exact nonce_mk p0 ro.nonce d.entry.work (by rw [he]; exact hw0)
      -- the typed answer
      have hrow := famOf_row O hO (PDS Bd S C dec leaf) (K + 1) i v
        ((_root_.Fmt.rootsOf ro.vals).map bytesToDig)
        (embP (.inl (.inr (GPlain.mk d.entry.work p0 ro.nonce)))) r.kind hkind
      rw [hM, hN, hwork, hv] at hrow
      obtain ⟨hu, hnext⟩ := hrow
      have hwE : d.entry.work = r.entry.work := congrArg (·.work) he
      have hu' : ∀ k : Fin (K + 1),
          (famOf O (PDS Bd S C dec leaf) (K + 1) (.fb .onl)
                (⟨i + 1, .f2 none v,
                  (_root_.Fmt.rootsOf ro.vals).map bytesToDig,
                  embP (.inl (.inr
                        (GPlain.mk d.entry.work p0
                          ro.nonce)))⟩ : FbIn 256 (LbS Bd C (rds S) dec) .onl) :
                              (Fin (K + 1) → Dig 256) × Dig 256).1
              k =
            bytesToDig
              (_root_.Fmt.blockW (_root_.Fmt.HO O) (PDS Bd S C dec leaf).label c.rho
                  (i + 1) ro.msg r.kind
                r.entry.work ro.nonce (blockNo d.entry.work (K + 1) k.castSucc)) :=
        fun k => (hu k).trans (by rw [hwE])
      -- the page's row
      have hbs : rowBs (_root_.Fmt.HO O) c r ro =
          _root_.Fmt.fetchW (m := Id) (_root_.Fmt.HO O) S.label c.rho (i + 1)
            ro.msg r.kind r.entry.work ro.nonce
            (_root_.Fmt.firstBlock r.entry.work +
              _root_.Fmt.blocksFor (_root_.Fmt.wordsAtMost r.entry r.kind)) := by
        unfold rowBs
        rw [hlab, hrnd]
        rfl
      have hsize : (rowBs (_root_.Fmt.HO O) c r ro).size =
          _root_.Fmt.firstBlock r.entry.work +
            _root_.Fmt.blocksFor (_root_.Fmt.wordsAtMost r.entry r.kind) := by
        rw [hbs, _root_.Fmt.size_fetchW]
      have hget : ∀ b, b < (rowBs (_root_.Fmt.HO O) c r ro).size →
          (rowBs (_root_.Fmt.HO O) c r ro).getD b ByteArray.empty =
            _root_.Fmt.blockW (_root_.Fmt.HO O) (PDS Bd S C dec leaf).label c.rho (i + 1)
              ro.msg r.kind r.entry.work ro.nonce b := by
        intro b hb
        rw [hsize] at hb
        rw [hbs]
        exact _root_.Fmt.fetchW_getD _ _ _ _ _ _ _ _ _ b hb
      have hfb : 1 ≤ _root_.Fmt.firstBlock r.entry.work := by
        unfold _root_.Fmt.firstBlock; split <;> omega
      have hB32 : ∀ b,
          (_root_.Fmt.blockW (_root_.Fmt.HO O) (PDS Bd S C dec leaf).label c.rho (i + 1)
              ro.msg r.kind r.entry.work ro.nonce b).size = 32 :=
        fun b => size_blockW_HO O hO _ _ _ _ _ _ _ _
      -- the next round
      have hv' : bitsToBytes
            (List.ofFn
              (famOf O (PDS Bd S C dec leaf) (K + 1) (.fb .onl)
                (⟨i + 1, .f2 none v,
                  (_root_.Fmt.rootsOf ro.vals).map bytesToDig,
                  embP (.inl (.inr
                        (GPlain.mk d.entry.work p0
                          ro.nonce)))⟩ : FbIn 256 (LbS Bd C (rds S) dec) .onl) :
                              (Fin (K + 1) → Dig 256) × Dig 256).2) =
          (nextOf (_root_.Fmt.HO O) c r ro).rho := by
        rw [hnext]
        show digToBytes (bytesToDig _) =
          _root_.Fmt.nextA r.entry.work (rowBs (_root_.Fmt.HO O) c r ro)
        rw [TieTree.dig_bytes _ (hB32 _)]
        unfold _root_.Fmt.nextA
        rw [hget _ (by rw [hsize]; omega)]
      obtain ⟨ρ', v'', hch, hdr, hps⟩ :=
        chain_ind ds rs ros (i + 1) (nextOf (_root_.Fmt.HO O) c r ro) _ _
          (fun z => embP (.inr z)) pls hf' (fun k => by
            have := hsuf (k + 1); rw [List.getElem?_cons_succ] at this; rw [← this]; congr 1; omega)
        (fun r' hr' => hroom r' (List.mem_cons_of_mem _ hr')) (fun n rt z => hmsg n rt (.inr z))
          (fun n z => hnon n (.inr z)) hlab (by show c.round + 1 = i + 1; rw [hrnd]) hv' ht' hp1
      refine ⟨((wireS C K chal d).chal
            (famOf O (PDS Bd S C dec leaf) (K + 1) (.fb .onl)
              (⟨i + 1, .f2 none v,
                (_root_.Fmt.rootsOf ro.vals).map bytesToDig,
                embP (.inl (.inr
                      (GPlain.mk d.entry.work p0
                        ro.nonce)))⟩ : FbIn 256 (LbS Bd C (rds S) dec) .onl) :
                            (Fin (K + 1) → Dig 256) × Dig 256).1,
          ρ'),
        v'', ?_, ?_, ?_⟩
      · have hstep := chainP_lo (y := ()) (fun _ => LbS Bd C (rds S) dec)
          (famOf O (PDS Bd S C dec leaf) (K + 1)) .onl cms salt rtreq (roundS C d) (SL C ds)
          (allLo (SL C ds)) (wireS C K chal d) (wiresSL C K chal ds) embP (i + 1) v
          (((ro :: ros).flatMap fun r => _root_.Fmt.rootsOf r.vals).map bytesToDig)
            _ _ (GPlain.mk d.entry.work p0 ro.nonce) pls (by rw [List.flatMap_cons]; exact htake)
        refine hstep.trans ?_
        rw [hch]
        rfl
      · show C.dr d.entry d.kind
              (GChal.old (b := d.entry.work) (chalGrind (chal d.entry d.kind) d.entry.work _)) ::
            drawnSL C ds ρ' =
          ro.drawn :: ros.map (·.drawn)
        obtain ⟨mb, hmb, hmbB⟩ := old_grind (chal d.entry d.kind)
          (_root_.Fmt.blockW (_root_.Fmt.HO O) (PDS Bd S C dec leaf).label c.rho (i + 1)
            ro.msg r.kind r.entry.work ro.nonce)
          d.entry.work _ hu'
        rw [hmb, hdr, hdrawn]
        congr 1
        rw [hwE] at hmbB
        have := drawn_eq _ hB32 r.entry.work _ (rowBs (_root_.Fmt.HO O) c r ro)
          hsize hget S.plan.field C K chal hkit d.entry d.kind (by rw [he, hk])
          (hroom r List.mem_cons_self) mb hmbB
        rw [this, he, hk]
      · show (GChal.pass (b := d.entry.work) (chalGrind (chal d.entry d.kind) d.entry.work _) &&
            passSL C ds ρ') =
          (_root_.Fmt.passesA r.entry.work (rowBs (_root_.Fmt.HO O) c r ro) &&
            passL (_root_.Fmt.HO O) rs ros (nextOf (_root_.Fmt.HO O) c r ro))
        rw [hps,
          pass_grind (chal d.entry d.kind)
            (_root_.Fmt.blockW (_root_.Fmt.HO O) (PDS Bd S C dec leaf).label c.rho (i + 1)
              ro.msg r.kind r.entry.work ro.nonce)
            (rowBs (_root_.Fmt.HO O) c r ro) d.entry.work _ (by rw [hwE]; exact hw64)
            hu' (hget 0 (by rw [hsize]; omega)), hwE]

end Rounds

/-! ## E. The first query, and the whole -/

/-- the typed answer to the first query: its chain value -/
theorem famOf_first {I X : Type} {L : BatchProtocolWithLeafBody I X} (O : ByteArray → ByteArray) (D : PageD L .onl)
    (K : ℕ) (pd : Dig 256) (x : Option X) (salt : Bits) (rt : List (Dig 256))
    (pl : PlainPart (Compile.Batch.shapeOf L .onl) (annOf L .onl)) :
    (famOf O D K (.fb .onl)
        (⟨0, .f1 [pd] x salt, rt, pl⟩ : FbIn 256 L .onl) : (Fin K → Dig 256) × Dig 256).2 =
      bytesToDig
        (O (_root_.Fmt.oStr 0 160 0 D.label _root_.Fmt.zero32
            (Run.firstBytes (digToBytes pd) (D.stm x) salt))) := by
  show ansOf O
      (if (Fin.last K).val = K then
          some
            ⟨0, 160, 0, D.label, _root_.Fmt.zero32, Run.firstBytes (digToBytes pd) (D.stm x) salt⟩
        else none) = _
  rw [if_pos (Fin.val_last K)]
  rfl

/-- the first round: the chain's step -/
theorem chainP_first {I X : Type} {lam K : ℕ} {y : X} (Lf : Unit → BatchProtocolWithLeafBody I X)
    (g : Fam (typedOracleFamily lam K (Lf ()))) (t : Tag) (cms : List (Dig lam)) (salt : Bits) (rtreq : Dig lam)
    (r : RS) (Ss : List RS) (A : RoundSplits (up Ss)) (w : WireRB lam K r.up r.lo)
    (W : RoundsQueryLayout lam K (up Ss) A)
    (embP : PlainPart (up (r :: Ss)) (r.lo, A) → PlainPart (Compile.Batch.shapeOf (Lf ()) t) (annOf (Lf ()) t))
    (rts : List (Dig lam)) (pl : r.Plain) (pls : Plains (up Ss)) (hw : w.depthJ = []) :
    chainP Lf g id none t cms (some y : Option X) salt rtreq (r :: Ss) (r.lo, A) (w, W)
        embP 0 .first rts (pl, pls) =
      (chainP Lf g id none t cms (some y : Option X) salt rtreq Ss A W (fun z => embP (.inr z)) 1
        (.loc (List.ofFn
            (g (OracleName.fb t)
              (⟨0, .f1 cms (some y) salt, [],
                embP (.inl (.inr pl))⟩ : FbIn lam (Lf ()) t) : (Fin K → Dig lam) × Dig lam).2))
        rts pls).map fun z =>
          ((w.chal (g (OracleName.fb t)
                  (⟨0, .f1 cms (some y) salt, [],
                    embP (.inl (.inr pl))⟩ : FbIn lam (Lf ()) t) : (Fin K → Dig lam) × Dig lam).1,
              z.1),
            ((none, some []), z.2.1),
            z.2.2) := by
  show (match takeRt w.depthJ.length rts with
    | some (rt, rts') => _
    | none => none) = _
  rw [hw]
  rfl

/-- THE CHAIN'S HALF. -/
theorem pi_chain : Spec.pi_chain := by
  intro Bd leaf O hO S C K chal dec hok hkit hroom o run pl hL hrun hpl
  obtain ⟨rnd, -, hr⟩ := hL.run
  have hrun32 : run.size = 32 := by
    rw [hrun] at hr
    rw [Option.some.inj hr]
    exact size_HO32 O hO _ _ _ _ _ (by decide)
  have hpd32 : o.pd.size = 32 := by
    rw [hL.pd]
    exact size_HO32 O hO _ _ _ _ _ (by decide)
  have hv : bitsToBytes
    (List.ofFn
      (famOf O (PDS Bd S C dec leaf) (K + 1) (.fb .onl)
        (⟨0, .f1 [bytesToDig o.pd] (some ()) (bytesToBits run),
          [],
          embPS Bd C (rds S) dec
            (.inl (.inr
                ()))⟩ : FbIn 256 (LbS Bd C (rds S) dec) .onl) :
                    (Fin (K + 1) → Dig 256) × Dig 256).2) =
      o.rho0 := by
    rw [hL.rho0 run hrun, famOf_first, firstValue_HO]
    show digToBytes
        (bytesToDig
          (O (_root_.Fmt.oStr 0 160 0 S.label _root_.Fmt.zero32
              (Run.firstBytes (digToBytes (bytesToDig o.pd)) S.statement (bytesToBits run))))) = _
    rw [TieTree.dig_bytes _ (hO _), TieTree.dig_bytes _ hpd32, first_bytes _ _ _ hrun32]
  obtain ⟨ρ, v, hch, hdr, hps⟩ :=
    chain_ind Bd leaf O hO S C K chal dec hkit [bytesToDig o.pd] (bytesToBits run) (fun _ => false)
      (rds S) S.rounds o.rounds.toList 0 ⟨S.label, o.rho0, 0⟩ #[] _
      (fun z => embPS Bd C (rds S) dec (.inr z)) pl (fit_rds S hok) (fun k => by rw [Nat.zero_add])
      hroom (fun _ _ _ => rfl) (fun _ _ => rfl) rfl rfl hv hL.trace hpl
  refine ⟨ρ, v, ?_, hdr, hps⟩
  refine (chainP_first (y := ()) (fun _ => LbS Bd C (rds S) dec)
      (famOf O (PDS Bd S C dec leaf) (K + 1)) .onl
    [bytesToDig o.pd] (bytesToBits run) (fun _ => false) (s0 C) (SL C (rds S))
    (allLo (SL C (rds S))) (wire0S C K chal) (wiresSL C K chal (rds S)) (embPS Bd C (rds S) dec)
    ((rootsB o).map bytesToDig) () pl rfl).trans ?_
  have hch' := hch
  rw [show (0 : ℕ) + 1 = 1 from rfl] at hch'
  show Option.map _
      (chainP _ _ id none .onl _ _ _ _ (SL C (rds S)) _ _ _ 1 _
        ((o.rounds.toList.flatMap fun r => _root_.Fmt.rootsOf r.vals).map bytesToDig) pl) = _
  rw [hch']
  show some ((_, ρ), _) = some ((default, ρ), _)
  rw [Subsingleton.elim ((wire0S C K chal).chal _) default]

end TypedOracleCompiler.Run.PQ
