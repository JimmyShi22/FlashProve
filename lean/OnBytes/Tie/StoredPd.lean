-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/StoredPd.lean: a chain with stored tables that the strict reader has read, and on which
the decision says yes, is accepted by the compiled verifier's thin form; with the digest of the
parameter bytes as an argument.

OnBytes/Tie/StoredExt.lean, StoredChain.lean, StoredTop.lean and StoredMain.lean prove that under
the typed oracle functions `Run.PQ.famX`, which hold the format's own digest of the parameter bytes
as a constant, for a function O whose hash gives that digest on these bytes. This file says ten of
their declarations again under `famXPd` (OnBytes/Tie/FamPd.lean), for a function O whose hash gives
ANY byte string pd on these bytes. These ten are all that name the family at a function O that is
free. Two more name it at the format's own oracle (`CompiledAcceptsX`, `stored_VX`, StoredMain.lean)
and stay as they are. The others do not name it and are imported.

The text is that of the four files, with `famXPd D dec pd O` for `famX D dec O`, pd for the
constant, and pd handed on where one of the ten calls another. So four statements differ in more
than the family's name: `famXPd_first` spells pd, and the hypothesis `hpd` of `chainXPd`,
`verifyX_truePd` and `stored_corePd` has pd on its right side. Of the proofs one step uses that: the
one in `chainXPd` that rewrites by `hpd`. The four files are not changed; each of their ten follows
from its like here at pd := `Fmt.paramsDigest` of the parameter bytes, by rewriting with
`famX_eq_pd`. That is a reading: it is not stated here. For the two definitions above them it is
proved (`digestAt_iff_pd`, `compiledAcceptsXAt_iff_pd`, OnBytes/Tie/StoredAtPd.lean).

Main theorems: `famXPd_leaf`, `famXPd_node`, `ext_forestPd`; `famXPd_round`, `famXPd_first`,
`chainXPd`; `leaf_agreePd`, `afterXPd`, `verifyX_truePd`; `stored_corePd`.

This file doubles text of the four files. The text could stand once: the ten stated there with pd,
as here, and the four files' names as the case pd := `Fmt.paramsDigest` of the parameter bytes, one
rewriting by `famX_eq_pd` each. With the four as they are: `Run.Thin.afterP` reads its family at
leaves and vertices alone, where `famXPd` does not read pd, so a congruence lemma for it (about 25
lines) would spare `famXPd_leaf`, `famXPd_node`, `ext_forestPd`, `leaf_agreePd`, `afterXPd`. If the
library's `firstX` and `famX` took pd as an argument, OnBytes/Tie/FamPd.lean would not be needed
either.

What is not claimed. What the heads of the four files do not claim. Nothing on soundness; no
probability. For a function O whose hash gives another value than pd on the parameter bytes nothing
is said.

-/
import OnBytes.Tie.StoredMain
import OnBytes.Tie.FamPd

set_option autoImplicit false

namespace OnBytes.Tie
open Rom Iop Compile Compile.Batch Run Run.PQ Run.Twin Run.Thin

section
variable (D : XD) (dec : View → Bool) (pd : ByteArray) (O : ByteArray → ByteArray)
  (hO : ∀ s, (O s).size = 32)

/-- If the configuration's digest has 32 bytes, the typed leaf function at a symbol of a stored
table, with the typed salt `leafSalt cfg s`, is the format's call 174. Nothing is said of another
typed salt. -/
theorem famXPd_leaf (x : ℕ) (col : List UInt64) (s : ByteArray) (hc : D.base.cfg.size = 32) :
    (famXPd D dec pd O (D.K + 1) .leaf
        (⟨some (.inl (x, col)), leafSalt D.base.cfg s⟩ : LeafIn (D.L dec)) : Dig 256)
      = bytesToDig (Fmt.HO O 174 (Fmt.leafPlace 0 col.length (s.size / 8)) (2 ^ D.a + x)
          D.base.cfg (Fmt.leafBytes col s)) := by
  -- The typed salt is the 256 bits of cfg and then the bits of s.
  have hl : (bytesToBits D.base.cfg).length = 256 := by rw [length_bytesToBits, hc]
  have hfront : bitsToBytes ((leafSalt D.base.cfg s).take 256) = D.base.cfg := by
    unfold leafSalt
    rw [List.take_left' hl, bitsToBytes_bytesToBits]
  have hback : bitsToBytes ((leafSalt D.base.cfg s).drop 256) = s := by
    unfold leafSalt
    rw [List.drop_left' hl, bitsToBytes_bytesToBits]
  -- The number of the salt's words of 64 bits is the number of its words of 8 bytes.
  have hwords : ((leafSalt D.base.cfg s).length - 256) / 64 = s.size / 8 := by
    unfold leafSalt
    rw [List.length_append, hl, length_bytesToBits]
    omega
  -- So the test on the salt's front holds, and the leaf is spelled as call 174.
  have hcall : leafX D dec ⟨some (.inl (x, col)), leafSalt D.base.cfg s⟩
      = some ⟨0, 174, Fmt.leafPlace 0 col.length (s.size / 8), 2 ^ D.a + x, D.base.cfg,
          Fmt.leafBytes col s⟩ := by
    show (if bitsToBytes ((leafSalt D.base.cfg s).take 256) == D.base.cfg then
        some (⟨0, 174,
          Fmt.leafPlace 0 col.length (((leafSalt D.base.cfg s).length - 256) / 64),
          2 ^ D.a + x, D.base.cfg,
          Fmt.leafBytes col (bitsToBytes ((leafSalt D.base.cfg s).drop 256))⟩ : Fmt.OQ)
      else none) = _
    rw [hfront, hback, hwords, if_pos (bytes_beq_self D.base.cfg)]
  show ansOf O (leafX D dec ⟨some (.inl (x, col)), leafSalt D.base.cfg s⟩) = _
  rw [hcall]
  -- `Fmt.HO` asks O once under every number but 162.
  rfl

/-- The typed node function is the format's call 166. -/
theorem famXPd_node :
    nodeP (fun _ => D.L dec) (famXPd D dec pd O (D.K + 1))
      = TieTree.digFn (fun l r => Fmt.HO O 166 0 0 D.base.cfg (l ++ r)) := by
  funext l r
  -- Both sides are the answer of O at the string of call 166 on the bytes of l and then of r.
  show ansOf O (nodeCallC D.base.cfg (List.ofFn l, List.ofFn r))
    = bytesToDig (Fmt.HO O 166 0 0 D.base.cfg (digToBytes l ++ digToBytes r))
  exact node_call O D.base.cfg (List.ofFn l) (List.ofFn r)

include hO in
/-- The forest of the two stored tables, given `StoOK`, with O's answers, the roots and the
configuration's digest of 32 bytes, and "read" taken to be what the openings list (`readOf`): there
is one; it has as many checks as places are listed; each check is well formed and of the tables'
depth; its walk ends in the roots of the tables that are opened. A table that is not opened is not
walked. -/
theorem ext_forestPd (r0 r1 : ByteArray) (h0 : r0.size = 32) (h1 : r1.size = 32)
    (hc : D.base.cfg.size = 32) (sto : List (Bool × ℕ × OpenB))
    (hs : StoOK O D.base.cfg D.a D.base.plan.salt r0 r1 sto) :
    ∃ Fx : Forest 256 (D.L dec),
      forestExtP (fun _ => D.L dec) (weX D.a) (fun s => some (.inl s))
        [bytesToDig r0, bytesToDig r1] (fun p => decide (p ∈ readOf D.a sto))
        (extOf D.a D.base.cfg (tabsOf sto)) = some [Fx] ∧
      (flatP (fun _ => D.L dec) [Fx]).length = (sto.map (·.2.2.idx.length)).sum ∧
      (∀ c ∈ flatP (fun _ => D.L dec) [Fx], wellP (fun _ => D.L dec) c = true ∧ c.depth = D.a) ∧
      runForestP (fun _ => D.L dec) (famXPd D dec pd O (D.K + 1)) Fx
        (readsOneP (fun _ => D.L dec) Fx) = true := by
  have k0 : TabOK O D.base.cfg D.a D.base.plan.salt r0 (tabAt D.a sto false) := tabOK_of hs false
  have k1 : TabOK O D.base.cfg D.a D.base.plan.salt r1 (tabAt D.a sto true) := tabOK_of hs true
  refine ⟨twoF (fun _ => D.L dec) (fun s => some (.inl s)) D.base.cfg D.a
    (fun t => [bytesToDig r0, bytesToDig r1].getD t default) (tabAt D.a sto false).2
    (tabAt D.a sto true).2, ?_, ?_, ?_, ?_⟩
  · exact forest_two (fun _ => D.L dec) (fun s => some (.inl s)) [bytesToDig r0, bytesToDig r1]
      D.a D.base.plan.salt D.base.cfg sto hs.once hs.ok hs.depth
  · rw [length_two (fun _ => D.L dec) (fun s => some (.inl s)) D.base.cfg D.a D.base.plan.salt _
      (tabAt D.a sto false) (tabAt D.a sto true) k0.ok k1.ok]
    exact (sum_two D.a (fun T => T.2.idx.length) rfl sto hs.once).symm
  · exact well_two (fun _ => D.L dec) (fun s => some (.inl s)) D.base.cfg D.a D.base.plan.salt _
      (tabAt D.a sto false) (tabAt D.a sto true) k0.ok k1.ok k0.depth k1.depth
  · exact run_two (fun _ => D.L dec) (fun s => some (.inl s)) (famXPd D dec pd O (D.K + 1)) O hO
      D.base.cfg D.a D.base.plan.salt r0 r1 h0 h1 (famXPd_node D dec pd O)
      (fun x col s => famXPd_leaf D dec pd O x col s hc) _ rfl rfl (tabAt D.a sto false)
      (tabAt D.a sto true) k0 k1

end

section
variable (D : XD) (dec : View → Bool) (pd : ByteArray)

/-- Behind the first query, the typed chain functions of the case with stored tables are those of
the plain case. -/
theorem famXPd_round (O : ByteArray → ByteArray) (j : ℕ) (v : Bits) (rt : Option (Dig 256))
    (z : PlainPart (uL D.C D.ds) (allLo (SL D.C D.ds))) :
    (Run.famOf O (PDS D.base D.C dec) (D.K + 1) (.fb .onl)
        (⟨j, .f2 none v, rt, embPS D.C D.ds dec (.inr z)⟩ :
          FbIn 256 (LbS D.C D.ds dec) .onl) : (Fin (D.K + 1) → Dig 256) × Dig 256)
      = (famXPd D dec pd O (D.K + 1) (.fb .link)
        (⟨j, .f2 none v, rt, embPX D.C D.ds D.a D.xs dec (fun _ _ p => (p.val, []))
          (fun _ => some ()) (.inr z)⟩ : FbIn 256 (D.L dec) .link) :
          (Fin (D.K + 1) → Dig 256) × Dig 256) := by
  cases j <;> rfl

/-- In the case with stored tables, the chain value in the typed answer to the first query is O's
answer at the format's first call, with pd in the place of the parameters' digest, and `stm` of the
two roots. -/
theorem famXPd_first (O : ByteArray → ByteArray) (cm cm' : Dig 256) (salt : Bits)
    (rt : Option (Dig 256))
    (pl : PlainPart (Compile.Batch.shapeOf (D.L dec) .link) (annOf (D.L dec) .link)) :
    (famXPd D dec pd O (D.K + 1) (.fb .link)
        (⟨0, .f1 [cm, cm'] none salt, rt, pl⟩ : FbIn 256 (D.L dec) .link) :
          (Fin (D.K + 1) → Dig 256) × Dig 256).2 =
      bytesToDig (O (Fmt.oStr 0 160 0 D.base.label Fmt.zero32
        (Run.firstBytes pd
          (D.stm (digToBytes cm) (digToBytes cm')) salt))) := by
  show ansOf O (if (Fin.last (D.K + 1)).val = D.K + 1 then some ⟨0, 160, 0, D.base.label,
    Fmt.zero32, Run.firstBytes pd
      (D.stm (digToBytes cm) (digToBytes cm')) salt⟩ else none) = _
  rw [if_pos (Fin.val_last (D.K + 1))]
  rfl

/-- The compiled verifier's chain at the tag "link", on the run value, roots and plain parts of a
chain output o. It yields what the plain case's chain yields: the draws of o's rounds, and work that
passes exactly if o's does. The hypotheses: O's answers, r0 and r1 have 32 bytes; the own part is
within the library's limits; the statement is `D.stm r0 r1`; o has `LaxFacts` and a run value, and
its `pd` is pd; pl types its plain parts. -/
theorem chainXPd (O : ByteArray → ByteArray) (hO : ∀ s, (O s).size = 32) (r0 r1 : ByteArray)
    (hok : PQ.ok D.base = true)
    (hst : D.base.statement = D.stm r0 r1) (h0 : r0.size = 32) (h1 : r1.size = 32)
    (o : Fmt.ChainOut) (run : ByteArray) (pl : Plains (uL D.C D.ds))
    (hL : LaxFacts (Fmt.HO O) D.base o) (hpd : o.pd = pd)
    (hrun : o.run = some run) (hpl : plainsSL D.C D.ds o.rounds.toList = some pl) :
    ∃ (ρ : Rho (uL D.C D.ds)) (v : Bits),
      chainP (fun _ => D.L dec) (famXPd D dec pd O (D.K + 1)) id none .link
          [bytesToDig r0, bytesToDig r1] (none : Option Unit) (bytesToBits run) (fun _ => false)
          (SOf D.C D.ds) (allLo (SOf D.C D.ds))
          (wqX D.C D.K (chalP D.base.plan.field D.K) D.ds D.a D.xs dec).sh
          (embPX D.C D.ds D.a D.xs dec (fun _ _ p => (p.val, [])) (fun _ => some ())) 0 .first
          ((rootsB o).map bytesToDig) ((), pl)
        = some ((default, ρ), ((none, some none), rtSL D.C D.ds o.rounds.toList), .loc v) ∧
      drawnSL D.C D.ds ρ = o.rounds.toList.map (·.drawn) ∧
      passSL D.C D.ds ρ
        = passL (Fmt.HO O) D.base.rounds o.rounds.toList ⟨D.base.label, o.rho0, 0⟩ := by
  obtain ⟨ρ, v, hc, hd, hp⟩ := pi_chain O hO D.base D.C D.K
    (chalP D.base.plan.field D.K) dec hok (kit_pull _ _) (room_kOf D.base) o run pl hL hrun hpl
  refine ⟨ρ, v, ?_, hd, hp⟩
  rw [← hc]
  have hpd32 : o.pd.size = 32 := by
    rw [hL.pd]
    exact size_HO32 O hO _ _ _ _ _ (by decide)
  have htail : (famXPd D dec pd O (D.K + 1) (.fb .link)
        (⟨0, .f1 [bytesToDig r0, bytesToDig r1] none (bytesToBits run), none,
          embPX D.C D.ds D.a D.xs dec (fun _ _ p => (p.val, [])) (fun _ => some ())
            (.inl (.inr ()))⟩ : FbIn 256 (D.L dec) .link) : (Fin (D.K + 1) → Dig 256) × Dig 256).2
      = (Run.famOf O (PDS D.base D.C dec) (D.K + 1) (.fb .onl)
        (⟨0, .f1 [bytesToDig o.pd] (some ()) (bytesToBits run), none,
          embPS D.C D.ds dec (.inl (.inr ()))⟩ : FbIn 256 (LbS D.C D.ds dec) .onl) :
          (Fin (D.K + 1) → Dig 256) × Dig 256).2 := by
    rw [famXPd_first, famOf_first, TieTree.dig_bytes _ h0, TieTree.dig_bytes _ h1,
      TieTree.dig_bytes _ hpd32, hpd, ← hst]
    rfl
  refine (chainP_first_none (fun _ => D.L dec) (famXPd D dec pd O (D.K + 1)) .link
    [bytesToDig r0, bytesToDig r1] (bytesToBits run) (fun _ => false) (s0 D.C) (SL D.C D.ds)
    (allLo (SL D.C D.ds)) (wire0S D.C D.K (chalP D.base.plan.field D.K))
    (wiresSL D.C D.K (chalP D.base.plan.field D.K) D.ds)
    (embPX D.C D.ds D.a D.xs dec (fun _ _ p => (p.val, [])) (fun _ => some ()))
    ((rootsB o).map bytesToDig) () pl rfl).trans ?_
  refine Eq.trans ?_ (chainP_first (y := ()) (fun _ => LbS D.C D.ds dec)
    (Run.famOf O (PDS D.base D.C dec) (D.K + 1)) .onl [bytesToDig o.pd]
    (bytesToBits run) (fun _ => false) (s0 D.C) (SL D.C D.ds) (allLo (SL D.C D.ds))
    (wire0S D.C D.K (chalP D.base.plan.field D.K))
    (wiresSL D.C D.K (chalP D.base.plan.field D.K) D.ds) (embPS D.C D.ds dec)
    ((rootsB o).map bytesToDig) () pl rfl).symm
  have hcong := chainP_congr (fun _ => D.L dec) (fun _ => LbS D.C D.ds dec)
    (famXPd D dec pd O (D.K + 1)) (Run.famOf O (PDS D.base D.C dec) (D.K + 1))
    .link .onl [bytesToDig r0, bytesToDig r1] [bytesToDig o.pd] none (some ()) (bytesToBits run)
    (bytesToBits run) (fun _ => false) (fun _ => false) (SL D.C D.ds)
    (wiresSL D.C D.K (chalP D.base.plan.field D.K) D.ds)
    (fun z => embPX D.C D.ds D.a D.xs dec (fun _ _ p => (p.val, [])) (fun _ => some ()) (.inr z))
    (fun z => embPS D.C D.ds dec (.inr z)) 1
    (List.ofFn (Run.famOf O (PDS D.base D.C dec) (D.K + 1) (.fb .onl)
        (⟨0, .f1 [bytesToDig o.pd] (some ()) (bytesToBits run), none,
          embPS D.C D.ds dec (.inl (.inr ()))⟩ : FbIn 256 (LbS D.C D.ds dec) .onl) :
          (Fin (D.K + 1) → Dig 256) × Dig 256).2)
    ((rootsB o).map bytesToDig) pl (fun j v rt z => (famXPd_round D dec pd O j v rt z).symm)
  rw [htail]
  rw [hcong]
  refine congrArg (fun f => Option.map f _) (funext fun z => ?_)
  exact congrArg (fun c => ((c, z.1), ((none, some none), z.2.1), z.2.2)) (Subsingleton.elim _ _)

end

section
variable (D : XD) (dec : View → Bool) (pd : ByteArray) (O : ByteArray → ByteArray)
  (hO : ∀ s, (O s).size = 32)

/-- The two cases' typed leaf functions agree along `toLink`. -/
theorem leaf_agreePd (b : Body (LbS D.C D.ds dec)) (salt : Bits) :
    (famXPd D dec pd O (D.K + 1) OracleName.leaf (⟨toLink D dec b, salt⟩ : LeafIn (D.L dec)) : Dig 256)
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
theorem afterXPd (r0 r1 : ByteArray) (h0 : r0.size = 32) (h1 : r1.size = 32)
    (hok : PQ.ok D.base = true) (hc : D.base.cfg.size = 32)
    (oo : Fmt.ChainOut) (run : ByteArray) (pl : Plains (uL D.C D.ds)) (ρ : Rho (uL D.C D.ds))
    (v : Bits) (sto : List (Bool × ℕ × OpenB))
    (hf : LaxFacts (Fmt.HO O) D.base oo) (hr : oo.run = some run)
    (hd : drawnSL D.C D.ds ρ = oo.rounds.toList.map (·.drawn))
    (hroots : rootsAll (Fmt.HO O) D.base.cfg run oo.rounds.toList = true)
    (hs : StoOK O D.base.cfg D.a D.base.plan.salt r0 r1 sto)
    (hx : xWanted D.a D.ds D.xs (drawnSL D.C D.ds ρ) = askedOf sto)
    (hcnt : (sto.map (·.2.2.idx.length)).sum ≤ (D.xs.map (·.count)).sum) :
    afterP (fun _ => D.L dec) (famXPd D dec pd O (D.K + 1)) (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec)
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
  obtain ⟨Fx, x1, x2, x3, x4⟩ := ext_forestPd D dec pd O hO r0 r1 h0 h1 hc sto hs
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
  have hrun1 : runForestsP (fun _ => D.L dec) (famXPd D dec pd O (D.K + 1))
      (Fs.map (mapF (toLink D dec))) (readsP (fun _ => D.L dec) (Fs.map (mapF (toLink D dec))))
      = true := by
    rw [readsP_map, runForestsP_map (toLink D dec)
      (Run.famOf O (PDS D.base D.C dec) (D.K + 1)) (famXPd D dec pd O (D.K + 1)) (fun q => rfl) Fs _
      (fun c _ => leaf_agreePd D dec pd O c.inp.body c.inp.salt)]
    have h4 := g4 [] []
    rw [List.append_nil, List.append_nil] at h4
    rw [h4, tree_roots O D.base D.C dec oo run hok hf, hroots]
    rfl
  unfold afterP
  rw [hFo]
  dsimp only
  rw [if_pos ⟨hlen, hall⟩, hrd, runForestsP_append, hrun1,
    runForests_cons (K := D.K) (famXPd D dec pd O (D.K + 1)) Fx [] [], x4]
  rfl

include hO in
/-- All parts together. If the decision says yes on the view of o (hdec), then the library's typing
of o gives a string, and the evaluable form of the compiled verifier says yes on it. The other
hypotheses are bounds, limits on the description, and what the strict reader has checked of o: O's
answers, r0, r1 and the configuration's digest have 32 bytes; the own part is within the library's
limits; the statement is `D.stm r0 r1`; o is rc with the stored openings joined in, oo its own part,
both with the run value run; oo has `LaxFacts`, its `pd` is pd,
all its work has passed and all its own openings have walked to their roots; each stored opening has
`StoredFact`, all have `StoOK`, one depth and items 0 or 1; and every part of the draws is full. -/
theorem verifyX_truePd (r0 r1 : ByteArray) (h0 : r0.size = 32) (h1 : r1.size = 32)
    (hok : PQ.ok D.base = true) (hst : D.base.statement = D.stm r0 r1)
    (hc : D.base.cfg.size = 32) (o oo : Fmt.ChainOut)
    (run : ByteArray)
    (rc : List (Fmt.RoundOut × List (Fmt.Shape × List ℕ × Fmt.OpenOut)))
    (hoo : oo.rounds.toList = rc.map fun p => stripR p.1) (ho : o.rounds.toList = rc.map roundWithStoredOpenings)
    (hr : o.run = some run) (hrr : oo.run = some run)
    (hL : LaxFacts (Fmt.HO O) D.base oo) (hpd : oo.pd = pd)
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
      verifyP (fun _ => D.L dec) (famXPd D dec pd O (D.K + 1)) id none
          (256 + 8 * D.base.plan.salt) 256
        .link (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec)
        (wqX D.C D.K (chalP D.base.plan.field D.K) D.ds D.a D.xs dec)
        (fun p s => some (.inr ⟨Tag.link, ⟨p, s⟩⟩))
        (embPX D.C D.ds D.a D.xs dec (fun _ _ p => (p.val, [])) (fun _ => some ()))
        (fun _ => none) (fun s => some (.inl s)) 0 [bytesToDig r0, bytesToDig r1] () π = true := by
  obtain ⟨run', pl, hr', hpl, -⟩ := pi_typed' (Fmt.HO O) D.base D.C dec oo hL
  obtain ⟨ρ, v, hch, hd, hp⟩ := chainXPd D dec pd O hO r0 r1 hok hst h0 h1 oo run pl hL hpd hrr hpl
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
  have hch' : chainP (fun _ => D.L dec) (famXPd D dec pd O (D.K + 1)) id none .link
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
    afterXPd D dec pd O hO r0 r1 h0 h1 hok hc oo run pl ρ v _ hL hrr hd hroots hs hx
      (sto_count (Fmt.HO O) D o rc ho hS)]
  exact acceptX D dec O r0 r1 hok o oo run pl ρ hL hpl hd rc hoo ho hS hD hs (hp.trans hpass)
    (by rw [hd]; exact hfull) hx hdec

end

section
variable (S : Fmt.SpecX) (stm : ByteArray → ByteArray → ByteArray) (dec : View → Bool)
  (pd : ByteArray) (O : ByteArray → ByteArray) (hO : ∀ s, (O s).size = 32)

include hO in
/-- If the strict reader, at the hash that O induces, has read a chain that opens stored tables and
the decision is yes, the typing gives a typed string and the evaluable form of the compiled verifier
accepts it. O is any function on byte strings with answers of 32 bytes whose digest of the
parameters is pd (`hpd`). The other hypotheses are those of `stored_VX` without `smallFX`,
with the clauses of `withinX` one by one. -/
theorem stored_corePd (r0 r1 : ByteArray) (h0 : r0.size = 32) (h1 : r1.size = 32)
    (hok : (xdOf S stm).ok = true) (hn : S.base.rand.isNone = false)
    (honce : (S.stored.flatten.map (·.item == 1)).Nodup)
    (hst : S.base.statement = stm r0 r1)
    (hroot : ∀ t ∈ S.stored.flatten,
      Fmt.itemRoot S.base.statement t.item = some (if t.item == 1 then r1 else r0))
    (hpd : Fmt.HO O 169 0 1 Fmt.zero32 S.base.params = pd)
    (seen : Fmt.Seen) (b : ByteArray) (i : ℕ) (o : Fmt.ChainOut) (j : ℕ)
    (e : Fmt.readChainX (m := Id) (Fmt.HO O) S seen b i = some (o, j))
    (hdec : dec (Fmt.viewX S o) = true) :
    ∃ π, toBPrfX S.base.plan.salt S.base.cfg (xdOf S stm).C (xdOf S stm).ds (xdOf S stm).a
        (xdOf S stm).xs dec o = some π ∧
      verifyP (fun _ => (xdOf S stm).L dec) (famXPd (xdOf S stm) dec pd O
          ((xdOf S stm).K + 1)) id none
        (256 + 8 * S.base.plan.salt) 256 .link
        (skeletonOverBothExternalStrings (xdOf S stm).C (xdOf S stm).ds (xdOf S stm).a (xdOf S stm).xs dec)
        (wqX (xdOf S stm).C (xdOf S stm).K (chalP S.base.plan.field (xdOf S stm).K)
          (xdOf S stm).ds (xdOf S stm).a (xdOf S stm).xs dec)
        (fun p s => some (.inr ⟨Tag.link, ⟨p, s⟩⟩))
        (embPX (xdOf S stm).C (xdOf S stm).ds (xdOf S stm).a (xdOf S stm).xs dec
          (fun _ _ p => (p.val, [])) (fun _ => some ()))
        (fun _ => none) (fun s => some (.inl s)) 0 [bytesToDig r0, bytesToDig r1] () π = true := by
  have hok' := hok
  unfold XD.ok at hok'
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq] at hok'
  obtain ⟨⟨hokb, -⟩, hall⟩ := hok'
  have hbok : (inFile S.base).ok = true := base_ok _ hokb
  obtain ⟨hSok, x, i0, hd, s, hr, hst', hf, rfl, rfl⟩ := readX_stages (Fmt.HO O) S seen b i o j e
  obtain ⟨rnd, rfl⟩ := rnd_some S.base b i x i0 hn hr
  obtain ⟨hdrun, rho0⟩ := hd
  obtain ⟨h32, hrun, hrho⟩ := startChain_some (Fmt.HO O) _ _ _ _ _ hst'
  obtain ⟨R, hR⟩ : ∃ R : ByteArray, hdrun = some R := ⟨_, hrun⟩
  subst hR
  have hown : ∀ r ∈ S.base.rounds.zip S.stored, ∀ x ∈ r.1.opens, ∃ n, x.2 = .own n :=
    fun r hr' => own_of_ok (inFile S.base) hokb r.1 (List.of_mem_zip hr').1
  obtain ⟨rc, g1, g2, g3, g4, g5⟩ := foldX_facts (Fmt.HO O) S.base.cfg S.base.statement S.base.plan
    R b (S.base.rounds.zip S.stored) _ s hown hf
  have hlen := specX_len S hSok
  have hfst : (S.base.rounds.zip S.stored).map (·.1) = S.base.rounds :=
    List.map_fst_zip (le_of_eq hlen.symm)
  have hsnd : (S.base.rounds.zip S.stored).map (·.2) = S.stored :=
    List.map_snd_zip (le_of_eq hlen)
  rw [hfst] at g2 g3
  have g1' : s.out.toList = rc.map roundWithStoredOpenings := by simpa using g1
  have ht : ((rc.map fun p => stripR p.1).toArray).toList = rc.map fun p => stripR p.1 := by simp
  have hF : List.Forall₂ (fun (ts : List Fmt.Stored)
        (p : Fmt.RoundOut × List (Fmt.Shape × List ℕ × Fmt.OpenOut)) =>
      List.Forall₂ (StoredFact (Fmt.HO O) S.base.cfg S.base.statement p.1.drawn.poss) ts p.2)
      S.stored rc := by
    rw [← hsnd]
    exact List.forall₂_map_left_iff.2 (g5.imp fun _ _ hh => hh.2)
  have hfull : everyOpeningHasItsDraws (xdOf S stm).xs ((rc.map fun p => stripR p.1).map (·.drawn)) = true := by
    refine fullX_true S.stored _ ?_
    rw [← hsnd, List.map_map]
    refine List.forall₂_map_left_iff.2 (List.forall₂_map_right_iff.2 ?_)
    refine (forall2_and_left g5 (specX_parts S hSok)).imp fun x p hh t ht' => ?_
    show t.lo + t.count ≤ p.1.drawn.poss.length
    rw [hh.1.1]
    exact hh.2 t ht'
  have hL : LaxFacts (Fmt.HO O) (inFile S.base)
      (ownOut (Fmt.HO O 169 0 1 Fmt.zero32 S.base.params) R rho0 s.chain.rho rc) := by
    refine ⟨rfl, ⟨rnd, h32, hrun⟩, ?_, ?_⟩
    · intro r hr'
      have hr2 : some r = some _ := hr'.symm.trans hrun
      rw [Option.some.inj hr2]
      exact hrho
    · show TraceL (Fmt.HO O) S.base.plan S.base.rounds
        ((rc.map fun p => stripR p.1).toArray).toList ⟨S.base.label, rho0, 0⟩ #[]
      rw [ht]
      exact g2
  exact verifyX_truePd (xdOf S stm) dec pd O hO r0 r1 h0 h1 hokb hst
    (beq_iff_eq.1 (Fmt.ok_cfg hbok))
    _ (ownOut (Fmt.HO O 169 0 1 Fmt.zero32 S.base.params) R rho0 s.chain.rho rc) R rc ht g1' rfl rfl
    hL hpd
    (by
      show passL (Fmt.HO O) S.base.rounds ((rc.map fun p => stripR p.1).toArray).toList
        ⟨S.base.label, rho0, 0⟩ = true
      rw [ht]
      exact g3)
    (by
      show rootsAll (Fmt.HO O) S.base.cfg R ((rc.map fun p => stripR p.1).toArray).toList = true
      rw [ht]
      exact g4)
    hF (fun t ht' => ⟨(hall t ht').1.1, (hall t ht').2⟩)
    (stoOK_of S stm O r0 r1 hSok _ rc g1' hF (fun t ht' => ⟨(hall t ht').1.1, (hall t ht').1.2⟩)
      honce hroot)
    (by
      show everyOpeningHasItsDraws (xdOf S stm).xs (((rc.map fun p => stripR p.1).toArray).toList.map (·.drawn))
        = true
      rw [ht]
      exact hfull)
    hdec

end

end OnBytes.Tie
