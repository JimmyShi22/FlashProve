-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/ChainERead.lean: THE CHAIN's HALF FOR ONE CHAIN (AN ENTRY FILE's): FROM ONE YES OF
THE STRICT READER TO chainP AT A SKELETON OF skeletonOverBothExternalStrings's MAKE. The small case of Run/ChainF |
ChainFRead. A piece of "the tie at H_b" for an entry file (LinkE). The compiler under OnBytes/TypedOracleCompiler/
is the one that `innerCompiledVerifier` is made with; it builds on definitions of Compile/.
WHY. An entry file has ONE chain: no joining round, no seal. entryRead_ok hands Fmt.readChainX (m :=
Id) h spec [] file j = some (o, next). The typed side: the first round .f1 cms (early x) salt (for
E:
cms = [cm, cm′]) WITHOUT A ROOT, then the written rounds, all local.
AT WHICH TERMS: THE SKELETON's OWN: S := SOf C ds = s0 C :: SL C ds; annotation allLo (SOf C ds);
wires (wire0S C K chal, wiresSL C K chal ds): WHAT skeletonOverBothExternalStrings | wqX (Run/PlanQX.lean) AND PSof | wqS
HOLD. RoundSplits.allLocal (uL C ds) = allLo (SL C ds) IS NOT rfl AT A VARIABLE ds (by Lean): so nothing
here applies BY TYPE at LXE's .link (annotation RoundSplits.allLocal): the one equation from a skeleton to
that protocol is not here.
  chain_one        from StretchFacts, RowEnd (typed rounds 1, 2, …; the format's indices c.round +
                   1, …) and the first query's law hs0 (the typed tail at ⟨0, .f1 cms (early x)
                   salt, [], the first round's plain part⟩ is c.rho): chainP … (SOf C ds) (allLo
                   (SOf C ds)) (wire0S …, wiresSL …) embP 0 .first (rootsD ros ++ rest) ((), pls)
                       = some (ρ, ((none, some []), rtSL C ds ros), .loc v') ∧ drawnSL C ds ρ.2 =
                       ros.map drawn ∧ passSL C ds ρ.2 = the reader's passL. ANY interface, family,
                       tag, outer roots, instance; late names no written round
  ReadE, chain_one_read     the same from ONE yes of Fmt.readChainX at HO O, READ AT THE READER's
                            OWN o.rounds; ALL TYPED TESTS OF WORK PASS. Asked, in one record: the
                            yes; FitL ds S.base.rounds and room (the description's); the chain has a
                            round; the typed plain parts are plainsSL of o.rounds; RowEnd (row) and
                            the first query's law (first) at
                       S.base.label | o.rho0; late names no written round
  pi_chain (Run/PageIsChain.lean) is the old pattern: one named family, the lenient reader's facts,
  x := some (), early id, late none.
  seal_sealRead    [beside: for F] THE PORT's ChainRead.seal IS sealRead (Run/ChainFRead.lean):
                   r.seal = some x → sealRead r.out = x (seal_eq): WITH Run/SealDigest | SealJoints
                   THIS CLOSES "chain_whole_read's slot value is Run/ReqClimb.lean's closing"
WHAT IS NOT SAID. THAT ANY g HAS RowEnd AND THE FIRST QUERY's LAW (the page of E under a record;
Run/RowsE2.lean: rowEndE | s0E at embP := wayE D early e: in these letters; not checked here). "fit"
and "room": the description's. The equation to LXE's protocol. What follows the chain: the forests
(own trees, TWO stored tables), the decision with the record. o.rho0 as the format's first value
(readX_head has it).

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Run.ChainFRead
import OnBytes.TypedOracleCompiler.Run.PlanQX

set_option autoImplicit false

namespace TypedOracleCompiler.Run.PQ
open Rom TypedOracleCompiler.Iop _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Run.Twin
    TypedOracleCompiler.Run.Thin
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ TypedOracleCompiler.Run
open _root_.Run.Twin (allLo)
open _root_.Fmt (RoundOut ChainOut Item ItemValue)

section
variable {I X : Type} (Lf : Unit → BatchProtocolWithLeafBody I X) (C : CK) (K : ℕ) (g : Fam (typedOracleFamily 256 (K + 1) (Lf ())))
    (early : X → X)
  (late : Option ℕ) (t : Tag) (cms : List (Dig 256)) (x : Option X) (salt : Bits) (rtreq : Dig 256)
  (O : ByteArray → ByteArray) (hO : ∀ s, (O s).size = 32) (P : _root_.Fmt.Plan)
  (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (hkit : KitFits P.field C K chal) (ds : List RD)
  (embP : PlainPart (up (SOf C ds)) (allLo (SOf C ds)) → PlainPart (Compile.Batch.shapeOf (Lf ()) t)
      (annOf (Lf ()) t))

include hO hkit in
/-- ONE CHAIN, FROM THE FIRST PHASE TO ITS END. -/
theorem chain_one (rs : List _root_.Fmt.Round) (ros : List RoundOut) (c : _root_.Fmt.Chain)
    (roots : Array ByteArray)
    (rest : List (Dig 256)) (pls : Plains (uL C ds))
        (F : StretchFacts O P C K ds rs ros c roots pls)
    (hrow : RowEnd Lf C K g t O c.label ds (fun z => embP (Sum.inr z)) 1 (c.round + 1))
        (hz : c.rho.size = 32)
    (hs0 : (g (OracleName.fb t) (⟨0, .f1 cms (x.map early) salt, [], embP (Sum.inl (Sum.inr ()))⟩ :
                FbIn 256 (Lf ()) t) :
      (Fin (K + 1) → Dig 256) × Dig 256).2 = bytesToDig c.rho)
    (hl : ∀ k, k < ds.length → late ≠ some (1 + k)) :
    ∃ (ρ : Rho (up (SOf C ds))) (v' : Bits),
      chainP Lf g early late t cms x salt rtreq (SOf C ds) (allLo (SOf C ds))
          (wire0S C K chal, wiresSL C K chal ds)
          embP 0 .first (rootsD ros ++ rest) ((), pls) =
        some (ρ, ((none, some []), rtSL C ds ros), .loc v') ∧
      drawnSL C ds ρ.2 = ros.map (·.drawn) ∧
      passSL C ds ρ.2 = passL (_root_.Fmt.HO O) rs ros c := by
  obtain ⟨ρ, v', e, d, p, -, -⟩ := chain_end_lo Lf C K g early late t cms x salt rtreq O hO P chal
      hkit ds rs ros 1 c roots
    (List.ofFn (bytesToDig c.rho)) rest none (fun z => embP (Sum.inr z)) pls F hrow
        (TieTree.dig_bytes _ hz)
    List.length_ofFn hl
  have st := chainP_firstT Lf g early late t cms x salt rtreq (s0 C) (SL C ds) (allLo (SL C ds))
      (wire0S C K chal)
    (wiresSL C K chal ds) embP 0 (rootsD ros ++ rest) (rootsD ros ++ rest) [] () pls
        (takeRt_zero _) _ hs0
  exact ⟨(_, ρ), v', st.trans (congrArg (Option.map _) e), d, p⟩

end

section
variable {I X : Type} (Lf : Unit → BatchProtocolWithLeafBody I X) (C : CK) (K : ℕ) (g : Fam (typedOracleFamily 256 (K + 1) (Lf ())))
    (early : X → X)
  (late : Option ℕ) (t : Tag) (cms : List (Dig 256)) (x : Option X) (salt : Bits)
  (O : ByteArray → ByteArray) (ds : List RD)
  (embP : PlainPart (up (SOf C ds)) (allLo (SOf C ds)) → PlainPart (Compile.Batch.shapeOf (Lf ()) t)
      (annOf (Lf ()) t))

/-- What is asked, for one chain. -/
structure ReadE (pls : Plains (uL C ds)) (S : _root_.Fmt.SpecX) (o : ChainOut) : Prop where
  /-- the strict reader's yes -/
  read : ∃ seen b i j, _root_.Fmt.readChainX (m := Id) (_root_.Fmt.HO O) S seen b i = some (o, j)
  /-- the description -/
  fit : FitL ds S.base.rounds
  room : ∀ r ∈ S.base.rounds, _root_.Fmt.blocksFor (_root_.Fmt.wordsAtMost r.entry r.kind) ≤ K
  hasRound : S.base.rounds ≠ []
  /-- the typed plain parts are those of the rounds read -/
  plains : plainsSL C ds o.rounds.toList = some pls
  /-- the laws on g -/
  row : RowEnd Lf C K g t O S.base.label ds (fun z => embP (Sum.inr z)) 1 (0 + 1)
  first : (g (OracleName.fb t) (⟨0, .f1 cms (x.map early) salt, [], embP (Sum.inl (Sum.inr ()))⟩ :
              FbIn 256 (Lf ()) t) :
    (Fin (K + 1) → Dig 256) × Dig 256).2 = bytesToDig o.rho0
  noLate : ∀ k, k < ds.length → late ≠ some (1 + k)

variable (rtreq : Dig 256) (hO : ∀ s, (O s).size = 32) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)

include hO in
/-- ONE CHAIN FROM ONE YES OF THE STRICT READER. -/
theorem chain_one_read (pls : Plains (uL C ds)) (S : _root_.Fmt.SpecX) (o : ChainOut)
    (rest : List (Dig 256))
    (hkit : KitFits S.base.plan.field C K chal) (A :
        ReadE Lf C K g early late t cms x salt O ds embP pls S o) :
    ∃ (ρ : Rho (up (SOf C ds))) (v' : Bits),
      chainP Lf g early late t cms x salt rtreq (SOf C ds) (allLo (SOf C ds))
          (wire0S C K chal, wiresSL C K chal ds)
          embP 0 .first ((rootsB o).map bytesToDig ++ rest) ((), pls) =
        some (ρ, ((none, some []), rtSL C ds o.rounds.toList), .loc v') ∧
      drawnSL C ds ρ.2 = o.rounds.toList.map (·.drawn) ∧ passSL C ds ρ.2 = true := by
  obtain ⟨sn, b, i, j, e⟩ := A.read
  obtain ⟨ros, n, pl, rt', F, w, t', -, m, m'⟩ :=
    stretch_of_read O S sn b i o j e C K ds S.base.rounds [] (List.append_nil _).symm A.fit A.room
  have z : n = [] := by cases n with | nil => rfl | cons _ _ => exact t'.elim
  subst z
  rw [take_all _ _ (List.forall₂_nil_left_iff.1 m')] at m
  have hp : pl = pls := Option.some.inj ((F.plains.symm.trans (plainsSL_same C ds _ _ m)).trans
      A.plains)
  subst hp
  obtain ⟨ρ, v', E, d, p⟩ := chain_one Lf C K g early late t cms x salt rtreq O hO S.base.plan
      chal hkit ds embP
    S.base.rounds ros ⟨S.base.label, o.rho0, 0⟩ #[] rest pl F A.row
    (trace_rho32' (_root_.Fmt.HO O) S.base.plan _ ros _ _ A.hasRound F.trace) A.first A.noLate
  refine ⟨ρ, v', ?_, ?_, p.trans w⟩
  · show chainP Lf g early late t cms x salt rtreq (SOf C ds) (allLo (SOf C ds))
      (wire0S C K chal, wiresSL C K chal ds)
      embP 0 .first (rootsD o.rounds.toList ++ rest) ((), pl) = _
    rw [← rootsD_same _ _ m, ← rtSL_same C ds _ _ m]
    exact E
  · rw [← drawn_same _ _ m]
    exact d

end

/-- The port's seal of a chain as read is sealRead. -/
theorem seal_sealRead (r : OnBytes.ChainRead) (x : ByteArray) (h : r.seal = some x) :
    sealRead r.out = x := by
  obtain ⟨ro, hb, hd⟩ := OnBytes.Tie.seal_eq r x h
  unfold sealRead
  rw [Array.getLast?_toList, hb]
  show (ro.drawn.digest).getD ByteArray.empty = x
  rw [hd]
  rfl

end TypedOracleCompiler.Run.PQ
