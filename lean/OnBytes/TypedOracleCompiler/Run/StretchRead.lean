-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/StretchRead.lean: StretchFacts (Run/ChainFrom.lean: the reader's side of a stretch)
FROM THE STRICT READER's YES. A piece of "the tie at H_b" for a proof file (LinkF).
The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on
definitions of Compile/.
WHY (the typing is a twin of the port's own STRICT reader). ChainFrom | ChainF take of the reader
what chain_ind took of the LENIENT one (FitL, room, TraceL, the typed plain parts).
Tie/TraceStrict.lean (readX_trace, trace_append) gives, at every hash h and with nothing
asked of the description: the strict reader's yes ⇒ the rounds as read, less the stored tables'
openings and the vertices met, are a trace in the library's sense, and all work passes; and a trace
can be cut at any round.
Of readX_trace this file takes the first six clauses alone.
  chainAfter_eq      Tie/TraceStrict.lean's chainAfter is ChainFrom's endOf
  plainsSL_fit       of StretchFacts' four fields "plains" follows from "fit" and "trace" (the
                     library's ofGots_whole, round by round; PageIsTopProofs' plainsSL_some is the
                     case rdsFrom)
  passL_append       the reader's work tests over rs ++ rs' are those over rs and those over rs'
                     from the chain behind
  trace_rho32        a trace with a round begins at a chain value of 32 bytes (askOK's second
                     clause): chain_whole's z₁ z₂ z₃
  Same5, same5_strip_joined      two rounds as read agree in message, items, nonce, draw and list;
                                 so do "stripR p.1" (the trace's) and "roundWithStoredOpenings p" (the reader's own
                                 output), round by round
  plainsSL_same | rootsD_same | rtSL_same | rtShL_same | drawn_same what ChainF makes of a list of
  rounds hangs on these five fields alone: SO ITS STATEMENTS MAY BE READ AT THE READER's OWN
  o.rounds
  stretch_of_read    Fmt.readChainX (HO O) S seen b i = some (o, j), S.base.rounds = rs ++ rs', FitL
                     ds rs, room ⇒ ∃ ros ros' pl roots': StretchFacts O S.base.plan C K ds rs ros
                     ⟨S.base.label, o.rho0, 0⟩ #[] pl; the work of rs passes; ros' is a trace of rs'
                     from the chain behind (endOf), and its work passes;
                         ros | ros' agree (Same5) with the first |rs| rounds of o.rounds | with the
                         others. rs' := [] : a whole chain (the second); rs' := [the sealed round]:
                         chain 1 less its seal; for the shared chain take rs' := [] and SealLast
WHAT IS NOT SAID. "fit" and "room": the description's (that the port's three descriptions ARE flashProveDescription's
three lists: THE HEAVIEST PIECE, untouched). That the twin's reader rdAt q h is Fmt.readChainX at HO
O (ChecksWithHashAsArgument/ProofWith.lean's HashFns.at; q, h of O). The openings' facts of readX_trace (each walks
to its root from its own start; StoredFact) are not carried here: the forests' half wants them.
o.rho0 as the format's first value.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Run.SealDigest
import OnBytes.TypedOracleCompiler.Run.PageIsTopProofs
import OnBytes.Tie.TraceStrict

set_option autoImplicit false

namespace TypedOracleCompiler.Run.PQ
open Rom TypedOracleCompiler.Iop _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Run.Twin
    TypedOracleCompiler.Run.Thin
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ TypedOracleCompiler.Run
open _root_.Fmt (RoundOut ChainOut Item ItemValue)

theorem chainAfter_eq (h : HId) :
    ∀ (rs : List _root_.Fmt.Round) (ros : List RoundOut) (c : _root_.Fmt.Chain),
        OnBytes.Tie.chainAfter h rs ros c = endOf h rs ros c
  | r :: rs, ro :: ros, c => chainAfter_eq h rs ros (nextOf h c r ro)
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl

/-- the typed plain parts are there -/
theorem plainsSL_fit (h : HId) (C : CK) (P : _root_.Fmt.Plan) :
    ∀ (ds : List RD) (rs : List _root_.Fmt.Round) (ros : List RoundOut) (c : _root_.Fmt.Chain)
        (roots : Array ByteArray),
      FitL ds rs → TraceL h P rs ros c roots → ∃ pl, plainsSL C ds ros = some pl
  | [], [], [], _, _, _, _ => ⟨(), rfl⟩
  | [], [], _ :: _, _, _, _, t => t.elim
  | [], _ :: _, _, _, _, hf, _ => hf.elim
  | _ :: _, [], _, _, _, hf, _ => hf.elim
  | _ :: _, _ :: _, [], _, _, _, t => t.elim
  | d :: ds, r :: rs, ro :: ros, c, roots, hf, t => by
    obtain ⟨-, -, hit, -, -, -, hf'⟩ := hf
    obtain ⟨-, hv, -, -, -, t'⟩ := t
    obtain ⟨p, hp⟩ := ofGots_whole P.field d.items ro.msg ro.vals (by rw [hit]; exact hv)
    obtain ⟨pl, hpl⟩ := plainsSL_fit h C P ds rs ros _ _ hf' t'
    exact ⟨(GPlain.mk d.entry.work p ro.nonce, pl), by simp only [plainsSL, hp, hpl]⟩

theorem passL_nil_right (h : HId) : ∀ (rs : List _root_.Fmt.Round) (c : _root_.Fmt.Chain),
    passL h rs [] c = true
  | [], _ => rfl
  | _ :: _, _ => rfl

theorem passL_append (h : HId) :
    ∀ (rs rs' : List _root_.Fmt.Round) (ros : List RoundOut) (c : _root_.Fmt.Chain),
      passL h (rs ++ rs') ros c =
        (passL h rs (ros.take rs.length) c && passL h rs' (ros.drop rs.length)
            (endOf h rs (ros.take rs.length) c))
  | [], rs', ros, c => by
      show passL h rs' ros c = (passL h [] (ros.take 0) c && passL h rs' (ros.drop 0)
          (endOf h [] (ros.take 0) c))
      rw [List.take_zero, List.drop_zero]
      rfl
  | r :: rs, rs', [], c => by
      show true = (true && passL h rs' [] c)
      rw [passL_nil_right]
      rfl
  | r :: rs, rs', ro :: ros, c => by
      show (_root_.Fmt.passesA r.entry.work (rowBs h c r ro) && passL h (rs ++ rs') ros
          (nextOf h c r ro)) =
        ((_root_.Fmt.passesA r.entry.work (rowBs h c r ro) && passL h rs (ros.take rs.length)
            (nextOf h c r ro)) &&
          passL h rs' (ros.drop rs.length) (endOf h rs (ros.take rs.length) (nextOf h c r ro)))
      rw [passL_append h rs rs' ros, Bool.and_assoc]

theorem trace_rho32 (h : HId) (P : _root_.Fmt.Plan) (r : _root_.Fmt.Round)
    (rs : List _root_.Fmt.Round) (ros : List RoundOut)
    (c : _root_.Fmt.Chain) (roots : Array ByteArray) (t : TraceL h P (r :: rs) ros c roots) :
        c.rho.size = 32 := by
  cases ros with
  | nil => exact t.elim
  | cons ro ros =>
    have hask := t.1
    simp only [_root_.Fmt.askOK, Bool.and_eq_true, and_assoc, decide_eq_true_iff, Bool.or_eq_true,
      bne_iff_ne, beq_iff_eq] at hask
    exact hask.2.1

/-! ## What hangs on five fields alone -/

/-- two rounds as read agree but for their openings -/
def Same5 (a b : RoundOut) : Prop :=
  a.msg = b.msg ∧ a.vals = b.vals ∧ a.nonce = b.nonce ∧ a.drawn = b.drawn ∧ a.list = b.list

theorem same5_strip_joined :
    ∀ rc : List (RoundOut × List (_root_.Fmt.Shape × List ℕ × _root_.Fmt.OpenOut)),
      List.Forall₂ Same5 (rc.map fun p => stripR p.1) (rc.map OnBytes.Tie.roundWithStoredOpenings)
  | [] => .nil
  | _ :: rc => .cons ⟨rfl, rfl, rfl, rfl, rfl⟩ (same5_strip_joined rc)

theorem plainsSL_same (C : CK) :
    ∀ (ds : List RD) (l l' : List RoundOut), List.Forall₂ Same5 l l' →
        plainsSL C ds l = plainsSL C ds l'
  | [], _, _, .nil => rfl
  | [], _, _, .cons _ _ => rfl
  | _ :: _, _, _, .nil => rfl
  | d :: ds, a :: l, b :: l', .cons h t => by
      simp only [plainsSL]
      rw [h.2.1, h.2.2.1, plainsSL_same C ds l l' t]

theorem rootsD_same : ∀ (l l' : List RoundOut), List.Forall₂ Same5 l l' → rootsD l = rootsD l'
  | _, _, .nil => rfl
  | a :: l, b :: l', .cons h t => by
      have ih := rootsD_same l l' t
      unfold rootsD at ih ⊢
      rw [List.flatMap_cons, List.flatMap_cons, List.map_append, List.map_append, ih, h.2.1]

theorem rtSL_same (C : CK) :
    ∀ (ds : List RD) (l l' : List RoundOut), List.Forall₂ Same5 l l' → rtSL C ds l = rtSL C ds l'
  | [], _, _, _ => rfl
  | _ :: _, _, _, .nil => rfl
  | d :: ds, a :: l, b :: l', .cons h t => by
      show ((none, some ((_root_.Fmt.rootsOf a.vals).map bytesToDig)), rtSL C ds l) =
        ((none, some ((_root_.Fmt.rootsOf b.vals).map bytesToDig)), rtSL C ds l')
      rw [h.2.1, rtSL_same C ds l l' t]

theorem rtShL_same (C : CK) :
    ∀ (ds : List RD) (l l' : List RoundOut), List.Forall₂ Same5 l l' → rtShL C ds l = rtShL C ds l'
  | [], _, _, _ => rfl
  | _ :: _, _, _, .nil => rfl
  | d :: ds, a :: l, b :: l', .cons h t => by
      show ((some ((_root_.Fmt.rootsOf a.vals).map bytesToDig), none), rtShL C ds l) =
        ((some ((_root_.Fmt.rootsOf b.vals).map bytesToDig), none), rtShL C ds l')
      rw [h.2.1, rtShL_same C ds l l' t]

theorem drawn_same : ∀ (l l' : List RoundOut), List.Forall₂ Same5 l l' →
    l.map (·.drawn) = l'.map (·.drawn)
  | _, _, .nil => rfl
  | _ :: l, _ :: l', .cons h t => congrArg₂ List.cons h.2.2.2.1 (drawn_same l l' t)

/-! ## From the strict reader's yes -/

/-- A STRETCH's FACTS FROM THE STRICT READER's YES. -/
theorem stretch_of_read (O : ByteArray → ByteArray) (S : _root_.Fmt.SpecX) (seen : _root_.Fmt.Seen)
    (b : ByteArray) (i : ℕ)
    (o : ChainOut) (j : ℕ) (e : _root_.Fmt.readChainX (m := Id) (_root_.Fmt.HO O) S seen b
        i = some (o, j))
    (C : CK) (K : ℕ) (ds : List RD) (rs rs' : List _root_.Fmt.Round)
        (hS : S.base.rounds = rs ++ rs') (hfit : FitL ds rs)
    (hroom : ∀ r ∈ rs, _root_.Fmt.blocksFor (_root_.Fmt.wordsAtMost r.entry r.kind) ≤ K) :
    ∃ (ros ros' : List RoundOut) (pl : Plains (uL C ds)) (roots' : Array ByteArray),
      StretchFacts O S.base.plan C K ds rs ros ⟨S.base.label, o.rho0, 0⟩ #[] pl ∧
      passL (_root_.Fmt.HO O) rs ros ⟨S.base.label, o.rho0, 0⟩ = true ∧
      TraceL (_root_.Fmt.HO O) S.base.plan rs' ros'
          (endOf (_root_.Fmt.HO O) rs ros ⟨S.base.label, o.rho0, 0⟩) roots' ∧
      passL (_root_.Fmt.HO O) rs' ros' (endOf (_root_.Fmt.HO O) rs ros
          ⟨S.base.label, o.rho0, 0⟩) = true ∧
      List.Forall₂ Same5 ros (o.rounds.toList.take rs.length) ∧
      List.Forall₂ Same5 ros' (o.rounds.toList.drop rs.length) := by
  obtain ⟨-, -, rc, hrc, ht, hp, -⟩ := OnBytes.Tie.readX_trace (_root_.Fmt.HO O) S seen b i o j e
  rw [hS] at ht hp
  obtain ⟨t1, t2⟩ := OnBytes.Tie.trace_append (_root_.Fmt.HO O) S.base.plan rs rs' _ _ _ ht
  rw [chainAfter_eq] at t2
  rw [passL_append, Bool.and_eq_true] at hp
  obtain ⟨pl, hpl⟩ := plainsSL_fit (_root_.Fmt.HO O) C S.base.plan ds rs _ _ _ hfit t1
  have hs := same5_strip_joined rc
  rw [← hrc] at hs
  exact ⟨_, _, pl, _, ⟨hfit, hroom, t1, hpl⟩, hp.1, t2, hp.2, List.forall₂_take _ hs,
      List.forall₂_drop _ hs⟩

end TypedOracleCompiler.Run.PQ
