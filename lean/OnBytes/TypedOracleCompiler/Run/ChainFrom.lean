-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/ChainFrom.lean: THE CHAIN's HALF FOR A STRETCH OF WRITTEN ROUNDS BEFORE A SKELETON
TAIL: chain_ind (Run/PageIsChain.lean) FREED OF ITS FIVE FIXED THINGS. A piece of "the tie at H_b"
for a proof file (LinkF). The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is
made with; it builds on definitions of Compile/.
WHY. chain_ind says, for ONE chain from the first phase: the plain verifier's chain takes all roots
of each round's items in order, draws what the reader drew, and passes work if and only if the
reader's does. A proof file has THREE chains in ONE typed chain (front | first stretch | joining
round | SHARED stretch | seam | third stretch). chain_ind is fixed in five things; here each is a
letter:
  (1) THE INTERFACE AND THE FAMILY: any Lf, any family g of oracle functions, any tag t: WHAT IS
    ASKED OF g IS A HYPOTHESIS, THE "ROW LAW" (RowLo | RowSh | RowEnd): no family, no page is named;
    label and offset (typed round i against the format's index n) are letters;
  (2) THE SHAPE: SL C ds ++ T, T any skeleton tail: THE STATEMENT IS A CONTINUATION: chainP (SL C ds
    ++ T) … = (chainP T … (i + ds.length) (the next phase) (the rest of the roots) …).map (lay the
    stretch's part in front);
  (3) THE BRANCH: local rounds in the phase .loc OR .aft (phLo), head .f2 none ρ, the slot's
    component; SHARED rounds in the phase .shr, head .f5 ρ (no outer root), the shared component: a
    second step lemma and a second induction over ONE lemma on a round's blocks (row_step);
  (4) THE INSTANCE: any x, any early; late: any, if it names no round of the stretch;
  (5) THE ROOTS: "++ rest".
  Row O K label rho n msg kind work nonce ans      famOf_row's conclusion (PageIsChain.lean), in
                                                   letters: the typed answer ans, block by block, is
                                                   the digest of the row's block that the format's
                                                   chain step gives at (label, rho, index n, msg,
                                                   kind, work, nonce)
  row_step       ONE ROUND, ON ITS BLOCKS: from Row at the reader's data: the typed tail is the next
                 chain value; the kit's view of the wire's message is what the reader drew; the
                 typed work test is the reader's. chain_ind's text from "hu'" on, as a lemma of its
                 own
  phLo o v           the phase of a local round: .loc v (o = none) | .aft v c (o = some c)
  chainP_loG, chainP_shG   the chain's step at a local | a shared round, in these letters
  rhJ, rtJ, pbLo | pbSh, rtShL, endOf   the stretch's verifier messages | roots before the tail's; a
                                        tail's plain part in the whole; the roots of shared rounds;
                                        the reader's chain behind the stretch
  RowLo | RowSh | RowEnd    THE ROW LAW, round by round: at the typed query ⟨i, .f2 none ρ | .f5 ρ,
                            rt, embP (the round's plain part pl)⟩ g answers the row at (label, ρ's
                            bytes, n, the spelling of pl's items with rt's bytes, the round's kind,
                            work, pl's nonce): ASKED ONLY AT ρ OF 256 BITS, AS
                     MANY ROOTS AS THE ROUND HAS TREES, A NONCE BELOW 2 ^ 64 (a family behind a page
                     of partial codes has it nowhere else)
  StretchFacts       the reader's side, what chain_ind takes of the lenient reader: FitL,
                     room for the blocks, TraceL, the typed plain parts: in a structure of its own:
                     how they come from the strict reader's yes is not said in this file
  chain_from_lo, chain_from_sh    the two continuations; chain_end_lo a local stretch with no tail
                                  (SL C ds, allLo, wiresSL: the third stretch's own terms; SL C ds
                                  ++ [] is not SL C ds by unfolding)
  rowEnd_famOf, chain_ind_again   A GUARD AGAINST EMPTINESS: the one-chain tie's own family famOf O
                                  (PDS …) HAS the row law (by famOf_row), and chain_ind's statement
                                  follows from chain_end_lo_ind, to the letter BUT FOR ONE
                                  HYPOTHESIS MORE: v.length = 256 (the row law is asked at 256 bits
                                  alone)
EACH GIVES BESIDE THE EQUATION: drawnSL ρ = what the reader drew; passSL ρ = the reader's passL; THE
TYPED CHAIN VALUE BEHIND THE STRETCH IS THE READER's (bitsToBytes v' = (endOf …).rho; 256 bits):
chain_ind hid it behind ∃: a seam needs it.
WHAT IS NOT SAID. THE FOUR SEAMS (front; (G) with (F4); SEAL 2; (F3)): not here. IN THIS FILE the
guard shows an instance of RowEnd alone (local rounds, no tail, head .f2). [That RowAt holds in
these letters at the family of F's page is not shown in this library.] chain_from_sh (RowSh over a
WHOLE list) IS USED BY NOTHING: a proof file's shared
  stretch ends in a sealed round: Run/ChainF.lean's chain_from_shS_ind is the form that serves. That
  the strict reader's yes gives StretchFacts. AT A SEALED ROUND "what was drawn = what the reader
  drew" holds up to the digest alone: such a round is no round of a stretch here.
What follows the chain (forests, views). Values under oracle FUNCTIONS: chainP; its ties to recomputeChain's
run are Run/ThinTie*.lean | TwinTie | VerifyDetProofs.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Run.PageIsChain
import OnBytes.TypedOracleCompiler.Slice.Batch3SWire

set_option autoImplicit false

namespace TypedOracleCompiler.Run.PQ
open Rom TypedOracleCompiler.Iop _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Run.Twin
    TypedOracleCompiler.Run.Thin
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ TypedOracleCompiler.Run
open _root_.Run.Twin (allLo)
open _root_.Fmt (Chain RoundOut ChainOut Item ItemValue)
open TypedOracleCompiler.Slice (shA annLoS annShS wLoS wShS plF plS shdS wireSh)

/-! ## One round, on its blocks -/

/-- The row: the typed answer, block by block, is the digest of the format's block. -/
def Row (O : ByteArray → ByteArray) (K label : ℕ) (rho : ByteArray) (n : ℕ) (msg : ByteArray)
    (kind : _root_.Fmt.Kind)
    (work nonce : ℕ) (ans : (Fin K → Dig 256) × Dig 256) : Prop :=
  (∀ k : Fin K, ans.1 k =
    bytesToDig (_root_.Fmt.blockW (_root_.Fmt.HO O) label rho n msg kind work nonce
        (blockNo work K k.castSucc))) ∧
  ans.2 = bytesToDig (_root_.Fmt.blockW (_root_.Fmt.HO O) label rho n msg kind work nonce
      (_root_.Fmt.firstBlock work - 1))

section Step
variable (O : ByteArray → ByteArray) (hO : ∀ s, (O s).size = 32) (f : _root_.Fmt.Fld) (C : CK)
  (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (hkit : KitFits f C K chal)

include hO hkit in
/-- One round: the next chain value, the draw, the work test. -/
theorem row_step (d : RD) (r : _root_.Fmt.Round) (ro : RoundOut) (c : Chain)
    (he : d.entry = r.entry) (hk : d.kind = r.kind)
    (hroom : _root_.Fmt.blocksFor (_root_.Fmt.wordsAtMost r.entry r.kind) ≤ K)
        (hw64 : r.entry.work ≤ 64)
    (hdrawn : ro.drawn = _root_.Fmt.drawRound f r.entry r.kind
      (_root_.Fmt.rowOf (_root_.Fmt.msgA r.entry.work (rowBs (_root_.Fmt.HO O) c r ro))))
    (ans : (Fin (K + 1) → Dig 256) × Dig 256)
    (hrow : Row O (K + 1) c.label c.rho (c.round + 1) ro.msg r.kind r.entry.work ro.nonce ans) :
    bitsToBytes (List.ofFn ans.2) = (nextOf (_root_.Fmt.HO O) c r ro).rho ∧
    C.dr d.entry d.kind (GChal.old (b := d.entry.work)
        (chalGrind (chal d.entry d.kind) d.entry.work ans.1)) =
      ro.drawn ∧
    GChal.pass (b := d.entry.work) (chalGrind (chal d.entry d.kind) d.entry.work ans.1) =
      _root_.Fmt.passesA r.entry.work (rowBs (_root_.Fmt.HO O) c r ro) := by
  obtain ⟨hu, hnext⟩ := hrow
  have hwE : d.entry.work = r.entry.work := congrArg (·.work) he
  have hu' : ∀ k : Fin (K + 1), ans.1 k =
      bytesToDig (_root_.Fmt.blockW (_root_.Fmt.HO O) c.label c.rho (c.round + 1) ro.msg r.kind
        r.entry.work ro.nonce (blockNo d.entry.work (K + 1) k.castSucc)) :=
    fun k => (hu k).trans (by rw [hwE])
  have hbs : rowBs (_root_.Fmt.HO O) c r ro =
      _root_.Fmt.fetchW (m := Id) (_root_.Fmt.HO O) c.label c.rho (c.round + 1)
        ro.msg r.kind r.entry.work ro.nonce
        (_root_.Fmt.firstBlock r.entry.work +
          _root_.Fmt.blocksFor (_root_.Fmt.wordsAtMost r.entry r.kind)) := rfl
  have hsize : (rowBs (_root_.Fmt.HO O) c r ro).size =
      _root_.Fmt.firstBlock r.entry.work +
        _root_.Fmt.blocksFor (_root_.Fmt.wordsAtMost r.entry r.kind) := by
    rw [hbs, _root_.Fmt.size_fetchW]
  have hget : ∀ b, b < (rowBs (_root_.Fmt.HO O) c r ro).size →
      (rowBs (_root_.Fmt.HO O) c r ro).getD b ByteArray.empty =
        _root_.Fmt.blockW (_root_.Fmt.HO O) c.label c.rho (c.round + 1)
          ro.msg r.kind r.entry.work ro.nonce b := by
    intro b hb
    rw [hsize] at hb
    rw [hbs]
    exact _root_.Fmt.fetchW_getD _ _ _ _ _ _ _ _ _ b hb
  have hfb : 1 ≤ _root_.Fmt.firstBlock r.entry.work := by
    unfold _root_.Fmt.firstBlock; split <;> omega
  have hB32 : ∀ b,
      (_root_.Fmt.blockW (_root_.Fmt.HO O) c.label c.rho (c.round + 1)
          ro.msg r.kind r.entry.work ro.nonce b).size = 32 :=
    fun b => size_blockW_HO O hO _ _ _ _ _ _ _ _
  refine ⟨?_, ?_, ?_⟩
  · rw [hnext]
    show digToBytes (bytesToDig _) = _root_.Fmt.nextA r.entry.work (rowBs (_root_.Fmt.HO O) c r ro)
    rw [TieTree.dig_bytes _ (hB32 _)]
    unfold _root_.Fmt.nextA
    rw [hget _ (by rw [hsize]; omega)]
  · obtain ⟨mb, hmb, hmbB⟩ := old_grind (chal d.entry d.kind)
      (_root_.Fmt.blockW (_root_.Fmt.HO O) c.label c.rho (c.round + 1)
        ro.msg r.kind r.entry.work ro.nonce)
      d.entry.work _ hu'
    rw [hmb, hdrawn]
    rw [hwE] at hmbB
    have := drawn_eq _ hB32 r.entry.work _ (rowBs (_root_.Fmt.HO O) c r ro)
      hsize hget f C K chal hkit d.entry d.kind (by rw [he, hk]) hroom mb hmbB
    rw [this, he, hk]
  · rw [pass_grind (chal d.entry d.kind)
        (_root_.Fmt.blockW (_root_.Fmt.HO O) c.label c.rho (c.round + 1)
          ro.msg r.kind r.entry.work ro.nonce)
        (rowBs (_root_.Fmt.HO O) c r ro) d.entry.work _ (by rw [hwE]; exact hw64)
        hu' (hget 0 (by rw [hsize]; omega)), hwE]

end Step

/-! ## The chain's step, in letters -/

/-- the phase of a local round: before the shared rounds, or behind them with the slot value c -/
def phLo {lam : ℕ} (o : Option (Dig lam)) (v : Bits) : Phase lam :=
  match o with
  | none => .loc v
  | some c => .aft v c

/-- the roots of a component, off a list that goes on -/
theorem takeRt_app {lam : ℕ} (n : ℕ) (A B : List (Dig lam)) (h : n = A.length)
    (h1 : A.length ≤ TypedOracleCompiler.Iop.maxRt) :
    takeRt n (A ++ B) = some (A, B) := by
  subst h
  unfold takeRt
  rw [if_pos ⟨h1, by rw [List.length_append]; omega⟩, List.take_left' rfl, List.drop_left' rfl]

section Steps
variable {I X : Type} {lam K : ℕ} (Lf : Unit → BatchProtocolWithLeafBody I X) (g : Fam (typedOracleFamily lam K (Lf ())))
    (early : X → X)
  (late : Option ℕ) (t : Tag) (cms : List (Dig lam)) (x : Option X) (salt : Bits) (rtreq : Dig lam)

/-- a local round behind the first -/
theorem chainP_loG (r : RS) (Ss : List RS) (A : RoundSplits (up Ss)) (w : WireRB lam K r.up r.lo)
    (W : RoundsQueryLayout lam K (up Ss) A)
    (embP : PlainPart (up (r :: Ss)) (r.lo, A) → PlainPart (Compile.Batch.shapeOf (Lf ()) t) (annOf (Lf ()) t))
    (i : ℕ) (o : Option (Dig lam)) (hl : late ≠ some i) (v : Bits) (rts rts' : List (Dig lam))
        (rt : List (Dig lam))
    (pl : r.Plain) (pls : Plains (up Ss)) (ht : takeRt w.depthJ.length rts = some (rt, rts')) :
    chainP Lf g early late t cms x salt rtreq (r :: Ss) (r.lo, A) (w, W) embP i (phLo o v)
        rts (pl, pls) =
      (chainP Lf g early late t cms x salt rtreq Ss A W (fun z => embP (.inr z)) (i + 1)
        (phLo o (List.ofFn
            (g (OracleName.fb t)
              (⟨i, .f2 none v, rt, embP (.inl (.inr pl))⟩ : FbIn lam (Lf ()) t) :
                  (Fin K → Dig lam) × Dig lam).2))
        rts' pls).map fun z =>
          ((w.chal (g (OracleName.fb t)
                  (⟨i, .f2 none v, rt, embP (.inl (.inr pl))⟩ : FbIn lam (Lf ()) t) :
                      (Fin K → Dig lam) × Dig lam).1,
              z.1),
            ((none, some rt), z.2.1),
            z.2.2) := by
  cases o with
  | none =>
    show (match takeRt w.depthJ.length rts with
      | some (rt, rts') => _
      | none => none) = _
    rw [ht]
    simp only [if_neg hl]
    rfl
  | some c =>
    show (match takeRt w.depthJ.length rts with
      | some (rt, rts') => _
      | none => none) = _
    rw [ht]
    simp only [if_neg hl]
    rfl

/-- a shared round behind the joining round: only the shared part is sent -/
theorem chainP_shG (r : RS) (Ss : List RS) (A : RoundSplits (up Ss)) (w : WireRB lam K r.up (shdS r))
    (W : RoundsQueryLayout lam K (up Ss) A)
    (embP : PlainPart (up (r :: Ss)) (shdS r, A) → PlainPart (Compile.Batch.shapeOf (Lf ()) t) (annOf (Lf ()) t))
    (i : ℕ) (c : Dig lam) (v : Bits) (rts rts' : List (Dig lam)) (rt : List (Dig lam))
    (pl : r.Plain) (pls : Plains (up Ss)) (ht : takeRt w.depth0.length rts = some (rt, rts')) :
    chainP Lf g early late t cms x salt rtreq (r :: Ss) (shdS r, A) (w, W) embP i (.shr v c)
        rts (pl, pls) =
      (chainP Lf g early late t cms x salt rtreq Ss A W (fun z => embP (.inr z)) (i + 1)
        (.shr (List.ofFn
            (g (OracleName.fb t)
              (⟨i, .f5 v, rt, embP (.inl (.inl pl))⟩ : FbIn lam (Lf ()) t) :
                  (Fin K → Dig lam) × Dig lam).2) c)
        rts' pls).map fun z =>
          ((w.chal (g (OracleName.fb t)
                  (⟨i, .f5 v, rt, embP (.inl (.inl pl))⟩ : FbIn lam (Lf ()) t) :
                      (Fin K → Dig lam) × Dig lam).1,
              z.1),
            ((some rt, none), z.2.1),
            z.2.2) := by
  show (match takeRt w.depth0.length rts with
    | some (rt, rts') => _
    | none => none) = _
  rw [ht]
  rfl

end Steps

/-! ## A stretch's part before a tail's -/

section Kit
variable (C : CK) (T : List RS)

/-- the stretch's verifier messages before the tail's -/
def rhJ : (ds : List RD) → Rho (uL C ds) → Rho (up T) → Rho (shA C T ds)
  | [], _, b => b
  | _ :: ds, (c, a), b => (c, rhJ ds a b)

/-- the stretch's roots before the tail's -/
def rtJ : (ds : List RD) → RootsOfChain 256 (uL C ds) → RootsOfChain 256 (up T) → RootsOfChain 256 (shA C T ds)
  | [], _, b => b
  | _ :: ds, (c, a), b => (c, rtJ ds a b)

theorem rhF_rhJ : ∀ (ds : List RD) (a : Rho (uL C ds)) (b : Rho (up T)),
    TypedOracleCompiler.Slice.rhF C T ds (rhJ C T ds a b) = a
  | [], _, _ => rfl
  | _ :: ds, (c, a), b => congrArg (Prod.mk c) (rhF_rhJ ds a b)

theorem rhS_rhJ : ∀ (ds : List RD) (a : Rho (uL C ds)) (b : Rho (up T)),
    TypedOracleCompiler.Slice.rhS C T ds (rhJ C T ds a b) = b
  | [], _, _ => rfl
  | _ :: ds, (_, a), b => rhS_rhJ ds a b

/-- a plain part of the tail as one of the whole, behind local | shared rounds -/
def pbLo (At : RoundSplits (up T)) : (ds : List RD) → PlainPart (up T) At → PlainPart (shA C T ds) (annLoS C T At ds)
  | [], z => z
  | _ :: ds, z => .inr (pbLo At ds z)
def pbSh (At : RoundSplits (up T)) : (ds : List RD) → PlainPart (up T) At → PlainPart (shA C T ds) (annShS C T At ds)
  | [], z => z
  | _ :: ds, z => .inr (pbSh At ds z)

/-- what the chain yields for the roots of SHARED rounds: rtSL with the two components swapped -/
def rtShL : (ds : List RD) → List RoundOut → RootsOfChain 256 (uL C ds)
  | [], _ => ()
  | _ :: ds, [] => ((some [], none), rtShL ds [])
  | _ :: ds, ro :: ros => ((some ((_root_.Fmt.rootsOf ro.vals).map bytesToDig), none), rtShL ds ros)

end Kit

/-- the reader's chain behind a stretch -/
def endOf (h : HId) : List _root_.Fmt.Round → List RoundOut → Chain → Chain
  | r :: rs, ro :: ros, c => endOf h rs ros (nextOf h c r ro)
  | _, _, c => c

/-! ## The row law, the reader's side -/

section Laws
variable {I X : Type} (Lf : Unit → BatchProtocolWithLeafBody I X) (C : CK) (K : ℕ)
    (g : Fam (typedOracleFamily 256 (K + 1) (Lf ()))) (t : Tag)
  (O : ByteArray → ByteArray) (label : ℕ)

/-- the row law at one round d: hd ρ is the query's head, e pl its plain part -/
def RowAt (hd : Bits → Head 256 X) (d : RD)
    (e : (roundS C d).Plain → PlainPart (Compile.Batch.shapeOf (Lf ()) t) (annOf (Lf ()) t))
        (i n : ℕ) : Prop :=
  ∀ (ρ : Bits) (rt : List (Dig 256)) (pl : (roundS C d).Plain), ρ.length = 256 →
      rt.length = d.trees.length →
    GPlain.nonce (b := d.entry.work) pl < 2 ^ 64 →
    Row O (K + 1) label (bitsToBytes ρ) n (bytesL (rt.map digToBytes) d.items
        (GPlain.old (b := d.entry.work) pl))
      d.kind d.entry.work (GPlain.nonce (b := d.entry.work) pl)
      (g (OracleName.fb t) (⟨i, hd ρ, rt, e pl⟩ : FbIn 256 (Lf ()) t) : (Fin (K + 1) → Dig 256) × Dig 256)

variable (T : List RS) (At : RoundSplits (up T))

/-- The row law of a local stretch before a tail: typed rounds i, i + 1, …; the format's indices n,
n + 1, … -/
def RowLo : (ds : List RD) →
    (PlainPart (shA C T ds) (annLoS C T At ds) → PlainPart (Compile.Batch.shapeOf (Lf ()) t) (annOf (Lf ()) t)) →
        ℕ → ℕ → Prop
  | [], _, _, _ => True
  | d :: ds, embP, i, n =>
    RowAt Lf C K g t O label (fun ρ => .f2 none ρ) d (fun pl => embP (.inl (.inr pl))) i n ∧
      RowLo ds (fun z => embP (.inr z)) (i + 1) (n + 1)

/-- The row law of a shared stretch before a tail. -/
def RowSh : (ds : List RD) →
    (PlainPart (shA C T ds) (annShS C T At ds) → PlainPart (Compile.Batch.shapeOf (Lf ()) t) (annOf (Lf ()) t)) →
        ℕ → ℕ → Prop
  | [], _, _, _ => True
  | d :: ds, embP, i, n =>
    RowAt Lf C K g t O label (fun ρ => .f5 ρ) d (fun pl => embP (.inl (.inl pl))) i n ∧
      RowSh ds (fun z => embP (.inr z)) (i + 1) (n + 1)

/-- The row law of a local stretch with no tail. -/
def RowEnd : (ds : List RD) →
    (PlainPart (uL C ds) (allLo (SL C ds)) → PlainPart (Compile.Batch.shapeOf (Lf ()) t) (annOf (Lf ()) t)) → ℕ →
        ℕ → Prop
  | [], _, _, _ => True
  | d :: ds, embP, i, n =>
    RowAt Lf C K g t O label (fun ρ => .f2 none ρ) d (fun pl => embP (.inl (.inr pl))) i n ∧
      RowEnd ds (fun z => embP (.inr z)) (i + 1) (n + 1)

end Laws

/-- The reader's side: what chain_ind takes of the lenient reader. -/
structure StretchFacts (O : ByteArray → ByteArray) (P : _root_.Fmt.Plan) (C : CK) (K : ℕ)
    (ds : List RD)
    (rs : List _root_.Fmt.Round) (ros : List RoundOut) (c : Chain) (roots : Array ByteArray)
        (pl : Plains (uL C ds)) :
    Prop where
  /-- the rounds' data are the description's -/
  fit : FitL ds rs
  /-- K blocks are enough for every round's verifier message -/
  room : ∀ r ∈ rs, _root_.Fmt.blocksFor (_root_.Fmt.wordsAtMost r.entry r.kind) ≤ K
  /-- what the rounds of the reader's output are, from the chain c on -/
  trace : TraceL (_root_.Fmt.HO O) P rs ros c roots
  /-- the typed plain parts are the items read -/
  plains : plainsSL C ds ros = some pl

/-! ## One round of a stretch: what the reader's side and the row law give -/

section Round
variable {I X : Type} (Lf : Unit → BatchProtocolWithLeafBody I X) (C : CK) (K : ℕ)
    (g : Fam (typedOracleFamily 256 (K + 1) (Lf ()))) (t : Tag)
  (O : ByteArray → ByteArray) (hO : ∀ s, (O s).size = 32) (P : _root_.Fmt.Plan)
  (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (hkit : KitFits P.field C K chal)

include hO hkit in
/-- the round's query, as the chain asks it, has the reader's row; so row_step's three; and the
roots are taken -/
theorem round_factsG (hd : Bits → Head 256 X) (d : RD) (r : _root_.Fmt.Round) (ro : RoundOut)
    (c : Chain) (v : Bits)
    (e : (roundS C d).Plain → PlainPart (Compile.Batch.shapeOf (Lf ()) t) (annOf (Lf ()) t)) (i : ℕ)
        (p0 : PlainOf d.items)
    (he : d.entry = r.entry) (hk : d.kind = r.kind) (hit : d.items = r.items)
        (htree : d.trees.length = r.entry.roots)
    (hcount : _root_.Fmt.countItem .root r.items = r.entry.roots)
    (hroom : _root_.Fmt.blocksFor (_root_.Fmt.wordsAtMost r.entry r.kind) ≤ K)
    (hrow : RowAt Lf C K g t O c.label hd d e i (c.round + 1)) (hv : bitsToBytes v = c.rho)
        (hv256 : v.length = 256)
    (hask : _root_.Fmt.askOK c.label c.rho (c.round + 1) ro.msg r.kind r.entry.work ro.nonce = true)
    (hwhole : _root_.Fmt.whole (_root_.Fmt.readItems P.field r.items) ro.msg = some ro.vals)
    (hdrawn : ro.drawn = _root_.Fmt.drawRound P.field r.entry r.kind
      (_root_.Fmt.rowOf (_root_.Fmt.msgA r.entry.work (rowBs (_root_.Fmt.HO O) c r ro))))
    (hp0 : PlainOf.ofGots d.items ro.vals = some p0) :
    let ans : (Fin (K + 1) → Dig 256) × Dig 256 :=
      g (OracleName.fb t) (⟨i, hd v, (_root_.Fmt.rootsOf ro.vals).map bytesToDig,
                e (GPlain.mk d.entry.work p0 ro.nonce)⟩ : FbIn 256 (Lf ()) t)
    (_root_.Fmt.rootsOf ro.vals).length = r.entry.roots ∧
    bitsToBytes (List.ofFn ans.2) = (nextOf (_root_.Fmt.HO O) c r ro).rho ∧
    C.dr d.entry d.kind (GChal.old (b := d.entry.work)
        (chalGrind (chal d.entry d.kind) d.entry.work ans.1)) =
      ro.drawn ∧
    GChal.pass (b := d.entry.work) (chalGrind (chal d.entry d.kind) d.entry.work ans.1) =
      _root_.Fmt.passesA r.entry.work (rowBs (_root_.Fmt.HO O) c r ro) := by
  intro ans
  simp only [_root_.Fmt.askOK, Bool.and_eq_true, and_assoc, decide_eq_true_iff, Bool.or_eq_true,
    bne_iff_ne, beq_iff_eq] at hask
  obtain ⟨-, -, -, -, hw64, hn64, hw0, -⟩ := hask
  have hwE : d.entry.work = r.entry.work := congrArg (·.work) he
  have hlen : (_root_.Fmt.rootsOf ro.vals).length = r.entry.roots := by
    rw [roots_ofGots d.items ro.vals p0 hp0, hit, hcount]
  have hsz := roots_size P.field r.items ro.msg ro.vals hwhole
  have hrt := map_dig_bytes (_root_.Fmt.rootsOf ro.vals) hsz
  have hN : GPlain.nonce (b := d.entry.work) (GPlain.mk d.entry.work p0 ro.nonce) = ro.nonce :=
    nonce_mk p0 ro.nonce d.entry.work (by rw [he]; exact hw0)
  have hM : bytesL (((_root_.Fmt.rootsOf ro.vals).map bytesToDig).map digToBytes) d.items
      (GPlain.old (b := d.entry.work) (GPlain.mk d.entry.work p0 ro.nonce)) = ro.msg := by
    rw [hrt, old_mk]
    exact (msg_bytes P.field d.items ro.msg ro.vals p0 (by rw [hit]; exact hwhole) hp0).1
  have hR := hrow v ((_root_.Fmt.rootsOf ro.vals).map bytesToDig)
      (GPlain.mk d.entry.work p0 ro.nonce) hv256
    (by rw [List.length_map, hlen, htree]) (by rw [hN]; exact hn64)
  rw [hM, hN, hv] at hR
  have hto : ∀ (k : _root_.Fmt.Kind) (w : ℕ), k = r.kind → w = r.entry.work →
      Row O (K + 1) c.label c.rho (c.round + 1) ro.msg k w ro.nonce ans →
      Row O (K + 1) c.label c.rho (c.round + 1) ro.msg r.kind r.entry.work ro.nonce ans := by
    rintro _ _ rfl rfl h
    exact h
  exact ⟨hlen, row_step O hO P.field C K chal hkit d r ro c he hk hroom hw64 hdrawn ans
      (hto _ _ hk hwE hR)⟩

end Round

/-! ## The continuations -/

theorem map_eta {α β γ : Type} (o : Option (α × β × γ)) :
    (o.map fun z => (z.1, z.2.1, z.2.2)) = o := by
  cases o <;> rfl

section Main
variable {I X : Type} (Lf : Unit → BatchProtocolWithLeafBody I X) (C : CK) (K : ℕ) (g : Fam (typedOracleFamily 256 (K + 1) (Lf ())))
    (early : X → X)
  (late : Option ℕ) (t : Tag) (cms : List (Dig 256)) (x : Option X) (salt : Bits) (rtreq : Dig 256)
  (O : ByteArray → ByteArray) (hO : ∀ s, (O s).size = 32) (P : _root_.Fmt.Plan)
  (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (hkit : KitFits P.field C K chal) (label : ℕ)
  (T : List RS) (At : RoundSplits (up T)) (Wt : RoundsQueryLayout 256 (K + 1) (up T) At)

include hO hkit in
theorem chain_from_lo_ind (o : Option (Dig 256)) (rest : List (Dig 256)) :
    ∀ (ds : List RD) (rs : List _root_.Fmt.Round) (ros : List RoundOut) (i : ℕ) (c : Chain)
        (roots : Array ByteArray) (v : Bits)
        (embP : PlainPart (shA C T ds) (annLoS C T At ds) →
            PlainPart (Compile.Batch.shapeOf (Lf ()) t) (annOf (Lf ()) t))
        (pls : Plains (shA C T ds)),
      FitL ds rs → (∀ r ∈ rs, _root_.Fmt.blocksFor (_root_.Fmt.wordsAtMost r.entry r.kind) ≤ K) →
      RowLo Lf C K g t O label T At ds embP i (c.round + 1) → c.label = label →
      bitsToBytes v = c.rho → v.length = 256 → (∀ k, k < ds.length → late ≠ some (i + k)) →
      TraceL (_root_.Fmt.HO O) P rs ros c roots → plainsSL C ds ros = some (plF C T ds pls) →
      ∃ (ρ : Rho (uL C ds)) (v' : Bits),
        chainP Lf g early late t cms x salt rtreq (SL C ds ++ T) (annLoS C T At ds)
            (wLoS C K chal T At Wt ds)
            embP i (phLo o v) ((ros.flatMap fun r => _root_.Fmt.rootsOf r.vals).map bytesToDig
                ++ rest) pls =
          (chainP Lf g early late t cms x salt rtreq T At Wt (fun z => embP (pbLo C T At ds z))
              (i + ds.length)
            (phLo o v') rest (plS C T ds pls)).map
            (fun z => (rhJ C T ds ρ z.1, rtJ C T ds (rtSL C ds ros) z.2.1, z.2.2)) ∧
        drawnSL C ds ρ = ros.map (·.drawn) ∧
        passSL C ds ρ = passL (_root_.Fmt.HO O) rs ros c ∧
        bitsToBytes v' = (endOf (_root_.Fmt.HO O) rs ros c).rho ∧ v'.length = 256
  | [], [], [], i, c, roots, v, embP, pls, _, _, _, _, hv, hv256, _, _, _ =>
      ⟨(), v, (map_eta _).symm, rfl, rfl, hv, hv256⟩
  | [], [], _ :: _, _, _, _, _, _, _, _, _, _, _, _, _, _, ht, _ => ht.elim
  | [], _ :: _, _, _, _, _, _, _, _, hf, _, _, _, _, _, _, _, _ => hf.elim
  | _ :: _, [], _, _, _, _, _, _, _, hf, _, _, _, _, _, _, _, _ => hf.elim
  | _ :: _, _ :: _, [], _, _, _, _, _, _, _, _, _, _, _, _, _, ht, _ => ht.elim
  | d :: ds, r :: rs, ro :: ros, i, c, roots, v, embP, (p, pls), hf, hroom, hrow, hlab, hv,
      hv256, hl, ht, hp =>
      by
      obtain ⟨he, hk, hit, htree, hcount, h1, hf'⟩ := hf
      obtain ⟨hask, hwhole, hdrawn, -, -, ht'⟩ := ht
      obtain ⟨hrow0, hrow'⟩ := hrow
      rcases hp0 : PlainOf.ofGots d.items ro.vals with _ | p0
      · simp [plainsSL, hp0] at hp
      rcases hp1 : plainsSL C ds ros with _ | pl1
      · simp [plainsSL, hp0, hp1] at hp
      simp only [plainsSL, hp0, hp1, Option.some.injEq] at hp
      have hpa : GPlain.mk d.entry.work p0 ro.nonce = p := congrArg Prod.fst hp
      have hpb : pl1 = plF C T ds pls := congrArg Prod.snd hp
      subst hpa
      obtain ⟨hlen, hnext, hdr0, hps0⟩ := round_factsG Lf C K g t O hO P chal hkit
          (fun ρ => .f2 none ρ) d r ro c v
        (fun pl => embP (.inl (.inr pl))) i p0 he hk hit htree hcount (hroom r List.mem_cons_self)
        (by rw [hlab]; exact hrow0) hv hv256 hask hwhole hdrawn hp0
      have htake := takeRt_app (wireS C K chal d).depthJ.length
          ((_root_.Fmt.rootsOf ro.vals).map bytesToDig)
        ((ros.flatMap fun r => _root_.Fmt.rootsOf r.vals).map bytesToDig ++ rest)
        (by rw [List.length_map, hlen]; exact (List.length_map _).trans htree)
        (by rw [List.length_map, hlen]; exact h1)
      obtain ⟨ρ', v'', hch, hdr, hps, hend, hlen'⟩ :=
        chain_from_lo_ind o rest ds rs ros (i + 1) (nextOf (_root_.Fmt.HO O) c r ro) _ _
          (fun z => embP (.inr z)) pls hf' (fun r' hr' => hroom r' (List.mem_cons_of_mem _ hr'))
              hrow' hlab hnext
          List.length_ofFn
          (fun k hk' => by
            have := hl (k + 1) (by rw [List.length_cons]; omega)
            rwa [show i + (k + 1) = i + 1 + k by omega] at this)
          ht' (hp1.trans (congrArg some hpb))
      refine ⟨((wireS C K chal d).chal
            (g (OracleName.fb t) (⟨i, .f2 none v, (_root_.Fmt.rootsOf ro.vals).map bytesToDig,
                      embP (.inl (.inr (GPlain.mk d.entry.work p0 ro.nonce)))⟩ : FbIn 256 (Lf ()) t) :
                (Fin (K + 1) → Dig 256) × Dig 256).1, ρ'), v'', ?_, ?_, ?_, hend, hlen'⟩
      · have hstep := chainP_loG Lf g early late t cms x salt rtreq (roundS C d) (SL C ds ++ T)
          (annLoS C T At ds) (wireS C K chal d) (wLoS C K chal T At Wt ds) embP i o
          (by simpa using hl 0 (by rw [List.length_cons]; omega)) v _ _ _
          (GPlain.mk d.entry.work p0 ro.nonce) pls htake
        rw [List.flatMap_cons, List.map_append, List.append_assoc]
        refine hstep.trans ((congrArg (Option.map _) hch).trans ?_)
        rw [Option.map_map, show i + (d :: ds).length = i + 1 + ds.length by rw [List.length_cons]; omega]
        rfl
      · exact congrArg₂ List.cons hdr0 hdr
      · exact congrArg₂ (· && ·) hps0 hps

include hO hkit in
theorem chain_from_sh_ind (cS : Dig 256) (rest : List (Dig 256)) :
    ∀ (ds : List RD) (rs : List _root_.Fmt.Round) (ros : List RoundOut) (i : ℕ) (c : Chain)
        (roots : Array ByteArray) (v : Bits)
        (embP : PlainPart (shA C T ds) (annShS C T At ds) →
            PlainPart (Compile.Batch.shapeOf (Lf ()) t) (annOf (Lf ()) t))
        (pls : Plains (shA C T ds)),
      FitL ds rs → (∀ r ∈ rs, _root_.Fmt.blocksFor (_root_.Fmt.wordsAtMost r.entry r.kind) ≤ K) →
      RowSh Lf C K g t O label T At ds embP i (c.round + 1) → c.label = label →
      bitsToBytes v = c.rho → v.length = 256 →
      TraceL (_root_.Fmt.HO O) P rs ros c roots → plainsSL C ds ros = some (plF C T ds pls) →
      ∃ (ρ : Rho (uL C ds)) (v' : Bits),
        chainP Lf g early late t cms x salt rtreq (SL C ds ++ T) (annShS C T At ds)
            (wShS C K chal T At Wt ds)
            embP i (.shr v cS) ((ros.flatMap fun r => _root_.Fmt.rootsOf r.vals).map bytesToDig
                ++ rest) pls =
          (chainP Lf g early late t cms x salt rtreq T At Wt (fun z => embP (pbSh C T At ds z))
              (i + ds.length)
            (.shr v' cS) rest (plS C T ds pls)).map
            (fun z => (rhJ C T ds ρ z.1, rtJ C T ds (rtShL C ds ros) z.2.1, z.2.2)) ∧
        drawnSL C ds ρ = ros.map (·.drawn) ∧
        passSL C ds ρ = passL (_root_.Fmt.HO O) rs ros c ∧
        bitsToBytes v' = (endOf (_root_.Fmt.HO O) rs ros c).rho ∧ v'.length = 256
  | [], [], [], i, c, roots, v, embP, pls, _, _, _, _, hv, hv256, _, _ =>
      ⟨(), v, (map_eta _).symm, rfl, rfl, hv, hv256⟩
  | [], [], _ :: _, _, _, _, _, _, _, _, _, _, _, _, _, ht, _ => ht.elim
  | [], _ :: _, _, _, _, _, _, _, _, hf, _, _, _, _, _, _, _ => hf.elim
  | _ :: _, [], _, _, _, _, _, _, _, hf, _, _, _, _, _, _, _ => hf.elim
  | _ :: _, _ :: _, [], _, _, _, _, _, _, _, _, _, _, _, _, ht, _ => ht.elim
  | d :: ds, r :: rs, ro :: ros, i, c, roots, v, embP, (p, pls), hf, hroom, hrow, hlab, hv,
      hv256, ht, hp =>
      by
      obtain ⟨he, hk, hit, htree, hcount, h1, hf'⟩ := hf
      obtain ⟨hask, hwhole, hdrawn, -, -, ht'⟩ := ht
      obtain ⟨hrow0, hrow'⟩ := hrow
      rcases hp0 : PlainOf.ofGots d.items ro.vals with _ | p0
      · simp [plainsSL, hp0] at hp
      rcases hp1 : plainsSL C ds ros with _ | pl1
      · simp [plainsSL, hp0, hp1] at hp
      simp only [plainsSL, hp0, hp1, Option.some.injEq] at hp
      have hpa : GPlain.mk d.entry.work p0 ro.nonce = p := congrArg Prod.fst hp
      have hpb : pl1 = plF C T ds pls := congrArg Prod.snd hp
      subst hpa
      obtain ⟨hlen, hnext, hdr0, hps0⟩ := round_factsG Lf C K g t O hO P chal hkit
          (fun ρ => .f5 ρ) d r ro c v
        (fun pl => embP (.inl (.inl pl))) i p0 he hk hit htree hcount (hroom r List.mem_cons_self)
        (by rw [hlab]; exact hrow0) hv hv256 hask hwhole hdrawn hp0
      have htake := takeRt_app (wireSh C K chal d).depth0.length
          ((_root_.Fmt.rootsOf ro.vals).map bytesToDig)
        ((ros.flatMap fun r => _root_.Fmt.rootsOf r.vals).map bytesToDig ++ rest)
        (by rw [List.length_map, hlen]; exact (List.length_map _).trans htree)
        (by rw [List.length_map, hlen]; exact h1)
      obtain ⟨ρ', v'', hch, hdr, hps, hend, hlen'⟩ :=
        chain_from_sh_ind cS rest ds rs ros (i + 1) (nextOf (_root_.Fmt.HO O) c r ro) _ _
          (fun z => embP (.inr z)) pls hf' (fun r' hr' => hroom r' (List.mem_cons_of_mem _ hr'))
              hrow' hlab hnext
          List.length_ofFn ht' (hp1.trans (congrArg some hpb))
      refine ⟨((wireS C K chal d).chal
            (g (OracleName.fb t) (⟨i, .f5 v, (_root_.Fmt.rootsOf ro.vals).map bytesToDig,
                      embP (.inl (.inl (GPlain.mk d.entry.work p0 ro.nonce)))⟩ : FbIn 256 (Lf ()) t) :
                (Fin (K + 1) → Dig 256) × Dig 256).1, ρ'), v'', ?_, ?_, ?_, hend, hlen'⟩
      · have hstep := chainP_shG Lf g early late t cms x salt rtreq (roundS C d) (SL C ds ++ T)
          (annShS C T At ds) (wireSh C K chal d) (wShS C K chal T At Wt ds) embP i cS v _ _ _
          (GPlain.mk d.entry.work p0 ro.nonce) pls htake
        rw [List.flatMap_cons, List.map_append, List.append_assoc]
        refine hstep.trans ((congrArg (Option.map _) hch).trans ?_)
        rw [Option.map_map, show i + (d :: ds).length = i + 1 + ds.length by rw [List.length_cons]; omega]
        rfl
      · exact congrArg₂ List.cons hdr0 hdr
      · exact congrArg₂ (· && ·) hps0 hps

include hO hkit in
theorem chain_end_lo_ind (o : Option (Dig 256)) (rest : List (Dig 256)) :
    ∀ (ds : List RD) (rs : List _root_.Fmt.Round) (ros : List RoundOut) (i : ℕ) (c : Chain)
        (roots : Array ByteArray) (v : Bits)
        (embP : PlainPart (uL C ds) (allLo (SL C ds)) → PlainPart (Compile.Batch.shapeOf (Lf ()) t)
            (annOf (Lf ()) t))
        (pls : Plains (uL C ds)),
      FitL ds rs → (∀ r ∈ rs, _root_.Fmt.blocksFor (_root_.Fmt.wordsAtMost r.entry r.kind) ≤ K) →
      RowEnd Lf C K g t O label ds embP i (c.round + 1) → c.label = label →
      bitsToBytes v = c.rho → v.length = 256 → (∀ k, k < ds.length → late ≠ some (i + k)) →
      TraceL (_root_.Fmt.HO O) P rs ros c roots → plainsSL C ds ros = some pls →
      ∃ (ρ : Rho (uL C ds)) (v' : Bits),
        chainP Lf g early late t cms x salt rtreq (SL C ds) (allLo (SL C ds)) (wiresSL C K chal ds)
            embP i (phLo o v) ((ros.flatMap fun r => _root_.Fmt.rootsOf r.vals).map bytesToDig
                ++ rest) pls =
          some (ρ, rtSL C ds ros, phLo o v') ∧
        drawnSL C ds ρ = ros.map (·.drawn) ∧
        passSL C ds ρ = passL (_root_.Fmt.HO O) rs ros c ∧
        bitsToBytes v' = (endOf (_root_.Fmt.HO O) rs ros c).rho ∧ v'.length = 256
  | [], [], [], i, c, roots, v, embP, pls, _, _, _, _, hv, hv256, _, _, _ =>
      ⟨(), v, rfl, rfl, rfl, hv, hv256⟩
  | [], [], _ :: _, _, _, _, _, _, _, _, _, _, _, _, _, _, ht, _ => ht.elim
  | [], _ :: _, _, _, _, _, _, _, _, hf, _, _, _, _, _, _, _, _ => hf.elim
  | _ :: _, [], _, _, _, _, _, _, _, hf, _, _, _, _, _, _, _, _ => hf.elim
  | _ :: _, _ :: _, [], _, _, _, _, _, _, _, _, _, _, _, _, _, ht, _ => ht.elim
  | d :: ds, r :: rs, ro :: ros, i, c, roots, v, embP, (p, pls), hf, hroom, hrow, hlab, hv,
      hv256, hl, ht, hp =>
      by
      obtain ⟨he, hk, hit, htree, hcount, h1, hf'⟩ := hf
      obtain ⟨hask, hwhole, hdrawn, -, -, ht'⟩ := ht
      obtain ⟨hrow0, hrow'⟩ := hrow
      rcases hp0 : PlainOf.ofGots d.items ro.vals with _ | p0
      · simp [plainsSL, hp0] at hp
      rcases hp1 : plainsSL C ds ros with _ | pl1
      · simp [plainsSL, hp0, hp1] at hp
      simp only [plainsSL, hp0, hp1, Option.some.injEq] at hp
      have hpa : GPlain.mk d.entry.work p0 ro.nonce = p := congrArg Prod.fst hp
      have hpb : pl1 = pls := congrArg Prod.snd hp
      subst hpa
      obtain ⟨hlen, hnext, hdr0, hps0⟩ := round_factsG Lf C K g t O hO P chal hkit
          (fun ρ => .f2 none ρ) d r ro c v
        (fun pl => embP (.inl (.inr pl))) i p0 he hk hit htree hcount (hroom r List.mem_cons_self)
        (by rw [hlab]; exact hrow0) hv hv256 hask hwhole hdrawn hp0
      have htake := takeRt_app (wireS C K chal d).depthJ.length
          ((_root_.Fmt.rootsOf ro.vals).map bytesToDig)
        ((ros.flatMap fun r => _root_.Fmt.rootsOf r.vals).map bytesToDig ++ rest)
        (by rw [List.length_map, hlen]; exact (List.length_map _).trans htree)
        (by rw [List.length_map, hlen]; exact h1)
      obtain ⟨ρ', v'', hch, hdr, hps, hend, hlen'⟩ :=
        chain_end_lo_ind o rest ds rs ros (i + 1) (nextOf (_root_.Fmt.HO O) c r ro) _ _
          (fun z => embP (.inr z)) pls hf' (fun r' hr' => hroom r' (List.mem_cons_of_mem _ hr'))
              hrow' hlab hnext
          List.length_ofFn
          (fun k hk' => by
            have := hl (k + 1) (by rw [List.length_cons]; omega)
            rwa [show i + (k + 1) = i + 1 + k by omega] at this)
          ht' (hp1.trans (congrArg some hpb))
      refine ⟨((wireS C K chal d).chal
            (g (OracleName.fb t) (⟨i, .f2 none v, (_root_.Fmt.rootsOf ro.vals).map bytesToDig,
                      embP (.inl (.inr (GPlain.mk d.entry.work p0 ro.nonce)))⟩ : FbIn 256 (Lf ()) t) :
                (Fin (K + 1) → Dig 256) × Dig 256).1, ρ'), v'', ?_, ?_, ?_, hend, hlen'⟩
      · have hstep := chainP_loG Lf g early late t cms x salt rtreq (roundS C d) (SL C ds)
          (allLo (SL C ds)) (wireS C K chal d) (wiresSL C K chal ds) embP i o
          (by simpa using hl 0 (by rw [List.length_cons]; omega)) v _ _ _
          (GPlain.mk d.entry.work p0 ro.nonce) pls htake
        rw [List.flatMap_cons, List.map_append, List.append_assoc]
        exact hstep.trans (congrArg (Option.map _) hch)
      · exact congrArg₂ List.cons hdr0 hdr
      · exact congrArg₂ (· && ·) hps0 hps

/-! ### The same over StretchFacts -/

variable (ds : List RD) (rs : List _root_.Fmt.Round) (ros : List RoundOut) (i : ℕ) (c : Chain)
  (roots : Array ByteArray) (v : Bits) (rest : List (Dig 256))

include hO hkit in
/-- A LOCAL STRETCH BEFORE A TAIL. -/
theorem chain_from_lo (o : Option (Dig 256))
    (embP : PlainPart (shA C T ds) (annLoS C T At ds) → PlainPart (Compile.Batch.shapeOf (Lf ()) t)
        (annOf (Lf ()) t))
    (pls : Plains (shA C T ds)) (F : StretchFacts O P C K ds rs ros c roots (plF C T ds pls))
    (hrow : RowLo Lf C K g t O c.label T At ds embP i (c.round + 1))
    (hv : bitsToBytes v = c.rho) (hv256 : v.length = 256)
        (hl : ∀ k, k < ds.length → late ≠ some (i + k)) :
    ∃ (ρ : Rho (uL C ds)) (v' : Bits),
      chainP Lf g early late t cms x salt rtreq (SL C ds ++ T) (annLoS C T At ds)
          (wLoS C K chal T At Wt ds)
          embP i (phLo o v) ((ros.flatMap fun r => _root_.Fmt.rootsOf r.vals).map bytesToDig
              ++ rest) pls =
        (chainP Lf g early late t cms x salt rtreq T At Wt (fun z => embP (pbLo C T At ds z))
            (i + ds.length)
          (phLo o v') rest (plS C T ds pls)).map
          (fun z => (rhJ C T ds ρ z.1, rtJ C T ds (rtSL C ds ros) z.2.1, z.2.2)) ∧
      drawnSL C ds ρ = ros.map (·.drawn) ∧
      passSL C ds ρ = passL (_root_.Fmt.HO O) rs ros c ∧
      bitsToBytes v' = (endOf (_root_.Fmt.HO O) rs ros c).rho ∧ v'.length = 256 :=
  chain_from_lo_ind Lf C K g early late t cms x salt rtreq O hO P chal hkit c.label T At Wt o rest
      ds rs ros i c roots v
    embP pls F.fit F.room hrow rfl hv hv256 hl F.trace F.plains

include hO hkit in
/-- A SHARED STRETCH BEFORE A TAIL. -/
theorem chain_from_sh (cS : Dig 256)
    (embP : PlainPart (shA C T ds) (annShS C T At ds) → PlainPart (Compile.Batch.shapeOf (Lf ()) t)
        (annOf (Lf ()) t))
    (pls : Plains (shA C T ds)) (F : StretchFacts O P C K ds rs ros c roots (plF C T ds pls))
    (hrow : RowSh Lf C K g t O c.label T At ds embP i (c.round + 1))
    (hv : bitsToBytes v = c.rho) (hv256 : v.length = 256) :
    ∃ (ρ : Rho (uL C ds)) (v' : Bits),
      chainP Lf g early late t cms x salt rtreq (SL C ds ++ T) (annShS C T At ds)
          (wShS C K chal T At Wt ds)
          embP i (.shr v cS) ((ros.flatMap fun r => _root_.Fmt.rootsOf r.vals).map bytesToDig
              ++ rest) pls =
        (chainP Lf g early late t cms x salt rtreq T At Wt (fun z => embP (pbSh C T At ds z))
            (i + ds.length)
          (.shr v' cS) rest (plS C T ds pls)).map
          (fun z => (rhJ C T ds ρ z.1, rtJ C T ds (rtShL C ds ros) z.2.1, z.2.2)) ∧
      drawnSL C ds ρ = ros.map (·.drawn) ∧
      passSL C ds ρ = passL (_root_.Fmt.HO O) rs ros c ∧
      bitsToBytes v' = (endOf (_root_.Fmt.HO O) rs ros c).rho ∧ v'.length = 256 :=
  chain_from_sh_ind Lf C K g early late t cms x salt rtreq O hO P chal hkit c.label T At Wt cS rest
      ds rs ros i c roots v
    embP pls F.fit F.room hrow rfl hv hv256 F.trace F.plains

include hO hkit in
/-- A LOCAL STRETCH WITH NO TAIL. -/
theorem chain_end_lo (o : Option (Dig 256))
    (embP : PlainPart (uL C ds) (allLo (SL C ds)) → PlainPart (Compile.Batch.shapeOf (Lf ()) t) (annOf (Lf ()) t))
    (pls : Plains (uL C ds)) (F : StretchFacts O P C K ds rs ros c roots pls)
    (hrow : RowEnd Lf C K g t O c.label ds embP i (c.round + 1))
    (hv : bitsToBytes v = c.rho) (hv256 : v.length = 256)
        (hl : ∀ k, k < ds.length → late ≠ some (i + k)) :
    ∃ (ρ : Rho (uL C ds)) (v' : Bits),
      chainP Lf g early late t cms x salt rtreq (SL C ds) (allLo (SL C ds)) (wiresSL C K chal ds)
          embP i (phLo o v) ((ros.flatMap fun r => _root_.Fmt.rootsOf r.vals).map bytesToDig
              ++ rest) pls =
        some (ρ, rtSL C ds ros, phLo o v') ∧
      drawnSL C ds ρ = ros.map (·.drawn) ∧
      passSL C ds ρ = passL (_root_.Fmt.HO O) rs ros c ∧
      bitsToBytes v' = (endOf (_root_.Fmt.HO O) rs ros c).rho ∧ v'.length = 256 :=
  chain_end_lo_ind Lf C K g early late t cms x salt rtreq O hO P chal hkit c.label o rest ds rs
      ros i c roots v
    embP pls F.fit F.room hrow rfl hv hv256 hl F.trace F.plains

end Main

/-! ## A guard against emptiness: chain_ind's own family has the row law, and chain_ind follows -/

section Guard
variable (Bd : Type) (leaf : Bd → Option (Nat × Nat × ByteArray))
  (O : ByteArray → ByteArray) (hO : ∀ s, (O s).size = 32) (S : _root_.Fmt.Spec) (C : CK)
  (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (dec : View → Bool)
  (hkit : KitFits S.plan.field C K chal) (cms : List (Dig 256)) (salt : Bits) (rtreq : Dig 256)

include hO in
/-- THE ROW LAW IS MET: by the family famOf O (PDS …) of the one-chain tie, at "typed round = the
format's index" (famOf_row). -/
theorem rowEnd_famOf :
    ∀ (ds : List RD) (rs : List _root_.Fmt.Round) (i : ℕ)
        (embP : PlainPart (uL C ds) (allLo (SL C ds)) →
          PlainPart (Compile.Batch.shapeOf (LbS Bd C (rds S) dec) .onl)
              (annOf (LbS Bd C (rds S) dec) .onl)),
      FitL ds rs → (∀ k, S.rounds[i + k]? = rs[k]?) →
      (∀ n rt z, (PDS Bd S C dec leaf).msg n rt (embP z) = msgSL C rt ds (embPL C ds z)) →
      (∀ n z, (PDS Bd S C dec leaf).nonce n (embP z) = nonceSL C ds (embPL C ds z)) →
      RowEnd (fun _ => LbS Bd C (rds S) dec) C K (famOf O (PDS Bd S C dec leaf) (K + 1)) .onl O
          S.label ds embP
        (i + 1) (i + 1)
  | [], [], _, _, _, _, _, _ => trivial
  | [], _ :: _, _, _, hf, _, _, _ => hf.elim
  | _ :: _, [], _, _, hf, _, _, _ => hf.elim
  | d :: ds, r :: rs, i, embP, hf, hsuf, hmsg, hnon => by
      obtain ⟨he, hk, -, -, -, -, hf'⟩ := hf
      have hr0 : S.rounds[i]? = some r := by simpa using hsuf 0
      have hkind : r.kind.num = (PDS Bd S C dec leaf).kind (i + 1) := by
        show _ = if i + 1 = 0 then 7 else ((S.rounds[i + 1 - 1]?).map (·.kind.num)).getD 7
        rw [if_neg (Nat.succ_ne_zero i), Nat.add_sub_cancel, hr0]
        rfl
      have hwork : (PDS Bd S C dec leaf).work (i + 1) = r.entry.work := by
        show (if i + 1 = 0 then 0 else ((S.rounds[i + 1 - 1]?).map (·.entry.work)).getD 0) = _
        rw [if_neg (Nat.succ_ne_zero i), Nat.add_sub_cancel, hr0]
        rfl
      refine ⟨?_, rowEnd_famOf ds rs (i + 1) (fun z => embP (.inr z)) hf' (fun k => by
          have := hsuf (k + 1); rw [List.getElem?_cons_succ] at this; rw [← this]; congr 1; omega)
        (fun n rt z => hmsg n rt (.inr z)) (fun n z => hnon n (.inr z))⟩
      intro ρ rt pl _ _ _
      have hrow := famOf_row O hO (PDS Bd S C dec leaf) (K + 1) i ρ rt
          (embP (.inl (.inr pl))) r.kind hkind
      rw [hmsg, hnon, hwork] at hrow
      have hto : ∀ (k : _root_.Fmt.Kind) (w : ℕ) (m : ByteArray) (ν : ℕ)
          (a : (Fin (K + 1) → Dig 256) × Dig 256),
          r.kind = k → r.entry.work = w →
          Row O (K + 1) S.label (bitsToBytes ρ) (i + 1) m r.kind r.entry.work ν a →
          Row O (K + 1) S.label (bitsToBytes ρ) (i + 1) m k w ν a := by
        rintro _ _ _ _ _ rfl rfl h
        exact h
      exact hto _ _ _ _ _ hk.symm (congrArg (·.work) he).symm hrow

include hO hkit in
/-- chain_ind AGAIN, FROM chain_end_lo_ind AND rowEnd_famOf: its statement to the letter BUT FOR ONE
HYPOTHESIS MORE, hv256 : v.length = 256 (the row law is asked at 256 bits alone): so far the new
statement contains the old. -/
theorem chain_ind_again (ds : List RD) (rs : List _root_.Fmt.Round) (ros : List RoundOut)
    (i : ℕ) (c : Chain)
    (roots : Array ByteArray) (v : Bits)
    (embP : PlainPart (uL C ds) (allLo (SL C ds)) →
      PlainPart (Compile.Batch.shapeOf (LbS Bd C (rds S) dec) .onl) (annOf (LbS Bd C (rds S) dec) .onl))
    (pl : Plains (uL C ds)) (hf : FitL ds rs) (hsuf : ∀ k, S.rounds[i + k]? = rs[k]?)
    (hroom : ∀ r ∈ rs, _root_.Fmt.blocksFor (_root_.Fmt.wordsAtMost r.entry r.kind) ≤ K)
    (hmsg : ∀ n rt z, (PDS Bd S C dec leaf).msg n rt (embP z) = msgSL C rt ds (embPL C ds z))
    (hnon : ∀ n z, (PDS Bd S C dec leaf).nonce n (embP z) = nonceSL C ds (embPL C ds z))
    (hlab : c.label = S.label) (hrnd : c.round = i) (hv : bitsToBytes v = c.rho)
        (hv256 : v.length = 256)
    (ht : TraceL (_root_.Fmt.HO O) S.plan rs ros c roots) (hp : plainsSL C ds ros = some pl) :
    ∃ (ρ : Rho (uL C ds)) (v' : Bits),
      chainP (fun _ => LbS Bd C (rds S) dec) (famOf O (PDS Bd S C dec leaf) (K + 1))
          id none .onl cms
          (some () : Option Unit) salt rtreq (SL C ds) (allLo (SL C ds)) (wiresSL C K chal ds)
          embP (i + 1) (.loc v)
          ((ros.flatMap fun r => _root_.Fmt.rootsOf r.vals).map bytesToDig) pl =
        some (ρ, rtSL C ds ros, .loc v') ∧
      drawnSL C ds ρ = ros.map (·.drawn) ∧
      passSL C ds ρ = passL (_root_.Fmt.HO O) rs ros c := by
  obtain ⟨ρ, v', h1, h2, h3, -, -⟩ := chain_end_lo_ind (fun _ => LbS Bd C (rds S) dec) C K
    (famOf O (PDS Bd S C dec leaf) (K + 1)) id none .onl cms (some () : Option Unit) salt rtreq O hO
        S.plan chal hkit
    S.label none [] ds rs ros (i + 1) c roots v embP pl hf hroom
    (by rw [hrnd]; exact rowEnd_famOf Bd leaf O hO S C K dec ds rs i embP hf hsuf hmsg hnon) hlab hv hv256
    (fun _ _ h => by cases h) ht hp
  rw [List.append_nil] at h1
  exact ⟨ρ, v', h1, h2, h3⟩

end Guard

end TypedOracleCompiler.Run.PQ
