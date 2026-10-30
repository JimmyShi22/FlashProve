-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/ChainF.lean: THE WHOLE CHAIN OF THE TYPED VERIFIER AT THE BATCH's SKELETON (BatchPS
D dec).up | wqBS, FROM THE THREE CHAINS AS READ: THE THREE STRETCHES (Run/ChainFrom.lean) JOINED
OVER THE FOUR SEAMS. A piece of "the tie at H_b" for a proof file (LinkF). The compiler under
OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on definitions of
Compile/.
WHY. A proof file holds three hash chains; the typed
verifier has one chain over BD.S: front | ds₁ | THE JOINING ROUND | ds₂ (shared) | a seam | ds₃. ALL
FOUR SEAMS FIT THE SHAPE BD.S | annS | wiresS AS IT LIES (the steps and the three stretches compose
without a cast: that is said OF THE SHAPE, NOT OF THE TIE: every law on g and every fact of the
reader is a hypothesis here).
ros₁ | ros₂ | ros₃ ARE NOT THE READER's OWN o.rounds: TraceL holds of the STRIPPED rounds
(readX_trace: rc.map fun p => stripR p.1), not of o.rounds (= rc.map joined): Run/StretchRead.lean's
Same5 and its five lemmas carry what is said here to o.rounds; Run/ChainFRead.lean reads it there.
EACH SEAM HAS A LAW OF ITS OWN AS A HYPOTHESIS ON g (no family, no page is named):
  (s-front) s0   round 0: at ⟨0, .f1 cms (early x) salt, rtF, the front's plain part⟩ THE TYPED TAIL
                 IS c₁.rho: the first chain's first value. rtF: the front's own roots (as many as
                 D.F.depths; for a proof file [d]): chainP_first asks that there are none:
                 chainP_firstT is the new step
  (s-join)  sG   round J = 1 + |ds₁|: at ⟨J, ρ, [], the slot's plain part⟩, ρ the value behind ds₁,
                 g's ANSWER IS seal₁ (a letter; GAt | GAt.sG: THE ROW's BLOCK 1 of a sealed round
                 without message, work or nonce at start ρ: SEAL 1: so ds₁ IS CHAIN 1 LESS ITS
                 SEAL);
            s4   then at ⟨J, .f4 cms rtreq, [], the shared plain part⟩ THE TYPED TAIL IS c₂.rho: the
                 shared chain's first value; the phase behind: .shr c₂.rho seal₁
  (s-seal2) RowShS   ds₂'s LAST ROUND IS A SEALED ROUND (SealLast): there the law (SealAt) asks of
                     the typed answer ITS TAIL ALONE: THE ROW's BLOCK 1 (sealOf), not block 0; of
                     the typed message blocks nothing. So the value that (F3) holds in ρ₀'s place is
                     SEAL 2's seal.
                     THERE "WHAT WAS DRAWN = WHAT THE READER DREW" HOLDS UP TO THE DIGEST:
                     SameButSeal: equal, but that the last two are Alike (elements, positions, trits
                     equal; the digest free): by drawRound_alike: at an entry that draws nothing
                     else the draw hangs on the row in its digest alone
  (s-f3)    s3 round J3 = J + 1 + |ds₂|: at ⟨J3, .f3 (bits seal₂) (bits seal₁), [], the seam's plain
            part⟩ THE TYPED TAIL IS c₃.rho: the second chain's first value
  Alike, SealRound, drawRound_alike, old_some, pass_zero, SameButSeal, SealLast, sealOf,
  plainsSL_cons_some tools for the sealed round
  chainP_shT | chainP_firstT | chainP_joinT | chainP_f3T the chain's steps, EACH WITH ITS TYPED TAIL
  (AND THE SLOT VALUE) AS A LETTER WITH ITS EQUATION: a seam's law enters as an argument, not by a
  rewrite (a rewrite does not find the term: the implicit types of Sum.inl differ by unfolding)
  SealAt, RowShS, chain_from_shS_ind     a shared stretch that ends in a sealed round, before a
                                         tail: chain_from_sh_ind with another last step: v' = bits
                                         (sealOf …)
  qJ | q3, eJ | e3, rtAll, rootsD            the plain parts and the embeddings from the joining
                                             round | from the seam on; the roots round by round; a
                                             chain's roots as digests
  chain_whole     [the name chainF IS TAKEN: TypedOracleCompiler.Run.chainF is a def of Run/VerifyDet.lean,
                  in a namespace that this one opens] EACH CHAIN UNDER ITS OWN PLAN P₁ | P₂ | P₃,
                  the kit fitting each field [the strict reader gives each chain
                 at its own S.base.plan, and the three are three records]: chainP … D.S D.annS
                 (D.wiresS K chal o) embP 0 .first (rtF ++ roots₁ ++ roots₂ ++ roots₃ ++ rest) pls =
                 some (ρ, rtAll …, .aft v' (seal₁ as a digest)) WITH: D.r₁ ρ | D.r₃ ρ draw what the
                 first | second chain's reader drew; D.r₂ ρ what the shared chain's drew, up to SEAL
                 2's digest; passSL at each = the reader's passL; the roots by round are rtAll
  chain_whole_slot    so the last phase's slotVal is some (seal₁ as a digest): that is the c which
                      reqPart takes
  GAt, sealG, GAt.sG     (G)'s law in letters (at every ρ of 256 bits g's answer is block 1 of that
                         row) gives chain_whole's sG at seal₁ := sealG O (the chain behind ds₁)
pls IS ANY STRING OF PLAIN PARTS: the stretches' parts are read off it by Batch3S's plF | plS:
BD.plJ3 has them by its plF_plJS | plS_plJS.
WHAT IS NOT SAID. THAT seal₁ | sealOf … ARE THE PORT's SEALS: the port's "closing"
(Run/ReqClimb.lean) is the DIGEST THAT THE READER's SEALED ROUND DRAWS; that this digest is the
row's block 1 (by text) IS NO LEMMA HERE. That ds₁ with a sealed round behind it is chain 1 (a trace
cut at a round:
trace_append, Tie/TraceStrict.lean). THAT ANY FAMILY HAS THESE LAWS (RowLo, RowShS, RowEnd, s0, sG,
s4, s3): no instance IN THIS FILE; that the family of F's page has all seven is not shown in this
library.
StretchFacts from the STRICT reader's yes. That c₁.rho | c₂.rho | c₃.rho are the format's first
values at (pd, statement, run) (they are letters here: the laws s0, s4, s3 carry that). A TABLE WITH
A RECORD (a fourth chain between (G) and (F4)): not here. What follows the chain. chainP against
recomputeChain's run: the sibling's ties.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Run.ChainFrom

set_option autoImplicit false

namespace TypedOracleCompiler.Run.PQ
open Rom TypedOracleCompiler.Iop _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Run.Twin
    TypedOracleCompiler.Run.Thin
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ TypedOracleCompiler.Run
open _root_.Run.Twin (allLo)
open _root_.Fmt (Chain RoundOut ChainOut Item ItemValue)
open TypedOracleCompiler.Slice (shA annLoS annShS wLoS wShS plF plS shdS wireSh ofR BD)

/-! ## A sealed round: what is drawn, up to the digest -/

/-- two draws are equal but for the digest -/
def Alike (a b : _root_.Fmt.Drawn) : Prop := a.elems = b.elems ∧ a.poss = b.poss ∧ a.trits = b.trits

theorem Alike.rfl' (a : _root_.Fmt.Drawn) : Alike a a := ⟨rfl, rfl, rfl⟩

/-- a round that draws a digest and nothing else, without work: what the format's Entry.fits asks at
the kind "sealed", and no work -/
structure SealRound (d : RD) : Prop where
  kind : d.kind = .sealed
  poss : d.entry.poss = 0
  trits : d.entry.trits = 0
  drawE : d.entry.drawE = 0
  drawNZ : d.entry.drawNZ = 0
  work : d.entry.work = 0

/-- at such an entry the draw hangs on the row in its digest alone -/
theorem drawRound_alike (f : _root_.Fmt.Fld) (e : _root_.Fmt.Entry) (k : _root_.Fmt.Kind)
    (hk : k ≠ .seeds)
    (h1 : e.poss = 0) (h2 : e.trits = 0) (h3 : e.drawE = 0) (h4 : e.drawNZ = 0)
        (row row' : _root_.Fmt.Row) :
    Alike (_root_.Fmt.drawRound f e k row) (_root_.Fmt.drawRound f e k row') := by
  unfold Alike _root_.Fmt.drawRound _root_.Fmt.drawRoundD _root_.Fmt.drawElems
  rw [if_neg hk, h1, h2, h3, h4]
  exact ⟨rfl, rfl, rfl⟩

/-- the wire's message is the kit's at some blocks, whatever the blocks are -/
theorem old_some {Cc : Type} {K : ℕ} (ch : (Fin K → Dig 256) → Cc) :
    ∀ (w : ℕ) (u : Fin (K + 1) → Dig 256), ∃ mb : Fin K → Dig 256,
        GChal.old (chalGrind ch w u) = ch mb
  | 0, u => ⟨firstBlocks 256 (K + 1) K u, rfl⟩
  | _ + 1, u => ⟨fun i => u i.succ, rfl⟩

/-- without work the typed test passes -/
theorem pass_zero {Cc : Type} {K : ℕ} (ch : (Fin K → Dig 256) → Cc) :
    ∀ (w : ℕ) (u : Fin (K + 1) → Dig 256), w = 0 → GChal.pass (chalGrind ch w u) = true
  | 0, _, _ => by
      show decide (∀ i : Fin 0, _) = true
      simp
  | _ + 1, _, h => by cases h

/-- equal, but that the LAST two are equal up to the digest alone -/
def SameButSeal : List _root_.Fmt.Drawn → List _root_.Fmt.Drawn → Prop
  | [], [] => True
  | a :: as, b :: bs => (if bs.isEmpty then Alike a b else a = b) ∧ SameButSeal as bs
  | _, _ => False

/-- the last round of the list is a sealed round -/
def SealLast : List RD → Prop
  | [] => False
  | [d] => SealRound d
  | _ :: d :: ds => SealLast (d :: ds)

/-- the seal: block 1 of the last round's row -/
def sealOf (h : HId) : List _root_.Fmt.Round → List RoundOut → Chain → ByteArray
  | [r], [ro], c => _root_.Fmt.blockW h c.label c.rho (c.round + 1) ro.msg r.kind
      r.entry.work ro.nonce 1
  | r :: rs, ro :: ros, c => sealOf h rs ros (nextOf h c r ro)
  | _, _, _ => ByteArray.empty

/-- what a yes of the typing of a stretch's plain parts says at its first round -/
theorem plainsSL_cons_some (C : CK) {d : RD} {ds : List RD} {o : RoundOut} {os : List RoundOut}
    {z : Plains (uL C (d :: ds))} (h : plainsSL C (d :: ds) (o :: os) = some z) :
    ∃ p r, PlainOf.ofGots d.items o.vals = some p ∧ plainsSL C ds os = some r ∧
      z = (GPlain.mk d.entry.work p o.nonce, r) := by
  rcases hp0 : PlainOf.ofGots d.items o.vals with _ | p0
  · simp [plainsSL, hp0] at h
  rcases hp1 : plainsSL C ds os with _ | pl1
  · simp [plainsSL, hp0, hp1] at h
  simp only [plainsSL, hp0, hp1, Option.some.injEq] at h
  exact ⟨p0, pl1, rfl, rfl, h.symm⟩

/-! ## The chain's steps at the seams. Each takes the typed tail (and the slot value) AS A LETTER
with its equation: so a seam's law enters without a rewrite -/

theorem takeRt_zero {lam : ℕ} (rts : List (Dig lam)) : takeRt 0 rts = some ([], rts) := by
  unfold takeRt
  rw [if_pos ⟨Nat.zero_le _, Nat.zero_le _⟩]
  rfl

section Seams
variable {I X : Type} {lam K : ℕ} (Lf : Unit → BatchProtocolWithLeafBody I X) (g : Fam (typedOracleFamily lam K (Lf ())))
    (early : X → X)
  (late : Option ℕ) (t : Tag) (cms : List (Dig lam)) (x : Option X) (salt : Bits) (rtreq : Dig lam)

/-- a shared round, its typed tail a letter -/
theorem chainP_shT (r : RS) (Ss : List RS) (A : RoundSplits (up Ss)) (w : WireRB lam K r.up (shdS r))
    (W : RoundsQueryLayout lam K (up Ss) A)
    (embP : PlainPart (up (r :: Ss)) (shdS r, A) → PlainPart (Compile.Batch.shapeOf (Lf ()) t) (annOf (Lf ()) t))
    (i : ℕ) (c : Dig lam) (v : Bits) (rts rts' : List (Dig lam)) (rt : List (Dig lam))
    (pl : r.Plain) (pls : Plains (up Ss)) (ht : takeRt w.depth0.length rts = some (rt, rts'))
        (tl : Dig lam)
    (htl : (g (OracleName.fb t) (⟨i, .f5 v, rt, embP (.inl (.inl pl))⟩ : FbIn lam (Lf ()) t) :
      (Fin K → Dig lam) × Dig lam).2 = tl) :
    chainP Lf g early late t cms x salt rtreq (r :: Ss) (shdS r, A) (w, W) embP i (.shr v c)
        rts (pl, pls) =
      (chainP Lf g early late t cms x salt rtreq Ss A W (fun z => embP (.inr z)) (i + 1)
        (.shr (List.ofFn tl) c) rts' pls).map fun z =>
          ((w.chal (g (OracleName.fb t)
                  (⟨i, .f5 v, rt, embP (.inl (.inl pl))⟩ : FbIn lam (Lf ()) t) :
                      (Fin K → Dig lam) × Dig lam).1,
              z.1),
            ((some rt, none), z.2.1),
            z.2.2) := by
  subst htl
  exact chainP_shG Lf g early late t cms x salt rtreq r Ss A w W embP i c v rts rts' rt pl pls ht

/-- (s-front) the first round, WITH ROOTS (chainP_first asks that it has none) -/
theorem chainP_firstT (r : RS) (Ss : List RS) (A : RoundSplits (up Ss)) (w : WireRB lam K r.up r.lo)
    (W : RoundsQueryLayout lam K (up Ss) A)
    (embP : PlainPart (up (r :: Ss)) (r.lo, A) → PlainPart (Compile.Batch.shapeOf (Lf ()) t) (annOf (Lf ()) t))
    (i : ℕ) (rts rts' : List (Dig lam)) (rt : List (Dig lam))
    (pl : r.Plain) (pls : Plains (up Ss)) (ht : takeRt w.depthJ.length rts = some (rt, rts'))
        (tl : Dig lam)
    (htl : (g (OracleName.fb t) (⟨i, .f1 cms (x.map early) salt, rt, embP (.inl (.inr pl))⟩ :
                FbIn lam (Lf ()) t) :
      (Fin K → Dig lam) × Dig lam).2 = tl) :
    chainP Lf g early late t cms x salt rtreq (r :: Ss) (r.lo, A) (w, W) embP i .first
        rts (pl, pls) =
      (chainP Lf g early late t cms x salt rtreq Ss A W (fun z => embP (.inr z)) (i + 1)
        (.loc (List.ofFn tl)) rts' pls).map fun z =>
          ((w.chal (g (OracleName.fb t)
                  (⟨i, .f1 cms (x.map early) salt, rt, embP (.inl (.inr pl))⟩ :
                      FbIn lam (Lf ()) t) :
                    (Fin K → Dig lam) × Dig lam).1,
              z.1),
            ((none, some rt), z.2.1),
            z.2.2) := by
  subst htl
  show (match takeRt w.depthJ.length rts with
    | some (rt, rts') => _
    | none => none) = _
  rw [ht]
  rfl

/-- (s-join) the joining round, without trees: the query to g, whose answer is the slot value c;
then (F4) -/
theorem chainP_joinT (r : RS) (a : RAnn r.up) (ha : a.kind = Kind.sh) (Ss : List RS)
    (A : RoundSplits (up Ss))
    (w : WireRB lam K r.up a) (W : RoundsQueryLayout lam K (up Ss) A)
    (embP : PlainPart (up (r :: Ss)) (a, A) → PlainPart (Compile.Batch.shapeOf (Lf ()) t) (annOf (Lf ()) t))
    (i : ℕ) (v : Bits) (rts : List (Dig lam)) (pl : r.Plain) (pls : Plains (up Ss))
    (hj : w.depthJ = []) (h0 : w.depth0 = []) (c tl : Dig lam)
    (hc : (g (OracleName.g t) (⟨i, v, [], embP (.inl (.inr (a.plain pl).2))⟩ : JoiningRoundQuery lam (Lf ()) t) : Dig lam)
        = c)
    (htl : (g (OracleName.fb t) (⟨i, .f4 cms (List.ofFn rtreq), [], embP (.inl (.inl (a.plain pl).1))⟩ :
                FbIn lam (Lf ()) t) :
      (Fin K → Dig lam) × Dig lam).2 = tl) :
    chainP Lf g early late t cms x salt rtreq (r :: Ss) (a, A) (w, W) embP i (.loc v)
        rts (pl, pls) =
      (chainP Lf g early late t cms x salt rtreq Ss A W (fun z => embP (.inr z)) (i + 1)
        (.shr (List.ofFn tl) c) rts pls).map fun z =>
          ((w.chal (g (OracleName.fb t)
                  (⟨i, .f4 cms (List.ofFn rtreq), [], embP (.inl (.inl (a.plain pl).1))⟩ :
                      FbIn lam (Lf ()) t) :
                    (Fin K → Dig lam) × Dig lam).1,
              z.1),
            ((some [], some []), z.2.1),
            z.2.2) := by
  subst hc
  subst htl
  have e : actOf cms (x.map early) salt a.kind (.loc v) = some (.join v) := by rw [ha]; rfl
  simp only [Thin.chainP, e, hj, h0, List.length_nil, takeRt_zero]
  rfl

/-- (s-f3) the first local round behind the shared rounds -/
theorem chainP_f3T (r : RS) (Ss : List RS) (A : RoundSplits (up Ss)) (w : WireRB lam K r.up r.lo)
    (W : RoundsQueryLayout lam K (up Ss) A)
    (embP : PlainPart (up (r :: Ss)) (r.lo, A) → PlainPart (Compile.Batch.shapeOf (Lf ()) t) (annOf (Lf ()) t))
    (i : ℕ) (v : Bits) (c : Dig lam) (rts rts' : List (Dig lam)) (rt : List (Dig lam))
    (pl : r.Plain) (pls : Plains (up Ss)) (ht : takeRt w.depthJ.length rts = some (rt, rts'))
        (tl : Dig lam)
    (htl : (g (OracleName.fb t) (⟨i, .f3 v (List.ofFn c), rt, embP (.inl (.inr pl))⟩ : FbIn lam (Lf ()) t) :
      (Fin K → Dig lam) × Dig lam).2 = tl) :
    chainP Lf g early late t cms x salt rtreq (r :: Ss) (r.lo, A) (w, W) embP i (.shr v c)
        rts (pl, pls) =
      (chainP Lf g early late t cms x salt rtreq Ss A W (fun z => embP (.inr z)) (i + 1)
        (.aft (List.ofFn tl) c) rts' pls).map fun z =>
          ((w.chal (g (OracleName.fb t)
                  (⟨i, .f3 v (List.ofFn c), rt, embP (.inl (.inr pl))⟩ : FbIn lam (Lf ()) t) :
                    (Fin K → Dig lam) × Dig lam).1,
              z.1),
            ((none, some rt), z.2.1),
            z.2.2) := by
  subst htl
  show (match takeRt w.depthJ.length rts with
    | some (rt, rts') => _
    | none => none) = _
  rw [ht]
  rfl

end Seams

/-! ## A shared stretch whose last round is a sealed round -/

section LawS
variable {I X : Type} (Lf : Unit → BatchProtocolWithLeafBody I X) (C : CK) (K : ℕ)
    (g : Fam (typedOracleFamily 256 (K + 1) (Lf ()))) (t : Tag)
  (O : ByteArray → ByteArray) (label : ℕ)

/-- the row law at a sealed round that ends a shared stretch: THE TYPED TAIL IS THE ROW's BLOCK 1;
nothing is asked of the typed message blocks -/
def SealAt (d : RD) (e : (roundS C d).Plain → PlainPart (Compile.Batch.shapeOf (Lf ()) t)
    (annOf (Lf ()) t)) (i n : ℕ) : Prop :=
  ∀ (ρ : Bits) (rt : List (Dig 256)) (pl : (roundS C d).Plain), ρ.length = 256 →
      rt.length = d.trees.length →
    GPlain.nonce (b := d.entry.work) pl < 2 ^ 64 →
    (g (OracleName.fb t) (⟨i, .f5 ρ, rt, e pl⟩ : FbIn 256 (Lf ()) t) :
        (Fin (K + 1) → Dig 256) × Dig 256).2 =
      bytesToDig (_root_.Fmt.blockW (_root_.Fmt.HO O) label (bitsToBytes ρ) n
        (bytesL (rt.map digToBytes) d.items (GPlain.old (b := d.entry.work) pl)) d.kind d.entry.work
        (GPlain.nonce (b := d.entry.work) pl) 1)

variable (T : List RS) (At : RoundSplits (up T))

/-- The row law of a shared stretch that ends in a sealed round: RowAt at all rounds but the last,
SealAt at the last. -/
def RowShS : (ds : List RD) →
    (PlainPart (shA C T ds) (annShS C T At ds) → PlainPart (Compile.Batch.shapeOf (Lf ()) t) (annOf (Lf ()) t)) →
        ℕ → ℕ → Prop
  | [], _, _, _ => True
  | [d], embP, i, n => SealAt Lf C K g t O label d (fun pl => embP (.inl (.inl pl))) i n
  | d :: d' :: ds, embP, i, n =>
    RowAt Lf C K g t O label (fun ρ => .f5 ρ) d (fun pl => embP (.inl (.inl pl))) i n ∧
      RowShS (d' :: ds) (fun z => embP (.inr z)) (i + 1) (n + 1)

end LawS

section MainS
variable {I X : Type} (Lf : Unit → BatchProtocolWithLeafBody I X) (C : CK) (K : ℕ) (g : Fam (typedOracleFamily 256 (K + 1) (Lf ())))
    (early : X → X)
  (late : Option ℕ) (t : Tag) (cms : List (Dig 256)) (x : Option X) (salt : Bits) (rtreq : Dig 256)
  (O : ByteArray → ByteArray) (hO : ∀ s, (O s).size = 32) (P : _root_.Fmt.Plan)
  (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (hkit : KitFits P.field C K chal) (label : ℕ)
  (T : List RS) (At : RoundSplits (up T)) (Wt : RoundsQueryLayout 256 (K + 1) (up T) At)

include hO hkit in
/-- A SHARED STRETCH THAT ENDS IN A SEALED ROUND, BEFORE A TAIL: the typed chain value behind it is
THE SEAL. -/
theorem chain_from_shS_ind (cS : Dig 256) (rest : List (Dig 256)) :
    ∀ (ds : List RD) (rs : List _root_.Fmt.Round) (ros : List RoundOut) (i : ℕ) (c : Chain)
        (roots : Array ByteArray) (v : Bits)
        (embP : PlainPart (shA C T ds) (annShS C T At ds) →
            PlainPart (Compile.Batch.shapeOf (Lf ()) t) (annOf (Lf ()) t))
        (pls : Plains (shA C T ds)),
      SealLast ds → FitL ds rs → (∀ r ∈ rs, _root_.Fmt.blocksFor
          (_root_.Fmt.wordsAtMost r.entry r.kind) ≤ K) →
      RowShS Lf C K g t O label T At ds embP i (c.round + 1) → c.label = label →
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
        SameButSeal (drawnSL C ds ρ) (ros.map (·.drawn)) ∧
        passSL C ds ρ = passL (_root_.Fmt.HO O) rs ros c ∧
        v' = List.ofFn (bytesToDig (sealOf (_root_.Fmt.HO O) rs ros c))
  | [], _, _, _, _, _, _, _, _, hs, _, _, _, _, _, _, _, _ => hs.elim
  | [_], [], _, _, _, _, _, _, _, _, hf, _, _, _, _, _, _, _ => hf.elim
  | [_], _ :: _, [], _, _, _, _, _, _, _, _, _, _, _, _, _, ht, _ => ht.elim
  | _ :: _ :: _, [], _, _, _, _, _, _, _, _, hf, _, _, _, _, _, _, _ => hf.elim
  | _ :: _ :: _, [_], _, _, _, _, _, _, _, _, hf, _, _, _, _, _, _, _ => hf.2.2.2.2.2.2.elim
  | _ :: _ :: _, _ :: _ :: _, [], _, _, _, _, _, _, _, _, _, _, _, _, _, ht, _ => ht.elim
  | _ :: _ :: _, _ :: _ :: _, [_], _, _, _, _, _, _, _, _, _, _, _, _, _, ht, _ => ht.2.2.2.2.2.elim
  | [d], r :: rs, ro :: ros, i, c, roots, v, embP, (p, pls), hs, hf, hroom, hrow, hlab, hv,
      hv256, ht, hp =>
      by
      obtain ⟨he, hk, hit, htree, hcount, h1, hf'⟩ := hf
      obtain ⟨hask, hwhole, hdrawn, -, -, ht'⟩ := ht
      cases rs with
      | cons _ _ => exact hf'.elim
      | nil =>
      cases ros with
      | cons _ _ => exact ht'.elim
      | nil =>
      rcases hp0 : PlainOf.ofGots d.items ro.vals with _ | p0
      · simp [plainsSL, hp0] at hp
      simp only [plainsSL, hp0, Option.some.injEq] at hp
      have hpa : GPlain.mk d.entry.work p0 ro.nonce = p := congrArg Prod.fst hp
      subst hpa
      simp only [_root_.Fmt.askOK, Bool.and_eq_true, and_assoc, decide_eq_true_iff, Bool.or_eq_true,
        bne_iff_ne, beq_iff_eq] at hask
      obtain ⟨-, -, -, -, -, hn64, hw0, -⟩ := hask
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
      have hS := (hrow v ((_root_.Fmt.rootsOf ro.vals).map bytesToDig)
          (GPlain.mk d.entry.work p0 ro.nonce) hv256
        (by rw [List.length_map, hlen, htree]) (by rw [hN]; exact hn64)).trans
          (show _ = bytesToDig (_root_.Fmt.blockW (_root_.Fmt.HO O) c.label c.rho
              (c.round + 1) ro.msg r.kind
            r.entry.work ro.nonce 1) by rw [hM, hN, hv, hk, hwE, hlab])
      beta_reduce at hS
      have htake := takeRt_app (wireSh C K chal d).depth0.length
          ((_root_.Fmt.rootsOf ro.vals).map bytesToDig) rest
        (by rw [List.length_map, hlen]; exact (List.length_map _).trans htree)
        (by rw [List.length_map, hlen]; exact h1)
      refine ⟨((wireS C K chal d).chal
            (g (OracleName.fb t) (⟨i, .f5 v, (_root_.Fmt.rootsOf ro.vals).map bytesToDig,
                      embP (.inl (.inl (GPlain.mk d.entry.work p0 ro.nonce)))⟩ : FbIn 256 (Lf ()) t) :
                (Fin (K + 1) → Dig 256) × Dig 256).1, ()), _, ?_, ?_, ?_, rfl⟩
      · have hstep := chainP_shT Lf g early late t cms x salt rtreq (roundS C d) T At
          (wireSh C K chal d) Wt embP i cS v
          _ _ _ (GPlain.mk d.entry.work p0 ro.nonce) pls htake _ hS
        rw [List.flatMap_cons, List.flatMap_nil, List.append_nil]
        exact hstep
      · refine ⟨?_, trivial⟩
        show Alike (C.dr d.entry d.kind (GChal.old (b := d.entry.work)
            (chalGrind (chal d.entry d.kind) d.entry.work _)))
          ro.drawn
        obtain ⟨mb, hmb⟩ := old_some (chal d.entry d.kind) d.entry.work
          (g (OracleName.fb t) (⟨i, .f5 v, (_root_.Fmt.rootsOf ro.vals).map bytesToDig,
                      embP (.inl (.inl (GPlain.mk d.entry.work p0 ro.nonce)))⟩ : FbIn 256 (Lf ()) t) :
                (Fin (K + 1) → Dig 256) × Dig 256).1
        rw [hmb, hkit, hdrawn, ← he, ← hk]
        exact drawRound_alike P.field d.entry d.kind (by rw [hs.kind]; decide) hs.poss hs.trits hs.drawE hs.drawNZ _ _
      · show (GChal.pass (b := d.entry.work) (chalGrind (chal d.entry d.kind) d.entry.work _) &&
          true) =
          (_root_.Fmt.passesA r.entry.work (rowBs (_root_.Fmt.HO O) c r ro) && true)
        rw [pass_zero (chal d.entry d.kind) d.entry.work _ hs.work, ← hwE, hs.work]
        rfl
  | d :: d' :: ds, r :: r' :: rs, ro :: ro' :: ros, i, c, roots, v, embP, (p, pls), hs, hf, hroom,
      hrow, hlab, hv,
      hv256, ht, hp => by
      obtain ⟨he, hk, hit, htree, hcount, h1, hf'⟩ := hf
      obtain ⟨hask, hwhole, hdrawn, -, -, ht'⟩ := ht
      obtain ⟨hrow0, hrow'⟩ := hrow
      obtain ⟨p0, pl1, hp0, hp1, hp''⟩ := plainsSL_cons_some C hp
      have hpa : GPlain.mk d.entry.work p0 ro.nonce = p := (congrArg Prod.fst hp'').symm
      have hpb : pl1 = plF C T (d' :: ds) pls := (congrArg Prod.snd hp'').symm
      subst hpa
      obtain ⟨hlen, hnext, hdr0, hps0⟩ := round_factsG Lf C K g t O hO P chal hkit
          (fun ρ => .f5 ρ) d r ro c v
        (fun pl => embP (.inl (.inl pl))) i p0 he hk hit htree hcount (hroom r List.mem_cons_self)
        (by rw [hlab]; exact hrow0) hv hv256 hask hwhole hdrawn hp0
      have htake := takeRt_app (wireSh C K chal d).depth0.length
          ((_root_.Fmt.rootsOf ro.vals).map bytesToDig)
        (((ro' :: ros).flatMap fun r => _root_.Fmt.rootsOf r.vals).map bytesToDig ++ rest)
        (by rw [List.length_map, hlen]; exact (List.length_map _).trans htree)
        (by rw [List.length_map, hlen]; exact h1)
      obtain ⟨ρ', v'', hch, hdr, hps, hend⟩ :=
        chain_from_shS_ind cS rest (d' :: ds) (r' :: rs) (ro' :: ros) (i + 1)
            (nextOf (_root_.Fmt.HO O) c r ro) _ _
          (fun z => embP (.inr z)) pls hs hf' (fun r' hr' => hroom r' (List.mem_cons_of_mem _ hr'))
              hrow' hlab hnext
          List.length_ofFn ht' (hp1.trans (congrArg some hpb))
      refine ⟨((wireS C K chal d).chal
            (g (OracleName.fb t) (⟨i, .f5 v, (_root_.Fmt.rootsOf ro.vals).map bytesToDig,
                      embP (.inl (.inl (GPlain.mk d.entry.work p0 ro.nonce)))⟩ : FbIn 256 (Lf ()) t) :
                (Fin (K + 1) → Dig 256) × Dig 256).1, ρ'), v'', ?_, ?_, ?_, hend⟩
      · have hstep := chainP_shG Lf g early late t cms x salt rtreq (roundS C d)
          (SL C (d' :: ds) ++ T)
          (annShS C T At (d' :: ds)) (wireSh C K chal d) (wShS C K chal T At Wt (d' :: ds))
              embP i cS v _ _ _
          (GPlain.mk d.entry.work p0 ro.nonce) pls htake
        rw [List.flatMap_cons, List.map_append, List.append_assoc]
        refine hstep.trans ((congrArg (Option.map _) hch).trans ?_)
        rw [Option.map_map,
          show i + (d :: d' :: ds).length = i + 1 + (d' :: ds).length by simp only [List.length_cons]; omega]
        rfl
      · exact ⟨hdr0, hdr⟩
      · exact congrArg₂ (· && ·) hps0 hps

end MainS

/-! ## The whole chain of the typed verifier at the batch's skeleton -/

section Whole
variable {I X : Type} {Lf : Unit → BatchProtocolWithLeafBody I X} {t : Tag} (D : BD)

/-- the plain parts from the joining round on; from the seam behind the shared rounds on -/
def qJ (pls : Plains D.shS) : Plains (up D.SJ) := plS D.G.C D.SJ D.G.ds₁ pls.2
def q3 (pls : Plains D.shS) : Plains (up D.S₃) := plS D.G.C D.S₃ D.G.ds₂ (qJ D pls).2

variable (embP : PlainPart D.shS D.annS → PlainPart (Compile.Batch.shapeOf (Lf ()) t) (annOf (Lf ()) t))

/-- a plain part from the joining round on, in the whole; from the seam on -/
def eJ (z : PlainPart (up D.SJ) D.annSJ) : PlainPart (Compile.Batch.shapeOf (Lf ()) t) (annOf (Lf ()) t) :=
  embP (Sum.inr (pbLo D.G.C D.SJ D.annSJ D.G.ds₁ z))
def e3 (z : PlainPart (up D.S₃) D.annS₃) : PlainPart (Compile.Batch.shapeOf (Lf ()) t) (annOf (Lf ()) t) :=
  eJ D embP (Sum.inr (pbSh D.G.C D.S₃ D.annS₃ D.G.ds₂ z))

/-- what the chain yields for the roots, round by round -/
def rtAll (rtF : List (Dig 256)) (ros₁ ros₂ ros₃ : List RoundOut) : RootsOfChain 256 D.shS :=
  ((none, some rtF), rtJ D.G.C D.SJ D.G.ds₁ (rtSL D.G.C D.G.ds₁ ros₁)
    ((some [], some []), rtJ D.G.C D.S₃ D.G.ds₂ (rtShL D.G.C D.G.ds₂ ros₂)
      ((none, some []), rtSL D.G.C D.G.ds₃ ros₃)))

/-- a chain's roots as read, as digests -/
def rootsD (ros : List RoundOut) : List (Dig 256) :=
    (ros.flatMap fun r => _root_.Fmt.rootsOf r.vals).map bytesToDig

variable (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → D.G.C.Ch e k) (o : D.G.Ones)
  (g : Fam (typedOracleFamily 256 (K + 1) (Lf ()))) (early : X → X) (late : Option ℕ)
  (cms : List (Dig 256)) (x : Option X) (salt : Bits) (rtreq : Dig 256)
  (O : ByteArray → ByteArray) (hO : ∀ s, (O s).size = 32) (P₁ P₂ P₃ : _root_.Fmt.Plan)
  (hkit₁ : KitFits P₁.field D.G.C K chal) (hkit₂ : KitFits P₂.field D.G.C K chal)
      (hkit₃ : KitFits P₃.field D.G.C K chal)

include hO hkit₁ hkit₂ hkit₃ in
/-- THE WHOLE CHAIN, FROM THE THREE CHAINS AS READ. Each chain under its own plan. -/
theorem chain_whole (pls : Plains D.shS) (rtF rest : List (Dig 256))
    (hF : D.F.depths.length = rtF.length)
    (hF2 : rtF.length ≤ TypedOracleCompiler.Iop.maxRt)
    (rs₁ rs₂ rs₃ : List _root_.Fmt.Round) (ros₁ ros₂ ros₃ : List RoundOut) (c₁ c₂ c₃ : Chain)
    (ro₁ ro₂ ro₃ : Array ByteArray)
    (F₁ : StretchFacts O P₁ D.G.C K D.G.ds₁ rs₁ ros₁ c₁ ro₁ (plF D.G.C D.SJ D.G.ds₁ pls.2))
    (F₂ : StretchFacts O P₂ D.G.C K D.G.ds₂ rs₂ ros₂ c₂ ro₂ (plF D.G.C D.S₃ D.G.ds₂ (qJ D pls).2))
    (F₃ : StretchFacts O P₃ D.G.C K D.G.ds₃ rs₃ ros₃ c₃ ro₃ (q3 D pls).2)
    (hS : SealLast D.G.ds₂)
    (R₁ : RowLo Lf D.G.C K g t O c₁.label D.SJ D.annSJ D.G.ds₁ (fun z => embP (Sum.inr z)) 1
        (c₁.round + 1))
    (R₂ : RowShS Lf D.G.C K g t O c₂.label D.S₃ D.annS₃ D.G.ds₂ (fun z => eJ D embP (Sum.inr z))
      (1 + D.G.ds₁.length + 1) (c₂.round + 1))
    (R₃ : RowEnd Lf D.G.C K g t O c₃.label D.G.ds₃ (fun z => e3 D embP (Sum.inr z))
      (1 + D.G.ds₁.length + 1 + D.G.ds₂.length + 1) (c₃.round + 1))
    (z₁ : c₁.rho.size = 32) (z₂ : c₂.rho.size = 32) (z₃ : c₃.rho.size = 32) (seal₁ : ByteArray)
    (s0 : (g (OracleName.fb t) (⟨0, .f1 cms (x.map early) salt, rtF, embP (Sum.inl (Sum.inr pls.1))⟩ :
                FbIn 256 (Lf ()) t) :
      (Fin (K + 1) → Dig 256) × Dig 256).2 = bytesToDig c₁.rho)
    (sG : ∀ ρ : Bits, ρ.length = 256 → bitsToBytes ρ = (endOf (_root_.Fmt.HO O) rs₁ ros₁ c₁).rho →
      (g (OracleName.g t) (⟨1 + D.G.ds₁.length, ρ, [], eJ D embP
                  (Sum.inl (Sum.inr (D.aJ.plain (qJ D pls).1).2))⟩ :
                JoiningRoundQuery 256 (Lf ()) t) : Dig 256) = bytesToDig seal₁)
    (s4 : (g (OracleName.fb t) (⟨1 + D.G.ds₁.length, .f4 cms (List.ofFn rtreq), [],
                eJ D embP (Sum.inl (Sum.inl (D.aJ.plain (qJ D pls).1).1))⟩ : FbIn 256 (Lf ()) t) :
      (Fin (K + 1) → Dig 256) × Dig 256).2 = bytesToDig c₂.rho)
    (s3 : (g (OracleName.fb t) (⟨1 + D.G.ds₁.length + 1 + D.G.ds₂.length,
                .f3 (List.ofFn (bytesToDig (sealOf (_root_.Fmt.HO O) rs₂ ros₂ c₂)))
                    (List.ofFn (bytesToDig seal₁)), [],
                e3 D embP (Sum.inl (Sum.inr (q3 D pls).1))⟩ : FbIn 256 (Lf ()) t) :
      (Fin (K + 1) → Dig 256) × Dig 256).2 = bytesToDig c₃.rho)
    (hl₁ : ∀ k, k < D.G.ds₁.length → late ≠ some (1 + k))
    (hl₃ : ∀ k, k < D.G.ds₃.length → late ≠ some (1 + D.G.ds₁.length + 1 + D.G.ds₂.length + 1 + k))
        :
    ∃ (ρ : Rho D.shS) (v' : Bits),
      chainP Lf g early late t cms x salt rtreq D.S D.annS (D.wiresS K chal o) embP 0 .first
          (rtF ++ (rootsD ros₁ ++ (rootsD ros₂ ++ (rootsD ros₃ ++ rest)))) pls =
        some (ρ, rtAll D rtF ros₁ ros₂ ros₃, .aft v' (bytesToDig seal₁)) ∧
      drawnSL D.G.C D.G.ds₁ (D.r₁ ρ) = ros₁.map (·.drawn) ∧
      SameButSeal (drawnSL D.G.C D.G.ds₂ (D.r₂ ρ)) (ros₂.map (·.drawn)) ∧
      drawnSL D.G.C D.G.ds₃ (D.r₃ ρ) = ros₃.map (·.drawn) ∧
      passSL D.G.C D.G.ds₁ (D.r₁ ρ) = passL (_root_.Fmt.HO O) rs₁ ros₁ c₁ ∧
      passSL D.G.C D.G.ds₂ (D.r₂ ρ) = passL (_root_.Fmt.HO O) rs₂ ros₂ c₂ ∧
      passSL D.G.C D.G.ds₃ (D.r₃ ρ) = passL (_root_.Fmt.HO O) rs₃ ros₃ c₃ := by
  -- the first stretch
  obtain ⟨ρ₁, v₁, e1, d1, p1, hv1, hv1l⟩ := chain_from_lo Lf D.G.C K g early late t cms x salt rtreq
      O hO P₁ chal hkit₁
    D.SJ D.annSJ (D.wSJ K chal o) D.G.ds₁ rs₁ ros₁ 1 c₁ ro₁ (List.ofFn (bytesToDig c₁.rho))
    (rootsD ros₂ ++ (rootsD ros₃ ++ rest)) none (fun z => embP (Sum.inr z)) pls.2 F₁ R₁
    (TieTree.dig_bytes _ z₁) List.length_ofFn hl₁
  -- the shared stretch
  obtain ⟨ρ₂, v₂, e2, d2, p2, hv2⟩ := chain_from_shS_ind Lf D.G.C K g early late t cms x salt rtreq
      O hO P₂ chal hkit₂
    c₂.label D.S₃ D.annS₃ (D.wS₃ K chal o) (bytesToDig seal₁) (rootsD ros₃ ++ rest) D.G.ds₂ rs₂ ros₂
    (1 + D.G.ds₁.length + 1) c₂ ro₂ (List.ofFn (bytesToDig c₂.rho))
        (fun z => eJ D embP (Sum.inr z)) (qJ D pls).2
    hS F₂.fit F₂.room R₂ rfl (TieTree.dig_bytes _ z₂) List.length_ofFn F₂.trace F₂.plains
  subst hv2
  -- the third stretch
  obtain ⟨ρ₃, v₃, e3', d3, p3, -, -⟩ := chain_end_lo Lf D.G.C K g early late t cms x salt rtreq O
      hO P₃ chal hkit₃
    D.G.ds₃ rs₃ ros₃ (1 + D.G.ds₁.length + 1 + D.G.ds₂.length + 1) c₃ ro₃
        (List.ofFn (bytesToDig c₃.rho)) rest
    (some (bytesToDig seal₁)) (fun z => e3 D embP (Sum.inr z)) (q3 D pls).2 F₃ R₃
    (TieTree.dig_bytes _ z₃) List.length_ofFn hl₃
  -- the seam (F3), then backwards
  have st3 := chainP_f3T Lf g early late t cms x salt rtreq (ofR D.G.s3.r) (SL D.G.C D.G.ds₃)
    (allLo (SL D.G.C D.G.ds₃)) (D.G.s3.wire (K + 1) o.c3) (wiresSL D.G.C K chal D.G.ds₃) (e3 D embP)
    (1 + D.G.ds₁.length + 1 + D.G.ds₂.length) (List.ofFn
        (bytesToDig (sealOf (_root_.Fmt.HO O) rs₂ ros₂ c₂)))
    (bytesToDig seal₁) (rootsD ros₃ ++ rest) (rootsD ros₃ ++ rest) [] (q3 D pls).1 (q3 D pls).2
        (takeRt_zero _) _ s3
  have E3 := st3.trans (congrArg (Option.map _) e3')
  have E2 := e2.trans (congrArg (Option.map _) E3)
  have stJ := chainP_joinT Lf g early late t cms x salt rtreq (ofR D.G.s2.r) D.aJ D.hJ
      (SL D.G.C D.G.ds₂ ++ D.S₃)
    (annShS D.G.C D.S₃ D.annS₃ D.G.ds₂) (D.G.s2.wireA D.aJ (K + 1) o.c2)
    (wShS D.G.C K chal D.S₃ D.annS₃ (D.wS₃ K chal o) D.G.ds₂) (eJ D embP) (1 + D.G.ds₁.length) v₁
    (rootsD ros₂ ++ (rootsD ros₃ ++ rest)) (qJ D pls).1 (qJ D pls).2 rfl rfl (bytesToDig seal₁)
        (bytesToDig c₂.rho)
    (sG v₁ hv1l hv1) s4
  have EJ := stJ.trans (congrArg (Option.map _) E2)
  have E1 := e1.trans (congrArg (Option.map _) EJ)
  have st0 := chainP_firstT Lf g early late t cms x salt rtreq (ofR D.F.r)
      (SL D.G.C D.G.ds₁ ++ D.SJ)
    (annLoS D.G.C D.SJ D.annSJ D.G.ds₁) (D.F.wire (K + 1))
        (wLoS D.G.C K chal D.SJ D.annSJ (D.wSJ K chal o) D.G.ds₁)
    embP 0 (rtF ++ (rootsD ros₁ ++ (rootsD ros₂ ++ (rootsD ros₃ ++ rest))))
    (rootsD ros₁ ++ (rootsD ros₂ ++ (rootsD ros₃ ++ rest))) rtF pls.1 pls.2
        (takeRt_app _ rtF _ hF hF2) _ s0
  have E0 := st0.trans (congrArg (Option.map _) E1)
  have rJ : D.rJ (D.F.c, rhJ D.G.C D.SJ D.G.ds₁ ρ₁ (o.c2, rhJ D.G.C D.S₃ D.G.ds₂ ρ₂ (o.c3, ρ₃))) =
      rhJ D.G.C D.S₃ D.G.ds₂ ρ₂ (o.c3, ρ₃) :=
    congrArg Prod.snd (rhS_rhJ D.G.C D.SJ D.G.ds₁ ρ₁ (o.c2, rhJ D.G.C D.S₃ D.G.ds₂ ρ₂ (o.c3, ρ₃)))
  have r1 : D.r₁ (D.F.c, rhJ D.G.C D.SJ D.G.ds₁ ρ₁ (o.c2, rhJ D.G.C D.S₃ D.G.ds₂ ρ₂ (o.c3, ρ₃))) =
      ρ₁ :=
    rhF_rhJ D.G.C D.SJ D.G.ds₁ ρ₁ _
  have r2 : D.r₂ (D.F.c, rhJ D.G.C D.SJ D.G.ds₁ ρ₁ (o.c2, rhJ D.G.C D.S₃ D.G.ds₂ ρ₂ (o.c3, ρ₃))) =
      ρ₂ := by
    unfold BD.r₂
    rw [rJ]
    exact rhF_rhJ D.G.C D.S₃ D.G.ds₂ ρ₂ _
  have r3 : D.r₃ (D.F.c, rhJ D.G.C D.SJ D.G.ds₁ ρ₁ (o.c2, rhJ D.G.C D.S₃ D.G.ds₂ ρ₂ (o.c3, ρ₃))) =
      ρ₃ := by
    unfold BD.r₃
    rw [rJ]
    exact congrArg Prod.snd (rhS_rhJ D.G.C D.S₃ D.G.ds₂ ρ₂ (o.c3, ρ₃))
  refine ⟨(D.F.c, rhJ D.G.C D.SJ D.G.ds₁ ρ₁ (o.c2, rhJ D.G.C D.S₃ D.G.ds₂ ρ₂ (o.c3, ρ₃))), v₃, E0,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [r1]; exact d1
  · rw [r2]; exact d2
  · rw [r3]; exact d3
  · rw [r1]; exact p1
  · rw [r2]; exact p2
  · rw [r3]; exact p3

end Whole

/-! ## The slot value; (G)'s law in letters -/

/-- the last phase's slot value: what reqPart takes -/
theorem chain_whole_slot (v' : Bits) (c : Dig 256) : (Phase.aft v' c).slotVal = some c := rfl

/-- (G)'s law in letters: g's answer is block 1 of the row of a sealed round without message, work
or nonce -/
def GAt {I X : Type} (Lf : Unit → BatchProtocolWithLeafBody I X) (K : ℕ) (g : Fam (typedOracleFamily 256 (K + 1) (Lf ()))) (t : Tag)
    (O : ByteArray → ByteArray) (label : ℕ) (e : PlainPart (Compile.Batch.shapeOf (Lf ()) t)
        (annOf (Lf ()) t)) (i n : ℕ) : Prop :=
  ∀ ρ : Bits, ρ.length = 256 →
    (g (OracleName.g t) (⟨i, ρ, [], e⟩ : JoiningRoundQuery 256 (Lf ()) t) : Dig 256) =
      bytesToDig (_root_.Fmt.blockW (_root_.Fmt.HO O) label (bitsToBytes ρ) n ByteArray.empty
          .sealed 0 0 1)

/-- the seal that a sealed round behind the chain c draws -/
def sealG (O : ByteArray → ByteArray) (c : Chain) : ByteArray :=
  _root_.Fmt.blockW (_root_.Fmt.HO O) c.label c.rho (c.round + 1) ByteArray.empty .sealed 0 0 1

/-- it gives chain_whole's hypothesis sG at seal₁ := sealG O c, c the chain behind the first stretch
-/
theorem GAt.sG {I X : Type} {Lf : Unit → BatchProtocolWithLeafBody I X} {K : ℕ}
    {g : Fam (typedOracleFamily 256 (K + 1) (Lf ()))} {t : Tag}
    {O : ByteArray → ByteArray} {c : Chain} {e : PlainPart (Compile.Batch.shapeOf (Lf ()) t) (annOf (Lf ()) t)} {i : ℕ}
    (h : GAt Lf K g t O c.label e i (c.round + 1)) (ρ : Bits) (h1 : ρ.length = 256)
        (h2 : bitsToBytes ρ = c.rho) :
    (g (OracleName.g t) (⟨i, ρ, [], e⟩ : JoiningRoundQuery 256 (Lf ()) t) : Dig 256) = bytesToDig (sealG O c) :=
  (h ρ h1).trans (by rw [h2]; rfl)

end TypedOracleCompiler.Run.PQ
