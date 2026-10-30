-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/WireX.lean: a whole wiring at the entry's interface over the sibling, with the
sibling's laws of a whole wiring; and the compiled verifier of one slot as that wiring's compiled
Link verifier.
The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on
definitions of Compile/.

WHY. OnBytes/TypedOracleCompiler/Run/PageXAsked.lean to AllRoots.lean speak of `verifyOneProtocol` at the wiring `wX D dec`
of ONE protocol. The sibling's analysis of the compiled argument (Compile/Batch/Sound.lean), and a
judge over it, speak of `vLS W` at a wiring W of a WHOLE interface: three protocols, and how symbols
are written into leaves' bodies and read back. This file makes that W at `D.L Bd dec` and ties the
two verifiers.

After OnBytes/Slice/TopAny.lean (its first two sections and `WkAny`, `okgAny`, `asLink`, `vls_any`:
17 declarations) and the library's Run/PlanQXDoor.lean, PlanQXDoorProofs.lean (`wq1`, `wq1_okg`,
`one_depth`, `WkX`, `okgWkX`).
AS TEXT but for `_root_.` (in `psofX_up` and `embPL_eq`: `_root_.Run.` before `Twin.allLo_eq`) and
line breaks (15). `wireTo`, `wireTo_okg`, `wireTo_ext`, `wireTo_maxDepth`, `reAnn`, `reAnn_eq`,
`pbTo`, `pbTo_inl`, `pbTo_inr`, `verifyBS_ann`, `psofX_up`, `embPL_eq`, `wq1`, `wq1_okg`,
`one_depth`.
TURNED (7).
 `embPX_eq`         the type of bodies is an argument.
 `WkX`, `okgWkX`    the sibling's whole wiring has eight fields more, with four laws: stored symbols
                    go by `B.embE`, `B.getE` (`B.get_e`); Link's own symbols by E; Test and Batch
                    have no position.
 `WkAny`, `asLink`, `vls_any`   at B and E; the verifier's embeddings are `E.emb` and `B.embE`,
                    where the original writes the library's tagged bodies.
 `okgAny`           from the sibling's `planPull_okg` with `blocks_le_kOf`, where the original calls
                    the library's `M1RunTieP.okgOf`; the condition on work is said of the sibling's
                    rounds' data.
NEW (4).
 `OwnE Bd D`        an embedding of the chain's own symbols into bodies WITH a reading back and its
                    law. OnBytes/TypedOracleCompiler/Run/PageXAsked.lean and what follows take the embedding alone.
 `mem_rdsFrom`, `mem_rdsFrom_lib`, `blocks_le_kOf`   `D.K` is the library's `kOf`, the greatest
                    number of blocks over the LIBRARY'S rounds' data; it is enough for every round
                    of the sibling's, since both lists have the rounds' entries and kinds. The last
                    two name the library's rounds' data, on purpose.


WHAT IS NOT SAID. That any type of bodies has a `BodyD` and an `OwnE` together with `OwnFits` and
the spelling of own symbols that the files above ask: not here (at strings of bits:
OnBytes/TypedOracleCompiler/Slice/PartChainStr.lean). Round-by-round soundness of the Link of `D.L Bd dec`: its
shape is made from the sibling's rounds' data and is not the library's. The number of the Link
verifier's queries at this wiring. No judge, no part. Nothing on soundness; no probability; nothing
on any hash.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Run.PageXAsked
import OnBytes.TypedOracleCompiler.Run.PlanQXLawsProofs
import OnBytes.TypedOracleCompiler.Run.PlanPull
import Run.PlanPullM1

set_option autoImplicit false

namespace TypedOracleCompiler.Run.PQ
open Rom TypedOracleCompiler.Iop _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Run.Twin
  TypedOracleCompiler.Run.Thin
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ TypedOracleCompiler.Run

/-! ## The same data under an equal marking -/

section
variable {Y : Type} {E : ExtSpec} {lam K : ℕ}

/-- A wiring, carried along an equation between two batch protocols. -/
def wireTo {Q Q' : BatchInteractiveOracleProof Y E} (h : Q = Q') (w : ProtocolQueryLayout lam K Q) : ProtocolQueryLayout lam K Q' := h ▸ w

/-- The laws of a wiring go along. -/
theorem wireTo_okg {Q Q' : BatchInteractiveOracleProof Y E} (h : Q = Q') (w : ProtocolQueryLayout lam K Q) (hw : w.OKG) :
    (wireTo h w).OKG := by
  subst h
  exact hw

/-- The wire of the outside strings is not touched. -/
theorem wireTo_ext {Q Q' : BatchInteractiveOracleProof Y E} (h : Q = Q') (w : ProtocolQueryLayout lam K Q) :
    (wireTo h w).ext = w.ext := by
  subst h
  rfl

/-- The bound on depths is not touched. -/
theorem wireTo_maxDepth {Q Q' : BatchInteractiveOracleProof Y E} (h : Q = Q') (w : ProtocolQueryLayout lam K Q) :
    (wireTo h w).maxDepth = w.maxDepth := by
  subst h
  rfl

/-- A proof string under another marking of the same protocol. No field of a proof string reads
the marking, so the fields are the same. -/
def reAnn {loc : InteractiveOracleProof Y E} {A : RoundSplits loc.shape} (A' : RoundSplits loc.shape) (π : OneProtocolProof lam ⟨loc, A⟩) :
    OneProtocolProof lam ⟨loc, A'⟩ :=
  ⟨π.salt, π.roots, π.plains, π.opens, π.ext, π.rtreq, π.slot, π.path, π.rsalt⟩

/-- Carrying a proof string along the equation gives the same string. -/
theorem reAnn_eq {loc : InteractiveOracleProof Y E} {A A' : RoundSplits loc.shape} (h : A = A') (π : OneProtocolProof lam ⟨loc, A⟩) :
    (congrArg (BatchInteractiveOracleProof.mk loc) h ▸ π : OneProtocolProof lam ⟨loc, A'⟩) = reAnn A' π := by
  subst h
  rfl

/-- A plain part, carried along an equation between two markings of one shape. -/
def pbTo {s : Shape} {A A' : RoundSplits s} (e : A = A') (z : PlainPart s A) : PlainPart s A' := e ▸ z

/-- A plain part of the first round stays, if the first round's marking stays. -/
theorem pbTo_inl {r : Round} {s : Shape} (a : RAnn r) {A A' : RoundSplits s} (e : A = A')
    (h : ((a, A) : RoundSplits (r :: s)) = (a, A')) (x : a.P0 ⊕ a.Pj) :
    pbTo (s := r :: s) (A := (a, A)) (A' := (a, A')) h (Sum.inl x) = Sum.inl x := by
  subst e
  rfl

/-- A plain part of a later round is carried along the equation of the later rounds. -/
theorem pbTo_inr {r : Round} {s : Shape} (a : RAnn r) {A A' : RoundSplits s} (e : A = A')
    (h : ((a, A) : RoundSplits (r :: s)) = (a, A')) (q : PlainPart s A) :
    pbTo (s := r :: s) (A := (a, A)) (A' := (a, A')) h (Sum.inr q) = Sum.inr (pbTo e q) := by
  subst e
  rfl

/-- The compiled verifier of one slot does not change when the marking is replaced by an equal
one and wiring, string and the map on plain parts are carried along. -/
theorem verifyBS_ann {I X : Type} {L : BatchProtocolWithLeafBody I X} (sMT sFS : ℕ) (t : Tag) (loc : InteractiveOracleProof Y E)
    (A A' : RoundSplits loc.shape) (h : A = A') (wq : ProtocolQueryLayout lam K ⟨loc, A⟩)
    (embS : (p : OPos loc.shape) → OSym loc.shape p → Body L)
    (embP : PlainPart loc.shape A → PlainPart (shapeOf L t) (annOf L t))
    (embP' : PlainPart loc.shape A' → PlainPart (shapeOf L t) (annOf L t))
    (hP : ∀ z, embP z = embP' (pbTo h z))
    (xin : Y → Option X) (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y)
    (π : OneProtocolProof lam ⟨loc, A⟩) :
    verifyOneProtocol sMT sFS t ⟨loc, A⟩ wq embS embP xin embE depthReq cms x π =
      verifyOneProtocol sMT sFS t ⟨loc, A'⟩ (wireTo (congrArg (BatchInteractiveOracleProof.mk loc) h) wq) embS embP' xin embE
        depthReq cms x (reAnn A' π) := by
  subst h
  have hE : embP = embP' := funext hP
  subst hE
  rfl

end

/-! ## The protocol of a description -/

/-- The protocol that is made from a description carries the marking "all rounds local". -/
theorem psofX_up (C : CK) (ds : List RD) (a : ℕ) (xs : List XO) (dec : View → Bool) :
    (skeletonOverBothExternalStrings C ds a xs dec).up = BatchInteractiveOracleProof.ofProto (skeletonOverBothExternalStrings C ds a xs dec).up.loc :=
  congrArg (BatchInteractiveOracleProof.mk (skeletonOverBothExternalStrings C ds a xs dec).up.loc) (_root_.Run.Twin.allLo_eq (SOf C ds))

/-- The map `embPL` on plain parts of the rounds of a description is the carrying along the equation
between the two markings. -/
theorem embPL_eq (C : CK) : ∀ (ds : List RD) (q : PlainPart (uL C ds) (Twin.allLo (SL C ds))),
    embPL C ds q = pbTo (_root_.Run.Twin.allLo_eq (SL C ds)) q
  | [], q => q.elim
  | _ :: ds, .inl x => (pbTo_inl _ (_root_.Run.Twin.allLo_eq (SL C ds)) _ x).symm
  | _ :: ds, .inr q =>
    (congrArg Sum.inr (embPL_eq C ds q)).trans
      (pbTo_inr _ (_root_.Run.Twin.allLo_eq (SL C ds)) _ q).symm

/-- The same for the whole shape, with the round in front. -/
theorem embPX_eq (Bd : Type) (C : CK) (ds : List RD) (a : ℕ) (xs : List XO) (dec : View → Bool)
    (z : PlainPart (Twin.up (SOf C ds)) (Twin.allLo (SOf C ds))) :
    embPX (I := Unit) (RI := Unit) Bd C ds a xs dec (fun _ _ p => (p.val, [])) (fun _ => some ())
        z =
      pbTo (_root_.Run.Twin.allLo_eq (SOf C ds)) z := by
  cases z with
  | inl x => exact (pbTo_inl _ (_root_.Run.Twin.allLo_eq (SL C ds)) _ x).symm
  | inr q =>
    exact (congrArg Sum.inr (embPL_eq C ds q)).trans
      (pbTo_inr _ (_root_.Run.Twin.allLo_eq (SL C ds)) _ q).symm

/-! ## The whole wiring -/

/-- The wiring of a protocol without a round on one string. -/
def wq1 (K a : Nat) : ProtocolQueryLayout 256 K (BatchInteractiveOracleProof.ofProto (pT1 (2 ^ a))) :=
  ⟨(), WireE.one (2 ^ a) SgX (0, []), inferInstanceAs (DecidableEq Empty), 0, a⟩

/-- It obeys the laws of a wiring. -/
theorem wq1_okg (K a : Nat) : (wq1 K a).OKG :=
  { sh := trivial, ext := WireE.one_ok (2 ^ a) SgX (0, []),
    opens := fun _ _ _ => le_refl 0, depth := trivial }

/-- The wire of one string of 2^a symbols has the depth a. -/
theorem one_depth (a : Nat) : (WireE.one (2 ^ a) SgX (0, [])).depth = a :=
  Nat.clog_pow 2 a Nat.one_lt_two

/-- TWO: how the chain's own symbols lie among the bodies, as data: an embedding, a reading
back, and the law that what is written is read back. -/
structure OwnE (Bd : Type) (D : XD) where
  /-- a symbol of a prover oracle, as a body -/
  emb : (p : OPos (Twin.up (SOf D.C D.ds))) → OSym (Twin.up (SOf D.C D.ds)) p → Bd
  /-- a body, read as the symbol at position p -/
  prj : (p : OPos (Twin.up (SOf D.C D.ds))) → Bd → Option (OSym (Twin.up (SOf D.C D.ds)) p)
  /-- what is written is read back -/
  prj_emb : ∀ p a, prj p (emb p a) = some a

section
variable {Bd : Type} (B : BodyD Bd) (D : XD) (dec : View → Bool) (E : OwnE Bd D)

/-- The whole wiring at the entry's interface. Link's wiring is any wL of the sibling's type for
it; Test and Batch have no rounds; the external trees have the depth `D.a`; a batch has one slot.
TWO: stored symbols are written into bodies and read back by `B.embE`, `B.getE`; Link's own symbols
by E; Test and Batch have no position. -/
def WkX (K : Nat) (wL : ProtocolQueryLayout 256 K (BatchInteractiveOracleProof.ofProto (D.L Bd dec).link)) :
    QueryLayout 256 (D.L Bd dec) where
  K := K
  T := wq1 K D.a
  Lk := wL
  B := wq1 K D.a
  depth := D.a
  depthReq := 0
  depthReqT := 0
  depthReqL := 0
  embE := B.embE
  prjE := B.getE
  embT := fun p => p.elim
  prjT := fun p => p.elim
  embL := E.emb
  prjL := E.prj
  embB := fun p => p.elim
  prjB := fun p => p.elim

/-- It obeys the laws of a whole wiring, if Link's does, has the wire `weX D.a` of the two
strings, and bounds depths by at least `D.a`. -/
theorem okgWkX (K : Nat) (wL : ProtocolQueryLayout 256 K (BatchInteractiveOracleProof.ofProto (D.L Bd dec).link))
    (h : wL.OKG) (he : wL.ext = weX D.a) (hd : D.a ≤ wL.maxDepth) : (WkX B D dec E K wL).OKG :=
  { T := wq1_okg K D.a
    Lk := h
    B := wq1_okg K D.a
    fits := le_refl _
    slots := rfl
    extDepth := ⟨one_depth D.a, by show wL.ext.depth = D.a; rw [he]; rfl, one_depth D.a⟩
    depthT := le_refl _, depthL := hd, depthB := le_refl _
    extT := fun _ => ⟨rfl, rfl⟩
    extB := fun _ => ⟨rfl, rfl⟩
    extL := ⟨fun p => by
        show wL.ext.which (.inl p) = 0 ∧ wL.ext.leaf (.inl p) = p.val; rw [he]; exact ⟨rfl, rfl⟩,
      fun p => by
        show wL.ext.which (.inr p) = 1 ∧ wL.ext.leaf (.inr p) = p.val; rw [he]; exact ⟨rfl, rfl⟩⟩
    prjE_emb := B.get_e
    prjT_emb := fun p => p.elim
    prjL_emb := E.prj_emb
    prjB_emb := fun p => p.elim }

/-- The whole wiring, for every description: Link's is the protocol's `wX D dec`. -/
def WkAny : QueryLayout 256 (D.L Bd dec) :=
  WkX B D dec E (D.K + 1) (wireTo (psofX_up D.C D.ds D.a D.xs dec) (wX D dec))

end

/-! ## The number of blocks is enough -/

/-- A member of the sibling's rounds' data has the entry and the kind of one of the rounds. -/
theorem mem_rdsFrom (S : _root_.Fmt.Spec) : ∀ (rs : List _root_.Fmt.Round) (n : ℕ) (d : RD),
    d ∈ rdsFrom S n rs → ∃ r ∈ rs, d.entry = r.entry ∧ d.kind = r.kind
  | [], _, _, h => by cases h
  | r :: rs, n, d, h => by
    rcases List.mem_cons.1 h with e | h'
    · exact ⟨r, List.mem_cons_self, by rw [e], by rw [e]⟩
    · obtain ⟨r', hr', h1, h2⟩ := mem_rdsFrom S rs _ d h'
      exact ⟨r', List.mem_cons_of_mem _ hr', h1, h2⟩

/-- Each round has a member of the LIBRARY'S rounds' data with its entry and kind. -/
theorem mem_rdsFrom_lib (S : _root_.Fmt.Spec) : ∀ (rs : List _root_.Fmt.Round) (n : ℕ)
    (r : _root_.Fmt.Round), r ∈ rs →
    ∃ d ∈ _root_.Run.PQ.rdsFrom S n rs, d.entry = r.entry ∧ d.kind = r.kind
  | [], _, _, h => by cases h
  | r' :: rs, n, r, h => by
    rcases List.mem_cons.1 h with e | h'
    · subst e
      exact ⟨_, List.mem_cons_self, rfl, rfl⟩
    · obtain ⟨d, hd, h1, h2⟩ := mem_rdsFrom_lib S rs _ r h'
      exact ⟨d, List.mem_cons_of_mem _ hd, h1, h2⟩

/-- The library's number of blocks is enough for every round of the sibling's rounds' data.
`kOf` is the greatest number over the library's rounds' data; both lists have the rounds' entries
and kinds. -/
theorem blocks_le_kOf (S : _root_.Fmt.Spec) :
    ∀ d ∈ rds S, (bsRound S.plan.field d.entry d.kind).b ≤ kOf S := by
  intro d hd
  obtain ⟨r, hr, h1, h2⟩ := mem_rdsFrom S S.rounds 0 d hd
  obtain ⟨d', hd', g1, g2⟩ := mem_rdsFrom_lib S S.rounds 0 r hr
  have h := _root_.Run.le_kMax (fun e k => (bsRound S.plan.field e k).b) (_root_.Run.PQ.rds S) d'
    hd'
  rw [g1, g2, ← h1, ← h2] at h
  exact h

section
variable {Bd : Type} (B : BodyD Bd) (D : XD) (dec : View → Bool) (E : OwnE Bd D)

/-- The whole wiring obeys the sibling's laws. Asked: the two conditions on the description: no
round asks more than 64 bits of work; the limits `okX` on the stored tables' openings. -/
theorem okgAny (hwork : ∀ d ∈ D.ds, d.entry.work ≤ 64) (hokx : okX D.ds D.a D.xs = true) :
    (WkAny B D dec E).OKG :=
  okgWkX B D dec E (D.K + 1) _
    (wireTo_okg _ _ (wqX_okg D.C D.K (chalP D.base.plan.field D.K) D.ds D.a D.xs dec dec
      (okX_own D.ds D.a D.xs hokx)
      (planPull_okg D.base.plan.field D.K D.ds dec (blocks_le_kOf D.base) hwork)))
    (wireTo_ext _ _)
    (le_of_le_of_eq (le_max_right (maxDepth D.ds) D.a) (wireTo_maxDepth
      (psofX_up D.C D.ds D.a D.xs dec) (wX D dec)).symm)

/-- A typed string of the protocol as a Link string of the interface: the same fields. -/
def asLink (π : OneProtocolProof 256 (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).up) :
    OneProtocolProof 256 (BatchInteractiveOracleProof.ofProto (D.L Bd dec).link) :=
  reAnn _ π

/-- The compiled verifier of one slot, at the protocol, wiring and maps of a description, is the
compiled Link verifier of the whole wiring. -/
theorem vls_any (sMT : ℕ) (cm cm' : Dig 256)
    (π : OneProtocolProof 256 (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).up) :
    verifyOneProtocol (lam := 256) (K := D.K + 1) (L := D.L Bd dec) sMT 256 .link
      (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).up (wX D dec) E.emb (embX Bd D dec)
      (fun _ => none) B.embE 0 [cm, cm'] () π
    = vLS (WkAny B D dec E) sMT 256 cm cm' (asLink (Bd := Bd) D dec π) :=
  verifyBS_ann (L := D.L Bd dec) sMT 256 .link (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).up.loc
    (Twin.allLo (SOf D.C D.ds)) (RoundSplits.allLocal (Twin.up (SOf D.C D.ds)))
    (_root_.Run.Twin.allLo_eq (SOf D.C D.ds)) (wX D dec) E.emb (embX Bd D dec) id
    (embPX_eq Bd D.C D.ds D.a D.xs dec) (fun _ => none) B.embE 0 [cm, cm'] () π

end

end TypedOracleCompiler.Run.PQ
