-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/EntryVerdictShort.lean: `verifyE` (OnBytes/TypedOracleCompiler/Slice/EntryVerdict.lean) along
short lists, so that it can be run at the full size.

Why. `verifyE` lists all 2 ^ a positions of a stored table three times over. The wires `we1 a` and
`weX a` hold them as a field, and compiled Lean builds a record whole. The lax verifier walks
`weX a`'s list. And `mkX` first makes of the set of read positions one number with a bit for each
position (`maskOf`, Run/ThinExtReads.lean), which it then cuts in pieces. At the full size of the
entry file (`recordGround`, OnBytes/Tie/EntryGrounds.lean) a is 32, by the text of its parameters.

  `insU`, `sortU`: a list in the order of a key, each key once. Their laws:
    OnBytes/TypedOracleCompiler/Slice/EntryVerdictShortEq.lean.
  `weXL`, `wqXL`: `weX a` and `wqXE D dec` with a given list of all positions, written part by part.
  `memX`: membership in a finite set of positions, as a test.
  `weX_sorted`, `weX_all`: `weX a`'s own list increases strictly under `ix2` and holds every
    position. (OnBytes/RunA/ListedDefs.lean and ListedLaws.lean have the like of these, of `weXL`
    and of `lstX` for the library's own compiler: `all2_numbers`, `all2_complete`, `weLessX`,
    `readsInOrder2`.)
  `lstX`: the external positions that the link reads at given verifier's messages, in `ix2`'s order.
    Its laws: OnBytes/TypedOracleCompiler/Slice/EntryVerdictShortEq.lean.
  `laxEL`, `laxEL_yes`: `laxE` along `lstX`; its yes is a yes of `laxE`.
  `seedChainL`, `cmpEL`: `seedChain` and `cmpE` with the wire's own part named, so that the wire of
    the one string is not built. They are the same functions, by rfl.
  `verifyEL`: `verifyE`'s tests over these.
  `verifyEL_yes`: a yes of `verifyEL` is a yes of `verifyE`, at the same ground, statement and
    value.
What is not claimed: the other direction (OnBytes/TypedOracleCompiler/Slice/EntryVerdictShortEq.lean has it). That
`verifyEL` says yes on any value. A compiled program's answer true is no proof in Lean of
`verifyEL G hok x a = true`: whoever passes from it to `verifyE` trusts Lean's compiler and runtime.
Any time or memory. The limits named in the head of OnBytes/TypedOracleCompiler/Slice/EntryVerdict.lean hold here
too. For proofs and for test programs; the verifier program that ships does not import this file.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.EntryVerdict
import OnBytes.TypedOracleCompiler.Run.LaxShort

set_option autoImplicit false

namespace TypedOracleCompiler.Slice
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Run.PQ (XD BodyD OwnE SOf bodyS wX)
open _root_.Run.PQ (View SgX weX)
open _root_.Run (bytesToDig)
open _root_.Run.Twin (RS)
open TypedOracleCompiler.Run.Thin (chainP verifyLX verifyLXL verifyLXL_yes)
open OnBytes.Tie (EntryGround linkAtCfg keyAt AskedE)
open OnBytes.Slice (GE NZ seedEntry seedOfDrawnC)

/-- One more element into a list that increases strictly under a key. -/
def insU {α : Type} (key : α → ℕ) (x : α) : List α → List α
  | [] => [x]
  | y :: l =>
    if key x < key y then x :: y :: l else if key x = key y then y :: l else y :: insU key x l

/-- A list in the order of a key, each key once. Its laws:
OnBytes/TypedOracleCompiler/Slice/EntryVerdictShortEq.lean. -/
def sortU {α : Type} (key : α → ℕ) (l : List α) : List α := l.foldr (insU key) []

/-- `weX a` with L as its list of all positions, field by field. -/
def weXL (a : ℕ) (L : List (Fin (2 ^ a) ⊕ Fin (2 ^ a))) : WireE (twoExternalStrings (2 ^ a) SgX) where
  all := L
  which := fun p => p.elim (fun _ => 0) (fun _ => 1)
  leaf := fun p => p.elim (fun q => q.val) (fun q => q.val)
  depth := a
  build := fun f => (fun p => (f (.inl p)).getD (0, []), fun p => (f (.inr p)).getD (0, []))
  dec := inferInstanceAs (DecidableEq (Fin (2 ^ a) ⊕ Fin (2 ^ a)))
  pr := true

/-- Membership in a set of positions, as a test. -/
def memX (a : ℕ) (R : Finset (Fin (2 ^ a) ⊕ Fin (2 ^ a))) (p : Fin (2 ^ a) ⊕ Fin (2 ^ a)) : Bool :=
  decide (p ∈ R)

/-- `memX a R p` is true exactly if p is in R. (Stated at `id R`, as `verifyLXL_yes` asks it.) -/
theorem memX_eq (a : ℕ) (R : Finset (Fin (2 ^ a) ⊕ Fin (2 ^ a))) (p : Fin (2 ^ a) ⊕ Fin (2 ^ a)) :
    memX a (id R) p = true ↔ p ∈ R := decide_eq_true_iff

/-- `weX a`'s list of all positions increases strictly under `ix2`. -/
theorem weX_sorted (a : ℕ) : (weX a).all.Pairwise (fun p q => ix2 (2 ^ a) p < ix2 (2 ^ a) q) := by
  show ((List.finRange (2 ^ a)).map Sum.inl ++ (List.finRange (2 ^ a)).map Sum.inr).Pairwise _
  rw [List.pairwise_append]
  refine ⟨?_, ?_, ?_⟩
  · rw [List.pairwise_map]
    exact (List.pairwise_lt_finRange (2 ^ a)).imp fun h => h
  · rw [List.pairwise_map]
    exact (List.pairwise_lt_finRange (2 ^ a)).imp fun h => Nat.add_lt_add_left h _
  · intro p hp q hq
    obtain ⟨p', -, rfl⟩ := List.mem_map.1 hp
    obtain ⟨q', -, rfl⟩ := List.mem_map.1 hq
    show p'.val < 2 ^ a + q'.val
    have := p'.isLt
    omega

/-- `weX a`'s list of all positions holds every position. -/
theorem weX_all (a : ℕ) (p : Fin (2 ^ a) ⊕ Fin (2 ^ a)) : p ∈ (weX a).all := by
  show p ∈ (List.finRange (2 ^ a)).map Sum.inl ++ (List.finRange (2 ^ a)).map Sum.inr
  cases p with
  | inl q => exact List.mem_append_left _ (List.mem_map.2 ⟨q, List.mem_finRange q, rfl⟩)
  | inr q => exact List.mem_append_right _ (List.mem_map.2 ⟨q, List.mem_finRange q, rfl⟩)

section
variable {X : Type} (D : XD) (dec : X → View → Bool) {Bd : Type} (B : BodyD Bd) (E : OwnE Bd D)
    (early : X → X)
  (Tf : Unit → InteractiveOracleProof Unit (oneExternalString (2 ^ D.a) SgX))

/-- `wqXE D dec` with L as the list of all external positions, part by part. -/
def wqXL (L : List (Fin (2 ^ D.a) ⊕ Fin (2 ^ D.a))) : ProtocolQueryLayout 256 (D.K + 1) (PSXE D dec).up :=
  ⟨(PQ.wire0S D.C D.K (_root_.Run.chalP D.base.plan.field D.K),
      PQ.wiresSL D.C D.K (_root_.Run.chalP D.base.plan.field D.K) D.ds),
    weXL D.a L, PQ.decOS D.C D.ds, PQ.nOpen D.ds + (D.xs.map (·.count)).sum,
    max (PQ.maxDepth D.ds) D.a⟩

/-- The external positions that the link reads at ρ, in the order of `ix2`. -/
def lstX (_ : X) (ρ : Rho (_root_.Run.Twin.up (PSXE D dec).S)) :
    List (Fin (2 ^ D.a) ⊕ Fin (2 ^ D.a)) :=
  sortU (ix2 (2 ^ D.a))
    ((PQ.xWanted D.a D.ds D.xs (PQ.drawnSL D.C D.ds ρ.2)).filterMap (_root_.Run.PQ.xPos (2 ^ D.a)))

/-- `laxE` along the short list. -/
def laxEL (F : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 (D.K + 1) (LXE (Bd := Bd) D early (Tf ()))))
    (cms : List (Dig 256)) (x : X) (π : OneProtocolProof 256 (PSXE D dec).up) : Bool :=
  verifyLXL (fun _ => LXE (Bd := Bd) D early (Tf ())) F id (memX D.a) early none .link
    (PSXE D dec) (wqXL D dec []).sh (wqXL D dec) (ix2 (2 ^ D.a)) (lstX D dec) E.emb
    (embPXE D early (Tf ())) some B.embE 0 cms x π

/-- A yes of `laxEL` is a yes of `laxE`. -/
theorem laxEL_yes
    (F : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 (D.K + 1) (LXE (Bd := Bd) D early (Tf ()))))
    (cms : List (Dig 256)) (x : X) (π : OneProtocolProof 256 (PSXE D dec).up)
    (h : laxEL D dec B E early Tf F cms x π = true) : laxE D dec B E early Tf F cms x π = true :=
  verifyLXL_yes (fun _ => LXE (Bd := Bd) D early (Tf ())) F (mkX D.a) (tstX D.a) id
    (memX D.a) early none .link
    (PSXE D dec) (wqXE D dec) (wqXL D dec) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (ix2 (2 ^ D.a)) (weX_sorted D.a)
    (weX_all D.a) (tstX_eq D.a) (memX_eq D.a) (lstX D dec) E.emb (embPXE D early (Tf ())) some
    B.embE 0 cms x π h

end

/-! ## The seeds' comparison -/

section
variable {A S : Type} [DecidableEq S] (D : XD) {Bd : Type}
  (early : A × (S × S) → A × (S × S)) (e : _root_.Fmt.Entry) (sOf : List _root_.Fmt.Drawn → S)

/-- `seedChain` with the wire's own part named: the wire of the one string is not built. -/
def seedChainL (F : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 (D.K + 1)
    (LXE (Bd := Bd) D early (TSE D e)))) (c : Dig 256) :
    Option (Rho (TSE D e).shape × RootsOfChain 256 (TSE D e).shape × Phase 256) :=
  chainP (fun _ => LXE (Bd := Bd) D early (TSE D e)) F early none .test [c] none [] default
      (SOf D.C [dSeed e])
    (_root_.Run.Twin.allLo (SOf D.C [dSeed e]))
    (PQ.wire0S D.C D.K (_root_.Run.chalP D.base.plan.field D.K),
      PQ.wireS D.C D.K (_root_.Run.chalP D.base.plan.field D.K) (dSeed e), ()) id 0 .first []
    ((PQ.s0 D.C).dPlain, (PQ.roundS D.C (dSeed e)).dPlain, ())

omit [DecidableEq S] in
/-- `seedChainL` is `seedChain`. -/
theorem seedChainL_eq (F : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 (D.K + 1)
    (LXE (Bd := Bd) D early (TSE D e)))) : seedChainL D early e F = seedChain D early e F := rfl

/-- `cmpE` over it. -/
def cmpEL
    (F : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 (D.K + 1) (LXE (Bd := Bd) D early (TSE D e)))) :
    List (Dig 256) → ℕ → S × S → Bool :=
  cmpG (seedChainL D early e F) (fun y => seedOfE D e sOf y.1) (pack2 S).get

/-- `cmpEL` is `cmpE`. -/
theorem cmpEL_eq (F : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 (D.K + 1)
    (LXE (Bd := Bd) D early (TSE D e)))) : cmpEL D early e sOf F = cmpE D early e sOf F := rfl

end

/-! ## The verifier of a call -/

variable (G : EntryGround)
  (hok : ∀ c : ByteArray, c.size = 32 → TypedOracleCompiler.Run.PQ.ok (entryXD G c).base = true)

/-- `verifyE` along short lists. -/
def verifyEL (x : EntryStmt) (a : AskedE) : Bool :=
  pinsFit (entryXD G x.c) G.q.link.table &&
    match assembleS (entryXD G x.c)
      (decRun (linkAtCfg G.q x.c) G.q.link.table.v G.q.link.table.cubeBits G.q.link.table.answers)
      a.out with
    | none => false
    | some π =>
      (cmpEL (entryXD G x.c)
          (earlyTwo (d1Run G.q.link.table.cubeBits G.q.link.table.answers))
          (seedEntry G.q.link.table.cubeBits G.q.link.table.answers)
          (seedOfDrawnC G.q.link.table.cubeBits G.q.link.table.answers)
          (EntryRunTop.famOf (entryXD G x.c) x.hc
            (d1Run G.q.link.table.cubeBits G.q.link.table.answers) G.q.link.table)
          [_root_.Run.bytesToDig a.first.root, _root_.Run.bytesToDig a.further.root] 0
          (xOfAskedC G.q.link.table.cubeBits G.q.link.table.answers a).2 &&
        laxEL (entryXD G x.c) _ (bodyS (entryXD G x.c).a (entryXD G x.c).base.plan.salt)
          (ownES (entryXD G x.c) (hok x.c x.hc))
          (earlyTwo (d1Run G.q.link.table.cubeBits G.q.link.table.answers))
          (fun _ => TSE (entryXD G x.c) (seedEntry G.q.link.table.cubeBits G.q.link.table.answers))
          (EntryRunTop.famOf (entryXD G x.c) x.hc
            (d1Run G.q.link.table.cubeBits G.q.link.table.answers) G.q.link.table)
          [_root_.Run.bytesToDig a.first.root, _root_.Run.bytesToDig a.further.root]
          (xOfAskedC G.q.link.table.cubeBits G.q.link.table.answers a) π) &&
      (stmtId G.q.link.table x.c (_root_.Run.bytesToDig a.first.root)
        (xOfAskedC G.q.link.table.cubeBits G.q.link.table.answers a).2.1
        (xOfAskedC G.q.link.table.cubeBits G.q.link.table.answers a).1.1 == x.id)

/-- **A yes of `verifyEL` is a yes of `verifyE`.** -/
theorem verifyEL_yes (x : EntryStmt) (a : AskedE) (h : verifyEL G hok x a = true) :
    verifyE G hok x a = true := by
  unfold verifyEL at h
  unfold verifyE
  rw [Bool.and_eq_true] at h ⊢
  refine ⟨h.1, ?_⟩
  have h2 := h.2
  cases hA : assembleS (entryXD G x.c)
      (decRun (linkAtCfg G.q x.c) G.q.link.table.v G.q.link.table.cubeBits G.q.link.table.answers)
      a.out with
  | none =>
    rw [hA] at h2
    cases h2
  | some π =>
    rw [hA] at h2
    simp only [Bool.and_eq_true] at h2
    obtain ⟨⟨hc, hl⟩, hi⟩ := h2
    simp only [Bool.and_eq_true]
    refine ⟨?_, hi⟩
    rw [beq_iff_eq]
    exact (whyOutE_yes _ _ _ _ _ _ _ _).2 ⟨rfl, hc, laxEL_yes _ _ _ _ _ _ _ _ _ _ hl⟩

end TypedOracleCompiler.Slice
