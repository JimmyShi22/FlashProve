-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/EntryRun.lean: THE SECOND HALF OF THE ENTRY's JUDGE AS ONE CLOSED, EVALUABLE
TERM: runE: the typing's pure half (assembleS), then the evaluable lax verifier (verifyLX) at the
skeleton PSXE; AND THE TIE: runE … = true EXACTLY IF assembleE GIVES out AND (ZXE …).verifier SAYS
YES ON out UNDER F.
The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on
definitions of Compile/.
WHY. Whoever runs the judge on an entry file asks what the one closed term to evaluate is.
  ix2 n, ix2_inj, ix2_lt     a one-to-one numbering of the two tables' positions: q | n + q; below 2
    n
  mkX a, tstX a, tstX_eq     the set of external positions read as AN ARRAY OF MASKS OF 4,096 BITS
    (Run/MaskChunks.lean), not as the library's one number and Nat.testBit (a
    shift of 2 MB at each of 16.8 million positions at depth 23)
  runE D dec B E early Tf F r0 r1 x o : Bool      THE INTERFACE's TEST IS GIVEN BEHIND A
    FUNCTION OF Unit (Tf : Unit → InteractiveOracleProof …; call it with "fun _ => TSE D e"): with T
    a plain argument, caught by the closure "fun _ => LXE D early T", it is BUILT at the call,
    with its rounds' lists of all verifier messages: ToyEntry's run ended "out of memory" there
  laxE D dec B E early Tf F cms x π : Bool     the part behind assembleS, on a typed string;
    laxE_eq : laxE D dec B E early (fun _ => T) F cms x π = ((ZXE D dec B E early T wT eT
    pT).verifier cms x (ofPS D dec π)).det F;   whyE, whyE_yes: which clause says no
    (Run/LaxWhy.lean)
  runE_eq           runE D dec B E early (fun _ => T) F r0 r1 x o = true ↔ ∃ out, assembleE D
    dec r0 r1 x o = some out ∧ ((ZXE D dec B E early T wT eT pT).verifier out.1 out.2.1 out.2.2).det
    F = true
WHAT IS FED: D: the description (entryXD …, Slice/EntryDesc.lean); dec: the decision as a function
of the instance; B, E: how stored and own symbols lie among the bodies; early, T: the letters
earlyTwo d₁ (Slice/EntryXJudge.lean); TSE D (seedEntry lg s); F: the typed oracle functions (a fast
family, to be tied to readBlocks m H_b by its writer); r0, r1: the two outer roots as bytes; x: the
instance; o: the chain as the strict reader returned it.
WHAT IS NOT SAID. THE JUDGE's FIRST HALF (the seeds' chains under both roots, compared: cmpT) IS NOT
IN runE. That the evaluator brings it home: the wire weX D.a holds the list of all 2 · 2 ^ D.a
external positions, and the verifier walks it once. Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.EntryTyping
import OnBytes.TypedOracleCompiler.Run.LaxWhy
import OnBytes.TypedOracleCompiler.Run.MaskChunks

set_option autoImplicit false

namespace TypedOracleCompiler.Slice
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Run.PQ (XD BodyD OwnE SOf)
open _root_.Run.PQ (View SgX)
open _root_.Run (bytesToDig)
open TypedOracleCompiler.Run.Thin (verifyLX lax_thin mkC tstC tstC_eq)

/-- a numbering of the two tables' positions -/
def ix2 (n : ℕ) : Fin n ⊕ Fin n → ℕ
  | .inl q => q.val
  | .inr q => n + q.val

theorem ix2_inj (n : ℕ) : Function.Injective (ix2 n) := by
  intro p q h
  cases p with
  | inl a =>
    cases q with
    | inl b => exact congrArg Sum.inl (Fin.ext h)
    | inr b =>
      have h' : a.val = n + b.val := h
      have := a.isLt
      omega
  | inr a =>
    cases q with
    | inl b =>
      have h' : n + a.val = b.val := h
      have := b.isLt
      omega
    | inr b =>
      have h' : n + a.val = n + b.val := h
      exact congrArg Sum.inr (Fin.ext (by omega))

theorem ix2_lt (n : ℕ) (p : Fin n ⊕ Fin n) : ix2 n p < 2 * n := by
  cases p with
  | inl q =>
    have := q.isLt
    show q.val < 2 * n
    omega
  | inr q =>
    have := q.isLt
    show n + q.val < 2 * n
    omega

/-- the set of external positions read, as an array of masks of 4,096 bits (Run/MaskChunks.lean) -/
def mkX (a : ℕ) : Finset (Fin (2 ^ a) ⊕ Fin (2 ^ a)) → Array ℕ :=
    mkC (ix2 (2 ^ a)) 4096 (2 * 2 ^ a / 4096 + 1)
/-- is a position in it? -/
def tstX (a : ℕ) : Array ℕ → Fin (2 ^ a) ⊕ Fin (2 ^ a) → Bool := tstC (ix2 (2 ^ a)) 4096

theorem tstX_eq (a : ℕ) (R : Finset (Fin (2 ^ a) ⊕ Fin (2 ^ a))) (p : Fin (2 ^ a) ⊕ Fin (2 ^ a)) :
    tstX a (mkX a R) p = true ↔ p ∈ R :=
  tstC_eq (ix2 (2 ^ a)) (ix2_inj (2 ^ a)) (by decide) (fun q => lt_trans (ix2_lt _ q) (by
    rw [Nat.mul_comm (2 * 2 ^ a / 4096 + 1)]
    exact Nat.lt_mul_div_succ _ (by decide))) R p

variable {X : Type} (D : XD) (dec : X → View → Bool) {Bd : Type} (B : BodyD Bd) (E : OwnE Bd D)
    (early : X → X)
  (Tf : Unit → InteractiveOracleProof Unit (oneExternalString (2 ^ D.a) SgX))

/-- The lax verifier on a typed string, evaluable. The interface's Test stands BEHIND A FUNCTION
OF Unit: a InteractiveOracleProof holds
rounds, a round the list of all its verifier messages: as a plain argument it is built at the call.
-/
def laxE (F : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 (D.K + 1) (LXE (Bd := Bd) D early (Tf ()))))
    (cms : List (Dig 256)) (x : X)
    (π : OneProtocolProof 256 (PSXE D dec).up) : Bool :=
  verifyLX (fun _ => LXE (Bd := Bd) D early (Tf ())) F (mkX D.a) (tstX D.a) early none .link
    (PSXE D dec) (wqXE D dec) E.emb (embPXE D early (Tf ())) some B.embE 0 cms x π

/-- which clause of it says no -/
def whyE (F : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 (D.K + 1) (LXE (Bd := Bd) D early (Tf ()))))
    (cms : List (Dig 256)) (x : X)
    (π : OneProtocolProof 256 (PSXE D dec).up) : TypedOracleCompiler.Run.Thin.Why :=
  TypedOracleCompiler.Run.Thin.whyLX (fun _ => LXE (Bd := Bd) D early (Tf ())) F (mkX D.a) (tstX D.a) early
    none .link (PSXE D dec) (wqXE D dec) E.emb (embPXE D early (Tf ())) some B.embE 0 cms x π

theorem whyE_yes (F : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 (D.K + 1)
    (LXE (Bd := Bd) D early (Tf ())))) (cms : List (Dig 256))
    (x : X) (π : OneProtocolProof 256 (PSXE D dec).up) :
    whyE D dec B E early Tf F cms x π = .yes ↔ laxE D dec B E early Tf F cms x π = true :=
  TypedOracleCompiler.Run.Thin.whyLX_yes _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-- The run. -/
def runE (F : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 (D.K + 1) (LXE (Bd := Bd) D early (Tf ()))))
    (r0 r1 : ByteArray) (x : X)
    (o : _root_.Fmt.ChainOut) : Bool :=
  match assembleS D dec o with
  | some π => laxE D dec B E early Tf F [bytesToDig r0, bytesToDig r1] x π
  | none => false

variable (T : InteractiveOracleProof Unit (oneExternalString (2 ^ D.a) SgX)) (wT : ProtocolQueryLayout 256 (D.K + 1) (BatchInteractiveOracleProof.ofProto T))
  (eT : (p : OPos T.shape) → OSym T.shape p → Bd)
  (pT : (p : OPos T.shape) → Bd → Option (OSym T.shape p))

/-- The lax verifier's tie. -/
theorem laxE_eq (F : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 (D.K + 1) (LXE (Bd := Bd) D early T)))
    (cms : List (Dig 256))
    (x : X) (π : OneProtocolProof 256 (PSXE D dec).up) :
    laxE D dec B E early (fun _ => T) F cms x π =
      ((ZXE D dec B E early T wT eT pT).verifier cms x (ofPS D dec π)).det F :=
  (lax_thin (Y := X) (E := twoExternalStrings (2 ^ D.a) SgX) (LXE (Bd := Bd) D early T) F (mkX D.a) (tstX D.a)
      (tstX_eq D.a) .link (PSXE D dec)
    (wqXE D dec) E.emb (embPXE D early T) some B.embE 0 cms x π).trans
    (congrArg (fun c => OComp.det F c) (ZXE_verifier D dec B E early T wT eT pT cms x
        (ofPS D dec π)).symm)

/-- The tie. -/
theorem runE_eq (F : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 (D.K + 1) (LXE (Bd := Bd) D early T)))
    (r0 r1 : ByteArray)
    (x : X) (o : _root_.Fmt.ChainOut) :
    runE D dec B E early (fun _ => T) F r0 r1 x o = true ↔
      ∃ out, assembleE D dec r0 r1 x o = some out ∧
        ((ZXE D dec B E early T wT eT pT).verifier out.1 out.2.1 out.2.2).det F = true := by
  unfold runE assembleE
  cases hπ : assembleS D dec o with
  | none =>
    constructor
    · intro h
      cases h
    · rintro ⟨out, h, -⟩
      cases h
  | some π =>
    have e := laxE_eq D dec B E early T wT eT pT F [bytesToDig r0, bytesToDig r1] x π
    constructor
    · intro h
      exact ⟨_, rfl, e.symm.trans h⟩
    · rintro ⟨out, h, hv⟩
      obtain rfl := Option.some.inj h
      exact e.trans hv

end TypedOracleCompiler.Slice
