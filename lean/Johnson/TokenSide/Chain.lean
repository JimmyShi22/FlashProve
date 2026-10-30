-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TokenSide/Chain.lean: THE CHAIN OF THE COMPILED PROVER OF ONE SLOT AS A TOKEN PROGRAM, for
the second form. DEFINITIONS, and five small lemmas that the definitions need.

The program chainT is laid, bind by bind, on the compiled prover's chain (searchO, fsO, onFs,
chainO, OnBytes/Prover/Defs.lean): the same case split (by the kind of the round and the phase), in
each case the same trees and the same queries in the same order. IT HAS NO REVEAL. It follows the
pattern of the first form's prover (fbT, fbTw, fbW, fbTG, gT, Compile/Batch/Prover.lean) at one
slot.

What is a token, and what each evaluation is charged to.
  the chain's first salt              (F1) is charged to it
  the chaining value of an answer     the next query (F2), (F5) or g is charged to it
  the slot value c (g's answer)       the request tree's leaf, and (F3), are charged to it; (F3)
                                      also holds the last shared chaining value
  the digests on the request path     the inner node above is charged to the one below
  the request root                    (F4) is charged to it
  the free bits of a leaf's salt      the leaf (Johnson/TokenSide/Tree.lean)
Values, not tokens (CoinsD): the body of a padding leaf, the slot's number, the sibling digests of
the request path, the string behind the slot value. No evaluation is charged to them, and each
point that holds one of them also holds an unshown token.
The roots of the trees are values in the points.

A ROUND WITH A TEST. The compiled prover asks one Fiat-Shamir oracle once for each nonce. A token
may be charged once at each oracle. So try number 0 is written at fb t and try number n + 1 at the
name fbw t n, at the same input and with the same charge, as in the first form. The number of tries
in round number i is cap i + 1: THE CAP IS A LETTER, the wire's own number (GrW.more) is not read.
A SEARCH THAT RUNS OUT STOPS THE RUN: the outcome is Res.ranOut i, as the compiled prover's. (The
first form's prover goes on with the last try.)

Main names (namespace OnBytes.TokenSide).
  CoinsD    the coins that are values.
  PhT, PhT.val, ActT, actT   the phase with tokens; its value; what is done in a round.
  fbT, gT, rleafT, rnodeL, rnodeR, climbT   the marked evaluations.
  Hit, searchT, fsT, onFsT   what a search returns; the search; a Fiat-Shamir query with a test or
            without; what follows it.
  KeptT, OutT, consT, chainT   what is kept; what the chain yields; THE CHAIN.

OutT.toks: every token that the chain has made but for the leaves': the chaining values of all
tries, the failed ones too, the slot value, the digests on the request path with its root. With the
first salt they are what the first reveal shows if the run's string is handed out (endC,
Johnson/TokenRules/Chunks.lean).

Limits. Definitions: that chainT erases to chainO, keeps the rules, and how many evaluations it
makes, is not shown here (the first: Johnson/TokenSide/TieAll.lean). One slot.
Terms: lean/GLOSSARY.md.

-/
import Johnson.TokenSide.Tree

set_option autoImplicit false

noncomputable section

namespace OnBytes.TokenSide
open _root_.Compile hiding ON
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom OnBytes.Prover
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-! ## Coins that are values -/

/-- What of a compiled run's coins (Coins, OnBytes/Prover/Defs.lean) is a value in the token
program: all but the first salt and the leaves' salts. -/
structure CoinsD (lam : ℕ) (L : BatchProtocolWithLeafBody I X) where
  /-- the body of a leaf at which no position stands -/
  pad : Body L
  /-- the slot, the sibling digests of its leaf in the request tree, the string behind its value -/
  slot : ℕ
  path : List (Dig lam)
  rsalt : Bits

/-! ## Phases and acts -/

/-- how far the chain has come, with tokens in the place of the strings of Phase
(OnBytes/TypedOracleCompiler/Compile/Batch/Verifier.lean) -/
inductive PhT
  | first
  | loc (tk : Tok)
  | shr (tk0 : Tok) (c : Tok)
  | aft (tk : Tok) (c : Tok)

/-- the phase, at values of the tokens -/
def PhT.val (lam : ℕ) (val : Tok → Bits) : PhT → Phase lam
  | .first => .first
  | .loc tk => .loc (val tk)
  | .shr tk0 c => .shr (val tk0) (digOf lam (val c))
  | .aft tk c => .aft (val tk) (digOf lam (val c))

theorem f1_inj (cms : List (Dig lam)) (x xl : Option X) :
    Function.Injective fun v : Bits => (Head.f1 cms x v).withLate xl := fun a b h => by
  have h' : Head.f1 cms x a = Head.f1 cms x b := h
  cases h'; rfl

theorem f2_inj (xl : Option X) :
    Function.Injective fun v : Bits => (Head.f2 none v : Head lam X).withLate xl := fun a b h => by
  have h' : (Head.f2 xl a : Head lam X) = Head.f2 xl b := h
  cases h'; rfl

theorem f3_inj (ρ0 : Bits) (xl : Option X) :
    Function.Injective fun v : Bits => (Head.f3 ρ0 v : Head lam X).withLate xl := fun a b h => by
  have h' : (Head.f3 ρ0 a : Head lam X) = Head.f3 ρ0 b := h
  cases h'; rfl

theorem f4_inj (cms : List (Dig lam)) :
    Function.Injective fun v : Bits => (Head.f4 cms v : Head lam X) := fun a b h => by
  cases h; rfl

theorem f5_inj (xl : Option X) :
    Function.Injective fun v : Bits => (Head.f5 v : Head lam X).withLate xl := fun a b h => by
  have h' : (Head.f5 a : Head lam X) = Head.f5 b := h
  cases h'; rfl

/-- What is done in a round, with tokens: the twin of Act
(OnBytes/TypedOracleCompiler/Compile/Batch/Verifier.lean). -/
inductive ActT (lam : ℕ) (X : Type)
  /-- one Fiat-Shamir query: charged to tk, with the further tokens us; its header is hd (values of
  us) (value of tk); own and next as in Act.one, next a function of the token of the chaining
  value -/
  | one (tk : Tok) (us : List Tok) (hd : List Bits → Bits → Head lam X)
      (inj : ∀ (xl : Option X) (vs : List Bits),
        Function.Injective fun v => (hd vs v).withLate xl)
      (own : Bool) (next : Tok → PhT)
  /-- the joining round; tk: the last chaining value -/
  | join (tk : Tok)

/-- Kind and phase fix the format: the twin of actOf. salt: the token of the chain's first salt. -/
def actT (cms : List (Dig lam)) (x : Option X) (salt : Tok) : Kind → PhT → Option (ActT lam X)
  | .lo, .first => some (.one salt [] (fun _ v => .f1 cms x v) (fun xl _ => f1_inj cms x xl) true
      .loc)
  | .lo, .loc tk => some (.one tk [] (fun _ v => .f2 none v) (fun xl _ => f2_inj xl) true .loc)
  | .sh, .loc tk => some (.join tk)
  | .sh, .shr tk0 c => some (.one tk0 [] (fun _ v => .f5 v) (fun xl _ => f5_inj xl) false
      fun v => .shr v c)
  | .lo, .shr tk0 c => some (.one c [tk0] (fun vs v => .f3 (vs.headD []) v)
      (fun xl vs => f3_inj (vs.headD []) xl) true fun v => .aft v c)
  | .lo, .aft tk c => some (.one tk [] (fun _ v => .f2 none v) (fun xl _ => f2_inj xl) true
      fun v => .aft v c)
  | .sh, .first => none
  | .sh, .aft _ _ => none

/-! ## The marked evaluations -/

/-- Try number n of a Fiat-Shamir query: at fb t for n = 0, at the name fbw t (n - 1) else. Charged
to tk, with the further tokens us; the roots rt and the plain part pl are values. It gives the
blocks and the token of the chaining value. -/
def fbT (t : Tag) (n i : ℕ) (tk : Tok) (us : List Tok) (hd : List Bits → Bits → Head lam X)
    (hinj : ∀ vs, Function.Injective (hd vs)) (rt : List (Dig lam))
    (pl : PlainPart (shapeOf L t) (annOf L t)) : StT lam K L ((Fin K → Dig lam) × Tok) :=
  match n with
  | 0 => Step.marked (S := typedOracleFamily lam K L) (OracleName.fb t) tk us
      (fun v vs => (⟨i, hd vs v, rt, pl⟩ : FbIn lam L t))
      (fun vs _ _ h => hinj vs (congrArg FbIn.head h))
      fun bl tl => Step.pure ((bl : Fin K → Dig lam), tl)
  | n + 1 => Step.marked (S := typedOracleFamily lam K L) (OracleName.fbw t n) tk us
      (fun v vs => (⟨i, hd vs v, rt, pl⟩ : FbIn lam L t))
      (fun vs _ _ h => hinj vs (congrArg FbIn.head h))
      fun bl tl => Step.pure ((bl : Fin K → Dig lam), tl)

/-- the query to g in the joining round, charged to the last chaining value: the token of the slot
value -/
def gT (t : Tag) (i : ℕ) (tk : Tok) (rt : List (Dig lam)) (pl : PlainPart (shapeOf L t) (annOf L t)) :
    StT lam K L Tok :=
  Step.marked (S := typedOracleFamily lam K L) (OracleName.g t) tk [] (fun v _ => (⟨i, v, rt, pl⟩ : JoiningRoundQuery lam L t))
    (fun _ _ _ h => congrArg JoiningRoundQuery.ρ h) fun _ c => Step.pure c

/-- the slot's leaf of the request tree: the slot value, then the string rs; charged to the slot
value -/
def rleafT (c : Tok) (rs : Bits) : StT lam K L Tok :=
  Step.marked (S := typedOracleFamily lam K L) OracleName.rleaf c [] (fun v _ => (v ++ rs : Bits))
    (fun _ _ _ h => List.append_cancel_right h) fun _ d => Step.pure d

/-- an inner node of the request path, the path's digest on the left -/
def rnodeL (c : Tok) (s : Dig lam) : StT lam K L Tok :=
  Step.marked (S := typedOracleFamily lam K L) OracleName.rnode c [] (fun v _ => ((v, List.ofFn s) : Bits × Bits))
    (fun _ _ _ h => (Prod.mk.inj h).1) fun _ d => Step.pure d

/-- the same, the path's digest on the right -/
def rnodeR (s : Dig lam) (c : Tok) : StT lam K L Tok :=
  Step.marked (S := typedOracleFamily lam K L) OracleName.rnode c [] (fun v _ => ((List.ofFn s, v) : Bits × Bits))
    (fun _ _ _ h => (Prod.mk.inj h).2) fun _ d => Step.pure d

/-- From the token of a leaf's digest along given sibling digests to the token of the root: the twin
of climbM (Compile/MerkleM.lean). It also gives the tokens of the digests above the leaf, the root's
last. -/
def climbT : List (Dig lam) → ℕ → Tok → StT lam K L (Tok × List Tok)
  | [], _, c => .pure (c, [])
  | s :: ss, j, c =>
    (if j % 2 = 0 then rnodeL (K := K) (L := L) c s else rnodeR s c).bind fun u =>
      (climbT ss (j / 2) u).bind fun r => .pure (r.1, u :: r.2)

/-! ## The search for a nonce -/

/-- What a Fiat-Shamir query, with a test or without, returns: the plain part that was hashed, the
blocks and the token of the chaining value of the final try, the tokens of the chaining values of
the tries before it (the newest first). -/
structure Hit (lam K : ℕ) (P : Type) where
  pl : P
  bl : Fin K → Dig lam
  tl : Tok
  dead : List Tok

/-- try the nonces n, n + 1, ..: at most fuel of them; the first whose test bits are all 0. ask n:
try number n. The twin of searchO. -/
def searchT {C P : Type} (gr : GrW C P) (chal : (Fin K → Dig lam) → C)
    (ask : ℕ → P → StT lam K L ((Fin K → Dig lam) × Tok)) (α : P) :
    ℕ → ℕ → List Tok → StT lam K L (Option (Hit lam K P))
  | 0, _, _ => .pure none
  | fuel + 1, n, dd => (ask n (gr.put n α)).bind fun a =>
      if gr.ok (chal a.1) then .pure (some ⟨gr.put n α, a.1, a.2, dd⟩)
      else searchT gr chal ask α fuel (n + 1) (a.2 :: dd)

/-- a Fiat-Shamir query, with a test or without: the twin of fsO -/
def fsT {C P : Type} (gr : Option (GrW C P)) (cap : ℕ) (chal : (Fin K → Dig lam) → C)
    (ask : ℕ → P → StT lam K L ((Fin K → Dig lam) × Tok)) (α : P) :
    StT lam K L (Option (Hit lam K P)) :=
  match gr with
  | none => (ask 0 α).bind fun a => .pure (some ⟨α, a.1, a.2, []⟩)
  | some g => searchT g chal ask α (cap + 1) 0 []

/-- go on with what a Fiat-Shamir query has returned; or stop: the search of round i has run out.
The twin of onFs. -/
def onFsT {P β : Type} (i : ℕ) (k : Hit lam K P → StT lam K L (Res β)) :
    Option (Hit lam K P) → StT lam K L (Res β)
  | none => .pure (.ranOut i)
  | some p => k p

/-! ## The chain -/

/-- what is kept of the rounds s: the message as it was hashed, the trees over the shared component,
the trees over the slot's. The twin of Kept. -/
def KeptT (lam : ℕ) (L : BatchProtocolWithLeafBody I X) : Shape → Type
  | [] => Unit
  | r :: s => (r.Msg × List (TreeT lam L) × List (TreeT lam L)) × KeptT lam L s

/-- What the chain yields: the twin of OutP, and the chain's tokens. -/
structure OutT (lam : ℕ) (L : BatchProtocolWithLeafBody I X) (s : Shape) where
  /-- the verifier messages -/
  rho : Rho s
  kept : KeptT lam L s
  /-- the last phase -/
  ph : PhT
  /-- the token of the request root, if the joining round lies in these rounds -/
  rq : Option Tok
  /-- all tokens that the chain has made in these rounds, but for the leaves' -/
  toks : List Tok

def consT {r : Round} {s : Shape} (c : r.Chal)
    (kp : r.Msg × List (TreeT lam L) × List (TreeT lam L)) (rq : Option Tok) (ts : List Tok)
    (z : OutT lam L s) : OutT lam L (r :: s) :=
  ⟨(c, z.rho), (kp, z.kept), z.ph, rq.orElse fun _ => z.rq, ts ++ z.toks⟩

/-- **The chain as a token program**: the twin of chainO. ℓ: the free bits of a leaf's salt; pre: in
round number i a leaf's salt starts with pre i b (the first salt), b: is the tree over the slot's
component?; salt: the token of the first salt.
What else the start hangs on (values that the strategy sends in the clear) is in the letter pre. -/
def chainT (t : Tag) (cms : List (Dig lam)) (x : Option X) (ℓ : ℕ) (pre : ℕ → Bool → Bits → Bits)
    (salt : Tok) (cd : CoinsD lam L) (cap : ℕ → ℕ) :
    (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → ((p : OPos s) → OSym s p → Body L) →
    (PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) → ℕ → PhT → Strat s Unit →
    StT lam K L (Res (OutT lam L s))
  | [], _, _, _, _, _, ph, _ => .pure (.ok ⟨(), (), ph, none, []⟩)
  | _ :: s, (a, A), (w, W), embS, embP, i, ph, (m, k) =>
      match actT cms (x.map L.early) salt a.kind ph with
      | some (.one tk us hd inj true next) =>
          (treesT (K := K) ℓ [salt] (fun vs => pre i true (vs.headD [])) cd.pad w.posAtJ
            (fun p => embS (.inl p)) m.1 0 w.depthJ).bind fun TJ =>
          (fsT w.grJ (cap i) w.chal (fun n α => fbT (K := K) t n i tk us
              (fun vs v => (hd vs v).withLate (lateInstancePart L i x)) (inj (lateInstancePart L i x))
              (TJ.map TreeT.root) (embP (.inl (.inr α)))) (a.plain m.2).2).bind <| onFsT i fun q =>
            (chainT t cms x ℓ pre salt cd cap s A W (fun p => embS (.inr p))
              (fun z => embP (.inr z)) (i + 1) (next q.tl) (k (w.chal q.bl))).bind fun r =>
            .pure (r.map (consT (w.chal q.bl)
              ((m.1, a.plain.symm ((a.plain m.2).1, q.pl)), [], TJ) none (q.tl :: q.dead)))
      | some (.one tk us hd inj false next) =>
          (treesT (K := K) ℓ [salt] (fun vs => pre i false (vs.headD [])) cd.pad w.posAt0
            (fun p => embS (.inl p)) m.1 0 w.depth0).bind fun T0 =>
          (fsT w.gr0 (cap i) w.chal (fun n α => fbT (K := K) t n i tk us hd
              (fun vs a b h => inj none vs (congrArg (fun z => z.withLate none) h))
              (T0.map TreeT.root) (embP (.inl (.inl α)))) (a.plain m.2).1).bind <| onFsT i fun q =>
            (chainT t cms x ℓ pre salt cd cap s A W (fun p => embS (.inr p))
              (fun z => embP (.inr z)) (i + 1) (next q.tl) (k (w.chal q.bl))).bind fun r =>
            .pure (r.map (consT (w.chal q.bl)
              ((m.1, a.plain.symm (q.pl, (a.plain m.2).2)), T0, []) none (q.tl :: q.dead)))
      | some (.join tk) =>
          (treesT (K := K) ℓ [salt] (fun vs => pre i true (vs.headD [])) cd.pad w.posAtJ
            (fun p => embS (.inl p)) m.1 0 w.depthJ).bind fun TJ =>
          (treesT (K := K) ℓ [salt] (fun vs => pre i false (vs.headD [])) cd.pad w.posAt0
            (fun p => embS (.inl p)) m.1 0 w.depth0).bind fun T0 =>
          (gT (K := K) t i tk (TJ.map TreeT.root) (embP (.inl (.inr (a.plain m.2).2)))).bind
            fun c =>
          (rleafT (K := K) (L := L) c cd.rsalt).bind fun d =>
          (climbT (K := K) (L := L) cd.path cd.slot d).bind fun rq =>
          (fsT w.gr0 (cap i) w.chal (fun n α => fbT (K := K) t n i rq.1 []
              (fun _ v => .f4 cms v) (fun _ => f4_inj cms)
              (T0.map TreeT.root) (embP (.inl (.inl α)))) (a.plain m.2).1).bind <| onFsT i fun q =>
            (chainT t cms x ℓ pre salt cd cap s A W (fun p => embS (.inr p))
              (fun z => embP (.inr z)) (i + 1) (.shr q.tl c) (k (w.chal q.bl))).bind fun r =>
            .pure (r.map (consT (w.chal q.bl)
              ((m.1, a.plain.symm (q.pl, (a.plain m.2).2)), T0, TJ) (some rq.1)
              (c :: d :: (rq.2 ++ q.tl :: q.dead))))
      | none => .pure .noFormat

end OnBytes.TokenSide

#print axioms OnBytes.TokenSide.f1_inj
#print axioms OnBytes.TokenSide.f2_inj
#print axioms OnBytes.TokenSide.f3_inj
#print axioms OnBytes.TokenSide.f4_inj
#print axioms OnBytes.TokenSide.f5_inj
