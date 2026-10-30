-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PageQ.lean: the encoding of the typed queries into the single oracle's strings as a function of
a chain's description in the programs' format; and the typed oracle functions that it reads out of
the single oracle.

The compiled verifier asks typed oracles (`OracleName`, Compile/Batch/Oracles.lean), among them those for
chain queries and for the leaves and nodes of hash trees. To run it over one hash function, every
typed query, with the number of a block of its answer, is written as a bit string by a one-to-one
encoding with a parser (a coding: `Rom.OracleCoding`, Rom/Family.lean). Run/CodingPage.lean builds such an
encoding from a record of data, `PageC`.
This file gives all the data of that record (`PageC`, Run/CodingPage.lean) for the generic
construction. Every piece is made without the interface as a value. From a description the generic
construction (Run/PlanQS.lean) makes a protocol, its wiring and run functions. A description is a
value `S : Fmt.Spec` (Fmt/Rules8.lean). C is a choice of challenge types (`CK`,
Run/PlanQTypes.lean), and dec is a decision.
Definitions that compute, with their laws (six theorems); one theorem more (`gQ_eq`).

Main names:
  `serPl`, `serG`, `serVec`, `serSymL`, `serPBL`: serialisers of a plain part, of a plain part with
    a nonce (none where the work is 0), of a column, of a symbol with its position, of a plain part
    of some round. `serQ` is the record of serialisers (`SerP`, Run/SerThin.lean) made from them;
    with it Run/SerThin.lean's total code (`backP`) is `pageQ`'s field `back`.
  `rcQ`, `chainQ`: the chain's data: the description's label, kinds and work, and the code of a
    round's message; at round 0 there is nothing; at round i + 1 the code is Run/PageQChain.lean's
    `rcL` at i, under the trivial round (`s0`, Run/PlanQS.lean).
  `stmQ`, `unstmQ`, `firstQ`: the first chain query (Run/CodingThin.lean: `pFirstP`) at the
    description's label and statement. The typed query holds the statement () (some (): the
    interface's instances have one value). The statement's bytes are the description's constant.
  `OKQ S`: a test, to be evaluated at a closed description: the words with the label and with the
    trees' numbers have the calls' numbers (`t162`, `t164`, Run/CodingTag.lean) in their low 16
    bits; the configuration's digest has 32 bytes; a salt is a whole number of words (its number of
    words stands in a leaf's label: the format page, in an edition that is not the one that ships).
  `pageQ S C dec K h`, for `h : OKQ S = true`: the record of data (`PageC`).
  `gQ S C dec K h`: Run/CodingThin.lean's `famC` at it and at the format's oracle asked at `toBytes
    s` for a bit string s (`oBy`, Run/FamThin.lean; `toBytes`: Run/OracleBits.lean).
  `gQ_eq`: `gQ S C dec K h = readBlocks (theImpl (pageQ S C dec K h)) oBits`: the family read out
    of a single oracle with all blocks asked (`Rom.readBlocks`, Rom/Prefix.lean), at an encoding
    with its inverse and both laws.

Notation:
  `K`: the number of blocks of verifier message in a chain oracle's answer (Run/CodingFn.lean,
    `rngOf` in Compile/Batch/Oracles.lean);
  `.test`, `.link`, `.onl`: which compiled protocol: Test, Link or Batch (`Tag`,
    Compile/Oracles.lean);
  `7` (in `chainQ`): the number of the kind `.nothing` (`Kind.num`, Fmt/Plan.lean);
  `View`: the structure on which a protocol's decision is written (Fmt/View.lean).

Limits: this file does not say that `pageQ`'s strings are those of Run/PlanQS.lean's spellings
`PDS` (Run/CodingAgree.lean: `PageFit`): not proved here. What the evaluator builds is a fact about
a compiler. Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import Run.PageQChain
import Run.CodingThin
import Run.SerThin

set_option autoImplicit false

namespace Run.PQ
open Rom Iop Compile Compile.Batch
open _root_.Fmt (Item)

/-! ### Serialisers, for the total code behind the escape -/

def serW : Ser UInt64 :=
  Ser.ofEquiv ⟨UInt64.toFin, UInt64.ofFin, fun _ => rfl, fun _ => rfl⟩ (Ser.fin UInt64.size)

def serX : Ser _root_.Fmt.Ext := Ser.prod serW (Ser.prod serW serW)

def serPl : (l : List Item) → Ser (PlainOf l)
  | [] => Ser.unit
  | .root :: l => serPl l
  | .f :: l => Ser.prod serW (serPl l)
  | .word :: l => Ser.prod serW (serPl l)
  | .e :: l => Ser.prod serX (serPl l)
  | .answer :: l => Ser.prod serX (serPl l)

def serG {P : Type} (s : Ser P) : (w : ℕ) → Ser (GPlain ℕ w P)
  | 0 => s
  | _ + 1 => Ser.prod s Ser.nat

def serVec : (W : ℕ) → Ser (Fin W → UInt64)
  | 0 =>
    Ser.ofEquiv
      ⟨fun _ => (), fun _ i => i.elim0, fun _ => funext fun i => i.elim0, fun _ => rfl⟩ Ser.unit
  | W + 1 =>
    Ser.ofEquiv (Fin.consEquiv fun _ : Fin (W + 1) => UInt64).symm (Ser.prod serW (serVec W))

def serNo (α : Empty → Type) : Ser (Σ p : Empty, α p) :=
  Ser.ofEquiv ⟨fun x => x.1, fun e => e.elim, fun x => x.1.elim, fun e => e.elim⟩ Ser.empty

def serSymL (C : CK) : (ds : List RD) → Ser (SymAny (uL C ds))
  | [] => serNo _
  | d :: ds =>
    Ser.ofEquiv
      (Equiv.sumSigmaDistrib (α := Fin (posN d.tree)) (β := OPos (uL C ds)) (OSym (uL C (d :: ds))))
      (Ser.sum (Ser.sigma (Ser.fin (posN d.tree)) fun _ => serVec (colW d.tree)) (serSymL C ds))

def serPBL (C : CK) : (ds : List RD) → Ser (PBL C ds)
  | [] => Ser.empty
  | d :: ds => Ser.sum (Ser.sum Ser.unit (serG (serPl d.items) d.entry.work)) (serPBL C ds)

variable (S : _root_.Fmt.Spec) (C : CK) (dec : View → Bool)

/-- the interface behind a function of Unit -/
def LfQ : Unit → BatchProtocol Unit Unit := fun _ => LbS C (rds S) dec

def symQ : ∀ t : Tag, Ser (SymAny (Compile.Batch.shapeOf (LfQ S C dec ()) t))
  | .onl =>
    Ser.ofEquiv
      (Equiv.sumSigmaDistrib (α := Empty) (β := OPos (uL C (rds S)))
        (OSym (Twin.up (SOf C (rds S)))))
      (Ser.sum (serNo _) (serSymL C (rds S)))
  | .link => serNo _
  | .test => serNo _

def pbQ :
    ∀ t : Tag,
      Ser (PlainPart (Compile.Batch.shapeOf (LfQ S C dec ()) t) (Compile.Batch.annOf (LfQ S C dec ()) t))
  | .onl => Ser.sum (Ser.sum Ser.unit Ser.unit) (serPBL C (rds S))
  | .link => Ser.empty
  | .test => Ser.empty

/-- The serialisers. -/
def serQ : SerP (LfQ S C dec) := ⟨Ser.unit, Ser.unit, symQ S C dec, pbQ S C dec⟩

/-! ### The chain, the leaves, the first query -/

abbrev PBQ : Type :=
  PlainPart (Compile.Batch.shapeOf (LfQ S C dec ()) .onl) (Compile.Batch.annOf (LfQ S C dec ()) .onl)

/-- A round's message is nothing at round 0; at round i + 1 it is that of the description's round
with the number i, under the trivial round. -/
def rcQ : ℕ → PCode (Option (Dig 256) × PBQ S C dec)
  | 0 => PCode.empty _
  | i + 1 => inR (rcL C (rds S) i)

theorem rcQ_ge :
    ∀ (i : ℕ) (y : Option (Dig 256) × PBQ S C dec) (s : List Bool),
      (rcQ S C dec i).put y = some s → 64 ≤ s.length
  | 0, _, _, h => by cases h
  | i + 1, y, s, h => by
      obtain ⟨y1, h1⟩ := inR_put _ y s h
      exact rcL_ge C (rds S) i y1 s h1

/-- The chain's data. -/
def chainQ : ChainD (LfQ S C dec ()) .onl where
  label := S.label
  kind := fun i => if i = 0 then 7 else ((S.rounds[i - 1]?).map (·.kind.num)).getD 7
  work := fun i => if i = 0 then 0 else ((S.rounds[i - 1]?).map (·.entry.work)).getD 0
  rc := rcQ S C dec
  hrc := rcQ_ge S C dec

/-- the leaves' code, under the trivial round -/
def leafQ : PCode (SymAny (Compile.Batch.shapeOf (LfQ S C dec ()) .onl)) :=
  ((PCode.empty (Σ p : Empty, OSym (Twin.up (SOf C (rds S))) (.inl p))).sumF
      (leafCL C S.plan.salt (rds S))).congr
    (Equiv.sumSigmaDistrib (α := Empty) (β := OPos (uL C (rds S)))
      (OSym (Twin.up (SOf C (rds S))))).symm

theorem leafQ_tag (h : tagsOK S.plan.salt (rds S) = true)
    (y : SymAny (Compile.Batch.shapeOf (LfQ S C dec ()) .onl))
    (m : List Bool) (hm : (leafQ S C dec).put y = some m) :
    16 ≤ m.length ∧ m.take 16 = t164 := by
  rcases hz : (Equiv.sumSigmaDistrib
      (α := Empty) (β := OPos (uL C (rds S))) (OSym (Twin.up (SOf C (rds S))))) y with a | b
  · exact a.1.elim
  · have h0 : ((PCode.empty (Σ p : Empty, OSym (Twin.up (SOf C (rds S))) (.inl p))).sumF
      (leafCL C S.plan.salt (rds S))).put
        ((Equiv.sumSigmaDistrib (α := Empty) (β := OPos (uL C (rds S)))
              (OSym (Twin.up (SOf C (rds S))))) y) = some m := hm
    rw [hz] at h0
    exact leafCL_tag C S.plan.salt (rds S) h b m (PCode.sumF_inr _ _ b m h0)

/-- the statement's bytes: the typed query holds no statement but () -/
def stmQ : Option Unit → Option ByteArray
  | some _ => some S.statement
  | none => none

def unstmQ (b : ByteArray) : Option (Option Unit) :=
  if b = S.statement then some (some ()) else none

theorem unstm_stmQ (x : Option Unit) (b : ByteArray) (h : stmQ S x = some b) :
    unstmQ S b = some x := by
  cases x with
  | none => cases h
  | some _ =>
      rw [← Option.some.inj h]
      exact if_pos rfl

theorem stm_unstmQ (b : ByteArray) (x : Option Unit) (h : unstmQ S b = some x) :
    stmQ S x = some b := by
  unfold unstmQ at h
  by_cases hb : b = S.statement
  · rw [if_pos hb] at h
    rw [← Option.some.inj h, hb]
    rfl
  · rw [if_neg hb] at h
    cases h

/-- the plain part of the trivial round 0 -/
def p0Q : PBQ S C dec := .inl (.inr ())

def isP0Q : PBQ S C dec → Bool
  | .inl (.inr ()) => true
  | _ => false

theorem isP0Q_iff (p : PBQ S C dec) : isP0Q S C dec p = true ↔ p = p0Q S C dec := by
  rcases p with (_ | ⟨⟩) | _
  · exact ⟨fun h => (by cases h), fun h => (by cases h)⟩
  · exact ⟨fun _ => rfl, fun _ => rfl⟩
  · exact ⟨fun h => (by cases h), fun h => (by cases h)⟩

/-- The first chain query. -/
def firstQ : PCode (FbIn 256 (LfQ S C dec ()) .onl) :=
  pFirstP (LfQ S C dec) (p0Q S C dec) (isP0Q S C dec) (isP0Q_iff S C dec) S.label (stmQ S)
    (unstmQ S) (unstm_stmQ S) (stm_unstmQ S)

theorem firstQ_hdr (q : FbIn 256 (LfQ S C dec ()) .onl)
    (s : List Bool) (h : (firstQ S C dec).put q = some s) : ∃ r, s = hdr160 S.label ++ r :=
  pFirst_hdr (L := LfQ S C dec ()) (p0Q S C dec) (isP0Q S C dec) (isP0Q_iff S C dec) S.label
    (stmQ S) (unstmQ S) (unstm_stmQ S) (stm_unstmQ S) q s h

/-! ### The assembly -/

/-- A test, to be evaluated at a closed description. -/
def OKQ : Bool :=
  decide ((bytesToBits (_root_.Fmt.u64n (162 + 65536 * S.label))).take 16 = t162) &&
    tagsOK S.plan.salt (rds S) && decide (S.cfg.size = 32) && decide (S.plan.salt % 8 = 0)

/-- All data of the coding, from the description. -/
def pageQ (K : ℕ) (h : OKQ S = true) : PageC (LfQ S C dec ()) K .onl where
  cfg := S.cfg
  hcfg := by
    unfold OKQ at h
    simp only [Bool.and_eq_true, decide_eq_true_iff] at h
    exact h.1.2
  chain := chainQ S C dec
  chainTag := by
    unfold OKQ at h
    simp only [Bool.and_eq_true, decide_eq_true_iff] at h
    exact h.1.1.1
  first := firstQ S C dec
  firstTag := fun q s hq => by
    obtain ⟨r, rfl⟩ := firstQ_hdr S C dec q s hq
    exact tag16_hdr 0 160 0 S.label _root_.Fmt.zero32 rfl r
  firstHd := fun q s hq e he => by
    obtain ⟨r, rfl⟩ := firstQ_hdr S C dec q s hq
    exact hdr_not_prefix e 0 he 160 0 S.label _root_.Fmt.zero32 r
  saltBits := 8 * S.plan.salt
  leafP := leafQ S C dec
  leafTag := leafQ_tag S C dec (by
    unfold OKQ at h
    simp only [Bool.and_eq_true, decide_eq_true_iff] at h
    exact h.1.1.2)
  back := backP (LfQ S C dec) (serQ S C dec) K

/-- The typed oracle functions that the coding reads out of the single oracle. -/
def gQ (K : ℕ) (h : OKQ S = true) : Fam (spec 256 K (LfQ S C dec ())) :=
  famC (LfQ S C dec) (pageQ S C dec K h) oBy

theorem gQ_eq (K : ℕ) (h : OKQ S = true) :
    gQ S C dec K h = readBlocks (theImpl (pageQ S C dec K h)) oBits :=
  famC_oBits (L := LbS C (rds S) dec) (pageQ S C dec K h)

end Run.PQ
