-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/PV/LinkPut.lean: THE ENTRY FILE's CHAIN QUERIES' STRINGS WITH CODE: the function that the
  code `linkAt` (OnBytes/TypedOracleCompiler/Slice/ArmLinkCode.lean:67) writes, without its parser and with a
  WRITTEN way back from the two tables' answers' digests.
WHY. linkAt has no code: its first query's code lf0 reads the answers back out of the list of
  digests by choice (backOf: OnBytes/TypedOracleCompiler/Run/LinkFirstAns.lean:51-54; selLA :92-100). A run reads
  «put» alone.
  un1 d          the three words of a digest, if d is the digest of an element of the field (digE:
    OnBytes/Flat/RecordCode.lean:73): else nothing
  unA v s l      a list of 2 · 2^v · s digests as two lists of triples
  selLAC un      selLA's text with «un l» in the place of «backOf (pairA cA) l» and the two «tr»
  linkPutC un    the strings: at round 0, at the last block: first0E's string at selLAC; at a later
    round: roundsAlong (laterM …) (e162 …)
  selLAC_eq · **linkPutC_eq**: under hun (un IS the way back by choice, followed by tr) it IS
    (linkAt …).pL.put.
OWED: hun at un := unA v s, cA := codeA, tr := trAns. NOTHING HAS RUN. No soundness.


-/
import OnBytes.TypedOracleCompiler.Slice.ArmLinkCode
import OnBytes.Flat.RecordCode
import OnBytes.Flat.LinkSib

set_option autoImplicit false

namespace W4M
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Slice
open TypedOracleCompiler.Run.Apart TypedOracleCompiler.Run.PageG TypedOracleCompiler.Run.SeedPage TypedOracleCompiler.Run.LinkOf
open TypedOracleCompiler.Run.EntryFb TypedOracleCompiler.Run.EntryPage TypedOracleCompiler.Slice.EntryFill
open TypedOracleCompiler.Run.PlainIn TypedOracleCompiler.Run.SeamAt TypedOracleCompiler.Run.EntryFirst
open TypedOracleCompiler.Run.LinkAlong TypedOracleCompiler.Run.LinkAlongM TypedOracleCompiler.Run.LinkFirstAns
open TypedOracleCompiler.Run.ArmRounds TypedOracleCompiler.Run.ArmDirect TypedOracleCompiler.Slice.ArmRead
open TypedOracleCompiler.Run.FirstAnswers (T3)
open TypedOracleCompiler.Run.PQ (XD)
open OnBytes.Slice (seedEntry toE ofE)
open TypedOracleCompiler.Slice.ArmLinkCode (linkAt)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run

/-! ## The written way back -/

/-- The word in the 64 places of a digest from off on, lowest bit first. -/
def wordAt (d : Dig 256) (off : ℕ) : UInt64 :=
  UInt64.ofNat ((List.range 64).foldl (fun acc j =>
    if h : off + j < 256 then (if d ⟨off + j, h⟩ then acc + 2 ^ j else acc) else acc) 0)

/-- The three words of a digest, if it is the digest of an element of the field. -/
def un1 (d : Dig 256) : Option T3 :=
  let x := toE (wordAt d 0, wordAt d 64, wordAt d 128)
  if (List.finRange 256).all (fun i => OnBytes.Flat.digE x i == d i) then some (ofE x) else none

/-- Two tables' answers' digests, in a row, as two lists of triples. -/
def unA (v s : ℕ) (l : List (Dig 256)) : Option (List T3 × List T3) :=
  if l.length = 2 ^ v * s + 2 ^ v * s then
    (l.mapM un1).map fun ts => (ts.take (2 ^ v * s), ts.drop (2 ^ v * s))
  else none

/-! ## The first query -/

section First
variable {I X : Type} (L : BatchProtocolWithLeafBody I X) (t : Tag) (isP0 : PlainPart (shapeOf L t) (annOf L t) → Bool) (pd : Dig
                                 256)
  (un : List (Dig 256) → Option (List T3 × List T3))

/-- Of a query of the form: (pd, roots and answers as triples, salt). -/
def selLAC (q : FbIn 256 L t) : Option (Dig 256 × Option (Dig 256 × YE) × List Bool) :=
  match q.round, q.head, q.rt with
  | 0, .f1 (cm :: cm' :: l) none salt, [] =>
      match un l with
      | some aa =>
          if isP0 q.plain = true then some (pd, some (cm, (aa.1, (cm', aa.2))), salt)
          else none
      | none => none
  | _, _, _ => none

variable {An : Type} (cA : An → List (Dig 256)) (tr : An → List T3)

/-- It is selLA, where un is the way back by choice, followed by tr. -/
theorem selLAC_eq (hun : ∀ l, un l = (backOf (pairA cA) l).map fun aa => (tr aa.1, tr aa.2))
    (q : FbIn 256 L t) : selLAC L t isP0 pd un q = selLA L t isP0 pd cA tr q := by
  obtain ⟨round, head, rt, plain⟩ := q
  unfold selLAC selLA
  split
  · rename_i cm cm' l salt e1 e2 e3
    have e1' : round = 0 := e1
    have e2' : head = .f1 (cm :: cm' :: l) none salt := e2
    have e3' : rt = [] := e3
    subst e1' e2' e3'
    rw [hun]
    show _ = (match backOf (pairA cA) l with
      | some aa =>
          if isP0 plain = true then some (pd, some (cm, (tr aa.1, (cm', tr aa.2))), salt) else none
      | none => none)
    cases backOf (pairA cA) l <;> rfl
  · rename_i hno
    split
    · rename_i cm cm' l salt e1 e2 e3
      exact (hno cm cm' l salt e1 e2 e3).elim
    · rfl

end First

/-! ## All chain queries of the entry file -/

variable {lg s : ℕ} (D : XD) (d₁ : Sd1 lg s) (cfg : ByteArray) (hcfg : cfg.size = 32)
  (pd : Dig 256) (rest1 : ByteArray)
  {I2 X2 : Type} (L2 : BatchProtocolWithLeafBody I2 X2)
  (pbF : PlainPart (shapeOf L2 .link) (annOf L2 .link) ≃
    PlainPart (shapeOf (Ls D d₁) .link) (annOf (Ls D d₁) .link))
  (isPL : PlainPart (shapeOf L2 .link) (annOf L2 .link) → Bool)
  (un : List (Dig 256) → Option (List T3 × List T3)) (K : ℕ)

/-- **THE STRINGS.** -/
def linkPutC (x : FbIn 256 L2 .link × Fin (K + 1)) : Option (List Bool) :=
  if x.1.round = 0 then
    (selT K x).bind fun q => (selLAC L2 .link isPL pd un q).bind (first0E
        OnBytes.Params.labelLink).put
  else (roundsAlong (laterM (Ls D d₁) L2 pbF) (e162 (pinsE D d₁ cfg hcfg pd rest1) K)).put x

variable (hpL : ∀ p, isPL p = true ↔
    p = pbF.symm (p0E D (earlyTwo (A := List T3 × List T3) d₁) (seedEntry lg s)))
  {An : Type} (cA : An → List (Dig 256)) (tr : An → List T3) (hinj : Function.Injective cA)
  (hlen : ∀ a a', (cA a).length = (cA a').length) (htr : Function.Injective tr)

/-- **THE EQUATION: IT IS WHAT linkAt WRITES**, where un is the way back by choice,
  followed by tr. -/
theorem linkPutC_eq (hun : ∀ l, un l = (backOf (pairA cA) l).map fun aa => (tr aa.1, tr aa.2)) :
    linkPutC D d₁ cfg hcfg pd rest1 L2 pbF isPL un K =
      (linkAt D d₁ cfg hcfg pd rest1 L2 pbF isPL hpL cA tr hinj hlen htr K).pL.put := by
  funext x
  unfold linkPutC
  by_cases h0 : x.1.round = 0
  · rw [if_pos h0]
    refine Eq.trans ?_ (split_true _ _ (fun x : FbIn 256 L2 .link × Fin (K + 1) => decide (x.1.round
        = 0)) _ x
      (decide_eq_true h0)).symm
    show _ = (selT K x).bind fun q => (selLA L2 .link isPL pd cA tr q).bind _
    congr 1
    funext q
    rw [selLAC_eq L2 .link isPL pd un cA tr hun]
  · rw [if_neg h0]
    exact (split_false _ _ (fun x : FbIn 256 L2 .link × Fin (K + 1) => decide (x.1.round = 0)) _ x
      (decide_eq_false h0)).symm

end W4M

#print axioms W4M.selLAC_eq
#print axioms W4M.linkPutC_eq
