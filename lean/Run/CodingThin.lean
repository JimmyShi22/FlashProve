-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/CodingThin.lean: the encoding of the queries of Run/CodingPage.lean (`theImpl`) in a form made
for the evaluator: the interface behind a function of `Unit`; and theorems that it writes the
strings of `theImpl` (`codeP_eq`) and reads out of the single oracle what `theImpl` reads
(`famC_eq`).

Definitions that compute; theorems.
The encoding of the queries writes each typed point (oracle, query, number of a block) of the
compiled scheme as a bit string for the single oracle.

Why: tried, with a trace in a round's instance: every definition of the encoding of the queries that
has the interface as a parameter {L}, though it stands in types alone, gets the interface built when
it is evaluated, with the list of all verifier messages of its rounds: hopeless at a round that
draws a field element. The generic tools for partial codes (type parameters only) do not. So here,
by the principle of Run/ThinDefs.lean and Run/CodingFnThin.lean: the texts of the writing side once
more, with the interface behind a function of `Unit`, an explicit first argument Lf, the types at Lf
().

Main names:
  `codeP Lf C o q j`: the string of a typed point. The spare oracle's points alone go through
    `theImpl` itself (behind the match: evaluated only if such a point is asked: a verifier asks
    none).
  `famCB`, `famCD`, `famC Lf C O`: the typed oracle functions that the encoding of the queries reads
    out of the single oracle O (into bytes): the blocks' strings by `codeP`, O once at each, into an
    array, then joined as `theImpl` joins them. No record of the encoding of the queries (`OracleCoding`)
    stands on this path (but for the spare oracle's points, above): tried: a record made of `codeP`,
    with `theImpl`'s inverse behind a λ, still got the list built when one of its fields was read.
  `leafPutP_eq`, `put162P_eq`, `fbPutP_eq`, `codeP_eq` (these four at Lf := fun _ => L),
    `pFirstP_put`, `pFirstP_parse`: each writes (and `pFirstP` reads) what its original does
    (`pLeaf`, `p162`, `pFb`, `theImpl`, `pFirst`).
  `famC_eq`, `famC_famM`; `famC_oBits`: at the format's oracle asked at `toBytes s` for a bit string
    s (Run/OracleBits.lean); all three at Lf := fun _ => L.

Limits: what the evaluator builds is a fact about a compiler and no theorem. The data C must
themselves be made without the interface as a value (the partial codes and "back" in it are closures
that a run calls).

Terms: lean/GLOSSARY.md.
-/
import Run.CodingPage
import Run.CodingPage160
import Run.FamThin

set_option autoImplicit false

namespace Run
open Rom Compile Compile.Batch Iop

variable {I X : Type} (Lf : Unit → BatchProtocol I X) {tg : Tag}

/-! ### A leaf -/

def leafSelP (q : LeafIn (Lf ())) : Option (SymAny (shapeOf (Lf ()) tg) × List Bool) :=
  match q.body with
  | some (.inr ⟨t', s⟩) =>
    (castTag (F := fun t => SymAny (shapeOf (Lf ()) t)) tg t' s).map fun s => (s, q.salt)
  | _ => none

def leafPutP (n : ℕ) (p : PCode (SymAny (shapeOf (Lf ()) tg))) (q : LeafIn (Lf ())) :
    Option (List Bool) :=
  (leafSelP Lf q).bind (pSalted pre33 n p).put

/-! ### A chain query of a round 1, 2, .. -/

def pTupP (D : ChainD (Lf ()) tg) : PCode (Tup (Lf ()) tg) :=
  pHalf.cons 8 pHalf_len fun _ =>
    PCode.pre mid32
      ((pBits 256).cons 256 (pBits_len 256) fun _ =>
        PCode.pre (bytesToBits (_root_.Fmt.u64n (162 + 65536 * D.label)))
          (pWord.cons 64 pWord_len fun i =>
            (D.rc i).ins (pKwc (D.kind i) (D.work i)) 64 64 (pKwc_len _ _) (D.hrc i)))

def toTupP (D : ChainD (Lf ()) tg) (K : ℕ) (x : FbIn 256 (Lf ()) tg × Fin (K + 1)) :
    Option (Tup (Lf ()) tg) :=
  match x.1.round, x.1.head with
  | i + 1, .f2 none ρ =>
      some (decide ((blockTo (decide (D.work (i + 1) ≠ 0)) K x.2).val % 2 = 1),
        ρ, i + 1,
        ((x.1.rt, x.1.plain), (blockTo (decide (D.work (i + 1) ≠ 0)) K x.2).val / 2))
  | _, _ => none

def put162P (D : ChainD (Lf ()) tg) (K : ℕ) (x : FbIn 256 (Lf ()) tg × Fin (K + 1)) :
    Option (List Bool) :=
  (toTupP Lf D K x).bind (pTupP Lf D).put

/-! ### Chain queries with a block -/

variable {K : ℕ}

def selKP (x : FbIn 256 (Lf ()) tg × Fin (K + 1)) : Option (FbIn 256 (Lf ()) tg) :=
  if x.2.val = K then some x.1 else none

def selRP (x : FbIn 256 (Lf ()) tg × Fin (K + 1)) :
    Option ((FbIn 256 (Lf ()) tg × Fin (K + 1)) ⊕ (FbIn 256 (Lf ()) tg × Fin (K + 1))) :=
  if x.1.round = 0 then some (.inl x) else some (.inr x)

def fb2PutP (C : PageC (Lf ()) K tg) :
    (FbIn 256 (Lf ()) tg × Fin (K + 1)) ⊕ (FbIn 256 (Lf ()) tg × Fin (K + 1)) → Option (List Bool)
  | .inl a => (selKP Lf a).bind C.first.put
  | .inr b => put162P Lf C.chain K b

def fbPutP (C : PageC (Lf ()) K tg) (x : FbIn 256 (Lf ()) tg × Fin (K + 1)) : Option (List Bool) :=
  (selRP Lf x).bind (fb2PutP Lf C)

/-! ### All points -/

/-- The format's string, if there is one; else the byte 2 and then the string of a total code. -/
def orB {A : Type} (back : StrCode A) (s : Option (List Bool)) (a : A) : List Bool :=
  match s with
  | some s => s
  | none => bitsOfByte 2 ++ back.put a

/-- The string of a typed point. -/
def codeP (C : PageC (Lf ()) K tg) :
    (o : Batch.OracleName) → Batch.domOf 256 (Lf ()) o → Fin (blk K o) → List Bool
  | .leaf, q, _ => orB C.back (leafPutP Lf C.saltBits C.leafP q) (.inl (.inl q))
  | .node, q, _ => orB C.back ((pNode C.cfg).put q) (.inl (.inr (.inl q)))
  | .rleaf, q, _ => bitsOfByte 2 ++ C.back.put (.inl (.inr (.inr (.inl q))))
  | .rnode, q, _ => bitsOfByte 2 ++ C.back.put (.inl (.inr (.inr (.inr (.inl q)))))
  | .fb t', q, j =>
    orB C.back
      ((castTag (F := fun t => FbIn 256 (Lf ()) t) tg t' q).bind fun q' => fbPutP Lf C (q', j))
      (.inl (.inr (.inr (.inr (.inr (.inl ⟨t', q, j⟩))))))
  | .g t, q, _ => bitsOfByte 2 ++ C.back.put (.inl (.inr (.inr (.inr (.inr (.inr ⟨t, q⟩))))))
  | .ann, _, j => j.elim0
  | .other, s, j => (theImpl (L := Lf ()) C).code .other s j
  | .fbw t k, q, j => bitsOfByte 2 ++ C.back.put (.inr ⟨t, k, q, j⟩)

variable {L : BatchProtocol I X}

theorem leafSelP_eq (q : LeafIn L) : leafSelP (tg := tg) (fun _ => L) q = leafSel q := by
  obtain ⟨body, salt⟩ := q
  rcases body with _ | (_ | ⟨t, s⟩) <;> rfl

theorem leafPutP_eq (n : ℕ) (p : PCode (SymAny (shapeOf L tg))) (q : LeafIn L) :
    leafPutP (fun _ => L) n p q = (pLeaf n p).put q := by
  show (leafSelP (fun _ => L) q).bind (pSalted pre33 n p).put =
    (leafSel q).bind (pSalted pre33 n p).put
  rw [leafSelP_eq]

theorem put162P_eq (D : ChainD L tg) (K : ℕ) (x : FbIn 256 L tg × Fin (K + 1)) :
    put162P (fun _ => L) D K x = (p162 D K).put x := rfl

theorem fbPutP_eq (C : PageC L K tg) (x : FbIn 256 L tg × Fin (K + 1)) :
    fbPutP (fun _ => L) C x = (pFb C).put x := by
  show (selR x).bind (fb2PutP (fun _ => L) C) = (selR x).bind (pFb2 C).put
  congr 1
  funext y
  rcases y with y | y <;> rfl

/-- At the constant function Lf := fun _ => L, `codeP` is the code of `theImpl`. -/
theorem codeP_eq (C : PageC L K tg) :
    ∀ (o : Batch.OracleName) (q : Batch.domOf 256 L o) (j : Fin (blk K o)),
      codeP (fun _ => L) C o q j = (theImpl C).code o q j
  | .leaf, q, _ => by
      show orB C.back (leafPutP (fun _ => L) C.saltBits C.leafP q) _ = _
      rw [leafPutP_eq]
      rfl
  | .node, _, _ => rfl
  | .rleaf, _, _ => rfl
  | .rnode, _, _ => rfl
  | .fb t', q, j => by
      show orB C.back
          ((castTag (F := fun t => FbIn 256 L t) tg t' q).bind fun q' =>
            fbPutP (fun _ => L) C (q', j)) _ = _
      simp only [fbPutP_eq]
      have e : (pAll C).put (.inl (.inr (.inr (.inr (.inr (.inl ⟨t', q, j⟩)))))) =
          (castTag (F := fun t => FbIn 256 L t) tg t' q).bind fun q' => (pFb C).put (q', j) := by
        show ((castTag (F := fun t => FbIn 256 L t) tg t' q).map fun q =>
              (Sum.inr (Sum.inr (q, j)) :
                LeafIn L ⊕ ((List Bool × List Bool) ⊕ (FbIn 256 L tg × Fin (K + 1))))).bind
            (p3 C).put = _
        cases castTag (F := fun t => FbIn 256 L t) tg t' q <;> rfl
      rw [← e]
      rfl
  | .g _, _, _ => rfl
  | .ann, _, j => j.elim0
  | .other, _, _ => rfl
  | .fbw _ _, _, _ => rfl

/-! ### The typed oracle functions read out of the single oracle -/

/-- The blocks of an answer, as bytes: data. -/
def famCB (C : PageC (Lf ()) K tg) (O : List Bool → ByteArray)
    (o : Batch.OracleName) (q : Batch.domOf 256 (Lf ()) o) : Array ByteArray :=
  Array.ofFn (n := blk K o) fun j => O (codeP Lf C o q j)

/-- The bytes as a typed answer. -/
def famCD (K : ℕ) (o : Batch.OracleName) (a : Array ByteArray) : Batch.rngOf 256 K o :=
  (rngEquiv 256 K o).symm fun j => digS (a.getD j.val ByteArray.empty)

/-- The typed oracle functions that the encoding of the queries reads out of the single oracle, in
the form made for the evaluator. -/
def famC (C : PageC (Lf ()) K tg) (O : List Bool → ByteArray) : Fam (spec 256 K (Lf ())) :=
  fun o q => famCD K o (famCB Lf C O o q)

/-- At the constant function Lf := fun _ => L, `famC` is `readBlocks` (Rom/Prefix.lean) at
`theImpl C` and the single oracle s ↦ bytesToDig (O s). -/
theorem famC_eq (C : PageC L K tg) (O : List Bool → ByteArray) :
    famC (fun _ => L) C O = readBlocks (theImpl C) (fun _ s => bytesToDig (O s)) := by
  funext o q
  show (rngEquiv 256 K o).symm (fun j =>
      digS ((Array.ofFn (n := blk K o) fun j => O (codeP (fun _ => L) C o q j)).getD
          j.val ByteArray.empty)) =
    (rngEquiv 256 K o).symm (fun j => bytesToDig (O ((theImpl C).code o q j)))
  congr 1
  funext j
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dif_pos j.isLt, codeP_eq]
  exact digS_eq _

/-- The same against the generic family of Run/FamThin.lean at `theImpl C` itself. -/
theorem famC_famM (C : PageC L K tg) (O : List Bool → ByteArray) :
    famC (fun _ => L) C O = famM (fun _ => L) K (theImpl C) O :=
  (famC_eq C O).trans (famM_eq K (theImpl C) O).symm

theorem famC_oBits (C : PageC L K tg) : famC (fun _ => L) C oBy = readBlocks (theImpl C) oBits :=
  famC_eq C oBy

/-! ### The first chain query -/

section
variable (p0 : PlainPart (shapeOf (Lf ()) tg) (annOf (Lf ()) tg))
  (isP0 : PlainPart (shapeOf (Lf ()) tg) (annOf (Lf ()) tg) → Bool)

def fbSel0P (q : FbIn 256 (Lf ()) tg) : Option (Dig 256 × Option X × List Bool) :=
  match q.round, q.head, q.rt with
  | 0, .f1 [pd] x salt, none => if isP0 q.plain = true then some (pd, x, salt) else none
  | _, _, _ => none

def fbMk0P (a : Dig 256 × Option X × List Bool) : FbIn 256 (Lf ()) tg :=
  ⟨0, .f1 [a.1] a.2.1 a.2.2, none, p0⟩

theorem fbSel0P_eq (q : FbIn 256 (Lf ()) tg) : fbSel0P Lf isP0 q = fbSel0 (L := Lf ()) isP0 q := rfl

variable (hp : ∀ p, isP0 p = true ↔ p = p0) (lab : Nat) (stm : Option X → Option ByteArray)
  (unstm : ByteArray → Option (Option X)) (h1 : ∀ x b, stm x = some b → unstm b = some x)
  (h2 : ∀ b x, unstm b = some x → stm x = some b)

/-- The partial code of the first chain query, in the form made for the evaluator. -/
def pFirstP : PCode (FbIn 256 (Lf ()) tg) where
  put := fun q => (fbSel0P Lf isP0 q).bind (pFirst0 lab stm unstm h1 h2).put
  parse := fun s => ((pFirst0 lab stm unstm h1 h2).parse s).map (fbMk0P Lf p0)
  parse_put := (pFirst (L := Lf ()) p0 isP0 hp lab stm unstm h1 h2).parse_put
  put_parse := (pFirst (L := Lf ()) p0 isP0 hp lab stm unstm h1 h2).put_parse

theorem pFirstP_put (q : FbIn 256 (Lf ()) tg) :
    (pFirstP Lf p0 isP0 hp lab stm unstm h1 h2).put q =
      (pFirst (L := Lf ()) p0 isP0 hp lab stm unstm h1 h2).put q := rfl

theorem pFirstP_parse (s : List Bool) :
    (pFirstP Lf p0 isP0 hp lab stm unstm h1 h2).parse s =
      (pFirst (L := Lf ()) p0 isP0 hp lab stm unstm h1 h2).parse s := rfl

end

end Run
