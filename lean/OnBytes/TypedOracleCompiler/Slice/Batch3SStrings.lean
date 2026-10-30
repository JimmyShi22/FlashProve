-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/Batch3SStrings.lean: THE BATCH's SKELETON WITH BODIES: MAKERS "WRITTEN ROUNDS
BEFORE A SKELETON TAIL" FOR WHAT THE EVALUABLE VERIFIER TAKES BESIDE THE PROTOCOL AND ITS WIRING:
the symbols' way into a leaf's body and back, the openings, the plain parts. BESIDE
Plain3Strings.lean (its like for the batch is not in this library), which stands.
The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on
definitions of Compile/.
WHY. The makers embApp | prjApp | embSeam | embFront, BD.embS | prjS | back of Plain3Strings.lean's
like for the batch (not in this library) have a Shape t as a
parameter: for a RUN that forces "the verifier messages are finitely many" as a datum
(Slice/Batch3S.lean's head). A file of this project that is not in this library and another such
file's encZ
| opZ write the same things
by hand, for numbers.
HERE: the text is that like's: where that has a Shape t, this has a skeleton tail T : List RS;
every maker RECURSES ON THE LIST OF ROUNDS' DATA. So "what is written is read back" is an induction
along that list, and no question of a symbol's type at depth arises.
GENERAL IN THE BODY. B is any type, and how a written round's symbols are written is a parameter,
tree list by tree list: eT : EncT B, pT : PrjT B. (Fmt.Shape, a tree's form, is numbers: it is not
Iop's Shape.) At B := List Bool, eT := "(ownT salt ts p a).getD []", pT := rdT salt these are
StringsList.lean's bodies: a file of this project that is not in this library, which imports that
  file.
  EncT B, PrjT B, BackOn eT pT ds      the two ways; "what is written at a tree of a round of ds is
    read back"
  embHS | prjHS | backHS               one skeleton round with ways of its own, before a skeleton
    tail (the front)
  embSeamS | prjSeamS | backSeamS      a seam before a skeleton tail: it has no position
  embAS | prjAS | backAS               written rounds before a skeleton tail;   embAS_poL |
    embAS_poR would need a symbol carried along poL | poR: NOT SAID: the recursion makes them
    needless
  embLS | prjLS | backLS               written rounds with nothing behind them (the third stretch:
    Twin.up (SL C ds), not … ++ [])
  relHS | relSeamS | relAS | relLS      two ways of writing, into bodies of two types: a relation
    that holds between what they write at each round's trees (RelOn) and in the tail holds
    everywhere: so "the body is the bits of …" is carried from a tree to the whole without a second
    recursion
  opTS look n ts                       the openings of one round's trees from a table "tree number,
    the tree's form, place ↦ opening": the round's first tree has the number n
  opHS, opSeamS, opAS, opLS            openings: as above; the trees are counted on along the rounds
  plAS, plLS                           plain parts: round i of the stretch has pl i d;   plF_plAS |
    plS_plAS: Batch3S's two cuts give back the written rounds' and the tail's
  BD.embSS, BD.prjSS, BD.backSS    at the batch's skeleton D.S: the front's ways are parameters;
    backSS: what is written is read back, if it is so at the front and at the trees of the three
    stretches
  BD.relSS                         the same at D.S
  BD.opSS of look                  the openings of a whole string: the front's; tree n of the
    three stretches counted through (Batch3S's posS counts so)
  BD.plSS pf pl₁ pJ pl₂ p3 pl₃     the plain parts of a whole string
WHAT IS NOT SAID. No way of writing is given here, and no law on it but "read back". That opSS at
Batch3S's posS n x is look n … x: not stated (the symbol's type at posS n x is the column's by a
proof alone); a file of this project that is not in this library tries it by a run. Nothing on size:
each maker walks to its round at
every call (a position costs O(rounds before it), as poL | poR); plAS is no tail call. The interface
and the whole wiring: a file of this project that is not in this library.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.Batch3SWire

set_option autoImplicit false

namespace TypedOracleCompiler.Slice
open TypedOracleCompiler.Iop Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run.Twin (RS PS)

/-- how the symbols of a round's trees are written into bodies -/
abbrev EncT (B : Type) : Type := (ts : List _root_.Fmt.Shape) → (p : PQ.PosT ts) → PQ.SymT ts p → B
/-- and read back -/
abbrev PrjT (B : Type) : Type := (ts : List _root_.Fmt.Shape) → (p : PQ.PosT ts) → B →
    Option (PQ.SymT ts p)

/-- what is written at a tree of a round of ds is read back -/
def BackOn {B : Type} (eT : EncT B) (pT : PrjT B) (ds : List PQ.RD) : Prop :=
  ∀ d ∈ ds, ∀ (p : PQ.PosT d.trees) (a : PQ.SymT d.trees p), pT d.trees p (eT d.trees p a) = some a

section Kit
variable {B : Type} (T : List RS)

/-! ## One round before a skeleton tail -/

/-- a skeleton round with a way of writing of its own, before a skeleton tail -/
def embHS (r : RS) (ef : (p : r.Pos) → r.Sym p → B)
    (et : (p : OPos (_root_.Run.Twin.up T)) → OSym (_root_.Run.Twin.up T) p → B) :
    (p : OPos (_root_.Run.Twin.up (r :: T))) → OSym (_root_.Run.Twin.up (r :: T)) p → B
  | .inl p, a => ef p a
  | .inr q, a => et q a

def prjHS (r : RS) (pf : (p : r.Pos) → B → Option (r.Sym p))
    (pt : (p : OPos (_root_.Run.Twin.up T)) → B → Option (OSym (_root_.Run.Twin.up T) p)) :
    (p : OPos (_root_.Run.Twin.up (r :: T))) → B → Option (OSym (_root_.Run.Twin.up (r :: T)) p)
  | .inl p, b => pf p b
  | .inr q, b => pt q b

theorem backHS (r : RS) (ef : (p : r.Pos) → r.Sym p → B) (pf : (p : r.Pos) → B → Option (r.Sym p))
    (hf : ∀ p a, pf p (ef p a) = some a)
    (et : (p : OPos (_root_.Run.Twin.up T)) → OSym (_root_.Run.Twin.up T) p → B)
    (pt : (p : OPos (_root_.Run.Twin.up T)) → B → Option (OSym (_root_.Run.Twin.up T) p))
    (ht : ∀ p a, pt p (et p a) = some a) :
    ∀ (p : OPos (_root_.Run.Twin.up (r :: T))) (a : OSym (_root_.Run.Twin.up (r :: T)) p),
      prjHS T r pf pt p (embHS T r ef et p a) = some a
  | .inl p, a => hf p a
  | .inr q, a => ht q a

/-- a seam before a skeleton tail has no position: the tail's way of writing -/
def embSeamS (s : Seam) (et : (p : OPos (_root_.Run.Twin.up T)) →
    OSym (_root_.Run.Twin.up T) p → B) :
    (p : OPos (_root_.Run.Twin.up (ofR s.r :: T))) → OSym (_root_.Run.Twin.up (ofR s.r :: T)) p → B
  | .inl p, _ => (s.noPos.false p).elim
  | .inr q, a => et q a

def prjSeamS (s : Seam)
    (pt : (p : OPos (_root_.Run.Twin.up T)) → B → Option (OSym (_root_.Run.Twin.up T) p)) :
    (p : OPos (_root_.Run.Twin.up (ofR s.r :: T))) → B →
        Option (OSym (_root_.Run.Twin.up (ofR s.r :: T)) p)
  | .inl p, _ => (s.noPos.false p).elim
  | .inr q, b => pt q b

theorem backSeamS (s : Seam) (et : (p : OPos (_root_.Run.Twin.up T)) →
    OSym (_root_.Run.Twin.up T) p → B)
    (pt : (p : OPos (_root_.Run.Twin.up T)) → B → Option (OSym (_root_.Run.Twin.up T) p))
    (ht : ∀ p a, pt p (et p a) = some a) :
    ∀ (p : OPos (_root_.Run.Twin.up (ofR s.r :: T)))
        (a : OSym (_root_.Run.Twin.up (ofR s.r :: T)) p),
      prjSeamS T s pt p (embSeamS T s et p a) = some a
  | .inl p, _ => (s.noPos.false p).elim
  | .inr q, a => ht q a

/-! ## Written rounds before a skeleton tail -/

variable (C : PQ.CK) (eT : EncT B) (pT : PrjT B)

/-- written rounds before a skeleton tail: a symbol of theirs as its round's trees' way says; one of
the tail as the tail's -/
def embAS (et : (p : OPos (_root_.Run.Twin.up T)) → OSym (_root_.Run.Twin.up T) p → B) :
    (ds : List PQ.RD) → (p : OPos (shA C T ds)) → OSym (shA C T ds) p → B
  | [], p, a => et p a
  | d :: _, .inl p, a => eT d.trees p a
  | _ :: ds, .inr q, a => embAS et ds q a

def prjAS (pt : (p : OPos (_root_.Run.Twin.up T)) → B → Option (OSym (_root_.Run.Twin.up T) p)) :
    (ds : List PQ.RD) → (p : OPos (shA C T ds)) → B → Option (OSym (shA C T ds) p)
  | [], p, b => pt p b
  | d :: _, .inl p, b => pT d.trees p b
  | _ :: ds, .inr q, b => prjAS pt ds q b

theorem backAS (et : (p : OPos (_root_.Run.Twin.up T)) → OSym (_root_.Run.Twin.up T) p → B)
    (pt : (p : OPos (_root_.Run.Twin.up T)) → B → Option (OSym (_root_.Run.Twin.up T) p))
    (ht : ∀ p a, pt p (et p a) = some a) :
    ∀ (ds : List PQ.RD), BackOn eT pT ds → ∀ (p : OPos (shA C T ds)) (a : OSym (shA C T ds) p),
      prjAS T C pT pt ds p (embAS T C eT et ds p a) = some a
  | [], _, p, a => ht p a
  | d :: _, h, .inl p, a => h d List.mem_cons_self p a
  | _ :: ds, h, .inr q, a => backAS et pt ht ds (fun d hd => h d (List.mem_cons_of_mem _ hd)) q a

/-- written rounds with nothing behind them -/
def embLS : (ds : List PQ.RD) → (p : OPos (PQ.uL C ds)) → OSym (PQ.uL C ds) p → B
  | [], p, _ => p.elim
  | d :: _, .inl p, a => eT d.trees p a
  | _ :: ds, .inr q, a => embLS ds q a

def prjLS : (ds : List PQ.RD) → (p : OPos (PQ.uL C ds)) → B → Option (OSym (PQ.uL C ds) p)
  | [], p, _ => p.elim
  | d :: _, .inl p, b => pT d.trees p b
  | _ :: ds, .inr q, b => prjLS ds q b

theorem backLS : ∀ (ds : List PQ.RD), BackOn eT pT ds →
    ∀ (p : OPos (PQ.uL C ds)) (a : OSym (PQ.uL C ds) p),
      prjLS C pT ds p (embLS C eT ds p a) = some a
  | [], _, p, _ => p.elim
  | d :: _, h, .inl p, a => h d List.mem_cons_self p a
  | _ :: ds, h, .inr q, a => backLS ds (fun d hd => h d (List.mem_cons_of_mem _ hd)) q a

end Kit

/-! ## Two ways of writing, side by side -/

/-- a relation holds between what two ways write at every tree of a round of ds -/
def RelOn {B B' : Type} (R : B → B' → Prop) (eT : EncT B) (eT' : EncT B')
    (ds : List PQ.RD) : Prop :=
  ∀ d ∈ ds, ∀ (p : PQ.PosT d.trees) (a : PQ.SymT d.trees p), R (eT d.trees p a) (eT' d.trees p a)

section Rel
variable {B B' : Type} (R : B → B' → Prop) (T : List RS)

theorem relHS (r : RS) (ef : (p : r.Pos) → r.Sym p → B) (ef' : (p : r.Pos) → r.Sym p → B')
    (hf : ∀ p a, R (ef p a) (ef' p a))
    (et : (p : OPos (_root_.Run.Twin.up T)) → OSym (_root_.Run.Twin.up T) p → B)
    (et' : (p : OPos (_root_.Run.Twin.up T)) → OSym (_root_.Run.Twin.up T) p → B')
    (ht : ∀ p a, R (et p a) (et' p a)) :
    ∀ (p : OPos (_root_.Run.Twin.up (r :: T))) (a : OSym (_root_.Run.Twin.up (r :: T)) p),
      R (embHS T r ef et p a) (embHS T r ef' et' p a)
  | .inl p, a => hf p a
  | .inr q, a => ht q a

theorem relSeamS (s : Seam) (et : (p : OPos (_root_.Run.Twin.up T)) →
    OSym (_root_.Run.Twin.up T) p → B)
    (et' : (p : OPos (_root_.Run.Twin.up T)) → OSym (_root_.Run.Twin.up T) p → B')
    (ht : ∀ p a, R (et p a) (et' p a)) :
    ∀ (p : OPos (_root_.Run.Twin.up (ofR s.r :: T)))
        (a : OSym (_root_.Run.Twin.up (ofR s.r :: T)) p),
      R (embSeamS T s et p a) (embSeamS T s et' p a)
  | .inl p, _ => (s.noPos.false p).elim
  | .inr q, a => ht q a

variable (C : PQ.CK) (eT : EncT B) (eT' : EncT B')

theorem relAS (et : (p : OPos (_root_.Run.Twin.up T)) → OSym (_root_.Run.Twin.up T) p → B)
    (et' : (p : OPos (_root_.Run.Twin.up T)) → OSym (_root_.Run.Twin.up T) p → B')
    (ht : ∀ p a, R (et p a) (et' p a)) :
    ∀ (ds : List PQ.RD), RelOn R eT eT' ds → ∀ (p : OPos (shA C T ds)) (a : OSym (shA C T ds) p),
      R (embAS T C eT et ds p a) (embAS T C eT' et' ds p a)
  | [], _, p, a => ht p a
  | d :: _, h, .inl p, a => h d List.mem_cons_self p a
  | _ :: ds, h, .inr q, a => relAS et et' ht ds (fun d hd => h d (List.mem_cons_of_mem _ hd)) q a

theorem relLS : ∀ (ds : List PQ.RD), RelOn R eT eT' ds →
    ∀ (p : OPos (PQ.uL C ds)) (a : OSym (PQ.uL C ds) p),
      R (embLS C eT ds p a) (embLS C eT' ds p a)
  | [], _, p, _ => p.elim
  | d :: _, h, .inl p, a => h d List.mem_cons_self p a
  | _ :: ds, h, .inr q, a => relLS ds (fun d hd => h d (List.mem_cons_of_mem _ hd)) q a

end Rel

/-! ## Openings -/

section Open
variable {lam : ℕ} (T : List RS)

/-- a table of openings: tree number, the tree's form, place -/
abbrev Look (lam : ℕ) : Type :=
  ℕ → (s : _root_.Fmt.Shape) → Fin (2 ^ s.a) → Option (Opening lam (Fin s.W → UInt64))

/-- the openings of one round's trees; the round's first tree has the number n -/
def opTS (look : Look lam) : ℕ → (ts : List _root_.Fmt.Shape) → (p : PQ.PosT ts) →
    Option (Opening lam (PQ.SymT ts p))
  | n, s :: _, .inl x => look n s x
  | n, _ :: ts, .inr p => opTS look (n + 1) ts p

def opHS (r : RS) (of : (p : r.Pos) → Option (Opening lam (r.Sym p)))
    (ot : (p : OPos (_root_.Run.Twin.up T)) → Option
        (Opening lam (OSym (_root_.Run.Twin.up T) p))) :
    (p : OPos (_root_.Run.Twin.up (r :: T))) → Option
        (Opening lam (OSym (_root_.Run.Twin.up (r :: T)) p))
  | .inl p => of p
  | .inr q => ot q

def opSeamS (s : Seam)
    (ot : (p : OPos (_root_.Run.Twin.up T)) → Option
        (Opening lam (OSym (_root_.Run.Twin.up T) p))) :
    (p : OPos (_root_.Run.Twin.up (ofR s.r :: T))) →
      Option (Opening lam (OSym (_root_.Run.Twin.up (ofR s.r :: T)) p))
  | .inl p => (s.noPos.false p).elim
  | .inr q => ot q

variable (C : PQ.CK) (look : Look lam)

/-- written rounds before a skeleton tail; n trees stand before the first of them -/
def opAS (ot : (p : OPos (_root_.Run.Twin.up T)) → Option
    (Opening lam (OSym (_root_.Run.Twin.up T) p))) :
    ℕ → (ds : List PQ.RD) → (p : OPos (shA C T ds)) → Option (Opening lam (OSym (shA C T ds) p))
  | _, [], p => ot p
  | n, d :: _, .inl p => opTS look n d.trees p
  | n, d :: ds, .inr q => opAS ot (n + d.trees.length) ds q

def opLS : ℕ → (ds : List PQ.RD) → (p : OPos (PQ.uL C ds)) →
    Option (Opening lam (OSym (PQ.uL C ds) p))
  | _, [], p => p.elim
  | n, d :: _, .inl p => opTS look n d.trees p
  | n, d :: ds, .inr q => opLS (n + d.trees.length) ds q

end Open

/-! ## Plain parts -/

section Plain
variable (C : PQ.CK) (T : List RS) (pl : ℕ → (d : PQ.RD) → (PQ.roundS C d).Plain)

/-- written rounds before a skeleton tail: the round with the number i has pl i d -/
def plAS (pt : Plains (_root_.Run.Twin.up T)) : ℕ → (ds : List PQ.RD) → Plains (shA C T ds)
  | _, [] => pt
  | i, d :: ds => (pl i d, plAS pt (i + 1) ds)

def plLS : ℕ → (ds : List PQ.RD) → Plains (PQ.uL C ds)
  | _, [] => ()
  | i, d :: ds => (pl i d, plLS (i + 1) ds)

/-- Batch3S's first cut gives back the written rounds' plain parts -/
theorem plF_plAS (pt : Plains (_root_.Run.Twin.up T)) :
    ∀ (i : ℕ) (ds : List PQ.RD), plF C T ds (plAS C T pl pt i ds) = plLS C pl i ds
  | _, [] => rfl
  | i, d :: ds => congrArg (Prod.mk (pl i d)) (plF_plAS pt (i + 1) ds)

/-- and its second cut the tail's -/
theorem plS_plAS (pt : Plains (_root_.Run.Twin.up T)) :
    ∀ (i : ℕ) (ds : List PQ.RD), plS C T ds (plAS C T pl pt i ds) = pt
  | _, [] => rfl
  | i, _ :: ds => plS_plAS pt (i + 1) ds

end Plain

/-! ## At the batch's skeleton -/

namespace BD
variable {B : Type} (D : BD) (eT : EncT B) (pT : PrjT B)
  (ef : (p : D.F.r.Pos) → D.F.r.Sym p → B) (pf : (p : D.F.r.Pos) → B → Option (D.F.r.Sym p))

/-- A symbol of the batch's oracles as a body: the front's by the given way; a stretch's by its
round's trees' way. -/
def embSS : (p : OPos D.shS) → OSym D.shS p → B :=
  embHS _ (ofR D.F.r) ef (embAS D.SJ D.G.C eT
    (embSeamS _ D.G.s2 (embAS D.S₃ D.G.C eT
      (embSeamS _ D.G.s3 (embLS D.G.C eT D.G.ds₃)) D.G.ds₂)) D.G.ds₁)

/-- A body read at a position. -/
def prjSS : (p : OPos D.shS) → B → Option (OSym D.shS p) :=
  prjHS _ (ofR D.F.r) pf (prjAS D.SJ D.G.C pT
    (prjSeamS _ D.G.s2 (prjAS D.S₃ D.G.C pT
      (prjSeamS _ D.G.s3 (prjLS D.G.C pT D.G.ds₃)) D.G.ds₂)) D.G.ds₁)

/-- What is written is read back, if it is so at the front and at the trees of the three
stretches. -/
theorem backSS (hf : ∀ p a, pf p (ef p a) = some a) (h₁ : BackOn eT pT D.G.ds₁)
    (h₂ : BackOn eT pT D.G.ds₂)
    (h₃ : BackOn eT pT D.G.ds₃) (p : OPos D.shS) (a : OSym D.shS p) :
    D.prjSS pT pf p (D.embSS eT ef p a) = some a :=
  backHS _ (ofR D.F.r) ef pf hf _ _ (backAS D.SJ D.G.C eT pT _ _
    (backSeamS _ D.G.s2 _ _ (backAS D.S₃ D.G.C eT pT _ _
      (backSeamS _ D.G.s3 _ _ (backLS D.G.C eT pT D.G.ds₃ h₃)) D.G.ds₂ h₂)) D.G.ds₁ h₁) p a

/-- A relation between what two ways write holds everywhere, if it holds at the front and at the
trees of the three stretches. -/
theorem relSS {B' : Type} (R : B → B' → Prop) (eT' : EncT B')
    (ef' : (p : D.F.r.Pos) → D.F.r.Sym p → B')
    (hf : ∀ p a, R (ef p a) (ef' p a)) (h₁ : RelOn R eT eT' D.G.ds₁) (h₂ : RelOn R eT eT' D.G.ds₂)
    (h₃ : RelOn R eT eT' D.G.ds₃) (p : OPos D.shS) (a : OSym D.shS p) :
    R (D.embSS eT ef p a) (D.embSS eT' ef' p a) :=
  relHS R _ (ofR D.F.r) ef ef' hf _ _ (relAS R D.SJ D.G.C eT eT' _ _
    (relSeamS R _ D.G.s2 _ _ (relAS R D.S₃ D.G.C eT eT' _ _
      (relSeamS R _ D.G.s3 _ _ (relLS R D.G.C eT eT' D.G.ds₃ h₃)) D.G.ds₂ h₂)) D.G.ds₁ h₁) p a

/-- The openings of a whole string: the front's; the trees of the three stretches counted
through. -/
def opSS {lam : ℕ} (of : (p : D.F.r.Pos) → Option (Opening lam (D.F.r.Sym p))) (look : Look lam) :
    (p : OPos D.shS) → Option (Opening lam (OSym D.shS p)) :=
  opHS _ (ofR D.F.r) of (opAS D.SJ D.G.C look
    (opSeamS _ D.G.s2 (opAS D.S₃ D.G.C look
      (opSeamS _ D.G.s3 (opLS D.G.C look (nTrees D.G.ds₁ + nTrees D.G.ds₂) D.G.ds₃))
      (nTrees D.G.ds₁) D.G.ds₂)) 0 D.G.ds₁)

/-- The plain parts of a whole string: the front's, the first stretch's, the joining round's,
the second stretch's, the seam's, the third stretch's; each stretch's rounds are numbered from 0. -/
def plSS (fp : D.F.r.Plain) (pl₁ : ℕ → (d : PQ.RD) → (PQ.roundS D.G.C d).Plain)
    (pJ : D.G.s2.r.Plain)
    (pl₂ : ℕ → (d : PQ.RD) → (PQ.roundS D.G.C d).Plain) (p3 : D.G.s3.r.Plain)
    (pl₃ : ℕ → (d : PQ.RD) → (PQ.roundS D.G.C d).Plain) : Plains D.shS :=
  (fp, plAS D.G.C D.SJ pl₁ (pJ, plAS D.G.C D.S₃ pl₂ (p3, plLS D.G.C pl₃ 0 D.G.ds₃) 0 D.G.ds₂) 0
      D.G.ds₁)

end BD

end TypedOracleCompiler.Slice
