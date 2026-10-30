-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLayDList.lean: masks sent in advance, in the forms `L.PendD`, `L.LayD`, along the list of a
request's segments: which blocks are pending behind each segment, and what is asked of each body.

In standard terms: book-keeping for the honest prover's side of a request's sub-protocol, along the
list of its segments: which sets of entries of earlier oracle messages are out and unused after
each segment, by recursion on the list, and two statements by induction on it. The whole request:
Cb/Ld/LdLayD.lean.

Definitions and statements (`Cb.Spec.ldLayD_laid`, `Cb.Spec.ldLayD_segs`); the proofs are in
Cb/Ld/LdLayDListProofs.lean. It builds on Cb/Ld/LdLayDKit.lean (pending blocks; a step's own
condition; the closure on data; standard sendings whose data do not look; "passes a closed body")
and Cb/Ld/LdLayDBody.lean (what zero knowledge asks of a closed body, beside its hypotheses, at a
set of pending blocks).

Main names:
For one reference segment S (entry step ; body ; batching ; bridge to fold ; the one sending ; the
locations):
  `S.CutD Rd own`: the cut's condition: the pair that the locations cut out of the new messages is
    the same at new messages that agree at the entries in Rd that are not own.
  `S.NewD Q β`: β is laid by the one sending: `S.Qc.snd.LaysD` (one of the two forms; free entries
    of a layout for which the sending is the standard one).
  `S.CrossW Q pp W own Mk val`: what a block is asked inside S so that it crosses: it passes the
    body (`A.OutD`); every member of the closing's group is seen whole and holds no own entry; the
    one sending is standard and its data do not look.
  `S.crossed W own Mk val RdN RrN`: the block behind S: of the kept messages what W saw; of the new
    ones RdN, RrN; own entries and values as they were.
  `S.CrossD Q pp β' β`: β', pending before S, crosses S as β: the entry step's own condition hands
    β' on as a block at the body's entry (`LdPend.StepD S.m`: the model's map); `S.CrossW` there; β
    is `S.crossed ..`.
Along the list L:
  `L.PendD Q pp P₀`: the blocks (`LdPend`, Cb/Ld/LdMia.lean) that are pending behind L, given the
    set P₀ of those pending at its start. Empty list: the closure of P₀ (`LdPend.JD`,
    Cb/Ld/LdLayDKit.lean: under pairs, smaller readings, other types for the same masks, the same
    own entries and values written otherwise). L ; S: the closure of: blocks with the cut's
    condition that S's one sending lays, or that cross S from a block pending behind L.
  `L.LayD Q pp P₀`: for each segment S of L: what zero knowledge asks of its body, beside its
    hypotheses, in the form `A.ZkD`, at the blocks that the entry step's own condition hands on from
    blocks pending before S.
  `L.Reads`: of the witness each closing's link from bridge to fold reads the group's members only
    and hands the rest on (`D.Reads l`, Cb/Req1/LdReqRefLayStd.lean: a theorem for the group's own
    link).
  Q: what is asked of a layout: a parameter (Cb/Ld/LdLayDKit.lean); the statements ask that it be
    sound.
  `Spec.ldLayD_laid`: E of characteristic pp; the configuration's further oracles have a string
    (`Nonempty I.C.E0.Str`, an instance binder); `Q.Sound`; `L.OK pp` (the segments' bundles: from
    the model's side and the protocol's); `L.Reads`; every block of P₀ has its fact in the closure
    of "base" ⇒ every block of `L.PendD` has its fact laid (`L.LaidJ base`,
    Cb/Req1/LdReqRefLayJ.lean).
  `Spec.ldLayD_segs`: E of characteristic pp, `Q.Sound`, `L.OK pp`, `L.Reads`, the same premise on
    P₀, and `L.LayD Q pp P₀` ⇒ `L.LayJ pp base`.

Why: `L.LaidJ` and `L.LayJ` unfold to "given all that a run shows the masks are uniform" (exactly:
`Honest.Fresh`, Ior/KnowCollRulesMask.lean) and "the link does not look", link for link. `L.PendD`
and `L.LayD` are made of: equations that say which sender stands where; layouts; injective families
of free entries; who reads what; the cuts; the entry steps' maps; and, inside the front's places,
some clauses on relations that repeat the model's side (not all is named here: see "What the clauses
are made of", Cb/Ld/LdLayD.lean).

Limits: that `L.PendD` and `L.LayD` name no property of an honest prover, of a sender or of a link
is one writer's reading, not a theorem.


A hypothesis that stands as an instance binder in `Spec.ldLayD_laid`: the configuration's further
oracles have a string (`Nonempty I.C.E0.Str`); in `Spec.ldLayD_segs` it comes out of `A.ZkD`.
This file does not say that a request meets `L.LayD`. This protocol's technical report
(lean/CREDITS.md) has no counterpart of
`LdPend.StepD` at `S.m`: it has no entry steps. A block laid in the form "whichever new members"
cannot cross the closing of a group that holds a member of the same sending. This file says nothing
on a splitting. A body's own sendings lay no masks. A block that crosses a closing lies in messages
that are no members of the closing's group. This file says nothing on segments with two groups. It
speaks of one statement at a time: it has no form for sets of instances.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLayDKit
import Cb.Ld.LdLayDBody
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain

section
variable {E Kc : Type} [Field E] [Fintype E]

namespace LdRefS
variable {I : LdRefIx E} {a : LdStage E Kc} (S : LdRefS E Kc I a)

/-- The cut's condition. -/
def CutD (Rd own : (S.K.R.c1.fold.tgt.S.sum S.Qc.N).Ent → Prop) : Prop :=
  ∀ m m' : S.Qc.N.Msg,
    (∀ n : S.Qc.N.Ent, Rd ⟨Sum.inr n.1, n.2⟩ → ¬ own ⟨Sum.inr n.1, n.2⟩ → m' n.1 n.2 = m n.1 n.2) →
    S.Qc.cutN m' = S.Qc.cutN m

/-- a block behind the one sending, as a block behind the locations: the same fields -/
def atEnd (β : LdPend S.Qc.snd.tgt) : LdPend S.d :=
  (⟨β.Rd, β.Rr, β.own, β.Mk, β.val⟩ : LdPend S.Qc.loc.tgt)

/-- Laid by the one sending. -/
def NewD (Q : LdLayQ E) (β : LdPend S.d) : Prop :=
  ∃ β₀ : LdPend S.Qc.snd.tgt, S.Qc.snd.LaysD Q β₀ ∧ β = S.atEnd β₀

/-- What a block is asked inside S so that it crosses. -/
structure CrossW (Q : LdLayQ E) (pp : ℕ) (W : LdRefW S.A) (own : S.A.Xa.Q.D.S.Ent → Prop)
    (Mk : Type) [Fintype Mk] [Nonempty Mk] (val : Mk → S.A.Xa.Q.D.S.Ent → E) : Prop where
  out   : S.A.OutD Q pp W own Mk val
  whole : ∀ o, S.K.R.c1.fold.G.mem o → W.Rr2 o ∧ ∀ j, W.Rd2 ⟨o, j⟩ ∧ ¬ S.A.own2 own ⟨o, j⟩
  one   : S.Qc.snd.StdBl Q (S.K.R.c1.fold.S₁.subQ _ (S.K.R.c1.fold.S.subQ S.K.R.c1.fold.kp W.Rd2))
    (fun o => W.Rr2 o.1.1)
    (S.K.R.c1.fold.S₁.subQ _ (S.K.R.c1.fold.S.subQ S.K.R.c1.fold.kp (S.A.own2 own)))

/-- the block behind S -/
def crossed (W : LdRefW S.A) (own : S.A.Xa.Q.D.S.Ent → Prop) (Mk : Type)
    [Fintype Mk] [Nonempty Mk] (val : Mk → S.A.Xa.Q.D.S.Ent → E)
    (RdN : S.Qc.N.Ent → Prop) (RrN : S.Qc.N.O → Prop) : LdPend S.d :=
  (⟨S.K.R.c1.fold.tgt.S.sumP S.Qc.N
      (S.K.R.c1.fold.S₁.subQ _ (S.K.R.c1.fold.S.subQ S.K.R.c1.fold.kp W.Rd2)) RdN,
    S.K.R.c1.fold.tgt.S.sumO S.Qc.N (fun a => W.Rr2 a.1.1) RrN,
    S.K.R.c1.fold.tgt.S.sumP S.Qc.N
      (S.K.R.c1.fold.S₁.subQ _ (S.K.R.c1.fold.S.subQ S.K.R.c1.fold.kp (S.A.own2 own)))
      fun _ => False,
    Mk,
    fun M =>
      S.K.R.c1.fold.tgt.S.sumV S.Qc.N
        (S.K.R.c1.fold.S₁.subF _ (S.K.R.c1.fold.S.subF S.K.R.c1.fold.kp (S.A.val2 val M)))
        fun _ => 0⟩ : LdPend S.Qc.loc.tgt)

/-- β', pending before S, crosses S as β. -/
def CrossD (Q : LdLayQ E) (pp : ℕ) (β' : LdPend a) (β : LdPend S.d) : Prop :=
  ∃ (W : LdRefW S.A) (own : S.A.Xa.Q.D.S.Ent → Prop) (Mk : Type) (_ : Fintype Mk) (_ : Nonempty Mk)
      (val : Mk → S.A.Xa.Q.D.S.Ent → E) (RdN : S.Qc.N.Ent → Prop) (RrN : S.Qc.N.O → Prop),
    LdPend.StepD S.m β' (⟨W.Rd, W.Rr, own, Mk, val⟩ : LdPend S.A.V.Fp.s0) ∧
    S.CrossW Q pp W own Mk val ∧
    β = S.crossed W own Mk val RdN RrN

end LdRefS

namespace LdRefL
variable {I : LdRefIx E} {a : LdStage E Kc}

/-- of the witness each closing's link reads the group's members only, and hands the rest on -/
def Reads : {b : LdStage E Kc} → LdRefL E Kc I a b → Prop
  | _, .nil => True
  | _, .snoc L S => L.Reads ∧ S.K.R.c1.fold.Reads S.l

/-- The blocks that are pending behind the list. -/
def PendD (Q : LdLayQ E) (pp : ℕ) (P₀ : LdPend a → Prop) :
    {b : LdStage E Kc} → LdRefL E Kc I a b → LdPend b → Prop
  | _, .nil => LdPend.JD P₀
  | _, .snoc L S =>
    LdPend.JD fun β =>
      S.CutD β.Rd β.own ∧ (S.NewD Q β ∨ ∃ β', L.PendD Q pp P₀ β' ∧ S.CrossD Q pp β' β)

/-- What is asked of the bodies: `A.ZkD` of each. -/
def LayD (Q : LdLayQ E) (pp : ℕ) (P₀ : LdPend a → Prop) :
    {b : LdStage E Kc} → LdRefL E Kc I a b → Prop
  | _, .nil => True
  | _, .snoc L S =>
    L.LayD Q pp P₀ ∧ S.A.ZkD Q pp fun γ => ∃ β, PendD Q pp P₀ L β ∧ LdPend.StepD S.m β γ

end LdRefL
end

namespace Spec

/-- Under the hypotheses below: every pending block's fact is laid. -/
def ldLayD_laid : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (pp : ℕ) [CharP E pp] (I : LdRefIx E)
      [Nonempty I.C.E0.Str] (a b : LdStage E Kc) (L : LdRefL E Kc I a b) (Q : LdLayQ E)
      (P₀ : LdPend a → Prop) (base : MaskFact a.J.W → Prop),
    Q.Sound → L.OK pp → L.Reads → (∀ β, P₀ β → MaskFact.JCl base β.fact) →
    ∀ β, L.PendD Q pp P₀ β → L.LaidJ base β.fact

/-- The clause "lay" (`lay` in `LdReqRefDS`, Cb/Req1/LdReqRefStd.lean), from `L.LayD`. (not all
hypotheses are named here: see the statement below) -/
def ldLayD_segs : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (pp : ℕ) [CharP E pp] (I : LdRefIx E) (a b : LdStage E Kc)
      (L : LdRefL E Kc I a b) (Q : LdLayQ E) (P₀ : LdPend a → Prop) (base : MaskFact a.J.W → Prop),
    Q.Sound → L.OK pp → L.Reads → (∀ β, P₀ β → MaskFact.JCl base β.fact) →
    L.LayD Q pp P₀ → L.LayJ pp base

end Spec
end Cb
