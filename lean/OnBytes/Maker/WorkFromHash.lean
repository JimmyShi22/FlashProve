-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Maker/WorkFromHash.lean: the bits of work of a written verifier's message are bits of the
hash function's answer: at the wire records of a whole file's written rounds (`wireLo`, `wireSh`,
OnBytes/Maker/Wire.lean), the message that the wire makes of an answer's K + 1 blocks passes its
test of work exactly if the first `work` bits of the answer's FIRST block are 0; where the round has
work, the rest of the message is made of the other K blocks alone (at no work: of the first K). And
that test is the format's own on the block's bytes.
Statements with proofs. TOOLS: general in the rounds' data: they name no description and no plan.

  `pass_chalGrind`, `old_chalGrind`: of `chalGrind` (Iop/GrindWire.lean) at any number of bits.
  `chal_wireLo`, `chal_wireSh`: the wire's function at a written round is `chalGrind`.
  `pass_wireLo`, `pass_wireSh`: at a local and at a shared written round.
  `pass_wireLo_fmt`, `pass_wireSh_fmt`: where the blocks are given by their bytes, as the format
    numbers them, and work ≤ 64: the wire's test is `Fmt.passesA` (by `Run.PQ.pass_grind`,
    Run/PageIsChain.lean).
  `Answers K ds`, `rhoOf`, `testsOf`, **`passT_rhoOf`**: for a stretch of written rounds: at the
    verifier's messages that the wire makes of the rounds' answers, the chain's test `passT` is: at
    every round the first `work` bits of that round's answer's first block are 0.

Why. `Maps.Held` (OnBytes/Flat/CarrySMaps.lean) divides a round's price by 2^work, and the file's
reduction asks `passT` in front of its decision (`wholeIOR_out_iff`, OnBytes/Maker/WholeViews.lean).
Here: what `passT` tests is, at the wire, a function of the answers' first blocks.

Limits. That the compiled verifier takes each round's message from the wire at the answer to that
round's query is the compiler's text (OnBytes/TypedOracleCompiler/Compile/Batch/Verifier.lean), not shown here. That
`d.entry.work` is the plan's stated work is not shown here. Nothing on what a query holds (the nonce
among it). Nothing on soundness.

-/
import OnBytes.Maker.Wire
import Run.PageIsChain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Maker
open TypedOracleCompiler.Iop
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ

/-- The message that `chalGrind` makes passes its test exactly if the first b bits of the first
block
are 0. -/
theorem pass_chalGrind {lam K : ℕ} {Cc : Type} (ch : (Fin K → Dig lam) → Cc) :
    ∀ (b : ℕ) (u : Fin (K + 1) → Dig lam),
      GChal.pass (chalGrind ch b u) = decide (∀ i : Fin b, testBits lam b (u 0) i = false)
  | 0, _ => by
      show decide (∀ i : Fin 0, _) = decide (∀ i : Fin 0, _)
      simp
  | _ + 1, _ => rfl

/-- Where a round has work, the rest of the message is made of the other K blocks alone. -/
theorem old_chalGrind {lam K : ℕ} {Cc : Type} (ch : (Fin K → Dig lam) → Cc) (b : ℕ)
    (u : Fin (K + 1) → Dig lam) :
    GChal.old (chalGrind ch (b + 1) u) = ch fun i => u i.succ := rfl

section
variable (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)

/-- The wire's function at a local written round. -/
theorem chal_wireLo (d : RDT) :
    (wireLo C K chal d).chal = chalGrind (chal d.entry d.kind) d.entry.work := rfl

/-- The wire's function at a shared written round. -/
theorem chal_wireSh (d : RDT) :
    (wireSh C K chal d).chal = chalGrind (chal d.entry d.kind) d.entry.work := rfl

/-- At a local written round. -/
theorem pass_wireLo (d : RDT) (u : Fin (K + 1) → Dig 256) :
    GChal.pass (b := d.entry.work) ((wireLo C K chal d).chal u) =
      decide (∀ i : Fin d.entry.work, testBits 256 d.entry.work (u 0) i = false) :=
  pass_chalGrind (chal d.entry d.kind) d.entry.work u

/-- At a shared written round. -/
theorem pass_wireSh (d : RDT) (u : Fin (K + 1) → Dig 256) :
    GChal.pass (b := d.entry.work) ((wireSh C K chal d).chal u) =
      decide (∀ i : Fin d.entry.work, testBits 256 d.entry.work (u 0) i = false) :=
  pass_chalGrind (chal d.entry d.kind) d.entry.work u

/-- At a local written round the wire's test is the format's, on the blocks' bytes. -/
theorem pass_wireLo_fmt (d : RDT) (u : Fin (K + 1) → Dig 256) (B : ℕ → ByteArray)
    (bs : Array ByteArray) (hw : d.entry.work ≤ 64)
    (hu : ∀ k : Fin (K + 1), u k = bytesToDig (B (blockNo d.entry.work (K + 1) k.castSucc)))
    (h0 : bs.getD 0 ByteArray.empty = B 0) :
    GChal.pass (b := d.entry.work) ((wireLo C K chal d).chal u) =
      _root_.Fmt.passesA d.entry.work bs :=
  pass_grind (chal d.entry d.kind) B bs d.entry.work u hw hu h0

/-- At a shared written round likewise. -/
theorem pass_wireSh_fmt (d : RDT) (u : Fin (K + 1) → Dig 256) (B : ℕ → ByteArray)
    (bs : Array ByteArray) (hw : d.entry.work ≤ 64)
    (hu : ∀ k : Fin (K + 1), u k = bytesToDig (B (blockNo d.entry.work (K + 1) k.castSucc)))
    (h0 : bs.getD 0 ByteArray.empty = B 0) :
    GChal.pass (b := d.entry.work) ((wireSh C K chal d).chal u) =
      _root_.Fmt.passesA d.entry.work bs :=
  pass_grind (chal d.entry d.kind) B bs d.entry.work u hw hu h0

/-- One answer of K + 1 blocks for each round of a stretch. -/
def Answers : List RDT → Type
  | [] => Unit
  | _ :: ds => (Fin (K + 1) → Dig 256) × Answers ds

/-- The verifier's messages that the wire makes of the rounds' answers. The wire's function is the
same at a local and at a shared round. -/
def rhoOf : (ds : List RDT) → Answers K ds → Rho (uLT C ds)
  | [], _ => ()
  | d :: ds, (u, us) => (chalGrind (chal d.entry d.kind) d.entry.work u, rhoOf ds us)

/-- At every round the first `work` bits of the answer's first block are 0. -/
def testsOf : (ds : List RDT) → Answers K ds → Bool
  | [], _ => true
  | d :: ds, (u, us) =>
      decide (∀ i : Fin d.entry.work, testBits 256 d.entry.work (u 0) i = false) && testsOf ds us

/-- **The chain's test of the work is a test on the hash function's answers.** -/
theorem passT_rhoOf : ∀ (ds : List RDT) (us : Answers K ds),
    passT C ds (rhoOf C K chal ds us) = testsOf K ds us
  | [], _ => rfl
  | d :: ds, (u, us) => by
      show (GChal.pass (b := d.entry.work) (chalGrind (chal d.entry d.kind) d.entry.work u) &&
        passT C ds (rhoOf C K chal ds us)) = _
      rw [pass_chalGrind, passT_rhoOf ds us]
      rfl

end

end OnBytes.Maker

#print axioms OnBytes.Maker.pass_chalGrind
#print axioms OnBytes.Maker.old_chalGrind
#print axioms OnBytes.Maker.chal_wireLo
#print axioms OnBytes.Maker.chal_wireSh
#print axioms OnBytes.Maker.pass_wireLo
#print axioms OnBytes.Maker.pass_wireSh
#print axioms OnBytes.Maker.pass_wireLo_fmt
#print axioms OnBytes.Maker.pass_wireSh_fmt
#print axioms OnBytes.Maker.passT_rhoOf
