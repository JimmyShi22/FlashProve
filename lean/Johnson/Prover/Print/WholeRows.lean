-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Print/WholeRows.lean: the maker of what the verifier is handed for a key file or a
proof file (`ofCarrier`, `madeFileOf`, Johnson/Top/Fire/Code/FileInOf.lean), at the parsed file that
is printed of a typed proof string (`carrierOf`, OnBytes/Prover/Print/Carrier.lean): its three
judged rows say yes, and the three silent plain parts that it makes are the string's own.

Main names (namespace `Johnson.Prover.Print`).
  `ofCarrier_carrierOf`    the rows and the three plain parts; general in the data
  `madeFileOf_carrierOf`   from the printed file's bytes the maker gives `ofCarrier` of that file

Limits. Asked, and shown nowhere here: that none of the three run values is 32 zero bytes; that the
second and the third chain have a round; `Printable`, and for the bytes `Canon`, `RootsFit`,
`SizesFit`. No prover, no oracle, no verifier.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Prover.Print.WholeWF
import Johnson.Top.Fire.Code.FileInOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Print

open OnBytes.Flat OnBytes.Slice OnBytes.Maker
open _root_.Run
open _root_.Iop (Dig)
open TypedOracleCompiler.Compile.Batch (OneProtocolProof)
open TypedOracleCompiler.Joined (pls₁ pls₂ pls₃)
open OnBytes.Prover.Print (carrierOf Printable Canon RootsFit SizesFit wrFile okSeed)
open OnBytes.Prover.Print (roundsOf length_roundsOf read_carrierOf map_ofTriple_triple)

theorem isEmpty_append_one {α : Type} (l : List α) (x : α) : (l ++ [x]).isEmpty = false := by
  cases l <;> rfl

theorem isEmpty_roundsOf (C : PQ.CK) (ds : List RDT) (rts : List (Dig 256))
    (pl : _root_.Iop.Plains (uLT C ds)) (h : ds ≠ []) : (roundsOf C ds rts pl).isEmpty = false := by
  cases hr : roundsOf C ds rts pl with
  | cons _ _ => rfl
  | nil =>
    have hl := length_roundsOf C ds rts pl
    rw [hr] at hl
    exact absurd (List.eq_nil_of_length_eq_zero hl.symm) h

/-- **Of the printed file the maker makes the string's own three silent plain parts, and its three
judged rows say yes.** -/
theorem ofCarrier_carrierOf :
  ∀ (C : PQ.CK) (D : WholeD) (tF : FrontMsg (List OnBytes.E))
    (tJ : Compile.Joined.JoinMsg (List OnBytes.E) ByteArray) (t3 : ByteArray) {Xi : Type}
    (silent : Xi → FrontMsg (List OnBytes.E) → Compile.Joined.JoinMsg (List OnBytes.E) ByteArray →
      ByteArray → Bool) (run : Xi → PQ.View → PQ.View → PQ.View → Bool)
    (what : String) (cfg root : ByteArray) (s : OnBytes.Params.LinBindingShape)
    (π : OneProtocolProof 256 (wholeDesc C D tF tJ t3 silent run).batch),
    Printable C D tF tJ t3 silent run cfg s π → root.size = 32 →
    -- none of the three run values is 32 zero bytes
    Fmt.runOk (bitsToBytes π.salt) = true →
    Fmt.runOk (pls₂ (wholeDesc C D tF tJ t3 silent run) π).1.run = true →
    Fmt.runOk (pls₃ (wholeDesc C D tF tJ t3 silent run) π).1 = true →
    -- public: the second and the third chain have a round
    D.ds₂ ≠ [] → D.ds₃ ≠ [] →
    (LKF.FileInOf.ofCarrier what cfg (carrierOf C D tF tJ t3 silent run root π)).ok = true ∧
    (LKF.FileInOf.ofCarrier what cfg (carrierOf C D tF tJ t3 silent run root π)).pF =
      (pls₁ (wholeDesc C D tF tJ t3 silent run) π).1 ∧
    (LKF.FileInOf.ofCarrier what cfg (carrierOf C D tF tJ t3 silent run root π)).pJ =
      (pls₂ (wholeDesc C D tF tJ t3 silent run) π).1 ∧
    (LKF.FileInOf.ofCarrier what cfg (carrierOf C D tF tJ t3 silent run root π)).p3 =
      (pls₃ (wholeDesc C D tF tJ t3 silent run) π).1 := by
  intro C D tF tJ t3 Xi silent run what cfg root s π hp hroot h1 h2 h3 hd2 hd3
  have ha : ((pls₁ (wholeDesc C D tF tJ t3 silent run) π).1.answers.map OnBytes.E.triple).map
      OnBytes.E.ofTriple = (pls₁ (wholeDesc C D tF tJ t3 silent run) π).1.answers :=
    map_ofTriple_triple _
  refine ⟨?_, ?_, ?_, rfl⟩
  · have r1 : (carrierOf C D tF tJ t3 silent run root π).run1.size = 32 :=
      size_bitsToBytes _ 32 hp.salt
    have rb : (carrierOf C D tF tJ t3 silent run root π).bindRoot.size = 32 := size_digToBytes _
    have e1 : (carrierOf C D tF tJ t3 silent run root π).rounds1.isEmpty = false := by
      exact isEmpty_append_one _ _
    have e2 : (carrierOf C D tF tJ t3 silent run root π).rounds2.isEmpty = false :=
      isEmpty_roundsOf C D.ds₂ _ _ hd2
    have e3 : (carrierOf C D tF tJ t3 silent run root π).rounds3.isEmpty = false :=
      isEmpty_roundsOf C D.ds₃ _ _ hd3
    have q0 : (carrierOf C D tF tJ t3 silent run root π).root.size = 32 := hroot
    have q2 : (carrierOf C D tF tJ t3 silent run root π).run2.size = 32 := hp.run2
    have q3 : (carrierOf C D tF tJ t3 silent run root π).run3.size = 32 := hp.run3
    have g1 : Fmt.runOk (carrierOf C D tF tJ t3 silent run root π).run1 = true := h1
    have g2 : Fmt.runOk (carrierOf C D tF tJ t3 silent run root π).run2 = true := h2
    have g3 : Fmt.runOk (carrierOf C D tF tJ t3 silent run root π).run3 = true := h3
    simp only [LKF.FileInOf.MadeFile.ok, LKF.FileInOf.ofCarrier, List.all_cons, List.all_nil, q0,
      rb, r1, q2, q3, g1, g2, g3, e1, e2, e3, decide_true, Bool.not_false, Bool.and_self]
  · show frontOf (((pls₁ (wholeDesc C D tF tJ t3 silent run) π).1.answers.map
      OnBytes.E.triple).map OnBytes.E.ofTriple)
      (pls₁ (wholeDesc C D tF tJ t3 silent run) π).1.copy = _
    rw [ha]
    rfl
  · show (⟨((pls₁ (wholeDesc C D tF tJ t3 silent run) π).1.answers.map OnBytes.E.triple).map
      OnBytes.E.ofTriple, (pls₂ (wholeDesc C D tF tJ t3 silent run) π).1.run⟩ :
        Compile.Joined.JoinMsg (List OnBytes.E) ByteArray) = _
    rw [ha, ← hp.answers]

/-- **From the printed file's bytes.** -/
theorem madeFileOf_carrierOf :
  ∀ (C : PQ.CK) (D : WholeD) (tF : FrontMsg (List OnBytes.E))
    (tJ : Compile.Joined.JoinMsg (List OnBytes.E) ByteArray) (t3 : ByteArray) {Xi : Type}
    (silent : Xi → FrontMsg (List OnBytes.E) → Compile.Joined.JoinMsg (List OnBytes.E) ByteArray →
      ByteArray → Bool) (run : Xi → PQ.View → PQ.View → PQ.View → Bool)
    (magic what : String) (cfg root : ByteArray) (s : OnBytes.Params.LinBindingShape)
    (π : OneProtocolProof 256 (wholeDesc C D tF tJ t3 silent run).batch),
    magic.toUTF8.size = 8 → RootsFit D → SizesFit D s → Printable C D tF tJ t3 silent run cfg s π →
    Canon C D tF tJ t3 silent run π → root.size = 32 →
    (magic = Carrier.magicKey → (pls₁ (wholeDesc C D tF tJ t3 silent run) π).1.copy = 0) →
    LKF.FileInOf.madeFileOf magic what cfg
        (wrFile magic (carrierOf C D tF tJ t3 silent run root π)) =
      .ok (LKF.FileInOf.ofCarrier what cfg (carrierOf C D tF tJ t3 silent run root π)) := by
  intro C D tF tJ t3 Xi silent run magic what cfg root s π hm hf hz hp hc hroot hcopy
  unfold LKF.FileInOf.madeFileOf
  rw [read_carrierOf C D tF tJ t3 silent run cfg root s magic π hm hf hz hp hc hroot hcopy]

end Johnson.Prover.Print
