-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/CodingFnKeep.lean: the typed oracle functions at the format's own oracle, with the hash's state
kept. The state is the one after the whole blocks of what all blocks of one chain answer share. A
theorem of this file says that these functions are `famP` at `Fmt.oracle`.

Definitions that compute; theorems with proofs. The format page (docs/format/FORMAT.md, which comes
with the programs, that is, with the C++ implementation that accompanies this Lean code): an
edition that is not the one that ships (R2.6's remark; R5.2); both rules have one and the same
text at the further editions that were compared by program; not held against the page that
ships.
The typed oracle functions (`famP`, Run/CodingFnThin.lean) answer a typed query of the compiled
verifier by the value of a function O on byte strings at the string of the format's hash call for
it, and by zeros where it has no call.

Why: a chain answer has K + 1 blocks; block b is half (b mod 2) of call (b div 2) of the round;
every call hashes the label, the prover's whole message and then two words. Run/CodingFnThin.lean's
`famB` asks the oracle once for each block: K + 1 times the whole message. With one K for all rounds
(some eighty blocks at the programs' plan) and a message of 77,280 bytes that is some eighty times
604 compressions. Fmt/Blake2bFast.lean has the state behind the whole blocks of a prefix (`absorb`),
the rest from there (`finish`), and the theorem (`finish_absorb`) that, under its hypotheses, the
two together are the hash.

Main names:
  `blocksFromK st left kind w nonce K`: the K + 1 typed blocks. The state is an argument of a
    function of its own: so it is made once (a "let" that is used under a λ is made anew at every
    use: measured in a separate trial, known here at second hand).
  `blocksK Lf D K q`: a chain query's blocks: for a round i + 1 with data in the hash's domain:
    absorb once, then `blocksFromK`; else (round 0; a head of another form; data outside the
    domain): the text of Run/CodingFnThin.lean at `Fmt.oracle`.
  `blocksK_eq`, `famBK_eq`, `famK_eq : famK Lf D K = famP Lf Fmt.oracle D K`: for all arguments; no
    hypothesis beside whatever the arguments hold as proofs.

These times were measured (one run each; scratch files outside this development, each run from
another file than this one; the evaluator; a made-up round with a message of 77,280 bytes; all 256
bits of all K + 1 blocks read; the texts of the hash and of the byte reader as they lay before a
later speed-up of theirs): K = 80: famK 0.3 seconds, famP at Fmt.oracle 241 seconds; K = 2: 0.3
against 8.7 seconds; the same values.

Limits: time is a fact about this compiler and these texts, no theorem. Leaves and nodes are asked
as in `famP`. This file says nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Run.CodingFnThin
import Fmt.Rules5Fast
import Fmt.Rules23Laws

set_option autoImplicit false

namespace Run
open Compile Compile.Batch Iop Rom

/-- A hash under 162 of "message, then a tail that is not empty" (`htl`), finished from the state
behind the whole blocks of "label, message", is the hash from its start. -/
theorem H162_finish (lab i : Nat) (rho msg tl : ByteArray) (htl : 0 < tl.size) :
    _root_.Fmt.finish 64
        (_root_.Fmt.absorb 64 ((_root_.Fmt.fit 32 rho).extract 0 16)
          ((_root_.Fmt.fit 32 rho).extract 16 32)
          ((_root_.Fmt.shared lab i msg).extract
            0 (_root_.Fmt.wholeOf (_root_.Fmt.shared lab i msg))))
        ((_root_.Fmt.shared lab i msg).extract
            (_root_.Fmt.wholeOf (_root_.Fmt.shared lab i msg)) (_root_.Fmt.shared lab i msg).size ++
          tl) =
      _root_.Fmt.formatHash 162 lab i rho (msg ++ tl) := by
  have hq : _root_.Fmt.wholeOf (_root_.Fmt.shared lab i msg) ≤ (_root_.Fmt.shared lab i msg).size :=
    Nat.mul_div_le _ _
  have h1 : ((_root_.Fmt.shared lab i msg).extract
          0 (_root_.Fmt.wholeOf (_root_.Fmt.shared lab i msg))).size % 128 = 0 := by
    rw [ByteArray.size_extract, Nat.min_eq_left hq, Nat.sub_zero]
    exact Nat.mul_mod_right _ _
  have h2 : 0 <
      ((_root_.Fmt.shared lab i msg).extract
          (_root_.Fmt.wholeOf (_root_.Fmt.shared lab i msg)) (_root_.Fmt.shared lab i msg).size ++
        tl).size := by
    rw [ByteArray.size_append]
    omega
  rw [_root_.Fmt.finish_absorb 64 _ _ _ _ h1 h2,
    ← ByteArray.append_assoc, _root_.Fmt.extract_split _ _ hq]
  show _root_.Fmt.blake2b 64 _ _ (_root_.Fmt.label 162 lab i ++ msg ++ tl) =
    _root_.Fmt.blake2b (_root_.Fmt.dlen 162) _ _ (_root_.Fmt.label 162 lab i ++ (msg ++ tl))
  rw [ByteArray.append_assoc]
  rfl

/-- Under a number that is no leaf's (`hl`) the domain asks of the bytes their number alone. -/
theorem hDom_size (n t i : Nat) (s b b' : ByteArray)
    (hl : _root_.Fmt.isLeaf n = false) (h : b.size = b'.size) :
    _root_.Fmt.hDom n t i s b = _root_.Fmt.hDom n t i s b' := by
  unfold _root_.Fmt.hDom
  rw [h, _root_.Fmt.leafOK_other n t b hl, _root_.Fmt.leafOK_other n t b' hl]

/-- The two words after the message in call c. -/
def tailK (kind w c nonce : Nat) : ByteArray :=
  _root_.Fmt.u64n (kind + 256 * w + 65536 * c) ++ _root_.Fmt.u64n nonce

theorem size_tailK (kind w c nonce : Nat) : (tailK kind w c nonce).size = 16 := rfl

theorem roundBytes_tailK (msg : ByteArray) (kind w c nonce : Nat) :
    roundBytes msg kind w c nonce = msg ++ tailK kind w c nonce := by
  unfold roundBytes tailK
  rw [ByteArray.append_assoc]

/-- Block b of the row, from the state. -/
def blockK (st : _root_.Fmt.B2.Mid) (left : ByteArray) (kind w nonce b : Nat) : ByteArray :=
  if b % 2 = 0 then (_root_.Fmt.finish 64 st (left ++ tailK kind w (b / 2) nonce)).extract 0 32
  else (_root_.Fmt.finish 64 st (left ++ tailK kind w (b / 2) nonce)).extract 32 64

/-- The K + 1 typed blocks, from the state. -/
def blocksFromK (st : _root_.Fmt.B2.Mid) (left : ByteArray) (kind w nonce K : Nat) :
    Array ByteArray :=
  Array.ofFn (n := K + 1) fun j => blockK st left kind w nonce (blockNo w K j)

variable {I X : Type} (Lf : Unit → BatchProtocol I X) {tg : Tag}

/-- A chain query's blocks, the state kept. -/
def blocksK (D : PageD (Lf ()) tg) (K : Nat) (q : FbIn 256 (Lf ()) tg) : Array ByteArray :=
  match q.round, q.head with
  | i + 1, .f2 none ρ =>
      if _root_.Fmt.hDom 162 D.label (i + 1) (bitsToBytes ρ)
          (roundBytes (D.msg (i + 1) (q.rt.map digToBytes) q.plain) (D.kind (i + 1))
            (D.work (i + 1)) 0 (D.nonce (i + 1) q.plain)) then
        blocksFromK (_root_.Fmt.absorb 64 ((_root_.Fmt.fit 32 (bitsToBytes ρ)).extract 0 16)
            ((_root_.Fmt.fit 32 (bitsToBytes ρ)).extract 16 32)
            ((_root_.Fmt.shared D.label (i + 1)
                (D.msg (i + 1) (q.rt.map digToBytes) q.plain)).extract
              0 (_root_.Fmt.wholeOf
                (_root_.Fmt.shared D.label (i + 1) (D.msg (i + 1) (q.rt.map digToBytes) q.plain)))))
          ((_root_.Fmt.shared D.label (i + 1) (D.msg (i + 1) (q.rt.map digToBytes) q.plain)).extract
            (_root_.Fmt.wholeOf
              (_root_.Fmt.shared D.label (i + 1) (D.msg (i + 1) (q.rt.map digToBytes) q.plain)))
            (_root_.Fmt.shared D.label (i + 1) (D.msg (i + 1) (q.rt.map digToBytes) q.plain)).size)
          (D.kind (i + 1)) (D.work (i + 1)) (D.nonce (i + 1) q.plain) K
      else blocksP Lf _root_.Fmt.oracle D K q
  | _, _ => blocksP Lf _root_.Fmt.oracle D K q

/-- The answer to a typed query as bytes. -/
def famBK (D : PageD (Lf ()) tg) (K : Nat) :
    (o : (spec 256 K (Lf ())).ι) → (spec 256 K (Lf ())).Dom o → Array ByteArray
  | .fb t', q =>
      match castTag (F := fun t => FbIn 256 (Lf ()) t) tg t' q with
      | some q => blocksK Lf D K q
      | none => #[]
  | o, q => famB Lf _root_.Fmt.oracle D K o q

/-- The typed oracle functions at the format's oracle, the state kept. -/
def famK (D : PageD (Lf ()) tg) (K : Nat) : Fam (spec 256 K (Lf ())) :=
  fun o q => decP Lf K o (famBK Lf D K o q)

/-! ## The equations -/

/-- One block, for data in the hash's domain (`hd`): `blockK` from the absorbed state is the answer
of `Fmt.oracle` at the call's string. -/
theorem blockK_eq (lab i : Nat) (rho msg : ByteArray) (kind w nonce b : Nat)
    (hd : _root_.Fmt.hDom 162 lab i rho (roundBytes msg kind w 0 nonce) = true) :
    blockK (_root_.Fmt.absorb 64 ((_root_.Fmt.fit 32 rho).extract 0 16)
          ((_root_.Fmt.fit 32 rho).extract 16 32)
          ((_root_.Fmt.shared lab i msg).extract
            0 (_root_.Fmt.wholeOf (_root_.Fmt.shared lab i msg))))
        ((_root_.Fmt.shared lab i msg).extract
          (_root_.Fmt.wholeOf (_root_.Fmt.shared lab i msg)) (_root_.Fmt.shared lab i msg).size)
        kind w nonce b =
      _root_.Fmt.oracle
        (_root_.Fmt.oStr (UInt8.ofNat (b % 2)) 162 lab i rho
          (roundBytes msg kind w (b / 2) nonce)) := by
  have hd' : _root_.Fmt.hDom 162 lab i rho (roundBytes msg kind w (b / 2) nonce) = true := by
    rw [← hd]
    apply hDom_size _ _ _ _ _ _ rfl
    rw [roundBytes_tailK, roundBytes_tailK, ByteArray.size_append,
      ByteArray.size_append, size_tailK, size_tailK]
  unfold blockK
  rw [H162_finish lab i rho msg _ (by rw [size_tailK]; omega), ← roundBytes_tailK]
  rcases Nat.mod_two_eq_zero_or_one b with h | h
  · rw [if_pos h, h]
    exact (_root_.Fmt.oracle_in0 162 lab i rho _ hd').symm
  · rw [if_neg (by omega), h]
    exact (_root_.Fmt.oracle_in1 lab i rho _ hd').symm

variable {Lf}

/-- A chain query's blocks. -/
theorem blocksK_eq (D : PageD (Lf ()) tg) (K : Nat) (q : FbIn 256 (Lf ()) tg) :
    blocksK Lf D K q = blocksP Lf _root_.Fmt.oracle D K q := by
  obtain ⟨round, head, rt, plain⟩ := q
  cases round with
  | zero => rfl
  | succ i =>
      cases head with
      | f2 xl ρ =>
          cases xl with
          | some _ => rfl
          | none =>
              show (if _root_.Fmt.hDom 162 D.label (i + 1) (bitsToBytes ρ)
                        (roundBytes (D.msg (i + 1) (rt.map digToBytes) plain) (D.kind (i + 1))
                          (D.work (i + 1)) 0 (D.nonce (i + 1) plain)) = true then _
                  else _) = _
              split
              · rename_i hd
                unfold blocksFromK blocksP
                congr 1
                funext j
                rw [blockK_eq _ _ _ _ _ _ _ _ hd]
                rfl
              · rfl
      | f1 _ _ _ => rfl
      | f3 _ _ => rfl
      | f4 _ _ => rfl
      | f5 _ => rfl

theorem famBK_eq (D : PageD (Lf ()) tg) (K : Nat)
    (o : (spec 256 K (Lf ())).ι) (q : (spec 256 K (Lf ())).Dom o) :
    famBK Lf D K o q = famB Lf _root_.Fmt.oracle D K o q := by
  cases o with
  | fb t =>
      by_cases ht : t = tg
      · subst ht
        simp only [famBK, famB, castTag_self]
        exact blocksK_eq D K q
      · simp only [famBK, famB, castTag_ne ht]
  | leaf => rfl
  | node => rfl
  | fbw _ _ => rfl
  | rleaf => rfl
  | rnode => rfl
  | g _ => rfl
  | ann => rfl
  | other => rfl

/-- `famK` is `famP` at `Fmt.oracle`. -/
theorem famK_eq (D : PageD (Lf ()) tg) (K : Nat) : famK Lf D K = famP Lf _root_.Fmt.oracle D K := by
  funext o q
  show decP Lf K o (famBK Lf D K o q) = decP Lf K o (famB Lf _root_.Fmt.oracle D K o q)
  rw [famBK_eq]

end Run
