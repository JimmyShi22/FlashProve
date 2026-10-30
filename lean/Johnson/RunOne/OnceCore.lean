-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/OnceCore.lean: what the K + 1 strings of one chain query share, computed once a
query, with the ties to `fbCallJ` and `fillJ` (OnBytes/Maker/Page/Frame.lean, Fill.lean).

No soundness: a test. This module serves the runs of lean/Ask/; it states nothing on soundness.

A file of its own, so that a file that needs these names alone need not import the running form of
the typed oracle functions that is built on them (Johnson/RunOne/FamT.lean).

Main names.
  `OnceJ`, `OnceJ.call`: what the calls of one chain query share: a row (label, index, start,
    message, kind, work, nonce, the order of blocks), or one call at the tail's block, or nothing;
    the call of a block from it.
  `onceJ F q`; `onceJ_call`: `(onceJ F q).call K j = fbCallJ F K q j`.
  `onceP`, `onceFill`; `onceFill_eq`: the same at the data `fillJ`, from ONE reading of the plain
    part (`PartJ`): `fillJ`'s msg and nonce each read it anew.

Limits. What an evaluator computes how often is a fact about the compiler, no theorem. The interface
L is an implicit parameter throughout, as in Frame.lean. Nothing on soundness.

-/
import OnBytes.Maker.Page.Fill

set_option autoImplicit false

namespace Johnson.RunOne

open TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop Rom
open _root_.Compile hiding ON
open _root_.Iop hiding BatchProtocol
open _root_.Run
open OnBytes OnBytes.Maker OnBytes.Maker.Page

variable {I X : Type} {L : BatchProtocolWithLeafBody I X} {t : Tag}

/-! ## Once a query -/

/-- What the K + 1 calls of one chain query share. -/
inductive OnceJ
  /-- a round's row: the blocks part in the half and the call's number alone -/
  | row (lab idx : ℕ) (start msg : ByteArray) (kind work nonce ow : ℕ)
  /-- the tail's block alone has a call -/
  | tail (c : Fmt.OQ)
  | nothing

/-- The call of a block. -/
def OnceJ.call (K : ℕ) : OnceJ → Fin (K + 1) → Option Fmt.OQ
  | .row lab idx st msg kind work nonce ow, j =>
    some ⟨UInt8.ofNat (blockNo ow K j % 2), 162, lab, idx, st,
      roundBytes msg kind work (blockNo ow K j / 2) nonce⟩
  | .tail c, j => if j.val = K then some c else none
  | .nothing, _ => none

/-- **What the calls of a chain query share**: `fbCallJ`'s text without the block. -/
def onceJ (F : FileJ L t) (q : FbIn 256 L t) : OnceJ :=
  match q.head with
  | .f1 cms x salt =>
    if q.round = 0 then .tail (firstCall F.lab₁ F.pd₁ (F.stm₁ cms x q.plain) salt) else .nothing
  | .f2 none ρ =>
    if 1 ≤ q.round ∧ q.round ≤ F.n₁ then
      .row F.lab₁ q.round (bitsToBytes ρ) (F.msg q.round (q.rt.map digToBytes) q.plain)
        (F.kind q.round) (F.work q.round) (F.nonce q.round q.plain) (F.work q.round)
    else if F.J3 + 1 ≤ q.round ∧ q.round ≤ F.J3 + F.n₃ then
      .row F.lab₃ (q.round - F.J3) (bitsToBytes ρ) (F.msg q.round (q.rt.map digToBytes) q.plain)
        (F.kind q.round) (F.work q.round) (F.nonce q.round q.plain) (F.work q.round)
    else .nothing
  | .f2 (some _) _ => .nothing
  | .f4 cms rtreq =>
    if q.round = F.J then
      .tail (firstCall F.lab₂ F.pd₂ (F.stm₂ cms rtreq q.plain) (F.run₂ q.plain))
    else .nothing
  | .f5 ρ =>
    if F.J + 1 ≤ q.round ∧ q.round ≤ F.J + F.n₂ then
      .row F.lab₂ (q.round - F.J) (bitsToBytes ρ) (F.msg q.round (q.rt.map digToBytes) q.plain)
        (F.kind q.round) (F.work q.round) (F.nonce q.round q.plain)
        (if q.round = F.J + F.n₂ then 1 else F.work q.round)
    else .nothing
  | .f3 ρ0 c =>
    if q.round = F.J3 then
      .tail (firstCall F.lab₃ F.pd₃ (F.stm₃ ρ0 c q.plain) (F.run₃ q.plain))
    else .nothing

/-- **The tie to `fbCallJ`.** -/
theorem onceJ_call (F : FileJ L t) (K : ℕ) (q : FbIn 256 L t) (j : Fin (K + 1)) :
    (onceJ F q).call K j = fbCallJ F K q j := by
  unfold onceJ fbCallJ
  generalize q.head = hd
  cases hd with
  | f1 cms x salt =>
    by_cases h0 : q.round = 0 <;> by_cases hj : j.val = K <;> simp [OnceJ.call, h0, hj]
  | f2 x ρ =>
    cases x with
    | none =>
      by_cases h1 : 1 ≤ q.round ∧ q.round ≤ F.n₁
      · simp only [if_pos h1]
        rfl
      · by_cases h3 : F.J3 + 1 ≤ q.round ∧ q.round ≤ F.J3 + F.n₃
        · simp only [if_neg h1, if_pos h3]
          rfl
        · simp only [if_neg h1, if_neg h3]
          rfl
    | some _ => rfl
  | f3 ρ0 c =>
    by_cases h0 : q.round = F.J3 <;> by_cases hj : j.val = K <;> simp [OnceJ.call, h0, hj]
  | f4 cms rtreq =>
    by_cases h0 : q.round = F.J <;> by_cases hj : j.val = K <;> simp [OnceJ.call, h0, hj]
  | f5 ρ =>
    by_cases h2 : F.J + 1 ≤ q.round ∧ q.round ≤ F.J + F.n₂
    · simp only [if_pos h2]
      rfl
    · simp only [if_neg h2]
      rfl

/-! ## One reading of the plain part -/

section
variable {TF TJ T3 : Type}

/-- **What the calls of a chain query share, at the data of `fillJ`, from one reading p of the
query's plain part.** -/
def onceP (D : WholeD) (S : SilentJ X TF TJ T3) (p : PartJ TF TJ T3) (q : FbIn 256 L t) : OnceJ :=
  let msg : ByteArray := match p with
    | .row i' m _ => if i' = q.round then m (q.rt.map digToBytes) else ByteArray.empty
    | _ => ByteArray.empty
  let nonce : ℕ := match p with
    | .row i' _ n => if i' = q.round then n else 0
    | _ => 0
  let n₁ := D.ds₁.length
  let n₂ := D.ds₂.length
  let n₃ := D.ds₃.length
  match q.head with
  | .f1 cms x salt =>
    if q.round = 0 then
      .tail (firstCall S.lab₁ S.pd₁ (match p with
        | .front a => S.stm₁ cms x a
        | _ => ByteArray.empty) salt)
    else .nothing
  | .f2 none ρ =>
    if 1 ≤ q.round ∧ q.round ≤ n₁ then
      .row S.lab₁ q.round (bitsToBytes ρ) msg (kindAt D q.round) (workAt D q.round) nonce
        (workAt D q.round)
    else if n₁ + n₂ + 2 + 1 ≤ q.round ∧ q.round ≤ n₁ + n₂ + 2 + n₃ then
      .row S.lab₃ (q.round - (n₁ + n₂ + 2)) (bitsToBytes ρ) msg (kindAt D q.round)
        (workAt D q.round) nonce (workAt D q.round)
    else .nothing
  | .f2 (some _) _ => .nothing
  | .f4 cms rtreq =>
    if q.round = n₁ + 1 then
      .tail (firstCall S.lab₂ S.pd₂ (match p with
        | .join a => S.stm₂ cms rtreq a
        | _ => ByteArray.empty) (match p with
        | .join a => S.run₂ a
        | _ => []))
    else .nothing
  | .f5 ρ =>
    if n₁ + 1 + 1 ≤ q.round ∧ q.round ≤ n₁ + 1 + n₂ then
      .row S.lab₂ (q.round - (n₁ + 1)) (bitsToBytes ρ) msg (kindAt D q.round) (workAt D q.round)
        nonce (if q.round = n₁ + 1 + n₂ then 1 else workAt D q.round)
    else .nothing
  | .f3 ρ0 c =>
    if q.round = n₁ + n₂ + 2 then
      .tail (firstCall S.lab₃ S.pd₃ (match p with
        | .seam a => S.stm₃ ρ0 c a
        | _ => ByteArray.empty) (match p with
        | .seam a => S.run₃ a
        | _ => []))
    else .nothing

/-- The same, with the reading `part` called once. -/
def onceFill (D : WholeD) (S : SilentJ X TF TJ T3) (part : PBt L t → PartJ TF TJ T3)
    (q : FbIn 256 L t) : OnceJ :=
  onceP D S (part q.plain) q

/-- **The tie to `fillJ`**: at the reading `partAt`. -/
theorem onceFill_eq (C : _root_.Run.PQ.CK) (D : WholeD) (tF : TF) (tJ : TJ) (t3 : T3)
    (rd : PBt L t → Option (PlainPart (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann))
    (S : SilentJ X TF TJ T3) (q : FbIn 256 L t) :
    onceFill D S (partAt C D tF tJ t3 rd) q = onceJ (fillJ C D tF tJ t3 rd S) q := by
  unfold onceFill onceP onceJ
  generalize q.head = hd
  cases hd with
  | f1 cms x salt => rfl
  | f2 x ρ =>
    cases x with
    | none => rfl
    | some _ => rfl
  | f3 ρ0 c => rfl
  | f4 cms rtreq => rfl
  | f5 ρ => rfl

end

end Johnson.RunOne

#print axioms Johnson.RunOne.onceJ_call
#print axioms Johnson.RunOne.onceFill_eq
