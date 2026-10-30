-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/SeedPoints.lean: partial codes of the two typed queries by which the compiled
verifier for an object with records draws a record's seed, as the strings that the programs hash;
the two as one code of chain queries under the seeds' tag; and what an encoding that takes that code
in reads out of the single oracle at the two queries.

The seeds of a stored table's record are drawn on a chain of hash calls of its own: the call number
160 under the label `Fmt.recordLabel` on the table's name; then the calls number 162 of one round,
which start from the first call's value. The typed verifier asks two queries under one tag:
  `q0 cm` := ⟨round 1, head f1 (cm :: cfgL) none sh, no root, p0⟩: the table's name in typed pieces;
  `q1 v`  := ⟨round 2, head f2 none v, no root, p1⟩: the chain value of the first answer.
OnBytes/TypedOracleCompiler/Run/FirstName.lean and SeedRound.lean have codes for two other typed forms (round 0 with
the head f1 [cm] none []; round 1). Here their strings are written at the forms above.

The interface L, the tag t, the fixed plain parts with their tests, the typed pieces cfgL and sh,
and the bytes `rest` that stand behind the root in a name are parameters. Nothing ties cfgL and sh
to `rest`: they are constants of the typed form, and a query with other constants is not written.

Main definitions: `q0`, `q1`, `s0`, `s1`, `fbSeeds`, `TakesIn`.
Main theorems.
 `s0_put`        at `q0 cm`: the bits of the string of the call 160 under the seeds' label, with 32
                 zero bytes for the parameters' digest and the statement `digToBytes cm ++ rest`.
 `s1_put`        at `q1 v` and the typed block j, for v of 256 bits and K below 2 ^ 48: the bits of
                 the string of one half of the call 162 under the seeds' label, ROUND 1, start v's
                 bytes.
 `s0_is`, `s1_is`, `fbSeeds_is`: every string has the form of a call 160, or 162, under that label.
 `fbSeeds_q0`, `fbSeeds_q1`: what the joint code writes at the two queries.
 `read_q0`, `read_q1`: for a page (OnBytes/TypedOracleCompiler/Run/PageG.lean) that takes the joint code in: the
                 chain value that its encoding reads out of `oBits` at `q0 cm` is the format's
                 oracle's answer at the first string; digest k at `q1 v` is its answer at the string
                 of block k + 1.

Not claimed. That a page takes the code in together with other codes under the same tag: whoever
gives the page shows that the strings are apart (`fbSeeds_is` is for that). The blocks of the first
answer other than its chain value have no string. That any program hashes these strings:
OnBytes/K/SeedBytes.lean. Nothing on soundness.


-/
import OnBytes.TypedOracleCompiler.Run.FirstName
import OnBytes.TypedOracleCompiler.Run.SeedRound
import OnBytes.TypedOracleCompiler.Run.PageG
import OnBytes.TypedOracleCompiler.Run.SeamAt
import Run.CodingAgree

set_option autoImplicit false

namespace TypedOracleCompiler.Run.SeedPoints
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open TypedOracleCompiler.Run.Apart TypedOracleCompiler.Run.SeamAt TypedOracleCompiler.Run.PutSome
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run

variable {I X : Type} (L : BatchProtocolWithLeafBody I X) (t : Tag) (p0 p1 : PlainPart (shapeOf L t) (annOf L t))
  (isP0 isP1 : PlainPart (shapeOf L t) (annOf L t) → Bool) (cfgL : List (Dig 256)) (sh : Bits)

/-- The first typed query of a seed. -/
def q0 (cm : Dig 256) : FbIn 256 L t := ⟨1, .f1 (cm :: cfgL) none sh, [], p0⟩

/-- The second typed query of a seed. -/
def q1 (v : Bits) : FbIn 256 L t := ⟨2, .f2 none v, [], p1⟩

/-! ## The first query -/

/-- A query of the first form, as (32 zero bytes as a digest, root, no salt). -/
def sel0 (q : FbIn 256 L t) : Option (Dig 256 × Option (Dig 256) × List Bool) :=
  match q.round, q.head, q.rt with
  | 1, .f1 (cm :: c) none s, [] =>
      if c = cfgL ∧ s = sh ∧ isP0 q.plain = true then some (FirstName.zeroPd, some cm, [])
      else none
  | _, _, _ => none

/-- The way back. -/
def mk0 (a : Dig 256 × Option (Dig 256) × List Bool) : Option (FbIn 256 L t) :=
  match a.2.1, a.2.2 with
  | some cm, [] => if a.1 = FirstName.zeroPd then some (q0 L t p0 cfgL sh cm) else none
  | _, _ => none

variable (hp0 : ∀ p, isP0 p = true ↔ p = p0) (hp1 : ∀ p, isP1 p = true ↔ p = p1)

include hp0 in
/-- What `sel0` reads: the query's fields. -/
theorem sel0_some (q : FbIn 256 L t) (a : Dig 256 × Option (Dig 256) × List Bool)
    (h : sel0 L t isP0 cfgL sh q = some a) :
    ∃ cm, q = q0 L t p0 cfgL sh cm ∧ a = (FirstName.zeroPd, some cm, []) := by
  obtain ⟨round, head, rt, plain⟩ := q
  unfold sel0 at h
  split at h
  · rename_i cm c s e1 e2 e3
    have e1' : round = 1 := e1
    have e2' : head = .f1 (cm :: c) none s := e2
    have e3' : rt = [] := e3
    have h' : (if c = cfgL ∧ s = sh ∧ isP0 plain = true then
        some (FirstName.zeroPd, some cm, ([] : List Bool)) else none) = some a := h
    by_cases hq : c = cfgL ∧ s = sh ∧ isP0 plain = true
    · rw [if_pos hq] at h'
      refine ⟨cm, ?_, (Option.some.inj h').symm⟩
      rw [e1', e2', e3', hq.1, hq.2.1, (hp0 plain).1 hq.2.2]
      rfl
    · rw [if_neg hq] at h'
      cases h'
  · cases h

/-- `sel0` at a query of the form. -/
theorem sel0_q0 (h0 : isP0 p0 = true) (cm : Dig 256) :
    sel0 L t isP0 cfgL sh (q0 L t p0 cfgL sh cm) = some (FirstName.zeroPd, some cm, []) :=
  if_pos ⟨rfl, rfl, h0⟩

include hp0 in
theorem mk0_sel0 (q : FbIn 256 L t) (a : Dig 256 × Option (Dig 256) × List Bool)
    (h : sel0 L t isP0 cfgL sh q = some a) : mk0 L t p0 cfgL sh a = some q := by
  obtain ⟨cm, rfl, rfl⟩ := sel0_some L t p0 isP0 cfgL sh hp0 q a h
  show (if FirstName.zeroPd = FirstName.zeroPd then some (q0 L t p0 cfgL sh cm) else none) = _
  rw [if_pos (Eq.refl FirstName.zeroPd)]

include hp0 in
theorem sel0_mk0 (a : Dig 256 × Option (Dig 256) × List Bool) (q : FbIn 256 L t)
    (h : mk0 L t p0 cfgL sh a = some q) : sel0 L t isP0 cfgL sh q = some a := by
  obtain ⟨p, x, salt⟩ := a
  cases x with
  | none => cases h
  | some cm =>
    cases salt with
    | cons _ _ => cases h
    | nil =>
      have h0 : (if p = FirstName.zeroPd then some (q0 L t p0 cfgL sh cm) else none) = some q := h
      by_cases hpd : p = FirstName.zeroPd
      · rw [if_pos hpd] at h0
        rw [← Option.some.inj h0, hpd]
        exact sel0_q0 L t p0 isP0 cfgL sh ((hp0 p0).2 rfl) cm
      · rw [if_neg hpd] at h0
        cases h0

variable (rest : ByteArray)

/-- **The first query's code.** -/
def s0 : PCode (FbIn 256 L t) :=
  (FirstName.first0N rest _root_.Fmt.recordLabel).pull (sel0 L t isP0 cfgL sh)
    (mk0 L t p0 cfgL sh) (mk0_sel0 L t p0 isP0 cfgL sh hp0) (sel0_mk0 L t p0 isP0 cfgL sh hp0)

/-- **What it writes at `q0 cm`**, for fixed bytes of fewer than 2 ^ 32. -/
theorem s0_put (cm : Dig 256) (hr : rest.size < 2 ^ 32) :
    (s0 L t p0 isP0 cfgL sh hp0 rest).put (q0 L t p0 cfgL sh cm) =
      some (bytesToBits (_root_.Fmt.oStr 0 160 0 _root_.Fmt.recordLabel _root_.Fmt.zero32
        (_root_.Fmt.firstBytes _root_.Fmt.zero32 (digToBytes cm ++ rest) ByteArray.empty none))) :=
        by
  show (sel0 L t isP0 cfgL sh _).bind _ = _
  rw [sel0_q0 L t p0 isP0 cfgL sh ((hp0 p0).2 rfl) cm, ← FirstName.zeroPd_bytes]
  exact pFirst0_put _root_.Fmt.recordLabel (FirstName.stmN rest) (FirstName.unstmN rest)
    (FirstName.unstm_stmN rest) (FirstName.stm_unstmN rest) FirstName.zeroPd (some cm) [] _ rfl
    (by rw [ByteArray.size_append, size_digToBytes]; omega) (Or.inl rfl)

/-- Every string of the first code has the form of a call 160 under the seeds' label. -/
theorem s0_is (q : FbIn 256 L t) (s : List Bool)
    (h : (s0 L t p0 isP0 cfgL sh hp0 rest).put q = some s) : Is160 _root_.Fmt.recordLabel s := by
  obtain ⟨a, -, ha⟩ := PCode.pull_put _ _ _ _ _ q s h
  exact is160_of_hdr _ _ (pFirst0_hdr _ _ _ _ _ a s ha)

/-- Whatever the first code writes, it writes at a query of the first form. -/
theorem s0_only (q : FbIn 256 L t) (s : List Bool)
    (h : (s0 L t p0 isP0 cfgL sh hp0 rest).put q = some s) : ∃ cm, q = q0 L t p0 cfgL sh cm := by
  obtain ⟨a, ha, -⟩ := PCode.pull_put _ _ _ _ _ q s h
  obtain ⟨cm, e, -⟩ := sel0_some L t p0 isP0 cfgL sh hp0 q a ha
  exact ⟨cm, e⟩

/-! ## The second query -/

variable (K : ℕ)

/-- A query of the second form with a block, as the query of round 1 with that block. -/
def sel1 (x : FbIn 256 L t × Fin (K + 1)) : Option (FbIn 256 L t × Fin (K + 1)) :=
  match x.1.round, x.1.head, x.1.rt with
  | 2, .f2 none v, [] =>
      if isP1 x.1.plain = true then some (⟨1, .f2 none v, [], p1⟩, x.2) else none
  | _, _, _ => none

/-- The way back. -/
def mk1 (y : FbIn 256 L t × Fin (K + 1)) : Option (FbIn 256 L t × Fin (K + 1)) :=
  match y.1.round, y.1.head, y.1.rt with
  | 1, .f2 none v, [] => if isP1 y.1.plain = true then some (q1 L t p1 v, y.2) else none
  | _, _, _ => none

include hp1 in
theorem sel1_some (x y : FbIn 256 L t × Fin (K + 1)) (h : sel1 L t p1 isP1 K x = some y) :
    ∃ v, x = (q1 L t p1 v, x.2) ∧ y = (⟨1, .f2 none v, [], p1⟩, x.2) := by
  obtain ⟨⟨round, head, rt, plain⟩, j⟩ := x
  unfold sel1 at h
  split at h
  · rename_i v e1 e2 e3
    have e1' : round = 2 := e1
    have e2' : head = .f2 none v := e2
    have e3' : rt = [] := e3
    have h' : (if isP1 plain = true then
        some ((⟨1, .f2 none v, [], p1⟩ : FbIn 256 L t), j) else none) = some y := h
    by_cases hq : isP1 plain = true
    · rw [if_pos hq] at h'
      refine ⟨v, ?_, (Option.some.inj h').symm⟩
      rw [e1', e2', e3', (hp1 plain).1 hq]
      rfl
    · rw [if_neg hq] at h'
      cases h'
  · cases h

theorem sel1_q1 (h1 : isP1 p1 = true) (v : Bits) (j : Fin (K + 1)) :
    sel1 L t p1 isP1 K (q1 L t p1 v, j) = some (⟨1, .f2 none v, [], p1⟩, j) :=
  if_pos h1

include hp1 in
theorem mk1_sel1 (x y : FbIn 256 L t × Fin (K + 1)) (h : sel1 L t p1 isP1 K x = some y) :
    mk1 L t p1 isP1 K y = some x := by
  obtain ⟨v, ex, rfl⟩ := sel1_some L t p1 isP1 hp1 K x y h
  rw [ex]
  exact if_pos ((hp1 p1).2 rfl)

include hp1 in
theorem sel1_mk1 (y x : FbIn 256 L t × Fin (K + 1)) (h : mk1 L t p1 isP1 K y = some x) :
    sel1 L t p1 isP1 K x = some y := by
  obtain ⟨⟨round, head, rt, plain⟩, j⟩ := y
  unfold mk1 at h
  split at h
  · rename_i v e1 e2 e3
    have e1' : round = 1 := e1
    have e2' : head = .f2 none v := e2
    have e3' : rt = [] := e3
    have h' : (if isP1 plain = true then some (q1 L t p1 v, j) else none) = some x := h
    by_cases hq : isP1 plain = true
    · rw [if_pos hq] at h'
      rw [← Option.some.inj h', sel1_q1 L t p1 isP1 K ((hp1 p1).2 rfl) v j, e1', e2', e3',
        (hp1 plain).1 hq]
    · rw [if_neg hq] at h'
      cases h'
  · cases h

/-- **The second query's code**, with the number of a block of the answer. -/
def s1 : PCode (FbIn 256 L t × Fin (K + 1)) :=
  (SeedRound.secondPS L t p1 isP1 hp1 K).pull (sel1 L t p1 isP1 K) (mk1 L t p1 isP1 K)
    (mk1_sel1 L t p1 isP1 hp1 K) (sel1_mk1 L t p1 isP1 hp1 K)

/-- **What it writes at `q1 v` and the typed block j.** -/
theorem s1_put (hK : K < 2 ^ 48) (v : Bits) (hv : v.length = 256) (j : Fin (K + 1)) :
    (s1 L t p1 isP1 hp1 K).put (q1 L t p1 v, j) =
      some (bytesToBits (_root_.Fmt.oStr (UInt8.ofNat (blockNo 0 K j % 2)) 162
        _root_.Fmt.recordLabel 1 (bitsToBytes v)
        (ByteArray.empty ++ _root_.Fmt.tail .seeds 0 0 (blockNo 0 K j / 2)))) := by
  show (sel1 L t p1 isP1 K _).bind _ = _
  rw [sel1_q1 L t p1 isP1 K ((hp1 p1).2 rfl) v j]
  exact SeedRound.secondPS_put L t p1 isP1 hp1 K hK v hv j

/-- Every string of the second code has the form of a call 162 under the seeds' label. -/
theorem s1_is (x : FbIn 256 L t × Fin (K + 1)) (s : List Bool)
    (h : (s1 L t p1 isP1 hp1 K).put x = some s) : Is162 _root_.Fmt.recordLabel s := by
  obtain ⟨y, -, hy⟩ := PCode.pull_put _ _ _ _ _ x s h
  obtain ⟨hb, ρ, r, hρ, rfl⟩ := p162_shape _ K y s hy
  refine ⟨?_, fun b h0 h1 => ?_⟩
  · unfold lw1
    rw [← List.append_assoc, ← List.append_assoc, List.drop_left'
      (by rw [List.length_append, List.length_append, length_bitsOfByte, length_mid32, hρ])]
    exact List.take_left' (length_u64n _)
  · cases hb
    · exact byte_prefix b 0 h0 _
    · exact byte_prefix b 1 h1 _

/-! ## The two as one code under the seeds' tag -/

/-- **The code of the seeds' two queries, each with a block**: by the typed round. -/
def fbSeeds : PCode (FbIn 256 L t × Fin (K + 1)) :=
  split (tailP (s0 L t p0 isP0 cfgL sh hp0 rest) K) (s1 L t p1 isP1 hp1 K)
    (fun x => decide (x.1.round = 1)) (fun a b s h1 h2 =>
      no_160_162 _ _ (by decide) s (s0_is L t p0 isP0 cfgL sh hp0 rest _ s (tailP_put _ K a s h1).1)
        (s1_is L t p1 isP1 hp1 K b s h2))

/-- What is known of every string of the joint code. -/
theorem fbSeeds_is (x : FbIn 256 L t × Fin (K + 1)) (s : List Bool)
    (h : (fbSeeds L t p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K).put x = some s) :
    Is160 _root_.Fmt.recordLabel s ∨ Is162 _root_.Fmt.recordLabel s := by
  rcases split_put _ _ _ _ x s h with h1 | h1
  · exact Or.inl (s0_is L t p0 isP0 cfgL sh hp0 rest _ s (tailP_put _ K x s h1).1)
  · exact Or.inr (s1_is L t p1 isP1 hp1 K x s h1)

/-- At the first query, at the block of the chain value. -/
theorem fbSeeds_q0 (cm : Dig 256) (hr : rest.size < 2 ^ 32) :
    (fbSeeds L t p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K).put (q0 L t p0 cfgL sh cm, Fin.last K) =
      some (bytesToBits (_root_.Fmt.oStr 0 160 0 _root_.Fmt.recordLabel _root_.Fmt.zero32
        (_root_.Fmt.firstBytes _root_.Fmt.zero32 (digToBytes cm ++ rest) ByteArray.empty none))) :=
        by
  unfold fbSeeds
  rw [split_true _ _ (fun x : FbIn 256 L t × Fin (K + 1) => decide (x.1.round = 1)) _
    (q0 L t p0 cfgL sh cm, Fin.last K) rfl]
  exact tailP_some _ K _ _ (s0_put L t p0 isP0 cfgL sh hp0 rest cm hr)

/-- At the second query, at every block. -/
theorem fbSeeds_q1 (hK : K < 2 ^ 48) (v : Bits) (hv : v.length = 256) (j : Fin (K + 1)) :
    (fbSeeds L t p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K).put (q1 L t p1 v, j) =
      some (bytesToBits (_root_.Fmt.oStr (UInt8.ofNat (blockNo 0 K j % 2)) 162
        _root_.Fmt.recordLabel 1 (bitsToBytes v)
        (ByteArray.empty ++ _root_.Fmt.tail .seeds 0 0 (blockNo 0 K j / 2)))) := by
  unfold fbSeeds
  rw [split_false _ _ (fun x : FbIn 256 L t × Fin (K + 1) => decide (x.1.round = 1)) _
    (q1 L t p1 v, j) rfl]
  exact s1_put L t p1 isP1 hp1 K hK v hv j

/-! ## What an encoding that takes the code in reads out of the single oracle -/

/-- No string of the joint code begins with the byte 4. -/
theorem fbSeeds_not4 (x : FbIn 256 L t × Fin (K + 1)) (s : List Bool)
    (h : (fbSeeds L t p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K).put x = some s) :
    ¬ bitsOfByte 4 <+: s := by
  rcases fbSeeds_is L t p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K x s h with g | g
  · exact g.2.2 4 (by decide)
  · exact g.2 4 (by decide) (by decide)

/-- The page takes the seeds' code in: where the joint code writes, the page's partial code of the
real points writes the same string at that chain query and block under the tag t. -/
def TakesIn (C : PageG.Page L K) : Prop :=
  ∀ x s, (fbSeeds L t p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K).put x = some s →
    C.real.put (.inr (.inr (.inr (.inr (.inl ⟨t, x⟩))))) = some s

/-- **The first query**: the chain value that the page's encoding reads out of `oBits` is the
format's oracle's answer at the string of the call 160 on the root and the fixed bytes. -/
theorem read_q0 (C : PageG.Page L K)
    (hC : TakesIn L t p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K C) (cm : Dig 256)
    (hr : rest.size < 2 ^ 32) :
    (readBlocks (PageG.implG C) oBits (.fb t) (q0 L t p0 cfgL sh cm) :
        (Fin K → Dig 256) × Dig 256).2 =
      bytesToDig (_root_.Fmt.oracle (_root_.Fmt.oStr 0 160 0 _root_.Fmt.recordLabel
        _root_.Fmt.zero32
        (_root_.Fmt.firstBytes _root_.Fmt.zero32 (digToBytes cm ++ rest) ByteArray.empty none))) :=
        by
  have hp := fbSeeds_q0 L t p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K cm hr
  have h4 := fbSeeds_not4 L t p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K _ _ hp
  show oBits () ((PageG.implG C).code (.fb t) (q0 L t p0 cfgL sh cm) (Fin.last K)) = _
  rw [PageG.implG_fb C t _ _ _ (hC _ _ hp)]
  exact oBits_call ⟨0, 160, 0, _root_.Fmt.recordLabel, _root_.Fmt.zero32, _⟩ h4

/-- **The second query**: digest k that the page's encoding reads out of `oBits` is the format's
oracle's answer at the string of block k + 1 of the seeds' round from v. -/
theorem read_q1 (C : PageG.Page L K)
    (hC : TakesIn L t p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K C) (hK : K < 2 ^ 48) (v : Bits)
    (hv : v.length = 256) (k : Fin K) :
    (readBlocks (PageG.implG C) oBits (.fb t) (q1 L t p1 v) : (Fin K → Dig 256) × Dig 256).1 k =
      bytesToDig (_root_.Fmt.oracle (_root_.Fmt.oStr (UInt8.ofNat ((k.val + 1) % 2)) 162
        _root_.Fmt.recordLabel 1 (bitsToBytes v)
        (ByteArray.empty ++ _root_.Fmt.tail .seeds 0 0 ((k.val + 1) / 2)))) := by
  have hp := fbSeeds_q1 L t p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K hK v hv k.castSucc
  rw [SeedRound.blockNo_cast] at hp
  have h4 := fbSeeds_not4 L t p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K _ _ hp
  show oBits () ((PageG.implG C).code (.fb t) (q1 L t p1 v) k.castSucc) = _
  rw [PageG.implG_fb C t _ _ _ (hC _ _ hp)]
  exact oBits_call ⟨UInt8.ofNat ((k.val + 1) % 2), 162, _root_.Fmt.recordLabel, 1, bitsToBytes v, _⟩
    h4

end TypedOracleCompiler.Run.SeedPoints
