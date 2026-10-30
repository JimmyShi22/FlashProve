-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/ChainsQ.lean: the chains' seven laws (OnBytes/Maker/Page/Chains.lean) from two
records that ask less: of the family's answer at the sealing call only at queries that meet a
condition, and of a round's queries that they meet the chain queries' condition only under the three
premises that the row laws have themselves.

Definitions, statements and proofs. `Speaks.slot` speaks of every query of the sealing call, though
the call's string is made of the round's number and the chain's value alone: two queries that differ
in their roots or their plain part get one string. A family that is read through a one-to-one code
meets `Speaks.slot` only where O has one answer at two strings. `RoundFitsJ.ours` asks the chain
queries' condition of every string of bits and every list of roots. The laws that are wanted speak
of a value of 256 bits, as many roots as the round sends trees, and a nonce below 2 ^ 64; and of the
sealing call at no roots and one plain part.

Main names:
  `SpeaksQ g t F O Q Qg`: `Speaks` with `slot` under the condition Qg. `Speaks.toQ`: from `Speaks`,
    at every Qg.
  `RoundFitsQ`: `RoundFitsJ` with `ours` under the three premises. `RoundFitsJ.toQ`.
  `FitsEndQ`, `FitsShEQ`: a stretch's rounds. `FitsEnd.toQ`, `FitsShE.toQ`.
  The seven laws: `rowEndQ₁`, `rowShEQ₂`, `rowEndQ₃`, `SpeaksQ.gAt`, `s0Q_of`, `s4Q_of`, `s3Q_of`,
    each with the conclusion of its like in Chains.lean.
No letter stands under "there is".
Limits: no family is shown here to meet `SpeaksQ` but through `Speaks`. Whether a family that meets
it is an encoding in the sense of the soundness theorem is not said. Nothing on soundness.


-/
import OnBytes.Maker.Page.Chains

set_option autoImplicit false

namespace OnBytes.Maker.Page

open TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop Rom
open _root_.Compile hiding ON
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run
open _root_.Run.PQ (CK first_bytes size_HO32)
open TypedOracleCompiler.Run.PQ TypedOracleCompiler.Run.Twin TypedOracleCompiler.Run.Thin
open _root_.Run.Twin (allLo)

variable {I X : Type} {L : BatchProtocolWithLeafBody I X} {t : Tag} {K : ℕ}

/-! ## The two records -/

/-- Wherever the file's data give a call, g answers with O at that call's string: at a chain query
that meets Q, and at a query of the sealing call that meets Qg. -/
structure SpeaksQ (g : Fam (typedOracleFamily 256 (K + 1) L)) (t : Tag) (F : FileJ L t)
    (O : ByteArray → ByteArray) (Q : FbIn 256 L t → Prop) (Qg : JoiningRoundQuery 256 L t → Prop) : Prop where
  /-- a block of the verifier's side -/
  blk : ∀ (q : FbIn 256 L t) (k : Fin (K + 1)) (c : Fmt.OQ), Q q →
    fbCallJ F (K + 1) q k.castSucc = some c →
    (g (OracleName.fb t) q : (Fin (K + 1) → Dig 256) × Dig 256).1 k = bytesToDig (O (strOf c))
  /-- the tail -/
  tail : ∀ (q : FbIn 256 L t) (c : Fmt.OQ), Q q →
    fbCallJ F (K + 1) q (Fin.last (K + 1)) = some c →
    (g (OracleName.fb t) q : (Fin (K + 1) → Dig 256) × Dig 256).2 = bytesToDig (O (strOf c))
  /-- the slot value -/
  slot : ∀ (q : JoiningRoundQuery 256 L t) (c : Fmt.OQ), Qg q → gCallJ F q = some c →
    (g (OracleName.g t) q : Dig 256) = bytesToDig (O (strOf c))

/-- From the record without the second condition, at every such condition. -/
theorem Speaks.toQ {g : Fam (typedOracleFamily 256 (K + 1) L)} {F : FileJ L t} {O : ByteArray → ByteArray}
    {Q : FbIn 256 L t → Prop} (S : Speaks g t F O Q) (Qg : JoiningRoundQuery 256 L t → Prop) :
    SpeaksQ g t F O Q Qg :=
  ⟨S.blk, S.tail, fun q c _ h => S.slot q c h⟩

/-- At narrower conditions. -/
theorem SpeaksQ.mono {g : Fam (typedOracleFamily 256 (K + 1) L)} {F : FileJ L t} {O : ByteArray → ByteArray}
    {Q Q' : FbIn 256 L t → Prop} {Qg Qg' : JoiningRoundQuery 256 L t → Prop} (S : SpeaksQ g t F O Q Qg)
    (h : ∀ q, Q' q → Q q) (hg : ∀ q, Qg' q → Qg q) : SpeaksQ g t F O Q' Qg' :=
  ⟨fun q k c hq => S.blk q k c (h q hq), fun q c hq => S.tail q c (h q hq),
    fun q c hq => S.slot q c (hg q hq)⟩

/-- What a row law needs of the file's data at one typed round. -/
structure RoundFitsQ (F : FileJ L t) (Q : FbIn 256 L t → Prop) (C : CK) (hd : Bits → Head 256 X)
    (d : RD) (e : (roundS C d).Plain → PBt L t) (i : ℕ) : Prop where
  ours : ∀ (ρ : Bits) (rt : List (Dig 256)) (pl : (roundS C d).Plain), ρ.length = 256 →
    rt.length = d.trees.length → GPlain.nonce (b := d.entry.work) pl < 2 ^ 64 →
    Q ⟨i, hd ρ, rt, e pl⟩
  kind : F.kind i = d.kind.num
  work : F.work i = d.entry.work
  msg : ∀ (bs : List ByteArray) (pl : (roundS C d).Plain),
    F.msg i bs (e pl) = bytesL bs d.items (GPlain.old (b := d.entry.work) pl)
  nonce : ∀ pl : (roundS C d).Plain, F.nonce i (e pl) = GPlain.nonce (b := d.entry.work) pl

theorem RoundFitsJ.toQ {F : FileJ L t} {Q : FbIn 256 L t → Prop} {C : CK}
    {hd : Bits → Head 256 X} {d : RD} {e : (roundS C d).Plain → PBt L t} {i : ℕ}
    (R : RoundFitsJ F Q C hd d e i) : RoundFitsQ F Q C hd d e i :=
  ⟨fun ρ rt pl _ _ _ => R.ours ρ rt pl, R.kind, R.work, R.msg, R.nonce⟩

/-! ## One round -/

section One
variable {g : Fam (typedOracleFamily 256 (K + 1) L)} {F : FileJ L t} {O : ByteArray → ByteArray}
  {Q : FbIn 256 L t → Prop} {Qg : JoiningRoundQuery 256 L t → Prop} (hO : ∀ s, (O s).size = 32)
  (S : SpeaksQ g t F O Q Qg) {C : CK} {d : RD} {e : (roundS C d).Plain → PBt L t} {i : ℕ}
include hO S

/-- The row, from the call of every block. lab, n: the call's label and index. -/
theorem rowQ_of_calls (hd : Bits → Head 256 X) (R : RoundFitsQ F Q C hd d e i) (lab n : ℕ)
    (hc : ∀ (ρ : Bits) (rt : List (Dig 256)) (pl : (roundS C d).Plain) (j : Fin (K + 1 + 1)),
      fbCallJ F (K + 1) (⟨i, hd ρ, rt, e pl⟩ : FbIn 256 L t) j =
        some (rowCall lab n ρ (F.msg i (rt.map digToBytes) (e pl)) (F.kind i) (F.work i)
          (F.nonce i (e pl)) (F.work i) (K + 1) j)) :
    RowAt (fun _ => L) C K g t O lab hd d e i n := by
  intro ρ rt pl a1 a2 a3
  refine ⟨fun k => ?_, ?_⟩
  · rw [S.blk _ k _ (R.ours ρ rt pl a1 a2 a3) (hc ρ rt pl k.castSucc), R.kind, R.work, R.msg,
      R.nonce, rowCall_block O hO]
  · rw [S.tail _ _ (R.ours ρ rt pl a1 a2 a3) (hc ρ rt pl (Fin.last (K + 1))), R.kind, R.work,
      R.msg, R.nonce, rowCall_block O hO, blockNo_last]

/-- A round of the first chain. -/
theorem rowAtQ_lo₁ (R : RoundFitsQ F Q C (fun ρ => .f2 none ρ) d e i) (h1 : 1 ≤ i)
    (h2 : i ≤ F.n₁) : RowAt (fun _ => L) C K g t O F.lab₁ (fun ρ => .f2 none ρ) d e i i :=
  rowQ_of_calls hO S _ R _ _ fun ρ rt pl j => by
    show (if 1 ≤ i ∧ i ≤ F.n₁ then _ else _) = _
    rw [if_pos ⟨h1, h2⟩]

/-- A round of the third chain. -/
theorem rowAtQ_lo₃ (R : RoundFitsQ F Q C (fun ρ => .f2 none ρ) d e i) (h1 : F.J3 + 1 ≤ i)
    (h2 : i ≤ F.J3 + F.n₃) :
    RowAt (fun _ => L) C K g t O F.lab₃ (fun ρ => .f2 none ρ) d e i (i - F.J3) :=
  rowQ_of_calls hO S _ R _ _ fun ρ rt pl j => by
    show (if 1 ≤ i ∧ i ≤ F.n₁ then _ else if F.J3 + 1 ≤ i ∧ i ≤ F.J3 + F.n₃ then _ else _) = _
    rw [if_neg (by unfold FileJ.J3 at h1; omega), if_pos ⟨h1, h2⟩]

/-- A round of the shared chain that is not its last. -/
theorem rowAtQ_sh (R : RoundFitsQ F Q C (fun ρ => .f5 ρ) d e i) (h1 : F.J + 1 ≤ i)
    (h2 : i < F.J + F.n₂) :
    RowAt (fun _ => L) C K g t O F.lab₂ (fun ρ => .f5 ρ) d e i (i - F.J) :=
  rowQ_of_calls hO S _ R _ _ fun ρ rt pl j => by
    show (if F.J + 1 ≤ i ∧ i ≤ F.J + F.n₂ then _ else _) = _
    rw [if_pos ⟨h1, Nat.le_of_lt h2⟩]
    show some (rowCall _ _ _ _ _ _ _ (if i = F.J + F.n₂ then 1 else F.work i) _ _) = _
    rw [if_neg (Nat.ne_of_lt h2)]

/-- The last round of the shared chain: the typed tail is the row's block 1. -/
theorem sealAtQ_sh (R : RoundFitsQ F Q C (fun ρ => .f5 ρ) d e i) (h1 : 1 ≤ F.n₂)
    (h2 : i = F.J + F.n₂) : SealAt (fun _ => L) C K g t O F.lab₂ d e i (i - F.J) := by
  intro ρ rt pl a1 a2 a3
  have hc : fbCallJ F (K + 1) (⟨i, .f5 ρ, rt, e pl⟩ : FbIn 256 L t) (Fin.last (K + 1)) =
      some (rowCall F.lab₂ (i - F.J) ρ (F.msg i (rt.map digToBytes) (e pl)) (F.kind i) (F.work i)
        (F.nonce i (e pl)) 1 (K + 1) (Fin.last (K + 1))) := by
    show (if F.J + 1 ≤ i ∧ i ≤ F.J + F.n₂ then _ else _) = _
    rw [if_pos ⟨by omega, Nat.le_of_eq h2⟩]
    show some (rowCall _ _ _ _ _ _ _ (if i = F.J + F.n₂ then 1 else F.work i) _ _) = _
    rw [if_pos h2]
  rw [S.tail _ _ (R.ours ρ rt pl a1 a2 a3) hc, R.kind, R.work, R.msg, R.nonce,
    rowCall_block O hO, blockNo_last]
  rfl

end One

/-! ## A stretch -/

/-- The file's data fit a stretch of local rounds with no tail, from the typed round i on. -/
def FitsEndQ (F : FileJ L t) (Q : FbIn 256 L t → Prop) (C : CK) : (ds : List RD) →
    (PlainPart (uL C ds) (allLo (SL C ds)) → PBt L t) → ℕ → Prop
  | [], _, _ => True
  | d :: ds, embP, i =>
    RoundFitsQ F Q C (fun ρ => .f2 none ρ) d (fun pl => embP (.inl (.inr pl))) i ∧
      FitsEndQ F Q C ds (fun z => embP (.inr z)) (i + 1)

/-- The file's data fit a stretch of shared rounds with no tail, from the typed round i on. -/
def FitsShEQ (F : FileJ L t) (Q : FbIn 256 L t → Prop) (C : CK) : (ds : List RD) →
    (PlainPart (uL C ds) (annShE C ds) → PBt L t) → ℕ → Prop
  | [], _, _ => True
  | d :: ds, embP, i =>
    RoundFitsQ F Q C (fun ρ => .f5 ρ) d (fun pl => embP (.inl (.inl pl))) i ∧
      FitsShEQ F Q C ds (fun z => embP (.inr z)) (i + 1)

theorem FitsEnd.toQ {F : FileJ L t} {Q : FbIn 256 L t → Prop} {C : CK} : ∀ {ds : List RD}
    {embP : PlainPart (uL C ds) (allLo (SL C ds)) → PBt L t} {i : ℕ}, FitsEnd F Q C ds embP i →
    FitsEndQ F Q C ds embP i
  | [], _, _, _ => trivial
  | _ :: _, _, _, h => ⟨h.1.toQ, FitsEnd.toQ h.2⟩

theorem FitsShE.toQ {F : FileJ L t} {Q : FbIn 256 L t → Prop} {C : CK} : ∀ {ds : List RD}
    {embP : PlainPart (uL C ds) (annShE C ds) → PBt L t} {i : ℕ}, FitsShE F Q C ds embP i →
    FitsShEQ F Q C ds embP i
  | [], _, _, _ => trivial
  | _ :: _, _, _, h => ⟨h.1.toQ, FitsShE.toQ h.2⟩

section Stretch
variable {g : Fam (typedOracleFamily 256 (K + 1) L)} {F : FileJ L t} {O : ByteArray → ByteArray}
  {Q : FbIn 256 L t → Prop} {Qg : JoiningRoundQuery 256 L t → Prop} (hO : ∀ s, (O s).size = 32)
  (S : SpeaksQ g t F O Q Qg) (C : CK)
include hO S

/-- The first chain's rounds from the typed round i on. -/
theorem rowEndQ₁ : ∀ (ds : List RD) (embP : PlainPart (uL C ds) (allLo (SL C ds)) → PBt L t) (i : ℕ),
    FitsEndQ F Q C ds embP i → 1 ≤ i → i + ds.length ≤ F.n₁ + 1 →
    RowEnd (fun _ => L) C K g t O F.lab₁ ds embP i i
  | [], _, _, _, _, _ => trivial
  | d :: ds, embP, i, h, h1, h2 => by
    have h2' : i + (ds.length + 1) ≤ F.n₁ + 1 := h2
    exact ⟨rowAtQ_lo₁ hO S h.1 h1 (by omega),
      rowEndQ₁ ds _ (i + 1) h.2 (by omega) (by omega)⟩

/-- The third chain's rounds from the typed round J3 + n on. -/
theorem rowEndQ₃ : ∀ (ds : List RD) (embP : PlainPart (uL C ds) (allLo (SL C ds)) → PBt L t) (n : ℕ),
    FitsEndQ F Q C ds embP (F.J3 + n) → 1 ≤ n → n + ds.length ≤ F.n₃ + 1 →
    RowEnd (fun _ => L) C K g t O F.lab₃ ds embP (F.J3 + n) n
  | [], _, _, _, _, _ => trivial
  | d :: ds, embP, n, h, h1, h2 => by
    have h2' : n + (ds.length + 1) ≤ F.n₃ + 1 := h2
    have r := rowAtQ_lo₃ hO S h.1 (by omega) (by omega)
    rw [Nat.add_sub_cancel_left] at r
    exact ⟨r, rowEndQ₃ ds _ (n + 1) h.2 (by omega) (by omega)⟩

/-- The shared chain's rounds from the typed round J + n on, to its last. -/
theorem rowShEQ₂ : ∀ (ds : List RD) (embP : PlainPart (uL C ds) (annShE C ds) → PBt L t) (n : ℕ),
    FitsShEQ F Q C ds embP (F.J + n) → 1 ≤ n → n + ds.length = F.n₂ + 1 →
    RowShE (fun _ => L) C K g t O F.lab₂ ds embP (F.J + n) n
  | [], _, _, _, _, _ => trivial
  | [d], embP, n, h, h1, h2 => by
    have h2' : n + 1 = F.n₂ + 1 := h2
    have r := sealAtQ_sh hO S h.1 (by omega) (by omega)
    rw [Nat.add_sub_cancel_left] at r
    exact r
  | d :: d' :: ds, embP, n, h, h1, h2 => by
    have h2' : n + (ds.length + 1 + 1) = F.n₂ + 1 := h2
    have r := rowAtQ_sh hO S h.1 (by omega) (by omega)
    rw [Nat.add_sub_cancel_left] at r
    exact ⟨r, rowShEQ₂ (d' :: ds) _ (n + 1) h.2 (by omega) (by
      show n + 1 + (ds.length + 1) = F.n₂ + 1
      omega)⟩

end Stretch

/-- **The law of the call in which the first chain is sealed.** hQ: the queries of which the law
speaks meet the second condition. -/
theorem SpeaksQ.gAt {g : Fam (typedOracleFamily 256 (K + 1) L)} {F : FileJ L t} {O : ByteArray → ByteArray}
    {Q : FbIn 256 L t → Prop} {Qg : JoiningRoundQuery 256 L t → Prop} (S : SpeaksQ g t F O Q Qg)
    (hO : ∀ s, (O s).size = 32) (e : PBt L t)
    (hQ : ∀ ρ : Bits, ρ.length = 256 → Qg ⟨F.J, ρ, [], e⟩) :
    GAt (fun _ => L) K g t O F.lab₁ e F.J F.J := by
  intro ρ hρ
  rw [S.slot _ _ (hQ ρ hρ) (if_pos rfl : gCallJ F (⟨F.J, ρ, [], e⟩ : JoiningRoundQuery 256 L t) = _),
    blockW_HO O hO, ← roundBytes_tail]
  rfl

/-! ## The first calls -/

section First
variable {g : Fam (typedOracleFamily 256 (K + 1) L)} {F : FileJ L t} {O : ByteArray → ByteArray}
  {Q : FbIn 256 L t → Prop} {Qg : JoiningRoundQuery 256 L t → Prop} (hO : ∀ s, (O s).size = 32)
  (S : SpeaksQ g t F O Q Qg) {Sp : Fmt.SpecX} {o : Fmt.ChainOut} {st rnd run : ByteArray}
include hO S

/-- **The first chain's first query.** -/
theorem s0Q_of (H : HeadIs (Fmt.HO O) Sp o F.lab₁ st rnd) (hr : o.run = some run)
    (hp : F.pd₁ = pdOf (Fmt.HO O) Sp) (cms : List (Dig 256)) (x : Option X)
    (rt : List (Dig 256)) (pl : PBt L t) (hq : Q ⟨0, .f1 cms x (bytesToBits run), rt, pl⟩)
    (hst : F.stm₁ cms x pl = st) :
    (g (OracleName.fb t) (⟨0, .f1 cms x (bytesToBits run), rt, pl⟩ : FbIn 256 L t) :
      (Fin (K + 1) → Dig 256) × Dig 256).2 = bytesToDig o.rho0 := by
  have hc : fbCallJ F (K + 1) (⟨0, .f1 cms x (bytesToBits run), rt, pl⟩ : FbIn 256 L t)
      (Fin.last (K + 1)) = some (firstCall F.lab₁ F.pd₁ (F.stm₁ cms x pl) (bytesToBits run)) := by
    show (if (0 : ℕ) = 0 ∧ (Fin.last (K + 1)).val = K + 1 then _ else _) = _
    rw [if_pos ⟨rfl, Fin.val_last _⟩]
  rw [S.tail _ _ hq hc, hp, hst, first_of O hO H run hr]

/-- **The shared chain's first query.** -/
theorem s4Q_of (H : HeadIs (Fmt.HO O) Sp o F.lab₂ st rnd) (hr : o.run = some run)
    (hp : F.pd₂ = pdOf (Fmt.HO O) Sp) (cms : List (Dig 256)) (rtreq : Bits)
    (rt : List (Dig 256)) (pl : PBt L t) (hq : Q ⟨F.J, .f4 cms rtreq, rt, pl⟩)
    (hst : F.stm₂ cms rtreq pl = st) (hrun : F.run₂ pl = bytesToBits run) :
    (g (OracleName.fb t) (⟨F.J, .f4 cms rtreq, rt, pl⟩ : FbIn 256 L t) :
      (Fin (K + 1) → Dig 256) × Dig 256).2 = bytesToDig o.rho0 := by
  have hc : fbCallJ F (K + 1) (⟨F.J, .f4 cms rtreq, rt, pl⟩ : FbIn 256 L t)
      (Fin.last (K + 1)) = some (firstCall F.lab₂ F.pd₂ (F.stm₂ cms rtreq pl) (F.run₂ pl)) := by
    show (if F.J = F.J ∧ (Fin.last (K + 1)).val = K + 1 then _ else _) = _
    rw [if_pos ⟨rfl, Fin.val_last _⟩]
  rw [S.tail _ _ hq hc, hp, hst, hrun, first_of O hO H run hr]

/-- **The third chain's first query.** ρ0: the shared chain's seal; c: the first chain's. -/
theorem s3Q_of (H : HeadIs (Fmt.HO O) Sp o F.lab₃ st rnd) (hr : o.run = some run)
    (hp : F.pd₃ = pdOf (Fmt.HO O) Sp) (ρ0 c : Bits) (rt : List (Dig 256)) (pl : PBt L t)
    (hq : Q ⟨F.J3, .f3 ρ0 c, rt, pl⟩) (hst : F.stm₃ ρ0 c pl = st)
    (hrun : F.run₃ pl = bytesToBits run) :
    (g (OracleName.fb t) (⟨F.J3, .f3 ρ0 c, rt, pl⟩ : FbIn 256 L t) :
      (Fin (K + 1) → Dig 256) × Dig 256).2 = bytesToDig o.rho0 := by
  have hc : fbCallJ F (K + 1) (⟨F.J3, .f3 ρ0 c, rt, pl⟩ : FbIn 256 L t)
      (Fin.last (K + 1)) = some (firstCall F.lab₃ F.pd₃ (F.stm₃ ρ0 c pl) (F.run₃ pl)) := by
    show (if F.J3 = F.J3 ∧ (Fin.last (K + 1)).val = K + 1 then _ else _) = _
    rw [if_pos ⟨rfl, Fin.val_last _⟩]
  rw [S.tail _ _ hq hc, hp, hst, hrun, first_of O hO H run hr]

end First

end OnBytes.Maker.Page
