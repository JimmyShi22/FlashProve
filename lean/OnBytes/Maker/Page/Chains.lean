-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/Chains.lean: the seven laws on typed oracle functions that the tie of a file's
three chains asks (`ReadL`, OnBytes/TypedOracleCompiler/Joined/K/RunsLineRead.lean: row₁, row₂, row₃, sG, s0, s4,
s3), for oracle functions that answer by the calls of OnBytes/Maker/Page/Frame.lean, under named
conditions on that page's data.

Statements and proofs. Four of the seven speak of the oracle functions alone: at every chain value
of 256 bits, every list of as many roots as the round sends trees and every plain part whose nonce
is below 2 ^ 64; the sealing call's at no roots and one plain part. They are the row law of the
first and of the third chain's rounds (`RowEnd`), of the shared chain's (`RowShE`), and the law of
the call in which the first chain is sealed (`GAt`). Three tie the first query of each chain to the
first value that the reader has computed. All are shown for a family g that `Speaks` by a file's
data F at the chain queries that meet a condition Q: wherever `fbCallJ F` gives a call at such a
query, or `gCallJ F` gives a call, g answers with O at that call's string. `gJ P O` speaks by
`P.proof` under the tag of the proof file, at every query. Under the tag of the key file the
spelling of the seeds' queries goes first, and it may write at a query that `fbCallJ P.key` spells
too. So `gJ P O` speaks by `P.key` at the queries at which the seeds' spelling is silent.

Main names:
  `Speaks g t F O Q`: as above. `Speaks.mono`: at a narrower Q. `speaks_onl`, `speaks_test`: at
    `gJ P O`, without a premise.
  `rowCall_block`: O at the string of a row's call is the format's block of that number.
  `RoundFitsJ F Q C hd d e i`: what a row law needs at the typed round i with the datum d, the
    head hd and the embedding e of the round's plain part: of F the kind's number, the bits of work,
    the message's bytes, the nonce; and that the round's queries meet Q. `FitsEnd`, `FitsShE`: round
    by round over a stretch.
  `row_of_calls`, `rowAt_lo₁`, `rowAt_lo₃`, `rowAt_sh`, `sealAt_sh`: one round.
  `rowEnd₁`, `rowEnd₃`, `rowShE₂`: a stretch: the first chain's rounds at the typed rounds i, i + 1,
    .. with the same indices; the third chain's at J3 + n, .. with the indices n, ..; the shared
    chain's at J + n, .. with the indices n, .., to its seal. `gAt_of`: the sealing call, at J.
  `first_of`: O at the string of `firstCall` is the first value of a chain's head (`HeadIs`,
    OnBytes/Maker/Page/FirstCalls.lean), if label, parameters' digest, statement and run's value are
    the head's. `s0_of`, `s4_of`, `s3_of`: the three laws.
No letter stands under "there is" in these statements.
Limits: that data F with these conditions exist at any interface is not shown here; nor that the
key file's own queries are queries at which the seeds' spelling is silent. O is a letter
whose answers have 32 bytes. Nothing is said of leaves, vertices or the request tree. These oracle
functions are no encoding in the sense of the soundness theorem (the head of Frame.lean). Nothing on
soundness.


-/
import OnBytes.Maker.Page.Frame
import OnBytes.Maker.Page.FirstCalls
import OnBytes.TypedOracleCompiler.Joined.K.RunsLineRead

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

/-! ## A family that answers by a file's calls -/

/-- Wherever the file's data give a call, at a chain query that meets Q, g answers with O at that
call's string. -/
structure Speaks (g : Fam (typedOracleFamily 256 (K + 1) L)) (t : Tag) (F : FileJ L t)
    (O : ByteArray → ByteArray) (Q : FbIn 256 L t → Prop) : Prop where
  /-- a block of the verifier's side -/
  blk : ∀ (q : FbIn 256 L t) (k : Fin (K + 1)) (c : Fmt.OQ), Q q →
    fbCallJ F (K + 1) q k.castSucc = some c →
    (g (OracleName.fb t) q : (Fin (K + 1) → Dig 256) × Dig 256).1 k = bytesToDig (O (strOf c))
  /-- the tail -/
  tail : ∀ (q : FbIn 256 L t) (c : Fmt.OQ), Q q →
    fbCallJ F (K + 1) q (Fin.last (K + 1)) = some c →
    (g (OracleName.fb t) q : (Fin (K + 1) → Dig 256) × Dig 256).2 = bytesToDig (O (strOf c))
  /-- the slot value -/
  slot : ∀ (q : JoiningRoundQuery 256 L t) (c : Fmt.OQ), gCallJ F q = some c →
    (g (OracleName.g t) q : Dig 256) = bytesToDig (O (strOf c))

/-- At a narrower condition. -/
theorem Speaks.mono {g : Fam (typedOracleFamily 256 (K + 1) L)} {F : FileJ L t} {O : ByteArray → ByteArray}
    {Q Q' : FbIn 256 L t → Prop} (S : Speaks g t F O Q) (h : ∀ q, Q' q → Q q) :
    Speaks g t F O Q' :=
  ⟨fun q k c hq => S.blk q k c (h q hq), fun q c hq => S.tail q c (h q hq), S.slot⟩

/-- The page's family speaks by the proof file's data, at every query. -/
theorem speaks_onl (P : PageJ L (K + 1)) (O : ByteArray → ByteArray)
    (Q : FbIn 256 L .onl → Prop) :
    Speaks (gJ P O) .onl P.proof O Q where
  blk q k c _ h := by
    show ansJ O (codeJ P (.fb .onl) q k.castSucc) = _
    have e : codeJ P (.fb .onl) q k.castSucc = (fbCallJ P.proof (K + 1) q k.castSucc).map strOf :=
      rfl
    rw [e, h]
    rfl
  tail q c _ h := by
    show ansJ O (codeJ P (.fb .onl) q (Fin.last (K + 1))) = _
    have e : codeJ P (.fb .onl) q (Fin.last (K + 1)) =
        (fbCallJ P.proof (K + 1) q (Fin.last (K + 1))).map strOf := rfl
    rw [e, h]
    rfl
  slot q c h := by
    show ansJ O (codeJ P (.g .onl) q (0 : Fin 1)) = _
    have e : codeJ P (.g .onl) q (0 : Fin 1) = (gCallJ P.proof q).map strOf := rfl
    rw [e, h]
    rfl

/-- The page's family speaks by the key file's data at the queries at which the seeds' spelling is
silent. -/
theorem speaks_test (P : PageJ L (K + 1)) (O : ByteArray → ByteArray) :
    Speaks (gJ P O) .test P.key O (fun q => ∀ j, P.seeds (q, j) = none) where
  blk q k c hq h := by
    show ansJ O (codeJ P (.fb .test) q k.castSucc) = _
    have e : codeJ P (.fb .test) q k.castSucc =
        (match P.seeds (q, k.castSucc) with
          | some s => some (bitsToBytes s)
          | none => (fbCallJ P.key (K + 1) q k.castSucc).map strOf) := rfl
    rw [e, hq _, h]
    rfl
  tail q c hq h := by
    show ansJ O (codeJ P (.fb .test) q (Fin.last (K + 1))) = _
    have e : codeJ P (.fb .test) q (Fin.last (K + 1)) =
        (match P.seeds (q, Fin.last (K + 1)) with
          | some s => some (bitsToBytes s)
          | none => (fbCallJ P.key (K + 1) q (Fin.last (K + 1))).map strOf) := rfl
    rw [e, hq _, h]
    rfl
  slot q c h := by
    show ansJ O (codeJ P (.g .test) q (0 : Fin 1)) = _
    have e : codeJ P (.g .test) q (0 : Fin 1) = (gCallJ P.key q).map strOf := rfl
    rw [e, h]
    rfl

/-! ## A row's call -/

/-- **O at the string of a row's call is the format's block of that number.** -/
theorem rowCall_block (O : ByteArray → ByteArray) (hO : ∀ s, (O s).size = 32) (lab idx : ℕ)
    (ρ : Bits) (msg : ByteArray) (kind : Fmt.Kind) (w nonce ow K' : ℕ) (j : Fin (K' + 1)) :
    O (strOf (rowCall lab idx ρ msg kind.num w nonce ow K' j)) =
      Fmt.blockW (Fmt.HO O) lab (bitsToBytes ρ) idx msg kind w nonce (blockNo ow K' j) := by
  rw [blockW_HO O hO, ← roundBytes_tail]
  rfl

/-- What a row law needs of the file's data at one typed round. -/
structure RoundFitsJ (F : FileJ L t) (Q : FbIn 256 L t → Prop) (C : CK) (hd : Bits → Head 256 X)
    (d : RD) (e : (roundS C d).Plain → PBt L t) (i : ℕ) : Prop where
  ours : ∀ (ρ : Bits) (rt : List (Dig 256)) (pl : (roundS C d).Plain), Q ⟨i, hd ρ, rt, e pl⟩
  kind : F.kind i = d.kind.num
  work : F.work i = d.entry.work
  msg : ∀ (bs : List ByteArray) (pl : (roundS C d).Plain),
    F.msg i bs (e pl) = bytesL bs d.items (GPlain.old (b := d.entry.work) pl)
  nonce : ∀ pl : (roundS C d).Plain, F.nonce i (e pl) = GPlain.nonce (b := d.entry.work) pl

section One
variable {g : Fam (typedOracleFamily 256 (K + 1) L)} {F : FileJ L t} {O : ByteArray → ByteArray}
  {Q : FbIn 256 L t → Prop} (hO : ∀ s, (O s).size = 32) (S : Speaks g t F O Q) {C : CK} {d : RD}
  {e : (roundS C d).Plain → PBt L t} {i : ℕ}
include hO S

/-- The row, from the call of every block. lab, n: the call's label and index. -/
theorem row_of_calls (hd : Bits → Head 256 X) (R : RoundFitsJ F Q C hd d e i) (lab n : ℕ)
    (hc : ∀ (ρ : Bits) (rt : List (Dig 256)) (pl : (roundS C d).Plain) (j : Fin (K + 1 + 1)),
      fbCallJ F (K + 1) (⟨i, hd ρ, rt, e pl⟩ : FbIn 256 L t) j =
        some (rowCall lab n ρ (F.msg i (rt.map digToBytes) (e pl)) (F.kind i) (F.work i)
          (F.nonce i (e pl)) (F.work i) (K + 1) j)) :
    RowAt (fun _ => L) C K g t O lab hd d e i n := by
  intro ρ rt pl _ _ _
  refine ⟨fun k => ?_, ?_⟩
  · rw [S.blk _ k _ (R.ours ρ rt pl) (hc ρ rt pl k.castSucc), R.kind, R.work, R.msg, R.nonce,
      rowCall_block O hO]
  · rw [S.tail _ _ (R.ours ρ rt pl) (hc ρ rt pl (Fin.last (K + 1))), R.kind, R.work, R.msg,
      R.nonce, rowCall_block O hO, blockNo_last]

/-- A round of the first chain. -/
theorem rowAt_lo₁ (R : RoundFitsJ F Q C (fun ρ => .f2 none ρ) d e i) (h1 : 1 ≤ i)
    (h2 : i ≤ F.n₁) : RowAt (fun _ => L) C K g t O F.lab₁ (fun ρ => .f2 none ρ) d e i i :=
  row_of_calls hO S _ R _ _ fun ρ rt pl j => by
    show (if 1 ≤ i ∧ i ≤ F.n₁ then _ else _) = _
    rw [if_pos ⟨h1, h2⟩]

/-- A round of the third chain. -/
theorem rowAt_lo₃ (R : RoundFitsJ F Q C (fun ρ => .f2 none ρ) d e i) (h1 : F.J3 + 1 ≤ i)
    (h2 : i ≤ F.J3 + F.n₃) :
    RowAt (fun _ => L) C K g t O F.lab₃ (fun ρ => .f2 none ρ) d e i (i - F.J3) :=
  row_of_calls hO S _ R _ _ fun ρ rt pl j => by
    show (if 1 ≤ i ∧ i ≤ F.n₁ then _ else if F.J3 + 1 ≤ i ∧ i ≤ F.J3 + F.n₃ then _ else _) = _
    rw [if_neg (by unfold FileJ.J3 at h1; omega), if_pos ⟨h1, h2⟩]

/-- A round of the shared chain that is not its last. -/
theorem rowAt_sh (R : RoundFitsJ F Q C (fun ρ => .f5 ρ) d e i) (h1 : F.J + 1 ≤ i)
    (h2 : i < F.J + F.n₂) :
    RowAt (fun _ => L) C K g t O F.lab₂ (fun ρ => .f5 ρ) d e i (i - F.J) :=
  row_of_calls hO S _ R _ _ fun ρ rt pl j => by
    show (if F.J + 1 ≤ i ∧ i ≤ F.J + F.n₂ then _ else _) = _
    rw [if_pos ⟨h1, Nat.le_of_lt h2⟩]
    show some (rowCall _ _ _ _ _ _ _ (if i = F.J + F.n₂ then 1 else F.work i) _ _) = _
    rw [if_neg (Nat.ne_of_lt h2)]

/-- The last round of the shared chain: the typed tail is the row's block 1. -/
theorem sealAt_sh (R : RoundFitsJ F Q C (fun ρ => .f5 ρ) d e i) (h1 : 1 ≤ F.n₂)
    (h2 : i = F.J + F.n₂) : SealAt (fun _ => L) C K g t O F.lab₂ d e i (i - F.J) := by
  intro ρ rt pl _ _ _
  have hc : fbCallJ F (K + 1) (⟨i, .f5 ρ, rt, e pl⟩ : FbIn 256 L t) (Fin.last (K + 1)) =
      some (rowCall F.lab₂ (i - F.J) ρ (F.msg i (rt.map digToBytes) (e pl)) (F.kind i) (F.work i)
        (F.nonce i (e pl)) 1 (K + 1) (Fin.last (K + 1))) := by
    show (if F.J + 1 ≤ i ∧ i ≤ F.J + F.n₂ then _ else _) = _
    rw [if_pos ⟨by omega, Nat.le_of_eq h2⟩]
    show some (rowCall _ _ _ _ _ _ _ (if i = F.J + F.n₂ then 1 else F.work i) _ _) = _
    rw [if_pos h2]
  rw [S.tail _ _ (R.ours ρ rt pl) hc, R.kind, R.work, R.msg, R.nonce, rowCall_block O hO,
    blockNo_last]
  rfl

end One

/-! ## A stretch -/

/-- The file's data fit a stretch of local rounds with no tail, from the typed round i on. -/
def FitsEnd (F : FileJ L t) (Q : FbIn 256 L t → Prop) (C : CK) : (ds : List RD) →
    (PlainPart (uL C ds) (allLo (SL C ds)) → PBt L t) → ℕ → Prop
  | [], _, _ => True
  | d :: ds, embP, i =>
    RoundFitsJ F Q C (fun ρ => .f2 none ρ) d (fun pl => embP (.inl (.inr pl))) i ∧
      FitsEnd F Q C ds (fun z => embP (.inr z)) (i + 1)

/-- The file's data fit a stretch of shared rounds with no tail, from the typed round i on. -/
def FitsShE (F : FileJ L t) (Q : FbIn 256 L t → Prop) (C : CK) : (ds : List RD) →
    (PlainPart (uL C ds) (annShE C ds) → PBt L t) → ℕ → Prop
  | [], _, _ => True
  | d :: ds, embP, i =>
    RoundFitsJ F Q C (fun ρ => .f5 ρ) d (fun pl => embP (.inl (.inl pl))) i ∧
      FitsShE F Q C ds (fun z => embP (.inr z)) (i + 1)

section Stretch
variable {g : Fam (typedOracleFamily 256 (K + 1) L)} {F : FileJ L t} {O : ByteArray → ByteArray}
  {Q : FbIn 256 L t → Prop} (hO : ∀ s, (O s).size = 32) (S : Speaks g t F O Q) (C : CK)
include hO S

/-- The first chain's rounds from the typed round i on. -/
theorem rowEnd₁ : ∀ (ds : List RD) (embP : PlainPart (uL C ds) (allLo (SL C ds)) → PBt L t) (i : ℕ),
    FitsEnd F Q C ds embP i → 1 ≤ i → i + ds.length ≤ F.n₁ + 1 →
    RowEnd (fun _ => L) C K g t O F.lab₁ ds embP i i
  | [], _, _, _, _, _ => trivial
  | d :: ds, embP, i, h, h1, h2 => by
    have h2' : i + (ds.length + 1) ≤ F.n₁ + 1 := h2
    exact ⟨rowAt_lo₁ hO S h.1 h1 (by omega),
      rowEnd₁ ds _ (i + 1) h.2 (by omega) (by omega)⟩

/-- The third chain's rounds from the typed round J3 + n on. -/
theorem rowEnd₃ : ∀ (ds : List RD) (embP : PlainPart (uL C ds) (allLo (SL C ds)) → PBt L t) (n : ℕ),
    FitsEnd F Q C ds embP (F.J3 + n) → 1 ≤ n → n + ds.length ≤ F.n₃ + 1 →
    RowEnd (fun _ => L) C K g t O F.lab₃ ds embP (F.J3 + n) n
  | [], _, _, _, _, _ => trivial
  | d :: ds, embP, n, h, h1, h2 => by
    have h2' : n + (ds.length + 1) ≤ F.n₃ + 1 := h2
    have r := rowAt_lo₃ hO S h.1 (by omega) (by omega)
    rw [Nat.add_sub_cancel_left] at r
    exact ⟨r, rowEnd₃ ds _ (n + 1) h.2 (by omega) (by omega)⟩

/-- The shared chain's rounds from the typed round J + n on, to its last. -/
theorem rowShE₂ : ∀ (ds : List RD) (embP : PlainPart (uL C ds) (annShE C ds) → PBt L t) (n : ℕ),
    FitsShE F Q C ds embP (F.J + n) → 1 ≤ n → n + ds.length = F.n₂ + 1 →
    RowShE (fun _ => L) C K g t O F.lab₂ ds embP (F.J + n) n
  | [], _, _, _, _, _ => trivial
  | [d], embP, n, h, h1, h2 => by
    have h2' : n + 1 = F.n₂ + 1 := h2
    have r := sealAt_sh hO S h.1 (by omega) (by omega)
    rw [Nat.add_sub_cancel_left] at r
    exact r
  | d :: d' :: ds, embP, n, h, h1, h2 => by
    have h2' : n + (ds.length + 1 + 1) = F.n₂ + 1 := h2
    have r := rowAt_sh hO S h.1 (by omega) (by omega)
    rw [Nat.add_sub_cancel_left] at r
    exact ⟨r, rowShE₂ (d' :: ds) _ (n + 1) h.2 (by omega) (by
      show n + 1 + (ds.length + 1) = F.n₂ + 1
      omega)⟩

/-- **The law of the call in which the first chain is sealed.** -/
theorem gAt_of (e : PBt L t) : GAt (fun _ => L) K g t O F.lab₁ e F.J F.J := by
  intro ρ _
  have hc : gCallJ F (⟨F.J, ρ, [], e⟩ : JoiningRoundQuery 256 L t) =
      some ⟨1, 162, F.lab₁, F.J, bitsToBytes ρ, roundBytes ByteArray.empty 6 0 0 0⟩ := by
    show (if F.J = F.J then _ else _) = _
    rw [if_pos rfl]
  rw [S.slot _ _ hc, blockW_HO O hO, ← roundBytes_tail]
  rfl

end Stretch

/-! ## The first calls -/

/-- **O at the string of a chain's first call is the first value of the chain's head.** -/
theorem first_of (O : ByteArray → ByteArray) (hO : ∀ s, (O s).size = 32) {S : Fmt.SpecX}
    {o : Fmt.ChainOut} {label : ℕ} {st rnd : ByteArray} (H : HeadIs (Fmt.HO O) S o label st rnd)
    (run : ByteArray) (hr : o.run = some run) :
    O (strOf (firstCall label (pdOf (Fmt.HO O) S) st (bytesToBits run))) = o.rho0 := by
  have h32 : run.size = 32 := by
    have e := H.run
    rw [hr] at e
    rw [Option.some.inj e]
    exact size_HO32 O hO _ _ _ _ _ (by decide)
  rw [H.rho0, hr]
  show O (Fmt.oStr 0 160 0 label Fmt.zero32
    (Run.firstBytes (pdOf (Fmt.HO O) S) st (bytesToBits run))) = _
  rw [first_bytes _ _ _ h32]
  rfl

section First
variable {g : Fam (typedOracleFamily 256 (K + 1) L)} {F : FileJ L t} {O : ByteArray → ByteArray}
  {Q : FbIn 256 L t → Prop} (hO : ∀ s, (O s).size = 32) (S : Speaks g t F O Q) {Sp : Fmt.SpecX}
  {o : Fmt.ChainOut} {st rnd run : ByteArray}
include hO S

/-- **The first chain's first query.** -/
theorem s0_of (H : HeadIs (Fmt.HO O) Sp o F.lab₁ st rnd) (hr : o.run = some run)
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
theorem s4_of (H : HeadIs (Fmt.HO O) Sp o F.lab₂ st rnd) (hr : o.run = some run)
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
theorem s3_of (H : HeadIs (Fmt.HO O) Sp o F.lab₃ st rnd) (hr : o.run = some run)
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
