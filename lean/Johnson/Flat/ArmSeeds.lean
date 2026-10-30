-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/ArmSeeds.lean: what the tie of the seeds' two tests of the entry's arm asks of the
record's wire, shown at the full size and at the small example.

Johnson/Top/TieSeedArm.lean ties the two tests of the seeds in the entry's arm to the program
`verify-on-bytes`. Of the record's wire S0 and the wire W it asks:
  wire : ∀ a : Fin W.K → Dig 256, S0.seed a = toSeed (seedsOfDigs f sh.cubeBits sh.answers a)
  room : nBlocks sh.cubeBits sh.answers ≤ W.K
  hK   : W.K < 2 ^ 48
Here S0 is the record's wire of Johnson/Flat/ArmSibAt.lean (`sdAtFull`, `sdAtSmall`), whose seed is
`recSeedK` (OnBytes/Flat/RecordSeed.lean); f and sh are the field and the table's shape of the
grounds `recordGround` and `smallRecordGround`; toSeed is `seedOfC` at the sizes' own numbers.

Main theorems (Small for Full at the small example).
 `full_cube`, `full_answers`   the ground's table has points of 29 coordinates and 1 answer.
 `wire_atFull`, `room_atFull`  `wire` and `room`, at every wire W that `sdAtFull` accepts.
 `enough_full`, `few_full`     at K := the number of blocks of the entry's description at the
                               ground, whatever the configuration's digest: K + 1 blocks are
                               enough for the seeds' sampler, and K + 1 < 2 ^ 48.

What is not claimed. That oracle functions answer the seeds' queries with the digests of the
program's blocks (the coding's matter: Johnson/Top/TieSeedSpelt.lean). That a wire's K is that
K + 1: at `wAtFull T K …` (Johnson/Flat/ArmSibClosed.lean) it is, by unfolding; it is not said here.
Nothing on soundness.


-/
import Johnson.Flat.ArmSibAt
import OnBytes.K.Left.SeedWire
import OnBytes.K.Left.SeedsAt

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Compile.Batch.Cms
open _root_.Compile TypedOracleCompiler.Iop Rom Hiop
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open OnBytes.Slice OnBytes.Flat Cb Cb.Ood
open OnBytes.RunA (RestR LrG)
open TypedOracleCompiler.Run.PQ (SOf)
open _root_.Run (ckP)
open OnBytes.Tie (recordGround smallRecordGround)
open TypedOracleCompiler.Slice (seedOfC entryXD)
open OnBytes.K (seedsOfDigs nBlocks)
open OnBytes.K.Left (wire_recSeedK room_recSeedK record_fit small_record_fit)

theorem full_cube : recordGround.q.link.table.cubeBits = recLg := by decide +kernel
theorem full_answers : recordGround.q.link.table.answers = recS := by decide +kernel
theorem small_cube : smallRecordGround.q.link.table.cubeBits = 19 := by decide +kernel
theorem small_answers : smallRecordGround.q.link.table.answers = 1 := by decide +kernel

section
variable {X X' RI : Type} [Fintype RI] [Nonempty RI] {A : (frS.toDecR frZ 402653181).Claims X}
  {R : (frS.toDecR frZ 402653181).RelationsAndEncoding A}
  (T : RestR (DecR.configurationOfStoredTable A R).I X' RI (Fin 1 → (Fin 29 → GE) × NZ)
    ((Fin frS.P.v → Bool) × Fin 1 → GE) frS.P.T.a linkSibFull)
  (Bd : Type) (aT : RoundSplits T.test.shape)
  (W : QueryLayout 256 (typedOracleCarrier (LrG T) Bd aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull))))
  (t : Tag) (cfg : List (Dig 256)) (shape : Bits)
  (pl0 pl1 : PlainPart (shapeOf (typedOracleCarrier (LrG T) Bd aT
             (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull))) t)
    (annOf (typedOracleCarrier (LrG T) Bd aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull))) t))
  (code : (LrG T).Rec → List (Dig 256)) (num : ℕ → Plains T.bat.loc.shape → Bool)
  (h : (seedBS recLg recS).b ≤ W.K) (dS : DecidableEq (Fin 1 → (Fin 29 → GE) × NZ))

/-- **`wire`**: the seed that the record's wire reads off the K digests of an answer is read off
the program's own draws on these digests' bytes, in the ground's letters. -/
theorem wire_atFull (a : Fin W.K → Dig 256) :
    (sdAtFull T Bd aT W t cfg shape pl0 pl1 code num h dS).seed a =
      seedOfC recLg recS (seedsOfDigs recordGround.q.given.plan.field
        recordGround.q.link.table.cubeBits recordGround.q.link.table.answers a) := by
  rw [record_fit.field, full_cube, full_answers]
  exact wire_recSeedK recT recLg recS W.K h a

include h in
/-- **`room`**: the blocks that the program fetches for the seeds fit into the wire's. -/
theorem room_atFull :
    nBlocks recordGround.q.link.table.cubeBits recordGround.q.link.table.answers ≤ W.K := by
  rw [full_cube, full_answers]
  exact room_recSeedK h

end

section
variable {X X' RI : Type} [Fintype RI] [Nonempty RI] {A : (srS.toDecR srZ 524285).Claims X}
  {R : (srS.toDecR srZ 524285).RelationsAndEncoding A}
  (T : RestR (DecR.configurationOfStoredTable A R).I X' RI (Fin 1 → (Fin 19 → GE) × NZ)
    ((Fin srS.P.v → Bool) × Fin 1 → GE) srS.P.T.a linkSibSmall)
  (Bd : Type) (aT : RoundSplits T.test.shape)
  (W : QueryLayout 256 (typedOracleCarrier (LrG T) Bd aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall))))
  (t : Tag) (cfg : List (Dig 256)) (shape : Bits)
  (pl0 pl1 : PlainPart (shapeOf (typedOracleCarrier (LrG T) Bd aT
             (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall))) t)
    (annOf (typedOracleCarrier (LrG T) Bd aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall))) t))
  (code : (LrG T).Rec → List (Dig 256)) (num : ℕ → Plains T.bat.loc.shape → Bool)
  (h : (seedBS 19 1).b ≤ W.K) (dS : DecidableEq (Fin 1 → (Fin 19 → GE) × NZ))

/-- **`wire`**: the seed that the record's wire reads off the K digests of an answer is read off
the program's own draws on these digests' bytes, in the ground's letters. -/
theorem wire_atSmall (a : Fin W.K → Dig 256) :
    (sdAtSmall T Bd aT W t cfg shape pl0 pl1 code num h dS).seed a =
      seedOfC 19 1 (seedsOfDigs smallRecordGround.q.given.plan.field
        smallRecordGround.q.link.table.cubeBits smallRecordGround.q.link.table.answers a) := by
  rw [small_record_fit.field, small_cube, small_answers]
  exact wire_recSeedK srT 19 1 W.K h a

include h in
/-- **`room`**: the blocks that the program fetches for the seeds fit into the wire's. -/
theorem room_atSmall :
    nBlocks smallRecordGround.q.link.table.cubeBits smallRecordGround.q.link.table.answers ≤
      W.K := by
  rw [small_cube, small_answers]
  exact room_recSeedK h

end

/-- At the full size K + 1 blocks are enough for the seeds' sampler, K the number of blocks of the
entry's description. -/
theorem enough_full (c : ByteArray) : (seedBS recLg recS).b ≤ (entryXD recordGround c).K + 1 := by
  have h := record_fit.room c
  rw [full_cube, full_answers] at h
  exact Nat.le_succ_of_le h

theorem few_full (c : ByteArray) : (entryXD recordGround c).K + 1 < 2 ^ 48 := record_fit.few c

/-- The same at the small example. -/
theorem enough_small (c : ByteArray) : (seedBS 19 1).b ≤ (entryXD smallRecordGround c).K + 1 := by
  have h := small_record_fit.room c
  rw [small_cube, small_answers] at h
  exact Nat.le_succ_of_le h

theorem few_small (c : ByteArray) : (entryXD smallRecordGround c).K + 1 < 2 ^ 48 :=
  small_record_fit.few c

end TypedOracleCompiler.Compile.Batch.Cms
