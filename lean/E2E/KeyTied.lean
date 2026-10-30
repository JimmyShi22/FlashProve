--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyTied.lean: THE CONDITION `Tied` AT THE KEY FILE. A statement on an honest side that is
written over the IOP of a file as written in Lean (below: a description) is made for pairs (private
input, explicit input) that are `Tied` (Johnson/Desc/ProofFile/Honest/Law/Rule/Tied.lean). Here:
every pair that is valid for the object's key file's protocol is tied, at what the library's map
writes for the instance, AT THE LETTERS OF THE SEAT of E2E/KeyHonest.lean and
E2E/KeyHonestLetters.lean. The twin of E2E/TiedAtFiles.lean and E2E/TiedAlong.lean, which do the
same for the proof file. By a call of the general theorem `tied`. Definitions, statements and
proofs. It is a condition on inputs: NOTHING IS SHOWN OF ANY PROVER: no completeness, nothing on
what a view shows.

THERE IS NO REQUEST. The object's instance at the key file is the OOD sample alone, and "valid"
(`HolographicProtocol.validT`) says: the instance is the honest OOD sample of (index, committer's coins, OOD seed).
In the general theorem's variables: the type of requests has one member; the copy's number is 0.

Definitions, at the configuration with the format's encoder (`Cf A Pad holdW`,
  E2E/TiedAtFiles.lean). `wrKey`: the writing map: of (nothing, an OOD sample): the table's key as
  the program writes it.
  `keyCommitterTied`: the index committer's share: the committed table's columns (the text of
    E2E/TiedAtFiles.lean's `cmAt`); the written key of the honest OOD sample; the explicit input:
    that key; what the shared chain reads of it: its one field.
  `keyAnswersTied`: the answers as they are read off the explicit input.
  **`relKey ok`: THE RELATION, BY NAME**: the explicit input is the written key of the honest OOD
    sample of (i, r) at SOME OOD seed, and ok i. NOTHING ELSE (`relKey_iff`). ok: a condition on the
    index alone: "every index" at the object, "in range" at the object whose index type is cut.
What is shown.
  `relKey_of`: THE GUARD ON THE COMMITTER's COINS: ok i gives `relKey ok` at the written key of the
    sample at ALL r and s: the relation shuts out no coin and no OOD seed.
  **`ext_cmKey`**: the committer's external string IS the committed table, whole symbols (position
    and words); the OOD seed is not read. `cmKey_beyond`: beyond the table's length it has nothing.
  `tiedAtKeyFile`: the six equations `TiedAt`, for every description F at the written key and every sh
    with "the shared chain's first state is sh of the instance's key". Three hold by `keyCommitterTied`'s own
    text, one by the three values' texts and `keyAnswersTied_along`, one is that premise, one by unfolding.
  `tied_key_files`: so, by `tied`: for any three protocols over that configuration and any provers:
    every valid pair with ok is tied: in the committer's own letters.
  `keySeam_eq_cm`, `tableOf_eq_cm`: THE SEAT's LETTERS ARE THE COMMITTER's: `keySeam val₂ val₃` is
    the committer's key with the three values at the number 0; `tableOf` is its external string.
  **`tied_key_seat`**: the same AT THE SEAT's LETTERS: prover of parts `keyLetters (keyCommitterTied.prover
    H)`, J := `keySeam val₂ val₃`, ext := `tableOf`, sh := `keyFirst X N P`.
  `tied_key_atFiles`: at three public files Z, at the object of `filesAt Z`: FREE: X, N, P (ANY key
    file's description, not only the one at Z); the prover H; the types of the two coins with val₂,
    val₃. NOT READ: the provers Q and the three protocols (`validT` reads the object's answers
    alone); of the rounds' data the depth alone.
  `tied_key_cut`: the same at the object whose index type is cut to the matrices in range, at ok :=
    "in range".
  **`tied_key_named`: ALL AT ONE DESCRIPTION**: for X, N, P with `KeyNamed Z X N P`
    (E2E/KeyProtocolOverDescription.lean): the key file's protocol at Z is the protocol over `keyFileDescription X N P`,
    read through the writing map; AND ext is the object's encoded index; AND every valid pair is
    tied at that description. **`tied_key_live`**: where the IOP's own test on the public files
    accepts, there are such X, N, P.
  `seat_letters`: the letters at which `tied_key_named` speaks, at run values of 256 bits, are those
    at which `keyHonestOfAt Z X N P B (keyCommitterTied.prover H)` is made: by unfolding.
  `valid_has`: every (index, coins, OOD seed) has a valid instance: the honest OOD sample.
  `validT_obj`, `seam_ext`, `keyAnswersTied_along`: three small steps.

Limits.
- `Tied` may be read as part of a goal; it counts as none.
- NEVER QUOTE A `tied_key_…` WITHOUT `ext_cmKey` | `tableOf_enc`: the six equations alone do not say
  that the committer's columns are an encoder's. `tied_key_named` carries the equation with it.
- `keyCommitterTied`, `keySeam` and `relKey` are definitions of these files: that three of the six equations
  hold "by the committer's own text" says that it was laid so. What ties them to the object:
  `ext_cmKey`,
  `recOf_eq`, `keySeam_silentK` (the verifier's test on the three plain parts accepts them).
- THE PROVER H IS FREE, but for its stored table, key and trace, which are laid: `Tied` reads of a
  prover its key and its stored columns alone. No part of a prover is written.
- AT THE OBJECT THAT IS NOT CUT the index is EVERY matrix: at ok := "every index" a pair whose index
  is out of range is tied too. `Tied` says nothing on whether a run can be played there.
- `Tied` does not bar a description that rejects early at every coin.
- The front round's answers are made of (index, coins, OOD seed), not read off the instance. Under
  `relKey` the two are equal: the instance IS the written key of that sample (`keySeam_public`).
- Two indices that share one valid explicit input are not shown here.
- That the test on the public files accepts any files is evaluated elsewhere, not proved.
- It is no statement on what a view shows, and none of zero knowledge.


-/
import E2E.KeyHonestTied
import E2E.KeyHonestLetters

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.AtFiles
open Iop Hiop AtPublicFiles.Cut
open OnBytes.Flat (Files relationsAndEncodingOfClaims RecFull codingHonest)
open OnBytes.Slice (frS frZ DecR ofF)
open OnBytes.Maker (WholeD)
open _root_.Run (digToBytes)
open VerifiableInference.Desc (FileDescription)
open VerifiableInference.Desc.Key (keyInstanceOfOutOfDomainSample)
open ProofFile.Honest (Prover KeyAndJoiningRoundMessages ProverCoinCounts Committer Isk Tied TiedAt relAt tied rel_of)
open AtPublicFiles.Committed (Cf Coin ansAt recAt encAt colF keyAt frontAt joinAt seamAt pubAt enc_col AZ PadZ
  holdZ)
open VerifierAndGoals (PublicFiles asDescriptionFiles)
open FlashProve (dataAtFiles)
open FlashProve (protocolDataWellFormed flashProveData)

/-- The writing map at the key file: of (nothing, an OOD sample): the written key. -/
def wrKey (a : Unit × RecFull) : KeyInst := keyInstanceOfOutOfDomainSample a.2

/-- The answers as they are read off the explicit input. -/
def keyAnswersTied (x : KeyInst) : List OnBytes.E := x.key.record.toList

/-- The writing map keeps the answers. -/
theorem keyAnswersTied_along (a : Unit × RecFull) : keyAnswersTied (wrKey a) = OnBytes.Flat.ansL a.2 := by
  unfold keyAnswersTied wrKey OnBytes.Flat.ansL
  rfl

/-- Two values of what stands beside a prover of parts are equal if their four fields are. -/
theorem seam_ext {W₀ Rc Sd Xi Ky TF TJ T3 : Type} {a b : KeyAndJoiningRoundMessages W₀ Rc Sd Xi Ky TF TJ T3}
    (h1 : a.keyOf = b.keyOf) (h2 : a.front = b.front) (h3 : a.join = b.join)
    (h4 : a.seam = b.seam) : a = b := by
  cases a
  cases b
  cases h1
  cases h2
  cases h3
  cases h4
  rfl

/-- A pair that is valid for the object's key file's protocol (`HolographicProtocol.validT`) holds the OOD seed with
the configuration's answers: for every configuration, three protocols and provers: by unfolding. -/
theorem validT_obj (C : ConfigurationWithOutOfDomainSample) (F : Files C) (Q : F.Provers) (w : C.I × (C.Pad × C.Rnd) × C.Seed)
    (a : C.Seed × C.Ans) (h : (F.withProvers Q).validT w a) :
    a = (w.2.2, AtPublicFiles.Committed.ansC C w.1 w.2.1 w.2.2) := h

/-! ## 1. At the configuration with the format's encoder -/

section Enc
variable {Y : Type} (A : (frS.toDecR frZ 402653181).Claims Y) (Pad : Type) [Fintype Pad]
  [Nonempty Pad] (holdW : A.Mat → Pad → ℕ → List UInt64)

/-- **The index committer's share at the key file.** -/
def keyCommitterTied : Committer (Cf A Pad holdW).I (Coin A Pad holdW) (Cf A Pad holdW).Seed Unit KeyInst
    OnBytes.TableKey where
  enc := fun i r p => if h : p < 2 ^ frS.P.T.a then some (colF A Pad holdW i r ⟨p, h⟩) else none
  ood := fun k => keyAt (recAt A Pad holdW k.index k.coins k.seed)
  xi := fun k _ => keyInstanceOfOutOfDomainSample (recAt A Pad holdW k.index k.coins k.seed)
  key := fun x => x.key
  tie := fun _ _ => rfl

/-- Beyond the table's length it has nothing. -/
theorem cmKey_beyond (i : (Cf A Pad holdW).I) (r : Coin A Pad holdW) (p : ℕ)
    (h : 2 ^ frS.P.T.a ≤ p) : (keyCommitterTied A Pad holdW).enc i r p = none :=
  dif_neg (Nat.not_lt.2 h)

/-- **Its external string is the committed table**: whole symbols; the OOD seed is not read. -/
theorem ext_cmKey (w : (Cf A Pad holdW).I × Coin A Pad holdW × (Cf A Pad holdW).Seed) :
    (keyCommitterTied A Pad holdW).ext frS.P.T.a w = encAt A Pad holdW w.1 w.2.1 := by
  funext p
  rw [enc_col]
  show (p.val, ((if h : p.val < 2 ^ frS.P.T.a then some (colF A Pad holdW w.1 w.2.1 ⟨p.val, h⟩)
    else none).getD []).map ofF) = _
  rw [dif_pos p.isLt]
  rfl

/-- **The relation, by name.** ok: a condition on the index alone. -/
def relKey (ok : (Cf A Pad holdW).I → Prop) :
    (Cf A Pad holdW).I → Coin A Pad holdW → KeyInst → Prop :=
  relAt (ansAt A Pad holdW) (fun i (_ : Unit) => ok i) wrKey

/-- Written out: the explicit input is the written key of the honest OOD sample at some OOD seed,
and ok holds of the index. -/
theorem relKey_iff (ok : (Cf A Pad holdW).I → Prop) (i : (Cf A Pad holdW).I)
    (r : Coin A Pad holdW) (ξ : KeyInst) :
    relKey A Pad holdW ok i r ξ ↔ ∃ s, ξ = keyInstanceOfOutOfDomainSample (recAt A Pad holdW i r s) ∧ ok i :=
  ⟨fun ⟨s, _, e, h⟩ => ⟨s, e, h⟩, fun ⟨s, e, h⟩ => ⟨s, (), e, h⟩⟩

/-- **The relation shuts out no coin of the committer's and no OOD seed.** -/
theorem relKey_of (ok : (Cf A Pad holdW).I → Prop) (i : (Cf A Pad holdW).I)
    (r : Coin A Pad holdW) (s : (Cf A Pad holdW).Seed) (h : ok i) :
    relKey A Pad holdW ok i r (keyInstanceOfOutOfDomainSample (recAt A Pad holdW i r s)) :=
  (relKey_iff A Pad holdW ok i r _).2 ⟨s, rfl, h⟩

variable {R₂ R₃ : Type} (val₂ : R₂ → ByteArray) (val₃ : R₃ → ByteArray)

/-- **The six equations at the key file**, for every description at the written key whose shared
chain's first state is sh of the instance's key. -/
theorem tiedAtKeyFile (DK : WholeD) (F : FileDescription KeyInst) (sh : OnBytes.TableKey → F.S₂)
    (hst : ∀ x : KeyInst, F.start₂ (F.pub x) = sh x.key) :
    TiedAt (ansAt A Pad holdW) wrKey (keyCommitterTied A Pad holdW) keyAt 0 (DK.at frS.P.T.a) F sh
      (frontAt (Xi := KeyInst) (R₂ := R₂) (R₃ := R₃) A Pad holdW) (joinAt A Pad holdW val₂)
      (seamAt (Xi := KeyInst) (R₂ := R₂) A Pad holdW val₃) (pubAt val₂ val₃ keyAnswersTied) where
  ood := fun _ => rfl
  writes := fun _ _ => rfl
  start := fun a => hst (wrKey a)
  full := fun i r p hp => by
    show (if h : p < 2 ^ frS.P.T.a then some (colF A Pad holdW i r ⟨p, h⟩) else none).isSome = true
    rw [dif_pos hp]
    rfl
  silent3 := fun r2 r3 k x' => by
    show (_, _, _) = pubAt val₂ val₃ keyAnswersTied 0 r2 r3
      (wrKey (x', recAt A Pad holdW k.index k.coins k.seed))
    unfold pubAt
    rw [keyAnswersTied_along]
    rfl
  reads := fun _ => rfl

variable (X : VerifiableInference.Desc.Key.Source) (N : H2U.PlaceNums)
  (P : VerifiableInference.Desc.Key.LaterPlaces) [Inhabited R₃]

/-- **Every valid pair is tied, in the committer's own letters**: for any three protocols over that
configuration and any provers Q. -/
theorem tied_key_files (DK : WholeD) {Tr X₀ Xh : Type}
    (H : Prover (Cf A Pad holdW).I (Coin A Pad holdW) KeyInst OnBytes.TableKey Tr X₀ Xh)
    (F : Files (Cf A Pad holdW)) (Q : F.Provers) (ok : (Cf A Pad holdW).I → Prop)
    (w : (Cf A Pad holdW).I × Coin A Pad holdW × (Cf A Pad holdW).Seed) (a : RecFull)
    (h : (F.withProvers Q).validT w a) (hok : ok w.1) :
    Tied (DK.at frS.P.T.a) (keyFileDescription X N P) ((keyCommitterTied A Pad holdW).prover H)
      (fun r2 r3 => (keyCommitterTied A Pad holdW).seam (frontAt A Pad holdW 0 r2 r3)
        (joinAt A Pad holdW val₂ r2) (seamAt A Pad holdW val₃ r2 r3))
      ((keyCommitterTied A Pad holdW).ext (DK.at frS.P.T.a).a) (pubAt val₂ val₃ keyAnswersTied 0) (keyFirst X N P)
      (relKey A Pad holdW ok) w (keyInstanceOfOutOfDomainSample a) :=
  tied (tiedAtKeyFile A Pad holdW val₂ val₃ DK (keyFileDescription X N P) (keyFirst X N P) fun _ => rfl) H w
    ((), a) ⟨by rw [AtPublicFiles.Committed.ansAt_eq]; exact validT_obj (Cf A Pad holdW) F Q w a h, hok⟩

omit [Inhabited R₃] in
/-- **The seat's J is the committer's key with the three values at the number 0.** -/
theorem keySeam_eq_cm :
    keySeam A (relationsAndEncodingOfClaims A (codingHonest frS frZ 402653181 A Pad holdW)) val₂ val₃ =
      fun r2 r3 => (keyCommitterTied A Pad holdW).seam (frontAt A Pad holdW 0 r2 r3)
        (joinAt A Pad holdW val₂ r2) (seamAt A Pad holdW val₃ r2 r3) := by
  funext r2 r3
  refine seam_ext rfl ?_ ?_ rfl
  · funext i r e x
    exact keySeam_frontAt A Pad holdW val₂ val₃ r2 r3 i r e x
  · funext i r e
    exact keySeam_joinAt A Pad holdW val₂ val₃ r2 r3 i r e

/-- **The seat's table is the committer's external string.** -/
theorem tableOf_eq_cm (DK : WholeD) :
    tableOf A (relationsAndEncodingOfClaims A (codingHonest frS frZ 402653181 A Pad holdW)) DK =
      (keyCommitterTied A Pad holdW).ext (DK.at frS.P.T.a).a :=
  funext fun w => (ext_cmKey A Pad holdW w).symm

/-- **Every valid pair is tied, AT THE SEAT's LETTERS.** -/
theorem tied_key_seat (DK : WholeD) {X₀ Xh : Type}
    (H : Prover (Cf A Pad holdW).I (Coin A Pad holdW) KeyInst OnBytes.TableKey Unit X₀ Xh)
    (F : Files (Cf A Pad holdW)) (Q : F.Provers) (ok : (Cf A Pad holdW).I → Prop)
    (w : (Cf A Pad holdW).I × Coin A Pad holdW × (Cf A Pad holdW).Seed) (a : RecFull)
    (h : (F.withProvers Q).validT w a) (hok : ok w.1) :
    Tied (DK.at frS.P.T.a) (keyFileDescription X N P) (keyLetters ((keyCommitterTied A Pad holdW).prover H))
      (keySeam A (relationsAndEncodingOfClaims A (codingHonest frS frZ 402653181 A Pad holdW)) val₂ val₃)
      (tableOf A (relationsAndEncodingOfClaims A (codingHonest frS frZ 402653181 A Pad holdW)) DK)
      (pubAt val₂ val₃ keyAnswersTied 0) (keyFirst X N P) (relKey A Pad holdW ok) w (keyInstanceOfOutOfDomainSample a) := by
  have t := tied_key_files A Pad holdW val₂ val₃ X N P DK H F Q ok w a h hok
  rw [keySeam_eq_cm, tableOf_eq_cm]
  exact ⟨t.rel, t.key, t.table, t.seam, t.start⟩

end Enc

/-- Every (index, coins, OOD seed) has a valid instance: the honest OOD sample. -/
theorem valid_has {I Y : Type} (L : HolographicProtocol I Y) (w : I × L.EncodingRandomness × L.OutOfDomainSeed) :
    L.validT w (L.recOf w.1 w.2.1 w.2.2) := rfl

/-! ## 2. At three public files Z -/

/- As in E2E/TiedAtFiles.lean: the search for this instance runs out of time. -/
local instance (priority := high) keyTied_pads : Nonempty PadZ := AtPublicFiles.Committed.pads_nonempty frS 402653181

section AtZ
variable (Z : PublicFiles) (X : VerifiableInference.Desc.Key.Source) (N : H2U.PlaceNums)
  (P : VerifiableInference.Desc.Key.LaterPlaces) (Q : (filesAt Z).Provers) {R₂ R₃ : Type}
  [Inhabited R₃] (val₂ : R₂ → ByteArray) (val₃ : R₃ → ByteArray) {X₀ Xh : Type}

/-- The committer's share at Z. -/
abbrev cmKeyZ : Committer FullSizeMatrix ((Cz Z).Pad × (Cz Z).Rnd) (Cz Z).Seed Unit KeyInst OnBytes.TableKey :=
  keyCommitterTied (AZ Z) PadZ (holdZ Z)

/-- The relation at Z. -/
abbrev relKeyZ (ok : FullSizeMatrix → Prop) : FullSizeMatrix → (Cz Z).Pad × (Cz Z).Rnd → KeyInst → Prop :=
  relKey (AZ Z) PadZ (holdZ Z) ok

/-- **AT THE OBJECT AT Z**: every pair that is valid for the key file's protocol is tied at the
written key of the instance. FREE: X, N, P: ANY key file's description, not only the one at Z
(`tied_key_named` joins them) · the prover H · the types of the two coins with val₂, val₃. NOT READ:
Q and the three protocols; of the rounds' data the depth alone. -/
theorem tied_key_atFiles
    (H : Prover FullSizeMatrix ((Cz Z).Pad × (Cz Z).Rnd) KeyInst OnBytes.TableKey Unit X₀ Xh)
    (w : FullSizeMatrix × ((filesAt Z).withProvers Q).EncodingRandomness × ((filesAt Z).withProvers Q).OutOfDomainSeed) (a : RecFull)
    (h : ((filesAt Z).withProvers Q).validT w a) :
    Tied ((dataAtFiles flashProveData Z).DK.at frS.P.T.a) (keyFileDescription X N P) (keyLetters ((cmKeyZ Z).prover H))
      (keySeam (dataAtFiles flashProveData Z).A (relationsAndEncodingOfClaims _ (dataAtFiles flashProveData Z).E) val₂ val₃)
      (tableOf (dataAtFiles flashProveData Z).A (relationsAndEncodingOfClaims _ (dataAtFiles flashProveData Z).E) (dataAtFiles flashProveData Z).DK)
      (pubAt val₂ val₃ keyAnswersTied 0) (keyFirst X N P) (relKeyZ Z fun _ => True) w (keyInstanceOfOutOfDomainSample a) :=
  tied_key_seat (AZ Z) PadZ (holdZ Z) val₂ val₃ X N P (dataAtFiles flashProveData Z).DK H (filesAt Z) Q
    (fun _ => True) w a h trivial

/-- **At the object whose index type is cut to the matrices in range**: at ok := "in range"; the
index is read through the inclusion. -/
theorem tied_key_cut
    (H : Prover FullSizeMatrix ((Cz Z).Pad × (Cz Z).Rnd) KeyInst OnBytes.TableKey Unit X₀ Xh)
    (w : Ix × (objAt Z Q).EncodingRandomness × (objAt Z Q).OutOfDomainSeed) (a : RecFull) (h : (objAt Z Q).validT w a) :
    Tied ((dataAtFiles flashProveData Z).DK.at frS.P.T.a) (keyFileDescription X N P) (keyLetters ((cmKeyZ Z).prover H))
      (keySeam (dataAtFiles flashProveData Z).A (relationsAndEncodingOfClaims _ (dataAtFiles flashProveData Z).E) val₂ val₃)
      (tableOf (dataAtFiles flashProveData Z).A (relationsAndEncodingOfClaims _ (dataAtFiles flashProveData Z).E) (dataAtFiles flashProveData Z).DK)
      (pubAt val₂ val₃ keyAnswersTied 0) (keyFirst X N P) (relKeyZ Z inRange) (onFst Subtype.val w)
      (keyInstanceOfOutOfDomainSample a) :=
  tied_key_seat (AZ Z) PadZ (holdZ Z) val₂ val₃ X N P (dataAtFiles flashProveData Z).DK H (filesAt Z) Q inRange
    (onFst Subtype.val w) a
    ((validT_reIndex (I := FullSizeMatrix) ((filesAt Z).withProvers Q) Subtype.val (back inRange) w a).1 h)
    w.1.property

end AtZ

/-- **ALL AT ONE DESCRIPTION.** For X, N, P that are what the key file's description at Z is made
of: the key file's protocol at Z, with its marks, is the protocol over that description, read
through the writing map; the seat's table is the object's encoded index; and every pair that is
valid for the object's key file's protocol is tied at that description: for all provers Q of the
object, all types of the two coins with their maps, and every prover H. -/
theorem tied_key_named {Z : PublicFiles} {X : VerifiableInference.Desc.Key.Source} {N : H2U.PlaceNums}
    {P : VerifiableInference.Desc.Key.LaterPlaces} (hn : KeyNamed Z X N P) :
    keyBatch (filesAt Z) =
        (keyOverOwn (dataAtFiles flashProveData Z).DK (keyFileDescription X N P) (dataAtFiles flashProveData Z).G.rec₀).comap keyInstanceOfOutOfDomainSample ∧
      ∀ (Q : (filesAt Z).Provers),
        (∀ i r e, tableOf (dataAtFiles flashProveData Z).A (relationsAndEncodingOfClaims _ (dataAtFiles flashProveData Z).E) (dataAtFiles flashProveData Z).DK
          (i, r, e) = ((filesAt Z).withProvers Q).encodeIndex i r) ∧
        ∀ (R₂ R₃ : Type) [Inhabited R₃] (val₂ : R₂ → ByteArray) (val₃ : R₃ → ByteArray)
          (X₀ Xh : Type)
          (H : Prover FullSizeMatrix ((Cz Z).Pad × (Cz Z).Rnd) KeyInst OnBytes.TableKey Unit X₀ Xh)
          (w : FullSizeMatrix × ((filesAt Z).withProvers Q).EncodingRandomness × ((filesAt Z).withProvers Q).OutOfDomainSeed) (a : RecFull),
          ((filesAt Z).withProvers Q).validT w a →
          Tied ((dataAtFiles flashProveData Z).DK.at frS.P.T.a) (keyFileDescription X N P)
            (keyLetters ((cmKeyZ Z).prover H))
            (keySeam (dataAtFiles flashProveData Z).A (relationsAndEncodingOfClaims _ (dataAtFiles flashProveData Z).E) val₂ val₃)
            (tableOf (dataAtFiles flashProveData Z).A (relationsAndEncodingOfClaims _ (dataAtFiles flashProveData Z).E) (dataAtFiles flashProveData Z).DK)
            (pubAt val₂ val₃ keyAnswersTied 0) (keyFirst X N P) (relKeyZ Z fun _ => True) w (keyInstanceOfOutOfDomainSample a) :=
  ⟨key_protocol_along hn, fun Q => ⟨fun _ _ _ => rfl,
    fun _ _ _ val₂ val₃ _ _ H w a h => tied_key_atFiles Z X N P Q val₂ val₃ H w a h⟩⟩

/-- **Where the IOP's own test on the public files accepts, there are such X, N, P.** -/
theorem tied_key_live (Z : PublicFiles) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) :
    ∃ X N P, KeyNamed Z X N P ∧
      keyBatch (filesAt Z) =
        (keyOverOwn (dataAtFiles flashProveData Z).DK (keyFileDescription X N P) (dataAtFiles flashProveData Z).G.rec₀).comap keyInstanceOfOutOfDomainSample ∧
      ∀ (Q : (filesAt Z).Provers),
        (∀ i r e, tableOf (dataAtFiles flashProveData Z).A (relationsAndEncodingOfClaims _ (dataAtFiles flashProveData Z).E) (dataAtFiles flashProveData Z).DK
          (i, r, e) = ((filesAt Z).withProvers Q).encodeIndex i r) ∧
        ∀ (R₂ R₃ : Type) [Inhabited R₃] (val₂ : R₂ → ByteArray) (val₃ : R₃ → ByteArray)
          (X₀ Xh : Type)
          (H : Prover FullSizeMatrix ((Cz Z).Pad × (Cz Z).Rnd) KeyInst OnBytes.TableKey Unit X₀ Xh)
          (w : FullSizeMatrix × ((filesAt Z).withProvers Q).EncodingRandomness × ((filesAt Z).withProvers Q).OutOfDomainSeed) (a : RecFull),
          ((filesAt Z).withProvers Q).validT w a →
          Tied ((dataAtFiles flashProveData Z).DK.at frS.P.T.a) (keyFileDescription X N P)
            (keyLetters ((cmKeyZ Z).prover H))
            (keySeam (dataAtFiles flashProveData Z).A (relationsAndEncodingOfClaims _ (dataAtFiles flashProveData Z).E) val₂ val₃)
            (tableOf (dataAtFiles flashProveData Z).A (relationsAndEncodingOfClaims _ (dataAtFiles flashProveData Z).E) (dataAtFiles flashProveData Z).DK)
            (pubAt val₂ val₃ keyAnswersTied 0) (keyFirst X N P) (relKeyZ Z fun _ => True) w (keyInstanceOfOutOfDomainSample a) := by
  obtain ⟨X, N, P, hn⟩ := key_named Z live
  exact ⟨X, N, P, hn, tied_key_named hn⟩

/- As in E2E/KeyHonestLetters.lean, and the same two terms: at the literal 256 the search for these
instances runs out of its budget. -/
local instance keyTied_digNonempty : Nonempty (Dig 256) := ⟨fun _ => false⟩
local instance keyTied_digInhabited : Inhabited (Dig 256) := ⟨fun _ => false⟩

/-- **The letters at which `tied_key_named` speaks, at run values of 256 bits, are those of which
the seat's term is made**: by unfolding. -/
theorem seat_letters (Z : PublicFiles) (X : VerifiableInference.Desc.Key.Source) (N : H2U.PlaceNums)
    (P : VerifiableInference.Desc.Key.LaterPlaces) {X₀ Xh : Type} (B : ProverCoinCounts)
    (H : Prover FullSizeMatrix ((Cz Z).Pad × (Cz Z).Rnd) KeyInst OnBytes.TableKey Unit X₀ Xh) :
    keyHonestOfAt Z X N P B ((cmKeyZ Z).prover H) =
      offlineProverAtFilesDecision Z (keyFileDescription X N P) B (keyLetters ((cmKeyZ Z).prover H))
        (keySeam (dataAtFiles flashProveData Z).A (relationsAndEncodingOfClaims _ (dataAtFiles flashProveData Z).E) digToBytes digToBytes)
        (keyFirst X N P)
        (tableOf (dataAtFiles flashProveData Z).A (relationsAndEncodingOfClaims _ (dataAtFiles flashProveData Z).E) (dataAtFiles flashProveData Z).DK) := rfl

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.keyAnswersTied_along
#print axioms AtPublicFiles.AtFiles.seam_ext
#print axioms AtPublicFiles.AtFiles.validT_obj
#print axioms AtPublicFiles.AtFiles.cmKey_beyond
#print axioms AtPublicFiles.AtFiles.ext_cmKey
#print axioms AtPublicFiles.AtFiles.relKey_iff
#print axioms AtPublicFiles.AtFiles.relKey_of
#print axioms AtPublicFiles.AtFiles.tiedAtKeyFile
#print axioms AtPublicFiles.AtFiles.tied_key_files
#print axioms AtPublicFiles.AtFiles.keySeam_eq_cm
#print axioms AtPublicFiles.AtFiles.tableOf_eq_cm
#print axioms AtPublicFiles.AtFiles.tied_key_seat
#print axioms AtPublicFiles.AtFiles.valid_has
#print axioms AtPublicFiles.AtFiles.tied_key_atFiles
#print axioms AtPublicFiles.AtFiles.tied_key_cut
#print axioms AtPublicFiles.AtFiles.tied_key_named
#print axioms AtPublicFiles.AtFiles.tied_key_live
#print axioms AtPublicFiles.AtFiles.seat_letters
