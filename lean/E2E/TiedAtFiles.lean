-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/TiedAtFiles.lean: at the library's object at three public files Z, `(filesAt Z).withProvers P`
(E2E/ObjectAtFiles.lean), every pair (private input, instance) that is valid for the object meets
the condition `Tied` (below: is tied), where every stored table that the description declares is
under the item 0 (the hypothesis hit): `tied_atFiles_along`, `tied_atFiles_pulled`. `Tied`
(Johnson/Desc/ProofFile/Honest/Law/Rule/Tied.lean) is a condition on the private input and the
explicit input of an honest prover of the proof file's protocol, as `ProofFile.Honest.honestBatchProverOfFile`
(Johnson/Desc/ProofFile/Honest/StratC.lean) builds one over the IOP as written in Lean (below: the
description). The parameters of `Tied` are defined here at the format's encoder and compared with
the object's fields. The main theorems hold for all provers P of the object. At the provers that
send fixed messages (`Files.fixedMessageProvers`) the object is the one in the input at which `VerifierAndGoals.verify`
calls the compiled verifier (`object_description`, E2E/DescriptionTie.lean). Definitions, statements
and proofs.

For what. A statement on such an honest prover is made for pairs that are `Tied`. As long as the
parameters of that condition are free, it can be met in ways that make the statement vacuous: by a
relation that shuts out some of the committer's coins, by an external string that is not the
encoder's table, by plain parts (the messages of the three rounds without a challenge) that carry
something of the index. Here the index committer's structure `cmAt` (a `Committer`,
Johnson/Desc/ProofFile/Honest/Committer.lean) and what these three rounds send (`frontAt`, `joinAt`,
`seamAt`) are definitions of this file. What ties the definitions to the object: the committer's
external string is the object's field `encodeIndex`, whole symbols (`ext_obj`); the OOD (out-of-domain)
answers are the object's field `honestOutOfDomainAnswer` (`ans_obj`, `valid_obj`); the protocol is the object's, where
the IOP's own test on the public files accepts, at the description that the library makes of Z's
files (`protocol_atFiles`); the object's own test on the three plain parts accepts the three values
as they are read off the instance (`silP_along`, and `pub_passes` in E2E/TiedAlong.lean).

  `tied_atFiles_along`: under hit, `((filesAt Z).withProvers P).validB (RyesZ Z) w a → Tied … w (instanceAsPlainRecord a)`:
    every pair that is valid for the object, at the relation `RyesZ Z`, is tied at what the
    library's writing map `LPFD.Full.instanceAsPlainRecord` (Johnson/Desc/Laid/ProofFull.lean) writes for the
    instance a. The description is `F0T OnBytes.secondHashFunction Zp Np cF` (Johnson/P5J/AtTerm.lean); the
    prover structure (`ProofFile.Honest.Prover`) is `(cmAlong …).proverAt 0 H`
  `tied_atFiles_pulled`: the same at a itself, under hit at the pulled-back description: the
    description is pulled back to the object's instances (`descAt`); the prover structure is
    `(cmPulled …).proverAt 0 H`
  `ext_obj`, `ext_obj_pulled`: at Z the external string of `cmAlong`, and that of `cmPulled`, is the
    object's field `encodeIndex`, whole symbols, for all P
  `protocol_atFiles`: where the IOP's own test on the public files accepts
    (`protocolDataWellFormed (asDescriptionFiles Z) = true`), for every (Zp, Np, cF) of which `LaidAt`
    (Johnson/P5J/LaidOpens.lean) holds at Z's files: the object's batch protocol is `batchOf` at the
    pulled-back description, the object's rounds' data and `silP`. E2E/TiedAlong.lean has the same
    protocol as the description's own, pulled back as a protocol
  `laid_of_live`: where that test accepts, `LaidAt` holds of some (Zp, Np, cF)
  `RyesZ Z`: a definition: the relation of the object's configuration `Cz Z`. `ryesZ_iff`: it is the
    model's relaxed relation: the matrix is in range, and it holds an index at which some trace
    meets the relaxed relation with the cost ledger (`RelLAt`, Johnson/Top/H/TargetAtPolicy.lean),
    at the table of scales and policy that the library's reader returns at Z's files (the
    reference's where it refuses). `ryesZ_ex`: as the library spells it: `∃ c, (Cz Z).Ryes i x' c`
  `conf_eq`: by unfolding, `Cz Z` is `Cf` at Z's claims, the library's pads and its way of holding a
    matrix of cells. `conf_types`, `ryes_obj`, `enc_obj`: the same for its parts: the four types of
    the private input, the relation, the object's field `encodeIndex`
  `AZ Z`, `PadZ`, `holdZ Z`: definitions: these claims, pads and way of holding a matrix, at the
    full size. `pads_nonempty`: the type of pads is not empty
  `tied_files_along`, `tied_files_pulled`: the two main theorems for any three protocols over the
    configuration `Cf A Pad holdW`, any provers of these, any relation Ryes and any rounds' data DP
  `tiedAt_along`, `tiedAt_pulled`: the six equations `TiedAt` at `cmAlong` and at `cmPulled`, at
    every (Zp, Np, cF). The three hypotheses of `tiedAt_cmAt` hold by unfolding
  `tiedAt_cmAt`: the six equations `TiedAt` at `cmAt`, from three equations on the writing map (hr,
    hans, hst: see Hypotheses). `ood`, `writes` and `full` hold by the definition of `cmAt`; `start`
    is hst and `reads` is hr; `silent3` holds by the definitions of `frontAt`, `joinAt`, `seamAt`
    and `pubAt`, and by hans
  `cmAt wr key kp hr`: a definition: the `Committer` structure at the format's encoder. wr: the
    writing map, from the object's instance (request, OOD sample) to the explicit input; key: the
    key as it is read off the explicit input; kp: the key of an OOD sample. Its fields: `enc`:
    `colF` at the positions below `2 ^ frS.P.T.a`, `none` beyond (`cmAt_beyond`); `ood`: kp of
    `recAt`; `xi`: wr of the request and `recAt`; `key`: key; `tie`: by hr
  `ext_cmAt`: the external string of `cmAt` is the committed table `encAt`, whole symbols: the
    position and the words; no OOD seed is read
  `cmAlong`: a definition: `cmAt` where the explicit input is the description's own instance
    (`ProofFile.Inst`): wr := `instanceAsPlainRecord`; key := that instance's key. `cmPulled`: a definition: `cmAt` where
    the explicit input is the object's own instance (request, OOD sample): wr := `id`; key :=
    `keyAt` of the sample. In both kp := `keyAt`
  `descAt Zp Np cF`: a definition: the description `F0T OnBytes.secondHashFunction Zp Np cF`, at any public part
    Zp (`ProofFile.Pub`) with its parameters Np and cF, pulled back along `instanceAsPlainRecord`. `shAt Zp Np cF`: a
    definition: the shared chain's first state as a function of a key
  `frontAt`, `joinAt`, `seamAt`: definitions: the front round sends the answers of `recAt` as a
    list, and the copy's number n; the joining round these answers and run₂ r2; the seam run₃ r3.
    `pubAt ansOf`: a definition: the same three values with the answers read off the explicit input
    by ansOf. n occurs in `frontAt` and in the first part of `pubAt`, and by the types of the others
    nowhere else
  `ansInst`: a definition: the answers as they are read off an `ProofFile.Inst`: the entries of its key's
    array. `ansInst_along`: read off `instanceAsPlainRecord z` they are the answers of z's OOD sample as a list
    (`ansL`)
  `silInst`: a definition: the library's test on the three plain parts (`silP`,
    OnBytes/Flat/FilesAt.lean), read off an `ProofFile.Inst`. `silP_along`: `silP` at an instance is
    `silInst` at what `instanceAsPlainRecord` writes for it: the writing map keeps the answers
  `Cf A Pad holdW`: a definition: the configuration of a committed table with the format's encoder
    (`codingHonest`, OnBytes/Flat/CodingHonest.lean), general in the claims A, the type of pads and
    how a matrix is held. `Coin`: a definition: the committer's coins there: pads and encoding
    randomness
  `ansC C i r s`: a definition: the OOD answers at any configuration C. `ans_obj`, `valid_obj`: by
    unfolding, for every C, any three protocols over it and any provers: the object's field `honestOutOfDomainAnswer` is
    `ansC C`, and in a pair that is valid for the object (`HolographicProtocol.validB`, Hiop/RecInterface.lean) the
    instance's OOD sample is the private input's OOD seed with `ansC C` at the private input
  `ansAt`, `recAt`, `encAt`: definitions at `Cf`: the OOD answers (`ansAt_eq`: they are `ansC` of
    `Cf`); the OOD sample: the OOD seed with the answers; the committed table (`enc_files`: it is
    the object's field `encodeIndex`, for any three protocols over `Cf`)
  `colF i r x`: a definition: the field values of the column at the position x. `enc_col`: a symbol
    of the committed table is its position with the words of `colF`
  `keyAt rec`: a definition: the key as the library writes it of an OOD sample (`keyOf`,
    OnBytes/Slice/KeyOfRec.lean)
  `seed_ne_zero`, `key_fits`: the factor in an OOD seed is never 0, by its type; the written key
    fits every shape with the sample's three numbers

By what. `Tied` (clauses rel, key, table, seam, start), the relation `relAt` and the six equations
`TiedAt` (ood, writes, start, full, silent3, reads) are defined in
Johnson/Desc/ProofFile/Honest/Law/Rule/Tied.lean, general in all parameters. The four theorems that
conclude `Tied` are by `ProofFile.Honest.tied_atItem` (TiedAtItem.lean, same folder): under `TiedAt`, and
where every stored table that a round of the description declares is under the item item₀, every
valid pair is tied at the prover structure `Cm.proverAt item₀ H`. That is `tied` (Tied.lean), stated
for `Committer.proverAt` (Johnson/Desc/ProofFile/Honest/CommitterAt.lean): H with the committer's
columns as its stored table at the item item₀, no column at another item, and the committer's key.
`rel_of` (Tied.lean; not called here): Ryes i x' gives `relAt` at what is written for x' and the OOD
sample, at all coins of the committer's and all OOD seeds. `enc_col` is by `honestTab_col`
(E2E/TableStrong.lean), `key_fits` by `keyOf_fits` (OnBytes/Slice/KeyOfRec.lean), `laid_of_live` by
`laid_at_name` (Johnson/P5J/AtName.lean) and `laid_opensK` (Johnson/P5J/LaidOpens.lean),
`protocol_atFiles` by `run_eq_of_laid` and `filesWith_eq` (E2E/ProtocolOverDescription.lean) and `LaidAt.laidPOf`
(Johnson/P5T/FenceAtMg.lean). The other proofs unfold definitions or call theorems of this file.

Hypotheses. Of the four theorems that conclude `Tied`. hit: `AtPublicFiles.AtZero.ItemsZero`
(E2E/ItemsZero.lean) of the description: every stored table that a round of the description declares
is under the item 0 (in the two theorems `…_pulled`: of `descAt Zp Np cF`). `itemsZero_of_data`
(same file) proves it wherever the description's `data` returns; for `F0T OnBytes.secondHashFunction Zp Np cF` a
`LaidAt` says so in its field `data`. h: the pair of w and a is valid for the object (`validB`). Of
`tiedAt_cmAt`. hr: `key (wr a) = kp a.2`. hans: `ansOf (wr a)` is the answers of a.2 as a list
(`ansL a.2`). hst: the shared chain's first state at `wr a` is sh of `key (wr a)`. Of
`protocol_atFiles`. live: `protocolDataWellFormed (asDescriptionFiles Z) = true`. L: `LaidAt` at Z's three files, some rounds'
data and decision, and (Zp, Np, cF); its field `value` says that the library makes the description
`F0T OnBytes.secondHashFunction Zp Np cF` of these files. Of `key_fits`. hv, hs, hl: the shape's `v`, `answers`
and `cubeBits` are `frS.P.v`, 1 and 29.

Limits.
- `TiedAt` does not say that the committer's columns are an encoder's: at a committer whose columns
  are empty lists it holds too. So never quote `tied`, `tied_atItem` or a theorem here that
  concludes `Tied` without `ext_obj` (at `cmPulled`: `ext_obj_pulled`).
- Still free parameters at Z: the prover structure H, of which `proverAt 0` replaces the stored
  table (the committer's columns at the item 0, no column at another item) and the key; the copy's
  number n; the types of the two coins r2, r3 with the maps run₂, run₃; (Zp, Np, cF), under hit: any
  description of that family that meets hit, not only the one of which `LaidAt` holds at Z.
- hit is a hypothesis: it is proved of no description here.
- No prover is built here, and nothing is shown of any. E2E/BridgeTied.lean (`onlineProversOfCommitter`) and
  E2E/BridgeJoinAtFiles.lean (`famG`) build honest provers with `honestBatchProverOfFile` at these values. That
  such a prover is the object's third prover is not stated in Lean: the statements on the compiled
  argument take their provers next to the object (`proversOf`, E2E/BridgePrivacy.lean).
- One slot of the proof file's protocol: nothing at several requests of a batch; the key file's and
  a copy's file's provers have no such condition here.
- The clause rel says «written for some OOD seed», not the private input's own (`relAt`). The
  private input's own OOD sample is held by the clause key only, through `keyAt`. That the key holds
  the whole sample is the library's `keyOf_injective` (OnBytes/Slice/KeyOfRecInj.lean), which is not
  called here. `TiedYes` in E2E/BridgeJoinAtFiles.lean adds the equation outright.
- Whether the library's writing map is one to one, as `rel_iff` (Tied.lean) asks, is not shown.
- The index type is every matrix; `RyesZ Z` holds at matrices in range only. How the condition goes
  over to the object that is cut to the matrices in range (`objAt`, E2E/ObjectAtFiles.lean) is not
  stated in Lean.
- The copy's number n is held by nothing in the object's protocol: `silP` does not read it, and no
  instance has a field for it. (The OOD-seed wire among the compiled verifier's parameters at Z has
  a test on the number, which reads the front round's number: `num_letters`,
  E2E/BridgeJoinAtFiles.lean.) With n in the private input the clause seam could not hold. An honest
  prover at one n says n at every stored copy. Who picks n is not said: it has to be fixed before
  the index, by the environment; a pick that reads anything of the prover's could tell.
- run₂ and run₃ are maps from the types of r2 and r3 to bytes; `silP` reads neither.
- No value is shown to meet the hypotheses together: that some pair is valid at Z, and that two
  indices share one valid explicit input, is not shown here. At a relation that never holds the main
  theorems are vacuous.
- That `protocolDataWellFormed` accepts is a theorem of the side library at the written files `storedPublicFiles` and `zGap`
  (`AtFullSide.Top.theLive_zFull`, `theLive_zGap`); this file, in the main library, cannot call it.
  Where it rejects, `laid_of_live` and `protocol_atFiles` say nothing.
- That `RyesZ Z i x'` gives «the index is in range» for the prover's own test, and a trace of the
  request, is not shown. The second is a matter of the prover's trace, at every request at which the
  relaxed relation holds.
- That the stored positions which a run asks for lie among the external reads is not shown.
- `seed_ne_zero` and `key_fits` are two facts. The three hypotheses of `key_fits` are shown at no
  shape of Z, and nothing says that these are the only tests that depend on the committer's coins or
  the OOD seed.
- `Tied` does not bar a description that rejects early at every coin. Nothing says that a run is
  played.
- `Tied` may be read as part of a goal; it counts as none.
- It is no statement on what a view shows, and none of zero knowledge.
- No property of a protocol is stated: nothing on completeness, soundness or hiding.
-/
import E2E.ProtocolOverDescription
import E2E.TableStrong
import E2E.ItemsZero
import Johnson.Desc.ProofFile.Honest.Law.Rule.TiedAtItem
import Johnson.Desc.ProofFile.Honest.Law.Rule.Tied
import Johnson.P5J.AtName
import Johnson.P5T.FenceAtMg

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.Committed
open Iop Hiop
open OnBytes (TableKey)
open OnBytes.Flat (Files relationsAndEncodingOfClaims RecFull codingHonest ansL silP front₀ join₀)
open OnBytes.Slice (frS frZ DecR GF ofF ptOf NZ keyOf)
open OnBytes.Maker (WholeD FrontMsg)
open Compile.Joined (JoinMsg)
open VerifiableInference.Desc (FileDescription Chain)
open ProofFile.Honest (Prover KeyAndJoiningRoundMessages batchOf Committer Isk Tied TiedAt relAt tied)
open _root_.Run.PQ (SgX)
open _root_.Run (ckP)

/-! ## 1. The parameters of `Tied` at the format's encoder -/

section AnyConf
variable (C : ConfigurationWithOutOfDomainSample)

/-- The OOD answers at a configuration, as a function of the index, the committer's coins (pads,
encoding randomness) and the OOD seed. The encoding randomness is not read. -/
def ansC (i : C.I) (r : C.Pad × C.Rnd) (s : C.Seed) : C.Ans := C.smp s (C.hold i r.1)

/-- **The object's field `honestOutOfDomainAnswer` is `ansC`**, for every configuration, any three protocols over it and
any provers: by unfolding. -/
theorem ans_obj (F : Files C) (P : F.Provers) (i : C.I) (r : C.Pad × C.Rnd) (s : C.Seed) :
    (F.withProvers P).honestOutOfDomainAnswer i r s = ansC C i r s := rfl

/-- **A valid pair has the OOD answers `ansC`**: in a pair that is valid for the object
(`HolographicProtocol.validB`) the instance's OOD sample is the private input's OOD seed with `ansC` at the private
input, and Ryes holds of the index and the request. By unfolding. -/
theorem valid_obj (F : Files C) (P : F.Provers) (Ryes : C.I → C.X → Prop)
    (w : C.I × (C.Pad × C.Rnd) × C.Seed) (a : C.X × (C.Seed × C.Ans))
    (h : (F.withProvers P).validB Ryes w a) :
    a.2 = (w.2.2, ansC C w.1 w.2.1 w.2.2) ∧ Ryes w.1 a.1 := h

end AnyConf

section Enc
variable {X : Type} (A : (frS.toDecR frZ 402653181).Claims X) (Pad : Type) [Fintype Pad]
  [Nonempty Pad] (holdW : A.Mat → Pad → ℕ → List UInt64)

/-- The configuration of a committed table with the format's encoder. -/
abbrev Cf : ConfigurationWithOutOfDomainSample := DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A (codingHonest frS frZ 402653181 A Pad holdW))

/-- The index committer's coins: pads and encoding randomness. -/
abbrev Coin : Type := (Cf A Pad holdW).Pad × (Cf A Pad holdW).Rnd

/-- The OOD answers of the index i, at the committer's coins r and the OOD seed s. The encoding
randomness is not read. -/
def ansAt (i : (Cf A Pad holdW).I) (r : Coin A Pad holdW) (s : (Cf A Pad holdW).Seed) :
    (Cf A Pad holdW).Ans :=
  (Cf A Pad holdW).smp s ((Cf A Pad holdW).hold i r.1)

/-- The OOD sample: the OOD seed with the answers. -/
def recAt (i : (Cf A Pad holdW).I) (r : Coin A Pad holdW) (s : (Cf A Pad holdW).Seed) : RecFull :=
  (s, ansAt A Pad holdW i r s)

/-- The committed table. -/
def encAt (i : (Cf A Pad holdW).I) (r : Coin A Pad holdW) :
    Fin (Cf A Pad holdW).n → (Cf A Pad holdW).Sg :=
  (Cf A Pad holdW).enc ((Cf A Pad holdW).hold i r.1) r.2

/-- The field values of the column at the position x. -/
def colF (i : (Cf A Pad holdW).I) (r : Coin A Pad holdW) (x : frS.Pos) : List GF :=
  List.ofFn fun a : Fin (2 ^ frS.P.v) =>
    AtPublicFiles.Table.share frS ((Cf A Pad holdW).hold i r.1) a x +
      Code.RS.gen (ptOf frS.P.T.a) (fun t : Fin frS.P.T.r => (t : ℕ)) (r.2 a) x

/-- A symbol of the committed table is its position with the words of the column's field values. -/
theorem enc_col (i : (Cf A Pad holdW).I) (r : Coin A Pad holdW) (x : frS.Pos) :
    encAt A Pad holdW i r x = (x.val, (colF A Pad holdW i r x).map ofF) := by
  have h := AtPublicFiles.Table.honestTab_col frS ((Cf A Pad holdW).hold i r.1) r.2 x
  unfold colF
  rw [List.map_ofFn]
  exact h

/-- For any three protocols over that configuration and any provers, the object's field `encodeIndex` is the
committed table: by unfolding. -/
theorem enc_files (F : Files (Cf A Pad holdW)) (P : F.Provers) (i : (Cf A Pad holdW).I)
    (r : Coin A Pad holdW) : (F.withProvers P).encodeIndex i r = encAt A Pad holdW i r := rfl

/-- The OOD answers are `ansC` of the configuration: by unfolding. -/
theorem ansAt_eq : ansAt A Pad holdW = ansC (Cf A Pad holdW) := rfl

/-- The key as the library's `keyOf` writes it of an OOD sample. -/
def keyAt (rec : RecFull) : TableKey := keyOf (fun β : NZ => β.val) rec

variable {Xi Ky : Type} (wr : X × RecFull → Xi) (key : Xi → Ky) (kp : RecFull → Ky)
  (hr : ∀ a, key (wr a) = kp a.2)

/-- The index committer's structure (`Committer`) at the format's encoder. wr: the writing map. key:
the key as it is read off the explicit input. kp: the key of an OOD sample. hr: the two keys agree
at what wr writes. -/
def cmAt : Committer (Cf A Pad holdW).I (Coin A Pad holdW) (Cf A Pad holdW).Seed X Xi Ky where
  enc := fun i r p => if h : p < 2 ^ frS.P.T.a then some (colF A Pad holdW i r ⟨p, h⟩) else none
  ood := fun k => kp (recAt A Pad holdW k.index k.coins k.seed)
  xi := fun k x' => wr (x', recAt A Pad holdW k.index k.coins k.seed)
  key := key
  tie := fun _ _ => hr _

/-- Beyond the table's length its field `enc` is `none`. -/
theorem cmAt_beyond (i : (Cf A Pad holdW).I) (r : Coin A Pad holdW) (p : ℕ)
    (h : 2 ^ frS.P.T.a ≤ p) : (cmAt A Pad holdW wr key kp hr).enc i r p = none :=
  dif_neg (Nat.not_lt.2 h)

/-- **Its external string is the committed table**: whole symbols; the OOD seed is not read. -/
theorem ext_cmAt
    (w : (Cf A Pad holdW).I × Coin A Pad holdW × (Cf A Pad holdW).Seed) :
    (cmAt A Pad holdW wr key kp hr).ext frS.P.T.a w = encAt A Pad holdW w.1 w.2.1 := by
  funext p
  rw [enc_col]
  show (p.val, ((if h : p.val < 2 ^ frS.P.T.a then some (colF A Pad holdW w.1 w.2.1 ⟨p.val, h⟩)
    else none).getD []).map ofF) = _
  rw [dif_pos p.isLt]
  rfl

variable {R₂ R₃ : Type} (run₂ : R₂ → ByteArray) (run₃ : R₃ → ByteArray)

/-- What the front round sends: the answers, and the copy's number n. -/
def frontAt (n : ℕ) (_ : R₂) (_ : R₃) (i : (Cf A Pad holdW).I) (r : Coin A Pad holdW)
    (s : (Cf A Pad holdW).Seed) (_ : Xi) : FrontMsg (List OnBytes.E) :=
  ⟨ansL (recAt A Pad holdW i r s), n⟩

/-- What the joining round sends: the answers, and the second chain's run value. -/
def joinAt (r2 : R₂) (i : (Cf A Pad holdW).I) (r : Coin A Pad holdW)
    (s : (Cf A Pad holdW).Seed) : JoinMsg (List OnBytes.E) ByteArray :=
  ⟨ansL (recAt A Pad holdW i r s), run₂ r2⟩

/-- What the seam sends: the third chain's run value. -/
def seamAt (_ : R₂) (r3 : R₃) (_ : (Cf A Pad holdW).I) (_ : Coin A Pad holdW)
    (_ : (Cf A Pad holdW).Seed) (_ : Xi) : ByteArray := run₃ r3

/-- The same three values, as functions of the explicit input, n and the two coins only. ansOf: the
answers as they are read off the explicit input. -/
def pubAt (ansOf : Xi → List OnBytes.E) (n : ℕ) (r2 : R₂) (r3 : R₃) (ξ : Xi) :
    FrontMsg (List OnBytes.E) × JoinMsg (List OnBytes.E) ByteArray × ByteArray :=
  (⟨ansOf ξ, n⟩, ⟨ansOf ξ, run₂ r2⟩, run₃ r3)

/-- **The six equations `TiedAt` at the format's encoder**, from three equations on the writing map:
hr, hans and hst. -/
theorem tiedAt_cmAt (n : ℕ) (DP : WholeD) (F : FileDescription Xi) (sh : Ky → F.S₂)
    (ansOf : Xi → List OnBytes.E) (hans : ∀ a, ansOf (wr a) = ansL a.2)
    (hst : ∀ a, F.start₂ (F.pub (wr a)) = sh (key (wr a))) :
    TiedAt (ansAt A Pad holdW) wr (cmAt A Pad holdW wr key kp hr) kp n (DP.at frS.P.T.a) F sh
      (frontAt (Xi := Xi) (R₂ := R₂) (R₃ := R₃) A Pad holdW) (joinAt A Pad holdW run₂)
      (seamAt (Xi := Xi) (R₂ := R₂) A Pad holdW run₃) (pubAt run₂ run₃ ansOf) where
  ood := fun _ => rfl
  writes := fun _ _ => rfl
  start := hst
  full := fun i r p hp => by
    show (if h : p < 2 ^ frS.P.T.a then some (colF A Pad holdW i r ⟨p, h⟩) else none).isSome = true
    rw [dif_pos hp]
    rfl
  silent3 := fun r2 r3 k x' => by
    show (_, _, _) = pubAt run₂ run₃ ansOf n r2 r3
      (wr (x', recAt A Pad holdW k.index k.coins k.seed))
    unfold pubAt
    rw [hans]
    rfl
  reads := hr

end Enc

/-- The factor in an OOD seed is never 0: by its type. -/
theorem seed_ne_zero (rec : RecFull) (i : Fin 1) : ((rec.1 i).2 : NZ).val ≠ 0 :=
  (rec.1 i).2.property

/-- The written key fits every shape with the sample's three numbers. -/
theorem key_fits (rec : RecFull) (sh : OnBytes.Params.IndexShape) (hv : sh.v = frS.P.v)
    (hs : sh.answers = 1) (hl : sh.cubeBits = 29) : (keyAt rec).fits sh = true :=
  OnBytes.Slice.keyOf_fits (fun β : NZ => β.val) rec sh hv hs hl

/-! ## 2. Two types of the explicit input, at the proof file's description -/

section Roads
open LPFD.Full (XF)
open P5J
variable (A : (frS.toDecR frZ 402653181).Claims XF) (Pad : Type) [Fintype Pad] [Nonempty Pad]
  (holdW : A.Mat → Pad → ℕ → List UInt64) (Zp : ProofFile.Pub) (Np : H2U.Places4)
  (cF : Chain TS ProofFile.Cl) {R₂ R₃ : Type} (run₂ : R₂ → ByteArray) (run₃ : R₃ → ByteArray)

/-- The shared chain's first state, as a function of a key. -/
def shAt (k : TableKey) : (F0T OnBytes.secondHashFunction Zp Np cF).S₂ :=
  Desc.K14.first (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).codes k

/-- The answers as they are read off the description's own instance. -/
def ansInst (x : ProofFile.Inst) : List OnBytes.E := x.pub.key.record.toList

/-- Read off what the library's map `instanceAsPlainRecord` writes, they are the answers of the OOD sample, as a
list. -/
theorem ansInst_along (z : XF × RecFull) : ansInst (LPFD.Full.instanceAsPlainRecord z) = ansL z.2 := by
  unfold ansInst ansL
  rfl

/-- The committer's structure where the explicit input is the description's own instance. -/
def cmAlong : Committer (Cf A Pad holdW).I (Coin A Pad holdW) (Cf A Pad holdW).Seed XF ProofFile.Inst
    TableKey :=
  cmAt A Pad holdW LPFD.Full.instanceAsPlainRecord (fun x : ProofFile.Inst => x.pub.key) keyAt fun _ => rfl

/-- The six equations where the explicit input is the description's own instance; the writing map is
the library's `instanceAsPlainRecord`. The three hypotheses of `tiedAt_cmAt` hold by unfolding. -/
theorem tiedAt_along (n : ℕ) (DP : WholeD) :
    TiedAt (ansAt A Pad holdW) LPFD.Full.instanceAsPlainRecord (cmAlong A Pad holdW) keyAt
      n (DP.at frS.P.T.a) (F0T OnBytes.secondHashFunction Zp Np cF) (shAt Zp Np cF)
      (frontAt (Xi := ProofFile.Inst) (R₂ := R₂) (R₃ := R₃) A Pad holdW) (joinAt A Pad holdW run₂)
      (seamAt (Xi := ProofFile.Inst) (R₂ := R₂) A Pad holdW run₃) (pubAt run₂ run₃ ansInst) :=
  tiedAt_cmAt A Pad holdW LPFD.Full.instanceAsPlainRecord (fun x : ProofFile.Inst => x.pub.key) keyAt (fun _ => rfl)
    run₂ run₃ n DP (F0T OnBytes.secondHashFunction Zp Np cF) (shAt Zp Np cF) ansInst ansInst_along
    fun _ => rfl

/-- The proof file's description, pulled back to the object's instances. -/
abbrev descAt : FileDescription (XF × RecFull) := (F0T OnBytes.secondHashFunction Zp Np cF).pull LPFD.Full.instanceAsPlainRecord

/-- The committer's structure where the explicit input is the object's own instance. -/
def cmPulled : Committer (Cf A Pad holdW).I (Coin A Pad holdW) (Cf A Pad holdW).Seed XF
    (XF × RecFull) TableKey :=
  cmAt A Pad holdW id (fun x : XF × RecFull => keyAt x.2) keyAt fun _ => rfl

/-- The six equations where the explicit input is the object's own instance; the description is
pulled back; the writing map is the identity. -/
theorem tiedAt_pulled (n : ℕ) (DP : WholeD) :
    TiedAt (ansAt A Pad holdW) id (cmPulled A Pad holdW) keyAt
      n (DP.at frS.P.T.a) (descAt Zp Np cF) (shAt Zp Np cF)
      (frontAt (Xi := XF × RecFull) (R₂ := R₂) (R₃ := R₃) A Pad holdW) (joinAt A Pad holdW run₂)
      (seamAt (Xi := XF × RecFull) (R₂ := R₂) A Pad holdW run₃)
      (pubAt run₂ run₃ fun x : XF × RecFull => ansL x.2) :=
  tiedAt_cmAt A Pad holdW id (fun x : XF × RecFull => keyAt x.2) keyAt (fun _ => rfl)
    run₂ run₃ n DP (descAt Zp Np cF) (shAt Zp Np cF) (fun x : XF × RecFull => ansL x.2)
    (fun _ => rfl) fun _ => rfl

/-- **Every valid pair is tied, at the format's encoder**, with the description's own instance as
the explicit input: for any three protocols over that configuration, any provers P and any relation
Ryes, every pair that is valid for their object is tied, at what the library's map writes for the
instance. hit: every stored table that a round of the description declares is under the item 0, the
one item at which the prover structure `proverAt 0 H` has the committer's columns. -/
theorem tied_files_along [Inhabited R₃] (n : ℕ) (DP : WholeD) {Tr X₀ Xh : Type}
    (H : Prover (Cf A Pad holdW).I (Coin A Pad holdW) ProofFile.Inst TableKey Tr X₀ Xh)
    (F : Files (Cf A Pad holdW)) (P : F.Provers) (Ryes : (Cf A Pad holdW).I → XF → Prop)
    (w : (Cf A Pad holdW).I × Coin A Pad holdW × (Cf A Pad holdW).Seed) (a : XF × RecFull)
    (hit : AtPublicFiles.AtZero.ItemsZero (F0T OnBytes.secondHashFunction Zp Np cF)) (h : (F.withProvers P).validB Ryes w a) :
    Tied (DP.at frS.P.T.a) (F0T OnBytes.secondHashFunction Zp Np cF) ((cmAlong A Pad holdW).proverAt 0 H)
      (fun r2 r3 => (cmAlong A Pad holdW).seam (frontAt A Pad holdW n r2 r3)
        (joinAt A Pad holdW run₂ r2) (seamAt A Pad holdW run₃ r2 r3))
      ((cmAlong A Pad holdW).ext (DP.at frS.P.T.a).a) (pubAt run₂ run₃ ansInst n)
      (shAt Zp Np cF) (relAt (ansAt A Pad holdW) Ryes LPFD.Full.instanceAsPlainRecord) w (LPFD.Full.instanceAsPlainRecord a) :=
  ProofFile.Honest.tied_atItem (tiedAt_along A Pad holdW Zp Np cF run₂ run₃ n DP) hit H w a
    (by rw [ansAt_eq]; exact valid_obj (Cf A Pad holdW) F P Ryes w a h)

/-- **The same with the object's own instance as the explicit input**: at the instance itself, with
the description pulled back. -/
theorem tied_files_pulled [Inhabited R₃] (n : ℕ) (DP : WholeD) {Tr X₀ Xh : Type}
    (H : Prover (Cf A Pad holdW).I (Coin A Pad holdW) (XF × RecFull) TableKey Tr X₀ Xh)
    (F : Files (Cf A Pad holdW)) (P : F.Provers) (Ryes : (Cf A Pad holdW).I → XF → Prop)
    (w : (Cf A Pad holdW).I × Coin A Pad holdW × (Cf A Pad holdW).Seed) (a : XF × RecFull)
    (hit : AtPublicFiles.AtZero.ItemsZero (descAt Zp Np cF)) (h : (F.withProvers P).validB Ryes w a) :
    Tied (DP.at frS.P.T.a) (descAt Zp Np cF) ((cmPulled A Pad holdW).proverAt 0 H)
      (fun r2 r3 => (cmPulled A Pad holdW).seam (frontAt A Pad holdW n r2 r3)
        (joinAt A Pad holdW run₂ r2) (seamAt A Pad holdW run₃ r2 r3))
      ((cmPulled A Pad holdW).ext (DP.at frS.P.T.a).a)
      (pubAt run₂ run₃ (fun x : XF × RecFull => ansL x.2) n)
      (shAt Zp Np cF) (relAt (ansAt A Pad holdW) Ryes id) w a :=
  ProofFile.Honest.tied_atItem (tiedAt_pulled A Pad holdW Zp Np cF run₂ run₃ n DP) hit H w a
    (by rw [ansAt_eq]; exact valid_obj (Cf A Pad holdW) F P Ryes w a h)

/-- The library's test on the proof file's three plain parts, read off the description's own
instance: both copies of the answers are the entries of the key's array. -/
def silInst (x : ProofFile.Inst) (f : FrontMsg (List OnBytes.E)) (j : JoinMsg (List OnBytes.E) ByteArray)
    (_ : ByteArray) : Bool :=
  decide (f.answers = ansInst x) && decide (j.answers = ansInst x)

/-- **The writing map keeps the answers**: the library's test `silP` on the plain parts at an
instance is `silInst` at what is written for it. -/
theorem silP_along (z : XF × RecFull) (f : FrontMsg (List OnBytes.E))
    (j : JoinMsg (List OnBytes.E) ByteArray) (t : ByteArray) :
    silP z f j t = silInst (LPFD.Full.instanceAsPlainRecord z) f j t := by
  unfold silP silInst
  rw [ansInst_along]

end Roads

/-! ## 3. At three public files Z -/

section AtZ
open AtPublicFiles.AtFiles
open OnBytes.Flat (claimsLedgerOnAt)
open VerifiableInference.OnPublicFiles (numsRef ppAtFiles)
open LPFD.Full (XF)
open VerifierAndGoals (PublicFiles asDescriptionFiles)
open FlashProve (dataAtFiles)
open FlashProve (protocolDataWellFormed flashProveData)
open P5J

/-- The claims at Z. -/
abbrev AZ (Z : PublicFiles) : (frS.toDecR frZ 402653181).Claims XF :=
  claimsLedgerOnAt (frS.toDecR frZ 402653181) numsRef (ppAtFiles (asDescriptionFiles Z).pol (asDescriptionFiles Z).KL)
    Subtype.val

/-- The pads' type is not empty. (Proved by hand: Lean's search for this instance runs out of time
here.) -/
theorem pads_nonempty (S : OnBytes.Slice.Sz) (cut : ℕ) : Nonempty (OnBytes.Flat.PadsOf S cut) :=
  ⟨fun _ _ => 0⟩

/-- The pads' type, at the full size. -/
abbrev PadZ : Type := OnBytes.Flat.PadsOf frS 402653181

local instance (priority := high) : Nonempty PadZ := pads_nonempty frS 402653181

/-- How a matrix is held, at the full size. Z occurs in its type only. -/
abbrev holdZ (Z : PublicFiles) : (AZ Z).Mat → PadZ → ℕ → List UInt64 :=
  OnBytes.Flat.cellWords frS frZ 402653181 numsRef

/-- The four types of the private input are those of the object's configuration: by unfolding. -/
theorem conf_types (Z : PublicFiles) :
    (Cf (AZ Z) PadZ (holdZ Z)).I = (Cz Z).I ∧ (Cf (AZ Z) PadZ (holdZ Z)).Pad = (Cz Z).Pad ∧
      (Cf (AZ Z) PadZ (holdZ Z)).Rnd = (Cz Z).Rnd ∧ (Cf (AZ Z) PadZ (holdZ Z)).Seed = (Cz Z).Seed :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The relation is that of the object's configuration: by unfolding. -/
theorem ryes_obj (Z : PublicFiles) (i : FullSizeMatrix) (x' : XF) :
    (Cf (AZ Z) PadZ (holdZ Z)).Ryes i x' () = (Cz Z).Ryes i x' () := rfl

/-- The committed table is the object's field `encodeIndex`, for all provers: by unfolding. -/
theorem enc_obj (Z : PublicFiles) (P : (filesAt Z).Provers) (i : FullSizeMatrix) (r : ((filesAt Z).withProvers P).EncodingRandomness) :
    ((filesAt Z).withProvers P).encodeIndex i r = encAt (AZ Z) PadZ (holdZ Z) i r := rfl

/-- **The object's configuration `Cz Z` is `Cf`** at Z's claims, the library's pads and its way of
holding a matrix of cells: by unfolding. -/
theorem conf_eq (Z : PublicFiles) : Cz Z = Cf (AZ Z) PadZ (holdZ Z) := rfl

/-- The relation at Z: that of the object's configuration: the matrix is in range, and the claim of
the instance on it holds. -/
def RyesZ (Z : PublicFiles) (i : FullSizeMatrix) (x' : XF) : Prop := (Cz Z).Ryes i x' ()

/-- **Written out, it is the model's relaxed relation**: the matrix is in range, and it holds an
index at which some trace meets the relaxed relation with the cost ledger, at the protocol's prime
and at the table of scales and policy that the library's reader returns at Z's files (the
reference's where it refuses). -/
theorem ryesZ_iff (Z : PublicFiles) (i : FullSizeMatrix) (x' : XF) :
    RyesZ Z i x' ↔ inRange i ∧
      VerifiableInference.OnPublicFiles.Flat.RelLAt (ppAtFiles (asDescriptionFiles Z).pol (asDescriptionFiles Z).KL) i x'.val :=
  Iff.rfl

/-- It is the relation as the library spells it at a configuration. -/
theorem ryesZ_ex (Z : PublicFiles) (i : FullSizeMatrix) (x' : XF) : RyesZ Z i x' ↔ ∃ c, (Cz Z).Ryes i x' c :=
  ⟨fun h => ⟨(), h⟩, fun ⟨_, h⟩ => h⟩

/-- **The committer's external string is the object's field `encodeIndex`**, whole symbols, for all provers.
-/
theorem ext_obj (Z : PublicFiles) (P : (filesAt Z).Provers)
    (w : FullSizeMatrix × ((filesAt Z).withProvers P).EncodingRandomness × ((filesAt Z).withProvers P).OutOfDomainSeed) :
    (cmAlong (AZ Z) PadZ (holdZ Z)).ext frS.P.T.a w = ((filesAt Z).withProvers P).encodeIndex w.1 w.2.1 :=
  ext_cmAt (AZ Z) PadZ (holdZ Z) _ _ _ _ w

/-- The same for `cmPulled`. -/
theorem ext_obj_pulled (Z : PublicFiles) (P : (filesAt Z).Provers)
    (w : FullSizeMatrix × ((filesAt Z).withProvers P).EncodingRandomness × ((filesAt Z).withProvers P).OutOfDomainSeed) :
    (cmPulled (AZ Z) PadZ (holdZ Z)).ext frS.P.T.a w = ((filesAt Z).withProvers P).encodeIndex w.1 w.2.1 :=
  ext_cmAt (AZ Z) PadZ (holdZ Z) _ _ _ _ w

section Named
variable (Z : PublicFiles) (P : (filesAt Z).Provers) (Zp : ProofFile.Pub) (Np : H2U.Places4)
  (cF : Chain TS ProofFile.Cl) {R₂ R₃ : Type} [Inhabited R₃] (run₂ : R₂ → ByteArray)
  (run₃ : R₃ → ByteArray) (n : ℕ) {Tr X₀ Xh : Type}

/-- **Every valid pair is tied, at the object at Z**, with the description's own instance as the
explicit input: every pair (private input, instance) that is valid for the object, at the relation
`RyesZ Z`, is tied at what the library's map writes for the instance. Free parameters: (Zp, Np, cF),
under hit: any description of that family whose declared stored tables are all under the item 0, not
only the one of which `LaidAt` holds at Z (`laid_of_live`; `tied_live` in E2E/TiedAlong.lean has
`LaidAt`, the protocol and this conclusion at one description); the prover structure H; n; the types
of the two coins with run₂, run₃. Not read: P and the three protocols (`validB` reads only the
object's `honestOutOfDomainAnswer`); of the rounds' data only the depth. -/
theorem tied_atFiles_along
    (H : Prover FullSizeMatrix ((filesAt Z).withProvers P).EncodingRandomness ProofFile.Inst TableKey Tr X₀ Xh)
    (w : FullSizeMatrix × ((filesAt Z).withProvers P).EncodingRandomness × ((filesAt Z).withProvers P).OutOfDomainSeed) (a : XF × RecFull)
    (hit : AtPublicFiles.AtZero.ItemsZero (F0T OnBytes.secondHashFunction Zp Np cF))
    (h : ((filesAt Z).withProvers P).validB (RyesZ Z) w a) :
    Tied ((dataAtFiles flashProveData Z).DP.at frS.P.T.a) (F0T OnBytes.secondHashFunction Zp Np cF)
      ((cmAlong (AZ Z) PadZ (holdZ Z)).proverAt 0 H)
      (fun r2 r3 => (cmAlong (AZ Z) PadZ (holdZ Z)).seam (frontAt (AZ Z) PadZ (holdZ Z) n r2 r3)
        (joinAt (AZ Z) PadZ (holdZ Z) run₂ r2) (seamAt (AZ Z) PadZ (holdZ Z) run₃ r2 r3))
      ((cmAlong (AZ Z) PadZ (holdZ Z)).ext ((dataAtFiles flashProveData Z).DP.at frS.P.T.a).a)
      (pubAt run₂ run₃ ansInst n) (shAt Zp Np cF)
      (relAt (ansAt (AZ Z) PadZ (holdZ Z)) (RyesZ Z) LPFD.Full.instanceAsPlainRecord) w (LPFD.Full.instanceAsPlainRecord a) :=
  tied_files_along (AZ Z) PadZ (holdZ Z) Zp Np cF run₂ run₃ n (dataAtFiles flashProveData Z).DP H (filesAt Z) P
    (RyesZ Z) w a hit h

/-- **The same with the object's own instance as the explicit input**: at the instance itself, with
the description pulled back. -/
theorem tied_atFiles_pulled
    (H : Prover FullSizeMatrix ((filesAt Z).withProvers P).EncodingRandomness (XF × RecFull) TableKey Tr X₀ Xh)
    (w : FullSizeMatrix × ((filesAt Z).withProvers P).EncodingRandomness × ((filesAt Z).withProvers P).OutOfDomainSeed) (a : XF × RecFull)
    (hit : AtPublicFiles.AtZero.ItemsZero (descAt Zp Np cF))
    (h : ((filesAt Z).withProvers P).validB (RyesZ Z) w a) :
    Tied ((dataAtFiles flashProveData Z).DP.at frS.P.T.a) (descAt Zp Np cF)
      ((cmPulled (AZ Z) PadZ (holdZ Z)).proverAt 0 H)
      (fun r2 r3 => (cmPulled (AZ Z) PadZ (holdZ Z)).seam (frontAt (AZ Z) PadZ (holdZ Z) n r2 r3)
        (joinAt (AZ Z) PadZ (holdZ Z) run₂ r2) (seamAt (AZ Z) PadZ (holdZ Z) run₃ r2 r3))
      ((cmPulled (AZ Z) PadZ (holdZ Z)).ext ((dataAtFiles flashProveData Z).DP.at frS.P.T.a).a)
      (pubAt run₂ run₃ (fun x : XF × RecFull => ansL x.2) n) (shAt Zp Np cF)
      (relAt (ansAt (AZ Z) PadZ (holdZ Z)) (RyesZ Z) id) w a :=
  tied_files_pulled (AZ Z) PadZ (holdZ Z) Zp Np cF run₂ run₃ n (dataAtFiles flashProveData Z).DP H (filesAt Z)
    P (RyesZ Z) w a hit h

end Named

/-- **Where the IOP's own test on the public files accepts, `LaidAt` holds of some (Zp, Np, cF)**:
so some value meets the hypothesis L of `protocol_atFiles`. By two theorems of the library,
`laid_at_name` and `laid_opensK`. -/
theorem laid_of_live (Z : PublicFiles) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) :
    ∃ Zp Np cF, LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL (FlashProve.theProofData (asDescriptionFiles Z))
      (FlashProve.theProofRun (asDescriptionFiles Z)) Zp Np cF := by
  obtain ⟨Zp, Np, cF, L, -⟩ := laid_opensK (laid_at_name live)
  exact ⟨Zp, Np, cF, L⟩

/-- **Where that test accepts, the object's batch protocol is `batchOf` at `descAt Zp Np cF`**, the
pulled-back description. `batchOf` is the protocol for which `honestBatchProverOfFile` builds an honest prover. -/
theorem protocol_atFiles (Z : PublicFiles) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) {D : WholeD}
    {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) :
    (filesAt Z).batch =
      batchOf (ckP .two) ((dataAtFiles flashProveData Z).DP.at frS.P.T.a) (front₀ (dataAtFiles flashProveData Z).G.z₀.2)
        (join₀ (dataAtFiles flashProveData Z).G.z₀.2) ByteArray.empty (descAt Zp Np cF) silP := by
  have e : (descAt Zp Np cF).run = (dataAtFiles flashProveData Z).runP :=
    (L.run.symm.trans (run_eq_of_laid Z live (D, r) L.laidPOf).symm)
  rw [← filesWith_eq Z (descAt Zp Np cF) e]
  rfl

end AtZ

end AtPublicFiles.Committed

#print axioms AtPublicFiles.Committed.pads_nonempty
#print axioms AtPublicFiles.Committed.ans_obj
#print axioms AtPublicFiles.Committed.valid_obj
#print axioms AtPublicFiles.Committed.enc_col
#print axioms AtPublicFiles.Committed.enc_files
#print axioms AtPublicFiles.Committed.ansAt_eq
#print axioms AtPublicFiles.Committed.cmAt_beyond
#print axioms AtPublicFiles.Committed.ext_cmAt
#print axioms AtPublicFiles.Committed.tiedAt_cmAt
#print axioms AtPublicFiles.Committed.seed_ne_zero
#print axioms AtPublicFiles.Committed.key_fits
#print axioms AtPublicFiles.Committed.ansInst_along
#print axioms AtPublicFiles.Committed.tiedAt_along
#print axioms AtPublicFiles.Committed.tiedAt_pulled
#print axioms AtPublicFiles.Committed.tied_files_along
#print axioms AtPublicFiles.Committed.tied_files_pulled
#print axioms AtPublicFiles.Committed.silP_along
#print axioms AtPublicFiles.Committed.conf_types
#print axioms AtPublicFiles.Committed.ryes_obj
#print axioms AtPublicFiles.Committed.enc_obj
#print axioms AtPublicFiles.Committed.conf_eq
#print axioms AtPublicFiles.Committed.ryesZ_iff
#print axioms AtPublicFiles.Committed.ryesZ_ex
#print axioms AtPublicFiles.Committed.ext_obj
#print axioms AtPublicFiles.Committed.ext_obj_pulled
#print axioms AtPublicFiles.Committed.tied_atFiles_along
#print axioms AtPublicFiles.Committed.tied_atFiles_pulled
#print axioms AtPublicFiles.Committed.laid_of_live
#print axioms AtPublicFiles.Committed.protocol_atFiles
#print axioms AtPublicFiles.Committed.ansC
#print axioms AtPublicFiles.Committed.Cf
#print axioms AtPublicFiles.Committed.Coin
#print axioms AtPublicFiles.Committed.ansAt
#print axioms AtPublicFiles.Committed.recAt
#print axioms AtPublicFiles.Committed.encAt
#print axioms AtPublicFiles.Committed.colF
#print axioms AtPublicFiles.Committed.keyAt
#print axioms AtPublicFiles.Committed.cmAt
#print axioms AtPublicFiles.Committed.frontAt
#print axioms AtPublicFiles.Committed.joinAt
#print axioms AtPublicFiles.Committed.seamAt
#print axioms AtPublicFiles.Committed.pubAt
#print axioms AtPublicFiles.Committed.shAt
#print axioms AtPublicFiles.Committed.ansInst
#print axioms AtPublicFiles.Committed.cmAlong
#print axioms AtPublicFiles.Committed.descAt
#print axioms AtPublicFiles.Committed.cmPulled
#print axioms AtPublicFiles.Committed.silInst
#print axioms AtPublicFiles.Committed.AZ
#print axioms AtPublicFiles.Committed.PadZ
#print axioms AtPublicFiles.Committed.holdZ
#print axioms AtPublicFiles.Committed.RyesZ
