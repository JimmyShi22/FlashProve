-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/LinkValueLaws.lean: the rounds of OnBytes/Maker/LinkValue.lean and the block of
OnBytes/Maker/Link.lean are those under which the verifier program reads and judges an entry's
chain.

Main theorems.
  `linkBlock_rounds`: at every instance whose two keys fit the tables' shape, the dry run of the
    block states the rounds at keys of zeros. So the rounds do not depend on the instance.
  `linkRounds_owed`: the same with `linkRounds`, where the dry run at keys of zeros succeeds: what
    `iorLink` (OnBytes/Maker/Link.lean) leaves to its caller, for the records whose keys fit.
  `link_value`: if `Tie.entrySpec` gives a block and a description at two tables, then each table
    has a key, the block is `linkBlock` at the pair of these keys, and the description is `linkSpec`
    with the link's statement on the two tables in the place of the empty one.
  `link_data`: at every statement, the kit of challenges, the number of hash blocks, the rounds'
    data, the depth and the openings of the stored tables are those of `linkData p (linkRounds p)`.
  `accept_reStated`: a yes of the compiled verifier at a description with another statement, carried
    to the description itself. It holds of every description. `link_accept_one`: the same at
    `linkSpec`, in the letters of the data that `linkValue` takes (`AcceptsAtOne`).
  `link_check`: if the program's check of an entry file says yes, the chain was read under
    `linkSpec` with the link's statement; under the limits tests the compiled verifier accepts what
    was read, at the decision of `linkBlock` at the pair of the tables' keys. The limits tests are
    three hypotheses: `withinX` and `smallFX` at the description with the statement, and a first
    root of 32 bytes. Nothing shows that the program's check makes them. `link_check_one`: the
    same with `AcceptsAtOne` as the conclusion.
  `linkValue_of_ok`, `linkValue_refuses`: where the dry run at keys of zeros succeeds the value is
    `iorLink` at `linkRounds p`; where it fails the value refuses everything.
  `linkValue_accept`, `linkValue_isLocal`: the value's decision at an instance; the value is local.

The record's type in `link_value` and `link_check` is the program's own, `TableKey`, with the
identity as `key`.

What is not claimed. That `Tie.entrySpec` gives a description, or that the dry run succeeds. What
the dry run states at a record whose key does not fit the tables' shape. That a key which the
program makes is written of a record of any other type. Nothing on soundness. In `accept_reStated`
and `link_check` the typed oracle functions are tied to those that the format's hash induces by an
equation between terms of two types (`HEq`): the rounds' data at two statements are equal by a
theorem, not by evaluation. The compiled verifier there is the one whose first query holds no
record (`Tie.CompiledAcceptsX`), at the trivial instance, and at an interface that is another for
each pair of keys. The decision in `link_check` is the block's; it is the value's (`linkDecide`)
where `linkOk p = true`, which no statement here draws from the check's yes. No equation here speaks
of the compiled verifier of the value's own protocol.

What a caller has to bring. `linkRounds_owed`: that the dry run at keys of zeros succeeds, and that
both keys fit. `link_check`, `link_check_one`: the three tests.


-/
import OnBytes.Maker.LinkValue
import OnBytes.Maker.TerminalLaws
import OnBytes.Iop.DrySizes
import OnBytes.Slice.TopNames

set_option autoImplicit false

namespace OnBytes.Maker

open _root_.Iop Rom Compile Compile.Batch _root_.Run _root_.Run.PQ
open OnBytes.Tie (xdOf inFile withinX CompiledAcceptsX smallFX entrySpec entryStatement)
open OnBytes.Slice (reStated accept_to)

/-- The rounds that the dry run of a link's block states depend on the tables' keys through their
sizes and items alone (`linkVerify_rounds_sizes`, OnBytes/Iop/DrySizes.lean). -/
theorem linkDry (S : OnBytes.Params.LinkShape) : OnBytes.Params.LinkDryBySizes S :=
  fun st _ _ _ _ f0 f0' f1 f1' i0 i1 => linkVerify_rounds_sizes st f0 f0' f1 f1' i0 i1

/-- A key that names the item is the key with that item laid. -/
theorem item_laid {k : TableKey} {item : Nat} (h : k.item = item) :
    ({ k with item := item } : TableKey) = k := by
  subst h
  rfl

/-- **The rounds do not depend on the instance**: at every pair of records whose keys fit the
tables' shape, the dry run of the block states the rounds at keys of zeros, or fails as that one
does. -/
theorem linkBlock_rounds {R : Type} (key : R → TableKey) (p : OnBytes.Params.Link) (rr : R × R)
    (h1 : (key rr.1).fits p.link.table = true) (h2 : (key rr.2).fits p.link.table = true) :
    (linkBlock key p rr).rounds (Entry.start p) = OnBytes.Params.entryRoundsAny p :=
  linkVerify_rounds_sizes (Entry.start p) h1 (OnBytes.Params.zeroKey_fits _ _) h2
    (OnBytes.Params.zeroKey_fits _ _) rfl rfl

/-- **What `iorLink` leaves to its caller**: if the dry run at keys of zeros succeeds, then at every
pair of records whose keys fit the tables' shape the dry run of the block states `linkRounds p`. -/
theorem linkRounds_owed {R : Type} (key : R → TableKey) (p : OnBytes.Params.Link)
    (hp : (OnBytes.Params.entryRoundsAny p).isSome = true) (rr : R × R)
    (h1 : (key rr.1).fits p.link.table = true) (h2 : (key rr.2).fits p.link.table = true) :
    (linkBlock key p rr).rounds (Entry.start p) = some (linkRounds p) := by
  rw [linkBlock_rounds key p rr h1 h2]
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 hp
  unfold linkRounds
  rw [hr]
  rfl

section
variable {p : OnBytes.Params.Link} {first further : OnBytes.Params.TableName} {block : Blk Unit}
  {S : Fmt.SpecX}

/-- **The block and the description under which the program reads an entry's chain**: each table
has a key; the block is the link's block at the pair of these keys; the description is `linkSpec`
with the link's statement on the two tables. -/
theorem link_value (h : entrySpec p first further = some (block, S)) :
    ∃ k0 k1, tableKey p.given.plan.field p.given.cfg p.link.table first 0 = some k0 ∧
      tableKey p.given.plan.field p.given.cfg p.link.table further 1 = some k1 ∧
      block = linkBlock id p (k0, k1) ∧
      S = reStated (linkSpec p) (OnBytes.Params.Link.statement first further) := by
  obtain ⟨⟨k0, k1, h0, h1, hb⟩, r, hr, hS⟩ := OnBytes.Params.entrySpec_eq_any (linkDry p.link) h
  refine ⟨k0, k1, h0, h1, ?_, ?_⟩
  · rw [hb]
    unfold linkBlock
    exact congrArg₂ (linkVerify p.link) (item_laid (OnBytes.Params.tableKey_fits h0).2).symm
      (item_laid (OnBytes.Params.tableKey_fits h1).2).symm
  · have e : linkRounds p = r := by
      unfold linkRounds
      rw [hr]
      rfl
    rw [hS]
    unfold linkSpec
    rw [e]
    rfl

end

/-- **At every statement the data are those of `linkData p (linkRounds p)`**, and the kit of
challenges is the one of hash blocks at the plan's field. -/
theorem link_data (p : OnBytes.Params.Link) (x : ByteArray)
    (stm : ByteArray → ByteArray → ByteArray) :
    (xdOf (reStated (linkSpec p) x) stm).C = ckP p.given.plan.field ∧
      (xdOf (reStated (linkSpec p) x) stm).K = (linkData p (linkRounds p)).K ∧
      (xdOf (reStated (linkSpec p) x) stm).ds = (linkData p (linkRounds p)).ds ∧
      (xdOf (reStated (linkSpec p) x) stm).a = (linkData p (linkRounds p)).a ∧
      (xdOf (reStated (linkSpec p) x) stm).xs = (linkData p (linkRounds p)).xs :=
  ⟨rfl,
    congrArg (kMax fun e k => (bsRound (linkSpec p).base.plan.field e k).b)
      (_root_.Run.rds_congr (inFile (reStated (linkSpec p) x).base) (inFile (linkSpec p).base)
        rfl rfl),
    _root_.Run.rds_congr _ _ rfl rfl, rfl, rfl⟩

/-- **A yes of the compiled verifier at a description with another statement, carried to the
description itself.** The typing at S makes a string from what was read, and the compiled verifier
of the protocol made from S accepts it under typed oracle functions that are equal, as terms of two
types, to those that the format's hash induces for the description with the statement x. -/
theorem accept_reStated (S : Fmt.SpecX) (stm₀ : ByteArray → ByteArray → ByteArray)
    (dec : View → Bool) (x : ByteArray) (stm : ByteArray → ByteArray → ByteArray)
    (r0 r1 : ByteArray) (o : Fmt.ChainOut) (ha : CompiledAcceptsX (reStated S x) stm dec r0 r1 o) :
    ∃ (π : OneProtocolProof 256 (skeletonOverBothExternalStrings (xdOf S stm₀).C (xdOf S stm₀).ds (xdOf S stm₀).a (xdOf S stm₀).xs
                      dec).up)
      (g : Fam (spec 256 ((xdOf S stm₀).K + 1) ((xdOf S stm₀).L dec))),
      toBPrfX S.base.plan.salt S.base.cfg (xdOf S stm₀).C (xdOf S stm₀).ds (xdOf S stm₀).a
        (xdOf S stm₀).xs dec o = some π ∧
      HEq g (famX (xdOf (reStated S x) stm) dec Fmt.oracle ((xdOf (reStated S x) stm).K + 1)) ∧
      (verifyOneProtocol (lam := 256) (K := (xdOf S stm₀).K + 1) (L := (xdOf S stm₀).L dec)
        (256 + 8 * S.base.plan.salt) 256 .link
        (skeletonOverBothExternalStrings (xdOf S stm₀).C (xdOf S stm₀).ds (xdOf S stm₀).a (xdOf S stm₀).xs dec).up
        (wqX (xdOf S stm₀).C (xdOf S stm₀).K (chalP S.base.plan.field (xdOf S stm₀).K)
          (xdOf S stm₀).ds (xdOf S stm₀).a (xdOf S stm₀).xs dec)
        (fun p s => some (.inr ⟨Tag.link, ⟨p, s⟩⟩))
        (embPX (xdOf S stm₀).C (xdOf S stm₀).ds (xdOf S stm₀).a (xdOf S stm₀).xs dec
          (fun _ _ p => (p.val, [])) (fun _ => some ()))
        (fun _ => none) (fun s => some (.inl s)) 0 [bytesToDig r0, bytesToDig r1] () π).det g =
        true := by
  obtain ⟨π', hty', hv'⟩ := ha
  exact accept_to (ckP S.base.plan.field)
    (kMax fun e k => (bsRound S.base.plan.field e k).b) (fun K => chalP S.base.plan.field K)
    (xdOf S stm₀).a (xdOf S stm₀).xs dec (rds (inFile S.base)) (rds (inFile (reStated S x).base))
    (_root_.Run.rds_congr _ _ rfl rfl) S.base.plan.salt S.base.cfg (256 + 8 * S.base.plan.salt)
    (bytesToDig r0) (bytesToDig r1) o (famX (xdOf (reStated S x) stm) dec Fmt.oracle _) π' hty' hv'

/-- What `link_accept_one` concludes. At the one description, in the letters of
`linkData p (linkRounds p)`, which are the data that `linkValue` takes: the library's typing makes a
typed string from the chain o as read, and the compiled verifier of one slot accepts it under the
roots r0 and r1, at the decision dec, under typed oracle functions that are equal, as terms of two
types, to those that the format's hash induces for the description with the statement x. -/
def AcceptsAtOne (p : OnBytes.Params.Link) (dec : View → Bool) (x : ByteArray)
    (stm : ByteArray → ByteArray → ByteArray) (r0 r1 : ByteArray) (o : Fmt.ChainOut) : Prop :=
  ∃ (π : OneProtocolProof 256 (skeletonOverBothExternalStrings (ckP p.given.plan.field) (linkData p (linkRounds p)).ds
                    (linkData p (linkRounds p)).a (linkData p (linkRounds p)).xs dec).up)
    (g : Fam (spec 256 ((linkData p (linkRounds p)).K + 1) ((linkData p (linkRounds p)).L dec))),
    toBPrfX p.given.plan.salt p.given.cfg (ckP p.given.plan.field)
      (linkData p (linkRounds p)).ds (linkData p (linkRounds p)).a
      (linkData p (linkRounds p)).xs dec o = some π ∧
    HEq g (famX (xdOf (reStated (linkSpec p) x) stm) dec Fmt.oracle
      ((xdOf (reStated (linkSpec p) x) stm).K + 1)) ∧
    (verifyOneProtocol (lam := 256) (K := (linkData p (linkRounds p)).K + 1)
      (L := (linkData p (linkRounds p)).L dec) (256 + 8 * p.given.plan.salt) 256 .link
      (skeletonOverBothExternalStrings (ckP p.given.plan.field) (linkData p (linkRounds p)).ds
        (linkData p (linkRounds p)).a (linkData p (linkRounds p)).xs dec).up
      (wqX (ckP p.given.plan.field) (linkData p (linkRounds p)).K
        (chalP p.given.plan.field (linkData p (linkRounds p)).K) (linkData p (linkRounds p)).ds
        (linkData p (linkRounds p)).a (linkData p (linkRounds p)).xs dec)
      (fun p s => some (.inr ⟨Tag.link, ⟨p, s⟩⟩))
      (embPX (ckP p.given.plan.field) (linkData p (linkRounds p)).ds
        (linkData p (linkRounds p)).a (linkData p (linkRounds p)).xs dec
        (fun _ _ p => (p.val, [])) (fun _ => some ()))
      (fun _ => none) (fun s => some (.inl s)) 0 [bytesToDig r0, bytesToDig r1] () π).det g =
      true

/-- `accept_reStated` at `linkSpec p`. -/
theorem link_accept_one (p : OnBytes.Params.Link) (dec : View → Bool) (x : ByteArray)
    (stm : ByteArray → ByteArray → ByteArray) (r0 r1 : ByteArray) (o : Fmt.ChainOut)
    (ha : CompiledAcceptsX (reStated (linkSpec p) x) stm dec r0 r1 o) :
    AcceptsAtOne p dec x stm r0 r1 o :=
  accept_reStated (linkSpec p) (fun _ _ => ByteArray.empty) dec x stm r0 r1 o ha

/-- **From a yes of the program's check of an entry file to the one protocol at an instance.** The
parameter bytes are read as p; each table has a key; the reader `readIn` reads a chain from some
byte offset j of the file (not shown to be the one that `Entry.check` used) under `linkSpec p` with
the link's statement. Given the limits tests `withinX` and `smallFX` at that description and a first
root of 32 bytes, the compiled verifier accepts what was read, at the decision of `linkBlock` at the
pair of the two keys. -/
theorem link_check (params : ByteArray) (first further : OnBytes.Params.TableName)
    (file : ByteArray) (h : Entry.check params first file = .ok further) :
    ∃ (p : OnBytes.Params.Link) (k0 k1 : TableKey) (j : ℕ) (r : ChainRead) (s' : Session),
      OnBytes.Params.Link.read params = some p ∧
      tableKey p.given.plan.field p.given.cfg p.link.table first 0 = some k0 ∧
      tableKey p.given.plan.field p.given.cfg p.link.table further 1 = some k1 ∧
      readIn (reStated (linkSpec p) (OnBytes.Params.Link.statement first further)) file j
        Session.start = some (r, s') ∧
      (withinX (reStated (linkSpec p) (OnBytes.Params.Link.statement first further)) = true →
        smallFX (reStated (linkSpec p) (OnBytes.Params.Link.statement first further)) file = true →
        first.root.size = 32 →
        CompiledAcceptsX (reStated (linkSpec p) (OnBytes.Params.Link.statement first further))
          (entryStatement first further) ((linkBlock id p (k0, k1)).decides (Entry.start p))
          first.root further.root r.out) := by
  obtain ⟨p, block, S, j, r, s', hp, hS, hrd, hc⟩ :=
    OnBytes.Tie.entry_check_compiled params first further file h
  obtain ⟨k0, k1, h0, h1, hb, hS'⟩ := link_value hS
  subst hb
  subst hS'
  exact ⟨p, k0, k1, j, r, s', hp, h0, h1, hrd, hc⟩

/-- `link_check` and `link_accept_one` in one: under the same three tests, the compiled verifier at
the one description accepts what was read. -/
theorem link_check_one (params : ByteArray) (first further : OnBytes.Params.TableName)
    (file : ByteArray) (h : Entry.check params first file = .ok further) :
    ∃ (p : OnBytes.Params.Link) (k0 k1 : TableKey) (j : ℕ) (r : ChainRead) (s' : Session),
      OnBytes.Params.Link.read params = some p ∧
      tableKey p.given.plan.field p.given.cfg p.link.table first 0 = some k0 ∧
      tableKey p.given.plan.field p.given.cfg p.link.table further 1 = some k1 ∧
      readIn (reStated (linkSpec p) (OnBytes.Params.Link.statement first further)) file j
        Session.start = some (r, s') ∧
      (withinX (reStated (linkSpec p) (OnBytes.Params.Link.statement first further)) = true →
        smallFX (reStated (linkSpec p) (OnBytes.Params.Link.statement first further)) file = true →
        first.root.size = 32 →
        AcceptsAtOne p ((linkBlock id p (k0, k1)).decides (Entry.start p))
          (OnBytes.Params.Link.statement first further) (entryStatement first further)
          first.root further.root r.out) := by
  obtain ⟨p, k0, k1, j, r, s', hp, h0, h1, hrd, hc⟩ := link_check params first further file h
  exact ⟨p, k0, k1, j, r, s', hp, h0, h1, hrd,
    fun hw hs h32 => link_accept_one p _ _ _ _ _ _ (hc hw hs h32)⟩

/-! ## The value itself -/

section
variable {R : Type} (C : CK) (a : ℕ) (key : R → TableKey) (p : OnBytes.Params.Link)

/-- Where the dry run at keys of zeros succeeds, the decision is the block's. -/
theorem linkDecide_of_ok (h : linkOk p = true) :
    linkDecide key p = fun rr => (linkBlock key p rr).decides (Entry.start p) := by
  funext rr v
  unfold linkDecide
  rw [h, Bool.true_and]

/-- **Where the dry run at keys of zeros succeeds, the value is `iorLink` at `linkRounds p`.** -/
theorem linkValue_of_ok (h : linkOk p = true) :
    linkValue C a key p = iorLink C a key p (linkRounds p) :=
  congrArg (iorX C (linkData p (linkRounds p)).ds a (linkData p (linkRounds p)).xs)
    (linkDecide_of_ok key p h)

/-- **Where that dry run fails, the value refuses**: every instance, all stored tables, every
transcript. -/
theorem linkValue_refuses (h : linkOk p = false) (rr : R × R) (y : (twoExternalStrings (2 ^ a) SgX).Str)
    (τ : Tr (linkValue C a key p).shape) : (linkValue C a key p).out rr y τ = none := by
  have hd : ∀ v, linkDecide key p rr v = false := fun v => by
    unfold linkDecide
    rw [h, Bool.false_and]
  show (if (_ && _ && _ && linkDecide key p rr _) = true then some () else none) = none
  rw [hd, Bool.and_false]
  rfl

/-- The value's decision at an instance is that of Run/PlanQX.lean's skeleton at `linkDecide` at
that instance. -/
theorem linkValue_accept (rr : R × R) :
    (linkValue C a key p).toInteractiveOracleProof.accept rr =
      (skeletonOverBothExternalStrings C (linkData p (linkRounds p)).ds a (linkData p (linkRounds p)).xs
        (linkDecide key p rr)).up.loc.accept () :=
  iorX_accept C _ a _ (linkDecide key p) rr

/-- The value is local. -/
theorem linkValue_isLocal : (linkValue C a key p).IsLocal :=
  iorX_isLocal C _ a _ (linkDecide key p)

end

end OnBytes.Maker

