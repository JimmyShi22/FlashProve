-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/KeyInScope.lean: WHAT THE
KEY FILE'S DESCRIPTION READS OF ITS SOURCE, IN SCOPE, AT ANY DIGEST AND AT ANY FUNCTION IN THE HASH
FUNCTION'S PLACE: THE LIGHT CUT: over the key file's description (Johnson/Desc/Key/:
Source, Desc, Road, FileOk, Slot, SlotIs) and the routine that reads the public files with the hash
function as a letter (Johnson/Desc/Ok/PlanWritten/PublicAt.lean) alone. No law on a block, no frame,
no row stands beneath it. The declarations lie under the namespaces of SourceIs.lean,
AtFreeCfg.lean, ReadAtO.lean, UnitsInScope.lean and OkStartInScope.lean, but stand in this file.

Main names (each under the namespace Johnson.RunOne.Law.‹file›):
  SourceIs: sendsFrom_key_codes · madeAt_parts · sourceOf_parts · desc_clauses (the public tests by
    name all hold) · fk_cut (the clause "cut") · five_at: THE FIVE EQUATIONS AT EVERY DIGEST.
  AtFreeCfg: ReadOf pol Z (it names no hash function) · readOf_publicOf · key_at_chains: the sized
    key is the written keyFull, at any digest.
  ReadAtO: readOf_publicOfO: at every letter o.
  UnitsInScope: wsLay_at_policy · sourceOf_units · units_in_scope.
  OkStartInScope: fk_shape (the clause "shape") · index_full · index_full_no.
  KeyInScope: laid_parts: what these laws spend of Key.keyDataAndDecisionAtFixedDigest's yes, typed once ·
    key_in_scope · five_in_scope: the five at keyFull · shared_lin_in_scope: a sixth.

Object: Key.madeAt · Key.sourceOf · Key.sourceClauses · Key.keyDataAndDecisionAtFixedDigest (laidFixed_is).
User: AtFreeCfg.lean, ReadAtO.lean, UnitsInScope.lean, OkStartInScope.lean, LinksAtO.lean,
ChainAtO.lean, AllAtO.lean.
Letters: Zp: three public files in scope · Z under ReadOf Zp.pol Z · cfg: any digest · o: any.

Limits. The premise on the plan is typed at Key.descriptionFromSource X N P; at the description pulled to the records
it is the same Bool by unfolding. One size. One direction. Nothing on soundness.

-/
import Johnson.Goal.PlanValues.ScopeAtPlan
import Johnson.Goal.PlanValues.KeySizedReturns
import Johnson.Desc.Key.SlotIs
import Johnson.G.SendsFrom
import Johnson.Desc.Ok.PlanWritten.PublicAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.SourceIs
open OnBytes OnBytes.Params
open OnBytes.Params (exc_bind)
open OnBytes.Model.Verify (Public chainsOf)
open Johnson.G (ChainSends sendsFrom)
open Johnson.G.OfPlan (Made)
open VerifiableInference.Desc (FileDescription)
open VerifiableInference.Desc.Key (Source madeAt sourceOf sourceClauses fileClauses)

/-- The first three lists of sendings bear the sized key's codes. -/
theorem sendsFrom_key_codes {c : Configured} {k0 k1 k2 : ChainSends} {r : List ChainSends}
    (h : sendsFrom c = .ok (k0 :: k1 :: k2 :: r)) :
    k0.codes = c.sized.key.codes ∧ k1.codes = c.sized.key.codes ∧
      k2.codes = c.sized.key.codes := by
  unfold sendsFrom at h
  extract_lets z a one K B x at h
  have hone : ∀ (f : String) (ch : Nat) (cs : Codes) (L : List Johnson.G.Listed) (P : Planned)
      (k : ChainSends), one f ch cs L P = .ok k → k.codes = cs := by
    intro f ch cs L P k hk
    simp only [one] at hk
    split at hk
    · obtain ⟨_, _, hk⟩ := exc_bind hk
      obtain ⟨out, _, hk⟩ := exc_bind hk
      cases hk
      rfl
    · obtain ⟨_, e, _⟩ := exc_bind hk
      cases e
  split at h
  · obtain ⟨w1, _, h⟩ := exc_bind h
    obtain ⟨s1, _, h⟩ := exc_bind h
    obtain ⟨w2, _, h⟩ := exc_bind h
    obtain ⟨s2, _, h⟩ := exc_bind h
    rw [List.mapM_cons] at h
    obtain ⟨a0, h0, h⟩ := exc_bind h
    obtain ⟨r0, hr0, h⟩ := exc_bind h
    rw [List.mapM_cons] at hr0
    obtain ⟨a1, h1, hr0⟩ := exc_bind hr0
    obtain ⟨r1, hr1, hr0⟩ := exc_bind hr0
    rw [List.mapM_cons] at hr1
    obtain ⟨a2, h2, hr1⟩ := exc_bind hr1
    obtain ⟨r2, _, hr1⟩ := exc_bind hr1
    cases hr1
    cases hr0
    cases h
    exact ⟨hone _ _ _ _ _ _ h0, hone _ _ _ _ _ _ h1, hone _ _ _ _ _ _ h2⟩
  · cases h

/-- **What the maker's record holds**, at any digest: what was handed in; the chains that the
program's own routine makes at that digest; and sendings of the first chain that bear the sized
key's codes. -/
theorem madeAt_parts {Z : Public} {lay cfg : ByteArray} {m : Made}
    (h : madeAt Z lay cfg = .ok m) :
    m.p.X = Z ∧ chainsOf Z (some lay) cfg = .ok m.p.chains ∧
      m.key.1.codes = m.p.chains.made.sized.key.codes := by
  unfold madeAt at h
  obtain ⟨ch, h1, h⟩ := exc_bind h
  obtain ⟨b, h2, h⟩ := exc_bind h
  obtain ⟨l, h3, h⟩ := exc_bind h
  split at h
  · cases h
    exact ⟨rfl, h1, (sendsFrom_key_codes h3).1⟩
  · cases h

/-- **What the source holds of the maker's record.** -/
theorem sourceOf_parts {m : Made} {X : Source} (h : sourceOf m = .ok X) :
    X.set = m.p.chains.made.sized.key.set ∧
      X.Y.cutShape = m.p.chains.made.sized.key.once.shape ∧ X.Y.cutCodes.1 = m.key.1.codes ∧
      X.Y.cutIdx = m.p.chains.made.sized.key.once.input ∧
      X.Y.cutRanges = m.p.chains.made.sized.key.ranges.x := by
  unfold sourceOf at h
  obtain ⟨D, _, h⟩ := exc_bind h
  obtain ⟨T, _, h⟩ := exc_bind h
  cases h
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

variable (X : Source) (N : H2U.PlaceNums) (P : VerifiableInference.Desc.Key.LaterPlaces)

/-- The public tests by name all hold. -/
theorem desc_clauses (h : (VerifiableInference.Desc.Key.descriptionFromSource X N P).planOk = true) :
    (sourceClauses X.Y).all (·.2) = true := by
  unfold FileDescription.planOk FileDescription.planOkCore at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hf, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := h
  have hf' : ((fileClauses X N P _ _ _).all (·.2) && _) = true := hf
  rw [Bool.and_eq_true] at hf'
  have hc := hf'.1
  unfold fileClauses at hc
  simp only [List.all_append, Bool.and_eq_true] at hc
  exact hc.1.1.1

/-- **The clause "cut", as equations**: the sized values by which the sendings were cut are the
one-time chain's values as read. -/
theorem fk_cut (h : (VerifiableInference.Desc.Key.descriptionFromSource X N P).planOk = true) :
    X.Y.cutShape = X.Y.k.oneTime.lin ∧ X.Y.cutCodes.1 = X.Y.k.oneTime.codes ∧
      X.Y.cutIdx = X.Y.k.oneTime.indexMasks ∧ X.Y.cutRanges = X.Y.k.oneTime.ranges := by
  have e := List.all_eq_true.1 (desc_clauses X N P h)
    ("cut", X.Y.cutShape == X.Y.k.oneTime.lin && X.Y.cutCodes.1 == X.Y.k.oneTime.codes &&
        X.Y.cutCodes.2.1 == X.Y.k.oneTime.codes && X.Y.cutCodes.2.2 == X.Y.k.oneTime.codes &&
        X.Y.cutIdx == X.Y.k.oneTime.indexMasks && X.Y.cutRanges == X.Y.k.oneTime.ranges &&
        X.Y.cutSamples == X.Y.k.oneTime.given.plan.samples)
    (by simp [sourceClauses])
  simp only [Bool.and_eq_true, beq_iff_eq] at e
  obtain ⟨⟨⟨⟨⟨⟨a, b⟩, -⟩, -⟩, c⟩, d⟩, -⟩ := e
  exact ⟨a, b, c, d⟩

variable {X N P}

/-- **THE FIVE EQUATIONS, AT EVERY DIGEST THAT IS HANDED IN.** -/
theorem five_at {Z : Public} {lay cfg : ByteArray} {m : Made} (hm : madeAt Z lay cfg = .ok m)
    (hX : sourceOf m = .ok X)
    (hp : (VerifiableInference.Desc.Key.descriptionFromSource X N P).planOk = true) :
    X.set = m.p.chains.made.sized.key.set ∧
      X.Y.k.oneTime.ranges = m.p.chains.made.sized.key.ranges.x ∧
      X.Y.k.oneTime.lin = m.p.chains.made.sized.key.once.shape ∧
      X.Y.k.oneTime.indexMasks = m.p.chains.made.sized.key.once.input ∧
      X.Y.k.oneTime.codes = m.p.chains.made.sized.key.codes := by
  obtain ⟨s1, s2, s3, s4, s5⟩ := sourceOf_parts hX
  obtain ⟨c1, c2, c3, c4⟩ := fk_cut X N P hp
  exact ⟨s1, c4.symm.trans s5, c1.symm.trans s2, c3.symm.trans s4,
    c2.symm.trans (s3.trans (madeAt_parts hm).2.2)⟩

end Johnson.RunOne.Law.SourceIs

namespace Johnson.RunOne.Law.AtFreeCfg
open OnBytes OnBytes.Model OnBytes.Model.Config OnBytes.Model.Verify
open Lk6.AtPlan

/-- **What these laws spend of "Z is what the program has read of the parameter file pol"**: the
scan of the file and the layout made of it are Z's, and Z's layout of the weights is made of them.
No hash function is named here: whichever routine has read the public files, with whichever hash
function it has held the tables against their digests, pays this by its own text. -/
def ReadOf (pol : ByteArray) (Z : Public) : Prop :=
  ∃ y, polLayout pol = .ok (Z.P, y) ∧
    wsLayOf (weightShape Z.P y) y.h.p3 Z.P.lkW = .ok Z.layers.wsLay

/-- The program's own routine pays it. -/
theorem readOf_publicOf {pol KL : ByteArray} {layout : Option ByteArray} {Z : Public}
    (h : publicOf pol KL layout = .ok Z) : ReadOf pol Z :=
  publicOf_wsLay h

end Johnson.RunOne.Law.AtFreeCfg

namespace Johnson.RunOne.Law.ReadAtO
open OnBytes OnBytes.Model OnBytes.Model.Config OnBytes.Model.Verify
open OnBytes.Params (exc_bind)
open Lk6.AtPlan
open VerifiableInference.PlanWritten (publicOfO)
open Johnson.RunOne.Law.AtFreeCfg

/-- **The routine with the hash function as a letter pays ReadOf, at every letter.** -/
theorem readOf_publicOfO {o : Nat → ByteArray → ByteArray} {pol KL : ByteArray}
    {layout : Option ByteArray} {X : Public} (h : publicOfO o pol KL layout = .ok X) :
    ReadOf pol X := by
  unfold publicOfO at h
  obtain ⟨⟨P, y⟩, h0, h⟩ := exc_bind h
  dsimp only at h
  obtain ⟨sc, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  have h := Fo.Pub.ite_unit_ok h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨ws, hws, h⟩ := exc_bind h
  obtain ⟨rope, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨HLy, _, h⟩ := exc_bind h
  have key : ∃ layers, Layer.Pub.of y sc rope ws P.h.V #[] P.settings = .ok layers ∧
      X.P = P ∧ X.layers = layers := by
    split at h
    · obtain ⟨_, _, h⟩ := exc_bind h
      obtain ⟨_, _, h⟩ := exc_bind h
      obtain ⟨layers, hlay, h⟩ := exc_bind h
      refine ⟨layers, hlay, ?_⟩
      repeat' first
        | (obtain ⟨_, _, h⟩ := exc_bind h)
        | (cases h; exact ⟨rfl, rfl⟩)
    · obtain ⟨_, _, h⟩ := exc_bind h
      obtain ⟨layers, hlay, h⟩ := exc_bind h
      refine ⟨layers, hlay, ?_⟩
      repeat' first
        | (obtain ⟨_, _, h⟩ := exc_bind h)
        | (cases h; exact ⟨rfl, rfl⟩)
  obtain ⟨layers, hlay, e1, e2⟩ := key
  unfold ReadOf
  rw [e1, e2, pubOf_wsLay hlay]
  exact ⟨y, h0, hws⟩

end Johnson.RunOne.Law.ReadAtO

namespace Johnson.RunOne.Law.UnitsInScope
open OnBytes OnBytes.Model OnBytes.Model.Config OnBytes.Model.Verify
open OnBytes.Params (exc_bind recordLines)
open Lk6.AtPlan
open Johnson.G.OfPlan (Made)
open VerifiableInference.Desc.Key (Source madeAt sourceOf)
open Johnson.RunOne.Law.SourceIs
open Johnson.RunOne.Law.AtFreeCfg

/-- **The layout of the committed matrix in what was read is the one of the ten written sizes.** -/
theorem wsLay_at_policy {v : VerifierAndGoals.FreeLines} {Z : Public}
    (hX : ReadOf (VerifierAndGoals.policyFile v) Z) :
    wsLayOf wsFull true recordLines.blockLog = .ok Z.layers.wsLay := by
  obtain ⟨y, hy, hw⟩ := hX
  have hS := polLayout_scan hy
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, bD⟩ := scan_sizes hS
  have hf := scan_frame hS
  obtain ⟨c1, c2, c3⟩ := layout_sizes (polLayout_layout hy)
  have hq : y.dq = 5120 := by
    rw [c2]
    show Z.P.h.H * Z.P.h.dh = 5120
    rw [b3, b5]
  have hkv : y.dkv = 1024 := by
    rw [c3]
    show Z.P.h.Gk * Z.P.h.dh = 1024
    rw [b4, b5]
  have h3 : y.h.p3 = true := by
    rw [c1]
    show (Z.P.h.prof == 3 || (Z.P.h.prof == 4 && decide (0 < Z.P.h.NE))) = true
    rw [b0, b8]
    rfl
  have hws : weightShape Z.P y = wsFull := by
    unfold weightShape wsFull
    simp only [bD, b1, b2, b5, hkv, hq, b6, b7, b8, b9]
  have hlk : Z.P.lkW = recordLines.blockLog := by
    show Z.P.frame.blockLog = _
    rw [hf]
  rw [hws, h3, hlk] at hw
  exact hw

/-- The source's units are those of the layout in the maker's record. -/
theorem sourceOf_units {m : Made} {X : Source} (h : sourceOf m = .ok X) :
    X.Y.units = Plan.unitsOfLayout m.p.X.layers.wsLay := by
  unfold sourceOf at h
  obtain ⟨D, _, h⟩ := exc_bind h
  obtain ⟨T, _, h⟩ := exc_bind h
  cases h
  rfl

/-- **THE UNITS THAT THE DESCRIPTION READS ARE THE WRITTEN LAYOUT'S, IN SCOPE, AT ANY DIGEST.** -/
theorem units_in_scope {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true) {Z : Public}
    (hP : ReadOf Zp.pol Z) {cfg : ByteArray} {m : Made} {X : Source}
    (hm : madeAt Z Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) :
    ∃ Y, wsLayOf wsFull true recordLines.blockLog = .ok Y ∧ X.Y.units = Plan.unitsOfLayout Y := by
  obtain ⟨v, hv⟩ := inScope_policy hZ
  rw [hv] at hP
  refine ⟨Z.layers.wsLay, wsLay_at_policy hP, ?_⟩
  rw [sourceOf_units hX, (madeAt_parts hm).1]

end Johnson.RunOne.Law.UnitsInScope

namespace Johnson.RunOne.Law.AtFreeCfg
open OnBytes OnBytes.Model OnBytes.Model.Config OnBytes.Model.Verify
open OnBytes.Params (recordLines)
open Lk6.AtPlan
open Johnson.RunOne.Law.UnitsInScope

/-- **The sized key is the written value, at the parameter file at any values of the eight free
numbers, any layout file and ANY DIGEST.** -/
theorem key_at_chains {v : VerifierAndGoals.FreeLines} {layout : Option ByteArray}
    {Z : Public} {cfg : ByteArray} {c : Chains}
    (hX : ReadOf (VerifierAndGoals.policyFile v) Z) (hc : chainsOf Z layout cfg = .ok c) :
    c.made.sized.key = keyFull := by
  obtain ⟨links, shapes, hs, hm, -, -⟩ := chainsOf_parts hc
  have hw := wsLay_at_policy hX
  obtain ⟨y, hy, -⟩ := hX
  have hf := scan_frame (polLayout_scan hy)
  have hk := Params.sized_key (Params.configure_plans hm).1
  rw [hf] at hk
  exact Option.some.inj (hk.symm.trans (keySized_returns hw (shapesOf_ranges hs)))

end Johnson.RunOne.Law.AtFreeCfg

namespace Johnson.RunOne.Law.OkStartInScope
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Flat
open Lk6.AtPlan
open VerifiableInference.Desc.Key (Source sourceClauses)
open Johnson.RunOne.Law.SourceIs

variable {X : Source} {N : H2U.PlaceNums} {P : VerifiableInference.Desc.Key.LaterPlaces}

/-- **The clause "shape", as an equation**: the two chains' shapes of the test on the table, as
read, are one. -/
theorem fk_shape (h : (VerifiableInference.Desc.Key.descriptionFromSource X N P).planOk = true) :
    X.Y.k.oneTime.lin = X.Y.k.shared.lin := by
  have e := List.all_eq_true.1 (desc_clauses X N P h)
    ("shape", sameItem X.Y.k.oneTime.given X.Y.k.shared.given
        "the test on the table" && X.Y.k.oneTime.lin == X.Y.k.shared.lin)
    (by simp [sourceClauses])
  simp only [Bool.and_eq_true, beq_iff_eq] at e
  exact e.2

/-- The three numbers at the written sizes of a key of full size. -/
theorem index_full : keyFull.once.shape.fold.index.rows = 2 ^ frS.P.v ∧
    keyFull.once.shape.fold.index.answers = 1 ∧ keyFull.once.shape.fold.index.cubeBits = 29 := by
  decide +kernel

/-- A control: such a test can say no. -/
theorem index_full_no : ¬ keyFull.once.shape.fold.index.cubeBits = 28 := by decide +kernel

end Johnson.RunOne.Law.OkStartInScope

namespace Johnson.RunOne.Law.KeyInScope
open OnBytes OnBytes.Maker
open OnBytes.Model.Verify (Public)
open Lk6.AtPlan
open Johnson.G.OfPlan (Made)
open VerifiableInference.Desc.Key (Source madeAt sourceOf keyDataAndDecisionAtFixedDigest KeyRun fixedDigest descriptionFromSource keyInstanceOfOutOfDomainSample)
open Johnson.RunOne.Law.SourceIs
open Johnson.RunOne.Law.AtFreeCfg

/-- **What these laws spend of the yes of the key file's piece at the fixed digest**: typed once, so
that no other file takes laidFixed_is apart by position. -/
theorem laid_parts {Z : Public} {lay : ByteArray} {D : WholeD} {r : KeyRun}
    (h : keyDataAndDecisionAtFixedDigest Z lay = .ok (D, r)) :
    ∃ m X N P, madeAt Z lay fixedDigest = .ok m ∧ sourceOf m = .ok X ∧
      (descriptionFromSource X N P).planOk = true ∧ (descriptionFromSource X N P).data "key file" = .ok D ∧
      r = ((descriptionFromSource X N P).pull keyInstanceOfOutOfDomainSample).run := by
  obtain ⟨m, X, N, P, hm, hX, -, -, -, hp, -, -, -, hD, hr⟩ :=
    VerifiableInference.Desc.Key.laidFixed_is Z lay D r h
  exact ⟨m, X, N, P, hm, hX, hp, hD, hr⟩

/-- The sized key of the maker's record is the written value, in scope, at any digest. -/
theorem key_in_scope {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true) {Z : Public}
    (hP : ReadOf Zp.pol Z) {cfg : ByteArray} {m : Made} (hm : madeAt Z Zp.lay cfg = .ok m) :
    m.p.chains.made.sized.key = keyFull := by
  obtain ⟨v, hv⟩ := inScope_policy hZ
  rw [hv] at hP
  exact key_at_chains hP (madeAt_parts hm).2.1

/-- **THE FIVE EQUATIONS AT THE WRITTEN VALUE, IN SCOPE, AT ANY DIGEST.** -/
theorem five_in_scope {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true) {Z : Public}
    (hP : ReadOf Zp.pol Z) {cfg : ByteArray} {m : Made} {X : Source} {N : H2U.PlaceNums}
    {P : VerifiableInference.Desc.Key.LaterPlaces} (hm : madeAt Z Zp.lay cfg = .ok m)
    (hX : sourceOf m = .ok X) (hp : (descriptionFromSource X N P).planOk = true) :
    X.set = keyFull.set ∧ X.Y.k.oneTime.ranges = keyFull.ranges.x ∧
      X.Y.k.oneTime.lin = keyFull.once.shape ∧ X.Y.k.oneTime.indexMasks = keyFull.once.input ∧
      X.Y.k.oneTime.codes = keyFull.codes := by
  have h := five_at hm hX hp
  rw [key_in_scope hZ hP hm] at h
  exact h

/-- **A sixth**: the shared chain's shape of the test on the table, as read, is the written value's
too: by the clause "shape". -/
theorem shared_lin_in_scope {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true) {Z : Public}
    (hP : ReadOf Zp.pol Z) {cfg : ByteArray} {m : Made} {X : Source} {N : H2U.PlaceNums}
    {P : VerifiableInference.Desc.Key.LaterPlaces} (hm : madeAt Z Zp.lay cfg = .ok m)
    (hX : sourceOf m = .ok X) (hp : (descriptionFromSource X N P).planOk = true) :
    X.Y.k.shared.lin = keyFull.once.shape := by
  rw [← Johnson.RunOne.Law.OkStartInScope.fk_shape hp, (five_in_scope hZ hP hm hX hp).2.2.1]

end Johnson.RunOne.Law.KeyInScope

#print axioms Johnson.RunOne.Law.SourceIs.sendsFrom_key_codes
#print axioms Johnson.RunOne.Law.SourceIs.madeAt_parts
#print axioms Johnson.RunOne.Law.SourceIs.sourceOf_parts
#print axioms Johnson.RunOne.Law.SourceIs.desc_clauses
#print axioms Johnson.RunOne.Law.SourceIs.fk_cut
#print axioms Johnson.RunOne.Law.SourceIs.five_at
#print axioms Johnson.RunOne.Law.AtFreeCfg.readOf_publicOf
#print axioms Johnson.RunOne.Law.AtFreeCfg.key_at_chains
#print axioms Johnson.RunOne.Law.ReadAtO.readOf_publicOfO
#print axioms Johnson.RunOne.Law.UnitsInScope.wsLay_at_policy
#print axioms Johnson.RunOne.Law.UnitsInScope.sourceOf_units
#print axioms Johnson.RunOne.Law.UnitsInScope.units_in_scope
#print axioms Johnson.RunOne.Law.OkStartInScope.fk_shape
#print axioms Johnson.RunOne.Law.OkStartInScope.index_full
#print axioms Johnson.RunOne.Law.OkStartInScope.index_full_no
#print axioms Johnson.RunOne.Law.KeyInScope.laid_parts
#print axioms Johnson.RunOne.Law.KeyInScope.key_in_scope
#print axioms Johnson.RunOne.Law.KeyInScope.five_in_scope
#print axioms Johnson.RunOne.Law.KeyInScope.shared_lin_in_scope
