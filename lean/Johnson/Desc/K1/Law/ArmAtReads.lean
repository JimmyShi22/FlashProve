-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/ArmAtReads.lean: **arm_at_reads**: the binder hArm of K01_law's fifty later places
(k01_fifty_atBase), in its form behind the tie, to the letter, from what the three sorts of segment's
files' halves of the exchange still ask.
A LETTER J : S → Prop: what the leftovers want of a state that the verifier
reaches, in front of its reads. The fence has the field inv : J x.2; the three theorems have the
antecedent, `ArmOk J x.2` (Johnson/Desc/K1/Law/ArmOk.lean), behind the promise: so they are the binder
hArm WITH THAT ANTECEDENT: the top hands it off its wider promise's letter xb.
hLay and hAtt are asked AN ENTRY AT A TIME: at an entry e of an array of the
second commitment that a form of the run names (`NamedEntry`), with the two sorts' files' structures at the reader
`oneEntry e`: their field hE ("every entry that a form names lies in the array of the reads ...") then
speaks of e alone: the public test allows forms that name an entry of the FIRST
commitment, and of these ArmCellIn asks nothing.
The facts of the step at the reads itself are paid
(Johnson/Desc/K1/Law/ArmStep.lean): at a feed-forward link hs ho hA hfun htab, and hu3 down to the plan;
at an attention link hfun, the link's number in hA, and htab | hu3 down to the state's own parameters in
front. The fence names X and arrs. A premise: hDlk (the top's own binder).
The binder stands behind the item `tie l`: said of every witness, with nothing asked of it, nobody
can meet it (`armCellIn_not_both`, Johnson/Desc/K1/Law/ArmHalves.lean).
OBJECT: `Sound.ArmCellIn` at link l's reads, at `armOf Dm.uL Dm.uA Dm.uH (link l's sort) l`.
USER: the top of K01_law's fifty later places (its binder hArm).
LETTERS: Dm, dk, Mg₀, Z, Bs, aN, R₁ R₂ R₃, c; l, X, arrs; x, x', y, y', w; j, n, p; A, B.
  `ReadsFence`       THE FENCE behind which every premise is asked: X is the built link l · an accept of
                   the sub-protocol at link l's reads from x to x' · x inside the promise in front · J x.2 · the
                   strings behind keep what lies below the piece's base · THE TIE at x', y', w · p a run
                   of a claim on linear forms that the place takes in · A, B the open segment's parts
  `rides_at_reads`   inside the fence: `Sound.Rides (Dm.N.sent l 0) A B`
  `plainIn_mw`       [kernel] "K5.plain" of link l is open in front of each attention link's reads.
                   `plainIn_fails`: the test can fail
  `arm_at_reads_of`  the binder at a letter Mg₀ for the meaning beneath (hM: its list of extra public
                   tests is empty)
  `arm_at_reads`     **the binder, to the letter, at mgBase**
PREMISES LEFT. hDlk : Dm.links = linksFull · hUA : Dm.uA = `uArm XV` (two equations on Dm's letters). AND
THREE, EACH POINTWISE, BEHIND THE FENCE, hLay AND hAtt AT ONE NAMED ENTRY e, EVERY LETTER PINNED BUT
M n | i:
  hLay   at a feed-forward link; b₀ the open link's part at x.2, o what its own rounds returned, hp the
         public parameters' plan at the link's group, tl' the parameters behind: letters M n with: Dm.uL l
         is `uLay hp.tl M` at x.2; and `LayRest` (three fields: hE hu3 hM)
  hAtt   at an attention link; a₀ the part at x.2, Ap the plan at the link's group, tlF | tl' the
         parameters in front | behind: a letter i with `AttRest XV` (eight fields: hA hin hNM hW hE htab
         hu3 hM)
  hHead  at the output head's link: ArmCellIn at Dm.uH l, as it was, behind the tie: not called
PAID HERE: T · hAc · the open link's number · hs ho hA hfun htab (feed-forward) · hfun (attention:
`K5Law.block4_funs`, with "the array of the reads is in the ledger" off the promise's "K5.plain").
The recursion limit is raised in this file (maxRecDepth 1000000), as in
Johnson/Desc/K1/Law/RestAtPlus13.lean: for the elaboration of the kernel's evaluations alone.
IS IT EMPTY HERE? NO MEMBER IS SHOWN: at no state is LayRest or AttRest shown.
What is not claimed. The premises. Nothing on soundness.

-/
import Johnson.Desc.K1.Law.ArmHalves
import Johnson.Desc.K1.Law.ArmStep
import Johnson.Desc.K1.Law.ArmOk
import Johnson.Desc.K1.Law.ArmBySort
import Johnson.Desc.K1.Law.K01FiftyR
import Johnson.Desc.K1.Law.MemberMw1
import Johnson.Desc.K1.Law.RestAtPlus13
import Johnson.Desc.Sound.MgBase
import Johnson.Desc.Sound.CellsAtName
import Johnson.Desc.First.PubAllAt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model
open Iop Run OnBytes.Maker OnBytes.Flat
open Cb Johnson.Pack
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers More flatPlacesOf standOf LayOwn
  AttOwn)
open VerifiableInference.Desc.Sound (linksFull MsgT MsgQ MgData CellsQ mgAll mgBase d13 rowQ seatTab
  UFn linkNo ArmCellIn Rides cellsAt_name)
open VerifiableInference.Desc.K13.Law (openAt plus13)
open VerifiableInference.Desc.K12.Door (K12Data)
open VerifiableInference.Desc.First.Att.P (uArm)
open OnBytes.Road.K4 (uLay)
open OnBytes.Model.Stages (LinkH)
open OnBytes.Params (Rounds)
open H2K5.Door (plainThereB wideB heardPlainB)
open ProofFile (Cl)
open IM (k1Ix)

/-! ## 1 Small steps -/

theorem here_lay_of_stand {s : S} (h : standOf s = .link .layers) : ∃ b₀, s.here = .lay b₀ := by
  unfold standOf at h
  cases hh : s.here with
  | lay a => exact ⟨a, rfl⟩
  | between => rw [hh] at h; cases h
  | att a => rw [hh] at h; cases h
  | head a =>
    rw [hh] at h
    dsimp only at h
    split at h <;> cases h
  | fin a => rw [hh] at h; cases h
  | mem a => rw [hh] at h; cases h

theorem here_att_of_stand {s : S} (h : standOf s = .link .attention) : ∃ a₀, s.here = .att a₀ := by
  unfold standOf at h
  cases hh : s.here with
  | att a => exact ⟨a, rfl⟩
  | between => rw [hh] at h; cases h
  | lay a => rw [hh] at h; cases h
  | head a =>
    rw [hh] at h
    dsimp only at h
    split at h <;> cases h
  | fin a => rw [hh] at h; cases h
  | mem a => rw [hh] at h; cases h

/-- "K5.plain" says that the array of the reads is in the open ledger. -/
theorem plain_isSome {i n : ℕ} {s : S} {a₀ : AttOwn} (hs : s.here = .att a₀)
    (h : plainThereB i n s = true) : (a₀.F.trees[i]?).isSome = true := by
  unfold plainThereB at h
  have hf : s.fork? = some a₀.F := by
    unfold S.fork?
    rw [hs]
  rw [hf] at h
  cases h5 : s.heard5? with
  | none =>
    rw [h5] at h
    cases h
  | some hh =>
    rw [h5] at h
    have h' : (heardPlainB hh && wideB a₀.F i n) = true := h
    have hw : wideB a₀.F i n = true := (Bool.and_eq_true_iff.1 h').2
    unfold wideB at hw
    cases e : a₀.F.trees[i]? with
    | none =>
      rw [e] at hw
      cases hw
    | some T => rfl

theorem plainIn_mw : ((List.range 25).all fun l =>
    !((linksFull[l]?).getD .layers == .attention) ||
      openB mwMore linksFull (flatPlacesOf linksFull true) (14 * l + k1Ix l false + 2)
        (.more (some l) "K5.plain")) = true := by
  decide +kernel

/-- **The test can fail**: at a feed-forward link's reads the name is not open; nor is another link's
at link 3's. -/
theorem plainIn_fails :
    openB mwMore linksFull (flatPlacesOf linksFull true) (14 * 2 + k1Ix 2 false + 2)
      (.more (some 2) "K5.plain") = false ∧
    openB mwMore linksFull (flatPlacesOf linksFull true) (14 * 3 + k1Ix 3 false + 2)
      (.more (some 5) "K5.plain") = false := by
  decide +kernel

section
variable {Xi Tok : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public}
  (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV) (dk : K12Data)
  (Mg₀ : Meaning ProofFile.InstPub (Wit (CellsQ rows cols) Tok MsgT))

/-! ## 2 The fence -/

/-- **The fence.** -/
structure ReadsFence (J : S → Prop) (Z : ProofFile.Pub) (Bs : ProofFile.PureBase) (aN : ℕ) (R₁ R₂ R₃ : Rounds)
    (c : Chain S Cl) (l : ℕ) (X : LinkH) (arrs : Option (List ℕ)) (x x' : ProofFile.InstPub × S)
    (y y' : Strs) (w : Wit (CellsQ rows cols) Tok MsgT) (p : ℕ × String) (A B : K9.Part) :
    Prop where
  lt : l < 25
  built : Bs.G₀.built[l]? = some X
  yes : YesOf (blkL Z Bs.G₀ l false X arrs) x x'
  inAt : InAt Dm.N (mw1 Dm.N (d13 Dm) dk (mgAll Dm Mg₀)) linksFull (flatPlacesOf linksFull true)
    (noL l false) x y
  inv : J x.2
  kept : KeptBelow (baseL aN R₁ R₂ R₃ c l false) y y'
  tie : (mw1 Dm.N (d13 Dm) dk (mgAll Dm Mg₀)).tie l x' y' w
  run : ∃ j n, Item.formsT l j n ∈ (rowQ linksFull (flatPlacesOf linksFull true) (noL l false)).ins ∧
    p ∈ Dm.runs l j n
  front : K9.segAt? x.2 = some A
  behind : K9.segAt? x'.2 = some B

variable {Dm dk Mg₀} in
/-- **Inside the fence the part behind rides on the part in front**, at the first commitment's
seats. -/
theorem rides_at_reads {J : S → Prop} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {aN : ℕ} {R₁ R₂ R₃ : Rounds}
    {c : Chain S Cl} {l : ℕ} {X : LinkH} {arrs : Option (List ℕ)} {x x' : ProofFile.InstPub × S}
    {y y' : Strs} {w : Wit (CellsQ rows cols) Tok MsgT} {p : ℕ × String} {A B : K9.Part}
    (F : ReadsFence Dm dk Mg₀ J Z Bs aN R₁ R₂ R₃ c l X arrs x x' y y' w p A B) :
    Rides (Dm.N.sent l 0) A B := by
  obtain ⟨_, rs, gs, hfit, hd⟩ := F.yes
  have hlen : (rs.map noDigest).length = 2 := by
    rw [List.length_map, Keeps.fit_length _ _ hfit, rounds_blkL]
  obtain ⟨B', hB', _, hr, _⟩ := rides_of_rec
    (laterSend_k1Reads Z Bs.G₀ l X _ arrs x.2 x'.2 _ gs hlen hd).2.1
    (laterGrows_k1Reads Z Bs.G₀ l X _ arrs x.2 x'.2 _ gs hd) (inAt_book F.inAt).1
    (Dm.N.sent l 0) F.front
  obtain rfl : B' = B := Option.some.inj (hB'.symm.trans F.behind)
  exact hr

/-! ## 3 The binder -/

/-- **The binder hArm, behind the tie, at a letter for the meaning beneath.** -/
theorem arm_at_reads_of (J : S → Prop) (hM : Mg₀.more = {}) (hDlk : Dm.links = linksFull) (Z : ProofFile.Pub)
    (Bs : ProofFile.PureBase) (aN : ℕ) (R₁ R₂ R₃ : Rounds) (c : Chain S Cl)
    (hLay : ∀ l X arrs x x' y y' w p A B, ReadsFence Dm dk Mg₀ J Z Bs aN R₁ R₂ R₃ c l X arrs x x' y y' w p A B →
      (linksFull[l]?).getD .layers = .layers →
      ∀ b₀ o hp tl', x.2.here = .lay b₀ → b₀.own = some o → Bs.G₀.W.G[X.g]? = some hp →
      x'.2.tl? = some tl' →
      ∀ e cc, NamedEntry (Dm.Rd l) (Dm.N.sent l 0) p.1 p.2 x.2 A e cc →
      ∃ M n, Dm.uL l x.2 = uLay hp.tl M x.2 ∧
        LayRest (oneEntry e) (Dm.N.sent l 0) p.1 p.2 x.2 A (seatTab Dm.cs Dm.arr Dm.ms w) hp.tl tl' M o n
          (Dm.A1 l x' w))
    (hUA : Dm.uA = uArm XV)
    (hAtt : ∀ l X arrs x x' y y' w p A B, ReadsFence Dm dk Mg₀ J Z Bs aN R₁ R₂ R₃ c l X arrs x x' y y' w p A B →
      (linksFull[l]?).getD .layers = .attention →
      ∀ a₀ Ap tlF tl', x.2.here = .att a₀ → Bs.G₀.W.A[X.g]? = some Ap → x.2.tl? = some tlF →
      x'.2.tl? = some tl' →
      ∀ e cc, NamedEntry (Dm.Rd l) (Dm.N.sent l 0) p.1 p.2 x.2 A e cc →
      ∃ i, AttRest XV (oneEntry e) (Dm.N.sent l 0) p.1 p.2 x.2 A (seatTab Dm.cs Dm.arr Dm.ms w) l Ap i
        tlF tl' (Dm.A1 l x' w))
    (hHead : ∀ l X arrs x x' y y' w p A B, ReadsFence Dm dk Mg₀ J Z Bs aN R₁ R₂ R₃ c l X arrs x x' y y' w p A B →
      (linksFull[l]?).getD .layers = .head →
      ArmCellIn (Dm.Rd l) (Dm.N.sent l 0) (Dm.N.group l) p.1 p.2 x.2 A B
        (seatTab Dm.cs Dm.arr Dm.ms w) (Dm.uH l)) :
    ∀ l, l < 25 → ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ (x x' : ProofFile.InstPub × S) y y'
      (w : Wit (CellsQ rows cols) Tok MsgT),
      YesOf (blkL Z Bs.G₀ l false X arrs) x x' → InAt Dm.N (mw1 Dm.N (d13 Dm) dk (mgAll Dm Mg₀)) linksFull (flatPlacesOf linksFull true) (noL l false) x y →
      ArmOk J x.2 →
      KeptBelow (baseL aN R₁ R₂ R₃ c l false) y y' → (mw1 Dm.N (d13 Dm) dk (mgAll Dm Mg₀)).tie l x' y' w →
      ∀ j n, Item.formsT l j n ∈ (rowQ linksFull (flatPlacesOf linksFull true) (noL l false)).ins →
      ∀ p ∈ Dm.runs l j n, ∀ A B, K9.segAt? x.2 = some A → K9.segAt? x'.2 = some B →
      ArmCellIn (Dm.Rd l) (Dm.N.sent l 0) (Dm.N.group l) p.1 p.2 x.2 A B
        (seatTab Dm.cs Dm.arr Dm.ms w) (armOf Dm.uL Dm.uA Dm.uH ((linksFull[l]?).getD .layers) l) := by
  intro l hl X arrs hX x x' y y' w hy hIn hJ hk ht j n hj p hp A B hA hB
  have F : ReadsFence Dm dk Mg₀ J Z Bs aN R₁ R₂ R₃ c l X arrs x x' y y' w p A B :=
    ⟨hl, hX, hy, hIn, hJ (atMoment1_of_yes Z Bs.G₀ l X arrs x x' hy), hk, ht, ⟨j, n, hj, hp⟩, hA, hB⟩
  have hr := rides_at_reads F
  obtain ⟨tl', htl, T⟩ : First.K8.TieAt (Dm.A1 l x') x'.2 w := ht
  have hcell : ∀ t cc, A.L.arrayOf[t]? = some cc → ∀ r i, Dm.A1 l x' w t r i =
      (Sound.dataQ (Dm.N.group l) B (seatTab Dm.cs Dm.arr Dm.ms w)).cell cc.1 cc.2 r i :=
    fun t cc hc r i => cellsAt_name Dm.cs Dm.arr Dm.ms Dm.N l x'.1 x'.2 w B hB t cc
      (by rw [hr.arrays]; exact hc) r i
  have hst := stand_of_promise l hl x y hIn
  obtain ⟨_, rs, gs, hfit, hd⟩ := hy
  have hlen : (rs.map noDigest).length = 2 := by
    rw [List.length_map, Keeps.fit_length _ _ hfit, rounds_blkL]
  obtain ⟨_, hLa, _, _, _⟩ := segAt_some hA
  cases hsub : (linksFull[l]?).getD .layers with
  | layers =>
    rw [hsub] at hst
    obtain ⟨b₀, hs⟩ := here_lay_of_stand hst
    obtain ⟨hp', o, tl₂, hg, ho, htl₂, e1, e2, e3⟩ :=
      lay_at_reads Z Bs.G₀ l X hX _ arrs x.2 x'.2 _ gs hlen hd b₀ hs
    obtain rfl : tl₂ = tl' := Option.some.inj (htl₂.symm.trans htl)
    refine armCellIn_of_entries _ _ _ _ _ _ _ _ _ _ fun en cn hN => ?_
    obtain ⟨M, k, e, L⟩ := hLay l X arrs x x' y y' w p A B F hsub b₀ o hp' tl₂ hs ho hg htl en cn hN
    have hAL : A.L = b₀.L := by
      have hl2 : x.2.link? = some b₀.L := by
        unfold S.link?
        rw [hs]
      exact Option.some.inj (hLa.symm.trans hl2)
    have O : LayOwes (oneEntry en) (Dm.N.sent l 0) p.1 p.2 x.2 A (seatTab Dm.cs Dm.arr Dm.ms w) hp'.tl
        tl₂ M b₀ o k (Dm.A1 l x' w) := ⟨hs, ho, hAL, L.hE, e1, e2, e3.trans L.hu3, L.hM⟩
    exact armCellIn_congr _ _ _ _ _ _ _ _ _ e (armCellIn_lay (O.left (Dm.N.group l) B T
      fun cc hc i _ => hcell _ cc (by rw [hAL]; exact hc) 0 i))
  | attention =>
    rw [hsub] at hst
    obtain ⟨a₀, hs⟩ := here_att_of_stand hst
    obtain ⟨Ap, tlF, tl₂, hg, htlF, htl₂, e2, e3, efun⟩ :=
      att_at_reads Z Bs.G₀ l X hX _ arrs x.2 x'.2 _ gs hlen hd a₀ hs
    obtain rfl : tl₂ = tl' := Option.some.inj (htl₂.symm.trans htl)
    refine armCellIn_of_entries _ _ _ _ _ _ _ _ _ _ fun en cn hN => ?_
    obtain ⟨i, L⟩ := hAtt l X arrs x x' y y' w p A B F hsub a₀ Ap tlF tl₂ hs hg htlF htl en cn hN
    have hno : linkNo x.2 = l :=
      linkNo_of_promise Dm dk Mg₀ hM l hl x y (inAt_down _ _ _ _ _ _ _ _ _ hIn) A hA
    have hlk : linksFull[l]? = some .attention := by
      cases e : linksFull[l]? with
      | none =>
        rw [e] at hsub
        cases hsub
      | some sb =>
        rw [e] at hsub
        exact congrArg some hsub
    have hisAtt : Dm.pubD.d5.isAtt l = true := by
      show (Dm.links[l]? == some .attention) = true
      rw [hDlk, hlk]
      rfl
    have hin : Pub.more (some l) "K5.plain" ∈
        (First.pubSets (mw1 Dm.N (d13 Dm) dk (mgAll Dm Mg₀)).more linksFull
          (flatPlacesOf linksFull true))[noL l false]?.getD [] ++
        First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l false)) := by
      have e : (mw1 Dm.N (d13 Dm) dk (mgAll Dm Mg₀)).more = mwMore :=
        plus13_more_closed Dm dk Mg₀ hM
      rw [e]
      have t := List.all_eq_true.1 plainIn_mw l (List.mem_range.2 hl)
      rw [hsub] at t
      exact open_of t
    have h0 : (plus13 (d13 Dm) dk (mgAll Dm Mg₀)).pub (.more (some l) "K5.plain") x = true :=
      inAt_pub hIn _ hin
    rw [pub_plus13, First.pubAll_more_plain _ _ l hisAtt] at h0
    have h0' : (XV.A[l / 2]?).any (fun q => plainThereB q.iU3 q.nW x.2) = true := h0
    rw [L.hA] at h0'
    have hT : (a₀.F.trees[Ap.iU3]?).isSome = true := plain_isSome hs h0'
    have O : AttOwes XV (oneEntry en) (Dm.N.sent l 0) p.1 p.2 x.2 A (seatTab Dm.cs Dm.arr Dm.ms w) Ap i
        tl₂ (Dm.A1 l x' w) :=
      ⟨by rw [hno]; exact L.hA, L.hin, L.hNM, L.hW, L.hE, efun hT,
        fun Fn cc sg => (L.htab Fn cc sg).trans (e2 Fn cc sg), e3.trans L.hu3, L.hM⟩
    have h := armCellIn_att' (O.left (Dm.N.group l) B T fun cc hc i _ => hcell _ cc hc 0 i)
    rw [hno] at h
    have e : Dm.uA l x.2 = uArm XV l x.2 := by rw [hUA]
    exact armCellIn_congr _ _ _ _ _ _ _ _ _ e h
  | head => exact hHead l X arrs x x' y y' w p A B F hsub

/-- **THE BINDER hArm, BEHIND THE TIE, TO THE LETTER, AT mgBase.** -/
theorem arm_at_reads (J : S → Prop) (hDlk : Dm.links = linksFull) (Z : ProofFile.Pub) (Bs : ProofFile.PureBase) (aN : ℕ)
    (R₁ R₂ R₃ : Rounds) (c : Chain S Cl)
    (hLay : ∀ l X arrs x x' y y' w p A B, ReadsFence Dm dk mgBase J Z Bs aN R₁ R₂ R₃ c l X arrs x x' y y' w p A B →
      (linksFull[l]?).getD .layers = .layers →
      ∀ b₀ o hp tl', x.2.here = .lay b₀ → b₀.own = some o → Bs.G₀.W.G[X.g]? = some hp →
      x'.2.tl? = some tl' →
      ∀ e cc, NamedEntry (Dm.Rd l) (Dm.N.sent l 0) p.1 p.2 x.2 A e cc →
      ∃ M n, Dm.uL l x.2 = uLay hp.tl M x.2 ∧
        LayRest (oneEntry e) (Dm.N.sent l 0) p.1 p.2 x.2 A (seatTab Dm.cs Dm.arr Dm.ms w) hp.tl tl' M o n
          (Dm.A1 l x' w))
    (hUA : Dm.uA = uArm XV)
    (hAtt : ∀ l X arrs x x' y y' w p A B, ReadsFence Dm dk mgBase J Z Bs aN R₁ R₂ R₃ c l X arrs x x' y y' w p A B →
      (linksFull[l]?).getD .layers = .attention →
      ∀ a₀ Ap tlF tl', x.2.here = .att a₀ → Bs.G₀.W.A[X.g]? = some Ap → x.2.tl? = some tlF →
      x'.2.tl? = some tl' →
      ∀ e cc, NamedEntry (Dm.Rd l) (Dm.N.sent l 0) p.1 p.2 x.2 A e cc →
      ∃ i, AttRest XV (oneEntry e) (Dm.N.sent l 0) p.1 p.2 x.2 A (seatTab Dm.cs Dm.arr Dm.ms w) l Ap i
        tlF tl' (Dm.A1 l x' w))
    (hHead : ∀ l X arrs x x' y y' w p A B, ReadsFence Dm dk mgBase J Z Bs aN R₁ R₂ R₃ c l X arrs x x' y y' w p A B →
      (linksFull[l]?).getD .layers = .head →
      ArmCellIn (Dm.Rd l) (Dm.N.sent l 0) (Dm.N.group l) p.1 p.2 x.2 A B
        (seatTab Dm.cs Dm.arr Dm.ms w) (Dm.uH l)) :
    ∀ l, l < 25 → ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ (x x' : ProofFile.InstPub × S) y y'
      (w : Wit (CellsQ rows cols) Tok MsgT),
      YesOf (blkL Z Bs.G₀ l false X arrs) x x' → InAt Dm.N (mw1 Dm.N (d13 Dm) dk (mgAll Dm mgBase)) linksFull (flatPlacesOf linksFull true) (noL l false) x y →
      ArmOk J x.2 →
      KeptBelow (baseL aN R₁ R₂ R₃ c l false) y y' → (mw1 Dm.N (d13 Dm) dk (mgAll Dm mgBase)).tie l x' y' w →
      ∀ j n, Item.formsT l j n ∈ (rowQ linksFull (flatPlacesOf linksFull true) (noL l false)).ins →
      ∀ p ∈ Dm.runs l j n, ∀ A B, K9.segAt? x.2 = some A → K9.segAt? x'.2 = some B →
      ArmCellIn (Dm.Rd l) (Dm.N.sent l 0) (Dm.N.group l) p.1 p.2 x.2 A B
        (seatTab Dm.cs Dm.arr Dm.ms w) (armOf Dm.uL Dm.uA Dm.uH ((linksFull[l]?).getD .layers) l) :=
  arm_at_reads_of Dm dk mgBase J rfl hDlk Z Bs aN R₁ R₂ R₃ c hLay hUA hAtt hHead

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.plainIn_mw
#print axioms VerifiableInference.Desc.K1.plainIn_fails
#print axioms VerifiableInference.Desc.K1.rides_at_reads
#print axioms VerifiableInference.Desc.K1.arm_at_reads_of
#print axioms VerifiableInference.Desc.K1.arm_at_reads
