-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Twin/ArmAtReadsB.lean: MADE BY PROGRAM OFF
Johnson/Desc/K1/Law/ArmAtReads.lean UNDER A MAP OF NAMES AND ONE TURN OF THE MEANING: 4 OF
ITS DECLARATIONS: ReadsFenceB · rides_at_reads_b · arm_at_reads_of_b · arm_at_reads_b. THE PROOFS
ARE COPIES.

This letter is for the honest run's own forms alone: no statement on any other party may take it.
NEVER ON SOUNDNESS's ROAD: at the meaning "honest" the
clauses noColl, shown and decodes are True by definition: a law at that meaning may stand beneath
statements on completeness or zero knowledge only, never beneath a statement on soundness.

The map of names. ReadsFence to ReadsFenceB; each twinned theorem n to n_b; the library's closed
facts at its wider table of names (mwMore) to their likes at mgMore, and its laws on the wider
meaning to their likes on "honest" over mgAll (both in Twin/HonestAt.lean, typed by hand).
The turn of the meaning. Where the elder has the wider meaning (mw1 Dm.N (d13 Dm) dk (mgAll Dm Mg₀),
or plus13 (d13 Dm) dk (mgAll Dm Mg₀)), the twin has honest (mgAll Dm Mg₀) ans test
(Johnson/Desc/ProofFile/Honest/Thread/First.lean): the meaning at which the honest thread's own
promise stands; at the item "tie": mgAll Dm Mg₀. The step down from mw1 to plus13 (inAt_down) falls.
The promise itself is the library's InAt: no new text of a promise.
Laid in, on no line of a statement: the letters ans and test, behind each block of letters: implicit
in the theorems, explicit in the structure ReadsFenceB; "include dk" where the original's block
binds dk (no twin's statement names it; it is kept so that a copied call has the original's number
of arguments). Kept as in the original: its namespace, open, variable, section, set_option
and attribute lines, but for one prefix that makes dk implicit (in ArmAtReadsB.lean): there "omit dk
in" stands.
The namespace is the library's, so that a copied proof finds its callees without a sign turned; the
names with the suffix _b are not the library's.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K1.Law.ArmAtReads
import Johnson.Desc.ProofFile.Honest.K1.Twin.ArmBySortB
import Johnson.Desc.ProofFile.Honest.K1.Twin.HonestAt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1
open ProofFile.Honest.FirstThread (honest)
open VerifiableInference.Desc (Strs Wit)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (CellsQ MsgT mgMore)
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

section
variable {Xi Tok : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public}
  (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV) (dk : K12Data)
  (Mg₀ : Meaning ProofFile.InstPub (Wit (CellsQ rows cols) Tok MsgT))

variable {ans : ℕ → ℕ → ProofFile.InstPub × S → Strs → Wit (CellsQ rows cols) Tok MsgT → Prop} {test : ℕ → S → Option String}
include dk
variable (ans test) in
/-- **The fence.** -/
structure ReadsFenceB (J : S → Prop) (Z : ProofFile.Pub) (Bs : ProofFile.PureBase) (aN : ℕ) (R₁ R₂ R₃ : Rounds)
    (c : Chain S Cl) (l : ℕ) (X : LinkH) (arrs : Option (List ℕ)) (x x' : ProofFile.InstPub × S)
    (y y' : Strs) (w : Wit (CellsQ rows cols) Tok MsgT) (p : ℕ × String) (A B : K9.Part) :
    Prop where
  lt : l < 25
  built : Bs.G₀.built[l]? = some X
  yes : YesOf (blkL Z Bs.G₀ l false X arrs) x x'
  inAt : InAt Dm.N (honest (mgAll Dm Mg₀) ans test) linksFull (flatPlacesOf linksFull true)
    (noL l false) x y
  inv : J x.2
  kept : KeptBelow (baseL aN R₁ R₂ R₃ c l false) y y'
  tie : (mgAll Dm Mg₀).tie l x' y' w
  run : ∃ j n, Item.formsT l j n ∈ (rowQ linksFull (flatPlacesOf linksFull true) (noL l false)).ins ∧
    p ∈ Dm.runs l j n
  front : K9.segAt? x.2 = some A
  behind : K9.segAt? x'.2 = some B

omit dk in
variable {Dm Mg₀} in
/-- **Inside the fence the part behind rides on the part in front**, at the first commitment's
seats. -/
theorem rides_at_reads_b {J : S → Prop} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {aN : ℕ} {R₁ R₂ R₃ : Rounds}
    {c : Chain S Cl} {l : ℕ} {X : LinkH} {arrs : Option (List ℕ)} {x x' : ProofFile.InstPub × S}
    {y y' : Strs} {w : Wit (CellsQ rows cols) Tok MsgT} {p : ℕ × String} {A B : K9.Part}
    (F : ReadsFenceB Dm Mg₀ ans test J Z Bs aN R₁ R₂ R₃ c l X arrs x x' y y' w p A B) :
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

/-- **The binder hArm, behind the tie, at a letter for the meaning beneath.** -/
theorem arm_at_reads_of_b (J : S → Prop) (hM : Mg₀.more = {}) (hDlk : Dm.links = linksFull) (Z : ProofFile.Pub)
    (Bs : ProofFile.PureBase) (aN : ℕ) (R₁ R₂ R₃ : Rounds) (c : Chain S Cl)
    (hLay : ∀ l X arrs x x' y y' w p A B, ReadsFenceB Dm Mg₀ ans test J Z Bs aN R₁ R₂ R₃ c l X arrs x x' y y' w p A B →
      (linksFull[l]?).getD .layers = .layers →
      ∀ b₀ o hp tl', x.2.here = .lay b₀ → b₀.own = some o → Bs.G₀.W.G[X.g]? = some hp →
      x'.2.tl? = some tl' →
      ∀ e cc, NamedEntry (Dm.Rd l) (Dm.N.sent l 0) p.1 p.2 x.2 A e cc →
      ∃ M n, Dm.uL l x.2 = uLay hp.tl M x.2 ∧
        LayRest (oneEntry e) (Dm.N.sent l 0) p.1 p.2 x.2 A (seatTab Dm.cs Dm.arr Dm.ms w) hp.tl tl' M o n
          (Dm.A1 l x' w))
    (hUA : Dm.uA = uArm XV)
    (hAtt : ∀ l X arrs x x' y y' w p A B, ReadsFenceB Dm Mg₀ ans test J Z Bs aN R₁ R₂ R₃ c l X arrs x x' y y' w p A B →
      (linksFull[l]?).getD .layers = .attention →
      ∀ a₀ Ap tlF tl', x.2.here = .att a₀ → Bs.G₀.W.A[X.g]? = some Ap → x.2.tl? = some tlF →
      x'.2.tl? = some tl' →
      ∀ e cc, NamedEntry (Dm.Rd l) (Dm.N.sent l 0) p.1 p.2 x.2 A e cc →
      ∃ i, AttRest XV (oneEntry e) (Dm.N.sent l 0) p.1 p.2 x.2 A (seatTab Dm.cs Dm.arr Dm.ms w) l Ap i
        tlF tl' (Dm.A1 l x' w))
    (hHead : ∀ l X arrs x x' y y' w p A B, ReadsFenceB Dm Mg₀ ans test J Z Bs aN R₁ R₂ R₃ c l X arrs x x' y y' w p A B →
      (linksFull[l]?).getD .layers = .head →
      ArmCellIn (Dm.Rd l) (Dm.N.sent l 0) (Dm.N.group l) p.1 p.2 x.2 A B
        (seatTab Dm.cs Dm.arr Dm.ms w) (Dm.uH l)) :
    ∀ l, l < 25 → ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ (x x' : ProofFile.InstPub × S) y y'
      (w : Wit (CellsQ rows cols) Tok MsgT),
      YesOf (blkL Z Bs.G₀ l false X arrs) x x' → InAt Dm.N (honest (mgAll Dm Mg₀) ans test) linksFull (flatPlacesOf linksFull true) (noL l false) x y →
      ArmOk J x.2 →
      KeptBelow (baseL aN R₁ R₂ R₃ c l false) y y' → (mgAll Dm Mg₀).tie l x' y' w →
      ∀ j n, Item.formsT l j n ∈ (rowQ linksFull (flatPlacesOf linksFull true) (noL l false)).ins →
      ∀ p ∈ Dm.runs l j n, ∀ A B, K9.segAt? x.2 = some A → K9.segAt? x'.2 = some B →
      ArmCellIn (Dm.Rd l) (Dm.N.sent l 0) (Dm.N.group l) p.1 p.2 x.2 A B
        (seatTab Dm.cs Dm.arr Dm.ms w) (armOf Dm.uL Dm.uA Dm.uH ((linksFull[l]?).getD .layers) l) := by
  intro l hl X arrs hX x x' y y' w hy hIn hJ hk ht j n hj p hp A B hA hB
  have F : ReadsFenceB Dm Mg₀ ans test J Z Bs aN R₁ R₂ R₃ c l X arrs x x' y y' w p A B :=
    ⟨hl, hX, hy, hIn, hJ (atMoment1_of_yes Z Bs.G₀ l X arrs x x' hy), hk, ht, ⟨j, n, hj, hp⟩, hA, hB⟩
  have hr := rides_at_reads_b F
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
      linkNo_of_promise_b Dm dk Mg₀ hM l hl x y hIn A hA
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
        (First.pubSets (honest (mgAll Dm Mg₀) ans test).more linksFull
          (flatPlacesOf linksFull true))[noL l false]?.getD [] ++
        First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l false)) := by
      have e : (honest (mgAll Dm Mg₀) ans test).more = mgMore :=
        honest_more_closed Dm Mg₀ ans test hM
      rw [e]
      have t := List.all_eq_true.1 plainIn_mg l (List.mem_range.2 hl)
      rw [hsub] at t
      exact open_of t
    have h0 : (honest (mgAll Dm Mg₀) ans test).pub (.more (some l) "K5.plain") x = true :=
      inAt_pub hIn _ hin
    rw [honest_pub_all, First.pubAll_more_plain _ _ l hisAtt] at h0
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
theorem arm_at_reads_b (J : S → Prop) (hDlk : Dm.links = linksFull) (Z : ProofFile.Pub) (Bs : ProofFile.PureBase) (aN : ℕ)
    (R₁ R₂ R₃ : Rounds) (c : Chain S Cl)
    (hLay : ∀ l X arrs x x' y y' w p A B, ReadsFenceB Dm mgBase ans test J Z Bs aN R₁ R₂ R₃ c l X arrs x x' y y' w p A B →
      (linksFull[l]?).getD .layers = .layers →
      ∀ b₀ o hp tl', x.2.here = .lay b₀ → b₀.own = some o → Bs.G₀.W.G[X.g]? = some hp →
      x'.2.tl? = some tl' →
      ∀ e cc, NamedEntry (Dm.Rd l) (Dm.N.sent l 0) p.1 p.2 x.2 A e cc →
      ∃ M n, Dm.uL l x.2 = uLay hp.tl M x.2 ∧
        LayRest (oneEntry e) (Dm.N.sent l 0) p.1 p.2 x.2 A (seatTab Dm.cs Dm.arr Dm.ms w) hp.tl tl' M o n
          (Dm.A1 l x' w))
    (hUA : Dm.uA = uArm XV)
    (hAtt : ∀ l X arrs x x' y y' w p A B, ReadsFenceB Dm mgBase ans test J Z Bs aN R₁ R₂ R₃ c l X arrs x x' y y' w p A B →
      (linksFull[l]?).getD .layers = .attention →
      ∀ a₀ Ap tlF tl', x.2.here = .att a₀ → Bs.G₀.W.A[X.g]? = some Ap → x.2.tl? = some tlF →
      x'.2.tl? = some tl' →
      ∀ e cc, NamedEntry (Dm.Rd l) (Dm.N.sent l 0) p.1 p.2 x.2 A e cc →
      ∃ i, AttRest XV (oneEntry e) (Dm.N.sent l 0) p.1 p.2 x.2 A (seatTab Dm.cs Dm.arr Dm.ms w) l Ap i
        tlF tl' (Dm.A1 l x' w))
    (hHead : ∀ l X arrs x x' y y' w p A B, ReadsFenceB Dm mgBase ans test J Z Bs aN R₁ R₂ R₃ c l X arrs x x' y y' w p A B →
      (linksFull[l]?).getD .layers = .head →
      ArmCellIn (Dm.Rd l) (Dm.N.sent l 0) (Dm.N.group l) p.1 p.2 x.2 A B
        (seatTab Dm.cs Dm.arr Dm.ms w) (Dm.uH l)) :
    ∀ l, l < 25 → ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ (x x' : ProofFile.InstPub × S) y y'
      (w : Wit (CellsQ rows cols) Tok MsgT),
      YesOf (blkL Z Bs.G₀ l false X arrs) x x' → InAt Dm.N (honest (mgAll Dm mgBase) ans test) linksFull (flatPlacesOf linksFull true) (noL l false) x y →
      ArmOk J x.2 →
      KeptBelow (baseL aN R₁ R₂ R₃ c l false) y y' → (mgAll Dm mgBase).tie l x' y' w →
      ∀ j n, Item.formsT l j n ∈ (rowQ linksFull (flatPlacesOf linksFull true) (noL l false)).ins →
      ∀ p ∈ Dm.runs l j n, ∀ A B, K9.segAt? x.2 = some A → K9.segAt? x'.2 = some B →
      ArmCellIn (Dm.Rd l) (Dm.N.sent l 0) (Dm.N.group l) p.1 p.2 x.2 A B
        (seatTab Dm.cs Dm.arr Dm.ms w) (armOf Dm.uL Dm.uA Dm.uH ((linksFull[l]?).getD .layers) l) :=
  arm_at_reads_of_b Dm dk mgBase J rfl hDlk Z Bs aN R₁ R₂ R₃ c hLay hUA hAtt hHead

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.ReadsFenceB
#print axioms VerifiableInference.Desc.K1.rides_at_reads_b
#print axioms VerifiableInference.Desc.K1.arm_at_reads_of_b
#print axioms VerifiableInference.Desc.K1.arm_at_reads_b
