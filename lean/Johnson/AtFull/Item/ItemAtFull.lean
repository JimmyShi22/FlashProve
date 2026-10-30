-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Item/ItemAtFull.lean: at `VerifierAndGoals.storedPublicFiles`, for every request of the right length, the
item "request" is made and its comparison with the public part accepts.

Why. The verifier's tests on an instance (`ProofFile.holdBy`, Johnson/Desc/ProofFile/Pub.lean) form the
item "request" from the parameter file, the scale file and the request, and compare it with the
public part (`Verify.statementHeld`, OnBytes/Model/VerifyStatement.lean). By a reading of these
texts, which no theorem here states: where that comparison fails at given public files, every
instance is refused, so that the verifier rejects everything there; and the test `protocolDataWellFormed` does not
ask it.

Main names.
* `parts_zFull`: `Parts` (Johnson/AtFull/Item/HeldOfParts.lean) holds at the public part's value X₀,
  the lines of the parameter file and 4,104 bytes.
* `item_zFull`: at every string req of 4 (X₀.T + 2) bytes, `Fmt.requestItem` at the format's second
  hash function returns an item, and `statementHeld X₀` accepts it.
* `no_item_zFull`: at a string of another length no item is made.
* `tokens_zFull`, `vocab_zFull`: X₀ has 1,024 tokens and 202,048 entries of the vocabulary.
* `facts_zFull`: these two and `parts_zFull` in one statement.

How. The closed facts of Johnson/AtFull/Item/PartsAtFull.lean, at the form of X₀ in
Johnson/AtFull/Public/Join.lean; the law `held_of_parts`; the tree hash returns by the strings'
lengths (`isSome_olderTK_eq`, Johnson/Unfolds/SecondHashFunctionTree.lean). No hash is evaluated in the files
under Johnson/AtFull/Item/: the three digests that are compared are, on both sides, the earlier hash
of one text; the scale file's and the request's digests are compared with nothing.

Limits.
* Two premises, at `parts_zFull`, `item_zFull`, `tokens_zFull`, `vocab_zFull` and `facts_zFull`.
  hsz: the layout file has 224,975 bytes; it is shown in the side library
  (AtFullSide/Layout/Size.lean). hX: `publicOfO` at the earlier hash returns X₀;
  `publicOfO_zFull_all` (Johnson/AtFull/Public/AtX0All.lean) gives it from hsz.
  `no_item_zFull` takes hsz alone.
* The parameter, scale and layout files of `VerifierAndGoals.storedPublicFiles` alone. `VerifierAndGoals.storedPublicFiles` is a term, which no
  Lean ties to files in a folder; the example's weights are synthetic. The goals' scope
  (`VerifierAndGoals.InScope`) takes in many parameter files: this file and ItemAtGap.lean settle two,
  at one scale file.
* At the format's second hash function (`OnBytes.secondHashFunction`).
* TWO OF THE SEVEN STEPS OF THE TESTS ON AN INSTANCE (`ProofFile.holdBy`): the item is made; the
  comparison accepts. The other five (the words' test, the reader of the request and the reply, the
  covered positions, the links' structures, the seeds of the table's key) are not shown here. That
  the verifier accepts any proof is not shown. Nothing on soundness, on binding or on hiding.
* The two steps are shown at X₀, `storedPublicFiles.pol` and `storedPublicFiles.KL`. `holdBy` compares at `Z.p.X` and forms
  the item from `Z.pol` and `Z.KL`, for a `Z : ProofFile.Pub`. No theorem in this file says that these
  agree: the caller has to show that.
* Other places where a test on the public files can make the verifier reject everything are known:
  three are settled side by side in AtFullSide/Top/ThreeTests.lean, and the key file's test on an
  instance is another. More are known, and no theorem says that any list of them is whole.
-/
import Johnson.AtFull.Item.PartsAtFull
import Johnson.AtFull.Public.Join
import Johnson.AtFull.Public.AtX0All
import Johnson.Unfolds.SecondHashFunctionTree
import Johnson.Unfolds.Sizes.KL

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Item
open OnBytes OnBytes.Proof OnBytes.Model OnBytes.Model.Verify OnBytes.K
open VerifiableInference.PlanWritten
open OnBytes.Road.K4.Trial.Values (PW yFull withY withY_eq)
open _root_.AtFull.Head (withLaid_true)

/-- The tree hash returns 32 bytes, where the test on the length accepts. -/
theorem olderTK_returns {w : ByteArray} (h : Johnson.Unfolds.tkOk w.size = true) :
    ∃ d, secondHashFunctionTree w = some d ∧ d.size = 32 := by
  have hs := Johnson.Unfolds.isSome_olderTK_eq w
  rw [h] at hs
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.1 hs
  exact ⟨d, hd, size_olderTK hd⟩

/-- **The two readers agree at `VerifierAndGoals.storedPublicFiles`**, and X₀ has 1,024 tokens and 202,048 entries of the
vocabulary. -/
theorem facts_zFull (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975) {X₀ : Public}
    (hX : publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) =
      .ok X₀) :
    Parts X₀ (ParamLines.read VerifierAndGoals.storedPublicFiles.pol) (4 * (2 ^ 10 + 2)) ∧ X₀.T = 1024 ∧
      X₀.P.h.V = 202048 := by
  obtain ⟨sc, wsLay, HLy, l, ps, layers, G, seenA, owner, -, -, ⟨hH, -, hLW⟩, hl, -, e6, -, -, -, -,
    hX'⟩ := _root_.AtFull.Public.publicOfO_zFull_of_rest hsz
  obtain rfl := Except.ok.inj (hX'.symm.trans hX)
  refine ⟨?_, ?_, vocab_W⟩
  · rw [read_zFull]
    refine parts_of_tests numbers_W ?_ ?_ ?_
    · exact calls_of_text ((withY_eq _).symm.trans call_W)
    · have h := callA_W
      unfold callAB at h
      rw [hl] at h
      exact calls_of_text h
    · obtain ⟨H, eH, hT⟩ := withLaid_true callH_W _ hLW
      obtain rfl := Except.ok.inj (eH.symm.trans hH)
      exact calls_of_text hT
  · show layers.y.T = 1024
    rw [OnBytes.Road.Hd.pubOf_y e6]
    exact eq_of_beq ((withY_eq _).symm.trans tokens_W)

/-- The two readers agree at `VerifierAndGoals.storedPublicFiles`. -/
theorem parts_zFull (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975) {X₀ : Public}
    (hX : publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) =
      .ok X₀) : Parts X₀ (ParamLines.read VerifierAndGoals.storedPublicFiles.pol) (4 * (2 ^ 10 + 2)) :=
  (facts_zFull hsz hX).1

/-- X₀ has 1,024 tokens. -/
theorem tokens_zFull (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975) {X₀ : Public}
    (hX : publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) =
      .ok X₀) : X₀.T = 1024 :=
  (facts_zFull hsz hX).2.1

/-- X₀ has 202,048 entries of the vocabulary. -/
theorem vocab_zFull (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975) {X₀ : Public}
    (hX : publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) =
      .ok X₀) : X₀.P.h.V = 202048 :=
  (facts_zFull hsz hX).2.2

/-- **AT `VerifierAndGoals.storedPublicFiles`, FOR EVERY REQUEST OF THE RIGHT LENGTH, THE ITEM IS MADE AND THE COMPARISON
ACCEPTS.** -/
theorem item_zFull (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975) {X₀ : Public}
    (hX : publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) =
      .ok X₀) :
    ∀ req : ByteArray, req.size = 4 * (X₀.T + 2) →
      ∃ it, Fmt.requestItem OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL req = some it ∧
        statementHeld X₀ it = .ok () := by
  intro req hreq
  rw [tokens_zFull hsz hX] at hreq
  obtain ⟨s, hs, -⟩ := olderTK_returns (w := VerifierAndGoals.storedPublicFiles.KL) (by
                rw [Johnson.Unfolds.size_KL]
                decide)
  obtain ⟨r, hr, hr32⟩ := olderTK_returns (w := req) (by
    rw [hreq]
    decide)
  obtain ⟨it, h1, h2⟩ := held_of_parts (parts_zFull hsz hX) hs hr32
  refine ⟨it, ?_, h2⟩
  rw [← OnBytes.Tie.Decl.RequestItemLaw.requestItem_eq, requestItem_eq_itemWith, hr, hreq]
  exact h1

/-- **At a request of another length no item is made.** -/
theorem no_item_zFull (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975) {req : ByteArray}
    (h : req.size ≠ 4 * (2 ^ 10 + 2)) :
    Fmt.requestItem OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL req = none := by
  obtain ⟨X₀, hX, -⟩ := _root_.Johnson.AtFull.Public.publicOfO_zFull_all hsz
  rw [← OnBytes.Tie.Decl.RequestItemLaw.requestItem_eq, requestItem_eq_itemWith]
  exact none_of_length (parts_zFull hsz hX) h _

end Johnson.AtFull.Item

#print axioms Johnson.AtFull.Item.olderTK_returns
#print axioms Johnson.AtFull.Item.facts_zFull
#print axioms Johnson.AtFull.Item.parts_zFull
#print axioms Johnson.AtFull.Item.tokens_zFull
#print axioms Johnson.AtFull.Item.vocab_zFull
#print axioms Johnson.AtFull.Item.item_zFull
#print axioms Johnson.AtFull.Item.no_item_zFull
