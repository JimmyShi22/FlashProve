-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/KeyBack/BytesShort.lean: the seven strings of parameter bytes are shorter than 2 ^ 64
(each has fewer than 2 ^ 24 bytes), where what the planner configured is the written value. This is
the row «r7» of the key file's back (the seventh of the eight rows from which IM.keyBack_of_rows,
Johnson/IMR/KeyBackOfRows.lean, has the return of Key.keyDataAndDecisionOfPlannerAnswer): the premise h of Key.asks_of
(Johnson/Desc/Key/AsksLaw.lean), and so the test Key.bytesFit (Johnson/Desc/Key/BytesFit.lean). And
four of the seven from the goals' scope, with no test. Joins over the files beside it; no bytes are
evaluated. No sub-protocol imports this file.
  configured_short  of what configure returns, where freeOf made = writtenMade: all seven
  r7_of_free        the row, from Key.madeAt X₀ lay cfg = .ok m
  r7_of_layout      the same with the layout's equation in the place of the bound on its spelling
  four_short        of what configure returns at the written lines, where the key's sizing returns
                    the written sizes: the key's three strings and the copy's file's: no test
  four_at_scope     so in scope, from publicOfO's and Key.madeAt's return and a digest of 32 bytes
Premises of r7_of_free, by name. hc : cfg.size = 32: the digest's size stands in every sum
(ShortOfBounds.lean's long_cfg: at a long digest a string is long); where the row is spent the
digest is Key.fixedDigest, 32 bytes by its make · hF : freeOf m.p.chains.made = writtenMade: all
sizes and all seven lists of rounds are the written ones · hL : what shapesOf returns has a layout
whose spelling has fewer than 2 ^ 20 bytes: configure spells x.layout as the item "layout" and
keeps it in no field of what it returns.
Who can pay. hF: free_of_sized (Johnson/Goal/Written/ChainsW.lean) from made.sized = writtenSized
and the proof file's first list; in scope these two hang on made.sized.proof = proofSizedFull and
made.proof.head?: «MadeWritten» (Johnson/Desc/Ok/PlanWritten/MadeTestLaws.lean): in the library that
is the accept of the test madePinnedAt (made_in_scope, Johnson/Goal/Numbers/MadeInScope.lean, on the
proof file's road; that its «made» is Key.madeAt's is true by reading; no lemma for it was found).
hL: the step «Plan.reqFrame … = some (reqLinks, layoutFull)» of whoever shows that chainsOf returns;
or a law on reqFrame.
What the row is worth. NO MEMBER OF hF ∧ hL IS KNOWN IN LEAN. Every «layoutFull» of the
library speaks of the layout as read back; x.layout itself has no theorem, and no evaluation of it
is shown here. For an example of the head by the kernel hF is the dear premise
(the planner's own run for the proof file). Until it is paid, r7_of_free is true and idle for the
proof file's three strings. four_at_scope can be called at once: it pays where publicOfO's and
Key.madeAt's returns are had.
A thought, not typed and not traced: with hL the circle at the layout may open:
Given.read_items_fit (OnBytes/Params/Fit/ReadItems.lean) asks of each item fewer than 2 ^ 64 bytes,
which hL gives for "layout" (it asks also that the entries' and the items' names fit, and that no
entry is named "configuration"); it concludes that the items are read back as spelled; what carries
that to the layout as read back was not read.
Called, not typed: short_of_bounds · the seven few_* · lin_sum | entry_sum | first_sum ·
reqItem_full | layoutItem_full | small_full (the files beside) · items_full
(Johnson/Goal/Conditions/KeyBytesFitAtScope.lean, which has the first string in scope at
Model.Verify.planned: keyOneTime_size_at_scope) · configure_kept (Johnson/G/MadeSpelled.lean) ·
Fo.chainsOf_cut (OnBytes/Tie/Pv/Lookup/Ends/FoPlannedCut.lean) · Key.madeAt_chains
(Johnson/Desc/Key/NoCfgLive.lean) · keyPlans_of_configure · args_of_steps · publicSteps_of_O ·
keySized_returns · shapesOf_ranges · inScope_policy · sized_key · sized_link · entry_written.
Limits. The full size alone. The bounds are not sharp. No soundness is claimed. On hiding nothing.

-/
import Johnson.AtFull.KeyBack.WrittenFew
import Johnson.AtFull.KeyBack.WrittenItems
import Johnson.G.MadeSpelled
import Johnson.Desc.Key.NoCfgLive
import Johnson.Goal.Numbers.NumberPricesInScope
import OnBytes.Tie.Pv.Lookup.Ends.FoPlannedCut

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFull.KeyBack
open OnBytes OnBytes.Params OnBytes.Model.Verify
open Johnson.G (layoutFull pricedEntryFull)
open Johnson.G.MadeFree
open VerifiableInference.PlanWritten (proofSizedFull publicOfO publicSteps_of_O)
open VerifiableInference.PlanWritten.Joined (writtenMade)
open VerifiableInference.Number.ByRuns
open Lk6.AtPlan

theorem key_items : itemsSize (Plan.oneTimeItems keyFull) < 2 ^ 22 :=
  Nat.lt_trans items_full (by decide)

theorem keyLin_items : itemsSize (madeLinItems keyFull.codes keyFull.once.shape) < 2 ^ 22 := by
  have a := lin_sum keyFull.codes keyFull.once.shape
  have s := small_full
  omega

theorem proofLin_items :
    itemsSize (madeLinItems proofSizedFull.codes proofSizedFull.batch.shape) < 2 ^ 21 := by
  have a := lin_sum proofSizedFull.codes proofSizedFull.batch.shape
  have s := small_full
  omega

theorem entry_items {z : Sized} (h1 : z.entryCodes = recordCodes) (h2 : z.link = writtenLink) :
    itemsSize (madeEntryItems z) < 2 ^ 22 := by
  have s := small_full
  rw [entry_sum, h1, h2]
  omega

theorem key_few : ∀ P ∈ [keyThree.A.plan, keyThree.B.plan, keyThree.C.plan],
    fewB 65536 P.plan.entries = true := by
  intro P hP
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
  rcases hP with rfl | rfl | rfl
  · exact few_key1
  · exact few_key2
  · exact few_key3

theorem proof_few : ∀ P ∈ [proofThree.A.plan, proofThree.B.plan, proofThree.C.plan],
    fewB 65536 P.plan.entries = true := by
  intro P hP
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
  rcases hP with rfl | rfl | rfl
  · exact few_proof1
  · exact few_proof2
  · exact few_proof3

/-- **All seven, where the four free fields are the written value.** -/
theorem configured_short {l : Lines} {x : Shapes} {cfg : ByteArray} {bits : Nat}
    {made : Configured} (h : configure l x cfg bits = .ok made) (hc : cfg.size = 32)
    (hF : freeOf made = writtenMade) (hL : (spellLayout x.layout).size < 2 ^ 20) :
    made.keyOneTime.size < 2 ^ 24 ∧ made.keyShared.size < 2 ^ 24 ∧ made.keySecond.size < 2 ^ 24 ∧
      made.entryLink.size < 2 ^ 24 ∧ made.first.size < 2 ^ 24 ∧ made.shared.size < 2 ^ 24 ∧
      made.second.size < 2 ^ 24 := by
  have hk : made.key = [keyThree.A.plan, keyThree.B.plan, keyThree.C.plan] :=
    congrArg Free.key hF
  have hp : made.proof = [proofThree.A.plan, proofThree.B.plan, proofThree.C.plan] :=
    congrArg Free.proof hF
  have he : made.entry = pricedEntryFull := congrArg Free.entry hF
  have zk : made.sized.key = keyFull := congrArg (·.sized.key) hF
  have zp : made.sized.proof = proofSizedFull := congrArg (·.sized.proof) hF
  have zl : made.sized.link = writtenLink := congrArg (·.sized.link) hF
  have zc : made.sized.entryCodes = recordCodes := congrArg (·.sized.entryCodes) hF
  have hi : x.identifiers.length = proofSizedFull.request.link.length := by
    have k := configure_kept h
    rw [zp] at k
    simp only [Bool.or_eq_true, not_or, bne_iff_ne, ne_eq, not_not] at k
    exact k.1.1.1
  refine short_of_bounds h hc (by rw [hk]; exact key_few) (by rw [hp]; exact proof_few)
    (by rw [he]; exact few_entry) (by rw [zk]; exact key_items) (by rw [zk]; exact keyLin_items)
    (entry_items zc zl) ?_ (by rw [zp]; exact Nat.lt_trans proofLin_items (by decide))
  have a := proofLin_items
  have r := reqItem_full
  have s := small_full
  rw [first_sum, zp, hi]
  omega

/-- **The row r7 of the key file's back.** -/
theorem r7_of_free {X₀ : Public} {lay cfg : ByteArray} {m : Johnson.G.OfPlan.Made}
    (hm : VerifiableInference.Desc.Key.madeAt X₀ lay cfg = .ok m) (hc : cfg.size = 32)
    (hF : freeOf m.p.chains.made = writtenMade)
    (hL : ∀ links shapes, shapesOf X₀ (some lay) = .ok (links, shapes) →
      (spellLayout shapes.layout).size < 2 ^ 20) :
    ∀ n : ChainName, (m.p.chains.bytes n).size < 2 ^ 64 := by
  obtain ⟨links, shapes, hs, hg, -⟩ :=
    Fo.chainsOf_cut (VerifiableInference.Desc.Key.madeAt_chains hm)
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := configured_short hg hc hF (hL links shapes hs)
  have big : (2 : Nat) ^ 24 < 2 ^ 64 := by decide
  intro n
  cases n
  · exact Nat.lt_trans a1 big
  · exact Nat.lt_trans a2 big
  · exact Nat.lt_trans a3 big
  · exact Nat.lt_trans a4 big
  · exact Nat.lt_trans a5 big
  · exact Nat.lt_trans a6 big
  · exact Nat.lt_trans a7 big

/-- The same from the layout's equation. -/
theorem r7_of_layout {X₀ : Public} {lay cfg : ByteArray} {m : Johnson.G.OfPlan.Made}
    (hm : VerifiableInference.Desc.Key.madeAt X₀ lay cfg = .ok m) (hc : cfg.size = 32)
    (hF : freeOf m.p.chains.made = writtenMade)
    (hL : ∀ links shapes, shapesOf X₀ (some lay) = .ok (links, shapes) →
      shapes.layout = layoutFull) :
    ∀ n : ChainName, (m.p.chains.bytes n).size < 2 ^ 64 :=
  r7_of_free hm hc hF fun links shapes hs => by rw [hL links shapes hs]; exact layoutItem_full

/-- **Four strings, with no test**: at the written lines, where the key's sizing returns the
written sizes. -/
theorem four_short {x : Shapes} {cfg : ByteArray} {bits : Nat} {made : Configured}
    (h : configure recordLines x cfg bits = .ok made)
    (hk : Plan.keySized recordLines x.ranges = some keyFull) (hc : cfg.size = 32) :
    made.keyOneTime.size < 2 ^ 24 ∧ made.keyShared.size < 2 ^ 24 ∧ made.keySecond.size < 2 ^ 24 ∧
      made.entryLink.size < 2 ^ 24 := by
  obtain ⟨hz, _, _, _, _, _, _, _, _, ae⟩ := OnBytes.Params.configure_plans h
  have ek := keyPlans_of_configure h hk
  have zk : made.sized.key = keyFull :=
    Option.some.inj ((OnBytes.Params.sized_key hz).symm.trans hk)
  obtain ⟨e2, T, hT, hL⟩ := sized_link hz
  obtain rfl : T = recordTable := Option.some.inj (hT.symm.trans record_table)
  have e56 : (made.sized.link, made.sized.entryCodes) = (writtenLink, recordCodes) :=
    Option.some.inj (hL.symm.trans writtenLink_sized)
  have zl : made.sized.link = writtenLink := congrArg Prod.fst e56
  have zc : made.sized.entryCodes = recordCodes := congrArg Prod.snd e56
  have e2' : made.sized.set = recordSet := e2
  rw [e2', zl] at ae
  have he : made.entry = pricedEntryFull := Except.ok.inj
    (ae.symm.trans VerifiableInference.PlanWritten.Joined.entry_written)
  obtain ⟨P1, P2, P3, _, _, _, ek', _, e1, e3, e4, e5, _⟩ := configure_bytes h
  rw [ek] at ek'
  obtain ⟨rfl, rfl, rfl⟩ : keyThree.A.plan = P1 ∧ keyThree.B.plan = P2 ∧ keyThree.C.plan = P3 := by
    simpa using ek'
  have i0 : itemsSize [] < 2 ^ 22 := by decide
  rw [e1, e3, e4, e5, zk, he]
  exact ⟨size_params_lt few_key1 hc key_items, size_params_lt few_key2 hc keyLin_items,
    size_params_lt few_key3 hc i0, size_params_lt few_entry hc (entry_items zc zl)⟩

/-- **In scope, from the two returns and a digest of 32 bytes: the key's three strings and the
copy's file's.** -/
theorem four_at_scope {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true)
    {lf : Option ByteArray} {X₀ : Public} (hX : publicOfO o Z.pol Z.KL lf = .ok X₀)
    {lay cfg : ByteArray} {m : Johnson.G.OfPlan.Made}
    (hm : VerifiableInference.Desc.Key.madeAt X₀ lay cfg = .ok m) (hc : cfg.size = 32) :
    (m.p.chains.bytes .keyOneTime).size < 2 ^ 24 ∧ (m.p.chains.bytes .keyShared).size < 2 ^ 24 ∧
      (m.p.chains.bytes .keySecond).size < 2 ^ 24 ∧ (m.p.chains.bytes .link).size < 2 ^ 24 := by
  obtain ⟨v, hv⟩ := inScope_policy hZ
  rw [hv] at hX
  obtain ⟨hf, hw⟩ := args_of_steps (publicSteps_of_O hX)
  obtain ⟨links, shapes, hs, hg, -⟩ :=
    Fo.chainsOf_cut (VerifiableInference.Desc.Key.madeAt_chains hm)
  rw [hf] at hg
  exact four_short hg (keySized_returns hw (shapesOf_ranges hs)) hc

end AtFull.KeyBack

#print axioms AtFull.KeyBack.key_items
#print axioms AtFull.KeyBack.keyLin_items
#print axioms AtFull.KeyBack.proofLin_items
#print axioms AtFull.KeyBack.entry_items
#print axioms AtFull.KeyBack.key_few
#print axioms AtFull.KeyBack.proof_few
#print axioms AtFull.KeyBack.configured_short
#print axioms AtFull.KeyBack.r7_of_free
#print axioms AtFull.KeyBack.r7_of_layout
#print axioms AtFull.KeyBack.four_short
#print axioms AtFull.KeyBack.four_at_scope
