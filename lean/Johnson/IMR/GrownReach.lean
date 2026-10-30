-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/IMR/GrownReach.lean: e₁ AT THE PROOF FILE, THE HALF THAT READS THE VERIFIER's STATE ALONE: THE JOIN AND THE WHOLE ROAD AT THE FENCE «REACHED», IN THE FORM THAT THE TOOLS CAN ENTER; AND OUR 101 QUIET ROWS THERE, WITHOUT THE PLAN's TWO COUNTS.
WHY (a reader's third flag on rider 5, right): the tools (book_of_reach · HandsR.of_five · handsR_of_counts | _same) ask «bs[k]? = some b»; SharesR hands a payer FlatCase Z G₀ c k b alone, which does not hold it: so the tools joined x_at_reach and not the other join. HERE THE PAYER HAS BOTH IN HAND.
  SharesRF p N E Z G₀ c   ∀ k b, c.blocksInOrder[k]? = some b → FlatCase Z G₀ c k b → HandsR (RF 0 c.blocksInOrder (ProofFile.startS Z) p) N linksW placesW E 0 k b.
  sharesRF_of_R     whoever has SharesR at that fence has it.
  x_reach_scope     IN SCOPE, THE WHOLE ROAD: SharesRF · the plan's two counts at the front · E 0 at the first state ⟹ X k AT EVERY REACHED STATE WITHOUT A MARK. (No premise hF: at this fence it is a theorem.)
  quiet_same        an accepting step of a sub-protocol that is seated alone over a lot's own of one of the six quiet kinds adds no tree and no oracle message.
  quiet_row_R       ★ OUR 101: HandsR (RF …) … (14 l + i + 2) b AT THE SEATED SUB-PROTOCOL, FROM: hB («bookAt at every reached state»: `book_reached`) · «more» at the lot's own. THE PLAN's TWO COUNTS hT | hM OF hear_quiet ARE NO PREMISES ANY MORE: FIVE OF SIX FIELDS STAND UNDER hB ALONE.
ON WORDS: «the state» is the verifier's state; a «sub-protocol» is a block of the IOP as written in Lean.
What is not claimed. «more» at any row (what each kind makes, asks or moves is its own). hB's own premises (K1Told · K2Told · blocksOk). No soundness.
-/
import Johnson.IMR.GrownFence
import Johnson.IMR.GrownQuiet
import Johnson.IMR.HandsReachR

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

open VerifiableInference.Desc (Block Chain FileDescription Place KindName foldBlocks OpenedColumn)
open VerifiableInference.Desc.First (S ModelPart Numbers frontPlace bookAt)
open Johnson.Desc.First.Walk.Tied (Reach)
open ProofFile (Cl)

/-- **The shares at the fence «reached», the number's entry in hand.** -/
def SharesRF (p : ProofFile.InstPub) (N : Numbers) (E : ℕ → S → Bool) (Z : ProofFile.Pub) (G₀ : ProofFile.Ground)
    (c : Chain S Cl) : Prop :=
  ∀ k b, c.blocksInOrder[k]? = some b → FlatCase Z G₀ c k b →
    HandsR (RF 0 c.blocksInOrder (ProofFile.startS Z) p) N linksW placesW E 0 k b

theorem sharesRF_of_R {p : ProofFile.InstPub} {N : Numbers} {E : ℕ → S → Bool} {Z : ProofFile.Pub}
    {G₀ : ProofFile.Ground} {c : Chain S Cl}
    (h : SharesR (RF 0 c.blocksInOrder (ProofFile.startS Z) p) N E 0 Z G₀ c) : SharesRF p N E Z G₀ c :=
  fun k b _ hc => h k b hc

/-- An accepting step of a sub-protocol seated alone over a quiet lot's own adds nothing. -/
theorem quiet_same {Z : ProofFile.Pub} {G₀ : ProofFile.Ground} {b b' : Block S Cl} {name : String} {a : Place}
    (lot : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀) (hq : quietMaker b'.place.kind = true)
    (hla : LaidAlone ProofFile.sameReply b b' name a) {ft : ℕ} :
    ∀ s s', Yes ft b s s' → s'.book.trees.size = s.book.trees.size ∧
      s'.st.oracles.size = s.st.oracles.size := by
  intro s s' hy
  obtain ⟨L, hL, hb⟩ := lot
  obtain ⟨rs, cols, n, e⟩ := hy.under (alone_underR hla)
  have Q := quiet_lot hL hb hq s _ _ s' (VerifiableInference.Desc.step_inv ft b' s s' rs cols n e).2.2.2
  exact ⟨by rw [Q.1.2.2.1], by rw [Q.1.1]⟩

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **IN SCOPE, THE WHOLE ROAD, AT THE FENCE «REACHED».** -/
theorem x_reach_scope (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {N : Numbers} {E : ℕ → S → Bool}
    {p : ProofFile.InstPub} (Sh : SharesRF p N E Z Bs.G₀ c)
    (hT : N.treesAt (some frontPlace) = 0) (hM : N.msgsAt (some frontPlace) = 0)
    (hE : (ProofFile.startS Z p).failed = none → E 0 (ProofFile.startS Z p) = true) {k : ℕ} {s : S}
    (hr : Reach 0 c.blocksInOrder (ProofFile.startS Z) k (p, s)) (hu : s.failed = none) :
    XK N linksW placesW E k s = true := by
  have h0 := s0_of_open (links := linksW) O p hT hM hE
  rw [places_scope hS hR O] at h0
  exact x_at_reach (fun k b hb => Sh k b hb (flat_cases hS hR O k b hb)) h0 hr hu

/-- **OUR 101 QUIET ROWS, WITHOUT THE PLAN's TWO COUNTS.** -/
theorem quiet_row_R {N : Numbers} {E : ℕ → S → Bool} {p : ProofFile.InstPub}
    (hB : ∀ k s, Reach 0 c.blocksInOrder (ProofFile.startS Z) k (p, s) → bookAt N placesW[k]? s = true)
    {l i : ℕ} {k0 : KindName} {b b' : Block S Cl} {name : String} (hl : l < 25)
    (hk : (VerifiableInference.Desc.First.kindsBeforeBatching (subAt l) (l == 0))[i]? = some k0)
    (lot : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks Bs.G₀)
    (hp : b'.place = { chain := 1, link := some l, piece := i + 1, kind := k0 })
    (hq : quietMaker k0 = true)
    (hla : LaidAlone ProofFile.sameReply b b' name { chain := 1, link := some l, piece := i + 1, kind := k0 })
    (hb : c.blocksInOrder[14 * l + i + 2]? = some b)
    (more : ∀ s s', Yes 0 b' s s' → s.failed = none → s'.failed = none →
      XK N linksW placesW E (14 * l + i + 2) s = true → E (14 * l + i + 2 + 1) s' = true) :
    HandsR (RF 0 c.blocksInOrder (ProofFile.startS Z) p) N linksW placesW E 0 (14 * l + i + 2) b := by
  have hi : i < nAt l := by
    have h1 := (List.getElem?_eq_some_iff.1 hk).1
    have h2 : ∀ l < 25, (VerifiableInference.Desc.First.kindsBeforeBatching (subAt l) (l == 0)).length = nAt l := by
      decide
    rwa [h2 l hl] at h1
  exact handsR_of_same hB hb (quiet_same lot (by rw [hp]; exact hq) hla)
    fun hT hM => (hear_quiet hl hi hk lot hp hq hT hM more).under (alone_underR hla)

end

end IM

#print axioms IM.sharesRF_of_R
#print axioms IM.quiet_same
#print axioms IM.x_reach_scope
#print axioms IM.quiet_row_R
