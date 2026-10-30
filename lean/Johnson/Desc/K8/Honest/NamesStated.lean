-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/NamesStated.lean: THE SMALLNESS TEST, THE HONEST PROVER's SIDE: THE ONE
SENTENCE THAT `AllFront` (Johnson/Desc/K8/Honest/LeftAtLink.lean) STILL WANTS AT THE 24 SEGMENTS IN
FRONT OF THE HEAD's, STATED, AND WHAT IT BUYS. THE SENTENCE ITSELF IS NOT SHOWN HERE: IT IS A
DEFINITION, AND A PREMISE OF THE TWO THEOREMS. Definitions and lemmas; none of the library's goals.

  `arrayNames F` a ledger's arrays' names, in order
  `ArrayNamesAt Xl s` whatever ledger the state s holds open has the names of the built segment's
                   planned arrays
  **`ArrayNamesAtBatch Z Bs c`** THE SENTENCE THAT IS OWED: `ArrayNamesAt` at every state that the
                   chain's own blocks reach in front of a segment's batching, at all 25 segments. It
                   has the form of `looks_at_batch` (Johnson/P1K8R/StaticAtBatch.lean), which says
                   the like of the arrays' looks, with the names in the looks' place
  `arrayName_at` where two ledgers have the same names, so has each array
  **`zzName_of_names`** under the sentence: the digits' array bears the name "ZZ" at the state's own
                   ledger, at all 25 segments
  **`allFront_of_names`** under the sentence, l < 24, at a state that the blocks with the test on
                   words in front reach AND THAT SHOWS the test's data tl and a ledger G: there are
                   g, nbW, Wn with tl.heard = some g and AllFront tl G g nbW Wn: NO OTHER SENTENCE
                   IS LEFT (that such a state shows the data is had: `drawn_at_batch`,
                   Johnson/P1K8R/DrawAtBatch.lean; that it shows a ledger is a binder here)
By: `allFront_at_wrap` (Johnson/Desc/K8/Honest/OneSentenceLeft.lean) · `arraysLook_built`,
`planned_arrays` (ArraysAtBatch.lean: the name at the planned ledger; the number of the digits'
array is a planned field) · the library's LinkJoin.planned_at_batch, `reach_raw`.
WRITTEN A FURTHER TIME: `arrayName_at`'s proof is that of `look_at`
(Johnson/Desc/K8/Honest/PlanesShape.lean), with the names in the looks' place.
THE ROAD THAT IS MEANT FOR THE SENTENCE, NOT WALKED: a property of a ledger of its own, «the arrays'
names are ns», over the root of the library's family on the looks, which is general in the property
(`ForkRests P`, `rests_fork`: Johnson/Desc/First/Link/Law/SizedRides.lean), and, above it, carried
by the library's generic walk (Meaning.K2.SeatKeeps, one field a kind; `open_fold`:
Johnson/IMR/SeatKeeps.lean, OpenWalk.lean) as the library carries the looks (`seatKeeps_looks`,
Johnson/LPFK9R/LooksSeat.lean) and Johnson/P1K8R/ZeroSeat.lean the rows' first columns. The last
mile is `looks_at_batch`'s own proof, with the names in the looks' place.
Limits. THE SENTENCE IS PAID BY NOBODY. That it holds is expected, since an array is built by the
planner's two routines alone (Johnson/Desc/First/Link/Law/LooksAre.lean's head), and not shown.
`allFront_of_names`: AT THE WRAPPED FAMILY ALONE; NOTHING AT THE HEAD's SEGMENT. IN SCOPE ALONE: the
full size; under an opening of the description and, in the last, its test on its plan; the first
chain. Nothing says that any state is reached. No prover stands in it.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.K8.Honest.OneSentenceLeft

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)

/-- A ledger's arrays' names, in order. -/
def arrayNames (F : Fork) : List String := F.trees.toList.map (·.name)

/-- Whatever ledger the state holds open has the names of the built segment's planned arrays. -/
def ArrayNamesAt (Xl : LinkH) (s : S) : Prop :=
  ∀ G, s.fork? = some G → arrayNames G = arrayNames Xl.Fp

/-- **THE SENTENCE THAT IS OWED**: at every state that the chain's own blocks reach in front of a
segment's batching, at all 25 segments. A definition: it claims nothing. -/
def ArrayNamesAtBatch (Z : ProofFile.Pub) (Bs : ProofFile.PureBase) (c : Chain S Claim) : Prop :=
  ∀ l, l < 25 → ∀ Xl, Bs.G₀.built[l]? = some Xl → ∀ (z : ProofFile.InstPub) (s : S),
    Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (z, s) → ArrayNamesAt Xl s

/-- Where two ledgers have the same names, so has each array. -/
theorem arrayName_at {F G : Fork} (h : arrayNames F = arrayNames G) (t : Nat) :
    (F.trees.getD t {}).name = (G.trees.getD t {}).name := by
  have h1 := congrArg (fun X => (X[t]?).getD ({} : HTree).name) h
  simp only [arrayNames, List.getElem?_map, Array.getElem?_toList] at h1
  simp only [Array.getD_eq_getD_getElem?]
  cases hA : F.trees[t]? <;> cases hB : G.trees[t]? <;>
    simp only [hA, hB, Option.map_some, Option.map_none, Option.getD_some,
      Option.getD_none] at h1 ⊢ <;> exact h1

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **What it buys, first: the digits' array bears its name at the state's own ledger**, at all
25 segments. -/
theorem zzName_of_names (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (N : ArrayNamesAtBatch Z Bs c)
    {l : ℕ} (hl : l < 25) {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (z, s))
    {tl : HTailF2} {G : Fork} (ht : s.tl? = some tl) (hG : s.fork? = some G) :
    (G.trees.getD tl.ix.ZZ {}).name = "ZZ" := by
  have hx : (l, (if l = 24 then 5 else 4), (if l = 24 then 3 else 2)) ∈ P1K8S.stretches :=
    List.mem_map.2 ⟨l, List.mem_range.2 hl, rfl⟩
  have e : 14 * l + (if l = 24 then 5 else 4) + 3 + (if l = 24 then 3 else 2) =
      14 * l + (if l = 24 then 11 else 9) := by
    split_ifs <;> omega
  have h' : Reach 0 c.blocksInOrder (ProofFile.startS Z)
      (14 * l + (if l = 24 then 5 else 4) + 3 + (if l = 24 then 3 else 2)) (z, s) := by
    rw [e]
    exact h
  have g := LinkJoin.of_readTl
    (LinkJoin.planned_at_batch planned_arrays hS hR O hx e3 (z, s) h') tl ht
  have ix : tl.ix = Xl.tl.ix := congrArg (·.1) g
  rw [arrayName_at (N l hl Xl e3 z s h G hG) tl.ix.ZZ, ix]
  exact (arraysLook_built hS hR O hl e3).2

/-- **WHAT IT BUYS: `AllFront` WITH NO SENTENCE LEFT**, at every state that the blocks with the
test on words in front reach in front of the batching of a segment l < 24. -/
theorem allFront_of_names (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    (N : ArrayNamesAtBatch Z Bs c)
    {l : ℕ} (hl : l < 24) {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) (14 * l + 9) (z, s))
    {tl : HTailF2} {G : Fork} (ht : s.tl? = some tl) (hG : s.fork? = some G) :
    ∃ (g : Forest.Heard) (nbW : Nat) (Wn : List Want), tl.heard = some g ∧
      AllFront tl G g nbW Wn := by
  have h' : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (z, s) := by
    rw [if_neg (by omega)]
    exact reach_raw h
  obtain ⟨g, hg, k⟩ := allFront_at_wrap hS hR O hOk hl e3 h ht hG
  obtain ⟨nbW, Wn, a⟩ := k (zzName_of_names hS hR O N (by omega) e3 h' ht hG)
  exact ⟨g, nbW, Wn, hg, a⟩

end

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.arrayName_at
#print axioms VerifiableInference.Desc.First.K8.Honest.zzName_of_names
#print axioms VerifiableInference.Desc.First.K8.Honest.allFront_of_names
