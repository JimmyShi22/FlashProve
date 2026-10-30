-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/NamesAtBatch.lean: THE SMALLNESS TEST, THE HONEST PROVER's SIDE: AT EVERY
STATE THAT THE FIRST CHAIN's OWN BLOCKS REACH IN FRONT OF A SEGMENT's BATCHING, AT ALL 25 SEGMENTS,
IN THE GOALS' SCOPE, THE OPEN LEDGER's ARRAYS HAVE, IN ORDER, THE NAMES OF THE BUILT SEGMENT's
PLANNED ARRAYS: THE SENTENCE `ArrayNamesAtBatch` (Johnson/Desc/K8/Honest/NamesStated.lean) IS SHOWN.
SO THE DIGITS' ARRAY BEARS THE NAME "ZZ" THERE; AND AT THE 24 SEGMENTS IN FRONT OF THE HEAD's, AT
EVERY STATE THAT THE BLOCKS WITH THE TEST ON WORDS IN FRONT (`Sound.below`) REACH, UNDER THE
DESCRIPTION's TEST ON ITS PLAN, `AllFront` (LeftAtLink.lean) HOLDS WITH NO SENTENCE LEFT. THAT ANY
SUCH STATE IS REACHED IS NOT SHOWN. Lemmas; none of the library's goals.

  **`arrayNames_at_batch`** the scope · the files read · an opening of the description ⊢
                   ArrayNamesAtBatch Z Bs c
  **`zzName_at_batch`** so, at all 25, at a reached state that shows tl and G: (G.trees.getD
                   tl.ix.ZZ {}).name = "ZZ"
  `allFront_at_wrapped` with the description's test on its plan, l < 24, at a state that the wrapped
                   blocks reach and that shows tl and G: there are g, nbW, Wn with tl.heard = some g
                   and AllFront tl G g nbW Wn
  **`allFront_at_wrapped_shown`** and such a state does show both: there are tl, G, g, nbW, Wn with
                   s.tl? = some tl, s.fork? = some G, tl.heard = some g and AllFront tl G g nbW Wn:
                   the binders are the scope, the files read, the opening, the test on the plan, l <
                   24, the built segment and the reached state
  `arrayNamesAt_bites`, `allFront_bites`, `allFront_empty_no`, `arrNamesAre_empty` TEETH ON THE TWO
                   PREDICATES, AT BENT DATA: at a state whose open ledger has one array more than
                   the plan ArrayNamesAt fails; at a ledger whose digits' array bears another name
                   AllFront fails; closed: at the empty ledger AllFront fails, whatever the other
                   letters; the empty ledger has the empty list of names and not the list of the one
                   name "ZZ"
By: `seatKeeps_arrNames`, `okHead_atN`, `arrNamesInv_none`, `anOf_at`
(Johnson/Desc/K8/Honest/Names/: seventeen files made by program from the library's family on the
arrays' looks) · the library's generic walk Meaning.K2.open_fold (Johnson/IMR/OpenWalk.lean),
Meaning.K2.group_all, Meaning.Carry.front_len, LinkJoin.start_none, `reach_fold`, `reach_raw` ·
`zzName_of_names`, `allFront_of_names` (NamesStated.lean) · `drawn_at_batch`
(Johnson/P1K8R/DrawAtBatch.lean), `sized_at_batch` (HeardAtBatch.lean).
WRITTEN A FURTHER TIME: the proof of `arrayNames_at_batch` is that of `looks_at_batch`
(Johnson/P1K8R/StaticAtBatch.lean), line for line, with the names in the looks' place.
Limits. NOTHING SAYS THAT ANY STATE IS REACHED IN FRONT OF A BATCHING: where none is, all is idle.
THAT THE PREMISES CAN BE MET TOGETHER IS NOT SHOWN HERE: an opening of the description is a premise.
`AllFront`: AT THE WRAPPED FAMILY ALONE (`Sound.below` is a device of the proof and runs nowhere;
the decision that runs makes the same test once, on all that is shown); UNDER THE DESCRIPTION's TEST
ON ITS PLAN; NOTHING AT THE HEAD's SEGMENT but the names. IN SCOPE ALONE: the full size; the first
chain. THE TEETH ARE ON THE PREDICATES, NOT ON THE THEOREMS' PREMISES: no bent plan is shown at
which an end fails. No prover stands in it.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.K8.Honest.NamesStated
import Johnson.Desc.K8.Honest.Names.ArrNamesSeat
import Johnson.Desc.K8.Honest.Names.ArrNamesAtOpen

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **THE SENTENCE THAT WAS OWED.** -/
theorem arrayNames_at_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) : ArrayNamesAtBatch Z Bs c := by
  intro l hl Xl e3 z s h G hG
  obtain ⟨-, rs, cols, f⟩ := Johnson.Desc.First.Walk.Tied.reach_fold.1 h
  have hk' : 14 * l + (if l = 24 then 11 else 9) ≤ (Meaning.K2.frontOf c).length := by
    rw [Meaning.Carry.front_len hS hR O]
    split_ifs <;> omega
  obtain ⟨L, h1, h2, -⟩ := Meaning.K2.group_all hS hR O hl
    (k := 14 * l + (if l = 24 then 11 else 9)) (by split_ifs <;> omega) (by split_ifs <;> omega) f
  have hlk : LinkJoin.ArrNamesAre (LinkJoin.anOfBuilt Z.p.built.links L.link) G :=
    Meaning.K2.open_fold (LinkJoin.seatKeeps_arrNames Z.p.built.links) O rfl
      (fun l Q hQ => LinkJoin.okHead_atN O.blank hQ) hk' f
      (LinkJoin.arrNamesInv_none _ (LinkJoin.start_none O.pub z)) G L hG h1
  rw [h2] at hlk
  exact hlk.trans (LinkJoin.anOf_at O.blank e3)

/-- **The digits' array bears its name at the state's own ledger**, at all 25 segments. -/
theorem zzName_at_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {l : ℕ} (hl : l < 25) {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (z, s))
    {tl : HTailF2} {G : Fork} (ht : s.tl? = some tl) (hG : s.fork? = some G) :
    (G.trees.getD tl.ix.ZZ {}).name = "ZZ" :=
  zzName_of_names hS hR O (arrayNames_at_batch hS hR O) hl e3 h ht hG

/-- **`AllFront`, WITH NO SENTENCE LEFT**, at every state that the blocks with the test on words
in front reach in front of the batching of a segment l < 24, and that shows tl and G. -/
theorem allFront_at_wrapped (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 24) {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) (14 * l + 9) (z, s))
    {tl : HTailF2} {G : Fork} (ht : s.tl? = some tl) (hG : s.fork? = some G) :
    ∃ (g : Forest.Heard) (nbW : Nat) (Wn : List Want), tl.heard = some g ∧
      AllFront tl G g nbW Wn :=
  allFront_of_names hS hR O hOk (arrayNames_at_batch hS hR O) hl e3 h ht hG

/-- **AND THE STATE SHOWS BOTH: no binder on what it shows is left.** -/
theorem allFront_at_wrapped_shown (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 24) {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) (14 * l + 9) (z, s)) :
    ∃ (tl : HTailF2) (G : Fork) (g : Forest.Heard) (nbW : Nat) (Wn : List Want),
      s.tl? = some tl ∧ s.fork? = some G ∧ tl.heard = some g ∧ AllFront tl G g nbW Wn := by
  have h' : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (z, s) := by
    rw [if_neg (by omega)]
    exact reach_raw h
  obtain ⟨tl, ht, -, -⟩ := _root_.P1K8.drawn_at_batch hS hR O (by omega : l < 25) h'
  obtain ⟨G, hG, -⟩ := _root_.P1K8.sized_at_batch hS hR O hOk hl (reach_raw h)
  obtain ⟨g, nbW, Wn, hg, a⟩ := allFront_at_wrapped hS hR O hOk hl e3 h ht hG
  exact ⟨tl, G, g, nbW, Wn, ht, hG, hg, a⟩

end

/-! ## Teeth: the two sentences can fail -/

/-- A TOOTH: at a state whose open ledger has one array more than the plan, `ArrayNamesAt`
fails. -/
theorem arrayNamesAt_bites {Xl : LinkH} {s : S} {G : Fork} (hG : s.fork? = some G) (X : HTree)
    (e : G.trees = Xl.Fp.trees.push X) : ¬ ArrayNamesAt Xl s := by
  intro N
  have k := congrArg List.length (N G hG)
  simp [arrayNames, e] at k

/-- A TOOTH: at a ledger whose digits' array bears another name, `AllFront` fails. -/
theorem allFront_bites {tl : HTailF2} {G : Fork} {g : Forest.Heard} {nbW : Nat} {Wn : List Want}
    (hn : (G.trees.getD tl.ix.ZZ {}).name ≠ "ZZ") : ¬ AllFront tl G g nbW Wn :=
  fun a => hn a.digits.name

/-- THAT TOOTH, CLOSED: at the empty ledger `AllFront` fails, whatever the other letters. -/
theorem allFront_empty_no (tl : HTailF2) (g : Forest.Heard) (nbW : Nat) (Wn : List Want) :
    ¬ AllFront tl ({} : Fork) g nbW Wn :=
  allFront_bites (by simp)

/-- The property that the walk carries can hold and can fail: the empty ledger has the empty list
of names, and not the list of the one name "ZZ". -/
theorem arrNamesAre_empty :
    LinkJoin.ArrNamesAre [] ({} : Fork) ∧ ¬ LinkJoin.ArrNamesAre ["ZZ"] ({} : Fork) := by
  constructor <;> simp [LinkJoin.ArrNamesAre]

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.arrayNames_at_batch
#print axioms VerifiableInference.Desc.First.K8.Honest.zzName_at_batch
#print axioms VerifiableInference.Desc.First.K8.Honest.allFront_at_wrapped
#print axioms VerifiableInference.Desc.First.K8.Honest.allFront_at_wrapped_shown
#print axioms VerifiableInference.Desc.First.K8.Honest.arrayNamesAt_bites
#print axioms VerifiableInference.Desc.First.K8.Honest.allFront_bites
#print axioms VerifiableInference.Desc.First.K8.Honest.allFront_empty_no
#print axioms VerifiableInference.Desc.First.K8.Honest.arrNamesAre_empty
